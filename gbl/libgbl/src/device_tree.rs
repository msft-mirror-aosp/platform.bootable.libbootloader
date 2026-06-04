// Copyright 2024, The Android Open Source Project
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! GblOps trait that defines device tree components helpers.

extern crate alloc;

use crate::{constants::FDT_ALIGNMENT, gbl_println, GblOps};
use alloc::vec::Vec;
use arrayvec::ArrayVec;
use dttable::{DtTableEntry, DtTableImage, DtTableMetadata};
use fdt::{Fdt, FdtHeader, FDT_HEADER_SIZE, MAXIMUM_OVERLAYS_TO_APPLY};
use liberror::{Error, Result};
use libutils::aligned_subslice;

/// Maximum number of device tree components GBL can handle to select from.
pub const MAXIMUM_DT_COMPONENTS: usize = 512;
/// Error message for unsupported number of device tree components.
pub const MAXIMUM_DT_COMPONENTS_ERROR_MSG: &str =
    "At most 512 device tree components are supported to build the final one";

/// The source device tree component is coming from.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum DtComponentSource {
    /// Loaded from Boot partition.
    Boot,
    /// Loaded from Vendor Boot partition.
    VendorBoot,
    /// Loaded from DTB partition.
    Dtb,
    /// Loaded from DTBO partition.
    Dtbo,
}

/// The device tree component type.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum DtComponentType {
    /// HLOS base device tree.
    BaseDt,
    /// HLOS device tree overlay.
    Overlay,
    /// Device assignment overlay to be applied to pVM
    PvmDeviceAssignmentOverlay,
}

/// To be used in the bootconfig. Do not change the values.
impl core::fmt::Display for DtComponentSource {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DtComponentSource::Boot => write!(f, "boot"),
            DtComponentSource::VendorBoot => write!(f, "vendor_boot"),
            DtComponentSource::Dtb => write!(f, "dtb"),
            DtComponentSource::Dtbo => write!(f, "dtbo"),
        }
    }
}

impl core::fmt::Display for DtComponentType {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DtComponentType::BaseDt => write!(f, "DTB"),
            DtComponentType::Overlay => write!(f, "DTBO"),
            DtComponentType::PvmDeviceAssignmentOverlay => write!(f, "PVM_DA_OVERLAY"),
        }
    }
}

/// Metadata for device tree component source information.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct DtComponentSourceMetadata {
    /// Source the component is loaded from.
    pub source: DtComponentSource,
    /// Index of the component within its source.
    pub source_index: usize,
}

/// Device tree component (base device tree or overlay) to build the final one.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct DtComponent<'a> {
    /// Source metadata.
    pub source_metadata: DtComponentSourceMetadata,
    /// Dt component type.
    pub component_type: DtComponentType,
    /// Metadata for entries loaded from dt_table structure.
    pub selection_metadata: Option<DtTableMetadata>,
    /// Device tree component payload. Must be 8 bytes aligned.
    pub dt: &'a [u8],
    /// Device tree component is selected.
    pub selected: bool,
}

/// Maintain, select and get the device tree components to build the final device tree.
pub struct DtComponentsRegistry<'a> {
    // TODO(b/374336105): Reconsider using dynamic memory here once the DT relocation
    // logic is eliminated, so covariance on 'a is no longer required.
    components: Vec<DtComponent<'a>>,
}

/// Selected device tree component.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct SelectedDtComponent<'a> {
    /// Source information metadata.
    pub source_metadata: DtComponentSourceMetadata,
    /// Device tree component payload.
    pub dt: &'a [u8],
}

/// A structure that holds all selected device tree components.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct SelectedDtComponentsContainer<T> {
    /// Selected base device tree.
    pub base_dt: T,
    /// Selected VMDTBO, if any.
    pub vmdtbo: Option<T>,
    /// Selected overlays.
    pub overlays: ArrayVec<T, MAXIMUM_OVERLAYS_TO_APPLY>,
}

/// A structure that holds all selected device tree components.
pub type SelectedDtComponents<'a> = SelectedDtComponentsContainer<SelectedDtComponent<'a>>;
/// A structure that holds all selected device tree components metadata.
pub type SelectedDtComponentsMetadata = SelectedDtComponentsContainer<DtComponentSourceMetadata>;

impl<'a> SelectedDtComponents<'a> {
    /// Consumes the object and returns lifetime-independent metadata for selected
    /// device tree components.
    pub fn into_metadata(self) -> SelectedDtComponentsMetadata {
        SelectedDtComponentsMetadata {
            base_dt: self.base_dt.source_metadata,
            vmdtbo: self.vmdtbo.map(|c| c.source_metadata),
            overlays: self.overlays.into_iter().map(|c| c.source_metadata).collect(),
        }
    }
}

/// Check the VM flag in overlay id
pub fn entry_is_vmdtbo(selection_metadata: &DtTableMetadata) -> bool {
    const VMDTBO_FLAG: u32 = 1 << 31;
    selection_metadata.id & VMDTBO_FLAG != 0
}

fn valid_vmdtbo(component: &DtComponent) -> bool {
    component.source_metadata.source == DtComponentSource::Dtbo
        && component.component_type == DtComponentType::PvmDeviceAssignmentOverlay
}

fn try_dt_totalsize_from_unaligned_bytes_ref(header: &[u8], buffer: &mut [u8]) -> Result<usize> {
    let aligned_buffer = aligned_subslice(buffer, FDT_ALIGNMENT)?;
    let header_slice = aligned_buffer
        .get_mut(..FDT_HEADER_SIZE)
        .ok_or(Error::BufferTooSmall(Some(FDT_HEADER_SIZE)))?;

    // Fdt header must be aligned, so copy to an aligned buffer.
    header_slice.copy_from_slice(
        &header.get(..FDT_HEADER_SIZE).ok_or(Error::BufferTooSmall(Some(FDT_HEADER_SIZE)))?,
    );

    match FdtHeader::from_bytes_ref(&header_slice) {
        Ok(header) => Ok(header.totalsize()),
        Err(e) => Err(e),
    }
}

impl<'a> DtComponentsRegistry<'a> {
    /// Create new empty DtComponentsRegistry.
    pub fn new() -> Self {
        DtComponentsRegistry { components: Vec::new() }
    }

    fn component_type(
        component_source: DtComponentSource,
        dt_entry: &DtTableEntry,
    ) -> DtComponentType {
        match component_source {
            DtComponentSource::Boot | DtComponentSource::VendorBoot | DtComponentSource::Dtb => {
                DtComponentType::BaseDt
            }
            DtComponentSource::Dtbo => {
                if entry_is_vmdtbo(&dt_entry.metadata) {
                    DtComponentType::PvmDeviceAssignmentOverlay
                } else {
                    DtComponentType::Overlay
                }
            }
        }
    }

    /// Load device tree components from a dt table image. Ensure components are 8 bytes
    /// aligned by using provided buffer to cut from. Returns remaining buffer.
    pub fn append_from_dttable<'b, 'c: 'a>(
        &mut self,
        component_source: DtComponentSource,
        dttable: &DtTableImage<'b>,
        buffer: &'c mut [u8],
    ) -> Result<&'c mut [u8]> {
        if self.components.len() + dttable.entries_count() > MAXIMUM_DT_COMPONENTS {
            return Err(Error::Other(Some(MAXIMUM_DT_COMPONENTS_ERROR_MSG)));
        }

        let mut remains = buffer;
        for (idx, entry) in dttable.entries().enumerate() {
            // TODO(b/374336105): Find a better way to handle 8-bytes alignment rather than copy.
            let (aligned_buffer, rest) = aligned_subslice(remains, FDT_ALIGNMENT)?
                .split_at_mut_checked(entry.dtb.len())
                .ok_or(Error::Other(Some(
                    "Provided buffer is too small to ensure dttable entry is aligned",
                )))?;
            aligned_buffer.copy_from_slice(entry.dtb);

            // Make sure the FDT reported size is valid (fits in the dttable entry size).
            let fdt_header = FdtHeader::from_bytes_ref(aligned_buffer)?;
            let fdt_totalsize = fdt_header.totalsize();
            if fdt_totalsize > aligned_buffer.len() {
                return Err(Error::Other(Some("DTBO overlay totalsize exceeds entry size")));
            }

            self.components.push(DtComponent {
                source_metadata: DtComponentSourceMetadata {
                    source: component_source,
                    source_index: idx,
                },
                component_type: Self::component_type(component_source, &entry),
                selection_metadata: Some(entry.metadata),
                // Trim off any unused trailing bytes e.g. due to dttable padding.
                dt: &aligned_buffer[..fdt_totalsize],
                selected: false,
            });

            remains = rest;
        }

        Ok(remains)
    }

    /// Append additional device trees from the buffer, where they are stored sequentially.
    /// Ensure components are 8 bytes aligned by using provided buffer to cut from. Returns
    /// remaining buffer.
    ///
    /// # Arguments
    ///
    /// * `ops` - an implementation of `GblOps`.
    /// * `component_source` - Source of the component.
    /// * `component_type` - Type of the component.
    /// * `start_index` - The starting index for components being appended. This is used to
    ///   assign a unique `source_index` to each appended component, relative to its
    ///   `component_source`.
    /// * `data` - Input buffer containing the raw sequential FDT data.
    /// * `buffer` - Output buffer where the 8-byte aligned FDT data will be stored.
    ///
    /// TODO(b/363244924): Remove after partners migrated to DTB.
    fn append_from_multifdt_buffer<'b, 'd: 'a>(
        &mut self,
        ops: &mut impl GblOps<'b>,
        component_source: DtComponentSource,
        component_type: DtComponentType,
        start_index: usize,
        data: &'a [u8],
        buffer: &'d mut [u8],
    ) -> Result<&'d mut [u8]> {
        let mut components_added = 0;
        let mut data_remains = data;
        let mut buffer_remains = buffer;

        while let Ok(next_fdt_size) =
            try_dt_totalsize_from_unaligned_bytes_ref(data_remains, buffer_remains)
        {
            if self.components.len() >= MAXIMUM_DT_COMPONENTS {
                return Err(Error::Other(Some(MAXIMUM_DT_COMPONENTS_ERROR_MSG)));
            }

            // Cut fdt and temporary buffers to make sure result fdt is 8 bytes aligned
            let (data_buffer, data_buffer_remains) =
                data_remains.split_at_checked(next_fdt_size).ok_or(Error::Other(Some(
                    "Multidt structure has a valid header but doesn't have a device tree payload",
                )))?;
            let aligned_buffer = aligned_subslice(buffer_remains, FDT_ALIGNMENT)?;
            let (aligned_buffer, aligned_buffer_remains) =
                aligned_buffer.split_at_mut_checked(next_fdt_size).ok_or(Error::Other(Some(
                    "Provided buffer is too small to ensure multidt entry is aligned",
                )))?;
            aligned_buffer.copy_from_slice(data_buffer);

            Fdt::new(&aligned_buffer)?;
            self.components.push(DtComponent {
                source_metadata: DtComponentSourceMetadata {
                    source: component_source,
                    source_index: start_index + components_added,
                },
                component_type: component_type,
                selection_metadata: None,
                dt: &aligned_buffer[..],
                selected: false,
            });

            components_added += 1;
            data_remains = data_buffer_remains;
            buffer_remains = aligned_buffer_remains;
        }

        if components_added > 0 {
            gbl_println!(
                ops,
                "WARNING: {} additional device trees detected in {}. This is only temporarily \
                supported in GBL. Please migrate to the DTB partition to provide multiple device \
                trees for selection.",
                components_added,
                component_source,
            );
        }

        Ok(buffer_remains)
    }

    /// Append device tree components from provided buffer prefix. `fdt` must be a 8 bytes aligned
    /// valid fdt buffer. `fdt` may also have multiple fdt buffers placed sequentially. Ensure each
    /// of such components are 8 bytes aligned by using provided `buffer` to cut from. Returns
    /// remaining buffer.
    pub fn append<'b, 'd: 'a>(
        &mut self,
        ops: &mut impl GblOps<'b>,
        component_source: DtComponentSource,
        component_type: DtComponentType,
        fdt: &'a [u8],
        buffer: &'d mut [u8],
    ) -> Result<&'d mut [u8]> {
        if self.components.len() >= MAXIMUM_DT_COMPONENTS {
            return Err(Error::Other(Some(MAXIMUM_DT_COMPONENTS_ERROR_MSG)));
        }

        let header = FdtHeader::from_bytes_ref(fdt)?;
        let (fdt_buffer, fdt_remains) = fdt
            .split_at_checked(header.totalsize())
            .ok_or(Error::Other(Some("FDT totalsize exceeds buffer length")))?;
        self.components.push(DtComponent {
            source_metadata: DtComponentSourceMetadata {
                source: component_source,
                source_index: 0,
            },
            component_type: component_type,
            selection_metadata: None,
            dt: fdt_buffer,
            selected: false,
        });

        // TODO(b/363244924): Remove after partners migrated to dttable.
        self.append_from_multifdt_buffer(
            ops,
            component_source,
            component_type,
            1,
            fdt_remains,
            buffer,
        )
    }

    /// Default implementation of selected logic in case external one isn't provided.
    /// Only base device tree is supported to choose from. Otherwise fail. No overlays will be
    /// selected.
    pub fn autoselect(&mut self) -> Result<()> {
        let base_dt_count = self
            .components
            .iter()
            .filter(|component| component.component_type == DtComponentType::BaseDt)
            .count();
        if base_dt_count > 1 {
            return Err(Error::Other(Some(
                "Base device tree autoselection isn't supported if multiple device trees are \
                provided",
            )));
        }

        let base = self
            .components
            .iter_mut()
            .find(|component| component.component_type == DtComponentType::BaseDt)
            .ok_or(Error::Other(Some("0 base device trees to autoselect from")))?;
        base.selected = true;

        Ok(())
    }

    /// Consumes the registry and returns selected base device tree and overlays to apply.
    /// Fail in case selection isn't correct. For correctness rules refer to
    /// `GblOps.select_device_trees` requirements.
    pub fn into_selected(self) -> Result<SelectedDtComponents<'a>> {
        Ok(SelectedDtComponents {
            base_dt: self.selected_base_dt()?,
            vmdtbo: self.selected_vmdtbo()?,
            overlays: self.selected_overlays()?,
        })
    }

    fn selected_base_dt(&self) -> Result<SelectedDtComponent<'a>> {
        self.components()
            .filter(|comp| comp.selected && comp.component_type == DtComponentType::BaseDt)
            .try_fold(None, |res, comp| match res {
                None => Ok(Some(SelectedDtComponent {
                    source_metadata: comp.source_metadata,
                    dt: comp.dt,
                })),
                _ => Err(Error::Other(Some("More than one base device tree is selected."))),
            })?
            .ok_or(Error::Other(Some("0 base device trees are selected")))
    }

    fn selected_overlays(
        &self,
    ) -> Result<ArrayVec<SelectedDtComponent<'a>, MAXIMUM_OVERLAYS_TO_APPLY>> {
        self.components()
            .filter(|comp| comp.selected && comp.component_type == DtComponentType::Overlay)
            .map(|comp| SelectedDtComponent { source_metadata: comp.source_metadata, dt: comp.dt })
            .try_fold(ArrayVec::new(), |mut acc, comp| {
                acc.try_push(comp)
                    .map_err(|_| Error::Other(Some("Too many overlays got selected.")))?;
                Ok(acc)
            })
    }

    /// Return the selected pvmfw VMDTBO, if any, and its index in the DTBO partition.
    fn selected_vmdtbo(&self) -> Result<Option<SelectedDtComponent<'a>>> {
        self.components().filter(|comp| comp.selected && valid_vmdtbo(comp)).try_fold(
            None,
            |res, comp| match res {
                None => Ok(Some(SelectedDtComponent {
                    source_metadata: comp.source_metadata,
                    dt: comp.dt,
                })),
                _ => Err(Error::Other(Some("More than one VMDTBO is selected"))),
            },
        )
    }

    /// Iterator over components.
    pub fn components(&self) -> impl Iterator<Item = &DtComponent<'a>> {
        self.components.iter()
    }

    /// Mutable iterator over components.
    pub fn components_mut(&mut self) -> impl Iterator<Item = &mut DtComponent<'a>> {
        self.components.iter_mut()
    }
}

#[cfg(test)]
pub(crate) mod test {
    use super::*;
    use crate::ops::test::FakeGblOps;

    #[test]
    fn test_components_registry_empty() {
        let registry = DtComponentsRegistry::new();

        assert_eq!(registry.components().count(), 0);
    }

    #[test]
    fn test_components_registry_append_component() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DtComponentsRegistry::new();

        registry
            .append(
                &mut gbl_ops,
                DtComponentSource::Boot,
                DtComponentType::BaseDt,
                &dt[..],
                &mut buffer,
            )
            .unwrap();

        assert_eq!(registry.components().count(), 1);

        let component = registry.components().next().unwrap();

        assert_eq!(
            component,
            &DtComponent {
                source_metadata: DtComponentSourceMetadata {
                    source: DtComponentSource::Boot,
                    source_index: 0,
                },
                component_type: DtComponentType::BaseDt,
                selection_metadata: None,
                dt: &dt[..],
                selected: false,
            }
        );
        assert!(component.component_type == DtComponentType::BaseDt);
    }

    #[test]
    fn test_components_registry_append_component_with_tail() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let dt_with_tail = [dt.clone(), vec![0; 100]].concat();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DtComponentsRegistry::new();

        registry
            .append(
                &mut gbl_ops,
                DtComponentSource::Boot,
                DtComponentType::BaseDt,
                &dt_with_tail[..],
                &mut buffer,
            )
            .unwrap();

        assert_eq!(registry.components().count(), 1);

        let component = registry.components().next().unwrap();

        assert_eq!(
            component,
            &DtComponent {
                source_metadata: DtComponentSourceMetadata {
                    source: DtComponentSource::Boot,
                    source_index: 0,
                },
                component_type: DtComponentType::BaseDt,
                selection_metadata: None,
                dt: &dt[..],
                selected: false,
            }
        );
        assert!(component.component_type == DtComponentType::BaseDt);
    }

    #[test]
    fn test_components_registry_append_too_many_components() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DtComponentsRegistry::new();

        let mut current_buffer = &mut buffer[..];
        // Fill the whole reserved space
        for _ in 0..MAXIMUM_DT_COMPONENTS {
            current_buffer = registry
                .append(
                    &mut gbl_ops,
                    DtComponentSource::Boot,
                    DtComponentType::BaseDt,
                    &dt[..],
                    current_buffer,
                )
                .unwrap();
        }

        assert_eq!(
            registry.append(
                &mut gbl_ops,
                DtComponentSource::Boot,
                DtComponentType::BaseDt,
                &dt[..],
                current_buffer
            ),
            Err(Error::Other(Some(MAXIMUM_DT_COMPONENTS_ERROR_MSG)))
        );
    }

    #[test]
    fn test_components_append_from_dttable() {
        let dttable = include_bytes!("../../libdttable/test/data/dttable.img").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut registry = DtComponentsRegistry::new();

        let table = DtTableImage::from_bytes(&dttable[..]).unwrap();
        registry.append_from_dttable(DtComponentSource::Dtbo, &table, &mut buffer[..]).unwrap();

        // Check data is loaded
        let components: Vec<_> = registry.components().cloned().collect();
        let expected_components: Vec<DtComponent> = table
            .entries()
            .enumerate()
            .map(|(i, e)| DtComponent {
                source_metadata: DtComponentSourceMetadata {
                    source: DtComponentSource::Dtbo,
                    source_index: i,
                },
                component_type: DtComponentType::Overlay,
                selection_metadata: Some(e.metadata),
                dt: e.dtb,
                selected: false,
            })
            .collect();
        assert_eq!(components, expected_components);

        // Check data is aligned
        registry.components().for_each(|c| assert!(c.dt.as_ptr().align_offset(FDT_ALIGNMENT) == 0));
    }

    #[test]
    fn test_components_append_from_dttable_invalid_totalsize() {
        let mut dttable = include_bytes!("../../libdttable/test/data/dttable.img").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut registry = DtComponentsRegistry::new();

        let table = DtTableImage::from_bytes(&dttable[..]).unwrap();
        let entry = table.nth_entry(0).unwrap();
        let entry_len = entry.dtb.len();
        let dtb_offset = entry.dtb.as_ptr() as usize - dttable.as_ptr() as usize;

        // Modify totalsize to be larger than entry length
        let invalid_size = (entry_len + 1) as u32;
        dttable[dtb_offset + 4..dtb_offset + 8].copy_from_slice(&invalid_size.to_be_bytes());

        // Re-parse the table image with modified buffer
        let table = DtTableImage::from_bytes(&dttable[..]).unwrap();

        // It should fail because totalsize > entry length
        assert!(registry
            .append_from_dttable(DtComponentSource::Dtbo, &table, &mut buffer[..])
            .is_err());
    }

    #[test]
    fn test_components_returns_selected() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DtComponentsRegistry::new();

        let sources = [
            (DtComponentSource::VendorBoot, DtComponentType::BaseDt),
            (DtComponentSource::Boot, DtComponentType::BaseDt),
            (DtComponentSource::Dtbo, DtComponentType::Overlay),
            (DtComponentSource::Dtbo, DtComponentType::Overlay),
            (DtComponentSource::Dtbo, DtComponentType::Overlay),
        ];
        let mut current_buffer = &mut buffer[..];
        for (source, component_type) in sources.iter() {
            current_buffer = registry
                .append(&mut gbl_ops, *source, *component_type, &dt, current_buffer)
                .unwrap();
        }

        // Select base device tree
        registry.components_mut().nth(0).unwrap().selected = true;
        // Select first overlay
        registry.components_mut().nth(2).unwrap().selected = true;
        // Select second overlay
        registry.components_mut().nth(3).unwrap().selected = true;

        // Expected selected data
        let expected_selected = SelectedDtComponents {
            base_dt: SelectedDtComponent {
                source_metadata: registry.components().nth(0).unwrap().source_metadata,
                dt: registry.components().nth(0).unwrap().dt,
            },
            vmdtbo: None,
            overlays: [
                SelectedDtComponent {
                    source_metadata: registry.components().nth(2).unwrap().source_metadata,
                    dt: registry.components().nth(2).unwrap().dt,
                },
                SelectedDtComponent {
                    source_metadata: registry.components().nth(3).unwrap().source_metadata,
                    dt: registry.components().nth(3).unwrap().dt,
                },
            ]
            .into_iter()
            .collect(),
        };

        assert_eq!(registry.into_selected().unwrap(), expected_selected);
    }

    #[test]
    fn test_components_returns_selected_no_overlays() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DtComponentsRegistry::new();

        let sources = [
            (DtComponentSource::VendorBoot, DtComponentType::BaseDt),
            (DtComponentSource::Boot, DtComponentType::BaseDt),
            (DtComponentSource::Dtbo, DtComponentType::Overlay),
            (DtComponentSource::Dtbo, DtComponentType::Overlay),
            (DtComponentSource::Dtbo, DtComponentType::Overlay),
        ];
        let mut current_buffer = &mut buffer[..];
        for (source, component_type) in sources.iter() {
            current_buffer = registry
                .append(&mut gbl_ops, *source, *component_type, &dt, current_buffer)
                .unwrap();
        }

        // Select base device tree
        registry.components_mut().nth(0).unwrap().selected = true;

        // Expected selected data
        let expected_selected = SelectedDtComponents {
            base_dt: SelectedDtComponent {
                source_metadata: registry.components().nth(0).unwrap().source_metadata,
                dt: registry.components().nth(0).unwrap().dt,
            },
            vmdtbo: None,
            overlays: ArrayVec::new(),
        };

        assert_eq!(registry.into_selected().unwrap(), expected_selected);
    }

    #[test]
    fn test_components_returns_selected_vmdtbo() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DtComponentsRegistry::new();

        let sources = [
            (DtComponentSource::VendorBoot, DtComponentType::BaseDt),
            (DtComponentSource::Dtbo, DtComponentType::PvmDeviceAssignmentOverlay),
        ];
        let mut current_buffer = &mut buffer[..];
        for (source, component_type) in sources.iter() {
            current_buffer = registry
                .append(&mut gbl_ops, *source, *component_type, &dt, current_buffer)
                .unwrap();
        }

        // Select base device tree
        registry.components_mut().nth(0).unwrap().selected = true;
        // Select VMDTBO
        registry.components_mut().nth(1).unwrap().selected = true;

        let expected_selected = SelectedDtComponents {
            base_dt: SelectedDtComponent {
                source_metadata: registry.components().nth(0).unwrap().source_metadata,
                dt: registry.components().nth(0).unwrap().dt,
            },
            vmdtbo: Some(SelectedDtComponent {
                source_metadata: registry.components().nth(1).unwrap().source_metadata,
                dt: registry.components().nth(1).unwrap().dt,
            }),
            overlays: ArrayVec::new(),
        };
        assert_eq!(registry.into_selected().unwrap(), expected_selected);
    }

    #[test]
    fn test_components_multiple_vmdtbos_failed() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DtComponentsRegistry::new();

        let sources = [
            (DtComponentSource::VendorBoot, DtComponentType::BaseDt),
            (DtComponentSource::Dtbo, DtComponentType::PvmDeviceAssignmentOverlay),
            (DtComponentSource::Dtbo, DtComponentType::PvmDeviceAssignmentOverlay),
        ];
        let mut current_buffer = &mut buffer[..];
        for (source, component_type) in sources.iter() {
            current_buffer = registry
                .append(&mut gbl_ops, *source, *component_type, &dt, current_buffer)
                .unwrap();
        }

        // Select base device tree
        registry.components_mut().nth(0).unwrap().selected = true;
        // Select 2 VMDTBOs
        registry.components_mut().nth(1).unwrap().selected = true;
        registry.components_mut().nth(2).unwrap().selected = true;

        assert!(registry.into_selected().is_err());
    }

    #[test]
    fn test_components_returns_no_base_device_tree_failed() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DtComponentsRegistry::new();

        let sources = [
            (DtComponentSource::VendorBoot, DtComponentType::BaseDt),
            (DtComponentSource::Boot, DtComponentType::BaseDt),
            (DtComponentSource::Dtbo, DtComponentType::Overlay),
            (DtComponentSource::Dtbo, DtComponentType::Overlay),
            (DtComponentSource::Dtbo, DtComponentType::Overlay),
        ];
        let mut current_buffer = &mut buffer[..];
        for (source, component_type) in sources.iter() {
            current_buffer = registry
                .append(&mut gbl_ops, *source, *component_type, &dt, current_buffer)
                .unwrap();
        }

        // Select first overlay
        registry.components_mut().nth(2).unwrap().selected = true;
        // Select second overlay
        registry.components_mut().nth(3).unwrap().selected = true;

        assert!(registry.into_selected().is_err());
    }

    #[test]
    fn test_components_returns_multiple_base_device_trees_failed() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DtComponentsRegistry::new();

        let sources = [
            (DtComponentSource::VendorBoot, DtComponentType::BaseDt),
            (DtComponentSource::Boot, DtComponentType::BaseDt),
            (DtComponentSource::Dtbo, DtComponentType::Overlay),
            (DtComponentSource::Dtbo, DtComponentType::Overlay),
            (DtComponentSource::Dtbo, DtComponentType::Overlay),
        ];
        let mut current_buffer = &mut buffer[..];
        for (source, component_type) in sources.iter() {
            current_buffer = registry
                .append(&mut gbl_ops, *source, *component_type, &dt, current_buffer)
                .unwrap();
        }

        // Select first base device tree
        registry.components_mut().nth(0).unwrap().selected = true;
        // Select second base device tree
        registry.components_mut().nth(1).unwrap().selected = true;

        assert!(registry.into_selected().is_err());
    }

    #[test]
    fn test_components_autoselect() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DtComponentsRegistry::new();

        let sources = [
            (DtComponentSource::VendorBoot, DtComponentType::BaseDt),
            (DtComponentSource::Dtbo, DtComponentType::Overlay),
            (DtComponentSource::Dtbo, DtComponentType::Overlay),
            (DtComponentSource::Dtbo, DtComponentType::Overlay),
        ];
        let mut current_buffer = &mut buffer[..];
        for (source, component_type) in sources.iter() {
            current_buffer = registry
                .append(&mut gbl_ops, *source, *component_type, &dt, current_buffer)
                .unwrap();
        }

        assert!(registry.autoselect().is_ok());

        // Expected auto selected data
        let expected_selected = SelectedDtComponents {
            base_dt: SelectedDtComponent {
                source_metadata: registry.components().nth(0).unwrap().source_metadata,
                dt: registry.components().nth(0).unwrap().dt,
            },
            vmdtbo: None,
            overlays: ArrayVec::new(),
        };

        assert_eq!(registry.into_selected().unwrap(), expected_selected);
    }

    #[test]
    fn test_components_autoselect_no_overlays() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DtComponentsRegistry::new();

        registry
            .append(
                &mut gbl_ops,
                DtComponentSource::VendorBoot,
                DtComponentType::BaseDt,
                &dt[..],
                &mut buffer,
            )
            .unwrap();

        assert!(registry.autoselect().is_ok());

        // Expected auto selected data
        let expected_selected = SelectedDtComponents {
            base_dt: SelectedDtComponent {
                source_metadata: registry.components().nth(0).unwrap().source_metadata,
                dt: registry.components().nth(0).unwrap().dt,
            },
            vmdtbo: None,
            overlays: ArrayVec::new(),
        };

        assert_eq!(registry.into_selected().unwrap(), expected_selected);
    }

    #[test]
    fn test_components_autoselect_multiple_base_device_trees_failed() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DtComponentsRegistry::new();

        let mut current_buffer = &mut buffer[..];
        current_buffer = registry
            .append(
                &mut gbl_ops,
                DtComponentSource::VendorBoot,
                DtComponentType::BaseDt,
                &dt[..],
                current_buffer,
            )
            .unwrap();
        registry
            .append(
                &mut gbl_ops,
                DtComponentSource::Boot,
                DtComponentType::BaseDt,
                &dt[..],
                current_buffer,
            )
            .unwrap();

        assert!(registry.autoselect().is_err());
    }

    #[test]
    fn test_components_autoselect_no_base_device_trees_failed() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DtComponentsRegistry::new();

        registry
            .append(
                &mut gbl_ops,
                DtComponentSource::Dtbo,
                DtComponentType::Overlay,
                &dt[..],
                &mut buffer,
            )
            .unwrap();

        assert!(registry.autoselect().is_err());
    }

    #[test]
    fn test_components_append_from_multifd() {
        let half = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let dt = [half.clone(), half].concat();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DtComponentsRegistry::new();

        registry
            .append(
                &mut gbl_ops,
                DtComponentSource::VendorBoot,
                DtComponentType::BaseDt,
                &dt[..],
                &mut buffer,
            )
            .unwrap();

        assert_eq!(registry.components().count(), 2);
    }

    #[test]
    fn test_components_append_from_multifd_with_tail() {
        let half = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let dt = [half.clone(), half, vec![0; 100]].concat();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DtComponentsRegistry::new();

        registry
            .append(
                &mut gbl_ops,
                DtComponentSource::VendorBoot,
                DtComponentType::BaseDt,
                &dt[..],
                &mut buffer,
            )
            .unwrap();

        assert_eq!(registry.components().count(), 2);
    }
}
