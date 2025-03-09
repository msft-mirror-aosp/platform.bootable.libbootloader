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

use crate::{constants::FDT_ALIGNMENT, gbl_print, gbl_println, GblOps};
use arrayvec::ArrayVec;
use dttable::{DtTableImage, DtTableMetadata};
use fdt::{Fdt, FdtHeader, FDT_HEADER_SIZE};
use liberror::{Error, Result};
use libutils::aligned_subslice;

/// Maximum amount of device tree components GBL can handle to select from.
/// TODO(b/353272981): Use dynamic memory to store components. Currently
/// DeviceTreeComponentsRegistry takes about 18kb of stack, which can be slow and dangerous.
pub const MAXIMUM_DEVICE_TREE_COMPONENTS: usize = 256;
/// Error message to fail in case of unsupported amount of device tree components.
pub const MAXIMUM_DEVICE_TREE_COMPONENTS_ERROR_MSG: &str =
    "At most 256 device components are supported to build the final one";

/// The source device tree component is coming from.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum DeviceTreeComponentSource {
    /// Loaded from Boot partition.
    Boot,
    /// Loaded from Vendor Boot partition.
    VendorBoot,
    /// Loaded from DTB partition.
    Dtb(DtTableMetadata),
    /// Loaded from DTBO partition.
    Dtbo(DtTableMetadata),
}

impl core::fmt::Display for DeviceTreeComponentSource {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DeviceTreeComponentSource::Boot => write!(f, "Boot"),
            DeviceTreeComponentSource::VendorBoot => write!(f, "VendorBoot"),
            DeviceTreeComponentSource::Dtb(_) => write!(f, "Dtb"),
            DeviceTreeComponentSource::Dtbo(_) => write!(f, "Dtbo"),
        }
    }
}

/// Device tree component (device tree or overlay) to build the final one.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct DeviceTreeComponent<'a> {
    /// Source the component is loaded from.
    pub source: DeviceTreeComponentSource,
    /// Device tree component payload. Must be 8 bytes aligned.
    pub dt: &'a [u8],
    /// Device tree component is selected.
    pub selected: bool,
}

/// Maintain, select and get the device tree components to build the final device tree.
pub struct DeviceTreeComponentsRegistry<'a> {
    components: ArrayVec<DeviceTreeComponent<'a>, MAXIMUM_DEVICE_TREE_COMPONENTS>,
    /// `selected_overlays` array is used to return selected overlays as a sequential reference
    /// slice. It must only be used within the `selected()` method and must not be assumed
    /// valid elsewhere.
    selected_overlays: ArrayVec<&'a [u8], MAXIMUM_DEVICE_TREE_COMPONENTS>,
}

impl<'a> DeviceTreeComponent<'a> {
    /// Whether device tree component is base device tree or overlay.
    pub fn is_base_device_tree(&self) -> bool {
        matches!(
            self.source,
            DeviceTreeComponentSource::Boot
                | DeviceTreeComponentSource::VendorBoot
                | DeviceTreeComponentSource::Dtb(_)
        )
    }
}

impl<'a> DeviceTreeComponentsRegistry<'a> {
    /// Create new empty DeviceTreeComponentsRegistry.
    pub fn new() -> Self {
        DeviceTreeComponentsRegistry {
            components: ArrayVec::new(),
            selected_overlays: ArrayVec::new(),
        }
    }

    /// Load device tree components from a dt table image. Ensure components are 8 bytes
    /// aligned by using provided buffer to cut from. Returns remain buffer.
    pub fn append_from_dttable<'b>(
        &mut self,
        is_dtb: bool,
        dttable: &DtTableImage<'b>,
        buffer: &'a mut [u8],
    ) -> Result<&'a mut [u8]> {
        if dttable.entries_count() > self.components.remaining_capacity() {
            return Err(Error::Other(Some(MAXIMUM_DEVICE_TREE_COMPONENTS_ERROR_MSG)));
        }

        let mut remains = buffer;
        for entry in dttable.entries() {
            // TODO(b/374336105): Find a better way to handle 8-bytes alignment rather than copy.
            let (aligned_buffer, rest) = aligned_subslice(remains, FDT_ALIGNMENT)?
                .split_at_mut_checked(entry.dtb.len())
                .ok_or(Error::Other(Some(
                    "Provided buffer is too small to ensure dttable entry is aligned",
                )))?;
            aligned_buffer.copy_from_slice(entry.dtb);

            self.components.push(DeviceTreeComponent {
                source: if is_dtb {
                    DeviceTreeComponentSource::Dtb(entry.metadata)
                } else {
                    DeviceTreeComponentSource::Dtbo(entry.metadata)
                },
                dt: aligned_buffer,
                selected: false,
            });

            remains = rest;
        }

        Ok(remains)
    }

    /// Load device tree components from a dtbo image. Ensure components are 8 bytes
    /// aligned by using provided `buffer` to cut from. Returns remain buffer.
    pub fn append_from_dtbo<'b>(
        &mut self,
        dttable: &DtTableImage<'b>,
        buffer: &'a mut [u8],
    ) -> Result<&'a mut [u8]> {
        self.append_from_dttable(false, dttable, buffer)
    }

    /// Append additional device trees from the buffer, where they are stored sequentially.
    /// Ensure components are 8 bytes aligned by using provided buffer to cut from. Returns remain
    /// buffer.
    /// TODO(b/363244924): Remove after partners migrated to DTB.
    fn append_from_multifdt_buffer<'b, 'c>(
        &mut self,
        ops: &mut impl GblOps<'b, 'c>,
        source: DeviceTreeComponentSource,
        data: &'a [u8],
        buffer: &'a mut [u8],
    ) -> Result<&'a mut [u8]> {
        let mut components_added = 0;
        let mut data_remains = data;
        let mut buffer_remains = buffer;
        while data_remains.len() >= FDT_HEADER_SIZE {
            let aligned_buffer = aligned_subslice(buffer_remains, FDT_ALIGNMENT)?;

            let header_slice = aligned_buffer.get_mut(..FDT_HEADER_SIZE).ok_or(Error::Other(
                Some("Provided buffer is too small to ensure multidt entry is aligned"),
            ))?;
            // Fdt header must be aligned, so copy to an aligned buffer.
            header_slice.copy_from_slice(&data_remains[..FDT_HEADER_SIZE]);
            let next_fdt_size = FdtHeader::from_bytes_ref(header_slice)?.totalsize();

            if self.components.is_full() {
                return Err(Error::Other(Some(MAXIMUM_DEVICE_TREE_COMPONENTS_ERROR_MSG)));
            }

            // Cut fdt and temporary buffers to make sure result fdt is 8 bytes aligned
            let (data_buffer, data_buffer_remains) =
                data_remains.split_at_checked(next_fdt_size).ok_or(Error::Other(Some(
                    "Multidt structure has a valid header but doesn't have a device tree payload",
                )))?;
            let (aligned_buffer, aligned_buffer_remains) =
                aligned_buffer.split_at_mut_checked(next_fdt_size).ok_or(Error::Other(Some(
                    "Provided buffer is too small to ensure multidt entry is aligned",
                )))?;
            aligned_buffer.copy_from_slice(data_buffer);

            Fdt::new(&aligned_buffer)?;
            self.components.push(DeviceTreeComponent {
                source: source,
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
                source,
            );
        }

        Ok(buffer_remains)
    }

    /// Append device tree components from provided buffer prefix. `fdt` must be a 8 bytes aligned
    /// valid fdt buffer. `fdt` may also have multiple fdt buffers placed sequentially. Ensure each
    /// of such components are 8 bytes aligned by using provided `buffer` to cut from. Returns
    /// remain buffer.
    /// TODO(b/363244924): Remove multiple fdt support after partners migrated to DTB.
    pub fn append<'b, 'c>(
        &mut self,
        ops: &mut impl GblOps<'b, 'c>,
        source: DeviceTreeComponentSource,
        fdt: &'a [u8],
        buffer: &'a mut [u8],
    ) -> Result<&'a mut [u8]> {
        if self.components.is_full() {
            return Err(Error::Other(Some(MAXIMUM_DEVICE_TREE_COMPONENTS_ERROR_MSG)));
        }

        let header = FdtHeader::from_bytes_ref(fdt)?;
        let (fdt_buffer, fdt_remains) = fdt.split_at(header.totalsize());
        self.components.push(DeviceTreeComponent {
            source: source,
            dt: fdt_buffer,
            selected: false,
        });

        // TODO(b/363244924): Remove after partners migrated to DTB.
        self.append_from_multifdt_buffer(ops, source, fdt_remains, buffer)
    }

    /// Default implementation of selected logic in case external one isn't provided.
    /// Only base device tree is supported to choose from. Otherwise fail. No overlays will be
    /// selected.
    pub fn autoselect(&mut self) -> Result<()> {
        let base_device_tree_count =
            self.components.iter().filter(|component| component.is_base_device_tree()).count();
        if base_device_tree_count > 1 {
            return Err(Error::Other(Some(
                "Base device tree autoselection isn't supported if multiple device trees are \
                provided",
            )));
        }

        let base = self
            .components
            .iter_mut()
            .find(|component| component.is_base_device_tree())
            .ok_or(Error::Other(Some("0 base device trees to autoselect from")))?;
        base.selected = true;

        Ok(())
    }

    /// Return selected base device tree and overlays to apply. Fail in case selection isn't
    /// correct. For correctness rules refer to `GblOps.select_device_trees` requirements.
    pub fn selected(&mut self) -> Result<(&[u8], &[&[u8]])> {
        let base_device_tree_count = self
            .components
            .iter()
            .filter(|component| component.is_base_device_tree() && component.selected)
            .count();
        if base_device_tree_count > 1 {
            return Err(Error::Other(Some("More than 1 base device tree is selected")));
        }

        let base = self
            .components
            .iter()
            .find(|component| component.is_base_device_tree() && component.selected)
            .ok_or(Error::Other(Some("0 base device trees are selected")))?;

        self.selected_overlays = self
            .components
            .iter()
            .filter(|component| !component.is_base_device_tree() && component.selected)
            .map(|component| component.dt)
            .collect();

        Ok((base.dt, &self.selected_overlays[..]))
    }

    /// Iterator over components.
    pub fn components(&self) -> impl Iterator<Item = &DeviceTreeComponent<'a>> {
        self.components.iter()
    }

    /// Mutable iterator over components.
    pub fn components_mut(&mut self) -> impl Iterator<Item = &mut DeviceTreeComponent<'a>> {
        self.components.iter_mut()
    }
}

#[cfg(test)]
pub(crate) mod test {
    use super::*;
    use crate::ops::test::FakeGblOps;

    #[test]
    fn test_components_registry_empty() {
        let registry = DeviceTreeComponentsRegistry::new();

        assert_eq!(registry.components().count(), 0);
    }

    #[test]
    fn test_components_registry_append_component() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DeviceTreeComponentsRegistry::new();

        registry
            .append(&mut gbl_ops, DeviceTreeComponentSource::Boot, &dt[..], &mut buffer)
            .unwrap();

        assert_eq!(registry.components().count(), 1);

        let component = registry.components().next().unwrap();

        assert_eq!(
            component,
            &DeviceTreeComponent {
                source: DeviceTreeComponentSource::Boot,
                dt: &dt[..],
                selected: false,
            }
        );
        assert!(component.is_base_device_tree());
    }

    #[test]
    fn test_components_registry_append_too_many_components() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DeviceTreeComponentsRegistry::new();

        let mut current_buffer = &mut buffer[..];
        // Fill the whole reserved space
        for _ in 0..MAXIMUM_DEVICE_TREE_COMPONENTS {
            current_buffer = registry
                .append(&mut gbl_ops, DeviceTreeComponentSource::Boot, &dt[..], current_buffer)
                .unwrap();
        }

        assert_eq!(
            registry.append(&mut gbl_ops, DeviceTreeComponentSource::Boot, &dt[..], current_buffer),
            Err(Error::Other(Some(MAXIMUM_DEVICE_TREE_COMPONENTS_ERROR_MSG)))
        );
    }

    #[test]
    fn test_components_append_from_dtbo() {
        let dttable = include_bytes!("../../libdttable/test/data/dttable.img").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut registry = DeviceTreeComponentsRegistry::new();

        let table = DtTableImage::from_bytes(&dttable[..]).unwrap();
        registry.append_from_dtbo(&table, &mut buffer[..]).unwrap();

        // Check data is loaded
        let components: Vec<_> = registry.components().cloned().collect();
        let expected_components: Vec<DeviceTreeComponent> = table
            .entries()
            .map(|e| DeviceTreeComponent {
                source: DeviceTreeComponentSource::Dtbo(e.metadata),
                dt: e.dtb,
                selected: false,
            })
            .collect();
        assert_eq!(components, expected_components);

        // Check data is aligned
        registry.components().for_each(|c| assert!(c.dt.as_ptr().align_offset(FDT_ALIGNMENT) == 0));
    }

    #[test]
    fn test_components_returns_selected() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DeviceTreeComponentsRegistry::new();

        let sources = [
            DeviceTreeComponentSource::VendorBoot,
            DeviceTreeComponentSource::Boot,
            DeviceTreeComponentSource::Dtbo(Default::default()),
            DeviceTreeComponentSource::Dtbo(Default::default()),
            DeviceTreeComponentSource::Dtbo(Default::default()),
        ];
        let mut current_buffer = &mut buffer[..];
        for source in sources.iter() {
            current_buffer = registry.append(&mut gbl_ops, *source, &dt, current_buffer).unwrap();
        }

        // Select base device tree
        registry.components_mut().nth(1).unwrap().selected = true;
        // Select first overlay
        registry.components_mut().nth(2).unwrap().selected = true;
        // Select second overlay
        registry.components_mut().nth(3).unwrap().selected = true;

        let expected_overlays =
            &[registry.components().nth(2).unwrap().dt, registry.components().nth(3).unwrap().dt];
        // Expected selected data
        let expected_selected = (registry.components().nth(1).unwrap().dt, &expected_overlays[..]);

        assert_eq!(registry.selected().unwrap(), expected_selected);
    }

    #[test]
    fn test_components_returns_selected_no_overlays() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DeviceTreeComponentsRegistry::new();

        let sources = [
            DeviceTreeComponentSource::VendorBoot,
            DeviceTreeComponentSource::Boot,
            DeviceTreeComponentSource::Dtbo(Default::default()),
            DeviceTreeComponentSource::Dtbo(Default::default()),
            DeviceTreeComponentSource::Dtbo(Default::default()),
        ];
        let mut current_buffer = &mut buffer[..];
        for source in sources.iter() {
            current_buffer = registry.append(&mut gbl_ops, *source, &dt, current_buffer).unwrap();
        }

        // Select base device tree
        registry.components_mut().nth(1).unwrap().selected = true;

        // Expected selected data
        let expected_selected = (registry.components().nth(1).unwrap().dt, &[][..]);

        assert_eq!(registry.selected().unwrap(), expected_selected);
    }

    #[test]
    fn test_components_returns_no_base_device_tree_failed() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DeviceTreeComponentsRegistry::new();

        let sources = [
            DeviceTreeComponentSource::VendorBoot,
            DeviceTreeComponentSource::Boot,
            DeviceTreeComponentSource::Dtbo(Default::default()),
            DeviceTreeComponentSource::Dtbo(Default::default()),
            DeviceTreeComponentSource::Dtbo(Default::default()),
        ];
        let mut current_buffer = &mut buffer[..];
        for source in sources.iter() {
            current_buffer = registry.append(&mut gbl_ops, *source, &dt, current_buffer).unwrap();
        }

        // Select first overlay
        registry.components_mut().nth(2).unwrap().selected = true;
        // Select second overlay
        registry.components_mut().nth(3).unwrap().selected = true;

        assert!(registry.selected().is_err());
    }

    #[test]
    fn test_components_returns_multiple_base_device_trees_failed() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DeviceTreeComponentsRegistry::new();

        let sources = [
            DeviceTreeComponentSource::VendorBoot,
            DeviceTreeComponentSource::Boot,
            DeviceTreeComponentSource::Dtbo(Default::default()),
            DeviceTreeComponentSource::Dtbo(Default::default()),
            DeviceTreeComponentSource::Dtbo(Default::default()),
        ];
        let mut current_buffer = &mut buffer[..];
        for source in sources.iter() {
            current_buffer = registry.append(&mut gbl_ops, *source, &dt, current_buffer).unwrap();
        }

        // Select first base device tree
        registry.components_mut().nth(0).unwrap().selected = true;
        // Select second base device tree
        registry.components_mut().nth(1).unwrap().selected = true;

        assert!(registry.selected().is_err());
    }

    #[test]
    fn test_components_autoselect() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DeviceTreeComponentsRegistry::new();

        let sources = [
            DeviceTreeComponentSource::VendorBoot,
            DeviceTreeComponentSource::Dtbo(Default::default()),
            DeviceTreeComponentSource::Dtbo(Default::default()),
            DeviceTreeComponentSource::Dtbo(Default::default()),
        ];
        let mut current_buffer = &mut buffer[..];
        for source in sources.iter() {
            current_buffer = registry.append(&mut gbl_ops, *source, &dt, current_buffer).unwrap();
        }

        assert!(registry.autoselect().is_ok());

        // Expected auto selected data
        let expected_selected = (registry.components().nth(0).unwrap().dt, &[][..]);

        assert_eq!(registry.selected().unwrap(), expected_selected);
    }

    #[test]
    fn test_components_autoselect_no_overlays() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DeviceTreeComponentsRegistry::new();

        registry
            .append(&mut gbl_ops, DeviceTreeComponentSource::VendorBoot, &dt[..], &mut buffer)
            .unwrap();

        assert!(registry.autoselect().is_ok());

        // Expected auto selected data
        let expected_selected = (registry.components().nth(0).unwrap().dt, &[][..]);

        assert_eq!(registry.selected().unwrap(), expected_selected);
    }

    #[test]
    fn test_components_autoselect_multiple_base_device_trees_failed() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DeviceTreeComponentsRegistry::new();

        let mut current_buffer = &mut buffer[..];
        current_buffer = registry
            .append(&mut gbl_ops, DeviceTreeComponentSource::VendorBoot, &dt[..], current_buffer)
            .unwrap();
        registry
            .append(&mut gbl_ops, DeviceTreeComponentSource::Boot, &dt[..], current_buffer)
            .unwrap();

        assert!(registry.autoselect().is_err());
    }

    #[test]
    fn test_components_autoselect_no_base_device_trees_failed() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut buffer = vec![0u8; 2 * 1024 * 1024]; // 2 MB
        let mut gbl_ops = FakeGblOps::new(&[]);
        let mut registry = DeviceTreeComponentsRegistry::new();

        registry
            .append(
                &mut gbl_ops,
                DeviceTreeComponentSource::Dtbo(Default::default()),
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
        let mut registry = DeviceTreeComponentsRegistry::new();

        registry
            .append(&mut gbl_ops, DeviceTreeComponentSource::VendorBoot, &dt[..], &mut buffer)
            .unwrap();

        assert_eq!(registry.components().count(), 2);
    }
}
