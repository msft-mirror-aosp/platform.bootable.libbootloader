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

use arrayvec::ArrayVec;
use dttable::{DtTableImage, DtTableMetadata};
use fdt::Fdt;
use liberror::{Error, Result};
use libutils::aligned_subslice;

/// Device tree alignment.
pub const FDT_ALIGNMENT: usize = 8;
/// Maximum amount of device tree components GBL can handle to select from.
pub const MAXIMUM_DEVICE_TREE_COMPONENTS: usize = 32;
/// Error message to fail in case of unsupported amount of device tree components.
pub const MAXIMUM_DEVICE_TREE_COMPONENTS_ERROR_MSG: &str =
    "At most 32 device components are supported to build the final one";

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
    fn append_from_dttable<'b>(
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
            let (aligned_buffer, rest) =
                aligned_subslice(remains, FDT_ALIGNMENT)?.split_at_mut(entry.dtb.len());
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

    /// Load device tree components from a dtbo image.
    pub fn append_from_dtbo<'b>(
        &mut self,
        dttable: &DtTableImage<'b>,
        buffer: &'a mut [u8],
    ) -> Result<&'a mut [u8]> {
        self.append_from_dttable(false, dttable, buffer)
    }

    /// Append device tree component from provided buffer prefix. `data` must be a 8 bytes aligned
    /// valid fdt buffer.
    pub fn append(&mut self, source: DeviceTreeComponentSource, data: &'a [u8]) -> Result<()> {
        if self.components.is_full() {
            return Err(Error::Other(Some(MAXIMUM_DEVICE_TREE_COMPONENTS_ERROR_MSG)));
        }

        let fdt = Fdt::new(data)?;
        self.components.push(DeviceTreeComponent {
            source: source,
            dt: &data[..fdt.size()?],
            selected: false,
        });

        Ok(())
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

    #[test]
    fn test_components_registry_empty() {
        let registry = DeviceTreeComponentsRegistry::new();

        assert_eq!(registry.components().count(), 0);
    }

    #[test]
    fn test_components_registry_append_component() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut registry = DeviceTreeComponentsRegistry::new();
        registry.append(DeviceTreeComponentSource::Boot, &dt[..]).unwrap();

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
        let mut registry = DeviceTreeComponentsRegistry::new();

        // Fill the whole reserved space
        for i in 0..MAXIMUM_DEVICE_TREE_COMPONENTS {
            registry.append(DeviceTreeComponentSource::Boot, &dt[..]).unwrap();
        }

        assert_eq!(
            registry.append(DeviceTreeComponentSource::Boot, &dt[..]),
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
        let mut registry = DeviceTreeComponentsRegistry::new();

        registry.append(DeviceTreeComponentSource::VendorBoot, &dt[..]).unwrap();
        registry.append(DeviceTreeComponentSource::Boot, &dt[..]).unwrap();
        registry.append(DeviceTreeComponentSource::Dtbo(Default::default()), &dt[..]).unwrap();
        registry.append(DeviceTreeComponentSource::Dtbo(Default::default()), &dt[..]).unwrap();
        registry.append(DeviceTreeComponentSource::Dtbo(Default::default()), &dt[..]).unwrap();

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
        let mut registry = DeviceTreeComponentsRegistry::new();

        registry.append(DeviceTreeComponentSource::VendorBoot, &dt[..]).unwrap();
        registry.append(DeviceTreeComponentSource::Boot, &dt[..]).unwrap();
        registry.append(DeviceTreeComponentSource::Dtbo(Default::default()), &dt[..]).unwrap();
        registry.append(DeviceTreeComponentSource::Dtbo(Default::default()), &dt[..]).unwrap();
        registry.append(DeviceTreeComponentSource::Dtbo(Default::default()), &dt[..]).unwrap();

        // Select base device tree
        registry.components_mut().nth(1).unwrap().selected = true;

        // Expected selected data
        let expected_selected = (registry.components().nth(1).unwrap().dt, &[][..]);

        assert_eq!(registry.selected().unwrap(), expected_selected);
    }

    #[test]
    fn test_components_returns_no_base_device_tree_failed() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut registry = DeviceTreeComponentsRegistry::new();

        registry.append(DeviceTreeComponentSource::VendorBoot, &dt[..]).unwrap();
        registry.append(DeviceTreeComponentSource::Boot, &dt[..]).unwrap();
        registry.append(DeviceTreeComponentSource::Dtbo(Default::default()), &dt[..]).unwrap();
        registry.append(DeviceTreeComponentSource::Dtbo(Default::default()), &dt[..]).unwrap();
        registry.append(DeviceTreeComponentSource::Dtbo(Default::default()), &dt[..]).unwrap();

        // Select first overlay
        registry.components_mut().nth(2).unwrap().selected = true;
        // Select second overlay
        registry.components_mut().nth(3).unwrap().selected = true;

        assert!(registry.selected().is_err());
    }

    #[test]
    fn test_components_returns_multiple_base_device_trees_failed() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut registry = DeviceTreeComponentsRegistry::new();

        registry.append(DeviceTreeComponentSource::VendorBoot, &dt[..]).unwrap();
        registry.append(DeviceTreeComponentSource::Boot, &dt[..]).unwrap();
        registry.append(DeviceTreeComponentSource::Dtbo(Default::default()), &dt[..]).unwrap();
        registry.append(DeviceTreeComponentSource::Dtbo(Default::default()), &dt[..]).unwrap();
        registry.append(DeviceTreeComponentSource::Dtbo(Default::default()), &dt[..]).unwrap();

        // Select first base device tree
        registry.components_mut().nth(0).unwrap().selected = true;
        // Select second base device tree
        registry.components_mut().nth(1).unwrap().selected = true;

        assert!(registry.selected().is_err());
    }

    #[test]
    fn test_components_autoselect() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut registry = DeviceTreeComponentsRegistry::new();

        registry.append(DeviceTreeComponentSource::VendorBoot, &dt[..]).unwrap();
        registry.append(DeviceTreeComponentSource::Dtbo(Default::default()), &dt[..]).unwrap();
        registry.append(DeviceTreeComponentSource::Dtbo(Default::default()), &dt[..]).unwrap();
        registry.append(DeviceTreeComponentSource::Dtbo(Default::default()), &dt[..]).unwrap();

        assert!(registry.autoselect().is_ok());

        // Expected auto selected data
        let expected_selected = (registry.components().nth(0).unwrap().dt, &[][..]);

        assert_eq!(registry.selected().unwrap(), expected_selected);
    }

    #[test]
    fn test_components_autoselect_no_overlays() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut registry = DeviceTreeComponentsRegistry::new();

        registry.append(DeviceTreeComponentSource::VendorBoot, &dt[..]).unwrap();

        assert!(registry.autoselect().is_ok());

        // Expected auto selected data
        let expected_selected = (registry.components().nth(0).unwrap().dt, &[][..]);

        assert_eq!(registry.selected().unwrap(), expected_selected);
    }

    #[test]
    fn test_components_autoselect_multiple_base_device_trees_failed() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut registry = DeviceTreeComponentsRegistry::new();

        registry.append(DeviceTreeComponentSource::VendorBoot, &dt[..]).unwrap();
        registry.append(DeviceTreeComponentSource::Boot, &dt[..]).unwrap();

        assert!(registry.autoselect().is_err());
    }

    #[test]
    fn test_components_autoselect_no_base_device_trees_failed() {
        let dt = include_bytes!("../../libfdt/test/data/base.dtb").to_vec();
        let mut registry = DeviceTreeComponentsRegistry::new();

        registry.append(DeviceTreeComponentSource::Dtbo(Default::default()), &dt[..]).unwrap();

        assert!(registry.autoselect().is_err());
    }
}
