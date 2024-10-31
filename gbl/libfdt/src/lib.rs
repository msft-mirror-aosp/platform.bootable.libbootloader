// Copyright 2023-2024, The Android Open Source Project
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

//! This library provides a few wrapper APIs for libfdt_c

#![cfg_attr(not(test), no_std)]

extern crate alloc;
extern crate libc;

use arrayvec::ArrayVec;
use core::ffi::{c_int, CStr};
use core::mem::size_of;
use core::slice::{from_raw_parts, from_raw_parts_mut};
use liberror::{Error, Result};
use libfdt_bindgen::{
    fdt_add_subnode_namelen, fdt_del_node, fdt_get_property, fdt_header, fdt_move, fdt_setprop,
    fdt_setprop_placeholder, fdt_strerror, fdt_subnode_offset_namelen,
};
use libufdt_bindgen::ufdt_apply_multioverlay;
use zerocopy::{AsBytes, FromBytes, FromZeroes, Ref};

/// Fdt header structure size.
pub const FDT_HEADER_SIZE: usize = size_of::<FdtHeader>();
const MAXIMUM_OVERLAYS_TO_APPLY: usize = 16;
const MAXIMUM_OVERLAYS_ERROR_MSG: &str = "At most 16 overlays are supported to apply at a time";

/// Convert libfdt_c error code to Result
fn map_result(code: c_int) -> Result<c_int> {
    match code {
        // SAFETY: Static null terminated string returned from libfdt_c API.
        v if v < 0 => {
            Err(Error::Other(Some(unsafe { CStr::from_ptr(fdt_strerror(v)).to_str().unwrap() })))
        }
        v => Ok(v),
    }
}

/// Convert libufdt_c error code to Result
fn map_result_libufdt(code: c_int) -> Result<c_int> {
    match code {
        v if v < 0 => Err(Error::Other(Some("Failed to execute libufdt call"))),
        v => Ok(v),
    }
}

/// Check header.
fn fdt_check_header(header: &[u8]) -> Result<()> {
    // SAFETY:
    // `fdt_check_header` is only access the memory pointed to by `header` during this call and
    // not store the pointer for later use. `header` remains valid for the duration of this call.
    map_result(unsafe { libfdt_bindgen::fdt_check_header(header.as_ptr() as *const _) })?;
    Ok(())
}

/// Check header and verified that totalsize does not exceed buffer size.
fn fdt_check_buffer(fdt: &[u8]) -> Result<()> {
    match FdtHeader::from_bytes_ref(fdt)?.totalsize() <= fdt.len() {
        true => Ok(()),
        _ => Err(Error::InvalidInput),
    }
}

/// Wrapper of fdt_add_subnode_namelen()
fn fdt_add_subnode(fdt: &mut [u8], parent: c_int, name: &str) -> Result<c_int> {
    // SAFETY: API from libfdt_c.
    map_result(unsafe {
        fdt_add_subnode_namelen(
            fdt.as_mut_ptr() as *mut _,
            parent,
            name.as_ptr() as *const _,
            name.len().try_into()?,
        )
    })
}

/// Wrapper of fdt_subnode_offset_namelen()
fn fdt_subnode_offset(fdt: &[u8], parent: c_int, name: &str) -> Result<c_int> {
    // SAFETY: API from libfdt_c.
    map_result(unsafe {
        fdt_subnode_offset_namelen(
            fdt.as_ptr() as *const _,
            parent,
            name.as_ptr() as *const _,
            name.len().try_into()?,
        )
    })
}

/// Rust wrapper for the FDT header data.
#[repr(transparent)]
#[derive(Debug, Copy, Clone, AsBytes, FromBytes, FromZeroes, PartialEq)]
pub struct FdtHeader(fdt_header);

impl FdtHeader {
    /// Return the totalsize field.
    pub fn totalsize(&self) -> usize {
        u32::from_be(self.0.totalsize) as usize
    }

    /// Return the minimal size of the FDT. Disregard trailing free space.
    pub fn actual_size(&self) -> usize {
        u32::from_be(self.0.off_dt_strings)
            .checked_add(u32::from_be(self.0.size_dt_strings))
            .unwrap() as usize
    }

    /// Update the totalsize field.
    pub fn set_totalsize(&mut self, value: u32) {
        self.0.totalsize = value.to_be();
    }

    /// Cast a bytes into a reference of FDT header
    pub fn from_bytes_ref(buffer: &[u8]) -> Result<&FdtHeader> {
        fdt_check_header(buffer)?;

        Ok(Ref::<_, FdtHeader>::new_from_prefix(buffer)
            .ok_or(Error::BufferTooSmall(Some(FDT_HEADER_SIZE)))?
            .0
            .into_ref())
    }

    /// Cast a bytes into a mutable reference of FDT header.
    pub fn from_bytes_mut(buffer: &mut [u8]) -> Result<&mut FdtHeader> {
        fdt_check_header(buffer)?;

        Ok(Ref::<_, FdtHeader>::new_from_prefix(buffer)
            .ok_or(Error::BufferTooSmall(Some(FDT_HEADER_SIZE)))?
            .0
            .into_mut())
    }

    /// Get FDT header and raw bytes from a raw pointer.
    ///
    /// Caller should guarantee that
    ///   1. `ptr` contains a valid FDT.
    ///   2. The buffer remains valid as long as the returned references are in use.
    pub unsafe fn from_raw(ptr: *const u8) -> Result<(&'static FdtHeader, &'static [u8])> {
        // SAFETY: By safety requirement of this function, `ptr` points to a valid FDT and remains
        // valid when in use.
        unsafe {
            let header_bytes = from_raw_parts(ptr, FDT_HEADER_SIZE);
            let header = Self::from_bytes_ref(header_bytes)?;
            Ok((header, from_raw_parts(ptr, header.totalsize())))
        }
    }
}

/// Object for managing an FDT.
pub struct Fdt<T>(T);

/// Read only APIs.
impl<'a, T: AsRef<[u8]> + 'a> Fdt<T> {
    /// Creates a new [Fdt] wrapping the contents of `init`.
    pub fn new(init: T) -> Result<Self> {
        fdt_check_buffer(init.as_ref())?;
        Ok(Fdt(init))
    }

    /// Returns the [FdtHeader], or an error if the underlying buffer was invalid.
    pub fn header_ref(&self) -> Result<&FdtHeader> {
        FdtHeader::from_bytes_ref(self.0.as_ref())
    }

    /// Returns the totalsize according to FDT header. Trailing free space is included.
    pub fn size(&self) -> Result<usize> {
        Ok(self.header_ref()?.totalsize())
    }

    /// Get a property from an existing node.
    pub fn get_property(&self, path: &str, name: &CStr) -> Result<&'a [u8]> {
        let node = self.find_node(path)?;
        let mut len: c_int = 0;
        // SAFETY: API from libfdt_c.
        let ptr = unsafe {
            fdt_get_property(
                self.0.as_ref().as_ptr() as *const _,
                node,
                name.to_bytes_with_nul().as_ptr() as *const _,
                &mut len as *mut _,
            )
        };
        // SAFETY: Buffer returned by API from libfdt_c.
        match unsafe { ptr.as_ref() } {
            // SAFETY: Buffer returned by API from libfdt_c.
            Some(v) => Ok(unsafe {
                from_raw_parts(
                    v.data.as_ptr() as *const u8,
                    u32::from_be(v.len).try_into().or(Err(Error::Other(None)))?,
                )
            }),
            _ => Err(map_result(len).unwrap_err()),
        }
    }

    /// Find the offset of a node by a given node path.
    fn find_node(&self, path: &str) -> Result<c_int> {
        let mut curr: c_int = 0;
        for name in path.split('/') {
            if name.len() == 0 {
                continue;
            }
            curr = fdt_subnode_offset(self.0.as_ref(), curr, name)?;
        }
        Ok(curr)
    }
}

/// APIs when data can be modified.
impl<T: AsMut<[u8]> + AsRef<[u8]>> Fdt<T> {
    /// Creates a new mut [Fdt] wrapping the contents of `init`.
    pub fn new_mut(init: T) -> Result<Self> {
        let mut fdt = Fdt::new(init)?;
        let new_size: u32 = fdt.as_mut().len().try_into().or(Err(Error::Other(None)))?;
        fdt.header_mut()?.set_totalsize(new_size);
        Ok(fdt)
    }

    /// Creates a mutable [Fdt] copied from `init`.
    pub fn new_from_init(mut fdt: T, init: &[u8]) -> Result<Self> {
        fdt_check_buffer(init)?;
        // SAFETY: API from libfdt_c.
        map_result(unsafe {
            fdt_move(
                init.as_ptr() as *const _,
                fdt.as_mut().as_ptr() as *mut _,
                fdt.as_mut().len().try_into().or(Err(Error::Other(None)))?,
            )
        })?;
        let new_size: u32 = fdt.as_mut().len().try_into().or(Err(Error::Other(None)))?;
        let mut ret = Fdt::new(fdt)?;
        ret.header_mut()?.set_totalsize(new_size);
        Ok(ret)
    }

    /// Parse and get the FDT header.
    fn header_mut(&mut self) -> Result<&mut FdtHeader> {
        FdtHeader::from_bytes_mut(self.0.as_mut())
    }

    /// Reduce the total size field in the header to minimum that will fit existing content.
    /// No more data can be added to the FDT. This should be called after all modification is
    /// done and before passing to the kernel. This is to prevent kernel hang when FDT size is too
    /// big.
    pub fn shrink_to_fit(&mut self) -> Result<()> {
        let actual = self.header_ref()?.actual_size();
        self.header_mut()?.set_totalsize(actual.try_into().unwrap());
        Ok(())
    }

    /// Delete node by `path``. Fail if node doesn't exist.
    pub fn delete_node(&mut self, path: &str) -> Result<()> {
        let node = self.find_node(path)?;
        // SAFETY:
        // * `self.0` is guaranteed to be a proper fdt header reference
        // * `node` is offset of the node to delete within `self.0` fdt buffer
        map_result(unsafe { fdt_del_node(self.0.as_mut().as_mut_ptr() as *mut _, node) })?;
        Ok(())
    }

    /// Set the value of a node's property. Create the node and property if it doesn't exist.
    pub fn set_property(&mut self, path: &str, name: &CStr, val: &[u8]) -> Result<()> {
        let node = self.find_or_add_node(path)?;
        // SAFETY: API from libfdt_c.
        map_result(unsafe {
            fdt_setprop(
                self.0.as_mut().as_mut_ptr() as *mut _,
                node,
                name.to_bytes_with_nul().as_ptr() as *const _,
                val.as_ptr() as *const _,
                val.len().try_into().or(Err(Error::Other(None)))?,
            )
        })?;
        Ok(())
    }

    /// Wrapper/equivalent of fdt_setprop_placeholder.
    /// It creates/resizes a node's property to the given size and returns the buffer for caller
    /// to modify content.
    pub fn set_property_placeholder(
        &mut self,
        path: &str,
        name: &CStr,
        len: usize,
    ) -> Result<&mut [u8]> {
        let node = self.find_or_add_node(path)?;
        let mut out_ptr: *mut u8 = core::ptr::null_mut();
        // SAFETY: API from libfdt_c.
        map_result(unsafe {
            fdt_setprop_placeholder(
                self.0.as_mut().as_mut_ptr() as *mut _,
                node,
                name.to_bytes_with_nul().as_ptr() as *const _,
                len.try_into().or(Err(Error::Other(None)))?,
                &mut out_ptr as *mut *mut u8 as *mut _,
            )
        })?;
        assert!(!out_ptr.is_null());
        // SAFETY: Buffer returned by API from libfdt_c.
        Ok(unsafe { from_raw_parts_mut(out_ptr, len) })
    }

    /// Wrapper/equivalent of ufdt_apply_multioverlay.
    /// It extend current FDT buffer by applying passed overlays.
    pub fn multioverlay_apply(&mut self, overlays: &[&[u8]]) -> Result<()> {
        // Avoid shrinking device tree or doing any other actions in case nothing to apply.
        if overlays.is_empty() {
            return Ok(());
        }
        if overlays.len() > MAXIMUM_OVERLAYS_TO_APPLY {
            return Err(Error::Other(Some(MAXIMUM_OVERLAYS_ERROR_MSG)));
        }

        self.shrink_to_fit()?;

        // Convert input fat references into the raw pointers.
        let pointers: ArrayVec<_, MAXIMUM_OVERLAYS_TO_APPLY> =
            overlays.iter().map(|&slice| slice.as_ptr()).collect();

        // SAFETY: The `ufdt_apply_multioverlay` function guarantees that `self.0` is accessed
        // within the specified length boundaries. The `pointers` are non-null and are accessed
        // by indexes only within the provided length.
        map_result_libufdt(unsafe {
            ufdt_apply_multioverlay(
                self.0.as_mut().as_mut_ptr() as *mut _,
                self.0.as_ref().len(),
                pointers.as_ptr().cast(),
                overlays.len(),
            )
        })?;

        Ok(())
    }

    /// Find the offset of a node by a given node path. Add if node does not exist.
    fn find_or_add_node(&mut self, path: &str) -> Result<c_int> {
        let mut curr: c_int = 0;
        for name in path.split('/') {
            if name.len() == 0 {
                continue;
            }
            curr = match fdt_subnode_offset(self.0.as_ref(), curr, name) {
                Ok(v) => v,
                _ => fdt_add_subnode(self.0.as_mut(), curr, name)?,
            };
        }
        Ok(curr)
    }
}

impl<T: AsMut<[u8]>> AsMut<[u8]> for Fdt<T> {
    fn as_mut(&mut self) -> &mut [u8] {
        self.0.as_mut()
    }
}

impl<T: AsRef<[u8]>> AsRef<[u8]> for Fdt<T> {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    // Fdt is required to be 8 bytes aligned. Buffer to test alignment-related logic.
    #[repr(align(8))]
    struct AlignedBytes<const N: usize>([u8; N]);

    /// Checks to verify `overlay_*_by_path`/`overlay_*_by_reference` are successfully applied
    fn check_overlays_are_applied(fdt: &[u8]) {
        let fdt = Fdt::new(fdt).unwrap();

        assert_eq!(
            CStr::from_bytes_with_nul(
                fdt.get_property("/dev-2/dev-2.2/dev-2.2.1", c"property-1").unwrap()
            )
            .unwrap()
            .to_str()
            .unwrap(),
            "overlay1-property-1-value",
            "overlay_modify: failed to modify \"property-1\" in \"/dev-2/dev-2.2/dev-2.2.1\""
        );
        assert_eq!(
            CStr::from_bytes_with_nul(
                fdt.get_property("/dev-1/overlay1-new-node", c"overlay1-new-node-property")
                    .unwrap()
            )
            .unwrap()
            .to_str()
            .unwrap(),
            "overlay1-new-node-property-value",
            "overlay_modify: failed to add \"overlay1-new-node\" to \"/dev-1\""
        );
        assert_eq!(
            CStr::from_bytes_with_nul(
                fdt.get_property("/dev-4", c"overlay1-root-node-property").unwrap()
            )
            .unwrap()
            .to_str()
            .unwrap(),
            "overlay1-root-node-property-value",
            "overlay_modify: failed to add \"/dev-4/overlay1-root-node-property\""
        );
        assert_eq!(
            CStr::from_bytes_with_nul(
                fdt.get_property("/dev-2/dev-2.2/dev-2.2.1", c"overlay1-new-property").unwrap()
            )
            .unwrap()
            .to_str()
            .unwrap(),
            "overlay2-new-property-value",
            "overlay_modify2: failed to modify \"overlay1-new-property\" in \"/dev-2/dev-2.2/dev-2.2.1\""
        );
        assert_eq!(
            CStr::from_bytes_with_nul(
                fdt.get_property("/dev-4", c"overlay2-root-node-property").unwrap()
            )
            .unwrap()
            .to_str()
            .unwrap(),
            "overlay2-root-node-property-value",
            "overlay_modify2: failed to add \"overlay2-root-node-property\" to \"/dev-4\""
        );
    }

    #[test]
    fn test_new_from_invalid_fdt() {
        let mut init = include_bytes!("../test/data/base.dtb").to_vec();
        let mut fdt_buf = vec![0u8; init.len()];
        // Invalid total size
        assert!(Fdt::new_from_init(&mut fdt_buf[..], &init[..init.len() - 1]).is_err());
        // Invalid FDT
        init[..4].fill(0);
        assert!(Fdt::new_from_init(&mut fdt_buf[..], &init[..]).is_err());
    }

    #[test]
    fn test_get_property() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let mut fdt_buf = vec![0u8; init.len()];
        let fdt = Fdt::new_from_init(&mut fdt_buf[..], &init[..]).unwrap();

        assert_eq!(
            CStr::from_bytes_with_nul(fdt.get_property("/", c"info").unwrap())
                .unwrap()
                .to_str()
                .unwrap(),
            "test device tree"
        );
        assert_eq!(
            CStr::from_bytes_with_nul(
                fdt.get_property("/dev-2/dev-2.2/dev-2.2.1", c"property-1").unwrap()
            )
            .unwrap()
            .to_str()
            .unwrap(),
            "dev-2.2.1-property-1"
        );

        // Non eixsts
        assert!(fdt.get_property("/", c"non-existent").is_err());
    }

    #[test]
    fn test_set_property() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let mut fdt_buf = vec![0u8; init.len() + 512];
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &init[..]).unwrap();
        let data = vec![0x11u8, 0x22u8, 0x33u8];
        fdt.set_property("/new-node", c"custom", &data).unwrap();
        assert_eq!(fdt.get_property("/new-node", c"custom").unwrap().to_vec(), data);
    }

    #[test]
    fn test_delete_node() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let mut fdt_buf = vec![0u8; init.len()];
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &init[..]).unwrap();

        assert_eq!(
            CStr::from_bytes_with_nul(
                fdt.get_property("/dev-2/dev-2.2/dev-2.2.1", c"property-1").unwrap()
            )
            .unwrap()
            .to_str()
            .unwrap(),
            "dev-2.2.1-property-1"
        );

        fdt.delete_node("dev-2").unwrap();

        assert!(
            fdt.get_property("/dev-2/dev-2.2/dev-2.2.1", c"property-1").is_err(),
            "dev-2.2.1-property-1 expected to be deleted"
        );
    }

    #[test]
    fn test_delete_nost_existed_node_is_failed() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let mut fdt_buf = vec![0u8; init.len()];
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &init[..]).unwrap();

        assert!(
            fdt.delete_node("/non-existent").is_err(),
            "expected failed to delete non existent node"
        );
    }

    #[test]
    fn test_set_property_placeholder() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let mut fdt_buf = vec![0u8; init.len() + 512];
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &init[..]).unwrap();
        let data = vec![0x11u8, 0x22u8, 0x33u8, 0x44u8, 0x55u8];
        let payload = fdt.set_property_placeholder("/new-node", c"custom", data.len()).unwrap();
        payload.clone_from_slice(&data[..]);
        assert_eq!(fdt.get_property("/new-node", c"custom").unwrap().to_vec(), data);
    }

    #[test]
    fn test_header_from_bytes() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let header = FdtHeader::from_bytes_ref(&init[..]).unwrap();

        assert_eq!(header.totalsize(), init.len());
    }

    #[test]
    fn test_header_from_bytes_wrong_alignment() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();

        const HEADER_SIZE: usize = size_of::<FdtHeader>();
        let mut bytes = AlignedBytes([0u8; HEADER_SIZE + 1]);

        // Guaranteed not to be 8 bytes aligned.
        let (_, unaligned) = bytes.0.split_at_mut(1);
        unaligned.copy_from_slice(&init[..HEADER_SIZE]);

        assert!(FdtHeader::from_bytes_ref(unaligned).is_err());
    }

    #[test]
    fn test_header_from_raw() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        // Pointer points to `init`
        let (header, bytes) = unsafe { FdtHeader::from_raw(init.as_ptr()).unwrap() };
        assert_eq!(header.totalsize(), init.len());
        assert_eq!(bytes.to_vec(), init);
    }

    #[test]
    fn test_header_from_raw_invalid() {
        let mut init = include_bytes!("../test/data/base.dtb").to_vec();
        init[..4].fill(0);
        // Pointer points to `init`
        assert!(unsafe { FdtHeader::from_raw(init.as_ptr()).is_err() });
    }

    #[test]
    fn test_fdt_shrink_to_fit() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let mut fdt_buf = vec![0u8; init.len() + 512];
        let fdt_buf_len = fdt_buf.len();
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &init[..]).unwrap();
        assert_eq!(fdt.size().unwrap(), fdt_buf_len);
        fdt.shrink_to_fit().unwrap();
        assert_eq!(fdt.size().unwrap(), init.len());
    }

    #[test]
    fn test_fdt_multioverlay_apply_by_path() {
        let base = include_bytes!("../test/data/base.dtb").to_vec();
        let overlay_modify = include_bytes!("../test/data/overlay_by_path.dtbo").to_vec();
        let overlay_modify2 = include_bytes!("../test/data/overlay_2_by_path.dtbo").to_vec();

        let mut fdt_buf = vec![0u8; base.len() + overlay_modify.len() + overlay_modify2.len()];
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &base[..]).unwrap();

        fdt.multioverlay_apply(&[&overlay_modify[..] as _, &overlay_modify2[..] as _]).unwrap();
        fdt.shrink_to_fit().unwrap();

        check_overlays_are_applied(fdt.0);
    }

    #[test]
    fn test_fdt_multioverlay_apply_by_path_separately() {
        let base = include_bytes!("../test/data/base.dtb").to_vec();
        let overlay_modify = include_bytes!("../test/data/overlay_by_path.dtbo").to_vec();
        let overlay_modify2 = include_bytes!("../test/data/overlay_2_by_path.dtbo").to_vec();

        let mut fdt_buf = vec![0u8; base.len() + overlay_modify.len() + overlay_modify2.len()];
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &base[..]).unwrap();

        fdt.multioverlay_apply(&[&overlay_modify[..] as _]).unwrap();
        fdt.multioverlay_apply(&[&overlay_modify2[..] as _]).unwrap();
        fdt.shrink_to_fit().unwrap();

        check_overlays_are_applied(fdt.0);
    }

    // TODO(b/362486327): symbols from overlay are not added to the result tree
    // so cannot refer to them.
    #[ignore]
    #[test]
    fn test_fdt_multioverlay_apply_by_reference() {
        let base = include_bytes!("../test/data/base.dtb").to_vec();
        let overlay_modify = include_bytes!("../test/data/overlay_by_reference.dtbo").to_vec();
        let overlay_modify2 = include_bytes!("../test/data/overlay_2_by_reference.dtbo").to_vec();

        let mut fdt_buf = vec![0u8; base.len() + overlay_modify.len() + overlay_modify2.len()];
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &base[..]).unwrap();

        fdt.multioverlay_apply(&[&overlay_modify[..] as _, &overlay_modify2[..] as _]).unwrap();
        fdt.shrink_to_fit().unwrap();

        check_overlays_are_applied(fdt.0);
    }

    // TODO(b/362486327): symbols from overlay are not added to the result tree
    // so cannot refer to them.
    #[ignore]
    #[test]
    fn test_fdt_multioverlay_apply_by_reference_separately() {
        let base = include_bytes!("../test/data/base.dtb").to_vec();
        let overlay_modify = include_bytes!("../test/data/overlay_by_reference.dtbo").to_vec();
        let overlay_modify2 = include_bytes!("../test/data/overlay_2_by_reference.dtbo").to_vec();

        let mut fdt_buf = vec![0u8; base.len() + overlay_modify.len() + overlay_modify2.len()];
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &base[..]).unwrap();

        fdt.multioverlay_apply(&[&overlay_modify[..] as _]).unwrap();
        fdt.multioverlay_apply(&[&overlay_modify2[..] as _]).unwrap();
        fdt.shrink_to_fit().unwrap();

        check_overlays_are_applied(fdt.0);
    }

    #[test]
    fn test_fdt_multioverlay_apply_not_enough_space() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let overlay_basic = include_bytes!("../test/data/overlay_by_path.dtbo").to_vec();

        let mut fdt_buf = vec![0u8; init.len()];
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &init[..]).unwrap();

        assert!(
            fdt.multioverlay_apply(&[&overlay_basic[..]]).is_err(),
            "expected the problem is catched when not enough space in the main fdt buffer"
        );
    }

    #[test]
    fn test_fdt_multioverlay_apply_corrupted() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let overlay_corrupted: Vec<u8> = include_bytes!("../test/data/overlay_by_path.dtbo")
            .to_vec()
            .iter()
            .copied()
            .rev()
            .collect();

        let mut fdt_buf = vec![0u8; init.len() + overlay_corrupted.len()];
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &init[..]).unwrap();

        assert!(
            fdt.multioverlay_apply(&[&overlay_corrupted[..]]).is_err(),
            "expected the problem is catched when applying corrupted overlay"
        );
    }

    #[test]
    fn test_fdt_multioverlay_apply_with_wrong_target_path() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let overlay_wrong_path = include_bytes!("../test/data/overlay_wrong_path.dtbo").to_vec();

        let mut fdt_buf = vec![0u8; init.len()];
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &init[..]).unwrap();

        assert!(
            fdt.multioverlay_apply(&[&overlay_wrong_path[..]]).is_err(),
            "expected the problem is catched when applying overlay with wrong target path"
        );
    }

    #[test]
    fn test_fdt_multioverlay_apply_maximum_amount_of_overlays_handled() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let too_many_overlays = &[&[] as &[u8]; MAXIMUM_OVERLAYS_TO_APPLY + 1];

        let mut fdt_buf = vec![0u8; init.len()];
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &init[..]).unwrap();

        assert_eq!(
            fdt.multioverlay_apply(too_many_overlays),
            Err(Error::Other(Some(MAXIMUM_OVERLAYS_ERROR_MSG))),
            "too many overlays isn't handled"
        );
    }
}
