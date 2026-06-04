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
use core::ffi::{c_int, c_void, CStr};
use core::mem::size_of;
use core::slice::{from_raw_parts, from_raw_parts_mut};
use liberror::{Error, Result};
use libfdt_bindgen::{
    fdt_add_subnode_namelen, fdt_create_empty_tree, fdt_del_node, fdt_delprop, fdt_first_subnode,
    fdt_get_property, fdt_header, fdt_move, fdt_setprop, fdt_setprop_placeholder, fdt_strerror,
    fdt_subnode_offset_namelen,
};
use libufdt_bindgen::ufdt_apply_multioverlay;
use safemath::SafeNum;
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout, Ref};

/// Fdt header structure size.
pub const FDT_HEADER_SIZE: usize = size_of::<FdtHeader>();
/// Maximum number of overlays that can be applied by GBL.
pub const MAXIMUM_OVERLAYS_TO_APPLY: usize = 32;
const MAXIMUM_OVERLAYS_ERROR_MSG: &str = "At most 32 overlays are supported to apply at a time";

/// Standard FDT property names
pub mod std_props {
    use core::ffi::CStr;

    /// #address-cells property name
    pub const ADDRESS_CELLS: &CStr = c"#address-cells";
    /// #size-cells property name
    pub const SIZE_CELLS: &CStr = c"#size-cells";
    /// compatible property name
    pub const COMPATIBLE: &CStr = c"compatible";
    /// reg property name
    pub const REG: &CStr = c"reg";
    /// no-map property name
    pub const NO_MAP: &CStr = c"no-map";
}

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

// Helper function used to set property bytes when sizes differ
fn copy_bytes_right_align(src: &[u8], dst: &mut [u8]) -> Result<()> {
    let dst_len = dst.len();
    let src_len = src.len();
    if src_len <= dst_len {
        let (pad, dst) = dst.split_at_mut(dst_len - src_len);
        pad.fill(0);
        dst.copy_from_slice(src);
    } else {
        let (pad, src) = src.split_at(src_len - dst_len);
        if pad.iter().any(|&v| v != 0) {
            return Err(Error::InvalidInput);
        }
        dst.copy_from_slice(src);
    }
    Ok(())
}

/// Encode a slice of values into a cell sized property.
///
/// A cell-sized FDT property is used to describe hardware resources using units called cells -
/// unsigned 32-bit integers. The number of cells used to encode each value from an array of values
/// is defined by the parent node’s properties. Therefore, a cell-sized property can contain one or
/// more values, each of which can span one or more 32-bit cells. This function encodes an array of
/// values using a given number of cells, and writes the encoded values into a buffer. Values can
/// form n-tuples, with each element taking up a different number of cells.
///
/// For example, a `reg` property may contain 5 pairs of (address, size) - a total of 10 values.
/// Its parent node may set `#address-cells = <2>`  and `#size-cells = <1>`, meaning this function
/// would use 2 u32 cells to encode the address, and one u32 cell to encode the size - a total of 3
/// cells for one pair, and 15 cells for 5 pairs of (address, size) values.
///
/// # Arguments
///
/// * `values` - list of values to encode; its length must be a multiple of `cells` length
/// * `tuple_cells` - list of cell sizes used to encode each n-tuple value; its length determines
/// the n-tuple size
/// * `out_buffer` - output buffer to write encoded values into
///
/// # Returns
///
/// * `Ok(usize)` - on success, the number of bytes written to output buffer.
/// * `Err(Error::BufferTooSmall)` - if the output buffer is too small.
/// * `Err(Error::InvalidInput)` - if the number of values is not a multiple of the size of `cells`.
/// * `Err(Error::ArithmeticOverflow)` - if values cannot be encoded into given number of cells.
pub fn fdt_encode_cell_sized_property(
    values: &[usize],
    tuple_cells: &[u32],
    mut out_buffer: &mut [u8],
) -> Result<usize> {
    const FDT_CELL_SIZE: usize = 4; // 4 bytes per cell
    if tuple_cells.is_empty() || values.len() % tuple_cells.len() != 0 {
        return Err(Error::InvalidInput.into());
    }
    let total_size: usize = (SafeNum::from(FDT_CELL_SIZE) * values.len() / tuple_cells.len()
        * tuple_cells.iter().fold(SafeNum::from(0), |a, i| a + *i))
    .try_into()?;

    // Encode values
    for (value, cells) in values.into_iter().zip(tuple_cells.iter().cycle()) {
        let encoding_bytes = (SafeNum::from(*cells) * FDT_CELL_SIZE).try_into()?;
        let (encoding_buffer, rest) = out_buffer
            .split_at_mut_checked(encoding_bytes)
            .ok_or(Error::BufferTooSmall(Some(total_size)))?;
        copy_bytes_right_align(&value.to_be_bytes(), encoding_buffer)?;
        out_buffer = rest;
    }
    Ok(total_size)
}

/// Rust wrapper for the FDT header data.
#[repr(transparent)]
#[derive(Copy, Clone, Debug, PartialEq, Immutable, FromBytes, IntoBytes, KnownLayout)]
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

        Ok(Ref::into_ref(
            Ref::<_, FdtHeader>::new_from_prefix(buffer)
                .ok_or(Error::BufferTooSmall(Some(FDT_HEADER_SIZE)))?
                .0,
        ))
    }

    /// Cast a bytes into a mutable reference of FDT header.
    pub fn from_bytes_mut(buffer: &mut [u8]) -> Result<&mut FdtHeader> {
        fdt_check_header(buffer)?;

        Ok(Ref::into_mut(
            Ref::<_, FdtHeader>::new_from_prefix(buffer)
                .ok_or(Error::BufferTooSmall(Some(FDT_HEADER_SIZE)))?
                .0,
        ))
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

    /// Get a property from an existing node at the given node offset.
    ///
    /// Note: The lifetime of the returned buffer must be tied to the Fdt
    /// instance. This prevents the underlying device tree from being modified
    /// while the buffer is in use, ensuring the data remains valid.
    pub fn get_property_by_node_offset(&self, node_offset: usize, name: &CStr) -> Result<&[u8]> {
        let mut len: c_int = 0;
        // SAFETY:
        // * `self.0` is guaranteed to be a proper fdt header reference.
        // * `name` is guaranteed to point to a null-terminated string.
        // * `len` is guaranteed to point to a writable integer buffer.
        let ptr = unsafe {
            fdt_get_property(
                self.0.as_ref().as_ptr() as *const c_void,
                node_offset.try_into()?,
                name.to_bytes_with_nul().as_ptr() as *const _,
                &mut len,
            )
        };
        // SAFETY: On error, `fdt_get_property` returns NULL. On success, it returns
        // a pointer to a `const struct fdt_property`.
        match unsafe { ptr.as_ref() } {
            // SAFETY: On success the `const struct fdt_property` contains a byte array
            // pointed to by `v.data`, with its length in `v.len`.
            // The length is in big-endian byte order, so we convert it before using it.
            Some(v) => Ok(unsafe {
                from_raw_parts(
                    v.data.as_ptr() as *const u8,
                    u32::from_be(v.len).try_into().or(Err(Error::Other(None)))?,
                )
            }),
            // On error, `len` is set to an error value.
            _ => Err(map_result(len).unwrap_err()),
        }
    }

    /// Get a property from an existing node at the given node path.
    pub fn get_property(&self, path: &str, name: &CStr) -> Result<&[u8]> {
        let node = self.find_node_offset(path)?;
        self.get_property_by_node_offset(node.try_into().unwrap(), name)
    }

    /// Treat the property value as a u32 and return it.
    pub fn get_property_u32(&self, path: &str, name: &CStr) -> Result<u32> {
        let bytes = self.get_property(path, name)?;
        Ok(u32::from_be_bytes(bytes.try_into().map_err(|_| Error::Other(Some("not a u32 value")))?))
    }

    /// Find the offset of a node by a given node path.
    pub fn find_node_offset(&self, path: &str) -> Result<usize> {
        let offset = self.find_node_offset_ffi(path)?;
        offset.try_into().map_err(|_| Error::Other(Some("Invalid FDT node offset")))
    }

    /// Find the offset of a node by a given node path.
    fn find_node_offset_ffi(&self, path: &str) -> Result<c_int> {
        let mut curr: c_int = 0;
        for name in path.split('/') {
            if name.len() == 0 {
                continue;
            }
            curr = fdt_subnode_offset(self.0.as_ref(), curr, name)?;
        }
        Ok(curr)
    }

    /// Get first subnode from an existing node.
    pub fn get_first_subnode_offset(&self, node_offset: usize) -> Result<usize> {
        // SAFETY:
        // * `self.0` is guaranteed to be a proper fdt header reference
        map_result(unsafe {
            fdt_first_subnode(self.0.as_ref().as_ptr() as *const c_void, node_offset.try_into()?)
        })
        .map(|o| o.try_into().unwrap())
    }

    /// Iterator based implementation of fdt_stringlist_get()
    pub fn get_property_stringlist_by_node_offset(
        &self,
        node_offset: usize,
        name: &CStr,
    ) -> Result<impl Iterator<Item = &CStr>> {
        // Stringlist is required to be null terminated.
        let prop = self.get_property_by_node_offset(node_offset, name)?;

        // Stringlist is required to be null terminated.
        if prop.last() != Some(&0) {
            return Err(Error::InvalidInput);
        }

        Ok(prop.split_inclusive(|v| *v == 0).map(|v| CStr::from_bytes_with_nul(v).unwrap()))
    }
}

/// APIs when data can be modified.
impl<T: AsMut<[u8]> + AsRef<[u8]>> Fdt<T> {
    /// Creates a new mut [Fdt] wrapping the contents of `init`.
    pub fn new_mut(init: T) -> Result<Self> {
        let mut fdt = Fdt::new(init)?;
        fdt.expand_to_buffer()?;
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
        let mut ret = Fdt::new(fdt)?;
        ret.expand_to_buffer()?;
        Ok(ret)
    }

    /// Creates a new empty [Fdt] in `init`.
    pub fn new_empty(mut init: T) -> Result<Self> {
        let buffer = init.as_mut();
        // SAFETY:
        // `buffer` is a valid, aligned, and writable byte slice. The pointer derived from it is
        // valid for writes up to `buffer.len()` bytes. The C function will not write out of bounds.
        // All byte patterns are valid for `[u8]`, so no additional invariants are violated.
        map_result(unsafe {
            fdt_create_empty_tree(
                buffer.as_mut_ptr().cast(),
                buffer.len().try_into().or(Err(Error::Other(None)))?,
            )
        })?;
        Ok(Fdt::new(init)?)
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

    /// Expand the total size field in the header to match the full buffer size.
    /// This allows the FDT to be modified further by ensuring sufficient space is available.
    /// Typically used before making modifications to an existing FDT, especially if it was
    /// previously shrunk. After modifications are complete, consider calling `shrink_to_fit`
    /// to reduce the size before passing to the kernel.
    pub fn expand_to_buffer(&mut self) -> Result<()> {
        let buffer_size = self.0.as_ref().len().try_into().unwrap();
        self.header_mut()?.set_totalsize(buffer_size);
        Ok(())
    }

    /// Create node by `path` if it does not exist already.
    pub fn ensure_node(&mut self, path: &str) -> Result<()> {
        self.find_or_add_node(path).map(|_| ())
    }

    /// Delete node by `path`. Fail if node doesn't exist.
    pub fn delete_node(&mut self, path: &str) -> Result<()> {
        let node = self.find_node_offset_ffi(path)?;
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
    ///
    /// Note: It is assumed that existing data in the property is retained when growing or shrinking
    /// the property. This is not explicitly guaranteed by the libfdt C API, but is observed in its
    /// implementation. Callers are responsible for dealing with any uninitialized garbage data in
    /// newly allocated space.
    pub fn set_property_placeholder(
        &mut self,
        path: &str,
        name: &CStr,
        len: usize,
    ) -> Result<&mut [u8]> {
        let node = self.find_or_add_node(path)?;
        let mut out_ptr: *mut u8 = core::ptr::null_mut();
        // SAFETY:
        // * `self.0` is guaranteed to be a valid FDT buffer.
        // * `node` is offset of the node within the `self.0` FDT buffer.
        // * `name` is guaranteed to be a valid null-terminated string.
        // * `&mut out_ptr` is a valid pointer to receive the address of the resized buffer.
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

    /// Delete property by `path` and `name`. Fail if property doesn't exist.
    pub fn delete_property(&mut self, path: &str, name: &CStr) -> Result<()> {
        let node = self.find_node_offset_ffi(path)?;
        // SAFETY:
        // * `self.0` is guaranteed to be a proper fdt header reference.
        // * `node` is offset of the node to delete within `self.0` fdt buffer.
        // * `name` is guaranteed to be a valid null-terminated string.
        map_result(unsafe {
            fdt_delprop(
                self.0.as_mut().as_mut_ptr() as *mut c_void,
                node,
                name.to_bytes_with_nul().as_ptr() as *const _,
            )
        })?;

        Ok(())
    }

    /// Wrapper/equivalent of ufdt_apply_multioverlay.
    /// It extend current FDT buffer by applying passed overlays.
    pub fn multioverlay_apply(
        &mut self,
        overlays: impl IntoIterator<Item = impl AsRef<[u8]>>,
    ) -> Result<()> {
        // Iterate through the overlays and extract their pointers.
        let mut pointers: ArrayVec<*const u8, MAXIMUM_OVERLAYS_TO_APPLY> = ArrayVec::new();
        for overlay in overlays {
            // Check each overlay size to prevent buffer overflows in the C FFI calls.
            let overlay_bytes = overlay.as_ref();
            fdt_check_buffer(overlay_bytes)?;

            pointers
                .try_push(overlay_bytes.as_ptr())
                .map_err(|_| Error::Other(Some(MAXIMUM_OVERLAYS_ERROR_MSG)))?;
        }

        if pointers.is_empty() {
            return Ok(());
        }

        self.shrink_to_fit()?;

        // SAFETY: The `ufdt_apply_multioverlay` function guarantees that `self.0` is accessed
        // within the specified length boundaries. The `pointers` are non-null and are accessed
        // by indexes only within the provided length.
        map_result_libufdt(unsafe {
            ufdt_apply_multioverlay(
                self.0.as_mut().as_mut_ptr() as *mut _,
                self.0.as_ref().len(),
                pointers.as_ptr().cast(),
                pointers.len(),
            )
        })?;

        self.expand_to_buffer()?;

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
    extern crate libc_deps_posix;

    use super::*;
    use libtestutils::AlignedBuffer;

    /// Checks to verify `overlay_*_by_path`/`overlay_*_by_reference` are successfully applied
    fn check_overlays_are_applied(fdt: &[u8]) {
        let fdt = Fdt::new(fdt).unwrap();

        assert_eq!(fdt.header_ref().unwrap().totalsize(), fdt.as_ref().len());
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
    fn test_get_property_by_node_offset() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let mut fdt_buf = vec![0u8; init.len()];
        let fdt = Fdt::new_from_init(&mut fdt_buf[..], &init[..]).unwrap();

        let node_offset = fdt.find_node_offset("/dev-2/dev-2.2/dev-2.2.1").unwrap();

        assert_eq!(
            CStr::from_bytes_with_nul(
                fdt.get_property_by_node_offset(node_offset.try_into().unwrap(), c"property-1")
                    .unwrap()
            )
            .unwrap()
            .to_str()
            .unwrap(),
            "dev-2.2.1-property-1"
        );

        // Non eixsts
        assert!(fdt
            .get_property_by_node_offset(node_offset.try_into().unwrap(), c"non-existent")
            .is_err());
    }

    #[test]
    fn test_get_property_u32() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let mut fdt_buf = vec![0u8; init.len()];
        let fdt = Fdt::new_from_init(&mut fdt_buf[..], &init[..]).unwrap();

        assert_eq!(
            fdt.get_property_u32("/dev-2/dev-2.2/dev-2.2.1", c"property-2").unwrap(),
            0x11223344
        );
        // Non a valid u32
        assert!(fdt.get_property_u32("/dev-2/dev-2.2/dev-2.2.1", c"property-1").is_err());
        // Non exists
        assert!(fdt.get_property_u32("/", c"non-existent").is_err());
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
    fn test_delete_not_existed_node_is_failed() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let mut fdt_buf = vec![0u8; init.len()];
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &init[..]).unwrap();

        assert!(
            fdt.delete_node("/non-existent").is_err(),
            "expected failed to delete non existent node"
        );
    }

    #[test]
    fn test_delete_property() {
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

        fdt.delete_property("/dev-2/dev-2.2/dev-2.2.1", c"property-1").unwrap();

        assert!(
            fdt.get_property("/dev-2/dev-2.2/dev-2.2.1", c"property-1").is_err(),
            "expected failed to get deleted property"
        )
    }

    #[test]
    fn test_delete_not_existed_property_is_failed() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let mut fdt_buf = vec![0u8; init.len()];
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &init[..]).unwrap();

        assert!(
            fdt.delete_property("/non-existent", c"not-existent").is_err(),
            "expected failed to delete non existent property"
        );
    }

    #[test]
    fn test_set_property_placeholder_extend() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let mut fdt_buf = vec![0u8; init.len() + 512];
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &init[..]).unwrap();

        // First set a property with some data.
        let data = vec![0x11u8, 0x22u8, 0x33u8, 0x44u8, 0x55u8];
        let payload = fdt.set_property_placeholder("/new-node", c"custom", data.len()).unwrap();
        payload.clone_from_slice(&data[..]);

        // Extend it.
        let extended_len = data.len() + 5;
        let payload = fdt.set_property_placeholder("/new-node", c"custom", extended_len).unwrap();
        assert_eq!(payload.len(), extended_len);
        assert_eq!(payload[..data.len()], data[..]);
    }

    #[test]
    fn test_set_property_placeholder_shrink() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let mut fdt_buf = vec![0u8; init.len() + 512];
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &init[..]).unwrap();

        // First set a property with some data.
        let data = vec![0x11u8, 0x22u8, 0x33u8, 0x44u8, 0x55u8];
        let payload = fdt.set_property_placeholder("/new-node", c"custom", data.len()).unwrap();
        payload.clone_from_slice(&data[..]);

        // Shrink it.
        let shrunk_len = data.len() - 3;
        let payload = fdt.set_property_placeholder("/new-node", c"custom", shrunk_len).unwrap();
        assert_eq!(payload, &data[..shrunk_len]);
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
        let mut bytes = AlignedBuffer::new(HEADER_SIZE + 1, 8);

        // Guaranteed not to be 8 bytes aligned.
        let unaligned = &mut bytes[1..];
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

        fdt.multioverlay_apply([&overlay_modify[..], &overlay_modify2[..]]).unwrap();

        check_overlays_are_applied(fdt.0);
    }

    #[test]
    fn test_fdt_multioverlay_apply_by_path_separately() {
        let base = include_bytes!("../test/data/base.dtb").to_vec();
        let overlay_modify = include_bytes!("../test/data/overlay_by_path.dtbo").to_vec();
        let overlay_modify2 = include_bytes!("../test/data/overlay_2_by_path.dtbo").to_vec();

        let mut fdt_buf = vec![0u8; base.len() + overlay_modify.len() + overlay_modify2.len()];
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &base[..]).unwrap();

        fdt.multioverlay_apply([&overlay_modify[..]]).unwrap();
        fdt.multioverlay_apply([&overlay_modify2[..]]).unwrap();

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

        fdt.multioverlay_apply([&overlay_modify[..], &overlay_modify2[..]]).unwrap();

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

        fdt.multioverlay_apply([&overlay_modify[..]]).unwrap();
        fdt.multioverlay_apply([&overlay_modify2[..]]).unwrap();

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
        let overlay = include_bytes!("../test/data/overlay_by_path.dtbo").to_vec();
        let too_many_overlays = &[&overlay[..]; MAXIMUM_OVERLAYS_TO_APPLY + 1];

        let mut fdt_buf = vec![0u8; init.len()];
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &init[..]).unwrap();

        assert_eq!(
            fdt.multioverlay_apply(too_many_overlays),
            Err(Error::Other(Some(MAXIMUM_OVERLAYS_ERROR_MSG))),
            "too many overlays isn't handled"
        );
    }

    #[test]
    fn test_fdt_multioverlay_apply_invalid_totalsize() {
        let base = include_bytes!("../test/data/base.dtb").to_vec();
        let mut overlay = include_bytes!("../test/data/overlay_by_path.dtbo").to_vec();

        let mut fdt_buf = vec![0u8; base.len() + overlay.len()];
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &base[..]).unwrap();

        // Modify the overlay reported size to be larger than the buffer.
        let original_size = overlay.len();
        let invalid_size = (original_size + 1) as u32;
        overlay[4..8].copy_from_slice(&invalid_size.to_be_bytes());

        assert!(fdt.multioverlay_apply([&overlay[..]]).is_err());
    }

    #[test]
    fn test_fdt_encode_cell_sized_property() {
        let mut buffer = [0u8; 48];
        fdt_encode_cell_sized_property(&[0xABABABAB12121212, 0x12345678], &[2, 1], &mut buffer)
            .unwrap();
        let vals = buffer
            .chunks_exact(size_of::<u32>())
            .take(3)
            .map(|b| u32::from_be_bytes(b.try_into().unwrap()))
            .collect::<Vec<_>>();
        assert_eq!(vals, vec![0xABABABAB, 0x12121212, 0x12345678]);

        fdt_encode_cell_sized_property(&[1, 2, 3, 4, 5, 6], &[2, 2], &mut buffer).unwrap();
        let vals = buffer
            .chunks_exact(size_of::<u32>())
            .take(12)
            .map(|b| u32::from_be_bytes(b.try_into().unwrap()))
            .collect::<Vec<_>>();
        assert_eq!(vals, vec![0, 1, 0, 2, 0, 3, 0, 4, 0, 5, 0, 6]);

        fdt_encode_cell_sized_property(&[1, 2, 3, 4, 5, 6], &[1, 3, 1], &mut buffer).unwrap();
        let vals = buffer
            .chunks_exact(size_of::<u32>())
            .take(10)
            .map(|b| u32::from_be_bytes(b.try_into().unwrap()))
            .collect::<Vec<_>>();
        assert_eq!(vals, vec![1, 0, 0, 2, 3, 4, 0, 0, 5, 6]);
    }

    #[test]
    fn test_fdt_encode_cell_sized_property_invalid_data() {
        let mut buffer = [0u8; 48];
        // Values do not form 3-tuples
        fdt_encode_cell_sized_property(
            &[0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7],
            &[1, 1, 1],
            &mut buffer,
        )
        .unwrap_err();
        // Values do not form 3-tuples
        fdt_encode_cell_sized_property(&[0x1, 0x2], &[1, 1, 1], &mut buffer).unwrap_err();
        // Value does not fit into one cell
        fdt_encode_cell_sized_property(&[0x1212121212121212, 0x2], &[1, 1], &mut buffer)
            .unwrap_err();
        // Buffer too small
        fdt_encode_cell_sized_property(&[0x1, 0x2, 0x3, 0x4, 0x5, 0x6], &[4, 4], &mut buffer)
            .unwrap_err();
    }

    #[test]
    fn test_ensure_node() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let mut dt_buf = [0u8; 1000];
        let mut dt = Fdt::new_from_init(&mut dt_buf, &init).unwrap();

        dt.find_node_offset("/dev-3").unwrap();
        dt.ensure_node("/dev-3").unwrap();
        dt.ensure_node("/dev-3/a/b").unwrap();
        dt.find_node_offset("/dev-3/a/b").unwrap();
    }

    #[test]
    fn test_create_fdt_from_empty() {
        let mut dt_buf = AlignedBuffer::new(256, 8);
        let mut dt = Fdt::new_empty(&mut dt_buf[..]).unwrap();

        dt.find_node_offset("/").unwrap();
        dt.find_node_offset("/a").unwrap_err();
        dt.ensure_node("/a").unwrap();
        dt.find_node_offset("/a").unwrap();
        dt.find_node_offset("/b").unwrap_err();

        dt.shrink_to_fit().unwrap();
        dt.header_ref().unwrap();
    }

    #[test]
    fn test_get_property_stringlist_by_node_offset() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let mut fdt_buf = vec![0u8; init.len()];
        let fdt = Fdt::new_from_init(&mut fdt_buf[..], &init[..]).unwrap();

        let valid_prop_node_offset = fdt.find_node_offset("/dev-4").unwrap();
        let invalid_prop_node_offset = fdt.find_node_offset("/dev-2/dev-2.2/dev-2.2.1").unwrap();
        let non_exist_prop_node_offset = fdt.find_node_offset("/").unwrap();
        let invalid_node_offset = usize::MAX;

        let strings_from_fdt: Vec<&str> = fdt
            .get_property_stringlist_by_node_offset(
                valid_prop_node_offset.try_into().unwrap(),
                c"property-1",
            )
            .unwrap()
            .map(|cs| cs.to_str().unwrap())
            .collect();
        assert_eq!(strings_from_fdt, vec!["Str1", "Str2", "Str3"]);

        // Not a valid stringlist
        assert!(fdt
            .get_property_stringlist_by_node_offset(
                invalid_prop_node_offset.try_into().unwrap(),
                c"property-2"
            )
            .is_err());
        // Non exists
        assert!(fdt
            .get_property_stringlist_by_node_offset(
                non_exist_prop_node_offset.try_into().unwrap(),
                c"non-existent"
            )
            .is_err());
        // Invalid node
        assert!(fdt
            .get_property_stringlist_by_node_offset(invalid_node_offset, c"invalid-property")
            .is_err());
    }

    #[test]
    fn test_find_node_offset() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let mut fdt_buf = vec![0u8; init.len()];
        let fdt = Fdt::new_from_init(&mut fdt_buf[..], &init[..]).unwrap();

        assert!(fdt.find_node_offset("/dev-4").is_ok());
        assert!(fdt.find_node_offset("/non-existent").is_err());
    }

    #[test]
    fn test_get_first_subnode_offset() {
        let init = include_bytes!("../test/data/base.dtb").to_vec();
        let mut fdt_buf = vec![0u8; init.len()];
        let mut fdt = Fdt::new_from_init(&mut fdt_buf[..], &init[..]).unwrap();

        let mut node_offset = fdt.find_node_offset("/dev-2/dev-2.2").unwrap();
        assert!(fdt.get_first_subnode_offset(node_offset.try_into().unwrap()).is_ok());

        fdt.delete_node("/dev-2/dev-2.2/dev-2.2.1").unwrap();
        node_offset = fdt.find_node_offset("/dev-2/dev-2.2").unwrap();
        assert!(fdt.get_first_subnode_offset(node_offset.try_into().unwrap()).is_err());
    }
}
