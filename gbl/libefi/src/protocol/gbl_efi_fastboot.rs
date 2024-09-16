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

//! Rust wrapper for `GBL_EFI_FASTBOOT_PROTOCOL`

use crate::{
    efi_call,
    protocol::{Protocol, ProtocolInfo},
};
use arrayvec::ArrayVec;
use core::str::{from_utf8, Split};
use efi_types::{EfiGuid, GblEfiFastbootArg, GblEfiFastbootPolicy, GblEfiFastbootProtocol};
use liberror::{Error, Result};

/// GBL_EFI_FASTBOOT_PROTOCOL
pub struct GblFastbootProtocol;

// Note: this is an internal limitation due to the need to allocate
// fixed sized buffers for storing args in the iterator
// and in the wrapper for `GblEfiFastbootProtocol.get_var`.
const MAX_ARGS: usize = 16;

impl ProtocolInfo for GblFastbootProtocol {
    type InterfaceType = GblEfiFastbootProtocol;

    const GUID: EfiGuid =
        EfiGuid::new(0xc67e48a0, 0x5eb8, 0x4127, [0xbe, 0x89, 0xdf, 0x2e, 0xd9, 0x3d, 0x8a, 0x9a]);
}

/// Wrapper type for get_next_var_args() tokens.
///
/// Tokens are opaque values used to store the iterator's position.
/// They can also be passed in get_var() to give the backend a hint
/// on where to find a variable entry.
#[derive(Copy, Clone, Debug)]
pub struct Token(*const core::ffi::c_void);

impl Token {
    const fn new() -> Self {
        Self(core::ptr::null())
    }
}

impl Protocol<'_, GblFastbootProtocol> {
    /// Hint-free wrapper of `GBL_EFI_FASTBOOT_PROTOCOL.get_var()`
    pub fn get_var(&self, args: Split<'_, char>, buffer: &mut [u8]) -> Result<usize> {
        self.get_var_with_hint(args, buffer, Token::new())
    }

    /// Wrapper of `GBL_EFI_FASTBOOT_PROTOCOL.get_var() with hint.`
    pub fn get_var_with_hint(
        &self,
        args: Split<'_, char>,
        buffer: &mut [u8],
        hint: Token,
    ) -> Result<usize> {
        let mut bufsize = buffer.len();
        let mut call_args: [GblEfiFastbootArg; MAX_ARGS + 1] = Default::default();
        let mut call_args_len = 0usize;
        for (a, ca) in core::iter::zip(args, call_args.iter_mut()) {
            ca.str_utf8 = a.as_ptr();
            ca.len = a.len();
            call_args_len += 1;
        }

        if call_args_len == MAX_ARGS + 1 {
            return Err(Error::InvalidInput);
        }

        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // No parameter is Null except optionally `hint`, and all parameters outlive the call.
        // Null is a valid value for hint.
        unsafe {
            efi_call!(
                @bufsize bufsize,
                self.interface()?.get_var,
                self.interface,
                call_args.as_ptr(),
                call_args_len,
                buffer.as_mut_ptr(),
                &mut bufsize,
                hint.0,
            )?
        };
        Ok(bufsize)
    }

    fn start_var_iterator(&self) -> Result<Token> {
        let mut token = Token::new();

        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is an input parameter and will not be retained. It outlives the call.
        // `token.0` is an output parameter. It is not retained, and it outlives the call.
        // Null is a valid value for token.
        unsafe { efi_call!(self.interface()?.start_var_iterator, self.interface, &mut token.0)? };

        Ok(token)
    }

    /// Wrapper of `GBL_EFI_FASTBOOT_PROTOCOL.get_next_var_args()`
    fn get_next_var_args(
        &self,
        args: &mut [GblEfiFastbootArg],
        token: Token,
    ) -> Result<(usize, Token)> {
        let mut bufsize = args.len();
        let mut new_token = token;

        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // No parameter is retained, and all parameters outlive the call.
        // No parameter is Null except possibly `new_token.0`
        // Null is a valid value for `new_token.0`.
        unsafe {
            efi_call!(
                @bufsize bufsize,
                self.interface()?.get_next_var_args,
                self.interface,
                args.as_mut_ptr(),
                &mut bufsize,
                &mut new_token.0
            )?
        };
        Ok((bufsize, new_token))
    }

    /// Returns an iterator over backend fastboot variables.
    pub fn var_iter(&self) -> Result<VarIterator> {
        VarIterator::try_new(self)
    }

    /// Wrapper of `GBL_EFI_FASTBOOT_PROTOCOL.run_oem_function()`
    pub fn run_oem_function(&self, cmd: &str, buffer: &mut [u8]) -> Result<usize> {
        let mut bufsize = buffer.len();

        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // No parameter is retained, all parameters outlive the call,
        // and no pointers are Null.
        unsafe {
            efi_call!(
                @bufsize bufsize,
                self.interface()?.run_oem_function,
                self.interface,
                cmd.as_ptr(),
                cmd.len(),
                buffer.as_mut_ptr(),
                &mut bufsize,
            )?
        };
        Ok(bufsize)
    }

    /// Wrapper of `GBL_EFI_FASTBOOT_PROTOCOL.get_policy()`
    pub fn get_policy(&self) -> Result<GblEfiFastbootPolicy> {
        let mut policy: GblEfiFastbootPolicy = Default::default();

        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // No parameters are retained, all parameters outlive the call,
        // and no pointers are Null.
        unsafe { efi_call!(self.interface()?.get_policy, self.interface, &mut policy)? };

        Ok(policy)
    }

    /// Wrapper of `GBL_EFI_FASTBOOT_PROTOCOL.set_lock()`
    pub fn set_lock(&self, flags: u64) -> Result<()> {
        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is an input parameter and will not be retained. It outlives the call.
        unsafe { efi_call!(self.interface()?.set_lock, self.interface, flags) }
    }

    /// Wrapper of `GBL_EFI_FASTBOOT_PROTOCOL.clear_lock()`
    pub fn clear_lock(&self, flags: u64) -> Result<()> {
        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is an input parameter and will not be retained. It outlives the call.
        unsafe { efi_call!(self.interface()?.clear_lock, self.interface, flags) }
    }

    /// Wrapper of `GBL_EFI_FASTBOOT_PROTOCOL.get_partition_permissions()`
    pub fn get_partition_permissions(&self, part_name: &str) -> Result<u64> {
        let mut permissions = 0u64;

        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // No parameters are retained, all parameters outlive the call,
        // and no pointers are Null.
        unsafe {
            efi_call!(
                self.interface()?.get_partition_permissions,
                self.interface,
                part_name.as_ptr(),
                part_name.len(),
                &mut permissions
            )?
        };
        Ok(permissions)
    }

    /// Wrapper of `GBL_EFI_FASTBOOT_PROTOCOL.wipe_user_data()`
    pub fn wipe_user_data(&self) -> Result<()> {
        // SAFETY:
        // `self.interface()?` guarantees self.interface is non-null and points to a valid object
        // established by `Protocol::new()`.
        // `self.interface` is an input parameter and will not be retained. It outlives the call.
        unsafe { efi_call!(self.interface()?.wipe_user_data, self.interface) }
    }

    /// Wrapper of `GBL_EFI_FASTBOOT_PROTOCOL.serial_number`
    pub fn serial_number(&self) -> Result<&str> {
        let serial_number = &self.interface()?.serial_number;
        let null_idx = serial_number.iter().position(|c| *c == 0).unwrap_or(serial_number.len());
        Ok(from_utf8(&serial_number[..null_idx])?)
    }

    /// Wrapper of `GBL_EFI_FASTBOOT_PROTOCOL.version`
    pub fn version(&self) -> Result<u32> {
        Ok(self.interface()?.version)
    }
}

/// Iterator over fastboot variables.
pub struct VarIterator<'a> {
    protocol: &'a Protocol<'a, GblFastbootProtocol>,
    token: Token,
}

impl<'a> VarIterator<'a> {
    /// Tries to construct a new iterator over fastboot variables.
    /// Returns Err if the call to protocol.start_var_iterator fails.
    pub fn try_new(protocol: &'a Protocol<'a, GblFastbootProtocol>) -> Result<Self> {
        let token = protocol.start_var_iterator()?;
        Ok(Self { protocol, token })
    }
}

impl<'a> Iterator for VarIterator<'a> {
    type Item = (ArrayVec<GblEfiFastbootArg, MAX_ARGS>, Token);
    fn next(&mut self) -> Option<Self::Item> {
        let mut args = [GblEfiFastbootArg::default(); MAX_ARGS];

        let prev_token = self.token;
        let (len, token) = self.protocol.get_next_var_args(&mut args, self.token).ok()?;
        self.token = token;

        if len == 0 {
            None
        } else {
            let mut args = ArrayVec::from(args);
            args.truncate(len);
            Some((args, prev_token))
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test::{generate_protocol, run_test};
    use crate::EfiEntry;
    use core::slice;
    use core::{
        ffi::{c_void, CStr},
        ptr::addr_of,
    };
    use efi_types::{
        EfiStatus, EFI_STATUS_BUFFER_TOO_SMALL, EFI_STATUS_INVALID_PARAMETER, EFI_STATUS_NOT_FOUND,
        EFI_STATUS_SUCCESS,
    };

    #[derive(Copy, Clone, Debug)]
    struct VarEntry<'a, 'b> {
        var_args: &'a [GblEfiFastbootArg],
        val: &'b CStr,
    }

    // SAFETY:
    // All VarEntry entities are immutable and static.
    unsafe impl Sync for VarEntry<'static, 'static> {}

    fn count_bytes_cstr(cstr: &CStr) -> usize {
        cstr.to_bytes_with_nul().iter().position(|c| *c == 0).unwrap()
    }

    unsafe fn join_args(args: &[GblEfiFastbootArg], conjunction: &str) -> String {
        args.iter()
            .map(|arg| {
                // SAFETY: It is the caller's responsibility to verify that `arg.str_utf8`
                // points to a byte slice of length `arg.len`.
                core::str::from_utf8(unsafe { slice::from_raw_parts(arg.str_utf8, arg.len) })
                    .unwrap()
            })
            .fold(String::new(), |mut acc, s| {
                acc.push_str(s);
                acc.push_str(conjunction);
                acc
            })
    }

    const fn from_str(s: &str) -> GblEfiFastbootArg {
        GblEfiFastbootArg { str_utf8: s.as_ptr(), len: s.len() }
    }

    static VARS: &[VarEntry] = &[
        VarEntry { var_args: &[from_str("bivalve")], val: c"clam" },
        VarEntry { var_args: &[from_str("cephalopod"), from_str("nautiloid")], val: c"nautilus" },
        VarEntry { var_args: &[from_str("cephalopod"), from_str("coleoid")], val: c"squid" },
        VarEntry {
            var_args: &[from_str("gastropod"), from_str("muricidae"), from_str("nucella")],
            val: c"whelk",
        },
    ];

    #[derive(Copy, Clone, Debug)]
    struct PtrWrapper<T> {
        ptr: *const T,
    }

    impl<T> PtrWrapper<T> {
        const fn new(ptr: *const T) -> Self {
            Self { ptr }
        }
        const fn get(&self) -> *const T {
            self.ptr
        }
    }

    static VARS_ADDR: PtrWrapper<VarEntry> = PtrWrapper::new(addr_of!(VARS[0]));
    // SAFETY
    // `VARS_ADDR` is a known valid pointer to a known-length array of VarEntry.
    // `VARS_ADDR + VARS.len()` is extremely unlikely to overwrap,
    // and `VARS_END` is never dereferenced.
    static VARS_END: PtrWrapper<VarEntry> =
        PtrWrapper::new(unsafe { VARS_ADDR.get().add(VARS.len()) });

    // SAFETY
    // PtrWrapper and the pointer it wraps are immutable.
    unsafe impl<T> Sync for PtrWrapper<T> {}

    unsafe fn arg_slices_equal_p(lhs: &[GblEfiFastbootArg], rhs: &[GblEfiFastbootArg]) -> bool {
        if lhs.len() != rhs.len() {
            return false;
        }

        // SAFETY:
        // It is the caller's responsibility to guarantee that for each element
        // 'arg' of `lhs`, `arg.str_utf8` is a valid UTF-8 encoded string of length `arg.len`.
        let lhs = lhs.iter().map(|arg| unsafe {
            core::str::from_utf8_unchecked(core::slice::from_raw_parts(arg.str_utf8, arg.len))
        });
        // SAFETY:
        // It is the caller's responsibility to guarantee that for each element
        // 'arg' of `rhs`, `arg.str_utf8` is a valid UTF-8 encoded string of length `arg.len`.
        let rhs = rhs.iter().map(|arg| unsafe {
            core::str::from_utf8_unchecked(core::slice::from_raw_parts(arg.str_utf8, arg.len))
        });

        core::iter::zip(lhs, rhs).all(|(l, r)| l == r)
    }

    unsafe extern "C" fn get_var(
        _: *mut GblEfiFastbootProtocol,
        args: *const GblEfiFastbootArg,
        args_len: usize,
        buffer: *mut u8,
        bufsize: *mut usize,
        _token: *const c_void,
    ) -> EfiStatus {
        if args.is_null() || buffer.is_null() || bufsize.is_null() {
            return EFI_STATUS_INVALID_PARAMETER;
        }
        // SAFETY:
        // The check at the beginning of the function guarantees that `args` is not Null.
        // It is the caller's responsibility to guarantee that `args` points to a valid
        // array of initialized GblEfiFastbootArg structs of length `args_len`.
        let args = unsafe { core::slice::from_raw_parts(args, args_len) };

        // SAFETY:
        // All elements of `VARS` contain valid UTF-8 encoded strings.
        // It is the caller's responsibility to guarantee that all elements of `args`
        // contain valid UTF-8 encoded strings.
        let entry = VARS.iter().find(|entry| unsafe { arg_slices_equal_p(args, &entry.var_args) });
        if let Some(entry) = entry {
            let val_len = count_bytes_cstr(entry.val);
            // SAFETY:
            // `bufsize` is not Null due to check at beginning of function.
            // Caller is responsible for passing a well-aligned pointer to a valid usize.
            let bs = unsafe { *bufsize };
            // SAFETY:
            // `bufsize` is not Null due to check at beginning of function.
            // It is the caller's responsibility to pass a valid, well-aligned pointer as `bufsize`.
            unsafe { *bufsize = val_len };
            if val_len > bs {
                EFI_STATUS_BUFFER_TOO_SMALL
            } else {
                // SAFETY:
                // `buffer` is not Null due to check at beginning of function.
                // It is the caller's responsibiltiy to pass a valid, well-aligned pointer
                // to an array of `u8` at least as long as the initial value of `bufsize`.
                unsafe { buffer.copy_from(entry.val.to_bytes().as_ptr(), *bufsize) };
                EFI_STATUS_SUCCESS
            }
        } else {
            EFI_STATUS_NOT_FOUND
        }
    }

    unsafe extern "C" fn start_var_iterator(
        _: *mut GblEfiFastbootProtocol,
        token: *mut *const c_void,
    ) -> EfiStatus {
        if token.is_null() {
            return EFI_STATUS_INVALID_PARAMETER;
        }

        // SAFETY:
        // `token` is not Null.
        // It is the caller's responsibility to pass a valid,
        // well aligned pointer as `token`.
        // `VARS_ADDR` contains a valid pointer to a static array.
        unsafe { *token = VARS_ADDR.get() as *const c_void };
        EFI_STATUS_SUCCESS
    }

    unsafe extern "C" fn get_next_var_args(
        _: *mut GblEfiFastbootProtocol,
        args: *mut GblEfiFastbootArg,
        args_len: *mut usize,
        token: *mut *const c_void,
    ) -> EfiStatus {
        if args.is_null() || args_len.is_null() || token.is_null() {
            return EFI_STATUS_INVALID_PARAMETER;
        }

        // SAFETY:
        // `token` is not Null due to check at beginning of function.
        // caller is responsible for passing a valid, well-aligned pointer.
        let pos = unsafe { *token.cast::<*const VarEntry>() };
        if pos == VARS_END.get() {
            // SAFETY:
            // `args_len` is not null due to check at beginning of funcion.
            // caller is responsible for passing a valid, well-aligned pointer as `args_len`.
            unsafe { *args_len = 0 };
            return EFI_STATUS_SUCCESS;
        } else if pos < VARS_ADDR.get() || pos > VARS_END.get() {
            return EFI_STATUS_INVALID_PARAMETER;
        }

        // SAFETY:
        // `args_len` is not Null due to check at beginning of function.
        // caller is responsible for passing a valid, well-aligned pointer for args_len.
        let args_max_len = unsafe { *args_len };

        // SAFETY:
        // `pos` is between `&VARS` inclusive and `&VARS + VARS.len()` exclusive
        // due to check earlier.
        let elt = unsafe { *pos };
        // SAFETY:
        // `args_len` is not Null.
        // caller is responsible for passing a valid, well-aligned pointer.
        unsafe { *args_len = elt.var_args.len() };
        if args_max_len < elt.var_args.len() {
            return EFI_STATUS_BUFFER_TOO_SMALL;
        }

        for (i, varg) in elt.var_args.iter().enumerate() {
            // SAFETY:
            // `args` is not Null due to check at beginning of function.
            // `args_len` is at least as large as as `elt.var_args.len()`
            // due to check before returning BUFFER_TOO_SMALL.
            // It is the caller's responsibility to guarantee that `args` is a valid
            // array of at least `args_len` length.
            unsafe { *args.add(i) = *varg };
        }
        // SAFETY:
        // `token` is not Null due to check at beginning of function.
        // `pos.add(1)` either points to a valid entry in `VARS` or
        // one past the end of `VARS`, which is a valid pointer to construct
        // for the purpose of checking for the end of iteration.
        unsafe { *token = pos.add(1).cast::<c_void>() };

        EFI_STATUS_SUCCESS
    }

    #[test]
    fn test_var_iterator() {
        run_test(|image_handle, systab_ptr| {
            let mut fb = GblEfiFastbootProtocol {
                start_var_iterator: Some(start_var_iterator),
                get_next_var_args: Some(get_next_var_args),
                ..Default::default()
            };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol = generate_protocol::<GblFastbootProtocol>(&efi_entry, &mut fb);
            let var_iter = protocol.var_iter().unwrap();

            // SAFETY:
            // All elements of `VARS`, and therefore all elements of `var_iter`,
            // contain valid UTF-8 encoded strings.
            let actual: Vec<String> = var_iter
                .map(|(args, _token): (_, Token)| unsafe { join_args(&args, ":") })
                .collect();

            let expected = &[
                "bivalve:",
                "cephalopod:nautiloid:",
                "cephalopod:coleoid:",
                "gastropod:muricidae:nucella:",
            ];

            assert_eq!(expected, actual.as_slice());
        });
    }

    #[test]
    fn test_get_var() {
        run_test(|image_handle, systab_ptr| {
            let mut fb = GblEfiFastbootProtocol { get_var: Some(get_var), ..Default::default() };
            let efi_entry = EfiEntry { image_handle, systab_ptr };
            let protocol = generate_protocol::<GblFastbootProtocol>(&efi_entry, &mut fb);

            let args = "cephalopod:coleoid".split(':');
            let mut buffer = [0u8; 32];
            let len = protocol.get_var(args, &mut buffer).unwrap();
            let actual = std::str::from_utf8(&buffer[..len]).unwrap();
            assert_eq!(actual, "squid");

            let args = "cephalopod:nautiloid".split(':');
            let len = protocol.get_var_with_hint(args, &mut buffer, Token::new()).unwrap();
            let actual = std::str::from_utf8(&buffer[..len]).unwrap();
            assert_eq!(actual, "nautilus");
        });
    }

    #[test]
    fn test_serial_number() {
        run_test(|image_handle, systab_ptr| {
            // Serial number is shorter than max length and contains non-ASCII unicode.
            let austria = "Österreich";

            let mut fb = GblEfiFastbootProtocol { ..Default::default() };
            fb.serial_number.as_mut_slice()[..austria.len()].copy_from_slice(austria.as_bytes());
            let efi_entry = EfiEntry { image_handle, systab_ptr };

            let protocol = generate_protocol::<GblFastbootProtocol>(&efi_entry, &mut fb);

            // Don't include trailing Null terminators.
            assert_eq!(protocol.serial_number().unwrap().len(), 11);
            assert_eq!(protocol.serial_number().unwrap(), austria);
        });
    }

    #[test]
    fn test_serial_number_max_length() {
        run_test(|image_handle, systab_ptr| {
            let mut fb = GblEfiFastbootProtocol { serial_number: [71u8; 32], ..Default::default() };
            let efi_entry = EfiEntry { image_handle, systab_ptr };

            let protocol = generate_protocol::<GblFastbootProtocol>(&efi_entry, &mut fb);

            assert_eq!(protocol.serial_number().unwrap().len(), 32);
            assert_eq!(protocol.serial_number().unwrap(), "GGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGG");
        });
    }

    #[test]
    fn test_serial_number_invalid_utf8() {
        run_test(|image_handle, systab_ptr| {
            let mut fb = GblEfiFastbootProtocol { serial_number: [0xF8; 32], ..Default::default() };
            let efi_entry = EfiEntry { image_handle, systab_ptr };

            let protocol = generate_protocol::<GblFastbootProtocol>(&efi_entry, &mut fb);

            assert_eq!(protocol.serial_number(), Err(Error::InvalidInput));
        });
    }
}
