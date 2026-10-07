// Copyright 2026, The Android Open Source Project
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

//! Contains API for semihosting
//!
//! For aarch64, see
//! https://github.com/ARM-software/abi-aa/blob/2982a9f3b512a5bfdc9e3fea5d3b298f9165c36b/semihosting/semihosting.rst
//!
//! For riscv64, see
//! https://docs.riscv.org/reference/platform-software/semihosting/_attachments/riscv-semihosting.pdf

#![cfg_attr(not(test), no_std)]

use core::{ffi::CStr, num::NonZeroUsize};
use liberror::Error;
pub use libutils::arch_timestamp;
use libutils::snprintf;

/// Semihosting operation codes.
#[derive(Copy, Clone, Debug)]
#[repr(usize)]
enum OpCode {
    Open,
    Close,
    WriteC,
    Write,
    Read,
    Remove,
    FLen,
    System,
    ExitExtended,
}

impl From<OpCode> for usize {
    fn from(op_code: OpCode) -> Self {
        match op_code {
            OpCode::Open => 0x1,
            OpCode::Close => 0x2,
            OpCode::WriteC => 0x3,
            OpCode::Write => 0x5,
            OpCode::Read => 0x6,
            OpCode::Remove => 0x0E,
            OpCode::FLen => 0x0C,
            OpCode::System => 0x12,
            OpCode::ExitExtended => 0x20,
        }
    }
}

/// Semihosting exit reasons.
#[derive(Copy, Clone, Debug)]
#[repr(usize)]
enum ExitReason {
    ApplicationExit = 0x20026,
}

/// Semihosting call for aarch64
#[cfg(target_arch = "aarch64")]
fn semihosting_call(op_code: OpCode, param: usize) -> Result<usize, Error> {
    let mut ret = usize::from(op_code);
    // SAFETY: Semihosting API call. The operation does not modify program state.
    unsafe {
        core::arch::asm!(
            "dsb sy",
            "hlt 0xF000",
            inout("x0") ret,
            in("x1") param,
            clobber_abi("C"),
        );
    };
    Ok(ret)
}

#[cfg(target_arch = "riscv64")]
fn semihosting_call(_: OpCode, _: usize) -> Result<usize, Error> {
    unimplemented!()
}

#[cfg(target_arch = "x86_64")]
fn semihosting_call(_: OpCode, _: usize) -> Result<usize, Error> {
    // X86 has no such concept
    Err(Error::Unsupported)
}

fn semihosting_call_with_args<const N: usize>(
    op_code: OpCode,
    args: [usize; N],
) -> Result<usize, Error> {
    let mut volatile_args = [0usize; N];
    for i in 0..N {
        // We need to make sure the arguments are written to memory and not optimized away.
        // SAFETY: `volatile_args[i]` is a valid pointer to a local variable.
        unsafe { core::ptr::write_volatile(&mut volatile_args[i], args[i]) };
    }
    semihosting_call(op_code, volatile_args.as_ptr() as _)
}

/// Run command on the host
pub fn system(cmd: &CStr) -> usize {
    semihosting_call_with_args(OpCode::System, [cmd.as_ptr() as usize, cmd.count_bytes()])
        .unwrap_or(usize::MAX)
}

/// Writes a character to the semihosting console.
pub fn writec(val: u8) {
    let _ = semihosting_call_with_args(OpCode::WriteC, [val.into()]);
}

/// Semihosting console based on writec
pub struct Console {}

impl core::fmt::Write for Console {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        s.as_bytes().iter().for_each(|v| writec(*v));
        Ok(())
    }
}

/// Print to semihosting console
#[macro_export]
macro_rules! print {
    ( $( $x:expr ),* $(,)? ) => {
        {
            use core::fmt::Write;
            write!($crate::Console{}, $($x,)*).unwrap();
        }
    };
}

/// Print line to semihosting console
#[macro_export]
macro_rules! println {
    ( $( $x:expr ),* $(,)? ) => {
        {
            // Print timestamp if supported
            let _ = $crate::arch_timestamp().inspect(|v| {
                $crate::print!("[{:.4}] ", v.as_secs_f32());
            });
            $crate::print!($($x,)*);
            $crate::print!("\r\n");
        }
    };
}

/// Exits system.
pub fn shutdown(exit_code: usize) -> ! {
    let args = [ExitReason::ApplicationExit as usize, exit_code];
    let _ = semihosting_call_with_args(OpCode::ExitExtended, args);
    loop {}
}

/// Mode for opening a file.
#[derive(Copy, Clone, Debug)]
#[repr(usize)]
pub enum OpenMode {
    /// read only.
    ReadOnly = 0,
    /// read, binary,
    ReadBinary = 1,
    /// read, write.
    ReadWrite = 2,
    /// read, write, binary.
    ReadWriteBinary = 3,
    /// write only.
    WriteOnly = 4,
    /// write binary.
    WriteBinary = 5,
    /// write, create if not exists.
    WriteCreate = 6,
    /// write, create, binary.
    WriteCreateBinary = 7,
    /// append only,
    Append = 8,
    /// append, binary,
    AppendBinary = 9,
    /// append, read
    AppendRead = 10,
    /// append, read, binary
    AppendReadBinary = 11,
}

/// Opens a file
pub fn fopen(path: &CStr, mode: OpenMode) -> Result<NonZeroUsize, Error> {
    match semihosting_call_with_args(
        OpCode::Open,
        [path.as_ptr() as _, mode as _, path.count_bytes()],
    )? {
        usize::MAX => Err(Error::Other(Some("fopen failed"))),
        v => NonZeroUsize::new(v).ok_or(Error::Other(Some("got zero handle"))),
    }
}

/// Closes a file
pub fn fclose(handle: NonZeroUsize) -> Result<(), Error> {
    match semihosting_call_with_args(OpCode::Close, [handle.get()])? {
        0 => Ok(()),
        _ => Err(Error::Other(Some("fclose() failed"))),
    }
}

/// Reads data from a file
pub fn fread(handle: NonZeroUsize, out: &mut [u8]) -> Result<usize, Error> {
    match semihosting_call_with_args(
        OpCode::Read,
        [handle.get(), out.as_mut_ptr() as _, out.len()],
    )? {
        0 => Ok(out.len()),
        v if v >= out.len() => Err(Error::Other(Some("fread() failed"))),
        v => Ok(v),
    }
}

/// Writes data to a file
pub fn fwrite(handle: NonZeroUsize, data: &[u8]) -> Result<(), Error> {
    match semihosting_call_with_args(OpCode::Write, [handle.get(), data.as_ptr() as _, data.len()])?
    {
        0 => Ok(()),
        _ => Err(Error::Other(Some("fwrite() failed"))),
    }
}

/// Queries file length
pub fn flen(handle: NonZeroUsize) -> Result<usize, Error> {
    match semihosting_call_with_args(OpCode::FLen, [handle.get()])? {
        usize::MAX => Err(Error::Other(Some("flen() failed"))),
        v => Ok(v),
    }
}

/// Represent a file handle in semihosting context.
pub struct File(NonZeroUsize);

impl File {
    /// Open a file.
    pub fn open(path: &CStr, mode: OpenMode) -> Result<Self, Error> {
        Ok(Self(fopen(path, mode)?))
    }

    /// Writes data to it.
    pub fn write(&mut self, data: &[u8]) -> Result<(), Error> {
        fwrite(self.0, data)
    }

    /// Read data from it.
    pub fn read(&mut self, out: &mut [u8]) -> Result<usize, Error> {
        fread(self.0, out)
    }

    /// Queries file length.
    pub fn len(&self) -> Result<usize, Error> {
        flen(self.0)
    }
}

impl Drop for File {
    fn drop(&mut self) {
        let _ = fclose(self.0);
    }
}

/// Deletes a file on the host.
pub fn remove(path: &CStr) -> Result<(), Error> {
    match semihosting_call_with_args(OpCode::Remove, [path.as_ptr() as _, path.count_bytes()])? {
        0 => Ok(()),
        _ => Err(Error::Other(Some("remove() failed"))),
    }
}

/// Queries the value of a host environment variable or all environment variables.
///
/// If `name` is `Some`, uses the semihosting `system` command to dump the specific
/// variable value to a temporary file on the host. If `name` is `None`, dumps all
/// environment variables (the output of `env`).
/// Reads the file into `buf` and removes the temporary file.
///
/// Returns the string slice of `buf` containing the output.
pub fn getenv<'a>(name: Option<&str>, buf: &'a mut [u8]) -> Result<&'a str, Error> {
    const TMP_FILE: &CStr = c"getenv.tmp";
    let mut cmd_buf = [0u8; 128];
    // Construct host commands. i.e.:
    //  - `printf "%s" "${}" > getenv.tmp\0`
    //  - `env > getenv.tmp\0`
    let cmd_str = match name {
        Some(var) => snprintf!(cmd_buf, "printf \"%s\" \"${}\" > {}\0", var, TMP_FILE.to_str()?),
        None => snprintf!(cmd_buf, "env > {}\0", TMP_FILE.to_str()?),
    };

    // Execute the command.
    if system(CStr::from_bytes_with_nul(cmd_str.as_bytes())?) != 0 {
        return Err(Error::Other(Some("system() call failed")));
    }

    // Read the content of tmp file.
    let read_len = (|| {
        let mut file = File::open(TMP_FILE, OpenMode::ReadOnly)?;
        match file.len()? {
            v if v <= buf.len() => file.read(&mut buf[..v]),
            v => Err(Error::BufferTooSmall(Some(v))),
        }
    })();

    // Remove tmp file.
    let _ = remove(TMP_FILE);
    match read_len? {
        0 => Err(Error::NotFound),
        n => Ok(core::str::from_utf8(&buf[..n])?),
    }
}

/// Queries a host environment variable and parses its value as a hexadecimal integer.
///
/// Supports optional `"0x"` or `"0X"` prefixes.
pub fn getenv_as_usize(name: &str) -> Result<usize, Error> {
    let mut buf = [0u8; 32];
    let val = getenv(Some(name), &mut buf)?.trim();
    let val = val.strip_prefix("0x").or_else(|| val.strip_prefix("0X")).unwrap_or(val);
    Ok(usize::from_str_radix(val, 16)?)
}
