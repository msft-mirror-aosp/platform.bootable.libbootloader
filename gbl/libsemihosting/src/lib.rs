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
pub use libgblutils::arch_timestamp;
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
///
/// # Safety
///
/// * `param` must point to a valid `usize` array with the argument count required by `op_code`.
/// * Any pointer and length arguments in the array must describe valid memory slices for the
///   duration of the call (readable for `Open`, `System`, `Write`, and `Remove`; writable for
///   `Read`).
#[cfg(target_arch = "aarch64")]
unsafe fn semihosting_call(op_code: OpCode, param: usize) -> Result<usize, Error> {
    let mut ret = usize::from(op_code);
    // SAFETY: By safety contract, `param` points to a valid semihosting argument block for
    // `op_code` and any referenced buffers are valid for the duration of the `hlt 0xF000` call.
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

/// Semihosting call for riscv64
///
/// # Safety
///
/// * `param` must point to a valid `usize` array with the argument count required by `op_code`.
/// * Any pointer and length arguments in the array must describe valid memory slices for the
///   duration of the call (readable for `Open`, `System`, `Write`, and `Remove`; writable for
///   `Read`).
#[cfg(target_arch = "riscv64")]
unsafe fn semihosting_call(_: OpCode, _: usize) -> Result<usize, Error> {
    unimplemented!()
}

/// Semihosting call for x86_64 QEMU using COM1 serial, `fw_cfg`, and ACPI/`isa-debug-exit`.
///
/// # Safety
///
/// * `param` must point to a valid `usize` array with the argument count required by `op_code`:
///   - `WriteC`, `Close`, `FLen`: at least 1 element.
///   - `ExitExtended`, `Remove`: at least 2 elements (`Remove`: `[path_ptr, path_len]`).
///   - `System`: at least 2 elements `[cmd_ptr, cmd_len]` where `cmd_ptr` points to `cmd_len`
///     valid readable bytes.
///   - `Open`: at least 3 elements `[path_ptr, mode, path_len]` where `path_ptr` points to
///     `path_len` valid readable bytes.
///   - `Read`: at least 3 elements `[handle, buf_ptr, buf_len]` where `buf_ptr` points to
///     `buf_len` valid writable bytes.
#[cfg(target_arch = "x86_64")]
unsafe fn semihosting_call(op_code: OpCode, param: usize) -> Result<usize, Error> {
    use core::{
        cmp::min,
        ptr,
        slice::from_raw_parts,
        sync::atomic::{compiler_fence, AtomicUsize, Ordering},
    };
    use x86_64::instructions::{
        hlt,
        port::{PortRead, PortWrite},
    };

    const COM1_DATA_PORT: u16 = 0x3f8;
    const COM1_LINE_STATUS_PORT: u16 = 0x3fd;
    const UART_LSR_THRE: u8 = 0x20;
    const ACPI_PM1A_CNT_PORT: u16 = 0x604;
    const ACPI_SLP_TYP_S5_PIIX4: u16 = 0x2000;
    const ACPI_SLP_TYP_S5_Q35: u16 = 0x3400;
    const ISA_DEBUG_EXIT_PORT: u16 = 0xf4;
    const FW_CFG_PORT_SEL: u16 = 0x510;
    const FW_CFG_PORT_DATA: u16 = 0x511;
    const FW_CFG_PORT_DMA_HIGH: u16 = 0x514;
    const FW_CFG_PORT_DMA_LOW: u16 = 0x518;
    const FW_CFG_FILE_DIR: u16 = 0x0019;
    const FW_CFG_DMA_CTL_ERROR: u32 = 1 << 0;
    const FW_CFG_DMA_CTL_READ: u32 = 1 << 1;
    const FW_CFG_DMA_CTL_SELECT: u32 = 1 << 3;
    const FW_CFG_FILE_NAME_SIZE: usize = 56;
    const HANDLE_SIZE_SHIFT: usize = 16;
    const HANDLE_SELECT_MASK: usize = 0xffff;
    const INVALID_ENV_HANDLE: usize = 1;

    static LAST_ENV_HANDLE: AtomicUsize = AtomicUsize::new(INVALID_ENV_HANDLE);

    #[repr(C, packed)]
    struct FwCfgDmaAccess {
        control: u32,
        length: u32,
        address: u64,
    }

    /// Reads bytes from `FW_CFG_PORT_DATA` into `buf`.
    ///
    /// # Safety
    ///
    /// Caller must ensure that a valid `fw_cfg` entry has been selected via `FW_CFG_PORT_SEL` and
    /// that execution is at CPL 0 in QEMU.
    unsafe fn fw_cfg_read(buf: &mut [u8]) {
        // SAFETY: By safety contract, a valid `fw_cfg` entry is selected on `FW_CFG_PORT_SEL` and
        // execution is at CPL 0 in QEMU, so reading `FW_CFG_PORT_DATA` returns the selected entry
        // bytes without affecting memory safety.
        buf.iter_mut().for_each(|b| *b = unsafe { u8::read_from_port(FW_CFG_PORT_DATA) });
    }
    /// Looks up `target` in the QEMU `fw_cfg` directory and returns an encoded
    /// `(size << 16) | select` handle if found.
    ///
    /// # Safety
    ///
    /// Caller must ensure that execution is at CPL 0 in QEMU with a valid `fw_cfg` device at
    /// `FW_CFG_PORT_SEL` and `FW_CFG_PORT_DATA`.
    unsafe fn fw_cfg_open(target: &[u8]) -> Option<usize> {
        let target = target.strip_prefix(b"opt/").unwrap_or(target);
        // SAFETY: By safety contract, execution is at CPL 0 in QEMU with a valid `fw_cfg` device;
        // writing `FW_CFG_FILE_DIR` to `FW_CFG_PORT_SEL` selects the read-only `fw_cfg` directory
        // table, satisfying the precondition of `fw_cfg_read` to read the entry count and headers
        // into local buffers.
        unsafe {
            u16::write_to_port(FW_CFG_PORT_SEL, FW_CFG_FILE_DIR);
            let mut count = [0u8; 4];
            fw_cfg_read(&mut count);
            for _ in 0..u32::from_be_bytes(count) {
                let (mut sz, mut sel, mut res, mut name) =
                    ([0u8; 4], [0u8; 2], [0u8; 2], [0u8; FW_CFG_FILE_NAME_SIZE]);
                fw_cfg_read(&mut sz);
                fw_cfg_read(&mut sel);
                fw_cfg_read(&mut res);
                fw_cfg_read(&mut name);
                let len = name.iter().position(|&b| b == 0).unwrap_or(name.len());
                let entry = name[..len].strip_prefix(b"opt/").unwrap_or(&name[..len]);
                if entry == target {
                    return Some(
                        ((u32::from_be_bytes(sz) as usize) << HANDLE_SIZE_SHIFT)
                            | (u16::from_be_bytes(sel) as usize),
                    );
                }
            }
        }
        None
    }

    let args = param as *const usize;
    // SAFETY:
    // * By the caller's safety contract on `semihosting_call`, `args` points to a valid `usize`
    //   array with the element count required by `op_code`, and any pointer/length pairs in `args`
    //   (for `System`, `Open`, and `Read`) point to valid readable or writable buffers for the
    //   duration of this call.
    // * Execution is at CPL 0 in QEMU, and I/O port accesses use dedicated QEMU device ports:
    //   - `COM1_LINE_STATUS_PORT` / `COM1_DATA_PORT`: UART line-status and transmit registers.
    //   - `ACPI_PM1A_CNT_PORT` / `ISA_DEBUG_EXIT_PORT`: QEMU ACPI S5 and debug-exit ports.
    //   - `FW_CFG_PORT_DMA_HIGH` / `FW_CFG_PORT_DMA_LOW`: `dma` is a valid stack-allocated
    //     `FwCfgDmaAccess` descriptor writing `to_read <= buf_len` bytes into the caller's valid
    //     writable buffer `buf_ptr`, ordered with `SeqCst` compiler fences and checked via
    //     `read_volatile` on the stack-allocated `dma.control` field.
    unsafe {
        match op_code {
            OpCode::WriteC => {
                while (u8::read_from_port(COM1_LINE_STATUS_PORT) & UART_LSR_THRE) == 0 {}
                u8::write_to_port(COM1_DATA_PORT, (*args) as u8);
                Ok(0)
            }
            OpCode::ExitExtended => {
                let code = *args.add(1);
                if code == 0 {
                    u16::write_to_port(ACPI_PM1A_CNT_PORT, ACPI_SLP_TYP_S5_PIIX4);
                    u16::write_to_port(ACPI_PM1A_CNT_PORT, ACPI_SLP_TYP_S5_Q35);
                    loop {
                        hlt();
                    }
                }
                u32::write_to_port(ISA_DEBUG_EXIT_PORT, code as u32);
                loop {}
            }
            OpCode::System => {
                // `getenv` invokes `system` with `printf "%s" "$<VAR>" > getenv.tmp`.
                // Extract `<VAR>` and open the corresponding `opt/<VAR>` fw_cfg entry.
                let cmd = from_raw_parts((*args) as *const u8, *args.add(1));
                let var = cmd
                    .strip_prefix(b"printf \"%s\" \"$")
                    .and_then(|s| s.split(|&b| b == b'"').next())
                    .unwrap_or(b"");
                LAST_ENV_HANDLE
                    .store(fw_cfg_open(var).unwrap_or(INVALID_ENV_HANDLE), Ordering::Relaxed);
                Ok(0)
            }
            OpCode::Open => {
                let path = from_raw_parts((*args) as *const u8, *args.add(2));
                if path == b"getenv.tmp" {
                    return Ok(LAST_ENV_HANDLE.load(Ordering::Relaxed));
                }
                Ok(fw_cfg_open(path).unwrap_or(usize::MAX))
            }
            OpCode::Close | OpCode::Remove => Ok(0),
            OpCode::FLen => Ok((*args) >> HANDLE_SIZE_SHIFT),
            OpCode::Read => {
                let (handle, buf_ptr, buf_len) = (*args, *args.add(1), *args.add(2));
                let to_read = min(buf_len, handle >> HANDLE_SIZE_SHIFT);
                if to_read > 0 {
                    let select = (handle & HANDLE_SELECT_MASK) as u32;
                    let dma_ctl =
                        (select << HANDLE_SIZE_SHIFT) | FW_CFG_DMA_CTL_SELECT | FW_CFG_DMA_CTL_READ;
                    let mut dma = FwCfgDmaAccess {
                        control: dma_ctl.to_be(),
                        length: (to_read as u32).to_be(),
                        address: (buf_ptr as u64).to_be(),
                    };
                    let dma_addr = ptr::addr_of_mut!(dma) as u64;
                    compiler_fence(Ordering::SeqCst);
                    u32::write_to_port(FW_CFG_PORT_DMA_HIGH, ((dma_addr >> 32) as u32).to_be());
                    u32::write_to_port(FW_CFG_PORT_DMA_LOW, (dma_addr as u32).to_be());
                    compiler_fence(Ordering::SeqCst);
                    if (u32::from_be(ptr::read_volatile(ptr::addr_of!(dma.control)))
                        & FW_CFG_DMA_CTL_ERROR)
                        != 0
                    {
                        return Ok(usize::MAX);
                    }
                }
                // Semihosting `SYS_READ` returns the number of bytes not filled (`0` on full read).
                Ok(buf_len - to_read)
            }
            _ => Err(Error::Unsupported),
        }
    }
}

/// Writes `args` to a stack parameter block and invokes `semihosting_call`.
///
/// # Safety
///
/// * `args` must have the element count and layout required by `op_code`.
/// * Any pointer and length arguments in `args` must describe valid memory slices for the
///   duration of the call (readable for `Open`, `System`, `Write`, and `Remove`; writable for
///   `Read`).
unsafe fn semihosting_call_with_args<const N: usize>(
    op_code: OpCode,
    args: [usize; N],
) -> Result<usize, Error> {
    let mut volatile_args = [0usize; N];
    for i in 0..N {
        // We need to make sure the arguments are written to memory and not optimized away.
        // SAFETY: `volatile_args[i]` is a valid pointer to a local variable.
        unsafe { core::ptr::write_volatile(&mut volatile_args[i], args[i]) };
    }
    // SAFETY: `volatile_args` is a valid `N`-element stack array initialized from `args`, which
    // satisfies `semihosting_call`'s safety requirements by the caller's safety contract.
    unsafe { semihosting_call(op_code, volatile_args.as_ptr() as _) }
}

/// Run command on the host
pub fn system(cmd: &CStr) -> usize {
    // SAFETY: `OpCode::System` requires `[cmd_ptr, cmd_len]` pointing to `cmd_len` readable bytes.
    // `cmd` is a `&CStr` reference, which guarantees `cmd.as_ptr()` is non-null and points to
    // `cmd.count_bytes()` valid, initialized, readable bytes for the duration of the call.
    unsafe {
        semihosting_call_with_args(OpCode::System, [cmd.as_ptr() as usize, cmd.count_bytes()])
    }
    .unwrap_or(usize::MAX)
}

/// Writes a character to the semihosting console.
pub fn writec(val: u8) {
    // SAFETY: `OpCode::WriteC` expects a 1-element array containing the byte to write.
    let _ = unsafe { semihosting_call_with_args(OpCode::WriteC, [val.into()]) };
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
    // SAFETY: `OpCode::ExitExtended` expects a 2-element array `[reason, exit_code]`.
    let _ = unsafe { semihosting_call_with_args(OpCode::ExitExtended, args) };
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
    // SAFETY: `OpCode::Open` requires `[path_ptr, mode, path_len]` with `path_ptr` pointing to
    // `path_len` readable bytes. `path` is a `&CStr` reference, which guarantees `path.as_ptr()`
    // is non-null and points to `path.count_bytes()` valid, initialized, readable bytes for the
    // duration of the call.
    match unsafe {
        semihosting_call_with_args(
            OpCode::Open,
            [path.as_ptr() as _, mode as _, path.count_bytes()],
        )
    }? {
        usize::MAX => Err(Error::Other(Some("fopen failed"))),
        v => NonZeroUsize::new(v).ok_or(Error::Other(Some("got zero handle"))),
    }
}

/// Closes a file
pub fn fclose(handle: NonZeroUsize) -> Result<(), Error> {
    // SAFETY: `OpCode::Close` expects a 1-element array `[handle]`.
    match unsafe { semihosting_call_with_args(OpCode::Close, [handle.get()]) }? {
        0 => Ok(()),
        _ => Err(Error::Other(Some("fclose() failed"))),
    }
}

/// Reads data from a file
pub fn fread(handle: NonZeroUsize, out: &mut [u8]) -> Result<usize, Error> {
    // SAFETY: `OpCode::Read` requires `[handle, buf_ptr, buf_len]` with `buf_ptr` pointing to
    // `buf_len` writable bytes. `out` is a `&mut [u8]` slice, which guarantees `out.as_mut_ptr()`
    // is non-null and points to `out.len()` valid, exclusively borrowed writable bytes for the
    // duration of the call.
    match unsafe {
        semihosting_call_with_args(OpCode::Read, [handle.get(), out.as_mut_ptr() as _, out.len()])
    }? {
        0 => Ok(out.len()),
        v if v >= out.len() => Err(Error::Other(Some("fread() failed"))),
        v => Ok(out.len() - v),
    }
}

/// Writes data to a file
pub fn fwrite(handle: NonZeroUsize, data: &[u8]) -> Result<(), Error> {
    // SAFETY: `OpCode::Write` requires `[handle, data_ptr, data_len]` with `data_ptr` pointing to
    // `data_len` readable bytes. `data` is a `&[u8]` slice, which guarantees `data.as_ptr()` is
    // non-null and points to `data.len()` valid, initialized, readable bytes for the duration of
    // the call.
    match unsafe {
        semihosting_call_with_args(OpCode::Write, [handle.get(), data.as_ptr() as _, data.len()])
    }? {
        0 => Ok(()),
        _ => Err(Error::Other(Some("fwrite() failed"))),
    }
}

/// Queries file length
pub fn flen(handle: NonZeroUsize) -> Result<usize, Error> {
    // SAFETY: `OpCode::FLen` expects a 1-element array `[handle]`.
    match unsafe { semihosting_call_with_args(OpCode::FLen, [handle.get()]) }? {
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
    // SAFETY: `OpCode::Remove` requires `[path_ptr, path_len]` with `path_ptr` pointing to
    // `path_len` readable bytes. `path` is a `&CStr` reference, which guarantees `path.as_ptr()`
    // is non-null and points to `path.count_bytes()` valid, initialized, readable bytes for the
    // duration of the call.
    match unsafe {
        semihosting_call_with_args(OpCode::Remove, [path.as_ptr() as _, path.count_bytes()])
    }? {
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
