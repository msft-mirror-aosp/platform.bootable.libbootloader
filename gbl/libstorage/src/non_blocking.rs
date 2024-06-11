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

use crate::{
    is_aligned, is_buffer_aligned, BlockInfo, BlockIo, BlockIoError, Result, StorageError,
};
use core::{marker::PhantomData, mem::swap};

/// `IoStatus` represents the status of a non-blocking IO.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum IoStatus {
    /// The IO request is aborted due to error or user request.
    Aborted,
    /// The IO request is completed.
    Completed,
    /// The IO request is still pending.
    Pending,
    /// The IO request doesn't exist.
    NotFound,
}

/// `NonBlockingBlockIo` provides interfaces for performing non-blocking read/write.
///
/// # Safety
///
/// * Implementation must guarantee that `Self::check_status(buffer)` returns `IoStatus::Pending`
///   if and only if it is retaining `buffer`. Once the implementation stops returning
///   `IoStatus::Pending` for a buffer, it must not retain the buffer again until a new read/write
///   request using the buffer is made.
/// * The buffer pointer passed to `Self::check_status(buffer)` should only be used as a key value
///   for looking up previously made read/write IO requests being tracked. Implementation should not
///   attempt to derefernce it without confirming that the corresponding IO exists. If caller passes
///   an invalid buffer pointer, implementation should be able to safely return
///   `IoStatus::NotFound`.
/// * If `Self::write_blocks()`/`Self::read_blocks()` returns error, the input buffer must not be
///   retained.
pub unsafe trait NonBlockingBlockIo {
    /// Returns the `BlockInfo` for this block device.
    fn info(&mut self) -> BlockInfo;

    /// Perform non-blocking writes of data to the block device.
    ///
    /// # Args
    ///
    /// * `blk_offset`: Offset in number of blocks.
    /// * `buffer`: Pointer to the data buffer.
    ///
    /// # Returns
    ///
    /// * Returns Ok(()) if the IO request is accepted.
    /// * Returns Err(BlockIoError::MediaBusy) if the device is busy and the caller should try
    ////  again later.
    /// * Returns Err(BlockIoError::Others()) for other errors.
    ///
    /// # Safety
    ///
    /// * Caller must ensure that `buffer` points to a valid buffer.
    /// * If the method returns Ok(()), caller must ensure that `buffer` remains valid and has no
    ///   other references until `Self::check_status(buffer)` no longer returns
    ///   `IoStatus::Pending`.
    unsafe fn write_blocks(
        &mut self,
        blk_offset: u64,
        buffer: *mut [u8],
    ) -> core::result::Result<(), BlockIoError>;

    /// Perform non-blocking read of data from the block device.
    ///
    /// # Args
    ///
    /// * `blk_offset`: Offset in number of blocks.
    /// * `buffer`: Pointer to the output buffer.
    ///
    /// # Returns
    ///
    /// * Returns Ok(()) if the IO request is accepted.
    /// * Returns Err(BlockIoError::MediaBusy) if the device is busy and the caller should try again
    ///   later.
    /// * Returns Err(BlockIoError::Others()) for other errors.
    ///
    /// # Safety
    ///
    /// * Caller must ensure that `buffer` points to a valid buffer.
    /// * If the method returns Ok(()), caller must ensure that `buffer` remains valid and has no
    ///   other references until `Self::check_status(buffer)` no longer returns
    ///   `IoStatus::Pending`.
    unsafe fn read_blocks(
        &mut self,
        blk_offset: u64,
        buffer: *mut [u8],
    ) -> core::result::Result<(), BlockIoError>;

    /// Checks the status of the non-blocking read/write associated with the given buffer.
    ///
    /// # Args
    ///
    /// * `buf`: The buffer previously passed to `read_blocks()` / `write_blocks()`.
    ///
    /// # Returns
    ///
    /// * Returns `IoStatus::NotFound` if the request is not found.
    /// * Returns `IoStatus::Pending` if the request is still pending.
    /// * Returns `IoStatus::Completed` if the request has been completed successfully.
    ///   Implementation can stop tracking the request and should return `IoStatus::NotFound` on
    ///   subsequent queries until a new read/write request is made with the same buffer.
    /// * Returns `IoStatus::Aborted` if the request is aborted, due to error or caller invoking
    ///   `Self::abort()`. Implementation can stop tracking the request and should return
    ///   `IoStatus::NotFound` on subsequent queries until a new read/write request is made with
    ///   the same buffer.
    fn check_status(&mut self, buf: *mut [u8]) -> IoStatus;

    /// Aborts pending non-blocking IO requests.
    ///
    /// For currently pending requests, `Self::check_status(buf)` should eventually return
    /// `IoStatus::Aborted` at some point in the future. For already completed requests,
    /// `Self::check_status(buf)` should continue to return `IoStatus::Completed`.
    fn abort(&mut self) -> core::result::Result<(), BlockIoError>;
}

// Implements the blocking version `BlockIo` for a `&mut dyn NonBlockingBlockIo`
impl BlockIo for &mut dyn NonBlockingBlockIo {
    fn info(&mut self) -> BlockInfo {
        (*self).info()
    }

    fn read_blocks(
        &mut self,
        blk_offset: u64,
        out: &mut [u8],
    ) -> core::result::Result<(), BlockIoError> {
        let ptr = out as *mut [u8];
        // SAFETY:
        // * This function blocks until the non-blocking IO is no longer pending.
        // * Buffer by `ptr` is not used elsewhere.
        unsafe { (*self).read_blocks(blk_offset, ptr)? };
        loop {
            match self.check_status(ptr) {
                IoStatus::Pending => {}
                IoStatus::Completed => return Ok(()),
                IoStatus::Aborted => return Err(BlockIoError::Others(Some("Read aborted"))),
                IoStatus::NotFound => panic!("Unexpected IoStatus::NotFound"),
            }
        }
    }

    fn write_blocks(
        &mut self,
        blk_offset: u64,
        data: &mut [u8],
    ) -> core::result::Result<(), BlockIoError> {
        let ptr = data as *mut [u8];
        // SAFETY:
        // * This function blocks until the non-blocking IO is no longer pending.
        // * Buffer by `ptr` is not used elsewhere.
        unsafe { (*self).write_blocks(blk_offset, ptr)? };
        loop {
            match self.check_status(ptr) {
                IoStatus::Pending => {}
                IoStatus::Completed => return Ok(()),
                IoStatus::Aborted => return Err(BlockIoError::Others(Some("write aborted"))),
                IoStatus::NotFound => panic!("Unexpected IoStatus::NotFound"),
            }
        }
    }
}

/// `BlockDeviceIo` represents either a `BlockIo` or `NonBlockingBlockIo`.
pub enum BlockDeviceIo<'a> {
    Blocking(&'a mut dyn BlockIo),
    NonBlocking(&'a mut dyn NonBlockingBlockIo),
}

impl<'a> From<&'a mut dyn BlockIo> for BlockDeviceIo<'a> {
    fn from(val: &'a mut dyn BlockIo) -> Self {
        Self::Blocking(val)
    }
}

impl<'a> From<&'a mut dyn NonBlockingBlockIo> for BlockDeviceIo<'a> {
    fn from(val: &'a mut dyn NonBlockingBlockIo) -> Self {
        Self::NonBlocking(val)
    }
}

impl<'a> BlockDeviceIo<'a> {
    /// Casts to a `BlockIo` trait object.
    fn as_block_io(&mut self) -> &mut dyn BlockIo {
        match self {
            Self::Blocking(v) => *v,
            Self::NonBlocking(v) => v,
        }
    }

    /// Creates a sub-instance that borrows internal fields.
    ///
    /// This creates an instance where its lifetime parameter 'a is coerced to the life time of the
    /// current object. This will be used for creating a local instance for blocking operation.
    fn scoped_instance(&mut self) -> BlockDeviceIo {
        match self {
            Self::Blocking(v) => BlockDeviceIo::Blocking(*v),
            Self::NonBlocking(v) => BlockDeviceIo::NonBlocking(*v),
        }
    }
}

/// `IoBufferState` wraps a raw buffer and keeps track of its use state in non-blocking IO.
#[derive(Debug)]
enum IoBufferState<'a> {
    Ready(&'a mut [u8], IoStatus),
    // (Original buffer &mut [u8], subslice pointer passed to non-blocking IO, phantom)
    Pending(*mut [u8], *mut [u8], PhantomData<&'a mut [u8]>),
}

/// `IoBuffer` wraps a `IoBufferState` and implements `Drop` to check that the buffer is not
/// pending when going out of scope.
#[derive(Debug)]
struct IoBuffer<'a>(IoBufferState<'a>);

impl Drop for IoBuffer<'_> {
    fn drop(&mut self) {
        // Panics if an `IoBuffer` goes out of scope in a pending state.
        // This is merely used for safety reasoning in `read_io_buffer()`/`write_io_buffer()` and
        // should not be triggered if implementation logic is incorrect. Specifically, `IoBuffer`
        // is only used internally in `BlockDeviceEx`. When `BlockDeviceEx` goes out of scope, it
        // performs abort() and sync() to make sure no buffer is pending.
        assert!(!self.is_pending());
    }
}

impl<'a> IoBuffer<'a> {
    /// Creates a new instance.
    fn new(buffer: &'a mut [u8]) -> Self {
        Self(IoBufferState::Ready(buffer, IoStatus::Completed))
    }

    /// Gets the cached status.
    ///
    /// To update the cached status, caller should call `Self::update()` first.
    fn status(&self) -> IoStatus {
        match self.0 {
            IoBufferState::Ready(_, status) => status,
            _ => IoStatus::Pending,
        }
    }

    /// Returns whether the buffer is pending in a non-blocking IO.
    ///
    /// The returned value is based on the cached status. To update the cached status, caller
    /// should call `Self::update()` first.
    fn is_pending(&self) -> bool {
        matches!(self.status(), IoStatus::Pending)
    }

    /// Returns whether the corresponding IO is aborted.
    ///
    /// The returned value is based on the cached status. To update the cached status, caller
    /// should call `Self::update()` first.
    fn is_aborted(&self) -> bool {
        matches!(self.status(), IoStatus::Aborted)
    }

    /// Sets buffer to the pending state.
    ///
    /// Returns the pointer to the specified subslice that can be passed to
    /// `NonBlockingBlockIo:read_blocks()` and `NonBlockingBlockIo::write_blocks()` interfaces.
    fn set_pending(&mut self, io_offset: usize, io_size: usize) -> *mut [u8] {
        match &mut self.0 {
            IoBufferState::Ready(b, _) => {
                let ptr = &mut b[io_offset..][..io_size] as *mut [u8];
                self.0 = IoBufferState::Pending(*b as _, ptr, PhantomData);
                ptr
            }
            _ => unreachable!(),
        }
    }

    /// Gets the buffer if not pending
    fn get(&mut self) -> &mut [u8] {
        match &mut self.0 {
            IoBufferState::Ready(buffer, _) => buffer,
            _ => unreachable!(),
        }
    }

    /// Updates the IO status
    fn update(&mut self, io: &mut dyn NonBlockingBlockIo) {
        match &mut self.0 {
            IoBufferState::Ready(_, _) => {}
            IoBufferState::Pending(buffer, ptr, _) => {
                match io.check_status(*ptr) {
                    IoStatus::NotFound => unreachable!(), // Logic error.
                    IoStatus::Pending => {}
                    v => {
                        // SAFETY:
                        // * `buffer` is a valid pointer as it came from
                        //   `IoBufferState::Ready(buffer, _)`
                        // * status is no longer pending, buffer is not retained any more.
                        self.0 = IoBufferState::Ready(unsafe { &mut **buffer }, v);
                    }
                }
            }
        }
    }

    /// Consumes and returns the raw buffer.
    fn take(mut self) -> &'a mut [u8] {
        match &mut self.0 {
            IoBufferState::Ready(buffer, _) => {
                // IoBuffer has a drop implementation, thus we can't move buffer out directly.
                // The solution is to swap with an empty slice, which is valid for any lifetime.
                let mut res = &mut [][..];
                swap(&mut res, buffer);
                res
            }
            _ => unreachable!(), // Logic error.
        }
    }
}

/// `Transaction` tracks the non-blocking read/write IO request made by
/// `BlockDeviceEx::read_scoped()` and `BlockDeviceEx::write_scoped()`. It automatically performs
/// sync when going out of scope.
pub struct Transaction<'a, 'b> {
    dev: BlockDeviceEx<'a, 'a>,
    _phantom: PhantomData<&'b mut [u8]>,
}

impl Transaction<'_, '_> {
    /// Wait until the IO request is either completed/aborted and consume the transaction.
    pub fn sync(mut self) -> Result<()> {
        self.do_sync()
    }

    /// Helper method for performing the sync.
    fn do_sync(&mut self) -> Result<()> {
        self.dev.sync()?;
        match self.dev.is_aborted() {
            true => Err(StorageError::IoAborted),
            _ => Ok(()),
        }
    }
}

impl Drop for Transaction<'_, '_> {
    fn drop(&mut self) {
        // We expect caller to sync() themselves if they expect errors. If not the drop will
        // perform the sync but panics on error.
        self.do_sync().unwrap()
    }
}

/// `BlockDeviceEx` provides safe APIs for performing blocking/non-blocking read/write.
///
/// `'a`: Lifetime of the borrow to BlockIo / NonBlockingBlockIo,
/// `'b`: Lifetime of the external user buffers that will be passed to `Self::read()` and
///       `Self::write()`.
pub struct BlockDeviceEx<'a, 'b> {
    io: BlockDeviceIo<'a>,
    current_io: Option<IoBuffer<'b>>,
}

impl<'a, 'b> BlockDeviceEx<'a, 'b> {
    /// Creates a new instance.
    pub fn new(io: BlockDeviceIo<'a>) -> Self {
        Self { io, current_io: None }
    }

    /// Checks if any IO buffer is pending.
    pub fn is_pending(&self) -> bool {
        self.current_io.as_ref().map(|v| v.is_pending()).unwrap_or(false)
    }

    /// Updates the IO status.
    fn update_status(&mut self) {
        let BlockDeviceIo::NonBlocking(ref mut io) = self.io else {
            return;
        };

        match self.current_io.as_mut() {
            Some(buffer) => buffer.update(*io),
            _ => {}
        }
    }

    /// Polls and updates IO status.
    pub fn poll(&mut self) {
        if self.current_io.is_some() {
            self.update_status();
        }
    }

    /// Aborts the current IO.
    pub fn abort(&mut self) -> Result<()> {
        match &mut self.io {
            BlockDeviceIo::NonBlocking(io) => Ok(io.abort()?),
            _ => Ok(()),
        }
    }

    /// Checks if any IO is aborted.
    pub fn is_aborted(&self) -> bool {
        match self.current_io.as_ref() {
            Some(buffer) => buffer.is_aborted(),
            _ => false,
        }
    }

    /// Waits until the IO is completed or aborted.
    pub fn sync(&mut self) -> Result<()> {
        while self.is_pending() {
            self.poll();
        }
        Ok(())
    }

    /// Checks whether an IO is currently in progress.
    fn check_busy(&self) -> Result<()> {
        // No IO implies not pending.
        match self.current_io.is_some() {
            true => Err(StorageError::NotReady),
            _ => Ok(()),
        }
    }

    /// Writes data from `buffer[offset..][..size]` to the block device at offset `dst_offset`.
    ///
    /// # Args
    ///
    /// * `dst_offset`: Destination offset to write in the block device.
    /// * `buffer`: On input, it must be a `Some(buffer)` that contains the data to write. On
    ///   success, the buffer will be taken and it will be set to `None`. On error, `buffer` will
    ///   remain the same so that caller can continue to access the buffer. When the IO completes
    ///   or aborts, caller can retrieve the buffer via `Self::take_io_buffer()`.
    /// * `offset`: Offset of the data to write in `buffer`.
    /// * `size`: Size of the data to write.
    pub fn write(
        &mut self,
        dst_offset: u64,
        buffer: &mut Option<&'b mut [u8]>,
        offset: usize,
        size: usize,
    ) -> Result<()> {
        self.check_busy()?;
        let blk_size = self.io.as_block_io().block_size();
        // TODO(b/338439051): Implement support for arbitrarily aligned buffer and read range.
        assert_eq!(dst_offset % blk_size, 0);
        let buffer_raw = buffer.take().ok_or(StorageError::InvalidInput)?;
        let mut io_buffer = IoBuffer::new(buffer_raw);
        match write_io_buffer(&mut self.io, dst_offset / blk_size, &mut io_buffer, offset, size) {
            Err(e) => {
                // Error. Returns the buffer to caller.
                *buffer = Some(io_buffer.take());
                Err(e)
            }
            Ok(()) => {
                self.current_io = Some(io_buffer);
                Ok(())
            }
        }
    }

    /// Reads data from the block device at offset `dst_offset` into `buffer[offset..][..size]`.
    ///
    /// # Args
    ///
    /// * `dst_offset`: Destination offset to read from the block device.
    /// * `buffer`: On input, it must be a `Some(buffer)` that contains the output buffer. On
    ///   success, the buffer will be taken and it will be set to `None`. On error, `buffer` will
    ///   remain the same so that caller can continue to access the buffer. When the IO completes
    ///   or aborts, caller can retrieve the buffer via `Self::take_io_buffer()`.
    /// * `offset`: Offset of `buffer` to read to.
    /// * `size`: Size of the read.
    pub fn read(
        &mut self,
        dst_offset: u64,
        buffer: &mut Option<&'b mut [u8]>,
        offset: usize,
        size: usize,
    ) -> Result<()> {
        self.check_busy()?;
        let blk_size = self.io.as_block_io().block_size();
        // TODO(b/338439051): Implement support for arbitrarily aligned buffer and read range.
        assert_eq!(dst_offset % blk_size, 0);
        let buffer_raw = buffer.take().ok_or(StorageError::InvalidInput)?;
        let mut io_buffer = IoBuffer::new(buffer_raw);
        match read_io_buffer(&mut self.io, dst_offset / blk_size, &mut io_buffer, offset, size) {
            Err(e) => {
                // Error. Returns the buffer to caller.
                *buffer = Some(io_buffer.take());
                Err(e)
            }
            Ok(()) => {
                self.current_io = Some(io_buffer);
                Ok(())
            }
        }
    }

    /// Retrieves the IO buffer if it is completed/aborted.
    pub fn take_io_buffer(&mut self) -> Result<&'b mut [u8]> {
        match self.current_io {
            None => Err(StorageError::NotExist),
            Some(_) => match !self.is_pending() {
                true => Ok(self.current_io.take().unwrap().take()),
                _ => Err(StorageError::NotReady),
            },
        }
    }

    /// Returns an instance that borrows the internal field.
    ///
    /// This creates an instance where its lifetime parameter 'a/'b/'c is coerced to the life time
    /// of the current object. This will be used for creating a local instance for blocking
    /// operation.
    fn scoped_instance(&mut self) -> Result<BlockDeviceEx> {
        self.check_busy()?;
        Ok(BlockDeviceEx { io: self.io.scoped_instance(), current_io: None })
    }

    /// Performs a non-blocking write and returns a `Transanction` object which automatically
    /// performs sync when going out of scope.
    pub fn write_scoped<'c, 'd: 'c>(
        &'c mut self,
        offset: u64,
        data: &'d mut [u8],
    ) -> Result<Transaction<'c, 'd>> {
        let mut dev = self.scoped_instance()?;
        let len = data.len();
        dev.write(offset, &mut Some(data), 0, len)?;
        Ok(Transaction { dev, _phantom: PhantomData })
    }

    /// Performs a non-blocking read and returns a `Transanction` object which automatically
    /// performs sync when going out of scope.
    pub fn read_scoped<'c, 'd: 'c>(
        &'c mut self,
        offset: u64,
        out: &'d mut [u8],
    ) -> Result<Transaction<'c, 'd>> {
        let mut dev = self.scoped_instance()?;
        let len = out.len();
        dev.read(offset, &mut Some(out), 0, len)?;
        Ok(Transaction { dev, _phantom: PhantomData })
    }

    /// Performs blocking write.
    pub fn write_blocking(&mut self, offset: u64, data: &mut [u8]) -> Result<()> {
        self.write_scoped(offset, data)?.sync()
    }

    /// Performs blocking read.
    pub fn read_blocking(&mut self, offset: u64, out: &mut [u8]) -> Result<()> {
        self.read_scoped(offset, out)?.sync()
    }
}

impl Drop for BlockDeviceEx<'_, '_> {
    fn drop(&mut self) {
        self.abort().unwrap();
        self.sync().unwrap();
    }
}

/// A helper to write an IO buffer to the block device.
fn write_io_buffer(
    io: &mut BlockDeviceIo,
    blk_offset: u64,
    buffer: &mut IoBuffer,
    offset: usize,
    size: usize,
) -> Result<()> {
    let data = &mut buffer.get()[offset..][..size];
    assert!(is_buffer_aligned(data, io.as_block_io().alignment().into())?);
    assert!(is_aligned(size.into(), io.as_block_io().block_size().into())?);
    Ok(match io {
        BlockDeviceIo::Blocking(io) => io.write_blocks(blk_offset, data),
        BlockDeviceIo::NonBlocking(io) => {
            let ptr = buffer.set_pending(offset, size);
            // SAFETY:
            // * `buffer.set_pending()` makes sure that no safe code can use the buffer until it is
            //   set ready by `IoBuffer::update_status()` when status is no longer
            //   `IoStatus::Pending`.
            // * When going out of scope, `IoBuffer` checks whether the buffer is still pending and
            //   will panic if it is. Thus the buffer will remain valid with no other references
            //   during the non-blocking IO.
            unsafe { (*io).write_blocks(blk_offset, ptr) }
        }
    }?)
}

/// A helper to read data from a block device to an IO buffer.
fn read_io_buffer(
    io: &mut BlockDeviceIo,
    blk_offset: u64,
    buffer: &mut IoBuffer,
    offset: usize,
    size: usize,
) -> Result<()> {
    let out = &mut buffer.get()[offset..][..size];
    assert!(is_buffer_aligned(out, io.as_block_io().alignment().into())?);
    assert!(is_aligned(size.into(), io.as_block_io().block_size().into())?);
    Ok(match io {
        BlockDeviceIo::Blocking(io) => io.read_blocks(blk_offset, out),
        BlockDeviceIo::NonBlocking(io) => {
            let ptr = buffer.set_pending(offset, size);
            // SAFETY:
            // * `buffer.set_pending()` makes sure that no safe code can use the buffer until it is
            //   set ready by `IoBuffer::update_status()` when status is no longer
            //   `IoStatus::Pending`.
            // * When going out of scope, `IoBuffer` checks whether the buffer is still pending and
            //   will panic if it is. Thus the buffer will remain valid with no other references
            //   during the non-blocking IO.
            unsafe { (*io).read_blocks(blk_offset, ptr) }
        }
    }?)
}

#[cfg(test)]
mod test {
    use gbl_storage_testlib::{TestBlockDeviceBuilder, TimestampPauser};

    #[test]
    fn test_read() {
        let mut blk = TestBlockDeviceBuilder::new()
            .set_alignment(1)
            .set_block_size(1)
            .set_data(&[1, 2, 3, 4])
            .build();
        let mut io_buffer = [1, 0, 0, 1];
        let mut to_write = Some(&mut io_buffer[..]);
        {
            let timestamp_pauser = TimestampPauser::new();
            let mut blk_ex = blk.as_block_device_ex();
            blk_ex.write(1, &mut to_write, 1, 2).unwrap();
            assert!(to_write.is_none());
            // Timestamp paused. IO not being processed. poll() should return false.
            blk_ex.poll();
            assert!(blk_ex.is_pending());

            timestamp_pauser.resume();
            blk_ex.sync().unwrap();
            blk_ex.poll();
        }
        assert_eq!(blk.io.storage, [1, 0, 0, 4]);
    }

    #[test]
    fn test_write() {
        let mut blk = TestBlockDeviceBuilder::new()
            .set_alignment(1)
            .set_block_size(1)
            .set_data(&[1, 2, 3, 4])
            .build();
        let mut io_buffer = [1, 0, 0, 1];
        let mut to_read = Some(&mut io_buffer[..]);
        {
            let timestamp_pauser = TimestampPauser::new();
            let mut blk_ex = blk.as_block_device_ex();
            blk_ex.read(1, &mut to_read, 1, 2).unwrap();
            assert!(to_read.is_none());
            // Timestamp paused. IO not being processed.
            blk_ex.poll();
            assert!(blk_ex.is_pending());

            timestamp_pauser.resume();
            blk_ex.sync().unwrap();
            blk_ex.poll();
        }
        assert_eq!(io_buffer, [1, 2, 3, 1]);
    }

    #[test]
    fn test_read_write_blocking() {
        let mut blk = TestBlockDeviceBuilder::new()
            .set_alignment(1)
            .set_block_size(1)
            .set_data(&[1, 2, 3, 4])
            .build();

        let mut io_buffer = [0u8; 2];
        blk.as_block_device_ex().read_blocking(1, &mut io_buffer[..]).unwrap();
        assert_eq!(io_buffer, [2, 3]);

        let mut io_buffer = [0u8; 2];
        blk.as_block_device_ex().write_blocking(1, &mut io_buffer[..]).unwrap();
        assert_eq!(blk.io.storage, [1, 0, 0, 4]);
    }

    #[test]
    fn test_abort() {
        let mut blk = TestBlockDeviceBuilder::new()
            .set_alignment(1)
            .set_block_size(1)
            .set_data(&[1, 2, 3, 4])
            .build();
        let mut io_buffer = [1, 0, 0, 1];
        let mut to_write = Some(&mut io_buffer[..]);
        {
            let _ = TimestampPauser::new();
            let mut blk_ex = blk.as_block_device_ex();
            blk_ex.write(1, &mut to_write, 1, 2).unwrap();
            blk_ex.abort().unwrap();
            blk_ex.sync().unwrap();
            assert!(blk_ex.is_aborted())
        }
        assert_eq!(blk.io.storage, [1, 2, 3, 4]);

        let mut to_read = Some(&mut io_buffer[..]);
        {
            let _ = TimestampPauser::new();
            let mut blk_ex = blk.as_block_device_ex();
            blk_ex.read(1, &mut to_read, 1, 2).unwrap();
            blk_ex.abort().unwrap();
            blk_ex.sync().unwrap();
            assert!(blk_ex.is_aborted())
        }
        assert_eq!(io_buffer, [1, 0, 0, 1]);
    }

    #[test]
    fn read_write_error_on_busy() {
        let mut blk = TestBlockDeviceBuilder::new()
            .set_alignment(1)
            .set_block_size(1)
            .set_data(&[1, 2, 3, 4])
            .build();
        let mut io_buffer = [1, 0, 0, 1];
        let mut to_write = Some(&mut io_buffer[..]);

        let mut io_buffer_other = [0u8; 4];
        let mut io_other_ref = Some(&mut io_buffer_other[..]);
        {
            let _ = TimestampPauser::new();
            let mut blk_ex = blk.as_block_device_ex();
            blk_ex.write(1, &mut to_write, 1, 2).unwrap();
            assert!(blk_ex.write(1, &mut io_other_ref, 1, 2).is_err());
            assert!(io_other_ref.is_some());
            assert!(blk_ex.read(1, &mut io_other_ref, 1, 2).is_err());
            assert!(io_other_ref.is_some());
        }
    }
}
