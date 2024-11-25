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

//! Fastboot backend for libgbl.

use crate::{
    fuchsia_boot::GblAbrOps,
    gbl_print, gbl_println,
    partition::{check_part_unique, GblDisk, PartitionIo},
    GblOps,
};
pub use abr::{mark_slot_active, set_one_shot_bootloader, set_one_shot_recovery, SlotIndex};
use core::{
    array::from_fn,
    cmp::min,
    fmt::Write,
    future::Future,
    marker::PhantomData,
    mem::take,
    ops::DerefMut,
    pin::Pin,
    str::{from_utf8, Split},
};
use fastboot::{
    next_arg, next_arg_u64, process_next_command, run_tcp_session, snprintf, CommandError,
    CommandResult, FastbootImplementation, FormattedBytes, InfoSender, OkaySender, RebootMode,
    UploadBuilder, Uploader, VarInfoSender,
};
use gbl_async::{join, yield_now};
use gbl_storage::{BlockIo, Disk, Gpt};
use liberror::Error;
use safemath::SafeNum;
use zbi::{ZbiContainer, ZbiType};

mod vars;

pub(crate) mod sparse;
use sparse::is_sparse_image;

mod shared;
pub use shared::Shared;

mod buffer_pool;
pub use buffer_pool::BufferPool;
use buffer_pool::ScopedBuffer;

mod pin_fut_container;
pub use pin_fut_container::PinFutContainer;
use pin_fut_container::{PinFutContainerTyped, PinFutSlice};

// Re-exports dependency types
pub use fastboot::{TcpStream, Transport};

/// Reserved name for indicating flashing GPT.
const FLASH_GPT_PART: &str = "gpt";

/// Represents a GBL Fastboot async task.
enum Task<'a, 'b, B: BlockIo, P: BufferPool> {
    /// Image flashing task. (partition io, downloaded data, data size)
    Flash(PartitionIo<'a, B>, ScopedBuffer<'b, P>, usize),
    // Image erase task.
    Erase(PartitionIo<'a, B>, ScopedBuffer<'b, P>),
    None,
}

impl<'a, 'b, B: BlockIo, P: BufferPool> Task<'a, 'b, B, P> {
    // Runs the task.
    async fn run(self) {
        let _ = async {
            match self {
                Self::Flash(mut part_io, mut download, data_size) => {
                    match is_sparse_image(&download) {
                        Ok(_) => part_io.write_sparse(0, &mut download).await,
                        _ => part_io.write(0, &mut download[..data_size]).await,
                    }
                }
                Self::Erase(mut part_io, mut buffer) => part_io.zeroize(&mut buffer).await,
                _ => Ok(()),
            }
        }
        .await;
    }
}

/// `GblFastboot` implements fastboot commands in the GBL context.
///
/// # Lifetimes
///
/// * `'a`: [GblOps] and disks lifetime.
/// * `'b`: Lifetime for the buffer allocated by `P`.
/// * `'c`: Lifetime of the pinned [Future]s in task container `task`.
/// * `'d`: Lifetime of the `tasks` and `gbl_ops` objects borrowed.
///
/// # Generics
///
/// * `G`: Type of `Self::gbl_ops` which implements [GblOps].
/// * `B`: Type that implements [BlockIo] in the [Disk] parameter of [GblDisk] for `Self::disks`.
/// * `S`: Type of scratch buffer in the [Disk] parameter of [GblDisk] for `Self::disks`.
/// * `T`: Type of gpt buffer in the [Gpt] parameter of [GblDisk] for `Self::disks`.
/// * `P`: Type of `Self::buffer_pool` which implements [BufferPool].
/// * `C`: Type of `Self::tasks` which implements [PinFutContainerTyped].
/// * `F`: Type of [Future] stored by `Self::Tasks`.
struct GblFastboot<'a, 'b, 'c, 'd, G, B, S, T, P, C, F>
where
    G: GblOps<'a>,
    B: BlockIo,
    S: DerefMut<Target = [u8]>,
    T: DerefMut<Target = [u8]>,
    P: BufferPool,
{
    pub(crate) gbl_ops: &'d mut G,
    // We store the partition devices returned by `gbl_ops.disks()` directly instead of getting it
    // from `gbl_ops` later because we need to establish to the compiler that the hidden type of
    // [BlockIo] in `GblDisk<Disk<impl BlockIO...>...>` returned by `gbl_ops.disks()` will be the
    // same as the [BlockIo] type (denoted as B) in the function pointer
    // `task_mapper`: fn(Task<'a, 'b, B, P>) -> F`. Otherwise, compiler won't allow `fn flash()`
    // to call `task_mapper` with a `Task` constructed from `GblDisk<Disk<impl BlockIO...>...>`.
    disks: &'a [GblDisk<Disk<B, S>, Gpt<T>>],
    buffer_pool: &'b Shared<P>,
    task_mapper: fn(Task<'a, 'b, B, P>) -> F,
    tasks: &'d Shared<C>,
    current_download_buffer: Option<ScopedBuffer<'b, P>>,
    current_download_size: usize,
    enable_async_task: bool,
    default_block: Option<usize>,
    // Introduces marker type so that we can enforce constraint 'd <= min('b, 'c).
    // The constraint is expressed in the implementation block for the `FastbootImplementation`
    // trait.
    _tasks_context_lifetime: PhantomData<&'c P>,
}

// See definition of [GblFastboot] for docs on lifetimes and generics parameters.
impl<'a: 'c, 'b: 'c, 'c, 'd, G, B, S, T, P, C, F> GblFastboot<'a, 'b, 'c, 'd, G, B, S, T, P, C, F>
where
    G: GblOps<'a>,
    B: BlockIo,
    S: DerefMut<Target = [u8]>,
    T: DerefMut<Target = [u8]>,
    P: BufferPool,
    C: PinFutContainerTyped<'c, F>,
    F: Future<Output = ()> + 'c,
{
    /// Creates a new [GblFastboot].
    ///
    /// # Args
    ///
    /// * `gbl_ops`: An implementation of `GblOps`.
    /// * `disks`: The disk devices returned by `gbl_ops.disks()`. This is needed for expressing the
    ///   property that the hidden [BlockIo] type is the same as that in `task_mapper`.
    /// * `task_mapper`: A function pointer that maps `Task<'a, 'b, G, B>` to the target [Future]
    ///   type `F` for input to `PinFutContainerTyped<F>::add_with()`.
    /// * `tasks`: A shared instance of `PinFutContainerTyped<F>`.
    /// * `buffer_pool`: A shared instance of `BufferPool`.
    ///
    /// The combination of `task_mapper` and `tasks` allows type `F`, which will be running the
    /// async function `Task::run()`, to be defined at the callsite. This is necessary for the
    /// usage of preallocated pinned futures (by `run_gbl_fastboot_stack()`) because the returned
    /// type of a `async fn` is compiler-generated and can't be named. The only way to create a
    /// preallocated slice of anonymous future is to keep the type generic and pass in the
    /// anonymous future instance at the initialization callsite (aka defining use) and let compiler
    /// infer and propagate it.
    fn new(
        gbl_ops: &'d mut G,
        disks: &'a [GblDisk<Disk<B, S>, Gpt<T>>],
        task_mapper: fn(Task<'a, 'b, B, P>) -> F,
        tasks: &'d Shared<C>,
        buffer_pool: &'b Shared<P>,
    ) -> Self {
        Self {
            gbl_ops,
            disks,
            task_mapper,
            tasks,
            buffer_pool,
            current_download_buffer: None,
            current_download_size: 0,
            enable_async_task: false,
            default_block: None,
            _tasks_context_lifetime: PhantomData,
        }
    }

    /// Returns the shared task container.
    fn tasks(&self) -> &'d Shared<impl PinFutContainerTyped<'c, F>> {
        self.tasks
    }

    /// Listens on the given USB/TCP channels and runs fastboot.
    async fn run(
        &mut self,
        mut usb: Option<impl GblUsbTransport>,
        mut tcp: Option<impl GblTcpStream>,
    ) {
        if usb.is_none() && tcp.is_none() {
            gbl_println!(self.gbl_ops, "No USB or TCP found for GBL Fastboot");
            return;
        }
        let tasks = self.tasks();
        // The fastboot command loop task for interacting with the remote host.
        let cmd_loop_end = Shared::from(false);
        let cmd_loop_task = async {
            loop {
                if let Some(v) = usb.as_mut() {
                    if v.has_packet() {
                        let res = match process_next_command(v, self).await {
                            Ok(true) => break,
                            v => v,
                        };
                        if res.is_err() {
                            gbl_println!(self.gbl_ops, "GBL Fastboot USB session error: {:?}", res);
                        }
                    }
                }

                if let Some(v) = tcp.as_mut() {
                    if v.accept_new() {
                        let res = match run_tcp_session(v, self).await {
                            Ok(()) => break,
                            v => v,
                        };
                        if res.is_err_and(|e| e != Error::Disconnected) {
                            gbl_println!(self.gbl_ops, "GBL Fastboot TCP session error: {:?}", res);
                        }
                    }
                }

                yield_now().await;
            }
            *cmd_loop_end.borrow_mut() = true;
        };

        // Schedules [Task] spawned by GBL fastboot.
        let gbl_fb_tasks = async {
            while tasks.borrow_mut().poll_all() > 0 || !*cmd_loop_end.borrow_mut() {
                yield_now().await;
            }
        };

        let _ = join(cmd_loop_task, gbl_fb_tasks).await;
    }

    /// Extracts the next argument and verifies that it is a valid block device ID if present.
    ///
    /// # Returns
    ///
    /// * Returns `Ok(Some(blk_id))` if next argument is present and is a valid block device ID.
    /// * Returns `None` if next argument is not available and there are more than one block
    ///   devices.
    /// * Returns `Err(())` if next argument is present but is an invalid block device ID.
    fn check_next_arg_blk_id<'s>(
        &self,
        args: &mut impl Iterator<Item = &'s str>,
    ) -> CommandResult<Option<usize>> {
        let devs = self.disks;
        let blk_id = match next_arg_u64(args)? {
            Some(v) => {
                let v = usize::try_from(v)?;
                // Checks out of range.
                devs.get(v).ok_or("Invalid block ID")?;
                Some(v)
            }
            _ => None,
        };
        let blk_id = blk_id.or(self.default_block);
        let blk_id = blk_id.or((devs.len() == 1).then_some(0));
        Ok(blk_id)
    }

    /// Parses and checks the argument for "fastboot flash gpt/<blk_idx>/"resize".
    ///
    /// # Returns
    ///
    /// * Returns `Ok(Some((blk_idx, resize)))` if command is a GPT flashing command.
    /// * Returns `Ok(None)` if command is not a GPT flashing command.
    /// * Returns `Err()` otherwise.
    pub(crate) fn parse_flash_gpt_args(&self, part: &str) -> CommandResult<Option<(usize, bool)>> {
        // Syntax: flash gpt/<blk_idx>/"resize"
        let mut args = part.split('/');
        if next_arg(&mut args).filter(|v| *v == FLASH_GPT_PART).is_none() {
            return Ok(None);
        }
        // Parses block device ID.
        let blk_id = self
            .check_next_arg_blk_id(&mut args)?
            .ok_or("Block ID is required for flashing GPT")?;
        // Parses resize option.
        let resize = match next_arg(&mut args) {
            Some("resize") => true,
            Some(_) => return Err("Unknown argument".into()),
            _ => false,
        };
        Ok(Some((blk_id, resize)))
    }

    /// Parses and checks the partition argument and returns the partition name, block device
    /// index, start offset and size.
    pub(crate) fn parse_partition<'s>(
        &self,
        part: &'s str,
    ) -> CommandResult<(Option<&'s str>, usize, u64, u64)> {
        let devs = self.disks;
        let mut args = part.split('/');
        // Parses partition name.
        let part = next_arg(&mut args);
        // Parses block device ID.
        let blk_id = self.check_next_arg_blk_id(&mut args)?;
        // Parses sub window offset.
        let window_offset = next_arg_u64(&mut args)?.unwrap_or(0);
        // Parses sub window size.
        let window_size = next_arg_u64(&mut args)?;
        // Checks uniqueness of the partition and resolves its block device ID.
        let find = |p: Option<&'s str>| match blk_id {
            None => Ok((check_part_unique(devs, p.ok_or("Must provide a partition")?)?, p)),
            Some(v) => Ok(((v, devs[v].find_partition(p)?), p)),
        };
        let ((blk_id, partition), actual) = match find(part) {
            // Some legacy Fuchsia devices in the field uses name "fuchsia-fvm" for the standard
            // "fvm" partition. However all of our infra uses the standard name "fvm" when flashing.
            // Here we do a one off mapping if the device falls into this case. Once we have a
            // solution for migrating those devices off the legacy name, we can remove this.
            //
            // If we run into more of such legacy aliases that we can't migrate, consider adding
            // interfaces in GblOps for this.
            Err(Error::NotFound) if part == Some("fvm") => find(Some("fuchsia-fvm"))?,
            v => v?,
        };
        let part_sz = SafeNum::from(partition.size()?);
        let window_size = window_size.unwrap_or((part_sz - window_offset).try_into()?);
        u64::try_from(part_sz - window_size - window_offset)?;
        Ok((actual, blk_id, window_offset, window_size))
    }

    /// Takes the download data and resets download size.
    fn take_download(&mut self) -> Option<(ScopedBuffer<'b, P>, usize)> {
        Some((self.current_download_buffer.take()?, take(&mut self.current_download_size)))
    }

    /// Waits until a Disk device is ready and get the [PartitionIo] for `part`.
    pub async fn wait_partition_io(
        &self,
        blk: usize,
        part: Option<&str>,
    ) -> CommandResult<PartitionIo<'a, B>> {
        loop {
            match self.disks[blk].partition_io(part) {
                Err(Error::NotReady) => yield_now().await,
                Ok(v) => {
                    v.last_err()?;
                    return Ok(v);
                }
                Err(e) => return Err(e.into()),
            }
        }
    }

    /// An internal helper for parsing a partition and getting the partition IO
    async fn parse_and_get_partition_io(
        &self,
        part: &str,
    ) -> CommandResult<(usize, PartitionIo<'a, B>)> {
        let (part, blk_idx, start, sz) = self.parse_partition(part)?;
        Ok((blk_idx, self.wait_partition_io(blk_idx, part).await?.sub(start, sz)?))
    }

    /// Helper for scheduiling an async task.
    ///
    /// * If `Self::enable_async_task` is true, the method will add the task to the background task
    ///   list. Otherwise it simply runs the task.
    async fn schedule_task(
        &mut self,
        task: Task<'a, 'b, B, P>,
        responder: &mut impl InfoSender,
    ) -> CommandResult<()> {
        match self.enable_async_task {
            true => {
                let mut t = Some((self.task_mapper)(task));
                self.tasks.borrow_mut().add_with(|| t.take().unwrap());
                while t.is_some() {
                    yield_now().await;
                    self.tasks.borrow_mut().add_with(|| t.take().unwrap());
                }
                self.tasks.borrow_mut().poll_all();
                let info = "An IO task is launched. To sync manually, run \"oem gbl-sync-tasks\".";
                responder.send_info(info).await?
            }
            _ => task.run().await,
        };
        Ok(())
    }

    /// Waits for all block devices to be ready.
    async fn sync_all_blocks(&self) -> CommandResult<()> {
        for (idx, _) in self.disks.iter().enumerate() {
            let _ = self.wait_partition_io(idx, None).await;
        }
        Ok(())
    }

    /// Implementation for "fastboot oem gbl-sync-tasks".
    async fn oem_sync_blocks<'s>(
        &self,
        mut responder: impl InfoSender,
        res: &'s mut [u8],
    ) -> CommandResult<&'s [u8]> {
        self.sync_all_blocks().await?;
        // Checks error.
        let mut has_error = false;
        for (i, ele) in self.disks.iter().enumerate() {
            match ele.partition_io(None)?.last_err() {
                Ok(_) => {}
                Err(e) => {
                    has_error = true;
                    responder.send_info(snprintf!(res, "Block #{} error: {:?}.", i, e)).await?;
                }
            }
        }
        match has_error {
            true => Err("Errors during async block IO. Please reset device.".into()),
            _ => Ok(b""),
        }
    }

    /// Syncs all storage devices and reboots.
    async fn sync_block_and_reboot(
        &mut self,
        mode: RebootMode,
        mut resp: impl InfoSender + OkaySender,
    ) -> CommandResult<()> {
        resp.send_info("Syncing storage...").await?;
        self.sync_all_blocks().await?;
        match mode {
            RebootMode::Normal => {
                resp.send_info("Rebooting...").await?;
                resp.send_okay("").await?;
                self.gbl_ops.reboot();
            }
            RebootMode::Bootloader => {
                let f = self.gbl_ops.reboot_bootloader()?;
                resp.send_info("Rebooting to bootloader...").await?;
                resp.send_okay("").await?;
                f()
            }
            RebootMode::Recovery => {
                let f = self.gbl_ops.reboot_recovery()?;
                resp.send_info("Rebooting to recovery...").await?;
                resp.send_okay("").await?;
                f()
            }
            _ => return Err("Unsupported".into()),
        }
        Ok(())
    }

    /// Appends a staged payload as bootloader file.
    async fn add_staged_bootloader_file(&mut self, file_name: &str) -> CommandResult<()> {
        let buffer = self
            .gbl_ops
            .get_zbi_bootloader_files_buffer_aligned()
            .ok_or("No ZBI bootloader file buffer is provided")?;
        let data = self.current_download_buffer.as_mut().ok_or("No file staged")?;
        let data = &mut data[..self.current_download_size];
        let mut zbi = match ZbiContainer::parse(&mut buffer[..]) {
            Ok(v) => v,
            _ => ZbiContainer::new(&mut buffer[..])?,
        };
        let next_payload = zbi.get_next_payload()?;
        // Format: name length (1 byte) | name | file content.
        let (name_len, rest) = next_payload.split_at_mut_checked(1).ok_or("Buffer too small")?;
        let (name, rest) = rest.split_at_mut_checked(file_name.len()).ok_or("Buffer too small")?;
        let file_content = rest.get_mut(..data.len()).ok_or("Buffer too small")?;
        name_len[0] = file_name.len().try_into().map_err(|_| "File name length overflows 256")?;
        name.clone_from_slice(file_name.as_bytes());
        file_content.clone_from_slice(data);
        // Creates the entry;
        zbi.create_entry(
            ZbiType::BootloaderFile,
            0,
            Default::default(),
            1 + file_name.len() + data.len(),
        )?;
        Ok(())
    }
}

// See definition of [GblFastboot] for docs on lifetimes and generics parameters.
impl<'a: 'c, 'b: 'c, 'c, G, B, S, T, P, C, F> FastbootImplementation
    for GblFastboot<'a, 'b, 'c, '_, G, B, S, T, P, C, F>
where
    G: GblOps<'a>,
    B: BlockIo,
    S: DerefMut<Target = [u8]>,
    T: DerefMut<Target = [u8]>,
    P: BufferPool,
    C: PinFutContainerTyped<'c, F>,
    F: Future<Output = ()> + 'c,
{
    async fn get_var(
        &mut self,
        var: &str,
        args: Split<'_, char>,
        out: &mut [u8],
        _: impl InfoSender,
    ) -> CommandResult<usize> {
        Ok(self.get_var_internal(var, args, out)?.len())
    }

    async fn get_var_all(&mut self, mut resp: impl VarInfoSender) -> CommandResult<()> {
        self.get_var_all_internal(&mut resp).await
    }

    async fn get_download_buffer(&mut self) -> &mut [u8] {
        if self.current_download_buffer.is_none() {
            self.current_download_buffer = Some(self.buffer_pool.allocate_async().await);
        }
        self.current_download_buffer.as_mut().unwrap()
    }

    async fn download_complete(
        &mut self,
        download_size: usize,
        _: impl InfoSender,
    ) -> CommandResult<()> {
        self.current_download_size = download_size;
        Ok(())
    }

    async fn flash(&mut self, part: &str, mut responder: impl InfoSender) -> CommandResult<()> {
        let disks = self.disks;

        // Checks if we are flashing new GPT partition table
        if let Some((blk_idx, resize)) = self.parse_flash_gpt_args(part)? {
            self.wait_partition_io(blk_idx, None).await?;
            let (mut gpt, size) = self.take_download().ok_or("No GPT downloaded")?;
            responder.send_info("Updating GPT...").await?;
            return match disks[blk_idx].update_gpt(&mut gpt[..size], resize).await {
                Err(Error::NotReady) => panic!("Should not be busy"),
                Err(Error::Unsupported) => Err("Block device is not for GPT".into()),
                v => Ok(v?),
            };
        }

        let (blk_idx, part_io) = self.parse_and_get_partition_io(part).await?;
        let (download_buffer, data_size) = self.take_download().ok_or("No download")?;
        let write_task = Task::Flash(part_io, download_buffer, data_size);
        self.schedule_task(write_task, &mut responder).await?;
        // Checks if block is ready already and returns errors. This can be the case when the
        // operation is synchronous or runs into early errors.
        Ok(disks[blk_idx].status().result()?)
    }

    async fn erase(&mut self, part: &str, mut responder: impl InfoSender) -> CommandResult<()> {
        let disks = self.disks;

        // Checks if we are erasing GPT partition table.
        if let Some((blk_idx, _)) = self.parse_flash_gpt_args(part)? {
            self.wait_partition_io(blk_idx, None).await?;
            return match disks[blk_idx].erase_gpt().await {
                Err(Error::NotReady) => panic!("Should not be busy"),
                Err(Error::Unsupported) => Err("Block device is not for GPT".into()),
                v => Ok(v?),
            };
        }

        let (blk_idx, part_io) = self.parse_and_get_partition_io(part).await?;
        self.get_download_buffer().await;
        let erase_task = Task::Erase(part_io, self.take_download().unwrap().0);
        self.schedule_task(erase_task, &mut responder).await?;
        // Checks if block is ready already and returns errors. This can be the case when the
        // operation is synchronous or runs into early errors.
        Ok(disks[blk_idx].status().result()?)
    }

    async fn upload(&mut self, _: impl UploadBuilder) -> CommandResult<()> {
        Err("Unimplemented".into())
    }

    async fn fetch(
        &mut self,
        part: &str,
        offset: u64,
        size: u64,
        mut responder: impl UploadBuilder + InfoSender,
    ) -> CommandResult<()> {
        let (_, mut part_io) = self.parse_and_get_partition_io(part).await?;
        let buffer = self.get_download_buffer().await;
        let end = u64::try_from(SafeNum::from(offset) + size)?;
        let mut curr = offset;
        responder
            .send_formatted_info(|v| write!(v, "Uploading {} bytes...", size).unwrap())
            .await?;
        let mut uploader = responder.initiate_upload(size).await?;
        while curr < end {
            let to_send = min(usize::try_from(end - curr)?, buffer.len());
            part_io.read(curr, &mut buffer[..to_send]).await?;
            uploader.upload(&mut buffer[..to_send]).await?;
            curr += u64::try_from(to_send)?;
        }
        Ok(())
    }

    async fn reboot(
        &mut self,
        mode: RebootMode,
        resp: impl InfoSender + OkaySender,
    ) -> CommandError {
        match self.sync_block_and_reboot(mode, resp).await {
            Err(e) => e,
            _ => "Unknown".into(),
        }
    }

    async fn r#continue(&mut self, mut resp: impl InfoSender) -> CommandResult<()> {
        resp.send_info("Syncing storage...").await?;
        Ok(self.sync_all_blocks().await?)
    }

    async fn set_active(&mut self, slot: &str, _: impl InfoSender) -> CommandResult<()> {
        self.sync_all_blocks().await?;
        match self.gbl_ops.expected_os_is_fuchsia()? {
            // TODO(b/374776896): Prioritizes platform specific `set_active_slot`  if available.
            true => Ok(mark_slot_active(
                &mut GblAbrOps(self.gbl_ops),
                match slot {
                    "a" => SlotIndex::A,
                    "b" => SlotIndex::B,
                    _ => return Err("Invalid slot index for Fuchsia A/B/R".into()),
                },
            )?),
            _ => Err("Not supported".into()),
        }
    }

    async fn oem<'s>(
        &mut self,
        cmd: &str,
        mut responder: impl InfoSender,
        res: &'s mut [u8],
    ) -> CommandResult<&'s [u8]> {
        let mut args = cmd.split(' ');
        let cmd = args.next().ok_or("Missing command")?;
        match cmd {
            "gbl-sync-tasks" => self.oem_sync_blocks(responder, res).await,
            "gbl-enable-async-task" => {
                self.enable_async_task = true;
                Ok(b"")
            }
            "gbl-disable-async-task" => {
                self.enable_async_task = false;
                Ok(b"")
            }
            "gbl-unset-default-block" => {
                self.default_block = None;
                Ok(b"")
            }
            "gbl-set-default-block" => {
                let id = next_arg_u64(&mut args)?.ok_or("Missing block device ID")?;
                let id = usize::try_from(id)?;
                self.disks.get(id).ok_or("Out of range")?;
                self.default_block = Some(id.try_into()?);
                responder
                    .send_formatted_info(|f| write!(f, "Default block device: {id:#x}").unwrap())
                    .await?;
                Ok(b"")
            }
            "add-staged-bootloader-file" => {
                let file_name = next_arg(&mut args).ok_or("Missing file name")?;
                self.add_staged_bootloader_file(file_name).await?;
                Ok(b"")
            }
            _ => Err("Unknown oem command".into()),
        }
    }
}

/// `GblUsbTransport` defines transport interfaces for running GBL fastboot over USB.
pub trait GblUsbTransport: Transport {
    /// Checks whether there is a new USB packet.
    fn has_packet(&mut self) -> bool;
}

/// `GblTcpStream` defines transport interfaces for running GBL fastboot over TCP.
pub trait GblTcpStream: TcpStream {
    /// Accepts a new TCP connection.
    ///
    /// If a connection is in progress, it should be aborted first.
    ///
    /// Returns true if a new connection is established, false otherwise.
    fn accept_new(&mut self) -> bool;
}

/// Runs GBL fastboot on the given USB/TCP channels.
///
/// # Args:
///
/// * `gbl_ops`: An instance of [GblOps].
/// * `buffer_pool`: An implementation of [BufferPool].
/// * `tasks`: An implementation of [PinFutContainer]
/// * `usb`: An optional implementation of [GblUsbTransport].
/// * `tcp`: An optional implementation of [GblTcpStream].
///
/// # Lifetimes
/// * `'a`: Lifetime of [GblOps].
/// * `'b`: Lifetime of `download_buffers`.
/// * `'c`: Lifetime of `tasks`.
pub async fn run_gbl_fastboot<'a: 'c, 'b: 'c, 'c>(
    gbl_ops: &mut impl GblOps<'a>,
    buffer_pool: &'b Shared<impl BufferPool>,
    tasks: impl PinFutContainer<'c> + 'c,
    usb: Option<impl GblUsbTransport>,
    tcp: Option<impl GblTcpStream>,
) {
    let tasks = tasks.into();
    let disks = gbl_ops.disks();
    GblFastboot::new(gbl_ops, disks, Task::run, &tasks, buffer_pool).run(usb, tcp).await;
}

/// Runs GBL fastboot on the given USB/TCP channels with N stack allocated worker tasks.
///
/// The choice of N depends on the level of parallelism the platform can support. For platform with
/// `n` storage devices that can independently perform non-blocking IO, it will required `N = n`
/// and a `buffer_pool` that can allocate at least n+1 buffers at the same time in order to achieve
/// parallel flashing to all storages plus a parallel downloading. However, it is common for
/// disks that need to be flashed to be on the same block deviece so flashing of them becomes
/// sequential, in which case N can be smaller. Caller should take into consideration usage pattern
/// for determining N.
///
/// # Args:
///
/// * `gbl_ops`: An instance of [GblOps].
/// * `buffer_pool`: An implementation of [BufferPool].
/// * `usb`: An optional implementation of [GblUsbTransport].
/// * `tcp`: An optional implementation of [GblTcpStream].
pub async fn run_gbl_fastboot_stack<'a, const N: usize>(
    gbl_ops: &mut impl GblOps<'a>,
    buffer_pool: impl BufferPool,
    usb: Option<impl GblUsbTransport>,
    tcp: Option<impl GblTcpStream>,
) {
    let buffer_pool = buffer_pool.into();
    // Creates N worker tasks.
    let mut tasks: [_; N] = from_fn(|_| Task::None.run());
    // It is possible to avoid the use of the unsafe `Pin::new_unchecked` by delaring the array and
    // manually pinning each element i.e.
    //
    // ```
    // let mut tasks = [
    //     core::pin::pin!(Task::None.run()),
    //     core::pin::pin!(Task::None.run()),
    //     core::pin::pin!(Task::None.run()),
    // ];
    // ```
    //
    // Parameterization of `N` will be an issue, but might be solvable with procedural macro.
    // SAFETY: `tasks` is immediately shadowed and thus guaranteed not moved for the rest of its
    // lifetime.
    let mut tasks: [_; N] = tasks.each_mut().map(|v| unsafe { Pin::new_unchecked(v) });
    let tasks = PinFutSlice::new(&mut tasks[..]).into();
    let disks = gbl_ops.disks();
    GblFastboot::new(gbl_ops, disks, Task::run, &tasks, &buffer_pool).run(usb, tcp).await;
}

/// Pre-generates a Fuchsia Fastboot MDNS service broadcast packet.
///
/// Fuchsia ffx development flow can detect fastboot devices that broadcast a "_fastboot·_tcp·local"
/// MDNS service. This API generates the broadcast MDNS packet for Ipv6. Caller is reponsible for
/// sending this packet via UDP at the following address and port (defined by MDNS):
///
/// * ipv6: ff02::fb
/// * port: 5353
///
/// # Args
///
/// * `node_name`: The Fuchsia node name for the service. Must be a 22 character ASCII string in the
///   format "fuchsia-xxxx-xxxx-xxxx".
/// * `ipv6_addr`: The Ipv6 address bytes.
///
/// The packet generated by the API contains the given IPv6 address and a fuchsia node name derived
/// from the given ethernet mac address `eth_mac`.
pub fn fuchsia_fastboot_mdns_packet(node_name: &str, ipv6_addr: &[u8]) -> Result<[u8; 140], Error> {
    // Pre-generated Fuchsia fastboot MDNS service packet template.
    // It contains the node name and ipv6 address. We simply replace with the device's node name and
    // ipv6 address.
    let mut packet: [u8; 140] = [
        0x00, 0x00, 0x84, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x02, 0x09, 0x5f, 0x66,
        0x61, 0x73, 0x74, 0x62, 0x6f, 0x6f, 0x74, 0x04, 0x5f, 0x74, 0x63, 0x70, 0x05, 0x6c, 0x6f,
        0x63, 0x61, 0x6c, 0x00, 0x00, 0x0c, 0x80, 0x01, 0x00, 0x00, 0x00, 0x78, 0x00, 0x19, 0x16,
        0x66, 0x75, 0x63, 0x68, 0x73, 0x69, 0x61, 0x2d, 0x34, 0x38, 0x32, 0x31, 0x2d, 0x30, 0x62,
        0x33, 0x31, 0x2d, 0x65, 0x61, 0x66, 0x38, 0xc0, 0x0c, 0xc0, 0x2c, 0x00, 0x21, 0x80, 0x01,
        0x00, 0x00, 0x00, 0x78, 0x00, 0x1f, 0x00, 0x00, 0x00, 0x00, 0x15, 0xb2, 0x16, 0x66, 0x75,
        0x63, 0x68, 0x73, 0x69, 0x61, 0x2d, 0x34, 0x38, 0x32, 0x31, 0x2d, 0x30, 0x62, 0x33, 0x31,
        0x2d, 0x65, 0x61, 0x66, 0x38, 0xc0, 0x1b, 0xc0, 0x57, 0x00, 0x1c, 0x80, 0x01, 0x00, 0x00,
        0x00, 0x78, 0x00, 0x10, 0xfe, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x4a, 0x21, 0x0b,
        0xff, 0xfe, 0x31, 0xea, 0xf8,
    ];
    // Offsets to the fuchsia node name field.
    const NODE_NAME_OFFSETS: &[usize; 2] = &[45, 88];
    // Offset to the IPv6 address field.
    const IP6_ADDR_OFFSET: usize = 124;

    if node_name.as_bytes().len() != 22 {
        return Err(Error::InvalidInput);
    }

    for off in NODE_NAME_OFFSETS {
        packet[*off..][..node_name.len()].clone_from_slice(node_name.as_bytes());
    }
    packet[IP6_ADDR_OFFSET..][..ipv6_addr.len()].clone_from_slice(ipv6_addr);
    Ok(packet)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        ops::test::{FakeGblOps, FakeGblOpsStorage},
        Os,
    };
    use abr::{
        get_and_clear_one_shot_bootloader, get_boot_slot, mark_slot_unbootable, ABR_DATA_SIZE,
    };
    use core::{
        mem::size_of,
        pin::{pin, Pin},
        str::from_utf8,
    };
    use fastboot::{test_utils::TestUploadBuilder, MAX_RESPONSE_SIZE};
    use gbl_async::{block_on, poll, poll_n_times};
    use gbl_storage_testlib::{BackingStore, TestBlockDeviceBuilder};
    use liberror::Error;
    use spin::{Mutex, MutexGuard};
    use std::{collections::VecDeque, io::Read};
    use zerocopy::AsBytes;

    /// A test implementation of [InfoSender] and [OkaySender].
    #[derive(Default)]
    struct TestResponder {
        okay_sent: Mutex<bool>,
        info_messages: Mutex<Vec<String>>,
    }

    impl InfoSender for &TestResponder {
        async fn send_formatted_info<F: FnOnce(&mut dyn Write)>(
            &mut self,
            cb: F,
        ) -> Result<(), Error> {
            let mut msg: String = "".into();
            cb(&mut msg);
            self.info_messages.try_lock().unwrap().push(msg);
            Ok(())
        }
    }

    impl OkaySender for &TestResponder {
        /// Sends a Fastboot "INFO<`msg`>" packet.
        async fn send_formatted_okay<F: FnOnce(&mut dyn Write)>(self, _: F) -> Result<(), Error> {
            *self.okay_sent.try_lock().unwrap() = true;
            Ok(())
        }
    }

    /// Helper to test fastboot variable value.
    fn check_var(gbl_fb: &mut impl FastbootImplementation, var: &str, args: &str, expected: &str) {
        let resp: TestResponder = Default::default();
        let mut out = vec![0u8; MAX_RESPONSE_SIZE];
        let val =
            block_on(gbl_fb.get_var_as_str(var, args.split(':'), &resp, &mut out[..])).unwrap();
        assert_eq!(val, expected, "var {}:{} = {} != {}", var, args, val, expected,);
    }

    /// A helper to set the download content.
    fn set_download(gbl_fb: &mut impl FastbootImplementation, data: &[u8]) {
        block_on(gbl_fb.get_download_buffer())[..data.len()].clone_from_slice(data);
        block_on(gbl_fb.download_complete(data.len(), &TestResponder::default())).unwrap();
    }

    impl<'a> PinFutContainer<'a> for Vec<Pin<Box<dyn Future<Output = ()> + 'a>>> {
        fn add_with<F: Future<Output = ()> + 'a>(&mut self, f: impl FnOnce() -> F) {
            self.push(Box::pin(f()));
        }

        fn for_each_remove_if(
            &mut self,
            mut cb: impl FnMut(&mut Pin<&mut (dyn Future<Output = ()> + 'a)>) -> bool,
        ) {
            for idx in (0..self.len()).rev() {
                cb(&mut self[idx].as_mut()).then(|| self.swap_remove(idx));
            }
        }
    }

    #[test]
    fn test_get_var_gbl() {
        let dl_buffers = Shared::from(vec![vec![0u8; 128 * 1024]; 1]);
        let storage = FakeGblOpsStorage::default();
        let mut gbl_ops = FakeGblOps::new(&storage);
        let tasks = vec![].into();
        let parts = gbl_ops.disks();
        let mut gbl_fb = GblFastboot::new(&mut gbl_ops, parts, Task::run, &tasks, &dl_buffers);
        check_var(
            &mut gbl_fb,
            FakeGblOps::GBL_TEST_VAR,
            "arg",
            format!("{}:Some(\"arg\")", FakeGblOps::GBL_TEST_VAR_VAL).as_str(),
        );
    }

    #[test]
    fn test_get_var_partition_info() {
        let dl_buffers = Shared::from(vec![vec![0u8; 128 * 1024]; 1]);
        let mut storage = FakeGblOpsStorage::default();
        storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin"));
        storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_2.bin"));
        storage.add_raw_device(c"raw_0", [0xaau8; 4 * 1024]);
        storage.add_raw_device(c"raw_1", [0x55u8; 8 * 1024]);
        let mut gbl_ops = FakeGblOps::new(&storage);
        let tasks = vec![].into();
        let parts = gbl_ops.disks();
        let mut gbl_fb = GblFastboot::new(&mut gbl_ops, parts, Task::run, &tasks, &dl_buffers);

        // Check different semantics
        check_var(&mut gbl_fb, "partition-size", "boot_a", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a/", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a//", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a///", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a/0", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a/0/", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a//0", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a/0/0", "0x2000");
        check_var(&mut gbl_fb, "partition-size", "boot_a//0x1000", "0x1000");

        check_var(&mut gbl_fb, "partition-size", "boot_b/0", "0x3000");
        check_var(&mut gbl_fb, "partition-size", "vendor_boot_a/1", "0x1000");
        check_var(&mut gbl_fb, "partition-size", "vendor_boot_b/1", "0x1800");
        check_var(&mut gbl_fb, "partition-size", "boot_a//0x1000", "0x1000");
        check_var(&mut gbl_fb, "partition-size", "raw_0", "0x1000");
        check_var(&mut gbl_fb, "partition-size", "raw_1", "0x2000");

        let resp: TestResponder = Default::default();
        let mut out = vec![0u8; MAX_RESPONSE_SIZE];
        assert!(block_on(gbl_fb.get_var_as_str(
            "partition",
            "non-existent".split(':'),
            &resp,
            &mut out[..],
        ))
        .is_err());
    }

    /// `TestVarSender` implements `TestVarSender`. It stores outputs in a vector of string.
    struct TestVarSender(Vec<String>);

    impl VarInfoSender for &mut TestVarSender {
        async fn send_var_info(
            &mut self,
            name: &str,
            args: impl IntoIterator<Item = &'_ str>,
            val: &str,
        ) -> Result<(), Error> {
            let args = args.into_iter().collect::<Vec<_>>();
            self.0.push(format!("{}:{}: {}", name, args.join(":"), val));
            Ok(())
        }
    }

    #[test]
    fn test_get_var_all() {
        let dl_buffers = Shared::from(vec![vec![0u8; 128 * 1024]; 1]);
        let mut storage = FakeGblOpsStorage::default();
        storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin"));
        storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_2.bin"));
        storage.add_raw_device(c"raw_0", [0xaau8; 4 * 1024]);
        storage.add_raw_device(c"raw_1", [0x55u8; 8 * 1024]);
        let mut gbl_ops = FakeGblOps::new(&storage);
        let tasks = vec![].into();
        let parts = gbl_ops.disks();
        let mut gbl_fb = GblFastboot::new(&mut gbl_ops, parts, Task::run, &tasks, &dl_buffers);

        let mut logger = TestVarSender(vec![]);
        block_on(gbl_fb.get_var_all(&mut logger)).unwrap();
        assert_eq!(
            logger.0,
            [
                "version-bootloader:: 1.0",
                "max-fetch-size:: 0xffffffffffffffff",
                "block-device:0:total-blocks: 0x80",
                "block-device:0:block-size: 0x200",
                "block-device:0:status: idle",
                "block-device:1:total-blocks: 0x100",
                "block-device:1:block-size: 0x200",
                "block-device:1:status: idle",
                "block-device:2:total-blocks: 0x1000",
                "block-device:2:block-size: 0x1",
                "block-device:2:status: idle",
                "block-device:3:total-blocks: 0x2000",
                "block-device:3:block-size: 0x1",
                "block-device:3:status: idle",
                "gbl-default-block:: None",
                "partition-size:boot_a/0: 0x2000",
                "partition-type:boot_a/0: raw",
                "partition-size:boot_b/0: 0x3000",
                "partition-type:boot_b/0: raw",
                "partition-size:vendor_boot_a/1: 0x1000",
                "partition-type:vendor_boot_a/1: raw",
                "partition-size:vendor_boot_b/1: 0x1800",
                "partition-type:vendor_boot_b/1: raw",
                "partition-size:raw_0/2: 0x1000",
                "partition-type:raw_0/2: raw",
                "partition-size:raw_1/3: 0x2000",
                "partition-type:raw_1/3: raw",
                format!("{}:1: {}:1", FakeGblOps::GBL_TEST_VAR, FakeGblOps::GBL_TEST_VAR_VAL)
                    .as_str(),
                format!("{}:2: {}:2", FakeGblOps::GBL_TEST_VAR, FakeGblOps::GBL_TEST_VAR_VAL)
                    .as_str(),
            ]
        );
    }

    /// A helper for fetching partition from a `GblFastboot`
    fn fetch<EOff: core::fmt::Debug, ESz: core::fmt::Debug>(
        fb: &mut impl FastbootImplementation,
        part: String,
        off: impl TryInto<u64, Error = EOff>,
        size: impl TryInto<u64, Error = ESz>,
    ) -> CommandResult<Vec<u8>> {
        let off = off.try_into().unwrap();
        let size = size.try_into().unwrap();
        let mut upload_out = vec![0u8; usize::try_from(size).unwrap()];
        let test_uploader = TestUploadBuilder(&mut upload_out[..]);
        block_on(fb.fetch(part.as_str(), off, size, test_uploader))?;
        Ok(upload_out)
    }

    #[test]
    fn test_fetch_invalid_partition_arg() {
        let dl_buffers = Shared::from(vec![vec![0u8; 128 * 1024]; 1]);
        let mut storage = FakeGblOpsStorage::default();
        storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin"));
        storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_2.bin"));
        storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_2.bin"));
        let mut gbl_ops = FakeGblOps::new(&storage);
        let tasks = vec![].into();
        let parts = gbl_ops.disks();
        let mut gbl_fb = GblFastboot::new(&mut gbl_ops, parts, Task::run, &tasks, &dl_buffers);

        // Missing mandatory block device ID for raw block partition.
        assert!(fetch(&mut gbl_fb, "//0/0".into(), 0, 0).is_err());

        // GPT partition does not exist.
        assert!(fetch(&mut gbl_fb, "non///".into(), 0, 0).is_err());

        // GPT Partition is not unique.
        assert!(fetch(&mut gbl_fb, "vendor_boot_a///".into(), 0, 0).is_err());

        // Offset overflows.
        assert!(fetch(&mut gbl_fb, "boot_a//0x2001/".into(), 0, 1).is_err());
        assert!(fetch(&mut gbl_fb, "boot_a".into(), 0x2000, 1).is_err());

        // Size overflows.
        assert!(fetch(&mut gbl_fb, "boot_a///0x2001".into(), 0, 0).is_err());
        assert!(fetch(&mut gbl_fb, "boot_a".into(), 0, 0x2001).is_err());
    }

    /// A helper for testing raw block upload. It verifies that data read from block device
    /// `blk_id` in range [`off`, `off`+`size`) is the same as `disk[off..][..size]`
    fn check_blk_upload(
        fb: &mut impl FastbootImplementation,
        blk_id: u64,
        off: u64,
        size: u64,
        disk: &[u8],
    ) {
        let expected = disk[off.try_into().unwrap()..][..size.try_into().unwrap()].to_vec();
        // offset/size as part of the partition string.
        let part = format!("/{:#x}/{:#x}/{:#x}", blk_id, off, size);
        assert_eq!(fetch(fb, part, 0, size).unwrap(), expected);
        // offset/size as separate fetch arguments.
        let part = format!("/{:#x}", blk_id);
        assert_eq!(fetch(fb, part, off, size).unwrap(), expected);
    }

    #[test]
    fn test_fetch_raw_block() {
        let dl_buffers = Shared::from(vec![vec![0u8; 128 * 1024]; 1]);
        let mut storage = FakeGblOpsStorage::default();
        let disk_0 = include_bytes!("../../../libstorage/test/gpt_test_1.bin");
        let disk_1 = include_bytes!("../../../libstorage/test/gpt_test_2.bin");
        storage.add_gpt_device(disk_0);
        storage.add_gpt_device(disk_1);
        let mut gbl_ops = FakeGblOps::new(&storage);
        let tasks = vec![].into();
        let parts = gbl_ops.disks();
        let mut gbl_fb = GblFastboot::new(&mut gbl_ops, parts, Task::run, &tasks, &dl_buffers);

        let off = 512;
        let size = 512;
        check_blk_upload(&mut gbl_fb, 0, off, size, disk_0);
        check_blk_upload(&mut gbl_fb, 1, off, size, disk_1);
    }

    /// A helper for testing uploading GPT partition. It verifies that data read from GPT partition
    /// `part` at disk `blk_id` in range [`off`, `off`+`size`) is the same as
    /// `partition_data[off..][..size]`.
    fn check_part_upload(
        fb: &mut impl FastbootImplementation,
        part: &str,
        off: u64,
        size: u64,
        blk_id: Option<u64>,
        partition_data: &[u8],
    ) {
        let expected =
            partition_data[off.try_into().unwrap()..][..size.try_into().unwrap()].to_vec();
        let blk_id = blk_id.map_or("".to_string(), |v| format!("{:#x}", v));
        // offset/size as part of the partition string.
        let gpt_part = format!("{}/{}/{:#x}/{:#x}", part, blk_id, off, size);
        assert_eq!(fetch(fb, gpt_part, 0, size).unwrap(), expected);
        // offset/size as separate fetch arguments.
        let gpt_part = format!("{}/{}", part, blk_id);
        assert_eq!(fetch(fb, gpt_part, off, size).unwrap(), expected);
    }

    #[test]
    fn test_fetch_partition() {
        let dl_buffers = Shared::from(vec![vec![0u8; 128 * 1024]; 1]);
        let mut storage = FakeGblOpsStorage::default();
        storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin"));
        storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_2.bin"));
        storage.add_raw_device(c"raw_0", [0xaau8; 4 * 1024]);
        storage.add_raw_device(c"raw_1", [0x55u8; 8 * 1024]);
        let mut gbl_ops = FakeGblOps::new(&storage);
        let tasks = vec![].into();
        let parts = gbl_ops.disks();
        let mut gbl_fb = GblFastboot::new(&mut gbl_ops, parts, Task::run, &tasks, &dl_buffers);

        let expect_boot_a = include_bytes!("../../../libstorage/test/boot_a.bin");
        let expect_boot_b = include_bytes!("../../../libstorage/test/boot_b.bin");
        let expect_vendor_boot_a = include_bytes!("../../../libstorage/test/vendor_boot_a.bin");
        let expect_vendor_boot_b = include_bytes!("../../../libstorage/test/vendor_boot_b.bin");

        let size = 512;
        let off = 512;

        check_part_upload(&mut gbl_fb, "boot_a", off, size, Some(0), expect_boot_a);
        check_part_upload(&mut gbl_fb, "boot_b", off, size, Some(0), expect_boot_b);
        check_part_upload(&mut gbl_fb, "vendor_boot_a", off, size, Some(1), expect_vendor_boot_a);
        check_part_upload(&mut gbl_fb, "vendor_boot_b", off, size, Some(1), expect_vendor_boot_b);
        check_part_upload(&mut gbl_fb, "raw_0", off, size, Some(2), &[0xaau8; 4 * 1024]);
        check_part_upload(&mut gbl_fb, "raw_1", off, size, Some(3), &[0x55u8; 8 * 1024]);

        // No block device id
        check_part_upload(&mut gbl_fb, "boot_a", off, size, None, expect_boot_a);
        check_part_upload(&mut gbl_fb, "boot_b", off, size, None, expect_boot_b);
        check_part_upload(&mut gbl_fb, "vendor_boot_a", off, size, None, expect_vendor_boot_a);
        check_part_upload(&mut gbl_fb, "vendor_boot_b", off, size, None, expect_vendor_boot_b);
        check_part_upload(&mut gbl_fb, "raw_0", off, size, None, &[0xaau8; 4 * 1024]);
        check_part_upload(&mut gbl_fb, "raw_1", off, size, None, &[0x55u8; 8 * 1024]);
    }

    /// A helper function to get a bit-flipped copy of the input data.
    fn flipped_bits(data: &[u8]) -> Vec<u8> {
        data.iter().map(|v| !(*v)).collect::<Vec<_>>()
    }

    /// A helper function to flash data to a partition
    fn flash_part(fb: &mut impl FastbootImplementation, part: &str, data: &[u8]) {
        // Prepare a download buffer.
        let dl_size = data.len();
        let download = data.to_vec();
        let resp: TestResponder = Default::default();
        set_download(fb, &download[..]);
        block_on(fb.flash(part, &resp)).unwrap();
        assert_eq!(fetch(fb, part.into(), 0, dl_size).unwrap(), download);
    }

    /// A helper for testing partition flashing.
    fn check_flash_part(fb: &mut impl FastbootImplementation, part: &str, expected: &[u8]) {
        flash_part(fb, part, expected);
        // Also flashes bit-wise reversed version in case the initial content is the same.
        flash_part(fb, part, &flipped_bits(expected));
    }

    #[test]
    fn test_flash_partition() {
        let disk_0 = include_bytes!("../../../libstorage/test/gpt_test_1.bin");
        let disk_1 = include_bytes!("../../../libstorage/test/gpt_test_2.bin");
        let dl_buffers = Shared::from(vec![vec![0u8; 128 * 1024]; 1]);
        let mut storage = FakeGblOpsStorage::default();
        storage.add_gpt_device(disk_0);
        storage.add_gpt_device(disk_1);
        storage.add_raw_device(c"raw_0", [0xaau8; 4 * 1024]);
        storage.add_raw_device(c"raw_1", [0x55u8; 8 * 1024]);
        let mut gbl_ops = FakeGblOps::new(&storage);
        let tasks = vec![].into();
        let parts = gbl_ops.disks();
        let mut gbl_fb = GblFastboot::new(&mut gbl_ops, parts, Task::run, &tasks, &dl_buffers);

        let expect_boot_a = include_bytes!("../../../libstorage/test/boot_a.bin");
        let expect_boot_b = include_bytes!("../../../libstorage/test/boot_b.bin");
        check_flash_part(&mut gbl_fb, "boot_a", expect_boot_a);
        check_flash_part(&mut gbl_fb, "boot_b", expect_boot_b);
        check_flash_part(&mut gbl_fb, "raw_0", &[0xaau8; 4 * 1024]);
        check_flash_part(&mut gbl_fb, "raw_1", &[0x55u8; 8 * 1024]);
        check_flash_part(&mut gbl_fb, "/0", disk_0);
        check_flash_part(&mut gbl_fb, "/1", disk_1);

        // Partital flash
        let off = 0x200;
        let size = 1024;
        check_flash_part(&mut gbl_fb, "boot_a//200", &expect_boot_a[off..size]);
        check_flash_part(&mut gbl_fb, "boot_b//200", &expect_boot_b[off..size]);
        check_flash_part(&mut gbl_fb, "/0/200", &disk_0[off..size]);
        check_flash_part(&mut gbl_fb, "/1/200", &disk_1[off..size]);
    }

    #[test]
    fn test_flash_partition_sparse() {
        let raw = include_bytes!("../../testdata/sparse_test_raw.bin");
        let sparse = include_bytes!("../../testdata/sparse_test.bin");
        let dl_buffers = Shared::from(vec![vec![0u8; 128 * 1024]; 1]);
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"raw", vec![0u8; raw.len()]);
        let mut gbl_ops = FakeGblOps::new(&storage);
        let tasks = vec![].into();
        let parts = gbl_ops.disks();
        let mut gbl_fb = GblFastboot::new(&mut gbl_ops, parts, Task::run, &tasks, &dl_buffers);

        let download = sparse.to_vec();
        let resp: TestResponder = Default::default();
        set_download(&mut gbl_fb, &download[..]);
        block_on(gbl_fb.flash("/0", &resp)).unwrap();
        assert_eq!(fetch(&mut gbl_fb, "/0".into(), 0, raw.len()).unwrap(), raw);
    }

    /// A helper to invoke OEM commands.
    ///
    /// Returns the result and INFO strings.
    async fn oem(
        fb: &mut impl FastbootImplementation,
        oem_cmd: &str,
        resp: impl InfoSender,
    ) -> CommandResult<String> {
        let mut res = [0u8; MAX_RESPONSE_SIZE];
        fb.oem(oem_cmd, resp, &mut res[..]).await?;
        Ok(from_utf8(&mut res[..]).unwrap().into())
    }

    #[test]
    fn test_async_flash() {
        // Creates two block devices for writing raw and sparse image.
        let sparse_raw = include_bytes!("../../testdata/sparse_test_raw.bin");
        let sparse = include_bytes!("../../testdata/sparse_test.bin");
        let mut dev_sparse = TestBlockDeviceBuilder::new()
            .add_partition("sparse", BackingStore::Size(sparse_raw.len()))
            .build();
        let dl_buffers = Shared::from(vec![vec![0u8; 128 * 1024]; 2]);
        let mut storage = FakeGblOpsStorage::default();
        storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin"));
        storage.add_gpt_device(dev_sparse.disk.io().storage());
        let mut gbl_ops = FakeGblOps::new(&storage);
        let tasks = vec![].into();
        let parts = gbl_ops.disks();
        let mut gbl_fb = GblFastboot::new(&mut gbl_ops, parts, Task::run, &tasks, &dl_buffers);
        let tasks = gbl_fb.tasks();
        let resp: TestResponder = Default::default();

        // "oem gbl-sync-tasks" should return immediately when there is no pending IOs.
        assert!(poll(&mut pin!(oem(&mut gbl_fb, "gbl-sync-tasks", &resp))).unwrap().is_ok());
        // Enable async IO.
        assert!(poll(&mut pin!(oem(&mut gbl_fb, "gbl-enable-async-task", &resp))).unwrap().is_ok());

        // Flashes "boot_a".
        let expect_boot_a = flipped_bits(include_bytes!("../../../libstorage/test/boot_a.bin"));
        set_download(&mut gbl_fb, expect_boot_a.as_slice());
        block_on(gbl_fb.flash("boot_a", &resp)).unwrap();
        check_var(&mut gbl_fb, "block-device", "0:status", "IO pending");

        // Flashes the "sparse" partition on the different block device.
        set_download(&mut gbl_fb, sparse);
        block_on(gbl_fb.flash("sparse", &resp)).unwrap();
        check_var(&mut gbl_fb, "block-device", "1:status", "IO pending");

        {
            // "oem gbl-sync-tasks" should block.
            let oem_sync_blk_fut = &mut pin!(oem(&mut gbl_fb, "gbl-sync-tasks", &resp));
            assert!(poll(oem_sync_blk_fut).is_none());
            // Schedules the disk IO tasks to completion.
            tasks.borrow_mut().run();
            // "oem gbl-sync-tasks" should now be able to finish.
            assert!(poll(oem_sync_blk_fut).unwrap().is_ok());
        }

        // The two blocks should be in the idle state.
        check_var(&mut gbl_fb, "block-device", "0:status", "idle");
        check_var(&mut gbl_fb, "block-device", "1:status", "idle");

        // Verifies flashed image.
        assert_eq!(
            fetch(&mut gbl_fb, "boot_a".into(), 0, expect_boot_a.len()).unwrap(),
            expect_boot_a
        );
        assert_eq!(fetch(&mut gbl_fb, "sparse".into(), 0, sparse_raw.len()).unwrap(), sparse_raw);
    }

    #[test]
    fn test_async_flash_block_on_busy_blk() {
        let dl_buffers = Shared::from(vec![vec![0u8; 128 * 1024]; 2]);
        let mut storage = FakeGblOpsStorage::default();
        storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin"));
        storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_2.bin"));
        let mut gbl_ops = FakeGblOps::new(&storage);
        let tasks = vec![].into();
        let parts = gbl_ops.disks();
        let mut gbl_fb = GblFastboot::new(&mut gbl_ops, parts, Task::run, &tasks, &dl_buffers);
        let tasks = gbl_fb.tasks();
        let resp: TestResponder = Default::default();

        // Enable async IO.
        assert!(poll(&mut pin!(oem(&mut gbl_fb, "gbl-enable-async-task", &resp))).unwrap().is_ok());

        // Flashes boot_a partition.
        let expect_boot_a = flipped_bits(include_bytes!("../../../libstorage/test/boot_a.bin"));
        set_download(&mut gbl_fb, expect_boot_a.as_slice());
        block_on(gbl_fb.flash("boot_a", &resp)).unwrap();

        // Flashes boot_b partition.
        let expect_boot_b = flipped_bits(include_bytes!("../../../libstorage/test/boot_b.bin"));
        set_download(&mut gbl_fb, expect_boot_b.as_slice());
        {
            let flash_boot_b_fut = &mut pin!(gbl_fb.flash("boot_b", &resp));
            // Previous IO has not completed. Block is busy.
            assert!(poll(flash_boot_b_fut).is_none());
            // There should only be the previous disk IO task for "boot_a".
            assert_eq!(tasks.borrow_mut().size(), 1);
            // Schedule the disk IO task for "flash boot_a" to completion.
            tasks.borrow_mut().run();
            // The blocked "flash boot_b" should now be able to finish.
            assert!(poll(flash_boot_b_fut).is_some());
            // There should be a disk IO task spawned for "flash boot_b".
            assert_eq!(tasks.borrow_mut().size(), 1);
            // Schedule the disk IO tasks for "flash boot_b" to completion.
            tasks.borrow_mut().run();
        }

        // Verifies flashed image.
        assert_eq!(
            fetch(&mut gbl_fb, "boot_a".into(), 0, expect_boot_a.len()).unwrap(),
            expect_boot_a
        );
        assert_eq!(
            fetch(&mut gbl_fb, "boot_b".into(), 0, expect_boot_b.len()).unwrap(),
            expect_boot_b
        );
    }

    #[test]
    fn test_async_flash_error() {
        let dl_buffers = Shared::from(vec![vec![0u8; 128 * 1024]; 2]);
        let mut storage = FakeGblOpsStorage::default();
        storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin"));
        let mut gbl_ops = FakeGblOps::new(&storage);
        // Injects an error.
        storage[0].partition_io(None).unwrap().dev().io().error =
            liberror::Error::Other(None).into();
        let tasks = vec![].into();
        let parts = gbl_ops.disks();
        let mut gbl_fb = GblFastboot::new(&mut gbl_ops, parts, Task::run, &tasks, &dl_buffers);
        let tasks = gbl_fb.tasks();
        let resp: TestResponder = Default::default();

        // Enable async IO.
        assert!(poll(&mut pin!(oem(&mut gbl_fb, "gbl-enable-async-task", &resp))).unwrap().is_ok());
        // Flashes boot_a partition.
        let expect_boot_a = flipped_bits(include_bytes!("../../../libstorage/test/boot_a.bin"));
        set_download(&mut gbl_fb, expect_boot_a.as_slice());
        block_on(gbl_fb.flash("boot_a", &resp)).unwrap();
        // Schedules the disk IO tasks to completion.
        tasks.borrow_mut().run();
        // New flash to "boot_a" should fail due to previous error
        set_download(&mut gbl_fb, expect_boot_a.as_slice());
        assert!(block_on(gbl_fb.flash("boot_a", &resp)).is_err());
        // "oem gbl-sync-tasks" should fail.
        assert!(block_on(oem(&mut gbl_fb, "gbl-sync-tasks", &resp)).is_err());
    }

    #[test]
    fn test_async_erase() {
        let dl_buffers = Shared::from(vec![vec![0u8; 128 * 1024]; 2]);
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"raw_0", [0xaau8; 4096]);
        storage.add_raw_device(c"raw_1", [0x55u8; 4096]);
        let mut gbl_ops = FakeGblOps::new(&storage);
        let tasks = vec![].into();
        let parts = gbl_ops.disks();
        let mut gbl_fb = GblFastboot::new(&mut gbl_ops, parts, Task::run, &tasks, &dl_buffers);
        let tasks = gbl_fb.tasks();
        let resp: TestResponder = Default::default();

        // Enable async IO.
        assert!(poll(&mut pin!(oem(&mut gbl_fb, "gbl-enable-async-task", &resp))).unwrap().is_ok());

        // Erases "raw_0".
        block_on(gbl_fb.erase("raw_0", &resp)).unwrap();
        check_var(&mut gbl_fb, "block-device", "0:status", "IO pending");

        // Erases second half of "raw_1"
        block_on(gbl_fb.erase("raw_1//800", &resp)).unwrap();
        check_var(&mut gbl_fb, "block-device", "1:status", "IO pending");

        {
            // "oem gbl-sync-tasks" should block.
            let oem_sync_blk_fut = &mut pin!(oem(&mut gbl_fb, "gbl-sync-tasks", &resp));
            assert!(poll(oem_sync_blk_fut).is_none());
            // Schedules the disk IO tasks to completion.
            tasks.borrow_mut().run();
            // "oem gbl-sync-tasks" should now be able to finish.
            assert!(poll(oem_sync_blk_fut).unwrap().is_ok());
        }

        // The two blocks should be in the idle state.
        check_var(&mut gbl_fb, "block-device", "0:status", "idle");
        check_var(&mut gbl_fb, "block-device", "1:status", "idle");

        assert_eq!(storage[0].partition_io(None).unwrap().dev().io().storage, [0u8; 4096]);
        assert_eq!(
            storage[1].partition_io(None).unwrap().dev().io().storage,
            [[0x55u8; 2048], [0u8; 2048]].concat()
        );
    }

    #[test]
    fn test_default_block() {
        let dl_buffers = Shared::from(vec![vec![0u8; 128 * 1024]; 1]);
        let mut storage = FakeGblOpsStorage::default();
        storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin"));
        let disk_dup = include_bytes!("../../../libstorage/test/gpt_test_2.bin");
        storage.add_gpt_device(disk_dup);
        storage.add_gpt_device(disk_dup);
        let raw_a = [0xaau8; 4 * 1024];
        let raw_b = [0x55u8; 8 * 1024];
        storage.add_raw_device(c"raw", raw_a);
        storage.add_raw_device(c"raw", raw_b);
        let mut gbl_ops = FakeGblOps::new(&storage);
        let tasks = vec![].into();
        let parts = gbl_ops.disks();
        let mut gbl_fb = GblFastboot::new(&mut gbl_ops, parts, Task::run, &tasks, &dl_buffers);
        let resp: TestResponder = Default::default();

        let boot_a = include_bytes!("../../../libstorage/test/boot_a.bin");
        // Flips the bits on partition "vendor_boot_a" on block device #2 to make it different from
        // block #1.
        let vendor_boot_a =
            flipped_bits(include_bytes!("../../../libstorage/test/vendor_boot_a.bin"));
        flash_part(&mut gbl_fb, "vendor_boot_a/2", &vendor_boot_a);

        let size = 512;
        let off = 512;

        check_var(&mut gbl_fb, "gbl-default-block", "", "None");
        // Sets default block to #2
        block_on(oem(&mut gbl_fb, "gbl-set-default-block 2", &resp)).unwrap();
        check_var(&mut gbl_fb, "gbl-default-block", "", "0x2");
        // The following fetch should succeed and fetch from "vendor_boot_a" on block 2.
        check_part_upload(&mut gbl_fb, "vendor_boot_a", off, size, None, &vendor_boot_a);

        // Sets default block to #4 (raw_b)
        block_on(oem(&mut gbl_fb, "gbl-set-default-block 4", &resp)).unwrap();
        check_var(&mut gbl_fb, "gbl-default-block", "", "0x4");
        // The following fetch should succeed and fetch from "raw" on block 4.
        check_part_upload(&mut gbl_fb, "raw", off, size, None, &raw_b);

        // Fetches with explicit storage ID shouldn't be affected.
        check_part_upload(&mut gbl_fb, "boot_a", off, size, Some(0), boot_a);
        check_part_upload(&mut gbl_fb, "raw", off, size, Some(3), &raw_a);
        check_blk_upload(&mut gbl_fb, 1, off, size, disk_dup);

        // Fetching without storage ID should use default ID and thus the following should fail.
        assert!(fetch(&mut gbl_fb, "boot_a".into(), 0, boot_a.len()).is_err());

        // Sets default block to #1 (unmodified `disk_dup`)
        block_on(oem(&mut gbl_fb, "gbl-set-default-block 1", &resp)).unwrap();
        check_var(&mut gbl_fb, "gbl-default-block", "", "0x1");
        // Fetches whole raw block but without block ID should use the default block.
        check_part_upload(&mut gbl_fb, "", off, size, None, disk_dup);

        // Unset default block
        block_on(oem(&mut gbl_fb, "gbl-unset-default-block", &resp)).unwrap();
        check_var(&mut gbl_fb, "gbl-default-block", "", "None");
        // Fetching non-unique partitions should now fail.
        assert!(fetch(&mut gbl_fb, "raw".into(), 0, raw_a.len()).is_err());
        assert!(fetch(&mut gbl_fb, "vendor_boot_a".into(), 0, vendor_boot_a.len()).is_err());
        assert!(fetch(&mut gbl_fb, "/".into(), 0, 512).is_err());
    }

    #[test]
    fn test_set_default_block_invalid_arg() {
        let dl_buffers = Shared::from(vec![vec![0u8; 128 * 1024]; 2]);
        let storage = FakeGblOpsStorage::default();
        let mut gbl_ops = FakeGblOps::new(&storage);
        let tasks = vec![].into();
        let parts = gbl_ops.disks();
        let mut gbl_fb = GblFastboot::new(&mut gbl_ops, parts, Task::run, &tasks, &dl_buffers);
        let resp: TestResponder = Default::default();
        // Missing block device ID.
        assert!(block_on(oem(&mut gbl_fb, "gbl-set-default-block ", &resp)).is_err());
        // Invalid block device ID.
        assert!(block_on(oem(&mut gbl_fb, "gbl-set-default-block zzz", &resp)).is_err());
        // Out of range block device ID. (We've added no block device).
        assert!(block_on(oem(&mut gbl_fb, "gbl-set-default-block 0", &resp)).is_err());
    }

    #[test]
    fn test_reboot_sync_all_blocks() {
        let dl_buffers = Shared::from(vec![vec![0u8; 128 * 1024]; 2]);
        let mut storage = FakeGblOpsStorage::default();
        storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin"));
        let mut gbl_ops = FakeGblOps::new(&storage);
        let tasks = vec![].into();
        let parts = gbl_ops.disks();
        let mut gbl_fb = GblFastboot::new(&mut gbl_ops, parts, Task::run, &tasks, &dl_buffers);
        let tasks = gbl_fb.tasks();
        let resp: TestResponder = Default::default();

        block_on(oem(&mut gbl_fb, "gbl-enable-async-task", &resp)).unwrap();

        // Flashes "boot_a".
        let expect_boot_a = flipped_bits(include_bytes!("../../../libstorage/test/boot_a.bin"));
        set_download(&mut gbl_fb, expect_boot_a.as_slice());
        block_on(gbl_fb.flash("boot_a", &resp)).unwrap();
        // Checks initial state, okay_sent=false.
        assert!(!(*resp.okay_sent.try_lock().unwrap()));
        // Performs a reboot.
        let mut reboot_fut = pin!(gbl_fb.reboot(RebootMode::Normal, &resp));
        // There is a pending flash task. Reboot should wait.
        assert!(poll(&mut reboot_fut).is_none());
        assert!(!(*resp.okay_sent.try_lock().unwrap()));
        assert_eq!(resp.info_messages.try_lock().unwrap()[1], "Syncing storage...");
        // Schedules the disk IO tasks to completion.
        tasks.borrow_mut().run();
        // The reboot can now complete.
        assert!(poll(&mut reboot_fut).is_some());
        assert!((*resp.okay_sent.try_lock().unwrap()));
        assert_eq!(resp.info_messages.try_lock().unwrap()[2], "Rebooting...");
    }

    #[test]
    fn test_continue_sync_all_blocks() {
        let dl_buffers = Shared::from(vec![vec![0u8; 128 * 1024]; 2]);
        let mut storage = FakeGblOpsStorage::default();
        storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin"));
        let mut gbl_ops = FakeGblOps::new(&storage);
        let tasks = vec![].into();
        let parts = gbl_ops.disks();
        let mut gbl_fb = GblFastboot::new(&mut gbl_ops, parts, Task::run, &tasks, &dl_buffers);
        let tasks = gbl_fb.tasks();
        let resp: TestResponder = Default::default();

        block_on(oem(&mut gbl_fb, "gbl-enable-async-task", &resp)).unwrap();

        // Flashes "boot_a".
        let expect_boot_a = flipped_bits(include_bytes!("../../../libstorage/test/boot_a.bin"));
        set_download(&mut gbl_fb, expect_boot_a.as_slice());
        block_on(gbl_fb.flash("boot_a", &resp)).unwrap();
        // Performs a continue.
        let mut continue_fut = pin!(gbl_fb.r#continue(&resp));
        // There is a pending flash task. Continue should wait.
        assert!(poll(&mut continue_fut).is_none());
        assert!(!(*resp.okay_sent.try_lock().unwrap()));
        assert_eq!(resp.info_messages.try_lock().unwrap()[1], "Syncing storage...");
        // Schedules the disk IO tasks to completion.
        tasks.borrow_mut().run();
        // The continue can now complete.
        assert!(poll(&mut continue_fut).is_some());
    }

    /// Generates a length prefixed byte sequence.
    fn length_prefixed(data: &[u8]) -> Vec<u8> {
        [&data.len().to_be_bytes()[..], data].concat()
    }

    /// Used for a test implementation of [GblUsbTransport] and [GblTcpStream].
    #[derive(Default)]
    struct TestListener {
        usb_in_queue: VecDeque<Vec<u8>>,
        usb_out_queue: VecDeque<Vec<u8>>,

        tcp_in_queue: VecDeque<u8>,
        tcp_out_queue: VecDeque<u8>,
    }

    /// A shared [TestListener].
    #[derive(Default)]
    struct SharedTestListener(Mutex<TestListener>);

    impl SharedTestListener {
        /// Locks the listener
        fn lock(&self) -> MutexGuard<TestListener> {
            self.0.try_lock().unwrap()
        }

        /// Adds packet to USB input
        fn add_usb_input(&self, packet: &[u8]) {
            self.lock().usb_in_queue.push_back(packet.into());
        }

        /// Adds bytes to input stream.
        fn add_tcp_input(&self, data: &[u8]) {
            self.lock().tcp_in_queue.append(&mut data.to_vec().into());
        }

        /// Adds a length pre-fixed bytes stream.
        fn add_tcp_length_prefixed_input(&self, data: &[u8]) {
            self.add_tcp_input(&length_prefixed(data));
        }

        /// Gets a copy of `Self::usb_out_queue`.
        fn usb_out_queue(&self) -> VecDeque<Vec<u8>> {
            self.lock().usb_out_queue.clone()
        }

        /// Gets a copy of `Self::tcp_out_queue`.
        fn tcp_out_queue(&self) -> VecDeque<u8> {
            self.lock().tcp_out_queue.clone()
        }

        /// A helper for decoding USB output packets as a string
        fn dump_usb_out_queue(&self) -> String {
            let mut res = String::from("");
            for v in self.lock().usb_out_queue.iter() {
                let v = String::from_utf8(v.clone()).unwrap_or(format!("{:?}", v));
                res += format!("b{:?},\n", v).as_str();
            }
            res
        }

        /// A helper for decoding TCP output data as strings
        fn dump_tcp_out_queue(&self) -> String {
            let mut data = self.lock();
            let mut v;
            let (_, mut remains) = data.tcp_out_queue.make_contiguous().split_at(4);
            let mut res = String::from("");
            while !remains.is_empty() {
                // Parses length-prefixed payload.
                let (len, rest) = remains.split_first_chunk::<{ size_of::<u64>() }>().unwrap();
                (v, remains) = rest.split_at(u64::from_be_bytes(*len).try_into().unwrap());
                let s = String::from_utf8(v.to_vec()).unwrap_or(format!("{:?}", v));
                res += format!("b{:?},\n", s).as_str();
            }
            res
        }
    }

    impl Transport for &SharedTestListener {
        async fn receive_packet(&mut self, out: &mut [u8]) -> Result<usize, Error> {
            match self.lock().usb_in_queue.pop_front() {
                Some(v) => Ok((&v[..]).read(out).unwrap()),
                _ => Err(Error::Other(Some("No more data"))),
            }
        }

        async fn send_packet(&mut self, packet: &[u8]) -> Result<(), Error> {
            Ok(self.lock().usb_out_queue.push_back(packet.into()))
        }
    }

    impl GblUsbTransport for &SharedTestListener {
        fn has_packet(&mut self) -> bool {
            !self.lock().usb_in_queue.is_empty()
        }
    }

    impl TcpStream for &SharedTestListener {
        async fn read_exact(&mut self, out: &mut [u8]) -> Result<(), Error> {
            match self.lock().tcp_in_queue.read(out).unwrap() == out.len() {
                true => Ok(()),
                _ => Err(Error::Other(Some("No more data"))),
            }
        }

        async fn write_exact(&mut self, data: &[u8]) -> Result<(), Error> {
            Ok(self.lock().tcp_out_queue.append(&mut data.to_vec().into()))
        }
    }

    impl GblTcpStream for &SharedTestListener {
        fn accept_new(&mut self) -> bool {
            !self.lock().tcp_in_queue.is_empty()
        }
    }

    /// A helper to make an expected stream of USB output.
    fn make_expected_usb_out(data: &[&[u8]]) -> VecDeque<Vec<u8>> {
        VecDeque::from(data.iter().map(|v| v.to_vec()).collect::<Vec<_>>())
    }

    /// A helper to make an expected stream of TCP output.
    fn make_expected_tcp_out(data: &[&[u8]]) -> VecDeque<u8> {
        let mut res = VecDeque::<u8>::from(b"FB01".to_vec());
        data.iter().for_each(|v| res.append(&mut length_prefixed(v).into()));
        res
    }

    #[test]
    fn test_run_gbl_fastboot() {
        let storage = FakeGblOpsStorage::default();
        let buffers = vec![vec![0u8; 128 * 1024]; 2];
        let mut gbl_ops = FakeGblOps::new(&storage);
        let listener: SharedTestListener = Default::default();
        let (usb, tcp) = (&listener, &listener);

        listener.add_usb_input(b"getvar:version-bootloader");
        listener.add_tcp_input(b"FB01");
        listener.add_tcp_length_prefixed_input(b"getvar:max-download-size");
        listener.add_tcp_length_prefixed_input(b"continue");
        block_on(run_gbl_fastboot_stack::<2>(&mut gbl_ops, buffers, Some(usb), Some(tcp)));

        assert_eq!(
            listener.usb_out_queue(),
            make_expected_usb_out(&[b"OKAY1.0"]),
            "\nActual USB output:\n{}",
            listener.dump_usb_out_queue()
        );

        assert_eq!(
            listener.tcp_out_queue(),
            make_expected_tcp_out(&[b"OKAY0x20000", b"INFOSyncing storage...", b"OKAY"]),
            "\nActual TCP output:\n{}",
            listener.dump_tcp_out_queue()
        );
    }

    #[test]
    fn test_run_gbl_fastboot_parallel_task() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"raw_0", [0u8; 4 * 1024]);
        storage.add_raw_device(c"raw_1", [0u8; 8 * 1024]);
        let buffers = vec![vec![0u8; 128 * 1024]; 2];
        let mut gbl_ops = FakeGblOps::new(&storage);
        let listener: SharedTestListener = Default::default();
        let (usb, tcp) = (&listener, &listener);
        let mut fb_fut =
            pin!(run_gbl_fastboot_stack::<2>(&mut gbl_ops, buffers, Some(usb), Some(tcp)));

        listener.add_usb_input(b"oem gbl-enable-async-task");
        listener.add_usb_input(format!("download:{:#x}", 4 * 1024).as_bytes());
        listener.add_usb_input(&[0x55u8; 4 * 1024]);
        listener.add_usb_input(b"flash:raw_0");

        listener.add_tcp_input(b"FB01");
        listener.add_tcp_length_prefixed_input(format!("download:{:#x}", 8 * 1024).as_bytes());
        listener.add_tcp_length_prefixed_input(&[0xaau8; 8 * 1024]);
        listener.add_tcp_length_prefixed_input(b"flash:raw_1");

        assert!(poll_n_times(&mut fb_fut, 100).is_none());

        assert_eq!(
            listener.usb_out_queue(),
            make_expected_usb_out(&[
                b"OKAY",
                b"DATA00001000",
                b"OKAY",
                b"INFOAn IO task is launched. To sync manually, run \"oem gbl-sync-tasks\".",
                b"OKAY",
            ]),
            "\nActual USB output:\n{}",
            listener.dump_usb_out_queue()
        );

        assert_eq!(
            listener.tcp_out_queue(),
            make_expected_tcp_out(&[
                b"DATA00002000",
                b"OKAY",
                b"INFOAn IO task is launched. To sync manually, run \"oem gbl-sync-tasks\".",
                b"OKAY",
            ]),
            "\nActual TCP output:\n{}",
            listener.dump_tcp_out_queue()
        );

        // Verifies flashed image on raw_0.
        assert_eq!(storage[0].partition_io(None).unwrap().dev().io().storage, [0x55u8; 4 * 1024]);

        // Verifies flashed image on raw_1.
        assert_eq!(storage[1].partition_io(None).unwrap().dev().io().storage, [0xaau8; 8 * 1024]);
    }

    #[test]
    fn test_oem_add_staged_bootloader_file() {
        let storage = FakeGblOpsStorage::default();
        let buffers = vec![vec![0u8; 128 * 1024]; 2];
        let mut gbl_ops = FakeGblOps::new(&storage);
        gbl_ops.get_zbi_bootloader_files_buffer().unwrap().fill(0);
        let listener: SharedTestListener = Default::default();
        let (usb, tcp) = (&listener, &listener);

        // Stages two zbi files.
        listener.add_usb_input(format!("download:{:#x}", 3).as_bytes());
        listener.add_usb_input(b"foo");
        listener.add_usb_input(b"oem add-staged-bootloader-file file_1");
        listener.add_usb_input(format!("download:{:#x}", 3).as_bytes());
        listener.add_usb_input(b"bar");
        listener.add_usb_input(b"oem add-staged-bootloader-file file_2");
        listener.add_usb_input(b"continue");

        block_on(run_gbl_fastboot_stack::<2>(&mut gbl_ops, buffers, Some(usb), Some(tcp)));

        let buffer = gbl_ops.get_zbi_bootloader_files_buffer_aligned().unwrap();
        let container = ZbiContainer::parse(&buffer[..]).unwrap();
        let mut iter = container.iter();
        assert_eq!(iter.next().unwrap().payload.as_bytes(), b"\x06file_1foo");
        assert_eq!(iter.next().unwrap().payload.as_bytes(), b"\x06file_2bar");
        assert!(iter.next().is_none());
    }

    #[test]
    fn test_oem_add_staged_bootloader_file_missing_file_name() {
        let storage = FakeGblOpsStorage::default();
        let buffers = vec![vec![0u8; 128 * 1024]; 2];
        let mut gbl_ops = FakeGblOps::new(&storage);
        let listener: SharedTestListener = Default::default();
        let (usb, tcp) = (&listener, &listener);

        listener.add_usb_input(format!("download:{:#x}", 3).as_bytes());
        listener.add_usb_input(b"foo");
        listener.add_usb_input(b"oem add-staged-bootloader-file");
        listener.add_usb_input(b"continue");

        block_on(run_gbl_fastboot_stack::<2>(&mut gbl_ops, buffers, Some(usb), Some(tcp)));

        assert_eq!(
            listener.usb_out_queue(),
            make_expected_usb_out(&[
                b"DATA00000003",
                b"OKAY",
                b"FAILMissing file name",
                b"INFOSyncing storage...",
                b"OKAY",
            ]),
            "\nActual USB output:\n{}",
            listener.dump_usb_out_queue()
        )
    }

    #[test]
    fn test_oem_add_staged_bootloader_file_missing_download() {
        let storage = FakeGblOpsStorage::default();
        let buffers = vec![vec![0u8; 128 * 1024]; 2];
        let mut gbl_ops = FakeGblOps::new(&storage);
        let listener: SharedTestListener = Default::default();
        let (usb, tcp) = (&listener, &listener);

        listener.add_usb_input(b"oem add-staged-bootloader-file file1");
        listener.add_usb_input(b"continue");

        block_on(run_gbl_fastboot_stack::<2>(&mut gbl_ops, buffers, Some(usb), Some(tcp)));

        assert_eq!(
            listener.usb_out_queue(),
            make_expected_usb_out(&[b"FAILNo file staged", b"INFOSyncing storage...", b"OKAY",]),
            "\nActual USB output:\n{}",
            listener.dump_usb_out_queue()
        );
    }

    #[test]
    fn test_fuchsia_fastboot_mdns_packet() {
        let expected = [
            0x00, 0x00, 0x84, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x02, 0x09, 0x5f,
            0x66, 0x61, 0x73, 0x74, 0x62, 0x6f, 0x6f, 0x74, 0x04, 0x5f, 0x74, 0x63, 0x70, 0x05,
            0x6c, 0x6f, 0x63, 0x61, 0x6c, 0x00, 0x00, 0x0c, 0x80, 0x01, 0x00, 0x00, 0x00, 0x78,
            0x00, 0x19, 0x16, 0x66, 0x75, 0x63, 0x68, 0x73, 0x69, 0x61, 0x2d, 0x35, 0x32, 0x35,
            0x34, 0x2d, 0x30, 0x30, 0x31, 0x32, 0x2d, 0x33, 0x34, 0x35, 0x36, 0xc0, 0x0c, 0xc0,
            0x2c, 0x00, 0x21, 0x80, 0x01, 0x00, 0x00, 0x00, 0x78, 0x00, 0x1f, 0x00, 0x00, 0x00,
            0x00, 0x15, 0xb2, 0x16, 0x66, 0x75, 0x63, 0x68, 0x73, 0x69, 0x61, 0x2d, 0x35, 0x32,
            0x35, 0x34, 0x2d, 0x30, 0x30, 0x31, 0x32, 0x2d, 0x33, 0x34, 0x35, 0x36, 0xc0, 0x1b,
            0xc0, 0x57, 0x00, 0x1c, 0x80, 0x01, 0x00, 0x00, 0x00, 0x78, 0x00, 0x10, 0xfe, 0x80,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x50, 0x54, 0x00, 0xff, 0xfe, 0x12, 0x34, 0x56,
        ];
        let ip6_addr = &[
            0xfe, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x50, 0x54, 0x00, 0xff, 0xfe, 0x12,
            0x34, 0x56,
        ];
        assert_eq!(
            fuchsia_fastboot_mdns_packet("fuchsia-5254-0012-3456", ip6_addr).unwrap(),
            expected
        );
    }

    #[test]
    fn test_fuchsia_fastboot_mdns_packet_invalid_node_name() {
        let ip6_addr = &[
            0xfe, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x50, 0x54, 0x00, 0xff, 0xfe, 0x12,
            0x34, 0x56,
        ];
        assert!(fuchsia_fastboot_mdns_packet("fuchsia-5254-0012-345", ip6_addr).is_err());
        assert!(fuchsia_fastboot_mdns_packet("fuchsia-5254-0012-34567", ip6_addr).is_err());
    }

    #[test]
    fn test_oem_update_gpt() {
        let disk_orig = include_bytes!("../../../libstorage/test/gpt_test_1.bin");
        // Erase the primary and secondary header.
        let mut disk = disk_orig.to_vec();
        disk[512..][..512].fill(0);
        disk.last_chunk_mut::<512>().unwrap().fill(0);

        let mut storage = FakeGblOpsStorage::default();
        storage.add_gpt_device(&disk);
        storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_2.bin"));
        let buffers = vec![vec![0u8; 128 * 1024]; 2];
        let mut gbl_ops = FakeGblOps::new(&storage);
        let listener: SharedTestListener = Default::default();
        let (usb, tcp) = (&listener, &listener);

        // Checks that there is no valid partitions for block #0.
        listener.add_usb_input(b"getvar:partition-size:boot_a");
        listener.add_usb_input(b"getvar:partition-size:boot_b");
        // No partitions on block #0 should show up in `getvar:all` despite being a GPT device,
        // since the GPTs are corrupted.
        listener.add_usb_input(b"getvar:all");
        // Download a GPT
        let gpt = &disk_orig[..34 * 512];
        listener.add_usb_input(format!("download:{:#x}", gpt.len()).as_bytes());
        listener.add_usb_input(gpt);
        listener.add_usb_input(b"flash:gpt/0");
        // Checks that we can get partition info now.
        listener.add_usb_input(b"getvar:partition-size:boot_a");
        listener.add_usb_input(b"getvar:partition-size:boot_b");
        listener.add_usb_input(b"getvar:all");

        listener.add_usb_input(b"continue");

        block_on(run_gbl_fastboot_stack::<2>(&mut gbl_ops, buffers, Some(usb), Some(tcp)));

        assert_eq!(
            listener.usb_out_queue(),
            make_expected_usb_out(&[
                b"FAILNotFound",
                b"FAILNotFound",
                b"INFOmax-download-size: 0x20000",
                b"INFOversion-bootloader: 1.0",
                b"INFOmax-fetch-size: 0xffffffffffffffff",
                b"INFOblock-device:0:total-blocks: 0x80",
                b"INFOblock-device:0:block-size: 0x200",
                b"INFOblock-device:0:status: idle",
                b"INFOblock-device:1:total-blocks: 0x100",
                b"INFOblock-device:1:block-size: 0x200",
                b"INFOblock-device:1:status: idle",
                b"INFOgbl-default-block: None",
                b"INFOpartition-size:vendor_boot_a/1: 0x1000",
                b"INFOpartition-type:vendor_boot_a/1: raw",
                b"INFOpartition-size:vendor_boot_b/1: 0x1800",
                b"INFOpartition-type:vendor_boot_b/1: raw",
                format!("INFO{}:1: {}:1", FakeGblOps::GBL_TEST_VAR, FakeGblOps::GBL_TEST_VAR_VAL)
                    .as_bytes(),
                format!("INFO{}:2: {}:2", FakeGblOps::GBL_TEST_VAR, FakeGblOps::GBL_TEST_VAR_VAL)
                    .as_bytes(),
                b"OKAY",
                b"DATA00004400",
                b"OKAY",
                b"INFOUpdating GPT...",
                b"OKAY",
                b"OKAY0x2000",
                b"OKAY0x3000",
                b"INFOmax-download-size: 0x20000",
                b"INFOversion-bootloader: 1.0",
                b"INFOmax-fetch-size: 0xffffffffffffffff",
                b"INFOblock-device:0:total-blocks: 0x80",
                b"INFOblock-device:0:block-size: 0x200",
                b"INFOblock-device:0:status: idle",
                b"INFOblock-device:1:total-blocks: 0x100",
                b"INFOblock-device:1:block-size: 0x200",
                b"INFOblock-device:1:status: idle",
                b"INFOgbl-default-block: None",
                b"INFOpartition-size:boot_a/0: 0x2000",
                b"INFOpartition-type:boot_a/0: raw",
                b"INFOpartition-size:boot_b/0: 0x3000",
                b"INFOpartition-type:boot_b/0: raw",
                b"INFOpartition-size:vendor_boot_a/1: 0x1000",
                b"INFOpartition-type:vendor_boot_a/1: raw",
                b"INFOpartition-size:vendor_boot_b/1: 0x1800",
                b"INFOpartition-type:vendor_boot_b/1: raw",
                format!("INFO{}:1: {}:1", FakeGblOps::GBL_TEST_VAR, FakeGblOps::GBL_TEST_VAR_VAL)
                    .as_bytes(),
                format!("INFO{}:2: {}:2", FakeGblOps::GBL_TEST_VAR, FakeGblOps::GBL_TEST_VAR_VAL)
                    .as_bytes(),
                b"OKAY",
                b"INFOSyncing storage...",
                b"OKAY",
            ]),
            "\nActual USB output:\n{}",
            listener.dump_usb_out_queue()
        );
    }

    #[test]
    fn test_oem_update_gpt_resize() {
        let disk_orig = include_bytes!("../../../libstorage/test/gpt_test_1.bin");
        let mut disk = disk_orig.to_vec();
        // Doubles the size of the disk
        disk.resize(disk_orig.len() * 2, 0);

        let mut storage = FakeGblOpsStorage::default();
        storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_2.bin"));
        storage.add_gpt_device(&disk);
        let buffers = vec![vec![0u8; 128 * 1024]; 2];
        let mut gbl_ops = FakeGblOps::new(&storage);
        let listener: SharedTestListener = Default::default();
        let (usb, tcp) = (&listener, &listener);

        // Checks current size of last partition `boot_b`.
        listener.add_usb_input(b"getvar:partition-size:boot_b");
        // Sets a default block.
        listener.add_usb_input(b"oem gbl-set-default-block 1");
        let gpt = &disk_orig[..34 * 512];
        listener.add_usb_input(format!("download:{:#x}", gpt.len()).as_bytes());
        listener.add_usb_input(gpt);
        // No need to specify block device index
        listener.add_usb_input(b"flash:gpt//resize");
        // Checks updated size of last partition `boot_b`.
        listener.add_usb_input(b"getvar:partition-size:boot_b");
        listener.add_usb_input(b"continue");

        block_on(run_gbl_fastboot_stack::<2>(&mut gbl_ops, buffers, Some(usb), Some(tcp)));

        assert_eq!(
            listener.usb_out_queue(),
            make_expected_usb_out(&[
                b"OKAY0x3000",
                b"INFODefault block device: 0x1",
                b"OKAY",
                b"DATA00004400",
                b"OKAY",
                b"INFOUpdating GPT...",
                b"OKAY",
                b"OKAY0x15a00",
                b"INFOSyncing storage...",
                b"OKAY",
            ]),
            "\nActual USB output:\n{}",
            listener.dump_usb_out_queue()
        );
    }

    #[test]
    fn test_oem_update_gpt_no_downloaded_gpt() {
        let disk = include_bytes!("../../../libstorage/test/gpt_test_1.bin");
        let mut storage = FakeGblOpsStorage::default();
        storage.add_gpt_device(&disk);
        let buffers = vec![vec![0u8; 128 * 1024]; 2];
        let mut gbl_ops = FakeGblOps::new(&storage);
        let listener: SharedTestListener = Default::default();
        let (usb, tcp) = (&listener, &listener);

        listener.add_usb_input(b"flash:gpt/0");
        listener.add_usb_input(b"continue");

        block_on(run_gbl_fastboot_stack::<2>(&mut gbl_ops, buffers, Some(usb), Some(tcp)));

        assert_eq!(
            listener.usb_out_queue(),
            make_expected_usb_out(&[b"FAILNo GPT downloaded", b"INFOSyncing storage...", b"OKAY",]),
            "\nActual USB output:\n{}",
            listener.dump_usb_out_queue()
        );
    }

    #[test]
    fn test_oem_update_gpt_bad_gpt() {
        let disk = include_bytes!("../../../libstorage/test/gpt_test_1.bin");
        let mut storage = FakeGblOpsStorage::default();
        storage.add_gpt_device(&disk);
        let buffers = vec![vec![0u8; 128 * 1024]; 2];
        let mut gbl_ops = FakeGblOps::new(&storage);
        let listener: SharedTestListener = Default::default();
        let (usb, tcp) = (&listener, &listener);
        // Download a bad GPT.
        let mut gpt = disk[..34 * 512].to_vec();
        gpt[512] = !gpt[512];
        listener.add_usb_input(format!("download:{:#x}", gpt.len()).as_bytes());
        listener.add_usb_input(&gpt);
        listener.add_usb_input(b"flash:gpt/0");
        listener.add_usb_input(b"continue");

        block_on(run_gbl_fastboot_stack::<2>(&mut gbl_ops, buffers, Some(usb), Some(tcp)));

        assert_eq!(
            listener.usb_out_queue(),
            make_expected_usb_out(&[
                b"DATA00004400",
                b"OKAY",
                b"INFOUpdating GPT...",
                b"FAILGptError(\n    IncorrectMagic(\n        6075990659671082682,\n    ),\n)",
                b"INFOSyncing storage...",
                b"OKAY",
            ]),
            "\nActual USB output:\n{}",
            listener.dump_usb_out_queue()
        );
    }

    #[test]
    fn test_oem_update_gpt_invalid_input() {
        let disk_orig = include_bytes!("../../../libstorage/test/gpt_test_1.bin");
        let mut storage = FakeGblOpsStorage::default();
        storage.add_gpt_device(&disk_orig);
        storage.add_gpt_device(&disk_orig);
        let buffers = vec![vec![0u8; 128 * 1024]; 2];
        let mut gbl_ops = FakeGblOps::new(&storage);
        let listener: SharedTestListener = Default::default();
        let (usb, tcp) = (&listener, &listener);

        let gpt = &disk_orig[..34 * 512];
        listener.add_usb_input(format!("download:{:#x}", gpt.len()).as_bytes());
        listener.add_usb_input(gpt);
        // Missing block device ID.
        listener.add_usb_input(b"flash:gpt");
        // Out of range block device ID.
        listener.add_usb_input(b"flash:gpt/2");
        // Invalid option.
        listener.add_usb_input(b"flash:gpt/0/invalid-arg");
        listener.add_usb_input(b"continue");
        block_on(run_gbl_fastboot_stack::<2>(&mut gbl_ops, buffers, Some(usb), Some(tcp)));

        assert_eq!(
            listener.usb_out_queue(),
            make_expected_usb_out(&[
                b"DATA00004400",
                b"OKAY",
                b"FAILBlock ID is required for flashing GPT",
                b"FAILInvalid block ID",
                b"FAILUnknown argument",
                b"INFOSyncing storage...",
                b"OKAY",
            ]),
            "\nActual USB output:\n{}",
            listener.dump_usb_out_queue()
        );
    }

    #[test]
    fn test_oem_update_gpt_fail_on_raw_blk() {
        let disk_orig = include_bytes!("../../../libstorage/test/gpt_test_1.bin");
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"raw_0", [0u8; 1024 * 1024]);
        let buffers = vec![vec![0u8; 128 * 1024]; 2];
        let mut gbl_ops = FakeGblOps::new(&storage);
        let listener: SharedTestListener = Default::default();
        let (usb, tcp) = (&listener, &listener);

        let gpt = &disk_orig[..34 * 512];
        listener.add_usb_input(format!("download:{:#x}", gpt.len()).as_bytes());
        listener.add_usb_input(gpt);
        listener.add_usb_input(b"flash:gpt/0");
        listener.add_usb_input(b"continue");
        block_on(run_gbl_fastboot_stack::<2>(&mut gbl_ops, buffers, Some(usb), Some(tcp)));

        assert_eq!(
            listener.usb_out_queue(),
            make_expected_usb_out(&[
                b"DATA00004400",
                b"OKAY",
                b"INFOUpdating GPT...",
                b"FAILBlock device is not for GPT",
                b"INFOSyncing storage...",
                b"OKAY",
            ]),
            "\nActual USB output:\n{}",
            listener.dump_usb_out_queue()
        );
    }

    #[test]
    fn test_oem_erase_gpt() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_1.bin"));
        storage.add_gpt_device(include_bytes!("../../../libstorage/test/gpt_test_2.bin"));
        let buffers = vec![vec![0u8; 128 * 1024]; 2];
        let mut gbl_ops = FakeGblOps::new(&storage);
        let listener: SharedTestListener = Default::default();
        let (usb, tcp) = (&listener, &listener);

        // Erases the GPT on disk #0.
        listener.add_usb_input(b"erase:gpt/0");
        // Checks that we can no longer get partition info on disk #0.
        listener.add_usb_input(b"getvar:partition-size:boot_a");
        listener.add_usb_input(b"getvar:partition-size:boot_b");
        // Checks that we can still get partition info on disk #1.
        listener.add_usb_input(b"getvar:partition-size:vendor_boot_a");
        listener.add_usb_input(b"getvar:partition-size:vendor_boot_b");
        listener.add_usb_input(b"continue");

        block_on(run_gbl_fastboot_stack::<2>(&mut gbl_ops, buffers, Some(usb), Some(tcp)));

        assert_eq!(
            listener.usb_out_queue(),
            make_expected_usb_out(&[
                b"OKAY",
                b"FAILNotFound",
                b"FAILNotFound",
                b"OKAY0x1000",
                b"OKAY0x1800",
                b"INFOSyncing storage...",
                b"OKAY",
            ]),
            "\nActual USB output:\n{}",
            listener.dump_usb_out_queue()
        );
    }

    #[test]
    fn test_oem_erase_gpt_fail_on_raw_blk() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"raw_0", [0u8; 1024 * 1024]);
        let buffers = vec![vec![0u8; 128 * 1024]; 2];
        let mut gbl_ops = FakeGblOps::new(&storage);
        let listener: SharedTestListener = Default::default();
        let (usb, tcp) = (&listener, &listener);

        listener.add_usb_input(b"erase:gpt/0");
        listener.add_usb_input(b"continue");
        block_on(run_gbl_fastboot_stack::<2>(&mut gbl_ops, buffers, Some(usb), Some(tcp)));

        assert_eq!(
            listener.usb_out_queue(),
            make_expected_usb_out(&[
                b"FAILBlock device is not for GPT",
                b"INFOSyncing storage...",
                b"OKAY",
            ]),
            "\nActual USB output:\n{}",
            listener.dump_usb_out_queue()
        );
    }

    /// Helper for testing fastboot set_active in fuchsia A/B/R mode.
    fn test_run_gbl_fastboot_set_active_fuchsia_abr(cmd: &str, slot: SlotIndex) {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"durable_boot", [0x00u8; 4 * 1024]);
        let buffers = vec![vec![0u8; 128 * 1024]; 2];
        let mut gbl_ops = FakeGblOps::new(&storage);
        gbl_ops.os = Some(Os::Fuchsia);
        let listener: SharedTestListener = Default::default();
        let (usb, tcp) = (&listener, &listener);

        mark_slot_unbootable(&mut GblAbrOps(&mut gbl_ops), SlotIndex::A).unwrap();
        mark_slot_unbootable(&mut GblAbrOps(&mut gbl_ops), SlotIndex::B).unwrap();

        // Flash some data to `durable_boot` after A/B/R metadata. This is for testing that sync
        // storage is done first.
        let data = vec![0x55u8; 4 * 1024 - ABR_DATA_SIZE];
        listener.add_usb_input(b"oem gbl-enable-async-task");
        listener.add_usb_input(format!("download:{:#x}", 4 * 1024 - ABR_DATA_SIZE).as_bytes());
        listener.add_usb_input(&data);
        listener.add_usb_input(format!("flash:durable_boot//{:#x}", ABR_DATA_SIZE).as_bytes());
        // Issues set_active commands
        listener.add_usb_input(cmd.as_bytes());
        listener.add_usb_input(b"continue");
        block_on(run_gbl_fastboot_stack::<2>(&mut gbl_ops, buffers, Some(usb), Some(tcp)));

        assert_eq!(
            listener.usb_out_queue(),
            make_expected_usb_out(&[
                b"OKAY",
                b"DATA00000fe0",
                b"OKAY",
                b"INFOAn IO task is launched. To sync manually, run \"oem gbl-sync-tasks\".",
                b"OKAY",
                b"OKAY",
                b"INFOSyncing storage...",
                b"OKAY",
            ]),
            "\nActual USB output:\n{}",
            listener.dump_usb_out_queue()
        );

        assert_eq!(get_boot_slot(&mut GblAbrOps(&mut gbl_ops), true), (slot, false));
        // Verifies storage sync
        assert_eq!(
            storage[0].partition_io(None).unwrap().dev().io().storage[ABR_DATA_SIZE..],
            data
        );
    }

    #[test]
    fn test_run_gbl_fastboot_set_active_fuchsia_abr_a() {
        test_run_gbl_fastboot_set_active_fuchsia_abr("set_active:a", SlotIndex::A);
    }

    #[test]
    fn test_run_gbl_fastboot_set_active_fuchsia_abr_b() {
        test_run_gbl_fastboot_set_active_fuchsia_abr("set_active:b", SlotIndex::B);
    }

    #[test]
    fn test_run_gbl_fastboot_set_active_fuchsia_abr_invalid_slot() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"durable_boot", [0x00u8; 4 * 1024]);
        let buffers = vec![vec![0u8; 128 * 1024]; 2];
        let mut gbl_ops = FakeGblOps::new(&storage);
        gbl_ops.os = Some(Os::Fuchsia);
        let listener: SharedTestListener = Default::default();
        let (usb, tcp) = (&listener, &listener);

        listener.add_usb_input(b"set_active:r");
        listener.add_usb_input(b"continue");
        block_on(run_gbl_fastboot_stack::<2>(&mut gbl_ops, buffers, Some(usb), Some(tcp)));

        assert_eq!(
            listener.usb_out_queue(),
            make_expected_usb_out(&[
                b"FAILInvalid slot index for Fuchsia A/B/R",
                b"INFOSyncing storage...",
                b"OKAY",
            ]),
            "\nActual USB output:\n{}",
            listener.dump_usb_out_queue()
        );
    }

    #[test]
    fn test_run_gbl_fastboot_fuchsia_reboot_bootloader_abr() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"durable_boot", [0x00u8; 4 * 1024]);
        let buffers = vec![vec![0u8; 128 * 1024]; 2];
        let mut gbl_ops = FakeGblOps::new(&storage);
        gbl_ops.os = Some(Os::Fuchsia);
        let listener: SharedTestListener = Default::default();
        let (usb, tcp) = (&listener, &listener);

        listener.add_usb_input(b"reboot-bootloader");
        listener.add_usb_input(b"continue");
        block_on(run_gbl_fastboot_stack::<2>(&mut gbl_ops, buffers, Some(usb), Some(tcp)));

        assert_eq!(
            listener.usb_out_queue(),
            make_expected_usb_out(&[
                b"INFOSyncing storage...",
                b"INFORebooting to bootloader...",
                b"OKAY",
                b"FAILUnknown",
                b"INFOSyncing storage...",
                b"OKAY",
            ]),
            "\nActual USB output:\n{}",
            listener.dump_usb_out_queue()
        );

        assert_eq!(get_and_clear_one_shot_bootloader(&mut GblAbrOps(&mut gbl_ops)), Ok(true));
    }

    #[test]
    fn test_run_gbl_fastboot_fuchsia_reboot_recovery_abr() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"durable_boot", [0x00u8; 4 * 1024]);
        let buffers = vec![vec![0u8; 128 * 1024]; 2];
        let mut gbl_ops = FakeGblOps::new(&storage);
        gbl_ops.os = Some(Os::Fuchsia);
        let listener: SharedTestListener = Default::default();
        let (usb, tcp) = (&listener, &listener);

        listener.add_usb_input(b"reboot-recovery");
        listener.add_usb_input(b"continue");
        block_on(run_gbl_fastboot_stack::<2>(&mut gbl_ops, buffers, Some(usb), Some(tcp)));

        assert_eq!(
            listener.usb_out_queue(),
            make_expected_usb_out(&[
                b"INFOSyncing storage...",
                b"INFORebooting to recovery...",
                b"OKAY",
                b"FAILUnknown",
                b"INFOSyncing storage...",
                b"OKAY",
            ]),
            "\nActual USB output:\n{}",
            listener.dump_usb_out_queue()
        );

        // One shot recovery is set.
        assert_eq!(get_boot_slot(&mut GblAbrOps(&mut gbl_ops), true), (SlotIndex::R, false));
        assert_eq!(get_boot_slot(&mut GblAbrOps(&mut gbl_ops), true), (SlotIndex::A, false));
    }

    #[test]
    fn test_legacy_fvm_partition_aliase() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"fuchsia-fvm", [0x00u8; 4 * 1024]);
        let buffers = vec![vec![0u8; 128 * 1024]; 2];
        let mut gbl_ops = FakeGblOps::new(&storage);
        gbl_ops.os = Some(Os::Fuchsia);
        let listener: SharedTestListener = Default::default();
        let (usb, tcp) = (&listener, &listener);

        listener.add_usb_input(format!("download:{:#x}", 4 * 1024).as_bytes());
        listener.add_usb_input(&[0xaau8; 4 * 1024]);
        listener.add_usb_input(b"flash:fvm");
        listener.add_usb_input(b"continue");
        block_on(run_gbl_fastboot_stack::<2>(&mut gbl_ops, buffers, Some(usb), Some(tcp)));

        assert_eq!(
            listener.usb_out_queue(),
            make_expected_usb_out(&[
                b"DATA00001000",
                b"OKAY",
                b"OKAY",
                b"INFOSyncing storage...",
                b"OKAY",
            ]),
            "\nActual USB output:\n{}",
            listener.dump_usb_out_queue()
        );
    }
}
