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

//! Android boot support.

use crate::{
    constants::{FDT_ALIGNMENT, KERNEL_ALIGNMENT},
    device_tree::{DeviceTreeComponentSource, DeviceTreeComponentsRegistry},
    fastboot::{
        run_gbl_fastboot, run_gbl_fastboot_stack, BufferPool, GblFastbootResult, GblTcpStream,
        GblUsbTransport, LoadedImageInfo, PinFutContainer, Shared,
    },
    gbl_print, gbl_println,
    ops::RebootReason,
    GblOps, Result,
};
use bootparams::commandline::CommandlineBuilder;
use core::{array::from_fn, ffi::CStr};
use dttable::DtTableImage;
use fastboot::local_session::LocalSession;
use fdt::Fdt;
use gbl_async::block_on;
use liberror::Error;
use libutils::{aligned_offset, aligned_subslice};
use misc::{AndroidBootMode, BootloaderMessage};
use safemath::SafeNum;

mod vboot;
use vboot::{avb_verify_slot, PartitionsToVerify};

pub(crate) mod load;
use load::split_chunks;
pub use load::{android_load_verify, LoadedImages};

/// Device tree bootargs property to store kernel command line.
pub const BOOTARGS_PROP: &CStr = c"bootargs";

/// A helper to convert a bytes slice containing a null-terminated string to `str`
fn cstr_bytes_to_str(data: &[u8]) -> core::result::Result<&str, Error> {
    Ok(CStr::from_bytes_until_nul(data)?.to_str()?)
}

/// Loads Android images from the given slot on disk and fixes up bootconfig, commandline, and FDT.
///
/// On success, returns a tuple of (ramdisk, fdt, kernel, unused buffer).
pub fn android_load_verify_fixup<'a, 'b, 'c>(
    ops: &mut impl GblOps<'b, 'c>,
    slot: u8,
    is_recovery: bool,
    load: &'a mut [u8],
) -> Result<(&'a mut [u8], &'a mut [u8], &'a mut [u8], &'a mut [u8])> {
    let load_addr = load.as_ptr() as usize;
    let images = android_load_verify(ops, slot, is_recovery, load)?;

    let mut components = DeviceTreeComponentsRegistry::new();
    let fdt_load = &mut images.unused[..];
    // TODO(b/353272981): Remove get_custom_device_tree
    let (fdt_load, base, overlays) = match ops.get_custom_device_tree() {
        Some(v) => (fdt_load, v, &[][..]),
        _ => {
            let mut remains = match images.dtbo.len() > 0 {
                // TODO(b/384964561, b/374336105): Investigate if we can avoid additional copy.
                true => {
                    gbl_println!(ops, "Handling overlays from dtbo");
                    components
                        .append_from_dtbo(&DtTableImage::from_bytes(images.dtbo)?, fdt_load)?
                }
                _ => fdt_load,
            };

            if images.dtb.len() > 0 {
                gbl_println!(ops, "Handling device tree from boot/vendor_boot");
                remains =
                    components.append(ops, DeviceTreeComponentSource::Boot, images.dtb, remains)?;
            }

            if images.dtb_part.len() > 0 {
                gbl_println!(ops, "Handling device trees from dtb");
                let dttable = DtTableImage::from_bytes(images.dtb_part)?;
                remains = components.append_from_dttable(true, &dttable, remains)?;
            }

            gbl_println!(ops, "Selecting device tree components");
            ops.select_device_trees(&mut components)?;
            let (base, overlays) = components.selected()?;
            (remains, base, overlays)
        }
    };
    let fdt_load = aligned_subslice(fdt_load, FDT_ALIGNMENT)?;
    let mut fdt = Fdt::new_from_init(&mut fdt_load[..], base)?;

    // Adds ramdisk range to FDT
    let ramdisk_addr: u64 = (images.ramdisk.as_ptr() as usize).try_into().map_err(Error::from)?;
    let ramdisk_end: u64 = ramdisk_addr + u64::try_from(images.ramdisk.len()).unwrap();
    fdt.set_property("chosen", c"linux,initrd-start", &ramdisk_addr.to_be_bytes())?;
    fdt.set_property("chosen", c"linux,initrd-end", &ramdisk_end.to_be_bytes())?;
    gbl_println!(ops, "linux,initrd-start: {:#x}", ramdisk_addr);
    gbl_println!(ops, "linux,initrd-end: {:#x}", ramdisk_end);

    // Updates the FDT commandline.
    let device_tree_commandline_length = match fdt.get_property("chosen", BOOTARGS_PROP) {
        Ok(val) => CStr::from_bytes_until_nul(val).map_err(Error::from)?.to_bytes().len(),
        Err(_) => 0,
    };

    // Reserves 1024 bytes for separators and fixup.
    let final_commandline_len = device_tree_commandline_length
        + images.boot_cmdline.len()
        + images.vendor_cmdline.len()
        + 1024;
    let final_commandline_buffer =
        fdt.set_property_placeholder("chosen", BOOTARGS_PROP, final_commandline_len)?;
    let mut commandline_builder =
        CommandlineBuilder::new_from_prefix(&mut final_commandline_buffer[..])?;
    commandline_builder.add(images.boot_cmdline)?;
    commandline_builder.add(images.vendor_cmdline)?;

    // TODO(b/353272981): Handle buffer too small
    commandline_builder.add_with(|current, out| {
        // TODO(b/353272981): Verify provided command line and fail here.
        Ok(ops.fixup_os_commandline(current, out)?.map(|fixup| fixup.len()).unwrap_or(0))
    })?;
    gbl_println!(ops, "final cmdline: \"{}\"", commandline_builder.as_str());

    gbl_println!(ops, "Applying {} overlays", overlays.len());
    fdt.multioverlay_apply(overlays)?;
    gbl_println!(ops, "Overlays applied");
    // `DeviceTreeComponentsRegistry` internally uses ArrayVec which causes it to have a default
    // life time equal to the scope it lives in. This is unnecessarily strict and prevents us from
    // accessing `load` buffer.
    drop(components);

    // Make sure we provide an actual device tree size, so FW can calculate amount of space
    // available for fixup.
    fdt.shrink_to_fit()?;
    // TODO(b/353272981): Make a copy of current device tree and verify provided fixup.
    // TODO(b/353272981): Handle buffer too small
    ops.fixup_device_tree(fdt.as_mut())?;
    fdt.shrink_to_fit()?;

    // Moves the kernel forward to reserve as much space as possible. This is in case there is not
    // enough memory after `load`, i.e. the memory after it is not mapped or is reserved.
    let ramdisk_off = usize::try_from(ramdisk_addr).unwrap() - load_addr;
    let fdt_len = fdt.header_ref()?.actual_size();
    let fdt_off = fdt_load.as_ptr() as usize - load_addr;
    let kernel_off = images.kernel.as_ptr() as usize - load_addr;
    let kernel_len = images.kernel.len();
    let mut kernel_new = (SafeNum::from(fdt_off) + fdt_len).try_into().map_err(Error::from)?;
    kernel_new += aligned_offset(&mut load[kernel_new..], KERNEL_ALIGNMENT)?;
    load.copy_within(kernel_off..kernel_off + kernel_len, kernel_new);
    let ([_, ramdisk, fdt, kernel], unused) =
        split_chunks(load, &[ramdisk_off, fdt_off - ramdisk_off, kernel_new - fdt_off, kernel_len]);
    let ramdisk = &mut ramdisk[..usize::try_from(ramdisk_end - ramdisk_addr).unwrap()];
    Ok((ramdisk, fdt, kernel, unused))
}

/// Gets the target slot to boot.
///
/// * If GBL is slotless (`GblOps::get_current_slot()` returns `Error::Unsupported`), the API
///   behaves the same as `GblOps::get_next_slot()`.
/// * If GBL is slotted, the API behaves the same as `GblOps::get_current_slot()` and
///   `mark_boot_attempt` is ignored.
/// * Default to A slot if slotting backend is not implemented on the platform.
pub(crate) fn get_boot_slot<'a, 'b, 'c>(
    ops: &mut impl GblOps<'a, 'b>,
    mark_boot_attempt: bool,
) -> Result<char> {
    let slot = match ops.get_current_slot() {
        // Slotless bootloader
        Err(Error::Unsupported) => {
            gbl_println!(ops, "GBL is Slotless.");
            ops.get_next_slot(mark_boot_attempt)
        }
        v => v,
    };
    match slot {
        Ok(slot) => Ok(slot.suffix.0),
        Err(Error::Unsupported) => {
            // Default to slot A if slotting is not supported.
            // Slotless partition name is currently not supported. Revisit if this causes problems.
            gbl_println!(ops, "Slotting is not supported. Choose A slot by default");
            Ok('a')
        }
        Err(e) => {
            gbl_println!(ops, "Failed to get boot slot: {e}");
            Err(e.into())
        }
    }
}

/// Provides methods to run GBL fastboot.
pub struct GblFastbootEntry<'d, G> {
    ops: &'d mut G,
    load: &'d mut [u8],
    result: &'d mut GblFastbootResult,
}

impl<'a, 'd, 'e, G> GblFastbootEntry<'d, G>
where
    G: GblOps<'a, 'e>,
{
    /// Runs GBL fastboot with the given buffer pool, tasks container, and usb/tcp/local transport
    /// channels.
    ///
    /// # Args
    ///
    /// * `buffer_pool`: An implementation of `BufferPool` wrapped in `Shared` for allocating
    ///    download buffers.
    /// * `tasks`: An implementation of `PinFutContainer` used as task container for GBL fastboot to
    // /   schedule dynamically spawned async tasks.
    /// * `local`: An implementation of `LocalSession` which exchanges fastboot packet from platform
    ///   specific channels i.e. UX.
    /// * `usb`: An implementation of `GblUsbTransport` that represents USB channel.
    /// * `tcp`: An implementation of `GblTcpStream` that represents TCP channel.
    pub fn run<'b: 'c, 'c>(
        self,
        buffer_pool: &'b Shared<impl BufferPool>,
        tasks: impl PinFutContainer<'c> + 'c,
        local: Option<impl LocalSession>,
        usb: Option<impl GblUsbTransport>,
        tcp: Option<impl GblTcpStream>,
    ) where
        'a: 'c,
        'd: 'c,
    {
        *self.result =
            block_on(run_gbl_fastboot(self.ops, buffer_pool, tasks, local, usb, tcp, self.load));
    }

    /// Runs fastboot with N pre-allocated async worker tasks.
    ///
    /// Comparing  to `Self::run()`, this API   simplifies the input by handling the implementation of
    /// `BufferPool` and `PinFutContainer` internally . However it only supports up to N parallel
    /// tasks where N is determined at build time. The download buffer will be split into N chunks
    /// evenly.
    ///
    /// The choice of N depends on the level of parallelism the platform can support. For platform
    /// with `n` storage devices that can independently perform non-blocking IO, it will required
    /// `N = n + 1` in order to achieve parallel flashing to all storages plus a parallel download.
    /// However, it is common for partitions that need to be flashed to be on the same block device
    /// so flashing of them becomes sequential, in which case N can be smaller. Caller should take
    /// into consideration usage pattern for determining N. If platform only has one physical disk
    /// or does not expect disks to be parallelizable, a common choice is N=2 which allows
    /// downloading and flashing to be performed in parallel.
    pub fn run_n<const N: usize>(
        self,
        download: &mut [u8],
        local: Option<impl LocalSession>,
        usb: Option<impl GblUsbTransport>,
        tcp: Option<impl GblTcpStream>,
    ) {
        if N < 1 {
            return self.run_n::<1>(download, local, usb, tcp);
        }
        // Splits into N download buffers.
        let mut arr: [_; N] = from_fn(|_| Default::default());
        for (i, v) in download.chunks_exact_mut(download.len() / N).enumerate() {
            arr[i] = v;
        }
        let bufs = &mut arr[..];
        *self.result =
            block_on(run_gbl_fastboot_stack::<N>(self.ops, bufs, local, usb, tcp, self.load));
    }
}

/// Runs full Android bootloader bootflow before kernel handoff.
///
/// The API performs slot selection, handles boot mode, fastboot and loads and verifies Android from
/// disk.
///
/// # Args:
///
/// * `ops`: An implementation of `GblOps`.
/// * `load`: Buffer for loading various Android images.
/// * `run_fastboot`: A closure for running GBL fastboot. The closure is passed a
///   `GblFastbootEntry` type which provides methods for running GBL fastboot. The caller is
///   responsible for preparing the required inputs and calling the method in the closure. See
///   `GblFastbootEntry` for more details.
///
/// On success, returns a tuple of slices corresponding to `(ramdisk, FDT, kernel, unused)`
pub fn android_main<'a, 'b, 'c, G: GblOps<'a, 'b>>(
    ops: &mut G,
    load: &'c mut [u8],
    run_fastboot: impl FnOnce(GblFastbootEntry<'_, G>),
) -> Result<(&'c mut [u8], &'c mut [u8], &'c mut [u8], &'c mut [u8])> {
    let (bcb_buffer, _) = load
        .split_at_mut_checked(BootloaderMessage::SIZE_BYTES)
        .ok_or(Error::BufferTooSmall(Some(BootloaderMessage::SIZE_BYTES)))
        .inspect_err(|e| gbl_println!(ops, "Buffer too small for reading misc. {e}"))?;
    ops.read_from_partition_sync("misc", 0, bcb_buffer)
        .inspect_err(|e| gbl_println!(ops, "Failed to read misc partition {e}"))?;
    let bcb = BootloaderMessage::from_bytes_ref(bcb_buffer)
        .inspect_err(|e| gbl_println!(ops, "Failed to parse bootloader messgae {e}"))?;
    let boot_mode = bcb
        .boot_mode()
        .inspect_err(|e| gbl_println!(ops, "Failed to parse BCB boot mode {e}. Ignored"))
        .unwrap_or(AndroidBootMode::Normal);
    gbl_println!(ops, "Boot mode from BCB: {}", boot_mode);

    // Checks platform reboot reason.
    let reboot_reason = ops
        .get_reboot_reason()
        .inspect_err(|e| {
            gbl_println!(ops, "Failed to get reboot reason from platform: {e}. Ignored.")
        })
        .unwrap_or(RebootReason::Normal);
    gbl_println!(ops, "Reboot reason from platform: {reboot_reason:?}");

    // Checks and enters fastboot.
    let result = &mut Default::default();
    if matches!(reboot_reason, RebootReason::Bootloader)
        || matches!(boot_mode, AndroidBootMode::BootloaderBootOnce)
        || ops
            .should_stop_in_fastboot()
            .inspect_err(|e| {
                gbl_println!(ops, "Warning: error while checking fastboot trigger ({:?})", e);
                gbl_println!(ops, "Ignoring error and continuing with normal boot");
            })
            .unwrap_or(false)
    {
        gbl_println!(ops, "Entering fastboot mode...");
        run_fastboot(GblFastbootEntry { ops, load: &mut load[..], result });
        gbl_println!(ops, "Leaving fastboot mode...");
    }

    // Checks if "fastboot boot" has loaded an android image.
    match &result.loaded_image_info {
        Some(LoadedImageInfo::Android { .. }) => {
            gbl_println!(ops, "Booting from \"fastboot boot\"");
            return Ok(result.split_loaded_android(load).unwrap());
        }
        _ => {}
    }

    // Checks whether fastboot has set a different active slot. Reboot if it does.
    let slot_suffix = get_boot_slot(ops, true)?;
    if result.last_set_active_slot.unwrap_or(slot_suffix) != slot_suffix {
        gbl_println!(ops, "Active slot changed by \"fastboot set_active\". Reset..");
        ops.reboot();
        return Err(Error::UnexpectedReturn.into());
    }

    // Currently we assume slot suffix only takes value within 'a' to 'z'. Revisit if this
    // is not the case.
    //
    // It's a little awkward to convert suffix char to integer which will then be converted
    // back to char by the API. Consider passing in the char bytes directly.
    let slot_idx = (u64::from(slot_suffix) - u64::from('a')).try_into().unwrap();

    let is_recovery = matches!(reboot_reason, RebootReason::Recovery)
        || matches!(boot_mode, AndroidBootMode::Recovery);
    android_load_verify_fixup(ops, slot_idx, is_recovery, load)
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::{
        fastboot::test::{make_expected_usb_out, SharedTestListener, TestLocalSession},
        gbl_avb::state::KeyValidationStatus,
        ops::test::{slot, FakeGblOps, FakeGblOpsStorage},
        tests::AlignedBuffer,
    };
    use load::tests::{
        check_ramdisk, make_expected_bootconfig, read_test_data, read_test_data_as_str,
        AvbResultBootconfigBuilder, MakeExpectedBootconfigInclude, TEST_DEFAULT_BUILD_ID,
        TEST_PUBLIC_KEY_DIGEST, TEST_VENDOR_BOOTCONFIG,
    };
    use std::{collections::HashMap, ffi::CString};

    const TEST_ROLLBACK_INDEX_LOCATION: usize = 1;

    /// Helper for testing `android_load_verify_fixup` given a partition layout, target slot and
    /// custom device tree.
    fn test_android_load_verify_fixup(
        slot: u8,
        partitions: &[(CString, String)],
        expected_kernel: &[u8],
        expected_ramdisk: &[u8],
        expected_bootconfig: &[u8],
        expected_bootargs: &str,
        expected_fdt_property: &[(&str, &CStr, Option<&[u8]>)],
    ) {
        let mut storage = FakeGblOpsStorage::default();
        for (part, file) in partitions {
            storage.add_raw_device(part, read_test_data(file));
        }
        let mut ops = FakeGblOps::new(&storage);
        ops.avb_ops.unlock_state = Ok(false);
        ops.avb_ops.rollbacks = HashMap::from([(TEST_ROLLBACK_INDEX_LOCATION, Ok(0))]);
        let mut out_color = None;
        let mut handler = |color,
                           _: Option<&CStr>,
                           _: Option<&[u8]>,
                           _: Option<&[u8]>,
                           _: Option<&[u8]>,
                           _: Option<&[u8]>,
                           _: Option<&[u8]>,
                           _: Option<&[u8]>| {
            out_color = Some(color);
            Ok(())
        };
        ops.avb_handle_verification_result = Some(&mut handler);
        ops.avb_key_validation_status = Some(Ok(KeyValidationStatus::Valid));

        let mut load_buffer = AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let (ramdisk, fdt, kernel, _) =
            android_load_verify_fixup(&mut ops, slot, false, &mut load_buffer).unwrap();
        assert_eq!(kernel, expected_kernel);
        check_ramdisk(ramdisk, expected_ramdisk, expected_bootconfig);

        let fdt = Fdt::new(fdt).unwrap();
        // "linux,initrd-start/end" are updated.
        assert_eq!(
            fdt.get_property("/chosen", c"linux,initrd-start").unwrap(),
            (ramdisk.as_ptr() as usize).to_be_bytes(),
        );
        assert_eq!(
            fdt.get_property("/chosen", c"linux,initrd-end").unwrap(),
            (ramdisk.as_ptr() as usize + ramdisk.len()).to_be_bytes(),
        );

        // Commandlines are updated.
        assert_eq!(
            CStr::from_bytes_until_nul(fdt.get_property("/chosen", c"bootargs").unwrap()).unwrap(),
            CString::new(expected_bootargs).unwrap().as_c_str(),
        );

        // Fixup is applied.
        assert_eq!(fdt.get_property("/chosen", c"fixup").unwrap(), &[1]);

        // Other FDT properties are as expected.
        for (path, property, res) in expected_fdt_property {
            assert_eq!(
                fdt.get_property(&path, &property).ok(),
                res.clone(),
                "{path}:{property:?} value doesn't match"
            );
        }
    }

    /// Helper for testing `android_load_verify_fixup` for v2 boot image or lower.
    fn test_android_load_verify_fixup_v2_or_lower(
        ver: u8,
        slot: char,
        additional_parts: &[(&CStr, &str)],
        additional_expected_fdt_properties: &[(&str, &CStr, Option<&[u8]>)],
    ) {
        let dtb =
            additional_parts.iter().any(|(name, _)| name.to_str().unwrap().starts_with("dtb_"));
        let dtbo =
            additional_parts.iter().any(|(name, _)| name.to_str().unwrap().starts_with("dtbo_"));
        let vbmeta = format!("vbmeta_v{ver}_{slot}.img");
        let mut parts: Vec<(CString, String)> = vec![
            (CString::new(format!("boot_{slot}")).unwrap(), format!("boot_v{ver}_{slot}.img")),
            (CString::new(format!("vbmeta_{slot}")).unwrap(), vbmeta.clone()),
        ];
        for (part, file) in additional_parts.iter().cloned() {
            parts.push((part.into(), file.into()));
        }

        test_android_load_verify_fixup(
            (u64::from(slot) - ('a' as u64)).try_into().unwrap(),
            &parts,
            &read_test_data(format!("kernel_{slot}.img")),
            &read_test_data(format!("generic_ramdisk_{slot}.img")),
            &make_expected_bootconfig(&vbmeta, slot, "",
                MakeExpectedBootconfigInclude {dtb, dtbo, ..Default::default() }
            ),
            "existing_arg_1=existing_val_1 existing_arg_2=existing_val_2 cmd_key_1=cmd_val_1,cmd_key_2=cmd_val_2",
            additional_expected_fdt_properties,
        )
    }

    #[test]
    fn test_android_load_verify_fixup_v0_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"dtb_slot", Some(b"a\0"))];
        // V0 image doesn't have built-in dtb. We need to provide from dtb partition.
        let parts = &[(c"dtb_a", "dtb_a.img")];
        test_android_load_verify_fixup_v2_or_lower(0, 'a', parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v0_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"dtb_slot", Some(b"a\0")),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a", "dtbo_a.img"), (c"dtb_a", "dtb_a.img")];
        test_android_load_verify_fixup_v2_or_lower(0, 'a', parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v0_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"dtb_slot", Some(b"b\0"))];
        let parts = &[(c"dtb_b", "dtb_b.img")];
        test_android_load_verify_fixup_v2_or_lower(0, 'b', parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v0_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"dtb_slot", Some(b"b\0")),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b", "dtbo_b.img"), (c"dtb_b", "dtb_b.img")];
        test_android_load_verify_fixup_v2_or_lower(0, 'b', parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v1_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"dtb_slot", Some(b"a\0"))];
        // V1 image doesn't have built-in dtb. We need to provide from dtb partition.
        let parts = &[(c"dtb_a", "dtb_a.img")];
        test_android_load_verify_fixup_v2_or_lower(1, 'a', parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v1_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"dtb_slot", Some(b"a\0")),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a", "dtbo_a.img"), (c"dtb_a", "dtb_a.img")];
        test_android_load_verify_fixup_v2_or_lower(1, 'a', parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v1_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"dtb_slot", Some(b"b\0"))];
        let parts = &[(c"dtb_b", "dtb_b.img")];
        test_android_load_verify_fixup_v2_or_lower(1, 'b', parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v1_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"dtb_slot", Some(b"b\0")),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b", "dtbo_b.img"), (c"dtb_b", "dtb_b.img")];
        test_android_load_verify_fixup_v2_or_lower(1, 'b', parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v2_slot_a() {
        // V2 image has built-in dtb. We don't need to provide custom device tree.
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        test_android_load_verify_fixup_v2_or_lower(2, 'a', &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v2_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a".into(), "dtbo_a.img".into())];
        test_android_load_verify_fixup_v2_or_lower(2, 'a', parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v2_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        test_android_load_verify_fixup_v2_or_lower(2, 'b', &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v2_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b".into(), "dtbo_b.img".into())];
        test_android_load_verify_fixup_v2_or_lower(2, 'b', parts, fdt_prop);
    }

    /// Common helper for testing `android_load_verify_fixup` for v3/v4 boot image.
    fn test_android_load_verify_fixup_v3_or_v4(
        slot: char,
        partitions: &[(CString, String)],
        vbmeta_file: &str,
        expected_vendor_bootconfig: &str,
        additional_expected_fdt_properties: &[(&str, &CStr, Option<&[u8]>)],
    ) {
        let dtbo = partitions
            .iter()
            .any(|(name, _)| name.clone().into_string().unwrap().starts_with("dtbo_"));
        let expected_ramdisk = [
            read_test_data(format!("vendor_ramdisk_{slot}.img")),
            read_test_data(format!("generic_ramdisk_{slot}.img")),
        ]
        .concat();
        test_android_load_verify_fixup(
            (u64::from(slot) - ('a' as u64)).try_into().unwrap(),
            &partitions,
            &read_test_data(format!("kernel_{slot}.img")),
            &expected_ramdisk,
            &make_expected_bootconfig(&vbmeta_file, slot, expected_vendor_bootconfig,
                MakeExpectedBootconfigInclude { dtbo, dtb: false, ..Default::default() },
                ),
            "existing_arg_1=existing_val_1 existing_arg_2=existing_val_2 cmd_key_1=cmd_val_1,cmd_key_2=cmd_val_2 cmd_vendor_key_1=cmd_vendor_val_1,cmd_vendor_key_2=cmd_vendor_val_2",
            additional_expected_fdt_properties,
        )
    }

    /// Helper for testing `android_load_verify_fixup` for v3/v4 boot image without init_boot.
    fn test_android_load_verify_fixup_v3_or_v4_no_init_boot(
        boot_ver: u32,
        vendor_ver: u32,
        slot: char,
        expected_vendor_bootconfig: &str,
        additional_parts: &[(CString, String)],
        additional_expected_fdt_properties: &[(&str, &CStr, Option<&[u8]>)],
    ) {
        let vbmeta = format!("vbmeta_v{boot_ver}_v{vendor_ver}_{slot}.img");
        let mut parts: Vec<(CString, String)> = vec![
            (CString::new(format!("boot_{slot}")).unwrap(), format!("boot_v{boot_ver}_{slot}.img")),
            (
                CString::new(format!("vendor_boot_{slot}")).unwrap(),
                format!("vendor_boot_v{vendor_ver}_{slot}.img"),
            ),
            (CString::new(format!("vbmeta_{slot}")).unwrap(), vbmeta.clone()),
        ];
        parts.extend_from_slice(additional_parts);
        test_android_load_verify_fixup_v3_or_v4(
            slot,
            &parts,
            &vbmeta,
            expected_vendor_bootconfig,
            additional_expected_fdt_properties,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_no_init_boot_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(3, 3, 'a', "", &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_no_init_boot_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a".into(), "dtbo_a.img".into())];
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(3, 3, 'a', "", parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_no_init_boot_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(3, 3, 'a', "", &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_no_init_boot_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b".into(), "dtbo_b.img".into())];
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(3, 3, 'b', "", parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_no_init_boot_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(4, 3, 'a', "", &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_no_init_boot_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a".into(), "dtbo_a.img".into())];
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(4, 3, 'a', "", parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_no_init_boot_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(4, 3, 'a', "", &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_no_init_boot_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b".into(), "dtbo_b.img".into())];
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(4, 3, 'b', "", parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_no_init_boot_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(3, 4, 'a', config, &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_no_init_boot_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a".into(), "dtbo_a.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(3, 4, 'a', config, parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_no_init_boot_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(3, 4, 'a', config, &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_no_init_boot_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b".into(), "dtbo_b.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(3, 4, 'b', config, parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_no_init_boot_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(4, 4, 'a', config, &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_no_init_boot_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a".into(), "dtbo_a.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(4, 4, 'a', config, parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_no_init_boot_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(4, 4, 'a', config, &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_no_init_boot_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b".into(), "dtbo_b.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(4, 4, 'b', config, parts, fdt_prop);
    }

    /// Helper for testing `android_load_verify_fixup` for v3/v4 boot image with init_boot.
    fn test_android_load_verify_fixup_v3_or_v4_init_boot(
        boot_ver: u32,
        vendor_ver: u32,
        slot: char,
        expected_vendor_bootconfig: &str,
        additional_parts: &[(CString, String)],
        additional_expected_fdt_properties: &[(&str, &CStr, Option<&[u8]>)],
    ) {
        let vbmeta = format!("vbmeta_v{boot_ver}_v{vendor_ver}_init_boot_{slot}.img");
        let mut parts: Vec<(CString, String)> = vec![
            (
                CString::new(format!("boot_{slot}")).unwrap(),
                format!("boot_no_ramdisk_v{boot_ver}_{slot}.img"),
            ),
            (
                CString::new(format!("vendor_boot_{slot}")).unwrap(),
                format!("vendor_boot_v{vendor_ver}_{slot}.img"),
            ),
            (CString::new(format!("init_boot_{slot}")).unwrap(), format!("init_boot_{slot}.img")),
            (CString::new(format!("vbmeta_{slot}")).unwrap(), vbmeta.clone()),
        ];
        parts.extend_from_slice(additional_parts);
        test_android_load_verify_fixup_v3_or_v4(
            slot,
            &parts,
            &vbmeta,
            expected_vendor_bootconfig,
            additional_expected_fdt_properties,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_init_boot_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 3, 'a', "", &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_init_boot_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a".into(), "dtbo_a.img".into())];
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 3, 'a', "", parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_init_boot_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 3, 'a', "", &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_init_boot_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b".into(), "dtbo_b.img".into())];
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 3, 'b', "", parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_init_boot_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 3, 'a', "", &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_init_boot_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a".into(), "dtbo_a.img".into())];
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 3, 'a', "", parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_init_boot_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 3, 'a', "", &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_init_boot_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b".into(), "dtbo_b.img".into())];
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 3, 'b', "", parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_init_boot_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 4, 'a', config, &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_init_boot_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a".into(), "dtbo_a.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 4, 'a', config, parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_init_boot_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 4, 'a', config, &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_init_boot_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b".into(), "dtbo_b.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 4, 'b', config, parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_init_boot_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 4, 'a', config, &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_init_boot_dtbo_slot_a() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ];
        let parts = &[(c"dtbo_a".into(), "dtbo_a.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 4, 'a', config, parts, fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_init_boot_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[("/chosen", c"builtin", Some(&[1]))];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 4, 'a', config, &[], fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_init_boot_dtbo_slot_b() {
        let fdt_prop: &[(&str, &CStr, Option<&[u8]>)] = &[
            ("/chosen", c"builtin", Some(&[1])),
            ("/chosen", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ];
        let parts = &[(c"dtbo_b".into(), "dtbo_b.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 4, 'b', config, parts, fdt_prop);
    }

    /// Helper for checking V2 image loaded from slot A and in normal mode.
    pub(crate) fn checks_loaded_v2_slot_a_normal_mode(ramdisk: &[u8], kernel: &[u8]) {
        let expected_bootconfig = AvbResultBootconfigBuilder::new()
            .vbmeta_size(read_test_data("vbmeta_v2_a.img").len())
            .digest(read_test_data_as_str("vbmeta_v2_a.digest.txt").strip_suffix("\n").unwrap())
            .partition_digest(
                "boot",
                read_test_data_as_str("vbmeta_v2_a.boot.digest.txt").strip_suffix("\n").unwrap(),
            )
            .public_key_digest(TEST_PUBLIC_KEY_DIGEST)
            .extra("androidboot.force_normal_boot=1\n")
            .extra(format!("androidboot.slot_suffix=_a\n"))
            .extra("androidboot.gbl.version=0\n")
            .extra(format!("androidboot.gbl.build_number={TEST_DEFAULT_BUILD_ID}\n"))
            .extra(FakeGblOps::GBL_TEST_BOOTCONFIG)
            .build();
        check_ramdisk(ramdisk, &read_test_data("generic_ramdisk_a.img"), &expected_bootconfig);
        assert_eq!(kernel, read_test_data("kernel_a.img"));
    }

    /// Helper for checking V2 image loaded from slot A and in recovery mode.
    fn checks_loaded_v2_slot_a_recovery_mode(ramdisk: &[u8], kernel: &[u8]) {
        let expected_bootconfig = AvbResultBootconfigBuilder::new()
            .vbmeta_size(read_test_data("vbmeta_v2_a.img").len())
            .digest(read_test_data_as_str("vbmeta_v2_a.digest.txt").strip_suffix("\n").unwrap())
            .partition_digest(
                "boot",
                read_test_data_as_str("vbmeta_v2_a.boot.digest.txt").strip_suffix("\n").unwrap(),
            )
            .public_key_digest(TEST_PUBLIC_KEY_DIGEST)
            .extra(format!("androidboot.slot_suffix=_a\n"))
            .extra("androidboot.gbl.version=0\n")
            .extra(format!("androidboot.gbl.build_number={TEST_DEFAULT_BUILD_ID}\n"))
            .extra(FakeGblOps::GBL_TEST_BOOTCONFIG)
            .build();
        check_ramdisk(ramdisk, &read_test_data("generic_ramdisk_a.img"), &expected_bootconfig);
        assert_eq!(kernel, read_test_data("kernel_a.img"));
    }

    /// Helper for getting default FakeGblOps for tests.
    pub(crate) fn default_test_gbl_ops(storage: &FakeGblOpsStorage) -> FakeGblOps {
        let mut ops = FakeGblOps::new(&storage);
        ops.avb_ops.unlock_state = Ok(false);
        ops.avb_ops.rollbacks = HashMap::from([(TEST_ROLLBACK_INDEX_LOCATION, Ok(0))]);
        ops.avb_key_validation_status = Some(Ok(KeyValidationStatus::Valid));
        ops.current_slot = Some(Ok(slot('a')));
        ops.reboot_reason = Some(Ok(RebootReason::Normal));
        ops
    }

    #[test]
    fn test_android_load_verify_fixup_recovery_mode() {
        // Recovery mode is specified by the absence of bootconfig arg
        // "androidboot.force_normal_boot=1\n" and therefore independent of image versions. We can
        // pick any image version for test. Use v2 for simplicity.
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("vbmeta_v2_a.img"));

        let mut ops = default_test_gbl_ops(&storage);
        let mut load_buffer = AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let (ramdisk, _, kernel, _) =
            android_load_verify_fixup(&mut ops, 0, true, &mut load_buffer).unwrap();
        checks_loaded_v2_slot_a_recovery_mode(ramdisk, kernel)
    }

    #[test]
    fn test_android_main_bcb_normal_mode() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        let mut load_buffer = AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let (ramdisk, _, kernel, _) = android_main(&mut ops, &mut load_buffer, |_| {}).unwrap();
        checks_loaded_v2_slot_a_normal_mode(ramdisk, kernel)
    }

    #[test]
    fn test_android_main_bcb_recovery_mode() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        ops.write_to_partition_sync("misc", 0, &mut b"boot-recovery".to_vec()).unwrap();
        let mut load_buffer = AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let (ramdisk, _, kernel, _) = android_main(&mut ops, &mut load_buffer, |_| {}).unwrap();
        checks_loaded_v2_slot_a_recovery_mode(ramdisk, kernel)
    }

    #[test]
    fn test_android_main_reboot_reason_recovery_mode() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        ops.reboot_reason = Some(Ok(RebootReason::Recovery));
        let mut load_buffer = AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let (ramdisk, _, kernel, _) = android_main(&mut ops, &mut load_buffer, |_| {}).unwrap();
        checks_loaded_v2_slot_a_recovery_mode(ramdisk, kernel)
    }

    /// Helper for checking V2 image loaded from slot B and in normal mode.
    pub(crate) fn checks_loaded_v2_slot_b_normal_mode(ramdisk: &[u8], kernel: &[u8]) {
        let expected_bootconfig = AvbResultBootconfigBuilder::new()
            .vbmeta_size(read_test_data("vbmeta_v2_b.img").len())
            .digest(read_test_data_as_str("vbmeta_v2_b.digest.txt").strip_suffix("\n").unwrap())
            .partition_digest(
                "boot",
                read_test_data_as_str("vbmeta_v2_b.boot.digest.txt").strip_suffix("\n").unwrap(),
            )
            .public_key_digest(TEST_PUBLIC_KEY_DIGEST)
            .extra("androidboot.force_normal_boot=1\n")
            .extra(format!("androidboot.slot_suffix=_b\n"))
            .extra("androidboot.gbl.version=0\n")
            .extra(format!("androidboot.gbl.build_number={TEST_DEFAULT_BUILD_ID}\n"))
            .extra(FakeGblOps::GBL_TEST_BOOTCONFIG)
            .build();
        check_ramdisk(ramdisk, &read_test_data("generic_ramdisk_b.img"), &expected_bootconfig);
        assert_eq!(kernel, read_test_data("kernel_b.img"));
    }

    #[test]
    fn test_android_main_slotted_gbl_slot_a() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        let mut load_buffer = AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let (ramdisk, _, kernel, _) = android_main(&mut ops, &mut load_buffer, |_| {}).unwrap();
        assert_eq!(ops.mark_boot_attempt_called, 0);
        checks_loaded_v2_slot_a_normal_mode(ramdisk, kernel)
    }

    #[test]
    fn test_android_main_slotless_gbl_slot_a() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        ops.current_slot = Some(Err(Error::Unsupported));
        ops.next_slot = Some(Ok(slot('a')));
        let mut load_buffer = AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let (ramdisk, _, kernel, _) = android_main(&mut ops, &mut load_buffer, |_| {}).unwrap();
        assert_eq!(ops.mark_boot_attempt_called, 1);
        checks_loaded_v2_slot_a_normal_mode(ramdisk, kernel)
    }

    #[test]
    fn test_android_main_slotted_gbl_slot_b() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_b", read_test_data("boot_v2_b.img"));
        storage.add_raw_device(c"vbmeta_b", read_test_data("vbmeta_v2_b.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        ops.current_slot = Some(Ok(slot('b')));

        let mut load_buffer = AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let (ramdisk, _, kernel, _) = android_main(&mut ops, &mut load_buffer, |_| {}).unwrap();
        assert_eq!(ops.mark_boot_attempt_called, 0);
        checks_loaded_v2_slot_b_normal_mode(ramdisk, kernel)
    }

    #[test]
    fn test_android_main_slotless_gbl_slot_b() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_b", read_test_data("boot_v2_b.img"));
        storage.add_raw_device(c"vbmeta_b", read_test_data("vbmeta_v2_b.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        ops.current_slot = Some(Err(Error::Unsupported));
        ops.next_slot = Some(Ok(slot('b')));
        let mut load_buffer = AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let (ramdisk, _, kernel, _) = android_main(&mut ops, &mut load_buffer, |_| {}).unwrap();
        assert_eq!(ops.mark_boot_attempt_called, 1);
        checks_loaded_v2_slot_b_normal_mode(ramdisk, kernel);
    }

    #[test]
    fn test_android_main_unsupported_slot_default_to_a() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        ops.current_slot = Some(Err(Error::Unsupported));
        ops.next_slot = Some(Err(Error::Unsupported));
        let mut load_buffer = AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let (ramdisk, _, kernel, _) = android_main(&mut ops, &mut load_buffer, |_| {}).unwrap();
        checks_loaded_v2_slot_a_normal_mode(ramdisk, kernel)
    }

    /// Helper for testing that fastboot mode is triggered.
    fn test_fastboot_is_triggered<'a, 'b>(ops: &mut impl GblOps<'a, 'b>) {
        let listener: SharedTestListener = Default::default();
        let mut load_buffer = AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let (ramdisk, _, kernel, _) = android_main(ops, &mut load_buffer, |fb| {
            listener.add_usb_input(b"getvar:max-fetch-size");
            listener.add_usb_input(b"continue");
            fb.run_n::<2>(
                &mut vec![0u8; 256 * 1024],
                Some(&mut TestLocalSession::default()),
                Some(&listener),
                Some(&listener),
            )
        })
        .unwrap();

        assert_eq!(
            listener.usb_out_queue(),
            make_expected_usb_out(
                &[b"OKAY0xffffffffffffffff", b"INFOSyncing storage...", b"OKAY",]
            ),
            "\nActual USB output:\n{}",
            listener.dump_usb_out_queue()
        );

        checks_loaded_v2_slot_a_normal_mode(ramdisk, kernel);
    }

    #[test]
    fn test_android_main_enter_fastboot_via_bcb() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);
        let mut ops = default_test_gbl_ops(&storage);
        ops.write_to_partition_sync("misc", 0, &mut b"bootonce-bootloader".to_vec()).unwrap();
        test_fastboot_is_triggered(&mut ops);
    }

    #[test]
    fn test_android_main_enter_fastboot_via_reboot_reason() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);
        let mut ops = default_test_gbl_ops(&storage);
        ops.reboot_reason = Some(Ok(RebootReason::Bootloader));
        test_fastboot_is_triggered(&mut ops);
    }

    #[test]
    fn test_android_main_enter_fastboot_via_should_stop_in_fastboot() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);
        let mut ops = default_test_gbl_ops(&storage);
        ops.stop_in_fastboot = Some(Ok(true));
        test_fastboot_is_triggered(&mut ops);
    }

    #[test]
    fn test_android_main_fastboot_boot() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"vbmeta_a", read_test_data("vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);
        let mut ops = default_test_gbl_ops(&storage);
        ops.stop_in_fastboot = Some(Ok(true));
        ops.current_slot = Some(Ok(slot('a')));

        let listener: SharedTestListener = Default::default();
        let mut load_buffer = AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let (ramdisk, _, kernel, _) = android_main(&mut ops, &mut load_buffer, |fb| {
            let data = read_test_data(format!("boot_v2_a.img"));
            listener.add_usb_input(format!("download:{:#x}", data.len()).as_bytes());
            listener.add_usb_input(&data);
            listener.add_usb_input(b"boot");
            listener.add_usb_input(b"continue");
            fb.run_n::<2>(
                &mut vec![0u8; 256 * 1024],
                Some(&mut TestLocalSession::default()),
                Some(&listener),
                Some(&listener),
            )
        })
        .unwrap();

        assert_eq!(
            listener.usb_out_queue(),
            make_expected_usb_out(&[b"DATA00004000", b"OKAY", b"OKAYboot_command",]),
            "\nActual USB output:\n{}",
            listener.dump_usb_out_queue()
        );

        checks_loaded_v2_slot_a_normal_mode(ramdisk, kernel);
    }

    #[test]
    fn test_android_main_reboot_if_set_active_to_different_slot() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);
        let mut ops = default_test_gbl_ops(&storage);
        ops.stop_in_fastboot = Some(Ok(true));
        ops.current_slot = Some(Ok(slot('a')));

        let listener: SharedTestListener = Default::default();
        let mut load_buffer = AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        assert_eq!(
            android_main(&mut ops, &mut load_buffer, |fb| {
                listener.add_usb_input(b"set_active:b");
                listener.add_usb_input(b"continue");
                fb.run_n::<2>(
                    &mut vec![0u8; 256 * 1024],
                    Some(&mut TestLocalSession::default()),
                    Some(&listener),
                    Some(&listener),
                )
            })
            .unwrap_err(),
            Error::UnexpectedReturn.into()
        );

        assert_eq!(
            listener.usb_out_queue(),
            make_expected_usb_out(&[b"OKAY", b"INFOSyncing storage...", b"OKAY",]),
            "\nActual USB output:\n{}",
            listener.dump_usb_out_queue()
        );
    }
}
