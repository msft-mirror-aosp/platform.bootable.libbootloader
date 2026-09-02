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
    constants::FDT_ALIGNMENT,
    device_tree::{DtSourceLocation, SelectedDtComponentsMetadata},
    fastboot::{
        boot_items::{BootItem, BootItemContainer},
        run_gbl_fastboot, run_gbl_fastboot_stack, split_loaded_android, GblFastbootResult,
        GblFbData, GblGenericTransport, GblTcpStream, LoadedImageInfo, PinFutContainer,
    },
    gbl_avb::{ArrayMaxParts, ArrayMaxSpecializedParts, LoadPartition, Verification},
    gbl_println,
    metrics::{FirmwareVersionMetrics, GblMetrics, GblTime},
    misc::{read_bootloader_message_to, write_bootloader_message},
    ops::{OneShotBootMode, PartitionBuffer},
    slots::{slotted_part, Slot},
    GblOps, IntegrationError, Result,
};
use arrayvec::ArrayVec;
use bootparams::{bootconfig::BootConfigBuilder, entry::CommandlineParser};
use cfg_if::cfg_if;
use core::{ffi::CStr, fmt::Write, mem::take, ops::Range};
use fdt::Fdt;
use gbl_async::block_on;
use libbuild_number::{format_build_fingerprint, format_build_vcs_info, BUILD_NUMBER, VERSION};
use liberror::Error;
use libutils::{aligned_subslice, buffer_pool::BufferPool, shared::Shared};
use misc::AndroidBootMode;

mod avf;
use avf::{avf_fixup_host_dt, avf_update_bootconfig, inject_vmdtbo};

pub(crate) mod hasher;

pub mod device_tree;
use device_tree::{fdt_build_bootargs, fdt_propagate_random, fdt_select, PROP_BOOTARGS};

pub mod vboot;
pub use vboot::{avb_verify_slot, PartitionsToVerify};

pub(crate) mod kernel;
pub(crate) mod load;
#[cfg(feature = "fuchsia")]
pub(crate) use load::get_kernel;
use load::{android_load_verified, BootBufferLoader};

/// A helper to convert a bytes slice containing a null-terminated string to `str`
fn cstr_bytes_to_str(data: &[u8]) -> core::result::Result<&str, Error> {
    Ok(CStr::from_bytes_until_nul(data)?.to_str()?)
}

/// The set of partitions we always verify with libavb for Android boot.
pub const STANDARD_PARTITIONS: &[LoadPartition] = &[
    // LINT.IfChange(always_verify_partitions)
    LoadPartition::Boot,
    LoadPartition::VendorBoot,
    LoadPartition::VendorKernelBoot,
    LoadPartition::InitBoot,
    LoadPartition::Dtb,
    LoadPartition::Dtbo,
    LoadPartition::Pvmfw,
    // LINT.ThenChange(/gbl/docs/gbl_efi_avb_protocol.md:always_verify_partitions)
];

/// Loads Android images from the given slot on disk and fixes up bootconfig, commandline, and FDT.
///
/// On success, returns a tuple of (ramdisk, fdt, kernel, unused buffer).
pub fn android_load_verify_fixup<'a, 'b>(
    ops: &mut impl GblOps<'b>,
    slot: Option<Slot>,
    is_recovery: bool,
    boot_buffer: BootBuffer<'a>,
) -> Result<(&'a [u8], &'a [u8], &'a [u8], &'a mut [u8])> {
    let mut loader = BootBufferLoader::new(boot_buffer);

    // Get the list of device-specific partitions to verify.
    let requested_partitions: ArrayMaxSpecializedParts<_> =
        ops.avb_read_partition_attributes()?.filter(|p| p.verification.is_some()).collect();
    gbl_println!(
        ops,
        "FW requested {} extra partitions to be loaded/verified",
        requested_partitions.len()
    );

    let mut partitions: ArrayMaxParts<(LoadPartition, Option<PartitionBuffer<_>>)> =
        ArrayMaxParts::new();

    // We need to first store all buffers and then create slices from them. Because they are
    // opaque objects that need to be dereferenced to yield slices.
    for partition in STANDARD_PARTITIONS
        .iter()
        .copied()
        .chain(requested_partitions.iter().map(|p| LoadPartition::PlatformSpecific(&p)))
    {
        let b = match ops.get_partition_buffer(partition) {
            Ok(b) => {
                let info = match b {
                    PartitionBuffer::Preloaded(_) => "preloaded",
                    PartitionBuffer::Designated(_) => "designated load",
                };
                gbl_println!(ops, "Found {info} buffer for {:?}", partition.name());
                Some(b)
            }
            Err(Error::NotFound) => None,
            Err(e) => return Err(e.into()),
        };
        partitions
            .try_push((partition, b))
            .map_err(|_| Error::TooManyPartitions(partitions.len()))?;
    }

    let mut partitions_to_verify = PartitionsToVerify::default();
    // Adds partitions for verification. AVB will only verify partitions that contain a hash
    // descriptor in vbmeta. Missing firmware-specific partitions will cause a verification
    // failure on locked devices.
    for (partition, buffer) in partitions.iter_mut() {
        match buffer {
            Some(buffer) => partitions_to_verify.try_push_preloaded(*partition, buffer)?,
            None => {
                // TODO(b/337846185): Android partitions listed in vbmeta must be loaded or boot
                // fails, so this size check should be removed. For now, it's kept to allow reusing
                // the same vbmeta in unit tests without providing all partitions.
                if partition.verification() == Verification::Required
                    || ops
                        .partition_size(&slotted_part(partition.name(), slot.map(|s| s.suffix)))?
                        .is_some()
                {
                    partitions_to_verify.try_push(*partition)?
                }
            }
        }
    }

    let start = ops.get_time().and_then(|t| t.current_tick().ok());

    #[allow(unused_mut)]
    let mut res = avb_verify_slot(ops, slot, &mut partitions_to_verify);
    #[cfg(feature = "gbl_dev")]
    {
        use crate::android_boot::vboot::avb_fake_verify_slot;

        // AVB failed, try to use fake avb flow since we're in dev flow. Fallback locking state to
        // unlocked since inside dev GBL flow.
        if res.is_err() && ops.avb_read_device_status().map(|s| s.is_unlocked).unwrap_or(true) {
            gbl_println!(
                ops,
                "AVB failed with: {}. Dev flavor of GBL, so trying fake AVB flow.",
                res.as_ref().err().unwrap()
            );

            // Needs to drop explicitly so that `partitions_to_verify` can be used.
            drop(res);
            res = avb_fake_verify_slot(ops, slot, &mut partitions_to_verify);
        }
    }

    if let Some(start) = start
        && let Some(delta) = ops.get_time().and_then(|t| t.elapsed_ticks(start).ok())
        && let Some(mut metrics) = ops.get_metrics()
    {
        metrics.add_avb_ticks(delta);
    }

    let (verify_data, status, unlocked) = res?;
    // Boot items are added from fastboot. It shall only be used when device is unlocked because it
    // effectively modifies boot images. The lock/unlock state should be the same one used by
    // libavb.
    let boot_items = unlocked.then_some(loader.take_boot_items());

    let images = android_load_verified(ops, slot, unlocked, is_recovery, &verify_data)?;

    let kernel_attrs = loader.kernel_load(ops, images.kernel)?;
    let mut pvmfw = match images.pvmfw.is_empty() {
        true => None,
        _ => Some(loader.pvmfw_load(
            ops,
            images.pvmfw,
            &kernel_attrs,
            &verify_data,
            unlocked,
            is_recovery,
            status.color,
            images.dtbo,
        )?),
    };
    loader.ramdisk_load(&images.ramdisks[..])?;

    let kernel_len = loader.kernel_sz;
    let ramdisk_len = loader.ramdisk_sz;

    // Updates bootconfig with AVB results and GBL metadata.

    let bootconfig_buf = loader.expand_bootconfig_buffer()?;
    let mut bootconfig_builder = BootConfigBuilder::new(bootconfig_buf)?;

    // Emit GBL-generated configs first to ensure they take precedence over any duplicates in
    // the commandline passthroughs (due to first-match resolution).
    bootconfig_builder.add_item("androidboot.verifiedbootstate", status.color)?;
    if !is_recovery {
        bootconfig_builder.add_item("androidboot.force_normal_boot", 1)?;
    }
    if let Some(s) = slot {
        bootconfig_builder
            .add_item("androidboot.slot_suffix", format_args!("_{}", s.suffix.as_char()))?;
    }
    add_android_gbl_bootconfig(&mut bootconfig_builder, ops.get_fw_api_level().ok())?;

    // Copy bootconfig items from the avb commandline with filtering to prevent chained vbmeta
    // blobs from trying to override or shadow properties we control.
    //
    // libavb doesn't indicate which commandline descriptors came from which blob, it just mashes
    // them all together, so we treat this whole commandline input as less-trusted.
    vbmeta_cmdline_to_bootconfig(
        ops,
        verify_data.cmdline().to_str().unwrap(),
        &mut bootconfig_builder,
    )?;

    // Add bootconfig from vendor_boot.
    //
    // This does not need to be filtered because we know it's coming from the vendor boot image
    // which is a higher level of trust than arbitrary chained vbmeta blobs; if it's compromised
    // then we've already lost control of the ramdisk so the bootconfig params are irrelevant.
    bootconfig_builder.add_raw_lines_with(|_, out| {
        out.get_mut(..images.vendor_bootconfig.len())
            .ok_or(Error::BufferTooSmall(Some(images.vendor_bootconfig.len())))?
            .clone_from_slice(images.vendor_bootconfig);
        Ok(images.vendor_bootconfig.len())
    })?;

    let bootconfig_sz = bootconfig_builder.config_bytes().len();
    loader.set_bootconfig_size(bootconfig_sz);
    // Notes: We keep bootconfig in the ramdisk regardless of whether it is supported for simplicity
    // and in case device is using boot v3+vendor_boot v4 combination where Android 11 and
    // Android 12+ are indistinguishable.
    let bootconfig_supported = images.bootconfig_supported();

    // Fixes up FDT.

    let (designated_fdt, remains) = loader.get_fdt_and_general_unused_buffer()?;
    let (selected, remains) = fdt_select(ops, &images, remains)?;

    // Assembles DT in designated buffer if provided, otherwise allocates from `general` buffer.
    let fdt_load = designated_fdt.unwrap_or(aligned_subslice(remains, FDT_ALIGNMENT)?);
    let mut fdt = match &selected {
        Some(selected) => {
            let mut fdt = Fdt::new_from_init(&mut fdt_load[..], selected.base_dt.dt)?;
            gbl_println!(ops, "Applying {} overlays", selected.overlays.len());
            fdt.multioverlay_apply(selected.overlays.iter().map(|c| c.dt))?;
            gbl_println!(ops, "Overlays applied");
            fdt
        }
        // TODO(b/555762992): This is a stopgap that fakes an empty device tree so the existing
        // fixup path still runs. Drop it once the proper no-device-tree boot flow lands.
        #[cfg(target_arch = "x86_64")]
        None => {
            use crate::constants::KiB;
            gbl_println!(ops, "WARNING: Booting with a synthesized empty device tree");
            let sz = fdt_load.len().min(KiB!(64));
            Fdt::new_empty(&mut fdt_load[..sz])?
        }
        #[cfg(not(target_arch = "x86_64"))]
        None => unreachable!("fdt_select only returns None on x86_64"),
    };

    let overlays = selected.as_ref().map_or(&[][..], |v| &v.overlays[..]);
    let vmdtbo = selected.as_ref().and_then(|v| v.vmdtbo);

    // Builds the FDT commandline. Reserves 1024 bytes for separators and fixup.
    fdt_build_bootargs(
        ops,
        &mut fdt,
        &images,
        overlays.iter().map(|c| c.dt),
        boot_items.as_ref(),
        1024,
    )?;

    if let Some((reg, bin_sz)) = pvmfw.as_mut() {
        let total_size = match vmdtbo {
            Some(vmdtbo) => inject_vmdtbo(reg, *bin_sz, &kernel_attrs, vmdtbo.dt)?,
            None => reg.len(),
        };
        avf_fixup_host_dt(ops, &mut fdt, &reg[..total_size], *bin_sz, &verify_data)?;
    };

    let selected_metadata = selected.map(|v| v.into_metadata());

    // Notifies platform to process loaded partitions before final bootconfig and FDT fixup, so
    // that backend can add fixup items that depend on certain partition data.
    //
    // Need to explicitly releases the partition buffers for the backend to safely inspect, update
    // or release them.
    drop(images);
    drop(verify_data);
    drop(partitions_to_verify);
    drop(partitions);
    ops.sync_partition_buffer(false)?;

    fdt_propagate_random(ops, &mut fdt)?;

    // Backend FDT fixup.

    // Make sure we provide an actual device tree size, so FW can calculate amount of space
    // available for fixup.
    fdt.shrink_to_fit()?;
    // TODO(b/353272981): Handle buffer too small
    ops.fixup_device_tree(fdt.as_mut())?;
    fdt.shrink_to_fit()?;
    let fdt_ptr_range = fdt.as_ref()[..fdt.header_ref()?.actual_size()].as_ptr_range();
    loader.set_fdt_range(fdt_ptr_range);

    // Finalize and fixup bootconfig.
    let bootconfig_sz = finalize_bootconfig(
        ops,
        loader.expand_bootconfig_buffer()?,
        bootconfig_sz,
        pvmfw.is_some(),
        selected_metadata.as_ref(),
        boot_items,
    )?;
    loader.set_bootconfig_size(bootconfig_sz);
    let ramdisk_len = ramdisk_len + bootconfig_sz;

    // Finalizes FDT with ramdisk address and adds bootconfig as bootarg if it is not supported.
    loader.expand_fdt()?;
    let [ramdisk, fdt, _, _] = loader.splits();
    let fdt_sz = finalize_dt(ops, fdt, &ramdisk[..ramdisk_len], !bootconfig_supported)?;
    let fdt_range = fdt[..fdt_sz].as_ptr_range();
    loader.set_fdt_range(fdt_range);
    let [ramdisk, fdt, kernel, unused] = loader.into_splits();

    Ok((&ramdisk[..ramdisk_len], &fdt[..fdt_sz], &kernel[..kernel_len], unused))
}

/// Add gbl properties to be exported to android boot properties.
fn add_android_gbl_bootconfig(builder: &mut impl Write, fw_api_level: Option<u64>) -> Result<()> {
    writeln!(builder, "androidboot.gbl.version={VERSION}").map_err(Error::from)?;
    writeln!(builder, "androidboot.gbl.build_number={BUILD_NUMBER}").map_err(Error::from)?;
    writeln!(builder, "androidboot.gbl.fingerprint={}", format_build_fingerprint!())
        .map_err(Error::from)?;
    writeln!(builder, "androidboot.gbl.vcs={}", format_build_vcs_info!()).map_err(Error::from)?;
    // TODO(b/484066914): Error if this var is missing.
    if let Some(fw_api_level) = fw_api_level {
        writeln!(builder, "androidboot.gbl.fw.api_level={fw_api_level}").map_err(Error::from)?;
    }
    Ok(())
}

/// Validates and appends command line entries to bootconfig.
///
/// The validation prevents any entries which might attempt to modify existing values. The idea here
/// is that GBL has already added its bootconfig values e.g. `androidboot.verifiedbootstate`, and we
/// do not want vbmeta commandline properties to be able to override these entries.
///
/// It's difficult to get the validation exactly right because it depends on how the kernel and init
/// process the bootconfig, and they aren't always in agreement (for example init doesn't currently
/// handle quoting, but just splits on `\n` without considering quotes). To avoid dependencies on
/// specific implementation details, this function is overly cautious and prohibits some entries
/// that might technically be valid. This should be OK because more complicated bootconfigs can
/// still be specified in the boot images; this only filters parameters coming from vbmeta
/// commandline descriptors which should be very simple.
fn vbmeta_cmdline_to_bootconfig<'a>(
    ops: &mut impl GblOps<'a>,
    cmdline: &str,
    builder: &mut BootConfigBuilder,
) -> Result<()> {
    for entry in CommandlineParser::new(cmdline) {
        let entry = entry?;

        // For now, prohibit any use of `:=` or `+=`.
        //
        // There are some subtleties here and we mask out some technically valid entries:
        //   * foo=bar:=baz - valid, creates one item {"foo": "bar:=baz"}
        //   * foo=bar\nbaz:=qux - invalid, creates {"foo": "bar"} and overrides {"baz": "qux"}
        //   * foo="bar\nbaz:=qux" - valid, creates one item {"foo": "bar\nbaz:=qux"}
        //     * note: _not_ valid for init, which doesn't properly escape `\n` inside quotes
        //
        // But this behavior depends on the particular implementation details in the OS, so to
        // be extra safe we just prohibit anything that looks like it might be attempting to
        // override a value.
        let check = |config: &str| match config.contains(":=") || config.contains("+=") {
            true => Err(Error::SecurityViolation),
            false => Ok(()),
        };

        // Log the exact descriptor and error out if we fail - the expectation of vbmeta is that all
        // commandline parameters will get passed into the kernel, if we cannot do this then we
        // should fail loudly instead of silently dropping them.
        builder.add_checked_item(&entry, check).inspect_err(|e| {
            gbl_println!(
                ops,
                "Error: failed to convert commandline descriptor {} to bootconfig: {}",
                &entry,
                e
            );
        })?
    }
    Ok(())
}

/// Sets `linux,initrd-start/end` and optionally appending bootconfig as bootarg in FDT.
///
/// # Args
///
/// * `ops`: An implementation of GblOps.
/// * `fdt`: Target FDT to fixup.
/// * `ramdisk`: Target ramdisk for setting `linux,initrd-start/end`
/// * `append_bootconfig`: Set to true to append bootconfig from ramdisk as bootarg on dev builds.
fn finalize_dt<'b>(
    ops: &mut impl GblOps<'b>,
    fdt: &mut [u8],
    ramdisk: &[u8],
    append_bootconfig: bool,
) -> Result<usize> {
    let mut fdt = Fdt::new_mut(fdt)?;
    let Range { start, end } = ramdisk.as_ptr_range();
    let ramdisk_addr = u64::try_from(start as usize)?;
    let ramdisk_end = u64::try_from(end as usize)?;
    fdt.set_property("chosen", c"linux,initrd-start", &ramdisk_addr.to_be_bytes())?;
    fdt.set_property("chosen", c"linux,initrd-end", &ramdisk_end.to_be_bytes())?;
    gbl_println!(ops, "linux,initrd-start: {:#x}", ramdisk_addr);
    gbl_println!(ops, "linux,initrd-end: {:#x}", ramdisk_end);
    if append_bootconfig {
        gbl_println!(ops, "WARNING: Boot image predates bootconfig support.");
        cfg_if! {
            if #[cfg(feature = "gbl_dev")] {
                use bootparams::bootconfig::extract_bootconfig;
                use device_tree::fdt_append_bootargs;

                gbl_println!(ops, "Converting bootconfig into the kernel commandline.");
                fdt_append_bootargs(ops, &mut fdt, extract_bootconfig(ramdisk)?.split('\n'))?;
            } else {
                let _ = ramdisk;
                gbl_println!(
                    ops,
                    "OS may ignore AVB and other important configuration, and potentially fail to \
                    boot."
                );
            }
        }
    }
    // Print the final commandline. If the bootargs were changed by the firmware during fdt fixup,
    // then the firmware must ensure the bootargs end with '\0'.
    let final_command_line = CStr::from_bytes_until_nul(fdt.get_property("chosen", PROP_BOOTARGS)?)
        .map_err(Error::from)?;
    gbl_println!(ops, "final cmdline: \"{}\"", final_command_line.to_str().unwrap());

    fdt.shrink_to_fit()?;
    Ok(fdt.header_ref()?.actual_size())
}

/// Serializes GBL perf metrics to bootconfig.
fn add_perf_metrics(
    builder: &mut BootConfigBuilder,
    metrics: &GblMetrics,
    time: &impl GblTime,
) -> Result<()> {
    if let Some(start) = metrics.start_tick
        && let Ok(ticks) = time.elapsed_ticks(start)
    {
        builder.add_item("androidboot.gbl.perf.boot_time", time.ticks_to_us(ticks))?;
    }
    if let Some(ticks) = metrics.avb_ticks {
        builder.add_item("androidboot.gbl.perf.avb", time.ticks_to_us(ticks))?;
    }
    for (name, ticks) in metrics.io_timings_ticks.iter() {
        if STANDARD_PARTITIONS.iter().any(|p| p.name() == name) {
            let us = time.ticks_to_us(*ticks);
            writeln!(builder, "androidboot.gbl.perf.io.{name}={us}").map_err(Error::from)?;
        }
    }

    Ok(())
}

/// Serializes GBL firmware version metrics to bootconfig using flat syntax.
fn add_firmware_version_metrics(
    builder: &mut BootConfigBuilder,
    proto_metrics: &FirmwareVersionMetrics,
) -> Result<()> {
    for (name, version) in proto_metrics.iter() {
        writeln!(builder, "androidboot.gbl.fw_version.{name}={version}",).map_err(Error::from)?;
    }
    Ok(())
}

/// Helper for performing platform custom bootconfig fixup.
///
/// # Args
///
/// * `ops`: An implementation of GblOps.
/// * `buf`: Buffer containing an existing bootconfig.
/// * `curr_bootconfig_sz`: The size including trailer of the existing bootconfig.
/// * `avf_enabled`: Whether to write AVF-related bootconfig.
/// * `selected_dt_metadata`: Metadata for selected device tree components, or `None` if the boot
///   images provided none and the device tree was synthesized.
/// * `boot_items`: Fastboot boot items.
fn finalize_bootconfig<'a, 'b, 'c>(
    ops: &mut impl GblOps<'b>,
    buf: &'a mut [u8],
    curr_bootconfig_sz: usize,
    avf_enabled: bool,
    selected_dt_metadata: Option<&SelectedDtComponentsMetadata>,
    boot_items: Option<BootItemContainer<'c>>,
) -> Result<usize> {
    let mut builder = BootConfigBuilder::from_prefix_unchecked(buf, curr_bootconfig_sz)?;

    if avf_enabled {
        let vmdtbo = selected_dt_metadata.and_then(|v| v.vmdtbo.as_ref());
        avf_update_bootconfig(ops, &mut builder, vmdtbo)?;
    }

    if let Some(selected_dt_metadata) = selected_dt_metadata {
        match &selected_dt_metadata.base_dt.location {
            DtSourceLocation::DtIndex(source_index) => {
                builder.add_item("androidboot.dtb_idx", source_index)?;
                builder.add_item("androidboot.dtb_source", selected_dt_metadata.base_dt.source)?;
            }
            DtSourceLocation::FitConfigOffset(config_offset) => {
                builder.add_item("androidboot.fit_source", selected_dt_metadata.base_dt.source)?;
                builder.add_item("androidboot.fit_configuration_offset", config_offset)?;
            }
        }

        builder.add_array(
            "androidboot.dtbo_idx",
            selected_dt_metadata.overlays.iter().filter_map(|m| match m.location {
                DtSourceLocation::DtIndex(source_index) => Some(source_index),
                DtSourceLocation::FitConfigOffset(_) => None,
            }),
        )?;

        builder.add_array(
            "androidboot.dtbo_source",
            selected_dt_metadata.overlays.iter().filter_map(|m| match m.location {
                DtSourceLocation::DtIndex(_source_index) => Some(m.source),
                DtSourceLocation::FitConfigOffset(_) => None,
            }),
        )?;
    }

    if let Some(ref v) = boot_items {
        for val in v.utf8_items(BootItem::Bootconfig) {
            write!(builder, "{}{}", val, val.ends_with("\n").then_some("").unwrap_or("\n"))
                .map_err(Error::from)?;
        }
    }
    // Adds platform-specific bootconfig.
    builder.add_raw_lines_with(|bytes, out| {
        Ok(ops.fixup_bootconfig(&bytes, out)?.map(|slice| slice.len()).unwrap_or(0))
    })?;

    if let Some(metrics) = ops.get_metrics()
        && let Some(time) = ops.get_time()
    {
        add_perf_metrics(&mut builder, &metrics, time)?;
    }

    #[cfg(feature = "gbl_tracing")]
    if let Some(v) = trace::gbl_trace_buffer_info() {
        gbl_println!(ops, "Adding trace buffer info {:#x}:{:#x}", v.start, v.len());
        writeln!(builder, "androidboot.gbl.trace_addr={:#x}", v.start).map_err(Error::from)?;
        writeln!(builder, "androidboot.gbl.trace_size={:#x}", v.len()).map_err(Error::from)?;
    }

    add_firmware_version_metrics(&mut builder, &ops.get_firmware_version_metrics())?;

    Ok(builder.config_bytes().len())
}

/// Gets the target slot to boot.
pub(crate) fn get_boot_slot<'a>(ops: &mut impl GblOps<'a>) -> Result<Option<Slot>> {
    match ops.get_current_slot() {
        Ok(slot) => Ok(Some(slot)),
        #[cfg(feature = "gbl_dev")]
        Err(e @ (Error::Unsupported | Error::NotFound)) => {
            if ops.partition_size("boot_a")?.is_some() {
                gbl_println!(
                    ops,
                    "Slotting is not supported but boot_a exists. Defaulting to 'a' slot. \
                    This is only supported on dev GBL"
                );
                Ok(Some(Slot { suffix: 'a'.try_into().unwrap(), ..Default::default() }))
            } else if ops.partition_size("boot")?.is_some() {
                gbl_println!(
                    ops,
                    "Slotting is not supported and boot_a not found, but boot exists. Defaulting to slotless. \
                    This is only supported on dev GBL"
                );
                Ok(None)
            } else {
                gbl_println!(
                    ops,
                    "Slotting is not supported and neither boot_a nor boot found. Failing."
                );
                Err(e.into())
            }
        }
        Err(e) => {
            gbl_println!(ops, "Failed to get boot slot: {e}");
            Err(e.into())
        }
    }
}

/// Contains loaded, verified and fixed-up images.
#[derive(Copy, Clone)]
pub(crate) struct LoadedImages<'a> {
    pub(crate) ramdisk: &'a [u8],
    pub(crate) fdt: &'a [u8],
    pub(crate) kernel: &'a [u8],
}

/// Provides methods to run GBL fastboot.
pub struct GblFastbootEntry<'a, G> {
    pub(crate) ops: &'a mut G,
    pub(crate) boot_buffer: BootBuffer<'a>,
    pub(crate) result: &'a mut GblFastbootResult,
    pub(crate) load_result: Option<core::result::Result<LoadedImages<'a>, &'a IntegrationError>>,
}

impl<'a, 'b, G> GblFastbootEntry<'b, G>
where
    G: GblOps<'a>,
{
    /// Runs GBL fastboot with the given buffer pool, tasks container, and transports/tcp channels.
    ///
    /// # Args
    ///
    /// * `buffer_pool`: An implementation of `BufferPool` wrapped in `Shared` for allocating
    ///    download buffers.
    /// * `tasks`: An implementation of `PinFutContainer` used as task container for GBL fastboot to
    ///   schedule dynamically spawned async tasks.
    /// * `transports`: Implementation of `GblGenericTransport` which exchanges fastboot packet
    ///   from platform.
    ///   specific channels i.e. UX.
    /// * `tcp`: An implementation of `GblTcpStream` that represents TCP channel.
    ///
    /// Returns the user-defined GblOps on completion.
    pub async fn run<'c: 'd, 'd>(
        self,
        buffer_pool: &'c Shared<impl BufferPool>,
        tasks: impl PinFutContainer<'d> + 'd,
        transports: &mut [impl GblGenericTransport],
        tcp: Option<impl GblTcpStream>,
    ) -> &'b mut G
    where
        'a: 'd,
        'b: 'd,
    {
        let data = GblFbData { boot_buffer: self.boot_buffer, load_result: self.load_result };
        *self.result = run_gbl_fastboot(self.ops, buffer_pool, tasks, transports, tcp, data).await;
        self.ops
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
    ///
    /// Returns the user-defined GblOps on completion.
    pub fn run_n<const N: usize>(
        self,
        download: &mut [u8],
        transports: &mut [impl GblGenericTransport],
        tcp: Option<impl GblTcpStream>,
    ) -> &'b mut G {
        if N < 1 {
            return self.run_n::<1>(download, transports, tcp);
        }
        // Splits into N download buffers.
        let pool: ArrayVec<_, N> =
            ArrayVec::from_iter(download.chunks_exact_mut(download.len() / N).map(|b| Some(b)));
        let data = GblFbData { boot_buffer: self.boot_buffer, load_result: self.load_result };
        *self.result = block_on(run_gbl_fastboot_stack::<N>(self.ops, pool, transports, tcp, data));
        self.ops
    }

    /// Returns the user defined GblOps
    pub fn ops(&mut self) -> &mut G {
        self.ops
    }
}

/// Contains various boot buffers
#[derive(Debug)]
pub struct BootBuffer<'a> {
    /// General load buffer internally manages a BootItemContainer.
    boot_items: BootItemContainer<'a>,
    /// Optional designated kernel load buffer.
    pub kernel: Option<&'a mut [u8]>,
    /// Optional designated ramdisk load buffer.
    pub ramdisk: Option<&'a mut [u8]>,
    /// Optional designated fdt load buffer.
    pub fdt: Option<&'a mut [u8]>,
    /// Optional designated pvmfw load buffer.
    pub pvmfw_data: Option<&'a mut [u8]>,
}

impl<'a> BootBuffer<'a> {
    /// Creates a new instance.
    pub fn new(
        buffer: &'a mut [u8],
        kernel: Option<&'a mut [u8]>,
        ramdisk: Option<&'a mut [u8]>,
        fdt: Option<&'a mut [u8]>,
        pvmfw_data: Option<&'a mut [u8]>,
    ) -> Self {
        let boot_items = BootItemContainer::new(buffer);
        Self { boot_items, kernel, ramdisk, fdt, pvmfw_data }
    }

    /// Creates an instance that borrows internal fields.
    pub fn as_borrowed(&mut self) -> BootBuffer<'_> {
        BootBuffer {
            boot_items: self.boot_items.as_borrowed(),
            kernel: self.kernel.as_mut().map(|v| v as _),
            ramdisk: self.ramdisk.as_mut().map(|v| v as _),
            fdt: self.fdt.as_mut().map(|v| v as _),
            pvmfw_data: self.pvmfw_data.as_mut().map(|v| v as _),
        }
    }

    /// Gets unused buffer from general load as scratch.
    pub fn scratch(&mut self) -> &mut [u8] {
        self.boot_items.get_unused()
    }

    /// Takes the boot item container.
    pub(crate) fn boot_items(&mut self) -> &mut BootItemContainer<'a> {
        &mut self.boot_items
    }

    /// Takes the boot item container.
    pub(crate) fn take_boot_items(&mut self) -> BootItemContainer<'a> {
        take(&mut self.boot_items)
    }
}

impl<'a> From<&'a mut [u8]> for BootBuffer<'a> {
    fn from(general: &'a mut [u8]) -> Self {
        Self::new(general, None, None, None, None)
    }
}

impl Default for BootBuffer<'_> {
    fn default() -> Self {
        (&mut [][..]).into()
    }
}

/// Helper for checking that whether `fastboot continue` in paused fastboot mode should reboot.
fn paused_fastboot_continue_should_reboot() -> bool {
    // In prod, don't proceed since device security setting may have been changed.
    // In dev, allow booting since an automated test flow may want to pause in fastboot to
    // check expected device state but still want to continue to test that OS boot works as well.
    cfg!(not(feature = "gbl_dev"))
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
pub fn android_main<'a, 'b, G: GblOps<'a>>(
    ops: &mut G,
    mut boot_buffer: BootBuffer<'b>,
    mut run_fastboot: impl FnMut(GblFastbootEntry<'_, G>),
) -> Result<(&'b [u8], &'b [u8], &'b [u8], &'b mut [u8])> {
    let bcb = read_bootloader_message_to(ops, boot_buffer.scratch()).inspect_err(|e| {
        gbl_println!(ops, "Failed to read bootloader message from misc partition: {e}")
    })?;
    let boot_mode = bcb
        .boot_mode()
        .inspect_err(|e| {
            let cmd = bcb.boot_command();
            gbl_println!(ops, "Failed to parse BCB boot command {cmd:?}: {e}");
        })
        .unwrap_or(AndroidBootMode::Normal);

    if matches!(boot_mode, AndroidBootMode::BootloaderBootOnce) {
        bcb.update_boot_command(AndroidBootMode::Normal);
        write_bootloader_message(ops, bcb)?;
    }
    gbl_println!(ops, "Boot mode from BCB: {boot_mode:?}");

    let one_shot_boot_mode = ops
        .get_one_shot_boot_mode()
        .inspect_err(|e| {
            gbl_println!(ops, "Failed to check hardware triggered boot mode override: {e}");
            gbl_println!(ops, "Ignoring error and assuming not triggered");
        })
        .unwrap_or(None);
    gbl_println!(ops, "Hardware triggered boot mode override: {one_shot_boot_mode:?}");

    let slot = get_boot_slot(ops)?;

    let result = &mut Default::default();
    // Checks and enters fastboot.
    if matches!(
        (one_shot_boot_mode, boot_mode),
        (Some(OneShotBootMode::Bootloader), _) | (None, AndroidBootMode::BootloaderBootOnce)
    ) {
        gbl_println!(ops, "Entering fastboot mode...");
        run_fastboot(GblFastbootEntry {
            ops,
            boot_buffer: boot_buffer.as_borrowed(),
            result,
            load_result: None,
        });
        gbl_println!(ops, "Leaving fastboot mode...");
        // Checks if "fastboot boot" has loaded an android image.
        if matches!(&result.loaded_image_info, LoadedImageInfo::Android { .. }) {
            gbl_println!(ops, "Booting from \"fastboot boot\"");
            return Ok(result.split_loaded_android(boot_buffer).unwrap());
        }

        // Device state or disk content might have changed. Re-sync preloaded partition buffer.
        ops.sync_partition_buffer(true)?;

        // Checks whether fastboot has set a different active slot. Reboot if it does.
        if slot.map_or(
            false,
            |s| matches!(result.last_set_active_slot, Some(x) if x != s.suffix.as_char()),
        ) {
            gbl_println!(ops, "Active slot changed by \"fastboot set_active\". Reset..");
            ops.reboot()?;
        }
    }

    let is_recovery = boot_mode.should_enter_recovery()
        || matches!(one_shot_boot_mode, Some(OneShotBootMode::Recovery));
    let load_res = android_load_verify_fixup(ops, slot, is_recovery, boot_buffer.as_borrowed())
        .map(|(ramdisk, fdt, kernel, _)| {
            let [ramdisk, fdt, kernel] = [ramdisk, fdt, kernel].map(|v| v.as_ptr_range());
            LoadedImageInfo::Android { ramdisk, fdt, kernel }
        });

    if result.pause_in_fastboot || ops.one_shot_pause_fastboot_after_load() {
        let result = &mut Default::default();
        // Some fastboot functions require a general load buffer as scratch. Use `unused` when
        // load is successful to prevent clobbering of images, otherwise use `boot_buffer`.
        let (load_res, boot_buffer) = match load_res.as_ref() {
            Ok(v) => {
                let (ramdisk, fdt, kernel, unused) =
                    split_loaded_android(v.clone(), boot_buffer.as_borrowed()).unwrap();
                (Ok(LoadedImages { ramdisk, fdt, kernel }), unused.into())
            }
            Err(e) => (Err(e), boot_buffer.as_borrowed()),
        };
        let load_result = Some(load_res.inspect_err(|e| gbl_println!(ops, "Load failed: {e}")));
        gbl_println!(ops, "Pausing in fastboot...");
        // Disable tracing for post-load fastboot as it is for debug/test only and not part of
        // normal functional flow.
        let _guard = trace::TraceGuard::new(false);
        run_fastboot(GblFastbootEntry { ops, boot_buffer, result, load_result });
        if paused_fastboot_continue_should_reboot() {
            gbl_println!(ops, "Device state may have changed. Rebooting...");
            ops.reboot()?;
        }
    }

    let (ramdisk, fdt, kernel, unused) = split_loaded_android(load_res?, boot_buffer).unwrap();

    // Note: handle_loaded_os must be the last call in the boot flow, as the implementation
    // may take over control flow with firmware-specific HLOS handoff, so never return back.
    match ops.handle_loaded_os(kernel, ramdisk, fdt) {
        // Loaded OS handling is optional.
        Ok(_) | Err(Error::Unsupported) => {}
        #[cfg(feature = "gbl_dev")]
        Err(Error::NotFound) => {}
        Err(e) => return Err(e.into()),
    }

    Ok((ramdisk, fdt, kernel, unused))
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::{
        android_boot::device_tree::{
            KASLR_SEED_PROP, KASLR_SEED_SIZE_BYTES, RNG_SEED_PROP, RNG_SEED_SIZE_BYTES,
        },
        constants::{KERNEL_ALIGNMENT, PAGE_SIZE, PVMFW_DATA_ALIGNMENT},
        fastboot::test::{make_expected_transport_out, SharedTestListener},
        gbl_avb::{
            state::{BootStateColor, KeyValidationStatus},
            AvbPartition, AvbProperty, Critical, Fdr, SpecializedPartition,
        },
        metrics::FirmwareVersion,
        misc::test::read_bootloader_message,
        ops::{
            test::{into_refmut_bytes, slot, FakeGblOps, FakeGblOpsStorage, FakeGblTime},
            PartitionBuffer,
        },
        tests::{read_test_data, read_test_data_as_str, test_data_exists},
    };
    use avf::{
        test::{dummy_pvmfw_partition, DUMMY_VENDOR_HANDOVER},
        PROTECTED_PROP, UNPROTECTED_PROP,
    };
    use bootparams::bootconfig::{extract_bootconfig, BootConfigBuilder, BOOTCONFIG_TRAILER_SIZE};
    use cfg_if::cfg_if;
    use fdt::std_props;
    use libbuild_number::{BUILD_BRANCH, BUILD_NUMBER, BUILD_REVISION, VERSION};
    use libtestutils::AlignedBuffer;
    use libutils::cstr_buffer;
    use std::{
        ascii::escape_default,
        cell::RefCell,
        collections::{BTreeMap, HashMap},
        ffi::CString,
        path::Path,
        str::from_utf8,
        string::String,
    };

    /// Rollback index location used in test artifacts.
    pub(crate) const TEST_ROLLBACK_INDEX_LOCATION: usize = 1;
    /// Rollback index value used in test artifacts.
    pub(crate) const TEST_ROLLBACK_INDEX: u64 = 2;

    // The vendor bootconfig in the generated vendor boot image.
    // See libgbl/testdata/gen_test_data.py for test data generation.
    pub(crate) const TEST_VENDOR_BOOTCONFIG: &str =
        "androidboot.config_1=val_1\x0aandroidboot.config_2=val_2\x0a";

    /// A key used to sign test vbmeta images. Each variant carries the public-key
    /// digest libavb reports in `androidboot.vbmeta.public_key_digest` (the sha256
    /// of the AVB-serialized public key).
    #[derive(Clone, Copy)]
    pub(crate) enum TestVbmetaKey {
        Rsa4096,
        Mldsa65,
        Mldsa87,
    }

    impl TestVbmetaKey {
        pub(crate) fn public_key_digest(self) -> &'static str {
            match self {
                Self::Rsa4096 => "7ec02ee1be696366f3fa91240a8ec68125c4145d698f597aa2b3464b59ca7fc3",
                Self::Mldsa65 => "0e84a0f0725841b15919a9db89705791c13d39be002516d2481dec3ed3f2b6ce",
                Self::Mldsa87 => "2ec52b1617dfd35327a766571a410c46a5d3299d2d0f858300a49bd614a8df21",
            }
        }
    }

    /// Expected AVB properties provided by the test data.
    pub(crate) const EXPECTED_AVB_PROPS: &[(&str, &str)] = &[
        ("com.android.build.system.os_version", "1"),
        ("com.android.build.system.security_patch", "1"),
    ];

    // Expected FDT properties provided by `dtb_a`.
    const EXPECTED_DTB_PROPS_A: &[(&str, &CStr, Option<&[u8]>)] =
        &[("/chosen", c"dtb_slot", Some(b"a\0"))];

    // Expected FDT properties aplied by `dtbo_a`.
    const EXPECTED_DTBO_PROPS_A: &[(&str, &CStr, Option<&[u8]>)] = &[
        ("/chosen/first_overlay", c"overlay_a_property", Some(b"overlay_a_val\0")),
        ("/chosen/first_overlay", c"second_overlay_a_property", Some(b"second_overlay_a_val\0")),
    ];

    // Expected FDT properties provided by `dtb_b`.
    const EXPECTED_DTB_PROPS_B: &[(&str, &CStr, Option<&[u8]>)] =
        &[("/chosen", c"dtb_slot", Some(b"b\0"))];

    // Expected FDT properties aplied by `dtbo_b`.
    const EXPECTED_DTBO_PROPS_B: &[(&str, &CStr, Option<&[u8]>)] = &[
        ("/chosen/first_overlay", c"overlay_b_property", Some(b"overlay_b_val\0")),
        ("/chosen/first_overlay", c"second_overlay_b_property", Some(b"second_overlay_b_val\0")),
    ];

    // Expected FDT properties provided by `boot` or `vendor_boot`.
    const EXPECTED_FDT_PROPS: &[(&str, &CStr, Option<&[u8]>)] =
        &[("/chosen", c"builtin", Some(&[1]))];

    /// Generates a readable string for a bootconfig bytes.
    pub(crate) fn dump_bootconfig(data: &[u8]) -> String {
        let s = data.iter().map(|v| escape_default(*v).to_string()).collect::<Vec<_>>().concat();
        let s = s.split("\\\\").collect::<Vec<_>>().join("\\");
        s.split("\\n").collect::<Vec<_>>().join("\n")
    }

    /// A helper for assert checking ramdisk binary and bootconfig separately.
    pub(crate) fn check_ramdisk(ramdisk: &[u8], expected_bin: &[u8], expected_bootconfig: &[u8]) {
        let (ramdisk, bootconfig) = ramdisk.split_at(expected_bin.len());
        assert_eq!(ramdisk, expected_bin);
        assert_eq!(
            bootconfig,
            expected_bootconfig,
            "\nexpect: \n{}\nactual: \n{}\n",
            dump_bootconfig(expected_bootconfig),
            dump_bootconfig(bootconfig),
        );
    }

    /// A helper for generating expected bootconfig with the given parameters.
    pub(crate) struct ExpectedBootconfigBuilder {
        slot: Option<char>,
        vbmeta_size: usize,
        digest: String,
        partition_digests: BTreeMap<String, String>,
        public_key_digest: String,
        color: BootStateColor,
        unlocked: bool,
        force_normal_boot: bool,
        vendor_bootconfig: Option<String>,
        dtb_idx: Option<usize>,
        dtb_source: Option<String>,
        dtbo_idx: Vec<usize>,
        dtbo_source: Vec<String>,
        extra: String,
    }

    impl ExpectedBootconfigBuilder {
        pub(crate) fn new() -> Self {
            Self {
                slot: None,
                vbmeta_size: 0,
                digest: String::new(),
                partition_digests: BTreeMap::new(),
                public_key_digest: String::new(),
                color: BootStateColor::Green,
                unlocked: false,
                force_normal_boot: true,
                vendor_bootconfig: None,
                dtb_idx: None,
                dtb_source: None,
                dtbo_idx: Vec::new(),
                dtbo_source: Vec::new(),
                extra: String::new(),
            }
        }

        pub(crate) fn slot(mut self, slot: char) -> Self {
            self.slot = Some(slot);
            self
        }

        pub(crate) fn vbmeta_size(mut self, size: usize) -> Self {
            self.vbmeta_size = size;
            self
        }

        pub(crate) fn digest(mut self, digest: impl Into<String>) -> Self {
            self.digest = digest.into();
            self
        }

        pub(crate) fn partition_digest(mut self, name: &str, digest: impl Into<String>) -> Self {
            self.partition_digests.insert(name.into(), digest.into());
            self
        }

        pub(crate) fn public_key_digest(mut self, key: TestVbmetaKey) -> Self {
            self.public_key_digest = key.public_key_digest().to_string();
            self
        }

        pub(crate) fn color(mut self, color: BootStateColor) -> Self {
            self.color = color;
            self
        }

        pub(crate) fn unlocked(mut self, unlocked: bool) -> Self {
            self.unlocked = unlocked;
            self
        }

        pub(crate) fn force_normal_boot(mut self, force: bool) -> Self {
            self.force_normal_boot = force;
            self
        }

        pub(crate) fn vendor_bootconfig(mut self, vendor_bootconfig: &str) -> Self {
            self.vendor_bootconfig = Some(vendor_bootconfig.to_string());
            self
        }

        pub(crate) fn dtb_idx(mut self, idx: usize) -> Self {
            self.dtb_idx = Some(idx);
            self
        }

        pub(crate) fn dtb_source(mut self, source: impl Into<String>) -> Self {
            self.dtb_source = Some(source.into());
            self
        }

        pub(crate) fn dtbo_idx(mut self, idx: &[usize]) -> Self {
            self.dtbo_idx = idx.to_vec();
            self
        }

        pub(crate) fn dtbo_source(mut self, source: &[&str]) -> Self {
            self.dtbo_source = source.iter().map(|&s| s.to_owned()).collect();
            self
        }

        pub(crate) fn extra(mut self, extra: impl Into<String>) -> Self {
            self.extra += &extra.into();
            self
        }

        /// Returns the bootconfig properties we expect GBL to add at runtime.
        pub(crate) fn build_string_gbl_props(&self) -> String {
            let mut result = String::new();
            writeln!(result, "androidboot.verifiedbootstate={}", self.color).unwrap();
            if self.force_normal_boot {
                writeln!(result, "androidboot.force_normal_boot=1").unwrap();
            }
            if let Some(slot) = self.slot {
                writeln!(result, "androidboot.slot_suffix=_{slot}").unwrap();
            }
            add_android_gbl_bootconfig(&mut result, Some(202604)).unwrap();
            result
        }

        /// Returns the bootconfig properties we expect AVB to add during verification.
        pub(crate) fn build_string_avb_props(&self) -> String {
            let mut result = String::new();
            let device_state = match self.unlocked {
                true => "unlocked",
                false => "locked",
            };
            let vbmeta_hash_alg = match self.digest.len() {
                64 => "sha256",
                _ => "sha512",
            };
            write!(
                result,
                "androidboot.vbmeta.device=PARTUUID=00000000-0000-0000-0000-000000000000\n\
                androidboot.vbmeta.public_key_digest={}\n\
                androidboot.vbmeta.avb_version=1.4\n\
                androidboot.vbmeta.device_state={device_state}\n\
                androidboot.vbmeta.hash_alg={}\n\
                androidboot.vbmeta.size={}\n\
                androidboot.vbmeta.digest={}\n\
                androidboot.veritymode=enforcing\n\
                androidboot.veritymode.managed=yes\n",
                self.public_key_digest, vbmeta_hash_alg, self.vbmeta_size, self.digest
            )
            .unwrap();

            for (k, v) in &self.partition_digests {
                writeln!(result, "androidboot.vbmeta.{k}.hash_alg=sha256").unwrap();
                writeln!(result, "androidboot.vbmeta.{k}.digest={v}").unwrap();
            }
            result
        }

        /// Returns the bootconfig properties we expect from the vendor_boot image.
        pub(crate) fn build_string_vendor_props(&self) -> String {
            let mut result = String::new();
            if let Some(vendor_bootconfig) = &self.vendor_bootconfig {
                result.push_str(vendor_bootconfig);
            }
            result
        }

        /// Returns the bootconfig properties we expect indicating the DTB selection.
        pub(crate) fn build_string_dtb_props(&self) -> String {
            let mut result = String::new();
            if let Some(dtb_idx) = self.dtb_idx {
                writeln!(result, "androidboot.dtb_idx={dtb_idx}").unwrap();
            }
            if let Some(dtb_source) = &self.dtb_source {
                writeln!(result, "androidboot.dtb_source={dtb_source}").unwrap();
            }
            if !self.dtbo_idx.is_empty() {
                let idx =
                    self.dtbo_idx.iter().map(ToString::to_string).collect::<Vec<_>>().join(",");
                writeln!(result, "androidboot.dtbo_idx={idx}").unwrap();
            }
            if !self.dtbo_source.is_empty() {
                writeln!(result, "androidboot.dtbo_source={}", self.dtbo_source.join(",")).unwrap();
            }
            result
        }

        /// Returns the full bootconfig properties expected without any verified boot.
        pub(crate) fn build_no_avb(self) -> Vec<u8> {
            let mut result = String::new();
            // GBL props should come first, the OS consumers use first-match.
            result.push_str(&self.build_string_gbl_props());
            result.push_str(&self.build_string_vendor_props());
            result.push_str(&self.build_string_dtb_props());
            result.push_str(&self.extra);
            make_bootconfig(result)
        }

        /// Returns the full bootconfig properties expected including verified boot.
        pub(crate) fn build(self) -> Vec<u8> {
            let mut result = String::new();
            // GBL props should come first, the OS consumers use first-match.
            result.push_str(&self.build_string_gbl_props());
            result.push_str(&self.build_string_avb_props());
            result.push_str(&self.build_string_vendor_props());
            result.push_str(&self.build_string_dtb_props());
            result.push_str(&self.extra);
            make_bootconfig(result)
        }
    }

    // A helper for generating expected bootconfig.
    pub(crate) fn make_bootconfig(bootconfig: impl AsRef<str>) -> Vec<u8> {
        let bootconfig = bootconfig.as_ref();
        let mut buffer = vec![0u8; bootconfig.len() + BOOTCONFIG_TRAILER_SIZE];
        let mut res = BootConfigBuilder::new(&mut buffer).unwrap();
        write!(res, "{bootconfig}").unwrap();
        res.config_bytes().to_vec()
    }

    /// Helper for generating expected bootconfig after load and verification.
    ///
    /// # Args
    ///
    /// * `vbmeta_file``: The test file name for the target vbmeta data.
    /// * `unlocked`: True if unlocked mode.
    /// * `color`: The expected boot state color.
    /// * `slot`: The expected slot.
    /// * `vendor_config:` The expected vendor_boot config.
    /// * `fixup_config`: The expected fixup config by GblOps.
    fn make_expected_bootconfig(
        partitions: &[(String, String)],
        vbmeta_file: Option<&str>,
        unlocked: bool,
        color: BootStateColor,
        slot: char,
        vendor_config: &str,
        fixup_config: &str,
        key: TestVbmetaKey,
    ) -> Vec<u8> {
        let mut builder = ExpectedBootconfigBuilder::new()
            .color(color)
            .slot(slot)
            .vendor_bootconfig(vendor_config)
            .extra(fixup_config);

        let has_partition = |name: &str| {
            let target = format!("{name}_{slot}");
            partitions.iter().any(|(p, _)| p == &target)
        };

        // Find the first matching source in priority order
        let dtb_sources = ["dtb", "vendor_boot", "boot"];
        if let Some(&source) = dtb_sources.iter().find(|&&s| has_partition(s)) {
            builder = builder.dtb_idx(0).dtb_source(source);
        }
        if has_partition("dtbo") {
            builder = builder.dtbo_idx(&[0, 1]).dtbo_source(&["dtbo", "dtbo"]);
        }

        match vbmeta_file {
            Some(vbmeta_file) => {
                let vbmeta_file = Path::new(vbmeta_file);
                let vbmeta_name = vbmeta_file.to_str().unwrap();
                let vbmeta_digest = vbmeta_file.with_extension("digest.txt");
                let vbmeta_digest = vbmeta_digest.to_str().unwrap();

                builder = builder
                    .vbmeta_size(read_test_data(vbmeta_name).len())
                    .digest(read_test_data_as_str(vbmeta_digest))
                    .public_key_digest(key)
                    .unlocked(unlocked);

                for (part, _) in partitions {
                    let slotless =
                        part.strip_suffix(&format!("_{slot}")).unwrap_or(part).to_string();
                    let digest = vbmeta_file.with_extension(format!("{slotless}.digest.txt"));
                    let digest = digest.to_str().unwrap();
                    if test_data_exists(digest) {
                        builder.partition_digests.insert(slotless, read_test_data_as_str(digest));
                    }
                }

                builder.build()
            }
            None => builder.build_no_avb(),
        }
    }

    /// Converts bootconfig to bootargs
    fn bootconfig_to_bootarg(bootconfig: &[u8]) -> String {
        let s = bootconfig.split_last_chunk::<BOOTCONFIG_TRAILER_SIZE>().unwrap().0;
        from_utf8(s).unwrap().split('\n').filter(|v| !v.is_empty()).collect::<Vec<_>>().join(" ")
    }

    /// Tests `android_load_verify_fixup` succeeds with the given setup.
    ///
    /// # Args
    ///
    /// * `slot`: Slot.
    /// * `partitions`: LoadPartition data for disk.
    /// * `specialized_partitions`: `SpecializedPartition`s to process.
    /// * `unlock`: Unlock state.
    /// * `rollback_idx`: Rollback index at location TEST_ROLLBACK_INDEX_LOCATION.
    /// * `load`: A BootBuffer.
    /// * `expected_kernel`: Expected loaded kernel.
    /// * `expected_ramdisk`: Expected loaded ramdisk.
    /// * `expected_bootconfig`: Expected fixed-up bootconfig.
    /// * `expected_bootargs`: Expected fixed-up bootargs.
    /// * `expected_fdt_property`: Expected fixed-up FDT properties.
    fn test_android_load_verify_fixup_internal<'a>(
        slot: Slot,
        partitions: &[(String, String)],
        specialized_partitions: &[SpecializedPartition],
        unlock: bool,
        rollback_idx: u64,
        boot_buffer: BootBuffer<'_>,
        expected_kernel: &[u8],
        expected_ramdisk: &[u8],
        expected_bootconfig: &[u8],
        expected_bootargs: &str,
        expected_fdt_property: &[(&str, &CStr, Option<&[u8]>)],
    ) {
        let mut storage = FakeGblOpsStorage::default();
        let partitions = partitions.iter().map(|(l, r)| (CString::new(l.clone()).unwrap(), r));
        for (part, file) in partitions.filter(|(_, f)| !f.is_empty()) {
            storage.add_raw_device(&part, read_test_data(file));
        }
        let mut ops = FakeGblOps::new(&storage);
        ops.avb_device_status.is_unlocked = unlock;
        ops.avb_ops.rollbacks = HashMap::from([(TEST_ROLLBACK_INDEX_LOCATION, Ok(rollback_idx))]);
        let mut out_status = None;
        let mut handler = |status,
                           _: Option<&CStr>,
                           _: Option<Vec<AvbProperty<'_>>>,
                           partitions: Option<Vec<AvbPartition<'_>>>| {
            // Checks presence of each `specialized_partitions` that requested verification.
            //
            // This currently only looks for `Required` verification, `IfExists` is a bit tricky to
            // handle correctly because it depends on whether the partition exists and has a hash
            // descriptor in the vbmeta image.
            if let Some(partitions) = partitions {
                for specialized_part in specialized_partitions
                    .iter()
                    .filter(|p| p.verification == Some(Verification::Required))
                {
                    assert!(
                        partitions.iter().any(|p| p.name == specialized_part.name_cstr()),
                        "Requested partition: {:?} isn't reported by handle_verification_result",
                        specialized_part
                    );
                }
            }
            out_status = Some(status);
            Ok(())
        };
        ops.avb_handle_verification_result = Some(&mut handler);
        ops.avb_key_validation_status = Some(Ok(KeyValidationStatus::Valid));
        ops.avb_partition_attributes = Some(Ok(specialized_partitions.to_vec()));

        let designated_ramdisk = boot_buffer.ramdisk.as_ref().map(|v| v.as_ptr());
        let designated_fdt = boot_buffer.fdt.as_ref().map(|v| v.as_ptr());
        let designated_kernel = boot_buffer.kernel.as_ref().map(|v| v.as_ptr());
        let (ramdisk, fdt, kernel, _) =
            android_load_verify_fixup(&mut ops, Some(slot), false, boot_buffer).unwrap();
        assert_eq!(kernel, expected_kernel);
        check_ramdisk(ramdisk, expected_ramdisk, expected_bootconfig);
        assert_eq!(ramdisk.as_ptr() as usize % PAGE_SIZE, 0);
        assert_eq!(designated_ramdisk.unwrap_or(ramdisk.as_ptr()), ramdisk.as_ptr());
        assert_eq!(designated_fdt.unwrap_or(fdt.as_ptr()), fdt.as_ptr());
        assert_eq!(designated_kernel.unwrap_or(kernel.as_ptr()), kernel.as_ptr());

        // If both ramdisk and fdt are in general load buffer, checks it starts at page size
        // aligned address.
        assert!(
            designated_ramdisk.is_some()
                || designated_fdt.is_some()
                || fdt.as_ptr().align_offset(PAGE_SIZE) == 0
        );

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

        assert_eq!(
            fdt.get_property("/chosen", RNG_SEED_PROP),
            Ok(&FakeGblOps::GBL_TEST_RANDOM_DATA[..RNG_SEED_SIZE_BYTES])
        );

        assert_eq!(
            fdt.get_property("/chosen", KASLR_SEED_PROP),
            Ok(&FakeGblOps::GBL_TEST_RANDOM_DATA[..KASLR_SEED_SIZE_BYTES])
        );

        // Fixup is applied.
        assert_eq!(
            fdt.get_property("/chosen", FakeGblOps::TEST_CUSTOM_FDT_FIXUP_PROP).unwrap(),
            FakeGblOps::GBL_TEST_FDT_FIXUP
        );

        // Bootconfig fixup should happen after DT fixup.
        assert_eq!(fdt.get_property("", c"fixup_bootconfig_calls").unwrap(), &[0]);

        // Other FDT properties are as expected.
        for (path, property, res) in expected_fdt_property {
            assert_eq!(
                fdt.get_property(&path, &property).ok(),
                res.clone(),
                "{path}:{property:?} value doesn't match"
            );
        }
    }

    /// Helper for testing `android_load_verify_fixup` given a partition layout and target slot
    /// using both monolithic and desinated load buffer.
    fn test_android_load_verify_fixup(
        slot: Slot,
        partitions: &[(String, String)],
        specialized_partitions: &[SpecializedPartition],
        unlock: bool,
        rollback_idx: u64,
        expected_kernel: &[u8],
        expected_ramdisk: &[u8],
        expected_bootconfig: &[u8],
        expected_bootargs: &str,
        expected_fdt_property: &[(&str, &CStr, Option<&[u8]>)],
    ) {
        let general = &mut AlignedBuffer::new(64 * 1024 * 1024, KERNEL_ALIGNMENT);
        let mut kernel = AlignedBuffer::<u8>::new(64 * 1024 * 1024, KERNEL_ALIGNMENT);
        let mut ramdisk = AlignedBuffer::<u8>::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let mut fdt = AlignedBuffer::<u8>::new(1 * 1024 * 1024, FDT_ALIGNMENT);
        // Tests all possible combinations of available/unavailable designated buffer for
        // kernel/ramdisk/fdt.
        for flag in 0..0x8 {
            let kernel = ((flag & 1) != 0).then_some(&mut kernel[..]);
            let ramdisk = ((flag & 2) != 0).then_some(&mut ramdisk[..]);
            let fdt = ((flag & 4) != 0).then_some(&mut fdt[..]);
            let mut buffers = BootBuffer::new(general, kernel, ramdisk, fdt, None);
            println!("\nBoot buffer config #{flag}");
            println!("  general: {:?} bytes", buffers.boot_items.raw_buffer().len());
            println!("  kernel: {:?} bytes", buffers.kernel.as_ref().map(|v| v.len()));
            println!("  ramdisk: {:?} bytes", buffers.ramdisk.as_ref().map(|v| v.len()));
            println!("  fdt: {:?} bytes", buffers.fdt.as_ref().map(|v| v.len()));
            test_android_load_verify_fixup_internal(
                slot,
                partitions,
                specialized_partitions,
                unlock,
                rollback_idx,
                buffers,
                expected_kernel,
                expected_ramdisk,
                expected_bootconfig,
                expected_bootargs,
                expected_fdt_property,
            );
        }
    }

    /// Helper for testing that `android_load_verify_fixup` succeeds for the given partition setup
    /// in various locked/unlocked mode.
    fn test_android_load_verify_fixup_success(
        slot_name: char,
        partitions: &[(String, String)],
        vbmeta: &str,
        expected_kernel: &[u8],
        expected_ramdisk: &[u8],
        expected_vendor_bootconfig: &str,
        expected_bootargs: &str,
        expected_fdt_property: &[(&str, &CStr, Option<&[u8]>)],
        bootconfig_supported: bool,
        key: TestVbmetaKey,
    ) {
        let test_common = |unlock, color, rollback_idx, vbmeta: Option<&str>| {
            let mut partitions = partitions.to_vec();
            let has_dtbo = partitions.iter().any(|p| p.0 == format!("dtbo_{slot_name}"));
            if let Some(vbmeta) = vbmeta {
                partitions.push((format!("vbmeta_{slot_name}"), vbmeta.into()));
            }
            partitions.push((format!("fw_{slot_name}"), format!("android/fw_{slot_name}.img")));

            let expected_bootconfig = make_expected_bootconfig(
                &partitions,
                vbmeta,
                unlock,
                color,
                slot_name,
                expected_vendor_bootconfig,
                FakeGblOps::GBL_TEST_BOOTCONFIG,
                key,
            );
            let mut expected_bootargs = String::from(expected_bootargs);
            // Appended via dtbo/bootargs_ext.
            if has_dtbo {
                expected_bootargs
                    .push_str(" top_level_overlay_bootargs_ext fragment_overlay_bootargs_ext");
            }
            // Appended via fixup.
            expected_bootargs.push_str(" fixup");
            // Converted items if bootconfig isn't supported.
            if !bootconfig_supported && cfg!(feature = "gbl_dev") {
                write!(expected_bootargs, " {}", &bootconfig_to_bootarg(&expected_bootconfig))
                    .unwrap();
            }

            test_android_load_verify_fixup(
                slot(slot_name),
                &partitions,
                &[
                    SpecializedPartition {
                        name_buffer: cstr_buffer("fw"),
                        verification: Some(Verification::Required),
                        ..Default::default()
                    },
                    // Add a set of specialized partitions that should be ignored by verification.
                    //
                    // Putting these in every test case that calls this function is a bit of
                    // overkill, it might be better to have separate focused tests, but setting up
                    // separate tests just for this would require more boilerplate than it's worth
                    // so just leave it here for now.
                    SpecializedPartition {
                        name_buffer: cstr_buffer("optional_and_not_present"),
                        verification: Some(Verification::IfExists),
                        ..Default::default()
                    },
                    SpecializedPartition {
                        name_buffer: cstr_buffer("fdr"),
                        fdr: Fdr::Yes,
                        ..Default::default()
                    },
                    SpecializedPartition {
                        name_buffer: cstr_buffer("critical"),
                        critical: Critical::Yes,
                        ..Default::default()
                    },
                ],
                unlock,
                rollback_idx,
                expected_kernel,
                expected_ramdisk,
                &expected_bootconfig,
                &expected_bootargs,
                expected_fdt_property,
            );
        };

        // All the following variants should succeed for the same setup.

        // AVB verification passes in locked mode.
        println!("\n---sub test: AVB passes, locked mode---\n");
        test_common(false, BootStateColor::Green, 0, Some(vbmeta));
        // AVB verification passes in unlocked mode.
        println!("\n---sub test: AVB passes, unlocked mode---\n");
        test_common(true, BootStateColor::Orange, 0, Some(vbmeta));
        println!("\n---sub test: AVB failed, unlocked mode---\n");
        // Causes rollback protection failure. Tests that in unlocked mode, images will be loaded
        // as usual.
        test_common(true, BootStateColor::Orange, 3, Some(vbmeta));

        // No valid vbmeta partition when unlocked and dev flow.
        if cfg!(feature = "gbl_dev") {
            println!("\n---sub test: No-AVB, unlocked mode, dev flow---\n");
            test_common(true, BootStateColor::Orange, 0, None);
        }
    }

    const EXPECTED_V2_CMDLINE: &str = "existing_arg_1=existing_val_1 existing_arg_2=existing_val_2 cmd_key_1=cmd_val_1,cmd_key_2=cmd_val_2";

    /// Helper for testing `android_load_verify_fixup` for v2 boot image or lower.
    fn test_android_load_verify_fixup_v2_or_lower(
        ver: u8,
        slot: char,
        additional_parts: &[(&str, &str)],
        additional_expected_fdt_properties: &[(&str, &CStr, Option<&[u8]>)],
    ) {
        let vbmeta_file = format!("android/vbmeta_v{ver}_{slot}.img");
        let mut parts = vec![(format!("boot_{slot}"), format!("android/boot_v{ver}_{slot}.img"))];
        for (part, file) in additional_parts.iter().cloned() {
            parts.push((part.into(), file.into()));
        }
        test_android_load_verify_fixup_success(
            slot,
            &parts,
            &vbmeta_file,
            &read_test_data(format!("android/kernel_{slot}.img")),
            &read_test_data(format!("android/generic_ramdisk_{slot}.img")),
            "",
            EXPECTED_V2_CMDLINE,
            additional_expected_fdt_properties,
            false,
            TestVbmetaKey::Rsa4096,
        )
    }

    #[test]
    fn test_android_load_verify_fixup_v0_slot_a() {
        // V0 image doesn't have built-in dtb. We need to provide from dtb partition.
        let parts = &[("dtb_a", "android/dtb_a.img")];
        test_android_load_verify_fixup_v2_or_lower(0, 'a', parts, EXPECTED_DTB_PROPS_A);
    }

    #[test]
    fn test_android_load_verify_fixup_v0_dtbo_slot_a() {
        let parts = &[("dtbo_a", "android/dtbo_a.img"), ("dtb_a", "android/dtb_a.img")];
        let fdt_prop = Vec::from([EXPECTED_DTB_PROPS_A, EXPECTED_DTBO_PROPS_A].concat());
        test_android_load_verify_fixup_v2_or_lower(0, 'a', parts, &fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v0_slot_b() {
        let parts = &[("dtb_b", "android/dtb_b.img")];
        test_android_load_verify_fixup_v2_or_lower(0, 'b', parts, EXPECTED_DTB_PROPS_B);
    }

    #[test]
    fn test_android_load_verify_fixup_v0_dtbo_slot_b() {
        let parts = &[("dtbo_b", "android/dtbo_b.img"), ("dtb_b", "android/dtb_b.img")];
        let fdt_prop = Vec::from([EXPECTED_DTB_PROPS_B, EXPECTED_DTBO_PROPS_B].concat());
        test_android_load_verify_fixup_v2_or_lower(0, 'b', parts, &fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v1_slot_a() {
        // V1 image doesn't have built-in dtb. We need to provide from dtb partition.
        let parts = &[("dtb_a", "android/dtb_a.img")];
        test_android_load_verify_fixup_v2_or_lower(1, 'a', parts, EXPECTED_DTB_PROPS_A);
    }

    #[test]
    fn test_android_load_verify_fixup_v1_dtbo_slot_a() {
        let parts = &[("dtbo_a", "android/dtbo_a.img"), ("dtb_a", "android/dtb_a.img")];
        let fdt_prop = Vec::from([EXPECTED_DTB_PROPS_A, EXPECTED_DTBO_PROPS_A].concat());
        test_android_load_verify_fixup_v2_or_lower(1, 'a', parts, &fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v1_slot_b() {
        let parts = &[("dtb_b", "android/dtb_b.img")];
        test_android_load_verify_fixup_v2_or_lower(1, 'b', parts, EXPECTED_DTB_PROPS_B);
    }

    #[test]
    fn test_android_load_verify_fixup_v1_dtbo_slot_b() {
        let parts = &[("dtbo_b", "android/dtbo_b.img"), ("dtb_b", "android/dtb_b.img")];
        let fdt_prop = Vec::from([EXPECTED_DTB_PROPS_B, EXPECTED_DTBO_PROPS_B].concat());
        test_android_load_verify_fixup_v2_or_lower(1, 'b', parts, &fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v2_slot_a() {
        // V2 image has built-in dtb. We don't need to provide custom device tree.
        test_android_load_verify_fixup_v2_or_lower(2, 'a', &[], EXPECTED_FDT_PROPS);
    }

    #[test]
    fn test_android_load_verify_fixup_v2_dtbo_slot_a() {
        let parts = &[("dtbo_a".into(), "android/dtbo_a.img".into())];
        let fdt_prop = Vec::from([EXPECTED_FDT_PROPS, EXPECTED_DTBO_PROPS_A].concat());
        test_android_load_verify_fixup_v2_or_lower(2, 'a', parts, &fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v2_slot_b() {
        test_android_load_verify_fixup_v2_or_lower(2, 'b', &[], EXPECTED_FDT_PROPS);
    }

    #[test]
    fn test_android_load_verify_fixup_v2_dtbo_slot_b() {
        let parts = &[("dtbo_b".into(), "android/dtbo_b.img".into())];
        let fdt_prop = Vec::from([EXPECTED_FDT_PROPS, EXPECTED_DTBO_PROPS_B].concat());
        test_android_load_verify_fixup_v2_or_lower(2, 'b', parts, &fdt_prop);
    }

    /// Returns the expected ramdisk for a slotted v3/v4 image in this test module.
    fn expected_v3_v4_ramdisk(slot: char) -> Vec<u8> {
        [
            read_test_data(format!("android/vendor_ramdisk_{slot}.img")),
            read_test_data(format!("android/generic_ramdisk_{slot}.img")),
        ]
        .concat()
    }

    const EXPECTED_V3_V4_CMDLINE: &str = "existing_arg_1=existing_val_1 existing_arg_2=existing_val_2 cmd_key_1=cmd_val_1,cmd_key_2=cmd_val_2 cmd_vendor_key_1=cmd_vendor_val_1,cmd_vendor_key_2=cmd_vendor_val_2";

    /// Common helper for testing `android_load_verify_fixup` for v3/v4 boot image.
    fn test_android_load_verify_fixup_v3_or_v4(
        slot: char,
        partitions: &[(String, String)],
        vbmeta_file: &str,
        expected_vendor_bootconfig: &str,
        additional_expected_fdt_properties: &[(&str, &CStr, Option<&[u8]>)],
        bootconfig_supported: bool,
        key: TestVbmetaKey,
    ) {
        test_android_load_verify_fixup_success(
            slot,
            partitions,
            vbmeta_file,
            &read_test_data(format!("android/kernel_{slot}.img")),
            &expected_v3_v4_ramdisk(slot),
            expected_vendor_bootconfig,
            EXPECTED_V3_V4_CMDLINE,
            additional_expected_fdt_properties,
            bootconfig_supported,
            key,
        )
    }

    /// Helper for testing `android_load_verify_fixup` for v3/v4 boot image without init_boot.
    fn test_android_load_verify_fixup_v3_or_v4_no_init_boot(
        boot_ver: u32,
        vendor_ver: u32,
        slot: char,
        expected_vendor_bootconfig: &str,
        additional_parts: &[(String, String)],
        additional_expected_fdt_properties: &[(&str, &CStr, Option<&[u8]>)],
    ) {
        let vbmeta = format!("android/vbmeta_v{boot_ver}_v{vendor_ver}_{slot}.img");
        let mut parts = vec![
            (format!("boot_{slot}"), format!("android/boot_v{boot_ver}_{slot}.img")),
            (
                format!("vendor_boot_{slot}"),
                format!("android/vendor_boot_v{vendor_ver}_{slot}.img"),
            ),
        ];
        parts.extend_from_slice(additional_parts);
        test_android_load_verify_fixup_v3_or_v4(
            slot,
            &parts,
            &vbmeta,
            expected_vendor_bootconfig,
            additional_expected_fdt_properties,
            boot_ver > 3 || vendor_ver > 3,
            TestVbmetaKey::Rsa4096,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_no_init_boot_slot_a() {
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(
            3,
            3,
            'a',
            "",
            &[],
            EXPECTED_FDT_PROPS,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_no_init_boot_dtbo_slot_a() {
        let parts = &[("dtbo_a".into(), "android/dtbo_a.img".into())];
        let fdt_prop = Vec::from([EXPECTED_FDT_PROPS, EXPECTED_DTBO_PROPS_A].concat());
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(3, 3, 'a', "", parts, &fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_no_init_boot_slot_b() {
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(
            3,
            3,
            'a',
            "",
            &[],
            EXPECTED_FDT_PROPS,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_no_init_boot_dtbo_slot_b() {
        let parts = &[("dtbo_b".into(), "android/dtbo_b.img".into())];
        let fdt_prop = Vec::from([EXPECTED_FDT_PROPS, EXPECTED_DTBO_PROPS_B].concat());
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(3, 3, 'b', "", parts, &fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_no_init_boot_slot_a() {
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(
            4,
            3,
            'a',
            "",
            &[],
            EXPECTED_FDT_PROPS,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_no_init_boot_dtbo_slot_a() {
        let parts = &[("dtbo_a".into(), "android/dtbo_a.img".into())];
        let fdt_prop = Vec::from([EXPECTED_FDT_PROPS, EXPECTED_DTBO_PROPS_A].concat());
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(4, 3, 'a', "", parts, &fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_no_init_boot_slot_b() {
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(
            4,
            3,
            'a',
            "",
            &[],
            EXPECTED_FDT_PROPS,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_no_init_boot_dtbo_slot_b() {
        let parts = &[("dtbo_b".into(), "android/dtbo_b.img".into())];
        let fdt_prop = Vec::from([EXPECTED_FDT_PROPS, EXPECTED_DTBO_PROPS_B].concat());
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(4, 3, 'b', "", parts, &fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_no_init_boot_slot_a() {
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(
            3,
            4,
            'a',
            config,
            &[],
            EXPECTED_FDT_PROPS,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_no_init_boot_dtbo_slot_a() {
        let parts = &[("dtbo_a".into(), "android/dtbo_a.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        let fdt_prop = Vec::from([EXPECTED_FDT_PROPS, EXPECTED_DTBO_PROPS_A].concat());
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(3, 4, 'a', config, parts, &fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_no_init_boot_slot_b() {
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(
            3,
            4,
            'a',
            config,
            &[],
            EXPECTED_FDT_PROPS,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_no_init_boot_dtbo_slot_b() {
        let parts = &[("dtbo_b".into(), "android/dtbo_b.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        let fdt_prop = Vec::from([EXPECTED_FDT_PROPS, EXPECTED_DTBO_PROPS_B].concat());
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(3, 4, 'b', config, parts, &fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_no_init_boot_slot_a() {
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(
            4,
            4,
            'a',
            config,
            &[],
            EXPECTED_FDT_PROPS,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_no_init_boot_dtbo_slot_a() {
        let parts = &[("dtbo_a".into(), "android/dtbo_a.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        let fdt_prop = Vec::from([EXPECTED_FDT_PROPS, EXPECTED_DTBO_PROPS_A].concat());
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(4, 4, 'a', config, parts, &fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_no_init_boot_slot_b() {
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(
            4,
            4,
            'a',
            config,
            &[],
            EXPECTED_FDT_PROPS,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_no_init_boot_dtbo_slot_b() {
        let parts = &[("dtbo_b".into(), "android/dtbo_b.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        let fdt_prop = Vec::from([EXPECTED_FDT_PROPS, EXPECTED_DTBO_PROPS_B].concat());
        test_android_load_verify_fixup_v3_or_v4_no_init_boot(4, 4, 'b', config, parts, &fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_pqc_mldsa65_slot_a() {
        test_android_load_verify_fixup_v3_or_v4(
            'a',
            &[
                (String::from("boot_a"), String::from("android/boot_v4_a.img")),
                (String::from("vendor_boot_a"), String::from("android/vendor_boot_v4_a.img")),
            ],
            "android/vbmeta_v4_v4_mldsa65_a.img",
            TEST_VENDOR_BOOTCONFIG,
            EXPECTED_FDT_PROPS,
            true,
            TestVbmetaKey::Mldsa65,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_pqc_mldsa87_slot_a() {
        test_android_load_verify_fixup_v3_or_v4(
            'a',
            &[
                (String::from("boot_a"), String::from("android/boot_v4_a.img")),
                (String::from("vendor_boot_a"), String::from("android/vendor_boot_v4_a.img")),
            ],
            "android/vbmeta_v4_v4_mldsa87_a.img",
            TEST_VENDOR_BOOTCONFIG,
            EXPECTED_FDT_PROPS,
            true,
            TestVbmetaKey::Mldsa87,
        );
    }

    /// Helper for testing `android_load_verify_fixup` with dttable vendor_boot
    fn test_android_load_verify_fixup_v4_vendor_boot_dttable(
        slot: char,
        expected_vendor_bootconfig: &str,
        additional_parts: &[(String, String)],
        additional_expected_fdt_properties: &[(&str, &CStr, Option<&[u8]>)],
    ) {
        let vbmeta = format!("android/vbmeta_v4_dttable_{slot}.img");
        let mut parts = vec![
            (format!("boot_{slot}"), format!("android/boot_v4_{slot}.img")),
            (format!("vendor_boot_{slot}"), format!("android/vendor_boot_v4_dttable_{slot}.img")),
        ];
        parts.extend_from_slice(additional_parts);
        test_android_load_verify_fixup_v3_or_v4(
            slot,
            &parts,
            &vbmeta,
            expected_vendor_bootconfig,
            additional_expected_fdt_properties,
            true,
            TestVbmetaKey::Rsa4096,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_no_init_boot_slot_dttable_vendor_boot_a() {
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v4_vendor_boot_dttable('a', config, &[], EXPECTED_FDT_PROPS);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_no_init_boot_slot_dttable_vendor_boot_b() {
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v4_vendor_boot_dttable('b', config, &[], EXPECTED_FDT_PROPS);
    }

    /// Helper for testing `android_load_verify_fixup` for v3/v4 boot image with init_boot.
    fn test_android_load_verify_fixup_v3_or_v4_init_boot(
        boot_ver: u32,
        vendor_ver: u32,
        slot: char,
        expected_vendor_bootconfig: &str,
        additional_parts: &[(String, String)],
        additional_expected_fdt_properties: &[(&str, &CStr, Option<&[u8]>)],
    ) {
        let vbmeta = format!("android/vbmeta_v{boot_ver}_v{vendor_ver}_init_boot_{slot}.img");
        let mut parts = vec![
            (format!("boot_{slot}"), format!("android/boot_no_ramdisk_v{boot_ver}_{slot}.img")),
            (
                format!("vendor_boot_{slot}"),
                format!("android/vendor_boot_v{vendor_ver}_{slot}.img"),
            ),
            (format!("init_boot_{slot}"), format!("android/init_boot_{slot}.img")),
        ];
        parts.extend_from_slice(additional_parts);
        test_android_load_verify_fixup_v3_or_v4(
            slot,
            &parts,
            &vbmeta,
            expected_vendor_bootconfig,
            additional_expected_fdt_properties,
            true, // init_boot implies Android 13+.
            TestVbmetaKey::Rsa4096,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_init_boot_slot_a() {
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 3, 'a', "", &[], EXPECTED_FDT_PROPS);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_init_boot_dtbo_slot_a() {
        let parts = &[("dtbo_a".into(), "android/dtbo_a.img".into())];
        let fdt_prop = Vec::from([EXPECTED_FDT_PROPS, EXPECTED_DTBO_PROPS_A].concat());
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 3, 'a', "", parts, &fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_init_boot_slot_b() {
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 3, 'a', "", &[], EXPECTED_FDT_PROPS);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v3_init_boot_dtbo_slot_b() {
        let parts = &[("dtbo_b".into(), "android/dtbo_b.img".into())];
        let fdt_prop = Vec::from([EXPECTED_FDT_PROPS, EXPECTED_DTBO_PROPS_B].concat());
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 3, 'b', "", parts, &fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_init_boot_slot_a() {
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 3, 'a', "", &[], EXPECTED_FDT_PROPS);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_init_boot_dtbo_slot_a() {
        let parts = &[("dtbo_a".into(), "android/dtbo_a.img".into())];
        let fdt_prop = Vec::from([EXPECTED_FDT_PROPS, EXPECTED_DTBO_PROPS_A].concat());
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 3, 'a', "", parts, &fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_init_boot_slot_b() {
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 3, 'a', "", &[], EXPECTED_FDT_PROPS);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v3_init_boot_dtbo_slot_b() {
        let parts = &[("dtbo_b".into(), "android/dtbo_b.img".into())];
        let fdt_prop = Vec::from([EXPECTED_FDT_PROPS, EXPECTED_DTBO_PROPS_B].concat());
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 3, 'b', "", parts, &fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_init_boot_slot_a() {
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_init_boot(
            3,
            4,
            'a',
            config,
            &[],
            EXPECTED_FDT_PROPS,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_init_boot_dtbo_slot_a() {
        let parts = &[("dtbo_a".into(), "android/dtbo_a.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        let fdt_prop = Vec::from([EXPECTED_FDT_PROPS, EXPECTED_DTBO_PROPS_A].concat());
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 4, 'a', config, parts, &fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_init_boot_slot_b() {
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_init_boot(
            3,
            4,
            'a',
            config,
            &[],
            EXPECTED_FDT_PROPS,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_v3_v4_init_boot_dtbo_slot_b() {
        let parts = &[("dtbo_b".into(), "android/dtbo_b.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        let fdt_prop = Vec::from([EXPECTED_FDT_PROPS, EXPECTED_DTBO_PROPS_B].concat());
        test_android_load_verify_fixup_v3_or_v4_init_boot(3, 4, 'b', config, parts, &fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_init_boot_slot_a() {
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_init_boot(
            4,
            4,
            'a',
            config,
            &[],
            EXPECTED_FDT_PROPS,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_init_boot_dtbo_slot_a() {
        let parts = &[("dtbo_a".into(), "android/dtbo_a.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        let fdt_prop = Vec::from([EXPECTED_FDT_PROPS, EXPECTED_DTBO_PROPS_A].concat());
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 4, 'a', config, parts, &fdt_prop);
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_init_boot_slot_b() {
        let config = TEST_VENDOR_BOOTCONFIG;
        test_android_load_verify_fixup_v3_or_v4_init_boot(
            4,
            4,
            'a',
            config,
            &[],
            EXPECTED_FDT_PROPS,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_v4_v4_init_boot_dtbo_slot_b() {
        let parts = &[("dtbo_b".into(), "android/dtbo_b.img".into())];
        let config = TEST_VENDOR_BOOTCONFIG;
        let fdt_prop = Vec::from([EXPECTED_FDT_PROPS, EXPECTED_DTBO_PROPS_B].concat());
        test_android_load_verify_fixup_v3_or_v4_init_boot(4, 4, 'b', config, parts, &fdt_prop);
    }

    /// Helper for testing v4 boot image with different kernel compression.
    fn test_android_load_verify_boot_v4_compression_slot(compression: &str) {
        let vbmeta = format!("android/vbmeta_v4_{compression}_a.img");
        let parts = vec![
            (format!("boot_a"), format!("android/boot_v4_{compression}_a.img")),
            (format!("vendor_boot_a"), format!("android/vendor_boot_v4_a.img")),
            (format!("vbmeta_a"), vbmeta.clone()),
        ];
        test_android_load_verify_fixup(
            slot('a'),
            &parts,
            &[],
            false,
            0,
            &read_test_data(format!("android/gki_boot_{compression}_kernel_uncompressed")),
            &expected_v3_v4_ramdisk('a'),
            &make_expected_bootconfig(
                &parts,
                Some(&vbmeta),
                false,
                BootStateColor::Green,
                'a',
                TEST_VENDOR_BOOTCONFIG,
                FakeGblOps::GBL_TEST_BOOTCONFIG,
                TestVbmetaKey::Rsa4096,
            ),
            &format!("{EXPECTED_V3_V4_CMDLINE} fixup"),
            &[],
        )
    }

    #[test]
    fn test_android_load_verify_gzip_boot_v4_vendor_v4_slot_a() {
        test_android_load_verify_boot_v4_compression_slot("gz")
    }

    #[test]
    fn test_android_load_verify_lz4_boot_v4_vendor_v4_slot_a() {
        test_android_load_verify_boot_v4_compression_slot("lz4")
    }

    fn test_android_load_verify_fixup_fails_if_vbmeta_missing_partitions(unlocked: bool) {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("android/boot_no_ramdisk_v4_a.img"));
        storage.add_raw_device(c"vendor_boot_a", read_test_data("android/vendor_boot_v4_a.img"));
        storage.add_raw_device(c"init_boot_a", read_test_data("android/init_boot_a.img"));
        // vbmeta_noop.img has no partition descriptors. Thus nothing should be loaded by avb.
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_noop.img"));
        let mut ops = FakeGblOps::new(&storage);
        ops.avb_device_status.is_unlocked = unlocked;
        ops.avb_ops.rollbacks = HashMap::from([(TEST_ROLLBACK_INDEX_LOCATION, Ok(0))]);
        let mut out_status = None;
        let mut handler = |status,
                           _: Option<&CStr>,
                           _: Option<Vec<AvbProperty<'_>>>,
                           _: Option<Vec<AvbPartition<'_>>>| {
            out_status = Some(status);
            Ok(())
        };
        ops.avb_handle_verification_result = Some(&mut handler);
        ops.avb_key_validation_status = Some(Ok(KeyValidationStatus::Valid));
        let mut load = AlignedBuffer::new(64 * 1024 * 1024, KERNEL_ALIGNMENT);
        assert!(android_load_verify_fixup(
            &mut ops,
            Some(slot('a')),
            false,
            (&mut load[..]).into()
        )
        .is_err());
    }

    #[test]
    fn test_android_load_verify_fixup_fails_if_vbmeta_missing_partitions_unlocked() {
        test_android_load_verify_fixup_fails_if_vbmeta_missing_partitions(true)
    }

    #[test]
    fn test_android_load_verify_fixup_fails_if_vbmeta_missing_partitions_locked() {
        test_android_load_verify_fixup_fails_if_vbmeta_missing_partitions(false)
    }

    #[test]
    fn test_android_load_verify_fixup_with_vendor_kernel_boot() {
        let parts = vec![
            ("boot_a".into(), "android/boot_no_ramdisk_v4_a.img".into()),
            ("vendor_kernel_boot_a".into(), "android/vendor_kernel_boot_a.img".into()),
            ("vendor_boot_a".into(), "android/vendor_boot_v4_a.img".into()),
            ("init_boot_a".into(), "android/init_boot_a.img".into()),
        ];
        test_android_load_verify_fixup_success(
            'a',
            &parts,
            "android/vbmeta_v4_v4_init_boot_a.img",
            &read_test_data("android/kernel_a.img"),
            &[
                read_test_data("android/vendor_ramdisk_a.img"),
                read_test_data("android/vendor_kernel_a.img"),
                read_test_data("android/generic_ramdisk_a.img"),
            ]
            .concat(),
            TEST_VENDOR_BOOTCONFIG,
            EXPECTED_V3_V4_CMDLINE,
            &[("/chosen", c"vendor_kernel", Some(b"1\0"))],
            true,
            TestVbmetaKey::Rsa4096,
        );
    }

    #[test]
    fn test_android_load_verify_fixup_with_partition_buffers() {
        let mut storage = FakeGblOpsStorage::default();
        // Zeroes only. Will be provided via preloaded buffer.
        storage.add_raw_device(c"boot_a", vec![0; 1024]);
        // Zeroes only. Will be provided via preloaded buffer.
        storage.add_raw_device(c"vendor_kernel_boot_a", vec![0; 1024]);
        storage.add_raw_device(c"vendor_boot_a", read_test_data("android/vendor_boot_v4_a.img"));
        storage.add_raw_device(c"init_boot_a", read_test_data("android/init_boot_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_v4_v4_init_boot_a.img"));

        let image_buffers: Vec<(LoadPartition, RefCell<Vec<u8>>, bool)> = vec![
            // Preloaded.
            (LoadPartition::Boot, read_test_data("android/boot_no_ramdisk_v4_a.img").into(), true),
            (
                LoadPartition::VendorKernelBoot,
                read_test_data("android/vendor_kernel_boot_a.img").into(),
                true,
            ),
            // Designated load
            (
                LoadPartition::VendorBoot,
                vec![0u8; read_test_data("android/vendor_boot_v4_a.img").len()].into(),
                false,
            ),
            (
                LoadPartition::InitBoot,
                vec![0u8; read_test_data("android/init_boot_a.img").len()].into(),
                false,
            ),
        ];
        let vendor_boot_addr = image_buffers[2].1.borrow_mut().as_ptr_range();
        let init_boot_addr = image_buffers[3].1.borrow_mut().as_ptr_range();

        let get_partition_buffer_handler = |img: LoadPartition| {
            let (_, buf, pre) = image_buffers.iter().find(|v| v.0 == img).ok_or(Error::NotFound)?;
            match pre {
                true => Ok(PartitionBuffer::Preloaded(into_refmut_bytes(buf.borrow_mut()))),
                _ => Ok(PartitionBuffer::Designated(into_refmut_bytes(buf.borrow_mut()))),
            }
        };

        let mut sync_partition_called = false;
        const TEST_FDT_FIXUP: &str = "fixup-by-sync-partition-buffer";
        // Not newline-terminated: `finalize_bootconfig` must add the newline itself.
        const TEST_BOOTCONFIG_FIXUP: &str = "fixup-by-sync-partition-buffer=1";
        let mut sync_partition_buffer_handler = |ops: &mut FakeGblOps, sync_preloaded: bool| {
            assert!(!sync_preloaded);
            // Checks that this is called after images are loaded.
            // Designated buffers are loaded with the correct image.
            assert_eq!(
                *image_buffers[2].1.borrow_mut(),
                read_test_data("android/vendor_boot_v4_a.img")
            );
            assert_eq!(vendor_boot_addr, image_buffers[2].1.borrow_mut().as_ptr_range());
            assert_eq!(*image_buffers[3].1.borrow_mut(), read_test_data("android/init_boot_a.img"));
            assert_eq!(init_boot_addr, image_buffers[3].1.borrow_mut().as_ptr_range());

            // Override test custom FDT/bootconifg fixup. Checks that this is called before final
            // FDT/bootconfig fixup.
            ops.test_custom_fdt_fixup = Some(TEST_FDT_FIXUP.into());
            ops.test_custom_bootconfig_fixup = Some(TEST_BOOTCONFIG_FIXUP.into());

            sync_partition_called = true;
            Ok(())
        };

        let mut ops = default_test_gbl_ops(&storage);
        ops.get_partition_buffer_handler = Some(&get_partition_buffer_handler);
        ops.sync_partition_buffer_handler = Some(&mut sync_partition_buffer_handler);

        let mut load = AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let (ramdisk, fdt, kernel, _) =
            android_load_verify_fixup(&mut ops, Some(slot('a')), false, (&mut load[..]).into())
                .unwrap();

        let expected_bootconfig = make_expected_bootconfig(
            &vec![
                ("boot_a".into(), "android/boot_no_ramdisk_v4_a.img".into()),
                ("vendor_kernel_boot_a".into(), "android/vendor_kernel_boot_a.img".into()),
                ("vendor_boot_a".into(), "android/vendor_boot_v4_a.img".into()),
                ("init_boot_a".into(), "android/init_boot_a.img".into()),
            ],
            Some("android/vbmeta_v4_v4_init_boot_a.img"),
            false,
            BootStateColor::Green,
            'a',
            TEST_VENDOR_BOOTCONFIG,
            &format!("{TEST_BOOTCONFIG_FIXUP}\n"),
            TestVbmetaKey::Rsa4096,
        );
        let expected_ramdisk = &[
            read_test_data("android/vendor_ramdisk_a.img"),
            read_test_data("android/vendor_kernel_a.img"),
            read_test_data("android/generic_ramdisk_a.img"),
        ]
        .concat();
        check_ramdisk(ramdisk, expected_ramdisk, &expected_bootconfig);
        assert_eq!(kernel, read_test_data("android/kernel_a.img"));

        // sync_partition_buffer is called and can affect fixup.
        assert_eq!(
            Fdt::new(fdt).unwrap().get_property("/chosen", FakeGblOps::TEST_CUSTOM_FDT_FIXUP_PROP),
            Ok(TEST_FDT_FIXUP.as_bytes())
        );
        assert!(sync_partition_called);
    }

    /// Helper for checking V2 image loaded from slot A and in normal mode.
    pub(crate) fn checks_loaded_v2_slot_a_normal_mode(ramdisk: &[u8], kernel: &[u8]) {
        let expected_bootconfig = ExpectedBootconfigBuilder::new()
            .vbmeta_size(read_test_data("android/vbmeta_v2_a.img").len())
            .digest(read_test_data_as_str("android/vbmeta_v2_a.digest.txt"))
            .partition_digest("boot", read_test_data_as_str("android/vbmeta_v2_a.boot.digest.txt"))
            .public_key_digest(TestVbmetaKey::Rsa4096)
            .slot('a')
            .dtb_idx(0)
            .dtb_source("boot")
            .extra(FakeGblOps::GBL_TEST_BOOTCONFIG)
            .build();
        check_ramdisk(
            ramdisk,
            &read_test_data("android/generic_ramdisk_a.img"),
            &expected_bootconfig,
        );
        assert_eq!(kernel, read_test_data("android/kernel_a.img"));
    }

    /// Helper for checking V2 image loaded in slotless and normal mode.
    pub(crate) fn checks_loaded_v2_slotless_normal_mode(ramdisk: &[u8], kernel: &[u8]) {
        let expected_bootconfig = ExpectedBootconfigBuilder::new()
            .vbmeta_size(read_test_data("android/vbmeta_v2_a.img").len())
            .digest(read_test_data_as_str("android/vbmeta_v2_a.digest.txt"))
            .partition_digest("boot", read_test_data_as_str("android/vbmeta_v2_a.boot.digest.txt"))
            .public_key_digest(TestVbmetaKey::Rsa4096)
            .dtb_idx(0)
            .dtb_source("boot")
            .extra(FakeGblOps::GBL_TEST_BOOTCONFIG)
            .build();
        check_ramdisk(
            ramdisk,
            &read_test_data("android/generic_ramdisk_a.img"),
            &expected_bootconfig,
        );
        assert_eq!(kernel, read_test_data("android/kernel_a.img"));
    }

    /// Helper for checking V2 image loaded from slot A and in unlocked mode.
    pub(crate) fn checks_loaded_v2_slot_a_unlocked_mode(ramdisk: &[u8], kernel: &[u8]) {
        let expected_bootconfig = ExpectedBootconfigBuilder::new()
            .vbmeta_size(read_test_data("android/vbmeta_v2_a.img").len())
            .digest(read_test_data_as_str("android/vbmeta_v2_a.digest.txt"))
            .partition_digest("boot", read_test_data_as_str("android/vbmeta_v2_a.boot.digest.txt"))
            .public_key_digest(TestVbmetaKey::Rsa4096)
            .slot('a')
            .dtb_idx(0)
            .dtb_source("boot")
            .unlocked(true)
            .color(BootStateColor::Orange)
            .extra(FakeGblOps::GBL_TEST_BOOTCONFIG)
            .build();
        check_ramdisk(
            ramdisk,
            &read_test_data("android/generic_ramdisk_a.img"),
            &expected_bootconfig,
        );
        assert_eq!(kernel, read_test_data("android/kernel_a.img"));
    }

    /// Helper for checking V2 image loaded from slot A and in recovery mode.
    fn checks_loaded_v2_slot_a_recovery_mode(ramdisk: &[u8], kernel: &[u8]) {
        let expected_bootconfig = ExpectedBootconfigBuilder::new()
            .vbmeta_size(read_test_data("android/vbmeta_v2_a.img").len())
            .digest(read_test_data_as_str("android/vbmeta_v2_a.digest.txt"))
            .partition_digest("boot", read_test_data_as_str("android/vbmeta_v2_a.boot.digest.txt"))
            .public_key_digest(TestVbmetaKey::Rsa4096)
            .force_normal_boot(false)
            .slot('a')
            .dtb_idx(0)
            .dtb_source("boot")
            .extra(FakeGblOps::GBL_TEST_BOOTCONFIG)
            .build();
        check_ramdisk(
            ramdisk,
            &read_test_data("android/generic_ramdisk_a.img"),
            &expected_bootconfig,
        );
        assert_eq!(kernel, read_test_data("android/kernel_a.img"));
    }

    /// Helper for getting default FakeGblOps for tests.
    pub(crate) fn default_test_gbl_ops(storage: &FakeGblOpsStorage) -> FakeGblOps<'_> {
        let mut ops = FakeGblOps::new(&storage);
        ops.avb_ops.rollbacks = HashMap::from([(TEST_ROLLBACK_INDEX_LOCATION, Ok(0))]);
        ops.avb_key_validation_status = Some(Ok(KeyValidationStatus::Valid));
        ops
    }

    #[test]
    fn test_android_load_verify_fixup_recovery_mode() {
        // Recovery mode is specified by the absence of bootconfig arg
        // "androidboot.force_normal_boot=1\n" and therefore independent of image versions. We can
        // pick any image version for test. Use v2 for simplicity.
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("android/boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_v2_a.img"));

        let mut ops = default_test_gbl_ops(&storage);
        let mut load = AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let (ramdisk, _, kernel, _) =
            android_load_verify_fixup(&mut ops, Some(slot('a')), true, (&mut load[..]).into())
                .unwrap();
        checks_loaded_v2_slot_a_recovery_mode(ramdisk, kernel)
    }

    const TEST_PVMFW_FILL_VALUE: u8 = 0xAB;
    const TEST_PVMFW_FILL_COUNT: usize = 0xC00;

    /// Helper for testing pvmfw load.
    fn test_android_load_verify_fixup_pvmfw_load(boot_buffer: BootBuffer) -> usize {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("android/boot_v2_a.img"));
        // We are just interested in pvmfw load behavior. Don't care about avb verification.
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_disabled.img"));
        let (pvmfw_part, min_exp_size) =
            dummy_pvmfw_partition(TEST_PVMFW_FILL_VALUE, TEST_PVMFW_FILL_COUNT);
        storage.add_raw_device(c"pvmfw_a", pvmfw_part);

        let mut ops = default_test_gbl_ops(&storage);
        // Rollback required by `vbmeta_disabled.img`.
        ops.avb_ops.rollbacks = HashMap::from([(0, Ok(0))]);
        ops.avf_is_supported = true;
        ops.avb_device_status.is_unlocked = true;
        ops.avf_vendor_dice_handover = Some(&DUMMY_VENDOR_HANDOVER[..]);
        let (ramdisk, fdt, _, _) =
            android_load_verify_fixup(&mut ops, Some(slot('a')), false, boot_buffer).unwrap();

        let bootconfig = extract_bootconfig(ramdisk).unwrap();
        bootconfig.find(&format!("{PROTECTED_PROP}=1")).unwrap();
        bootconfig.find(&format!("{UNPROTECTED_PROP}=1")).unwrap();

        let fdt = Fdt::new(&fdt[..]).unwrap();
        assert_eq!(
            fdt.get_property("/reserved-memory/pkvm_guest_firmware", std_props::COMPATIBLE)
                .unwrap(),
            b"linux,pkvm-guest-firmware-memory\0",
        );
        assert_eq!(
            fdt.get_property("/reserved-memory/pkvm_guest_firmware", std_props::NO_MAP).unwrap(),
            &[]
        );
        let reg_prop =
            fdt.get_property("/reserved-memory/pkvm_guest_firmware", std_props::REG).unwrap();
        let pvmfw_addr = usize::from_be_bytes(reg_prop[..8].try_into().unwrap());
        assert_eq!(pvmfw_addr % PVMFW_DATA_ALIGNMENT, 0);

        let mut length_bytes = reg_prop[8..].to_vec();
        // The length field is sometimes less than 8 bytes. Converts to little endian and resizes
        // to 8 bytes.
        length_bytes.reverse();
        length_bytes.resize(8, 0);
        assert!(usize::from_le_bytes(length_bytes.try_into().unwrap()) >= min_exp_size);

        pvmfw_addr
    }

    #[test]
    fn test_android_load_verify_fixup_pvmfw_load_designated() {
        let general = &mut AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let pvmfw_data = &mut AlignedBuffer::new(32 * 1024, PVMFW_DATA_ALIGNMENT);
        let boot_buffer = BootBuffer::new(general, None, None, None, Some(pvmfw_data));
        let pvmfw_addr = test_android_load_verify_fixup_pvmfw_load(boot_buffer);

        let expected_addr = pvmfw_data.as_ptr() as usize;
        assert_eq!(pvmfw_addr, expected_addr);
        assert!(&pvmfw_data[..TEST_PVMFW_FILL_COUNT].iter().all(|&b| b == TEST_PVMFW_FILL_VALUE));
    }

    #[test]
    fn test_android_load_verify_fixup_pvmfw_load_general() {
        let general = &mut AlignedBuffer::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let general_start = general.as_ptr() as usize;
        let general_end = general_start + general.len();
        let boot_buffer = BootBuffer::new(&mut general[..], None, None, None, None);
        let pvmfw_addr = test_android_load_verify_fixup_pvmfw_load(boot_buffer);

        assert!(pvmfw_addr >= general_start && pvmfw_addr < general_end);
        let off = pvmfw_addr - general_start;
        assert!(general[off..][..TEST_PVMFW_FILL_COUNT]
            .iter()
            .all(|&b| b == TEST_PVMFW_FILL_VALUE));
    }

    #[test]
    fn test_android_main_bcb_normal_mode() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("android/boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        let mut load_buffer = vec![0u8; 8 * 1024 * 1024];
        let load_buffer = (&mut load_buffer[..]).into();
        let (ramdisk, _, kernel, _) = android_main(&mut ops, load_buffer, |_| {}).unwrap();
        checks_loaded_v2_slot_a_normal_mode(ramdisk, kernel)
    }

    #[test]
    fn test_android_main_bcb_recovery_mode() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("android/boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        ops.write_to_partition_sync("misc", 0, &mut b"boot-recovery".to_vec()).unwrap();
        let mut load_buffer = vec![0u8; 8 * 1024 * 1024];
        let load_buffer = (&mut load_buffer[..]).into();
        let (ramdisk, _, kernel, _) = android_main(&mut ops, load_buffer, |_| {}).unwrap();

        let bcb = read_bootloader_message(&mut ops).unwrap();
        assert_eq!(bcb.boot_mode(), Ok(AndroidBootMode::Recovery));
        checks_loaded_v2_slot_a_recovery_mode(ramdisk, kernel)
    }

    /// Helper for checking V2 image loaded from slot B and in normal mode.
    pub(crate) fn checks_loaded_v2_slot_b_normal_mode(ramdisk: &[u8], kernel: &[u8]) {
        let expected_bootconfig = ExpectedBootconfigBuilder::new()
            .vbmeta_size(read_test_data("android/vbmeta_v2_b.img").len())
            .digest(read_test_data_as_str("android/vbmeta_v2_b.digest.txt"))
            .partition_digest("boot", read_test_data_as_str("android/vbmeta_v2_b.boot.digest.txt"))
            .public_key_digest(TestVbmetaKey::Rsa4096)
            .slot('b')
            .dtb_idx(0)
            .dtb_source("boot")
            .extra(FakeGblOps::GBL_TEST_BOOTCONFIG)
            .build();
        check_ramdisk(
            ramdisk,
            &read_test_data("android/generic_ramdisk_b.img"),
            &expected_bootconfig,
        );
        assert_eq!(kernel, read_test_data("android/kernel_b.img"));
    }

    /// Helper for checking V2 image loaded from slot B and in unlocked mode.
    pub(crate) fn checks_loaded_v2_slot_b_unlocked_mode(ramdisk: &[u8], kernel: &[u8]) {
        let expected_bootconfig = ExpectedBootconfigBuilder::new()
            .vbmeta_size(read_test_data("android/vbmeta_v2_b.img").len())
            .digest(read_test_data_as_str("android/vbmeta_v2_b.digest.txt"))
            .partition_digest("boot", read_test_data_as_str("android/vbmeta_v2_b.boot.digest.txt"))
            .public_key_digest(TestVbmetaKey::Rsa4096)
            .slot('b')
            .dtb_idx(0)
            .dtb_source("boot")
            .unlocked(true)
            .color(BootStateColor::Orange)
            .extra(FakeGblOps::GBL_TEST_BOOTCONFIG)
            .build();
        check_ramdisk(
            ramdisk,
            &read_test_data("android/generic_ramdisk_b.img"),
            &expected_bootconfig,
        );
        assert_eq!(kernel, read_test_data("android/kernel_b.img"));
    }

    #[test]
    fn test_android_main_slotted_gbl_slot_a() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("android/boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        let mut load_buffer = vec![0u8; 8 * 1024 * 1024];
        let load_buffer = (&mut load_buffer[..]).into();
        let (ramdisk, _, kernel, _) = android_main(&mut ops, load_buffer, |_| {}).unwrap();
        checks_loaded_v2_slot_a_normal_mode(ramdisk, kernel)
    }

    #[test]
    fn test_android_main_slotted_gbl_slot_b() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_b", read_test_data("android/boot_v2_b.img"));
        storage.add_raw_device(c"vbmeta_b", read_test_data("android/vbmeta_v2_b.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        ops.current_slot = Some(Ok(1));

        let mut load_buffer = vec![0u8; 8 * 1024 * 1024];
        let load_buffer = (&mut load_buffer[..]).into();
        let (ramdisk, _, kernel, _) = android_main(&mut ops, load_buffer, |_| {}).unwrap();
        checks_loaded_v2_slot_b_normal_mode(ramdisk, kernel)
    }

    #[test]
    #[cfg(feature = "gbl_dev")]
    fn test_android_main_unsupported_slot_default_to_a() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("android/boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        ops.current_slot = Some(Err(Error::Unsupported));
        let mut load_buffer = vec![0u8; 8 * 1024 * 1024];
        let load_buffer = (&mut load_buffer[..]).into();
        let (ramdisk, _, kernel, _) = android_main(&mut ops, load_buffer, |_| {}).unwrap();
        checks_loaded_v2_slot_a_normal_mode(ramdisk, kernel)
    }

    /// Helper for testing that fastboot mode is triggered.
    fn test_fastboot_is_triggered<'a>(ops: &mut impl GblOps<'a>) {
        let listener: SharedTestListener = Default::default();
        let mut load_buffer = vec![0u8; 8 * 1024 * 1024];
        let load_buffer = (&mut load_buffer[..]).into();
        let (ramdisk, _, kernel, _) = android_main(ops, load_buffer, |fb| {
            listener.add_transport_input(b"getvar:max-fetch-size");
            listener.add_transport_input(b"continue");
            fb.run_n::<2>(&mut vec![0u8; 256 * 1024], &mut [&listener], Some(&listener));
        })
        .unwrap();

        assert_eq!(
            listener.transport_out_queue(),
            make_expected_transport_out(&[b"OKAY0x7fffffff", b"OKAY",]),
            "\nActual Transport output:\n{}",
            listener.dump_transport_out_queue()
        );

        checks_loaded_v2_slot_a_normal_mode(ramdisk, kernel);
    }

    #[test]
    fn test_android_main_bootonce_bootloader_bcb_command_is_cleared() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("android/boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);
        let mut ops = default_test_gbl_ops(&storage);
        ops.write_to_partition_sync("misc", 0, &mut b"bootonce-bootloader".to_vec()).unwrap();
        test_fastboot_is_triggered(&mut ops);

        let bcb = read_bootloader_message(&mut ops).unwrap();
        assert_eq!(
            bcb.boot_mode().unwrap(),
            AndroidBootMode::Normal,
            "BCB mode is expected to be cleared after bootonce-bootloader is handled"
        );
    }

    #[test]
    fn test_android_main_enter_fastboot_via_bcb() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("android/boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);
        let mut ops = default_test_gbl_ops(&storage);
        ops.write_to_partition_sync("misc", 0, &mut b"bootonce-bootloader".to_vec()).unwrap();
        test_fastboot_is_triggered(&mut ops);
    }

    #[test]
    fn test_android_main_enter_fastboot_via_get_one_shot_boot_mode() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("android/boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);
        let mut ops = default_test_gbl_ops(&storage);
        ops.one_shot_boot_mode = Some(OneShotBootMode::Bootloader);

        test_fastboot_is_triggered(&mut ops);
    }

    #[test]
    fn test_android_main_enter_fastboot_via_get_one_shot_boot_mode_recovery_via_bcb() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("android/boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);
        let mut ops = default_test_gbl_ops(&storage);
        ops.write_to_partition_sync("misc", 0, &mut b"boot-recovery".to_vec()).unwrap();
        ops.one_shot_boot_mode = Some(OneShotBootMode::Bootloader);
        let listener: SharedTestListener = Default::default();
        let mut load_buffer = vec![0u8; 8 * 1024 * 1024];

        let (ramdisk, _, kernel, _) = android_main(&mut ops, (&mut load_buffer[..]).into(), |fb| {
            listener.add_transport_input(b"getvar:max-fetch-size");
            listener.add_transport_input(b"continue");
            fb.run_n::<2>(&mut vec![0u8; 256 * 1024], &mut [&listener], Some(&listener));
        })
        .unwrap();

        assert_eq!(
            listener.transport_out_queue(),
            make_expected_transport_out(&[b"OKAY0x7fffffff", b"OKAY",]),
            "\nActual Transport output:\n{}",
            listener.dump_transport_out_queue()
        );
        let bcb = read_bootloader_message(&mut ops).unwrap();
        assert_eq!(bcb.boot_mode(), Ok(AndroidBootMode::Recovery));
        checks_loaded_v2_slot_a_recovery_mode(ramdisk, kernel)
    }

    #[test]
    fn test_android_main_enter_recovery_mode_via_get_one_shot_boot_mode() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("android/boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);
        let mut ops = default_test_gbl_ops(&storage);
        ops.write_to_partition_sync("misc", 0, &mut b"bootonce-bootloader".to_vec()).unwrap();
        ops.one_shot_boot_mode = Some(OneShotBootMode::Recovery);
        let mut load_buffer = vec![0u8; 8 * 1024 * 1024];

        let (ramdisk, _, kernel, _) =
            android_main(&mut ops, (&mut load_buffer[..]).into(), |_| {}).unwrap();

        let bcb = read_bootloader_message(&mut ops).unwrap();
        assert_eq!(bcb.boot_mode(), Ok(AndroidBootMode::Normal));
        checks_loaded_v2_slot_a_recovery_mode(ramdisk, kernel)
    }

    #[test]
    fn test_android_main_fastboot_boot() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);
        let mut ops = default_test_gbl_ops(&storage);
        ops.avb_device_status.is_unlocked = true;
        ops.one_shot_boot_mode = Some(OneShotBootMode::Bootloader);

        let listener: SharedTestListener = Default::default();
        let mut load_buffer = vec![0u8; 8 * 1024 * 1024];
        let load_buffer = (&mut load_buffer[..]).into();
        let (ramdisk, _, kernel, _) = android_main(&mut ops, load_buffer, |fb| {
            let data = read_test_data(format!("android/boot_v2_a.img"));
            listener.add_transport_input(format!("download:{:#x}", data.len()).as_bytes());
            listener.add_transport_input(&data);
            listener.add_transport_input(b"boot");
            listener.add_transport_input(b"continue");
            fb.run_n::<2>(&mut vec![0u8; 256 * 1024], &mut [&listener], Some(&listener));
        })
        .unwrap();

        assert_eq!(
            listener.transport_out_queue(),
            make_expected_transport_out(&[
                b"DATA00004000",
                b"OKAY",
                b"INFOBoot image as Android slot a",
                b"OKAY",
            ]),
            "\nActual Transport output:\n{}",
            listener.dump_transport_out_queue()
        );

        checks_loaded_v2_slot_a_unlocked_mode(ramdisk, kernel);
    }

    #[test]
    fn test_android_main_fastboot_boot_designated_buffers() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);
        let mut ops = default_test_gbl_ops(&storage);
        ops.avb_device_status.is_unlocked = true;
        ops.one_shot_boot_mode = Some(OneShotBootMode::Bootloader);

        let general = &mut AlignedBuffer::new(64 * 1024 * 1024, KERNEL_ALIGNMENT);
        let mut kernel = AlignedBuffer::<u8>::new(64 * 1024 * 1024, KERNEL_ALIGNMENT);
        let kernel_addr = kernel.as_ptr();
        let mut ramdisk = AlignedBuffer::<u8>::new(8 * 1024 * 1024, KERNEL_ALIGNMENT);
        let ramdisk_addr = ramdisk.as_ptr();
        let mut fdt = AlignedBuffer::<u8>::new(1 * 1024 * 1024, FDT_ALIGNMENT);
        let fdt_addr = fdt.as_ptr();
        let buffers =
            BootBuffer::new(general, Some(&mut kernel), Some(&mut ramdisk), Some(&mut fdt), None);
        let listener: SharedTestListener = Default::default();
        let (ramdisk, fdt, kernel, _) = android_main(&mut ops, buffers, |fb| {
            let data = read_test_data(format!("android/boot_v2_a.img"));
            listener.add_transport_input(format!("download:{:#x}", data.len()).as_bytes());
            listener.add_transport_input(&data);
            listener.add_transport_input(b"boot");
            listener.add_transport_input(b"continue");
            fb.run_n::<2>(&mut vec![0u8; 256 * 1024], &mut [&listener], Some(&listener));
        })
        .unwrap();

        assert_eq!(
            listener.transport_out_queue(),
            make_expected_transport_out(&[
                b"DATA00004000",
                b"OKAY",
                b"INFOBoot image as Android slot a",
                b"OKAY",
            ]),
            "\nActual Transport output:\n{}",
            listener.dump_transport_out_queue()
        );
        checks_loaded_v2_slot_a_unlocked_mode(ramdisk, kernel);
        assert_eq!(kernel.as_ptr(), kernel_addr);
        assert_eq!(ramdisk.as_ptr(), ramdisk_addr);
        assert_eq!(fdt.as_ptr(), fdt_addr);
    }

    #[test]
    fn test_android_main_reboot_if_set_active_to_different_slot() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);
        let mut ops = default_test_gbl_ops(&storage);
        ops.avb_device_status.is_unlocked = true;
        ops.one_shot_boot_mode = Some(OneShotBootMode::Bootloader);

        let listener: SharedTestListener = Default::default();
        let mut load_buffer = vec![0u8; 8 * 1024 * 1024];
        let load_buffer = (&mut load_buffer[..]).into();
        assert_eq!(
            android_main(&mut ops, load_buffer, |fb| {
                listener.add_transport_input(b"set_active:b");
                listener.add_transport_input(b"continue");
                fb.run_n::<2>(&mut vec![0u8; 256 * 1024], &mut [&listener], Some(&listener));
            })
            .unwrap_err(),
            Error::Aborted.into()
        );

        assert_eq!(
            listener.transport_out_queue(),
            make_expected_transport_out(&[b"OKAY", b"OKAY",]),
            "\nActual Transport output:\n{}",
            listener.dump_transport_out_queue()
        );
    }

    #[test]
    fn test_android_main_enter_fastboot_trigger_sync_preloaded_partition() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("android/boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        // Set up designated load buffer for boot_a image
        let img_len = read_test_data("android/boot_v2_a.img").len();
        let buf = RefCell::new(vec![0u8; img_len]);
        let get_partition_buffer_handler = |img: LoadPartition| match img {
            LoadPartition::Boot => {
                Ok(PartitionBuffer::Designated(into_refmut_bytes(buf.borrow_mut())))
            }
            _ => Err(Error::NotFound),
        };

        // Records the calls and inputs of `GblOps::sync_partitions_buffer()`.
        let mut traces = vec![];
        let mut sync_partition_buffer_handler = |_: &mut FakeGblOps, sync_preloaded: bool| {
            traces.push((sync_preloaded, buf.borrow_mut().clone()));
            Ok(())
        };

        let mut ops = default_test_gbl_ops(&storage);
        ops.get_partition_buffer_handler = Some(&get_partition_buffer_handler);
        ops.sync_partition_buffer_handler = Some(&mut sync_partition_buffer_handler);
        ops.one_shot_boot_mode = Some(OneShotBootMode::Bootloader);

        let listener: SharedTestListener = Default::default();
        let mut load_buffer = vec![0u8; 8 * 1024 * 1024];
        let load_buffer = (&mut load_buffer[..]).into();
        let (ramdisk, _, kernel, _) = android_main(&mut ops, load_buffer, |fb| {
            listener.add_transport_input(b"continue");
            fb.run_n::<2>(&mut vec![0u8; 256 * 1024], &mut [&listener], Some(&listener));
        })
        .unwrap();

        assert_eq!(
            listener.transport_out_queue(),
            make_expected_transport_out(&[b"OKAY",]),
            "\nActual Transport output:\n{}",
            listener.dump_transport_out_queue()
        );

        checks_loaded_v2_slot_a_normal_mode(ramdisk, kernel);

        assert_eq!(
            traces,
            vec![
                // Called with `sync_preloaded=true` due to fastboot, image not loaded yet.
                (true, vec![0u8; img_len]),
                // sync_preloaded = false, image loaded.
                (false, read_test_data("android/boot_v2_a.img")),
            ]
        );
    }

    #[test]
    fn test_android_main_fastboot_boot_always_sync_preloaded_partition() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        // Set up designated load buffer for boot_a image
        let img_len = read_test_data("android/boot_v2_a.img").len();
        let buf = RefCell::new(vec![0u8; img_len]);
        let get_partition_buffer_handler = |img: LoadPartition| match img {
            LoadPartition::Boot => {
                Ok(PartitionBuffer::Designated(into_refmut_bytes(buf.borrow_mut())))
            }
            _ => Err(Error::NotFound),
        };

        // Records the calls and inputs of `GblOps::sync_partitions_buffer()`.
        let mut traces = vec![];
        let mut sync_partition_buffer_handler = |_: &mut FakeGblOps, sync_preloaded: bool| {
            traces.push((sync_preloaded, buf.borrow_mut().clone()));
            Ok(())
        };

        let mut ops = default_test_gbl_ops(&storage);
        ops.avb_device_status.is_unlocked = true;
        ops.get_partition_buffer_handler = Some(&get_partition_buffer_handler);
        ops.sync_partition_buffer_handler = Some(&mut sync_partition_buffer_handler);
        ops.one_shot_boot_mode = Some(OneShotBootMode::Bootloader);

        let listener: SharedTestListener = Default::default();
        let mut load_buffer = vec![0u8; 8 * 1024 * 1024];
        let load_buffer = (&mut load_buffer[..]).into();
        let (ramdisk, _, kernel, _) = android_main(&mut ops, load_buffer, |fb| {
            let data = read_test_data(format!("android/boot_v2_a.img"));
            listener.add_transport_input(format!("download:{:#x}", data.len()).as_bytes());
            listener.add_transport_input(&data);
            listener.add_transport_input(b"boot");
            listener.add_transport_input(b"continue");
            fb.run_n::<2>(&mut vec![0u8; 256 * 1024], &mut [&listener], Some(&listener));
        })
        .unwrap();

        assert_eq!(
            listener.transport_out_queue(),
            make_expected_transport_out(&[
                b"DATA00004000",
                b"OKAY",
                b"INFOBoot image as Android slot a",
                b"OKAY",
            ]),
            "\nActual Transport output:\n{}",
            listener.dump_transport_out_queue()
        );

        checks_loaded_v2_slot_a_unlocked_mode(ramdisk, kernel);

        assert_eq!(
            traces,
            vec![
                // Called with `sync_preloaded=true` due to fastboot, images not loaded yet.
                (true, vec![0u8; img_len]),
                // Called with `sync_preloaded=false`, after images are loaded.
                (false, read_test_data("android/boot_v2_a.img")),
            ]
        );
    }

    #[test]
    fn test_android_main_fastboot_boot_items() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("android/boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        ops.one_shot_boot_mode = Some(OneShotBootMode::Bootloader);
        ops.avb_device_status.is_unlocked = true;
        let listener: SharedTestListener = Default::default();
        let mut load_buffer = vec![0u8; 8 * 1024 * 1024];
        let load_buffer = (&mut load_buffer[..]).into();
        let (ramdisk, fdt, kernel, _) = android_main(&mut ops, load_buffer, |fb| {
            listener.add_transport_input(b"oem gbl-add-cmdline gbl-fb-cmd-1=1");
            listener.add_transport_input(b"oem gbl-add-cmdline gbl-fb-cmd-2=1");
            listener.add_transport_input(b"oem gbl-add-bootconfig gbl-fb-config-1=1");
            listener.add_transport_input(b"oem gbl-add-bootconfig gbl-fb-config-2=1");
            let download_data = b"some test data";
            listener.add_transport_input(format!("download:{:#x}", download_data.len()).as_bytes());
            listener.add_transport_input(download_data);
            listener.add_transport_input(b"oem gbl-add-staged-data test");
            listener.add_transport_input(b"continue");
            fb.run_n::<2>(&mut vec![0u8; 256 * 1024], &mut [&listener], Some(&listener));
        })
        .unwrap();

        let expected_bootconfig = ExpectedBootconfigBuilder::new()
            .vbmeta_size(read_test_data("android/vbmeta_v2_a.img").len())
            .digest(read_test_data_as_str("android/vbmeta_v2_a.digest.txt"))
            .partition_digest("boot", read_test_data_as_str("android/vbmeta_v2_a.boot.digest.txt"))
            .public_key_digest(TestVbmetaKey::Rsa4096)
            .unlocked(true)
            .color(BootStateColor::Orange)
            .slot('a')
            .dtb_idx(0)
            .dtb_source("boot")
            .extra("gbl-fb-config-1=1\n")
            .extra("gbl-fb-config-2=1\n")
            .extra("gbl.blob.test=c29tZSB0ZXN0IGRhdGE=\n")
            .extra(FakeGblOps::GBL_TEST_BOOTCONFIG)
            .build();
        check_ramdisk(
            ramdisk,
            &read_test_data("android/generic_ramdisk_a.img"),
            &expected_bootconfig,
        );
        assert_eq!(kernel, read_test_data("android/kernel_a.img"));

        let fdt = Fdt::new(fdt).unwrap();
        from_utf8(fdt.get_property("/chosen", c"bootargs").unwrap())
            .unwrap()
            .find("gbl-fb-cmd-1=1 gbl-fb-cmd-2=1")
            .unwrap();
    }

    #[test]
    fn test_android_main_fastboot_boot_items_ignored_when_locked() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("android/boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        ops.one_shot_boot_mode = Some(OneShotBootMode::Bootloader);
        ops.avb_device_status.is_unlocked = true;
        let listener: SharedTestListener = Default::default();
        let mut load_buffer = vec![0u8; 8 * 1024 * 1024];
        let load_buffer = (&mut load_buffer[..]).into();
        let (ramdisk, fdt, kernel, _) = android_main(&mut ops, load_buffer, |fb| {
            listener.add_transport_input(b"oem gbl-add-cmdline gbl-fb-cmd-1=1");
            listener.add_transport_input(b"oem gbl-add-cmdline gbl-fb-cmd-2=1");
            listener.add_transport_input(b"oem gbl-add-bootconfig gbl-fb-config-1=1");
            listener.add_transport_input(b"oem gbl-add-bootconfig gbl-fb-config-2=1");
            let download_data = b"some test data";
            listener.add_transport_input(format!("download:{:#x}", download_data.len()).as_bytes());
            listener.add_transport_input(download_data);
            listener.add_transport_input(b"oem gbl-add-staged-data test");
            listener.add_transport_input(b"continue");
            let ops = fb.run_n::<2>(&mut vec![0u8; 256 * 1024], &mut [&listener], Some(&listener));
            // Simulate device re-lock from external channel.
            ops.avb_device_status.is_unlocked = false;
        })
        .unwrap();

        checks_loaded_v2_slot_a_normal_mode(ramdisk, kernel);
        let fdt = Fdt::new(fdt).unwrap();
        assert!(from_utf8(fdt.get_property("/chosen", c"bootargs").unwrap())
            .unwrap()
            .find("gbl-fb-cmd-1=1 gbl-fb-cmd-2=1")
            .is_none());
    }

    #[test]
    fn test_android_main_with_no_rng() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("android/boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        ops.get_random_bytes_error = Some(Error::NotFound);
        let mut load_buffer = vec![0u8; 8 * 1024 * 1024];
        let load_buffer = (&mut load_buffer[..]).into();
        let r = android_main(&mut ops, load_buffer, |_| {});

        cfg_if! {
            if #[cfg(feature = "gbl_dev")] {
                assert!(r.is_ok());
            } else {
                assert_eq!(r, Err(Error::NotFound.into()));
            }
        }
    }

    #[test]
    fn test_android_main_post_load_fastboot() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot_a", read_test_data("android/boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        ops.one_shot_boot_mode = Some(OneShotBootMode::Bootloader);
        ops.avb_device_status.is_unlocked = true;
        let listener: SharedTestListener = Default::default();
        let mut load_buffer = vec![0u8; 8 * 1024 * 1024];
        let load_buffer = (&mut load_buffer[..]).into();
        let res = android_main(&mut ops, load_buffer, |fb| {
            listener.add_transport_input(b"oem gbl-stage kernel");
            listener.add_transport_input(b"oem gbl-stage ramdisk");
            listener.add_transport_input(b"oem gbl-stage fdt");
            listener.add_transport_input(b"oem gbl-pause-fastboot-after-load");
            listener.add_transport_input(b"continue");
            listener.add_transport_input(b"oem gbl-stage kernel");
            listener.add_transport_input(b"upload");
            listener.add_transport_input(b"oem gbl-stage ramdisk");
            listener.add_transport_input(b"upload");
            listener.add_transport_input(b"oem gbl-stage fdt");
            listener.add_transport_input(b"upload");
            listener.add_transport_input(b"continue");
            fb.run_n::<2>(&mut vec![0u8; 256 * 1024], &mut [&listener], Some(&listener));
        });

        // Only dev builds can continue after stopping post-load, prod builds must reboot.
        match cfg!(feature = "gbl_dev") {
            true => assert!(res.is_ok()),
            false => assert_eq!(res.unwrap_err(), Error::Aborted.into()),
        }

        assert_eq!(
            listener.transport_out_queue(),
            make_expected_transport_out(&[
                b"FAILImages not loaded. Run \"oem gbl-pause-fastboot-after-load\"",
                b"FAILImages not loaded. Run \"oem gbl-pause-fastboot-after-load\"",
                b"FAILImages not loaded. Run \"oem gbl-pause-fastboot-after-load\"",
                b"OKAY",
                b"OKAY",
                b"OKAY",
                &listener.transport_out_queue()[6],
                &listener.transport_out_queue()[7],
                &listener.transport_out_queue()[8],
                b"OKAY",
                &listener.transport_out_queue()[10],
                &listener.transport_out_queue()[11],
                &listener.transport_out_queue()[12],
                b"OKAY",
                &listener.transport_out_queue()[14],
                &listener.transport_out_queue()[15],
                &listener.transport_out_queue()[16],
                b"OKAY",
            ]),
            "\nActual USB output:\n{}",
            listener.dump_transport_out_queue()
        );

        // Checks that we have uploaded a valid device tree.
        let fdt = &listener.transport_out_queue()[15];
        let fdt = fdt::Fdt::new(fdt).unwrap();
        fdt.get_property("/chosen", c"linux,initrd-start").unwrap();
        let kernel = listener.transport_out_queue()[7].to_vec();
        let ramdisk = listener.transport_out_queue()[11].to_vec();
        checks_loaded_v2_slot_a_unlocked_mode(&ramdisk, &kernel);
    }

    #[test]
    fn test_android_main_post_load_fastboot_load_failed() {
        let mut storage = FakeGblOpsStorage::default();
        let mut boot_img = read_test_data("android/boot_v2_a.img");
        boot_img[0] = !boot_img[0]; // Corrupt kernel magic bits to trigger boot failure.
        storage.add_raw_device(c"boot_a", boot_img);
        storage.add_raw_device(c"vbmeta_a", read_test_data("android/vbmeta_v1_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        ops.one_shot_boot_mode = Some(OneShotBootMode::Bootloader);
        ops.avb_device_status.is_unlocked = true;
        let listener: SharedTestListener = Default::default();
        let mut load_buffer = vec![0u8; 8 * 1024 * 1024];
        let load_buffer = (&mut load_buffer[..]).into();
        let res = android_main(&mut ops, load_buffer, |fb| {
            listener.add_transport_input(b"oem gbl-pause-fastboot-after-load");
            listener.add_transport_input(b"continue");
            listener.add_transport_input(b"oem gbl-stage kernel");
            listener.add_transport_input(b"oem gbl-stage ramdisk");
            listener.add_transport_input(b"oem gbl-stage fdt");
            listener.add_transport_input(b"continue");
            fb.run_n::<2>(&mut vec![0u8; 256 * 1024], &mut [&listener], Some(&listener));
        });

        match cfg!(feature = "gbl_dev") {
            // Dev build should attempt to continue and hit the bad magic error.
            true => assert_eq!(res.unwrap_err(), Error::BadMagic.into()),
            // Prod build should never attempt to continue at all.
            false => assert_eq!(res.unwrap_err(), Error::Aborted.into()),
        }

        assert_eq!(
            listener.transport_out_queue(),
            make_expected_transport_out(&[
                b"OKAY",
                b"OKAY",
                b"FAILLoad didn't succeed: UnificationError(BadMagic)",
                b"FAILLoad didn't succeed: UnificationError(BadMagic)",
                b"FAILLoad didn't succeed: UnificationError(BadMagic)",
                b"OKAY",
            ]),
            "\nActual USB output:\n{}",
            listener.dump_transport_out_queue()
        );
    }

    #[test]
    fn test_get_boot_slot_slotless() {
        let mut storage = FakeGblOpsStorage::default();
        storage.add_raw_device(c"boot", read_test_data("android/boot_v2_a.img"));
        storage.add_raw_device(c"vbmeta", read_test_data("android/vbmeta_v2_a.img"));
        storage.add_raw_device(c"misc", vec![0u8; 4 * 1024 * 1024]);

        let mut ops = default_test_gbl_ops(&storage);
        ops.current_slot = Some(Err(liberror::Error::Unsupported));
        ops.slot_count = Some(Err(liberror::Error::Unsupported));
        let mut load_buffer = vec![0u8; 8 * 1024 * 1024];
        let load_buffer = (&mut load_buffer[..]).into();

        let r = android_main(&mut ops, load_buffer, |_| {});
        if cfg!(feature = "gbl_dev") {
            let (ramdisk, _, kernel, _) = r.unwrap();
            checks_loaded_v2_slotless_normal_mode(ramdisk, kernel);
        } else {
            assert_eq!(r.unwrap_err(), liberror::Error::Unsupported.into());
        }
    }

    #[test]
    fn test_add_perf_metrics() {
        let mut buffer = vec![0u8; 1024];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();
        let mut metrics = GblMetrics::default();
        metrics.start_tick = Some(100);
        metrics.avb_ticks = Some(200);
        metrics.add_io_timing_ticks("boot", 300);
        let time = FakeGblTime::new(vec![1000]);

        add_perf_metrics(&mut builder, &metrics, &time).unwrap();

        let bootconfig = builder.config_bytes();
        let content_len = bootconfig.len() - BOOTCONFIG_TRAILER_SIZE;
        assert_eq!(
            &bootconfig[..content_len],
            b"androidboot.gbl.perf.boot_time=900
androidboot.gbl.perf.avb=200
androidboot.gbl.perf.io.boot=300
"
        );
    }

    #[test]
    fn test_add_firmware_version_metrics() {
        let mut buffer = vec![0u8; 1024];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();
        let proto_metrics = FirmwareVersionMetrics::from_iter([
            ("gbl_avb", FirmwareVersion { major: 1, minor: 0 }),
            ("gbl_avf", FirmwareVersion { major: 2, minor: 1 }),
        ]);

        add_firmware_version_metrics(&mut builder, &proto_metrics).unwrap();

        let bootconfig = builder.config_bytes();
        let content_len = bootconfig.len() - BOOTCONFIG_TRAILER_SIZE;
        assert_eq!(
            &bootconfig[..content_len],
            b"androidboot.gbl.fw_version.gbl_avb=1.0
androidboot.gbl.fw_version.gbl_avf=2.1
"
        );
    }

    #[test]
    fn test_vbmeta_cmdline_to_bootconfig_valid() {
        let storage = FakeGblOpsStorage::default();
        let mut ops = FakeGblOps::new(&storage);
        let mut buffer = vec![0u8; 1024];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();

        vbmeta_cmdline_to_bootconfig(&mut ops, "foo=bar baz=qux", &mut builder).unwrap();

        assert_eq!(builder.config_str(), "foo=bar\nbaz=qux\n");
    }

    #[test]
    fn test_vbmeta_cmdline_to_bootconfig_invalid_override() {
        let storage = FakeGblOpsStorage::default();
        let mut ops = FakeGblOps::new(&storage);
        let mut buffer = vec![0u8; 1024];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();

        let res = vbmeta_cmdline_to_bootconfig(
            &mut ops,
            "normal_arg=val1 invalid_arg:=val2",
            &mut builder,
        );
        assert!(res.is_err());
    }

    #[test]
    fn test_vbmeta_cmdline_to_bootconfig_invalid_append() {
        let storage = FakeGblOpsStorage::default();
        let mut ops = FakeGblOps::new(&storage);
        let mut buffer = vec![0u8; 1024];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();

        let res = vbmeta_cmdline_to_bootconfig(
            &mut ops,
            "normal_arg=val1 invalid_arg+=val2",
            &mut builder,
        );
        assert!(res.is_err());
    }

    #[test]
    fn test_vbmeta_cmdline_to_bootconfig_invalid_embedded_override() {
        let storage = FakeGblOpsStorage::default();
        let mut ops = FakeGblOps::new(&storage);
        let mut buffer = vec![0u8; 1024];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();

        // Reject attempts to sneak a second bootconfig param into a single commandline arg.
        let res = vbmeta_cmdline_to_bootconfig(
            &mut ops,
            "normal_arg=val1\ninvalid_arg+=val2",
            &mut builder,
        );
        assert!(res.is_err());

        let res = vbmeta_cmdline_to_bootconfig(
            &mut ops,
            "normal_arg=val1;invalid_arg+=val2",
            &mut builder,
        );
        assert!(res.is_err());
    }

    #[test]
    #[cfg(feature = "gbl_dev")]
    fn test_add_android_gbl_bootconfig_dev() {
        let mut buffer = vec![0u8; 1024];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();

        add_android_gbl_bootconfig(&mut builder, Some(202604)).unwrap();

        let bootconfig = builder.config_bytes();
        let content_len = bootconfig.len() - BOOTCONFIG_TRAILER_SIZE;
        assert_eq!(
            &bootconfig[..content_len],
            format!(
                "androidboot.gbl.version={VERSION}
androidboot.gbl.build_number={BUILD_NUMBER}
androidboot.gbl.fingerprint=dev/{VERSION}/{BUILD_NUMBER}
androidboot.gbl.vcs={BUILD_BRANCH}:{BUILD_REVISION}
androidboot.gbl.fw.api_level=202604
"
            )
            .as_bytes(),
        );
    }

    #[test]
    #[cfg(not(feature = "gbl_dev"))]
    fn test_add_android_gbl_bootconfig_prod() {
        let mut buffer = vec![0u8; 1024];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();

        add_android_gbl_bootconfig(&mut builder, Some(202604)).unwrap();

        let bootconfig = builder.config_bytes();
        let content_len = bootconfig.len() - BOOTCONFIG_TRAILER_SIZE;
        assert_eq!(
            &bootconfig[..content_len],
            format!(
                "androidboot.gbl.version={VERSION}
androidboot.gbl.build_number={BUILD_NUMBER}
androidboot.gbl.fingerprint=prod/{VERSION}/{BUILD_NUMBER}
androidboot.gbl.vcs={BUILD_BRANCH}:{BUILD_REVISION}
androidboot.gbl.fw.api_level=202604
"
            )
            .as_bytes(),
        );
    }
}
