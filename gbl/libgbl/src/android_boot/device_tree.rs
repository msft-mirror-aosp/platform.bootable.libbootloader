// Copyright 2025, The Android Open Source Project
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

//! GBL Android boot device tree manipulations and related consts exposed.

use crate::{
    android_boot::load::LoadedImages,
    device_tree::{
        DtComponentSource, DtComponentSourceMetadata, DtComponentType, DtComponentsRegistry,
        DtSourceLocation, SelectedDtComponent, SelectedDtComponents,
    },
    fastboot::boot_items::{BootItem, BootItemContainer},
    gbl_println,
    random::get_random_seed,
    GblOps,
};
use arrayvec::ArrayVec;
use bootparams::commandline::CommandlineBuilder;
use core::ffi::CStr;
use dttable::DtTableImage;
use fdt::{Fdt, FdtHeader, FdtNodeMut, MAXIMUM_OVERLAYS_TO_APPLY};
use fit::Fit;
use liberror::{Error, Result};
use safemath::SafeNum;

/// Helper function to select device tree components from loaded partitions.
pub(crate) fn fdt_select<'b, 'a: 'b, 'c: 'b>(
    ops: &mut impl GblOps<'a>,
    images: &LoadedImages<'b>,
    buffer: &'c mut [u8],
) -> Result<(Option<SelectedDtComponents<'b>>, &'c mut [u8])> {
    // TODO(b/385690995): Track FIT usage in metrics.

    // Detect FIT in DTBO partition
    if images.dtbo.len() > 0 {
        if let Ok(fit) = Fit::from_bytes(images.dtbo) {
            gbl_println!(ops, "FIT image detected in DTBO partition");
            return get_fit_selected_devicetree(ops, fit, buffer)
                .map(|(selected, remains)| (Some(selected), remains));
        }
    }
    fdt_select_from_boot_partitions(ops, images, buffer)
}

fn get_fit_selected_devicetree<'a, 'b, 'c>(
    ops: &mut impl GblOps<'a>,
    fit: Fit<'b>,
    buffer: &'c mut [u8],
) -> Result<(SelectedDtComponents<'b>, &'c mut [u8])> {
    let (fit_fdt_buffer, metadata_buffer) = fit.get_fit_selection_metadata()?;
    gbl_println!(ops, "Selecting FIT configuration");
    let selected_config = ops.select_fit_configuration(fit_fdt_buffer, metadata_buffer)?;

    let (final_config, base, overlays_res) =
        fit.get_devicetrees_from_selected_configuration(selected_config)?;
    gbl_println!(ops, "FIT configuration at {} offset got selected", final_config);

    Ok((
        SelectedDtComponents {
            base_dt: SelectedDtComponent {
                source_metadata: DtComponentSourceMetadata {
                    source: DtComponentSource::Dtbo,
                    location: DtSourceLocation::FitConfigOffset(final_config),
                },
                dt: base,
            },
            vmdtbo: None,
            overlays: overlays_res
                .into_iter()
                .map(|dt| SelectedDtComponent {
                    source_metadata: DtComponentSourceMetadata {
                        source: DtComponentSource::Dtbo,
                        location: DtSourceLocation::FitConfigOffset(final_config),
                    },
                    dt,
                })
                .collect(),
        },
        buffer,
    ))
}

/// Helper function to select device trees from traditional Android boot partitions such as `boot`,
/// `vendor_boot`, `dtb`, `dtbo`, etc.
pub fn fdt_select_from_boot_partitions<'b, 'a: 'b, 'c: 'b>(
    ops: &mut impl GblOps<'a>,
    images: &LoadedImages<'b>,
    buffer: &'c mut [u8],
) -> Result<(Option<SelectedDtComponents<'b>>, &'c mut [u8])> {
    let mut components = DtComponentsRegistry::new();

    let mut remains = match images.dtbo.len() > 0 {
        // TODO(b/374336105): Investigate if we can avoid additional copy.
        true => {
            gbl_println!(ops, "Handling overlays from dtbo");
            components.append_from_dttable(
                DtComponentSource::Dtbo,
                &DtTableImage::from_bytes(images.dtbo)?,
                buffer,
            )?
        }
        _ => buffer,
    };
    if images.dtb.len() > 0 {
        let source = images.dtb_source.unwrap();
        gbl_println!(ops, "Handling device tree from {source}");
        remains = if FdtHeader::from_bytes_ref(images.dtb).is_ok() {
            gbl_println!(ops, "Raw device tree found");
            components.append(ops, source, DtComponentType::BaseDt, images.dtb, remains)?
        } else if let Ok(table) = DtTableImage::from_bytes(images.dtb) {
            gbl_println!(ops, "Dttable with {} entries found", table.entries_count());
            components.append_from_dttable(source, &table, remains)?
        } else {
            return Err(Error::Other(Some(
                "Invalid or unrecognized device tree format in boot/vendor_boot",
            ))
            .into());
        }
    }
    if images.dtb_part.len() > 0 {
        gbl_println!(ops, "Handling device trees from dtb");
        let dttable = DtTableImage::from_bytes(images.dtb_part)?;
        remains = components.append_from_dttable(DtComponentSource::Dtb, &dttable, remains)?;
    }

    // Only x86_64 boots a kernel that ignores the device tree, so only there may an empty set skip
    // selection; elsewhere it falls through to autoselection and fails, as it must.
    #[cfg(target_arch = "x86_64")]
    if components.is_empty() {
        return Ok((None, remains));
    }

    gbl_println!(ops, "Selecting device tree components");
    ops.select_device_trees(&mut components)?;

    Ok((Some(components.into_selected()?), remains))
}

/// Device tree bootargs property to store kernel command line.
pub const PROP_BOOTARGS: &CStr = c"bootargs";
/// `linux,initrd-start` property name.
pub const PROP_INITRD_START: &CStr = c"linux,initrd-start";
/// `linux,initrd-end` property name.
pub const PROP_INITRD_END: &CStr = c"linux,initrd-end";
const PROP_BOOTARGS_EXT: &CStr = c"bootargs_ext";
/// `/chosen` node path.
///
/// Looking it up walks every node that precedes it, which is slow on large device trees where it
/// can sit near the end. Callers updating several of its properties should look it up once with
/// `Fdt::find_or_add_node_mut()`.
pub(crate) const NODE_CHOSEN: &str = "chosen";

/// Helper function to build DT commandline from loaded images, overlays
/// `bootargs_ext` and additional items provided via fastboot.
pub(crate) fn fdt_build_bootargs<'a, 'b>(
    ops: &mut impl GblOps<'a>,
    fdt: &mut Fdt<&mut [u8]>,
    images: &LoadedImages,
    overlays: impl IntoIterator<Item = &'b [u8]>,
    boot_items: Option<&BootItemContainer>,
    extra_reserved: usize,
) -> Result<()> {
    // We need to obtain all Fdt instances first so that we can later store property slices from
    // them to calculate the expected destination size before copying the data.
    let mut parsed_overlays: ArrayVec<Fdt<&[u8]>, MAXIMUM_OVERLAYS_TO_APPLY> = ArrayVec::new();
    for overlay in overlays {
        parsed_overlays.push(Fdt::new(overlay)?);
    }

    // Reserves 2 for `boot_cmdline` and `vendor_cmdline`.
    let mut bootargs_to_append: ArrayVec<&str, { MAXIMUM_OVERLAYS_TO_APPLY + 2 }> = ArrayVec::new();
    bootargs_to_append.push(images.boot_cmdline);
    bootargs_to_append.push(images.vendor_cmdline);
    // Appends `/chosen/bootargs_ext` from the root of each overlay to `/chosen/bootargs`.
    for overlay in &parsed_overlays {
        if let Ok(bootargs_ext) = overlay.get_property(NODE_CHOSEN, PROP_BOOTARGS_EXT) {
            let bootargs_cstr = CStr::from_bytes_until_nul(bootargs_ext)?;
            bootargs_to_append.push(bootargs_cstr.to_str()?);
        }
    }

    let mut chosen = fdt.find_or_add_node_mut(NODE_CHOSEN)?;

    fdt_append_bootargs(ops, &mut chosen, bootargs_to_append)?;

    // Show debug messages related to EFI.
    #[cfg(all(feature = "efi_boot_stub", feature = "gbl_dev"))]
    fdt_append_bootargs(ops, &mut chosen, ["efi=debug"])?;

    // Appends `/chosen/bootargs_ext` to `/chosen/bootargs` after overlays are applied:
    // https://source.android.com/docs/core/architecture/dto/optimize#kernel
    //
    // TODO(b/482462468): Remove concat logic once all platforms have switched to using
    // bootargs_ext in the overlay root instead of within fragments.
    fdt_concat_bootargs_properties(&mut chosen, PROP_BOOTARGS, PROP_BOOTARGS_EXT)?;
    if let Some(items) = boot_items {
        fdt_append_bootargs(ops, &mut chosen, items.utf8_items(BootItem::Cmdline))?;
    }
    fdt_bootargs_reserve_space(&mut chosen, extra_reserved)?;

    Ok(())
}

/// Helper to get current bootargs length.
///
/// Returns `(actual_cmdline_size, total_buffer_size)`.
fn fdt_get_bootargs_len<T: AsRef<[u8]>>(chosen: &FdtNodeMut<'_, T>) -> (usize, usize) {
    chosen
        .get_property(PROP_BOOTARGS)
        .map(|b| {
            (
                CStr::from_bytes_until_nul(b).map(|s| s.to_bytes_with_nul().len()).unwrap_or(0),
                b.len(),
            )
        })
        .unwrap_or((0, 0))
}

/// Appends `cmds` to the FDT bootargs property.
pub(crate) fn fdt_append_bootargs<'a, 'b>(
    ops: &mut impl GblOps<'a>,
    chosen: &mut FdtNodeMut<'_, &mut [u8]>,
    cmds: impl IntoIterator<Item = &'b str> + Clone,
) -> Result<()> {
    let (current_used_prefix, current_buffer_len) = fdt_get_bootargs_len(chosen);
    let to_append_len = cmds.clone().into_iter().map(|v| v.len() + 1).sum::<usize>();
    let final_buffer_len = current_buffer_len + to_append_len + 1;
    let buffer = chosen.set_property_placeholder(PROP_BOOTARGS, final_buffer_len)?;
    let mut builder =
        CommandlineBuilder::from_prefix_with_len(&mut buffer[..], current_used_prefix)?;
    for v in cmds {
        // The commandline to be added may be from bootconfig which allows ":=". Emit a warning
        // just in case.
        if v.find(":=").is_some() {
            gbl_println!(ops, "{v},  \":=\" assignment may not be supported");
        }
        builder.add_raw(v)?;
    }

    // It has been observed that some OS call `from_utf8` on the entire bootarg buffer to decode,
    // which will pick up everything after the null terminator. Thus zeroize the remaining to
    // prevent OS from trying to think they are valid data.
    builder.zeroize_remains();
    Ok(())
}

/// Reserves additional space in the FDT bootargs property.
fn fdt_bootargs_reserve_space(
    chosen: &mut FdtNodeMut<'_, &mut [u8]>,
    reserved: usize,
) -> Result<()> {
    let (current_used_prefix, current_buffer_len) = fdt_get_bootargs_len(chosen);
    let final_buffer_len: usize = (SafeNum::from(current_buffer_len) + reserved).try_into()?;
    let buffer = chosen.set_property_placeholder(PROP_BOOTARGS, final_buffer_len)?;
    let mut builder =
        CommandlineBuilder::from_prefix_with_len(&mut buffer[..], current_used_prefix)?;
    builder.zeroize_remains();
    Ok(())
}

/// Appends the platform-specific kernel command line fixup to the FDT bootargs property.
///
/// The bootargs property must already be built by `fdt_build_bootargs()`. The fixup is written
/// in place into the free space of the property, which is extended if the platform requests a
/// larger buffer.
pub(crate) fn fdt_fixup_bootargs<'a>(
    ops: &mut impl GblOps<'a>,
    chosen: &mut FdtNodeMut<'_, &mut [u8]>,
) -> Result<()> {
    let mut fixup = |chosen: &mut FdtNodeMut<'_, &mut [u8]>| -> Result<()> {
        let (current_used_prefix, current_buffer_len) = fdt_get_bootargs_len(chosen);
        let buffer = chosen.set_property_placeholder(PROP_BOOTARGS, current_buffer_len)?;
        let mut builder =
            CommandlineBuilder::from_prefix_with_len(&mut buffer[..], current_used_prefix)?;
        builder.add_raw_with(|current, out| ops.fixup_kernel_commandline(current, out))?;
        builder.zeroize_remains();
        Ok(())
    };

    match fixup(chosen) {
        Err(Error::BufferTooSmall(Some(requested))) => {
            fdt_bootargs_reserve_space(chosen, requested)?;
            fixup(chosen)
        }
        v => v,
    }
}

/// Appends bootargs properties within the single FDT node.
///
/// This implementation performs the concatenation within the FDT buffer without
/// requiring temporary buffers.
fn fdt_concat_bootargs_properties(
    node: &mut FdtNodeMut<'_, &mut [u8]>,
    dst_name: &CStr,
    src_name: &CStr,
) -> Result<()> {
    // If src doesn't exist, we have nothing to concat.
    let Ok(src_prop) = node.get_property(src_name) else {
        return Ok(());
    };
    let src_len = CStr::from_bytes_until_nul(src_prop)?.to_bytes().len();
    if src_len == 0 {
        return Ok(());
    }

    let dst_prop = node.get_property(dst_name)?;
    let mut dst_len = CStr::from_bytes_until_nul(dst_prop)?.to_bytes().len();

    let needs_separator = dst_len > 0;
    let separator_len = usize::from(needs_separator);
    // Includes null terminator.
    let required_len: usize = (SafeNum::from(dst_len) + separator_len + src_len + 1).try_into()?;
    if dst_prop.len() < required_len {
        // Extends the property to required length.
        node.set_property_placeholder(dst_name, required_len)?;
    }

    let (dst_buf, src_buf) = node.get_property_mut_and_ref(dst_name, src_name)?;
    // Replaces null terminator with separator if needed.
    if needs_separator {
        dst_buf[dst_len] = b' ';
        dst_len += 1;
    }

    // Includes null terminator.
    dst_buf[dst_len..dst_len + src_len + 1].copy_from_slice(&src_buf[..src_len + 1]);

    Ok(())
}

/// RNG seed DT property name.
pub(crate) const RNG_SEED_PROP: &CStr = c"rng-seed";
/// KALSR seed DT property name.
pub(crate) const KASLR_SEED_PROP: &CStr = c"kaslr-seed";

/// The minimal sufficient RNG seed is 32 bytes. The Linux kernel considers up
/// to 512 bytes for this property. Providing 64 bytes as a reasonable balanced
/// option. Could be re-visited.
pub const RNG_SEED_SIZE_BYTES: usize = 64;
/// https://www.kernel.org/doc/Documentation/devicetree/bindings/chosen.txt
pub const KASLR_SEED_SIZE_BYTES: usize = core::mem::size_of::<u64>();

/// Helper function that utilizes device RNG capabilities to provide initial entropy
/// to HLOS and initialize the KASLR feature.
pub(crate) fn fdt_propagate_random<'a>(
    ops: &mut impl GblOps<'a>,
    chosen: &mut FdtNodeMut<'_, &mut [u8]>,
) -> Result<()> {
    fdt_propagate_random_seed(ops, chosen, RNG_SEED_PROP, RNG_SEED_SIZE_BYTES)?;
    // NOTE: We ensure that KASLR SEED is generated even for the Linux EFI boot stub flow.
    // The  EFI boot stub expects the EFI RNG protocol to be optional. If the RNG protocol is
    // somehow inaccessible from the boot stub, then it would continue boot without a KASLR seed.
    // To prevent this, we unconditionally inject the /chosen/kaslr-seed node from the bootloader.
    // This ensures that failing to initialize an RNG device and seed is treated as an error.
    // The EFI boot stub can choose to generate a new seed (thus ignoring the bootloader injected
    // one), or fallback to the bootloader injected one when it fails to generate a seed.
    fdt_propagate_random_seed(ops, chosen, KASLR_SEED_PROP, KASLR_SEED_SIZE_BYTES)?;

    Ok(())
}

fn fdt_propagate_random_seed<'a>(
    ops: &mut impl GblOps<'a>,
    node: &mut FdtNodeMut<'_, &mut [u8]>,
    name: &CStr,
    seed_size: usize,
) -> Result<()> {
    // Allocate space for seed data right inside device tree.
    let buffer = node.set_property_placeholder(name, seed_size)?;

    match get_random_seed(ops, buffer) {
        Ok(_) => Ok(()),
        Err(e) => {
            // Error occurred, so clear out seed placeholder.
            node.delete_property(name)?;

            match e {
                #[cfg(feature = "gbl_dev")]
                Error::Unsupported | Error::NotFound | Error::NotReady => {
                    gbl_println!(
                        ops,
                        "SECURITY WARNING: RNG capabilities aren't available: {e}. \
                        Skip KASLR and kernel entropy initialization since DEV GBL flow is used."
                    );
                    Ok(())
                }
                e => {
                    gbl_println!(
                        ops,
                        "SECURITY ERROR: RNG generation is reported an error: {e}. \
                        Cannot initialize KASLR and kernel entropy."
                    );
                    Err(e)
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ops::test::FakeGblOps;
    use libtestutils::AlignedBuffer;

    #[test]
    fn test_fdt_fixup_bootargs_extends_property() {
        let mut buffer = AlignedBuffer::new(16 * 1024, 8);
        let mut fdt = Fdt::new_empty(&mut buffer[..]).unwrap();
        // No free space: FW returns BufferTooSmall, GBL extends bootargs and retries.
        fdt.set_property(NODE_CHOSEN, PROP_BOOTARGS, b"a=b\0").unwrap();
        let fixup = format!("c={}", "d".repeat(4096));
        let mut ops = FakeGblOps::new(&[]);
        ops.test_custom_cmdline_fixup = Some(fixup.clone());

        let mut chosen = fdt.find_or_add_node_mut(NODE_CHOSEN).unwrap();
        fdt_fixup_bootargs(&mut ops, &mut chosen).unwrap();

        let bootargs = fdt.get_property(NODE_CHOSEN, PROP_BOOTARGS).unwrap();
        assert_eq!(
            CStr::from_bytes_until_nul(bootargs).unwrap().to_str(),
            Ok(&*format!("a=b {fixup}"))
        );
    }

    #[test]
    fn test_fdt_fixup_bootargs_in_place() {
        let mut buffer = AlignedBuffer::new(16 * 1024, 8);
        let mut fdt = Fdt::new_empty(&mut buffer[..]).unwrap();
        // Free space is filled with garbage to check that it is zeroized after the fixup.
        fdt.set_property(NODE_CHOSEN, PROP_BOOTARGS, b"a=b\0xxxx").unwrap();
        let mut ops = FakeGblOps::new(&[]);
        ops.test_custom_cmdline_fixup = Some("c".into());

        let mut chosen = fdt.find_or_add_node_mut(NODE_CHOSEN).unwrap();
        fdt_fixup_bootargs(&mut ops, &mut chosen).unwrap();

        // Property isn't extended since the fixup fits into the free space.
        assert_eq!(fdt.get_property(NODE_CHOSEN, PROP_BOOTARGS).unwrap(), b"a=b c\0\0\0");
    }

    #[test]
    fn test_fdt_fixup_bootargs_invalid_fixup() {
        let mut buffer = AlignedBuffer::new(16 * 1024, 8);
        let mut fdt = Fdt::new_empty(&mut buffer[..]).unwrap();
        fdt.set_property(NODE_CHOSEN, PROP_BOOTARGS, b"a=b\0").unwrap();
        let mut ops = FakeGblOps::new(&[]);
        ops.test_custom_cmdline_fixup = Some("c=\0".into());

        let mut chosen = fdt.find_or_add_node_mut(NODE_CHOSEN).unwrap();
        assert_eq!(fdt_fixup_bootargs(&mut ops, &mut chosen), Err(Error::InvalidInput));
    }

    enum BootargsConcatResult<'a> {
        Ok(&'a [u8]),
        Error,
    }

    enum FdtCapacity {
        Expanded,
        Shrunk,
    }

    fn test_fdt_concat_bootargs_properties<'a>(
        dst: Option<&[u8]>,
        src: Option<&[u8]>,
        capacity: FdtCapacity,
        expected: BootargsConcatResult<'a>,
    ) {
        let mut buffer = AlignedBuffer::new(1024, 8);
        let mut fdt = Fdt::new_empty(&mut buffer[..]).unwrap();

        if let Some(val) = dst {
            fdt.set_property("/", c"dst", val).unwrap();
        }
        if let Some(val) = src {
            fdt.set_property("/", c"src", val).unwrap();
        }

        // DT cannot be extended after shrink.
        if matches!(capacity, FdtCapacity::Shrunk) {
            fdt.shrink_to_fit().unwrap();
        }

        let mut root = fdt.find_or_add_node_mut("/").unwrap();
        let res = fdt_concat_bootargs_properties(&mut root, c"dst", c"src");

        match expected {
            BootargsConcatResult::Ok(expected_val) => {
                res.unwrap();
                assert_eq!(fdt.get_property("/", c"dst").unwrap(), expected_val);
            }
            BootargsConcatResult::Error => {
                res.unwrap_err();
            }
        }
    }

    #[test]
    fn test_fdt_concat_bootargs_properties_success() {
        test_fdt_concat_bootargs_properties(
            Some(b"val1\0"),
            Some(b"val2\0"),
            FdtCapacity::Expanded,
            BootargsConcatResult::Ok(b"val1 val2\0"),
        );
    }

    #[test]
    fn test_fdt_concat_bootargs_properties_no_extend() {
        test_fdt_concat_bootargs_properties(
            Some(b"val1\0\0\0\0\0"),
            Some(b"val2\0"),
            // DT is shrunk, but we have enough space to append.
            FdtCapacity::Shrunk,
            BootargsConcatResult::Ok(b"val1 val2\0"),
        );
    }

    #[test]
    fn test_fdt_concat_bootargs_properties_no_space() {
        test_fdt_concat_bootargs_properties(
            Some(b"val1\0"),
            Some(b"val2\0"),
            // DT is shrunk, so not enough space to append.
            FdtCapacity::Shrunk,
            BootargsConcatResult::Error,
        );
    }

    #[test]
    fn test_fdt_concat_bootargs_properties_src_invalid_cstr() {
        test_fdt_concat_bootargs_properties(
            Some(b"val1\0"),
            Some(b"val2"),
            FdtCapacity::Expanded,
            BootargsConcatResult::Error,
        );
    }

    #[test]
    fn test_fdt_concat_bootargs_properties_dst_invalid_cstr() {
        test_fdt_concat_bootargs_properties(
            Some(b"val1"),
            Some(b"val2\0"),
            FdtCapacity::Expanded,
            BootargsConcatResult::Error,
        );
    }

    #[test]
    fn test_fdt_concat_bootargs_properties_src_missing() {
        test_fdt_concat_bootargs_properties(
            Some(b"val1\0"),
            None,
            FdtCapacity::Shrunk,
            BootargsConcatResult::Ok(b"val1\0"),
        );
    }

    #[test]
    fn test_fdt_concat_bootargs_properties_src_empty() {
        test_fdt_concat_bootargs_properties(
            Some(b"val1\0"),
            Some(b"\0"),
            FdtCapacity::Shrunk,
            BootargsConcatResult::Ok(b"val1\0"),
        );
    }

    #[test]
    fn test_fdt_concat_bootargs_properties_dst_empty() {
        test_fdt_concat_bootargs_properties(
            Some(b"\0"),
            Some(b"val2\0"),
            FdtCapacity::Expanded,
            BootargsConcatResult::Ok(b"val2\0"),
        );
    }

    #[test]
    fn test_fdt_concat_bootargs_properties_dst_missing() {
        test_fdt_concat_bootargs_properties(
            None,
            Some(b"val2\0"),
            FdtCapacity::Expanded,
            BootargsConcatResult::Error,
        );
    }
}
