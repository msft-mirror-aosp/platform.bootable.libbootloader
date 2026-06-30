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

//! Android virtualization framework support for GBL

use crate::{
    android_boot::{
        hasher::{Hasher, Sha256, Sha512},
        kernel::KernelAttributes,
        load::split,
    },
    device_tree::{entry_is_vmdtbo, DtComponentSourceMetadata},
    gbl_avb::state::BootStateColor,
    gbl_println, GblOps, KiB,
};
use avb::{SlotVerifyData, VbmetaVerifyError};
use bootparams::bootconfig::BootConfigBuilder;
use core::{
    ffi::CStr,
    mem::{align_of, size_of},
};
use dttable::DtTableImage;
use fdt::{fdt_encode_cell_sized_property, fdt_ensure_reserved_memory_initialized, std_props, Fdt};
use liberror::{Error, Result};
use opendice::{
    dice::{Config, DiceMode, InputValues, HASH_SIZE, HIDDEN_SIZE},
    dice_android_format_config_descriptor, dice_android_handover_main_flow, DiceAndroidConfig,
};
use safemath::SafeNum;
use static_assertions::const_assert;
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

const NUM_PVMFW_CONFIG_ENTRIES: usize = 4;

fn align_up(size: usize, alignment: usize) -> Result<usize> {
    Ok(SafeNum::from(size).round_up(alignment).try_into().map_err(Error::ArithmeticOverflow)?)
}

/// Returns `Err(InvalidAlignment)` if `buf`'s pointer isn't aligned to `alignment`.
fn check_alignment(buf: &[u8], alignment: usize) -> Result<()> {
    match buf.as_ptr().align_offset(alignment) {
        0 => Ok(()),
        _ => Err(Error::InvalidAlignment),
    }
}

const fn align_up_const(size: usize, alignment: usize) -> usize {
    let offset = alignment.checked_sub(1).unwrap();
    size.checked_add(offset).unwrap() & !offset
}

/// Represents an object contains AVF verification data
pub(crate) trait AVFVerificationData {
    /// Returns the vendor hashtree digest if it exists.
    fn vendor_hashtree_digest(&self) -> Option<&[u8]>;

    /// Returns the Sha256 vbmeta digest
    fn vbmeta_digest_sha256(&self) -> [u8; Sha256::DIGEST_SIZE];

    /// Returns the Sha512 vbmeta digest
    fn vbmeta_digest_sha512(&self) -> [u8; Sha512::DIGEST_SIZE];

    /// Returns the hash of the vbmeta public key
    fn public_key_digest<T: Hasher>(
        &self,
        vbmeta: Option<&str>,
    ) -> core::result::Result<T::Output, VbmetaVerifyError>;

    /// Returns vbmeta rollback index
    fn vbmeta_rollback_index(&self) -> Result<u64>;
}

impl AVFVerificationData for SlotVerifyData<'_> {
    /// Extract the vendor hashtree digest from VB meta property.
    fn vendor_hashtree_digest(&self) -> Option<&[u8]> {
        // In order to successfully boot a Microdroid pVM with a vendor partition, the bootloader
        // must add the hashtree digest of the vendor image as a device tree property value.
        // See details:
        // https://cs.android.com/android/platform/superproject/main/+/main:packages/modules/Virtualization/docs/microdroid_vendor_modules.md,
        // AVF expects this property in the vendor.img footer (vbmeta_vendor), so
        // limit lookup to the root vbmeta and vbmeta_vendor partitions.
        const HASHTREE_DIGEST_PROPNAME: &str = "com.android.build.microdroid-vendor.root_digest";
        self.vbmeta_data()
            .iter()
            .filter(|data| matches!(data.partition_name().to_str(), Ok("vbmeta" | "vbmeta_vendor")))
            .find_map(|data| data.get_property_value(HASHTREE_DIGEST_PROPNAME))
    }

    fn vbmeta_digest_sha256(&self) -> [u8; Sha256::DIGEST_SIZE] {
        self.calculate_sha256_digest()
    }

    fn vbmeta_digest_sha512(&self) -> [u8; Sha512::DIGEST_SIZE] {
        self.calculate_sha512_digest()
    }

    fn public_key_digest<T: Hasher>(
        &self,
        vbmeta: Option<&str>,
    ) -> core::result::Result<T::Output, VbmetaVerifyError> {
        // TODO: a more precise approach identifying vbmetas that cover relevant partitions, and
        // extracting their public keys (b/429168146).
        let mut hasher = T::new();
        self.vbmeta_data().iter().try_for_each(|data| {
            if vbmeta.map_or(true, |v| data.partition_name().to_str() == Ok(v)) {
                hasher.update(data.header_verified()?.public_key());
            }
            Ok(())
        })?;
        Ok(hasher.finish())
    }

    fn vbmeta_rollback_index(&self) -> Result<u64> {
        // TODO:: consider including indexes from other vbmetas (b/448363880).
        let idx_loc = self
            .vbmeta_data()
            .iter()
            .find(|d| d.partition_name().to_str() == Ok("vbmeta"))
            .ok_or(Error::NotFound)?
            .header_verified()
            .map_err(|_| Error::Other(Some("vbmeta verify error")))?
            .rollback_index_location() as usize;
        self.rollback_indexes()
            .get(idx_loc)
            .copied()
            .ok_or(Error::Other(Some("missing rollback index")))
    }
}

/// A container for relevant boot parameters
pub(crate) struct BootInfo<'a, T: AVFVerificationData> {
    unlocked: bool,
    is_recovery: bool,
    color: BootStateColor,
    verify_data: &'a T,
}

const DEVICE_STATE_PROP: &CStr = c"host.vbmeta.device_state";
const VBMETA_DIGEST_PROP: &CStr = c"host.vbmeta.digest";
const VBMETA_PUBKEY_DIGEST_PROP: &CStr = c"host.vbmeta.public_key_digest";
const VB_STATE_PROP: &CStr = c"host.verifiedbootstate";

impl<'a, T> BootInfo<'a, T>
where
    T: AVFVerificationData,
{
    /// Create a new `BootInfo` instance.
    pub(crate) fn new(
        unlocked: bool,
        is_recovery: bool,
        color: BootStateColor,
        verify_data: &'a T,
    ) -> Self {
        Self { unlocked, is_recovery, color, verify_data }
    }

    fn device_state(&self) -> &[u8] {
        match self.unlocked {
            true => b"unlocked\0",
            false => b"locked\0",
        }
    }

    fn vb_state(&self) -> &[u8] {
        match self.color {
            BootStateColor::Green => b"green\0",
            BootStateColor::Yellow => b"yellow\0",
            BootStateColor::Orange => b"orange\0",
            BootStateColor::Red => b"red\0",
        }
    }

    fn pkey_digest(&self) -> Result<[u8; Sha256::DIGEST_SIZE]> {
        match self.verify_data.public_key_digest::<Sha256>(Some("vbmeta")) {
            Ok(h) => Ok(h),
            _ if self.unlocked => Ok([0u8; Sha256::DIGEST_SIZE]),
            _ => Err(Error::Other(Some("vbmeta verify error"))),
        }
    }

    fn as_avb_dt_props<U>(&self, target_dt: &mut Fdt<U>, node_path: &str) -> Result<()>
    where
        U: AsMut<[u8]> + AsRef<[u8]>,
    {
        target_dt.ensure_node(node_path)?;
        target_dt.set_property(node_path, std_props::COMPATIBLE, b"android,firmware\0")?;
        target_dt.set_property(node_path, DEVICE_STATE_PROP, self.device_state())?;
        target_dt.set_property(node_path, VBMETA_PUBKEY_DIGEST_PROP, &self.pkey_digest()?)?;
        target_dt.set_property(
            node_path,
            VBMETA_DIGEST_PROP,
            &self.verify_data.vbmeta_digest_sha256(),
        )?;
        target_dt.set_property(node_path, VB_STATE_PROP, self.vb_state())?;
        Ok(())
    }
}

/// Places pvmfw firmware binary and configuration data into reserved memory region
///
/// Copies the pvmfw binary, builds its configuration data, assembles them into a single blob, and
/// places it into a reserved memory region for later use by the hypervisor.
///
/// As per the requirements outlined at
/// https://cs.android.com/android/platform/superproject/main/+/main:packages/modules/Virtualization/guest/pvmfw/README.md,
/// pvmfw expects to have been loaded at 4KiB-aligned address. Therefore we respect this alignment
/// when loading the binary image. The bootloader is expected to describe the region using a
/// reserved memory device tree node, with both address and size properly aligned to the page size
/// used by the hypervisor. The configuration data must be 4KiB-aligned as well, while each config
/// entry must be 8b-aligned.
///
/// See more details of pvmfw loading, the configuration data layout, and meaning of
/// individual config entries at the link above.
///
/// # Arguments
///
/// * `ops` - an implementation of `GblOps`
/// * `output_buffer` - the target load buffer. Must be aligned to `kernel_attrs.page_size`.
/// * `pvmfw_binary` - a byte slice containing a preloaded pvmfw binary
/// * `kernel_attrs` - parsed kernel attributes. `page_size` is used to align the final
///   region size so the hypervisor's identity mapping covers it exactly.
/// * `boot_info` - boot state data
/// * `dtbo_partition` - loaded dtbo partition bytes
///
/// # Returns
///
/// * `Ok(usize)` - on success, the total size of the loaded image.
/// * `Err(InvalidArgument)` - if the pvmfw partition cannot be parsed
/// * `Err(InvalidAlignment)` - if `output_buffer` is not aligned to `kernel_attrs.page_size`
/// * `Err(BadBufferSize)` - if pvmfw binary cannot be extracted or the size data is invalid
/// * `Err(BufferTooSmall)` - of the pvmfw binary and config data doesn't fit into the target buffer
/// * `Err(ArithmeticOverflow)` - on overflow when calculating image buffer size
pub(crate) fn build_pvmfw_data_region<'a, T: AVFVerificationData>(
    ops: &mut impl GblOps<'a>,
    output_buffer: &mut [u8],
    pvmfw_binary: &[u8],
    kernel_attrs: &KernelAttributes,
    boot_info: &BootInfo<T>,
    dtbo_partition: &[u8],
) -> Result<usize> {
    check_alignment(output_buffer, kernel_attrs.page_size)?;
    // Split the pvmfw region into binary and configuration buffers
    let pvmfw_bin_size = pvmfw_binary.len();
    let (binary, config) = output_buffer
        .split_at_mut_checked(pvmfw_bin_size)
        .ok_or(Error::BufferTooSmall(Some(pvmfw_bin_size)))?;

    // Write the pvmfw configuration data to the config region
    let config_size = write_pvmfw_config(ops, config, binary, boot_info)?;
    let vmdtbo_reserve = vmdtbo_entry_max_size(dtbo_partition)?;
    // Copy the binary to the start of pvmfw region
    binary.copy_from_slice(pvmfw_binary);

    let used_size = SafeNum::from(pvmfw_bin_size) + config_size;
    let required_size =
        (used_size + vmdtbo_reserve).try_into().map_err(Error::ArithmeticOverflow)?;
    let used_size = used_size.try_into().map_err(Error::ArithmeticOverflow)?;
    // Size must be aligned to the hypervisor's page size
    let total_size = align_up(required_size, kernel_attrs.page_size)?;

    let padding = output_buffer
        .get_mut(used_size..total_size)
        .ok_or(Error::BufferTooSmall(Some(total_size)))?;
    padding.fill(0u8);

    gbl_println!(ops, "AVF: init successful");
    Ok(total_size)
}

/// Finds the size of the largest VMDTBO overlay present in the DTBO partition.
fn vmdtbo_entry_max_size(dtbo_partition: &[u8]) -> Result<usize> {
    if dtbo_partition.is_empty() {
        return Ok(0);
    }
    let dttable = DtTableImage::from_bytes(dtbo_partition)
        .map_err(|_| Error::Other(Some("invalid dtbo partition")))?;
    let max_vmdtbo_size = dttable
        .entries()
        .filter_map(|e| match entry_is_vmdtbo(&e.metadata) {
            true => Some(e.dtb.len()),
            _ => None,
        })
        .max()
        .unwrap_or(0);
    align_up(max_vmdtbo_size, PvmfwConfEntry::ALIGNMENT)
}

/// Injects VMDTBO overlay into the pvmfw data configuration region
///
/// # Arguments
///
/// * `pvmfw_data_buf` - a valid pvmfw data region, including extra space for the vmdtbo.
///   Must be aligned to `kernel_attrs.page_size`.
/// * `pvmfw_binary_size` - size of the pvmfw binary within the entire pvmfw data region
/// * `kernel_attrs` - parsed kernel attributes. `page_size` is used to align the final
///   region size so the hypervisor's identity mapping covers it exactly.
/// * `vmdtbo` - vmdtbo overlay to inject
///
/// # Returns
///
/// * `Ok(usize)` - on success, the new total size of pvmfw data, aligned correctly
/// * `Err(InvalidAlignment)` - if `pvmfw_data_buf` is not aligned to `kernel_attrs.page_size`
/// * `Err(BufferTooSmall)` - if there is not enough space to inject the VMDTBO
/// * `Err(ArithmeticOverflow)` - on overflow when calculating image buffer size
///
/// TODO(b/480459718): Replace VMDTBO injection with full pvmfw config build after performing DT
/// component selection.
pub(crate) fn inject_vmdtbo(
    pvmfw_data_buf: &mut [u8],
    pvmfw_binary_size: usize,
    kernel_attrs: &KernelAttributes,
    vmdtbo: &[u8],
) -> Result<usize> {
    check_alignment(pvmfw_data_buf, kernel_attrs.page_size)?;
    const VMDTBO_ENTRY_IDX: usize = 2;

    let vmdtbo_entry_sz = vmdtbo.len();
    let vmdtbo_entry_sz_padded = align_up(vmdtbo_entry_sz, PvmfwConfEntry::ALIGNMENT)?;

    let conf_data_buf = pvmfw_data_buf.get_mut(pvmfw_binary_size..).ok_or(Error::BadBufferSize)?;
    let (conf_header_buf, conf_entries_buf) = conf_data_buf
        .split_at_mut_checked(PvmfwConfHeader::PADDED_SIZE)
        .ok_or(Error::BadBufferSize)?;

    // Update contents of pvmfw configuration header - sizes and entry offsets
    let conf_header =
        PvmfwConfHeader::mut_from_prefix(conf_header_buf).map_err(|_| Error::InvalidAlignment)?.0;
    if conf_header.entries[VMDTBO_ENTRY_IDX].size != 0 {
        return Err(Error::Other(Some("vmdtbo already present")));
    }
    let new_config_size = SafeNum::from(conf_header.total_size) + vmdtbo_entry_sz_padded;
    let new_pvmfw_data_size: usize =
        (new_config_size + pvmfw_binary_size).try_into().map_err(Error::ArithmeticOverflow)?;

    // Shift subsequent entries right and insert vmdtbo entry
    let vmdtbo_offset: usize = conf_header.entries[VMDTBO_ENTRY_IDX].offset.try_into().unwrap();
    if TryInto::<usize>::try_into(new_config_size - PvmfwConfHeader::PADDED_SIZE).unwrap()
        > conf_entries_buf.len()
    {
        return Err(Error::BufferTooSmall(Some(new_pvmfw_data_size)));
    }
    let (_, next_entries) =
        conf_entries_buf.split_at_mut(vmdtbo_offset - PvmfwConfHeader::PADDED_SIZE);
    let entries_end = (conf_header.total_size as usize) - vmdtbo_offset;
    // Move entries and make space for VMDTBO
    next_entries.copy_within(0..entries_end, vmdtbo_entry_sz_padded);
    let (vmdtbo_entry, _) = next_entries.split_at_mut(vmdtbo_entry_sz_padded);
    let (vmdtbo_buf, vmdtbo_pad) = vmdtbo_entry.split_at_mut(vmdtbo_entry_sz);
    vmdtbo_buf.copy_from_slice(vmdtbo);
    vmdtbo_pad.fill(0u8);

    // Update size of VMDTBO entry in header
    conf_header.entries[VMDTBO_ENTRY_IDX].size = vmdtbo_entry_sz.try_into()?;
    // Update offsets of entries following VMDTBO
    for i in VMDTBO_ENTRY_IDX + 1..NUM_PVMFW_CONFIG_ENTRIES {
        conf_header.entries[i].offset += TryInto::<u32>::try_into(vmdtbo_entry_sz_padded)?;
    }
    // Update total size of config data
    conf_header.total_size = new_config_size.try_into().map_err(Error::ArithmeticOverflow)?;

    // New size must be aligned to the page size used by the hypervisor
    align_up(new_pvmfw_data_size, kernel_attrs.page_size)
}

/// Add a device tree node describing pvmfw memory carveout. This is default behavior, required for
/// pKVM, and can be overridden for other hypervisors by removing the
/// `/reserved-memory/pkvm_guest_firmware` node in `ops.fixup_device_tree`.
fn pkvm_describe_pvmfw_resvmem<'a, T>(fdt: &mut Fdt<T>, buffer: &[u8], bin_len: usize) -> Result<()>
where
    T: AsMut<[u8]> + AsRef<[u8]>,
{
    const PVMFW_RESVMEM_PATH: &str = "/reserved-memory/pkvm_guest_firmware";
    const CONFIG_OFFSET_PROP: &CStr = c"config-data-offset";
    const MAX_REG_CELLS: usize = 8;
    const FDT_CELL_SIZE: usize = 4;

    let resvmem = fdt_ensure_reserved_memory_initialized(fdt)?;

    // Serialize region address and size, and write DT node properties
    let mut reg_buf = [0u8; MAX_REG_CELLS * FDT_CELL_SIZE];
    let reg_bytes = fdt_encode_cell_sized_property(
        &[(buffer.as_ptr() as usize), buffer.len()],
        &[resvmem.address_cells, resvmem.size_cells],
        &mut reg_buf,
    )?;

    fdt.set_property(
        PVMFW_RESVMEM_PATH,
        std_props::COMPATIBLE,
        b"linux,pkvm-guest-firmware-memory\0",
    )?;
    fdt.set_property(PVMFW_RESVMEM_PATH, std_props::REG, &reg_buf[..reg_bytes])?;
    fdt.set_property(PVMFW_RESVMEM_PATH, std_props::NO_MAP, &[])?;
    let config_offset: u32 = bin_len.try_into().map_err(|_| Error::OutOfRange)?;
    fdt.set_property(PVMFW_RESVMEM_PATH, CONFIG_OFFSET_PROP, &config_offset.to_be_bytes())?;
    Ok(())
}

// TODO: Try to encapsulate building the pvmfw configuration buffer as suggested:
// http://aosp/3674715/comment/3fa5f59f_d119abc8/

/// Pvmfw configuration entry implementation; see:
/// https://cs.android.com/android/platform/superproject/main/+/main:packages/modules/Virtualization/guest/pvmfw/README.md
#[repr(C, packed)]
#[derive(
    Copy, Clone, Debug, Default, PartialEq, Eq, Immutable, KnownLayout, FromBytes, IntoBytes,
)]
struct PvmfwConfEntry {
    offset: u32,
    size: u32,
}

const_assert!(PvmfwConfEntry::ALIGNMENT >= align_of::<PvmfwConfEntry>());

impl PvmfwConfEntry {
    const ALIGNMENT: usize = 8;
}

/// Pvmfw configuration header implementation; see:
/// https://cs.android.com/android/platform/superproject/main/+/main:packages/modules/Virtualization/guest/pvmfw/README.md
#[repr(C, packed)]
#[derive(
    Copy, Clone, Debug, Default, PartialEq, Eq, Immutable, KnownLayout, FromBytes, IntoBytes,
)]
struct PvmfwConfHeader {
    magic: u32,
    version: u32,
    total_size: u32,
    flags: u32,
    entries: [PvmfwConfEntry; NUM_PVMFW_CONFIG_ENTRIES],
}

const_assert!(PvmfwConfHeader::ALIGNMENT >= align_of::<PvmfwConfHeader>());

type EntryBufsSizes = [(usize, usize); NUM_PVMFW_CONFIG_ENTRIES];

impl PvmfwConfHeader {
    const MAGIC: u32 = u32::from_ne_bytes(*b"pvmf");
    const DEFAULT_FLAGS: u32 = 0; // Flags field is currently unused and must be zero
    const ALIGNMENT: usize = KiB!(4);
    const PADDED_SIZE: usize = align_up_const(size_of::<Self>(), PvmfwConfEntry::ALIGNMENT);

    fn init_padded_prefix_mut<'a>(buffer: &'a mut [u8]) -> Result<(&'a mut Self, &'a mut [u8])> {
        if buffer.as_ptr().align_offset(PvmfwConfHeader::ALIGNMENT.into()) != 0 {
            return Err(Error::InvalidAlignment.into());
        }
        let (header_buf, remains) = split(buffer, Self::PADDED_SIZE)?;
        let (header, header_pad) =
            Self::mut_from_prefix(header_buf).map_err(|_| Error::BadBufferSize)?;
        header.magic = Self::MAGIC;
        header.version = Self::encode_pvmfw_config_version(1, 2);
        header.flags = Self::DEFAULT_FLAGS;
        header.total_size = Self::PADDED_SIZE.try_into()?;
        header_pad.fill(0u8);
        Ok((header, remains))
    }

    fn set_config_entries(&mut self, entry_sizes: EntryBufsSizes) -> Result<()> {
        let mut total_size = SafeNum::from(Self::PADDED_SIZE);

        for (entry, (entry_len, padded_len)) in self.entries.iter_mut().zip(entry_sizes) {
            if entry_len > padded_len || padded_len % PvmfwConfEntry::ALIGNMENT != 0 {
                return Err(Error::BadBufferSize.into());
            }
            entry.offset = total_size.try_into().map_err(Error::ArithmeticOverflow)?;
            entry.size = entry_len.try_into()?;
            total_size += padded_len;
        }
        self.total_size = total_size.try_into().map_err(Error::ArithmeticOverflow)?;
        Ok(())
    }

    const fn encode_pvmfw_config_version(major: u16, minor: u16) -> u32 {
        ((major as u32) << 16) | (minor as u32)
    }
}

/// Write the pvmfw configuration to the output buffer. Creates the configuration header and appends
/// the configuration entries.
fn write_pvmfw_config<'a, T: AVFVerificationData>(
    ops: &mut impl GblOps<'a>,
    config_out: &mut [u8],
    scratch_buffer: &mut [u8],
    boot_info: &BootInfo<T>,
) -> Result<usize> {
    let (header, entries) = PvmfwConfHeader::init_padded_prefix_mut(config_out)?;

    // Write pvmfw config entries
    let (bcc_len, bcc_padded_len, rest) =
        pvmfw_build_dice_handover(ops, entries, boot_info, scratch_buffer)?;
    let (ref_dt_len, ref_dt_padded_len, _) = pvmfw_build_reference_dt(ops, rest, boot_info)?;
    let entry_sizes = [(bcc_len, bcc_padded_len), (0, 0), (0, 0), (ref_dt_len, ref_dt_padded_len)];

    // Finally, update header config entries
    header.set_config_entries(entry_sizes)?;
    Ok(header.total_size.try_into()?)
}

fn pad_entry_split_rest(buffer: &mut [u8], entry_size: usize) -> Result<(usize, &mut [u8])> {
    let padded_size = align_up(entry_size, PvmfwConfEntry::ALIGNMENT)?;
    let (padded_entry, rest) = split(buffer, padded_size)?;
    padded_entry[entry_size..].fill(0u8);
    Ok((padded_size, rest))
}

const REF_DT_AVF_PATH: &str = "/avf";
const REF_DT_AVB_PATH: &str = "/firmware/android";
const HOST_DT_AVF_PATH: &str = "/avf/reference/avf";
const SK_PUB_KEY_PROP: &CStr = c"secretkeeper_public_key";
const VENDOR_HASH_PROP: &CStr = c"vendor_hashtree_descriptor_root_digest";

/// Write an FDT (the VM reference DT) to the output buffer and return its size, its padded size,
/// and the unused portion of the buffer.
fn pvmfw_build_reference_dt<'a, 'b, T: AVFVerificationData>(
    ops: &mut impl GblOps<'a>,
    output_buffer: &'b mut [u8],
    boot_info: &BootInfo<T>,
) -> Result<(usize, usize, &'b mut [u8])> {
    let mut ref_dt = Fdt::new_empty(&mut output_buffer[..])?;
    write_ref_dt_properties(ops, &mut ref_dt, REF_DT_AVF_PATH, boot_info.verify_data)?;
    boot_info.as_avb_dt_props(&mut ref_dt, REF_DT_AVB_PATH)?;
    ref_dt.shrink_to_fit()?;
    let entry_size = ref_dt.size()?;
    let (entry_padded_size, rest) = pad_entry_split_rest(output_buffer, entry_size)?;
    Ok((entry_size, entry_padded_size, rest))
}

fn write_ref_dt_properties<'a, T>(
    ops: &mut impl GblOps<'a>,
    target_dt: &mut Fdt<T>,
    avf_node_path: &str,
    verify_data: &impl AVFVerificationData,
) -> Result<()>
where
    T: AsMut<[u8]> + AsRef<[u8]>,
{
    // AVF node must be present
    target_dt.ensure_node(avf_node_path)?;

    // Write the secretkeeper public key.
    // The maximum size of a key returned from a Secretkeeper implementation depends on the
    // type of the key, so reserve enough for the largest key. See details:
    // https://cs.android.com/android/platform/superproject/main/+/main:external/trusty/bootloader/ql-tipc/include/trusty/secretkeeper.h;l=44
    // This property is required if updateable VMs feature is supported and Secretkeeper HAL
    // implementation exists.
    const SECRETKEEPER_KEY_BUFFER_SIZE: usize = 128;

    let mut sk_buf = [0u8; SECRETKEEPER_KEY_BUFFER_SIZE];
    let secretkeeper_public_key = ops.avf_read_secretkeeper_public_key(&mut sk_buf).ok().flatten();
    if let Some(sk_key) = secretkeeper_public_key {
        target_dt.set_property(avf_node_path, SK_PUB_KEY_PROP, sk_key)?;
    }

    // Write the vendor hashtree digest value. This property is required for vendor image
    // verification in Microdroid (eg for VM device assignment use). Otherwise it can be left out.
    let hashtree_digest = verify_data.vendor_hashtree_digest();
    if let Some(digest) = hashtree_digest {
        target_dt.set_property(avf_node_path, VENDOR_HASH_PROP, digest)?;
    }
    Ok(())
}

/// Add AVF-specific properties to host FDT
pub fn avf_fixup_host_dt<'a, T>(
    ops: &mut impl GblOps<'a>,
    host_dt: &mut Fdt<T>,
    pvmfw_buf: &[u8],
    pvmfw_bin_len: usize,
    verify_data: &impl AVFVerificationData,
) -> Result<()>
where
    T: AsMut<[u8]> + AsRef<[u8]>,
{
    pkvm_describe_pvmfw_resvmem(host_dt, pvmfw_buf, pvmfw_bin_len)?;
    write_ref_dt_properties(ops, host_dt, HOST_DT_AVF_PATH, verify_data)?;
    Ok(())
}

pub const PROTECTED_PROP: &str = "androidboot.hypervisor.protected_vm.supported";
pub const UNPROTECTED_PROP: &str = "androidboot.hypervisor.vm.supported";
pub const VMDTBO_IDX_PROP: &str = "androidboot.hypervisor.vm_dtbo_idx";
pub const VMDTBO_SOURCE_PROP: &str = "androidboot.hypervisor.vm_dtbo_source";

/// Add AVF-specific parameters to bootconfig
///
/// # Note
/// `androidboot.hypervisor.version` is free-form and should be set by vendor via bootconfig fixup
pub fn avf_update_bootconfig<'a>(
    ops: &mut impl GblOps<'a>,
    bootconfig: &mut BootConfigBuilder,
    vmdtbo_metadata: Option<&DtComponentSourceMetadata>,
) -> core::result::Result<(), Error> {
    for prop in [PROTECTED_PROP, UNPROTECTED_PROP] {
        if bootconfig.config_str().contains(prop) {
            gbl_println!(
                ops,
                "WARNING: Unexpected property `{prop}` is detected in the platform \
                bootconfig, this will not be supported by GBL in the future versions and will \
                cause GBL boot failure."
            );
        } else {
            bootconfig.add_item(prop, 1)?;
        }
    }
    if let Some(metadata) = vmdtbo_metadata {
        bootconfig.add_item(VMDTBO_IDX_PROP, metadata.source_index)?;
        bootconfig.add_item(VMDTBO_SOURCE_PROP, metadata.source)?;
    }
    Ok(())
}

type Hidden = [u8; HIDDEN_SIZE];
type Hash = [u8; HASH_SIZE];
type DiceInputs = (Hash, Hash, Hidden, DiceMode, Option<u64>);

fn prepare_dice_inputs(
    verify_data: &impl AVFVerificationData,
    unlocked: bool,
    is_recovery: bool,
) -> Result<DiceInputs> {
    let authority = if unlocked {
        verify_data.public_key_digest::<Sha512>(None).unwrap_or([0u8; Sha512::DIGEST_SIZE])
    } else {
        verify_data
            .public_key_digest::<Sha512>(None)
            .map_err(|_| Error::Other(Some("vbmeta verify error")))?
    };
    let mode = match (is_recovery, unlocked) {
        (false, false) => DiceMode::kDiceModeNormal,
        (true, false) => DiceMode::kDiceModeMaintenance,
        (_, true) => DiceMode::kDiceModeDebug,
    };
    let code = verify_data.vbmeta_digest_sha512();
    let hidden = [0u8; HIDDEN_SIZE]; // Leave hidden input empty.
    let rollback_idx = match verify_data.vbmeta_rollback_index() {
        Err(_) if unlocked => None,
        res => Some(res?),
    };
    Ok((authority, code, hidden, mode, rollback_idx))
}

/// Prepare the DICE handover config entry of pvmfw
fn pvmfw_build_dice_handover<'a, 'b, T: AVFVerificationData>(
    ops: &mut impl GblOps<'a>,
    output_buffer: &'b mut [u8],
    boot_info: &BootInfo<T>,
    scratch_buffer: &mut [u8],
) -> Result<(usize, usize, &'b mut [u8])> {
    const MAX_CONFIG_SIZE: usize = 64; // Enough for our config descriptor
    let (conf_desc_buffer, vendor_handover_buffer) = scratch_buffer
        .split_at_mut_checked(MAX_CONFIG_SIZE)
        .ok_or(Error::BufferTooSmall(Some(MAX_CONFIG_SIZE)))?;

    // Get vendor handover
    let vendor_handover = ops
        .avf_read_vendor_dice_handover(vendor_handover_buffer)
        .inspect_err(|e| gbl_println!(ops, "read vendor handover error: {e}"))?;
    if vendor_handover.is_empty() {
        return Err(Error::Other(Some("empty vendor handover")));
    }
    let (authority, code, hidden, mode, rollback_idx) =
        prepare_dice_inputs(boot_info.verify_data, boot_info.unlocked, boot_info.is_recovery)
            .inspect_err(|e| gbl_println!(ops, "Error preparing DICE inputs: {e}"))?;

    // Create config
    let config_values = DiceAndroidConfig {
        component_name: Some(c"pvmfw"),
        resettable: true,
        security_version: rollback_idx,
        rkp_vm_marker: true,
        ..Default::default()
    };

    let conf_size = dice_android_format_config_descriptor(&config_values, conf_desc_buffer)
        .map_err(Error::DiceError)?;
    let config_desc = Config::Descriptor(&conf_desc_buffer[..conf_size]);

    // Get next handover
    let input_values = InputValues::new(code, config_desc, authority, mode, hidden);
    let entry_size =
        dice_android_handover_main_flow(&vendor_handover, &input_values, output_buffer)
            .map_err(Error::DiceError)?;

    let (entry_padded_size, rest) = pad_entry_split_rest(output_buffer, entry_size)?;
    Ok((entry_size, entry_padded_size, rest))
}

#[cfg(test)]
pub(crate) mod test {
    use super::*;
    use crate::{
        constants::{PAGE_SIZE, PVMFW_DATA_ALIGNMENT},
        device_tree::DtComponentSource,
        ops::test::{FakeGblOps, FakeGblOpsStorage},
    };
    use fdt::{DEFAULT_ADDRESS_CELLS, DEFAULT_SIZE_CELLS};
    use libtestutils::AlignedBuffer;

    struct TestVerifyData<T: AsRef<[u8]>> {
        vendor_digest: Option<T>,
        rollback_index: Option<u64>,
    }

    impl<T: AsRef<[u8]>> TestVerifyData<T> {
        fn new(vendor_digest: Option<T>, rollback_index: Option<u64>) -> Self {
            Self { vendor_digest, rollback_index }
        }
    }

    impl Default for TestVerifyData<&[u8]> {
        fn default() -> Self {
            Self { vendor_digest: None, rollback_index: None }
        }
    }

    fn digest<T: Hasher>(data: &[u8]) -> T::Output {
        let mut ctx = T::new();
        ctx.update(data);
        ctx.finish()
    }

    impl<T: AsRef<[u8]>> AVFVerificationData for TestVerifyData<T> {
        fn vendor_hashtree_digest(&self) -> Option<&[u8]> {
            self.vendor_digest.as_ref().map(|t| t.as_ref())
        }

        fn vbmeta_digest_sha512(&self) -> [u8; Sha512::DIGEST_SIZE] {
            digest::<Sha512>(&[1, 2, 3, 4, 5])
        }

        fn vbmeta_digest_sha256(&self) -> [u8; Sha256::DIGEST_SIZE] {
            digest::<Sha256>(&[10, 11, 12, 13, 14, 15])
        }

        fn public_key_digest<U: Hasher>(
            &self,
            _vbmeta: Option<&str>,
        ) -> core::result::Result<U::Output, VbmetaVerifyError> {
            Ok(digest::<U>(&[5, 4, 3, 2, 1]))
        }

        fn vbmeta_rollback_index(&self) -> Result<u64> {
            self.rollback_index.ok_or(Error::NotFound)
        }
    }

    fn dummy_pvmfw_binary(fill_value: u8, fill_count: usize) -> Vec<u8> {
        let mut pvmfw_bin_buf = vec![fill_value; fill_count];
        pvmfw_bin_buf.resize(align_up(fill_count, PAGE_SIZE).unwrap(), 0);
        pvmfw_bin_buf
    }

    /// Returns a test pvmfw partition
    pub(crate) fn dummy_pvmfw_partition(fill_value: u8, fill_count: usize) -> (Vec<u8>, usize) {
        const HEADER_SIZE: usize = 4096;
        let binary = dummy_pvmfw_binary(fill_value, fill_count);
        let mut partition = vec![
            0x41, 0x4e, 0x44, 0x52, // magic
            0x4f, 0x49, 0x44, 0x21, // magic
            0x00, 0x00, 0x00, 0x00, // kernel size (binary size)
            0x00, 0x00, 0x00, 0x00, // ramdisk size
            0x8b, 0x01, 0x00, 0x1e, // os version
            0x2c, 0x06, 0x00, 0x00, // header size
            0x00, 0x00, 0x00, 0x00, // reserved
            0x00, 0x00, 0x00, 0x00, // reserved
            0x00, 0x00, 0x00, 0x00, // reserved
            0x00, 0x00, 0x00, 0x00, // reserved
            0x03, 0x00, 0x00, 0x00, // version
        ];
        partition.resize(HEADER_SIZE + binary.len(), 0);
        partition[8..12].copy_from_slice(&(fill_count as u32).to_le_bytes());
        partition[HEADER_SIZE..].copy_from_slice(&binary);
        (partition, align_up(fill_count, PAGE_SIZE).unwrap() + PvmfwConfHeader::PADDED_SIZE)
    }

    pub(crate) const DUMMY_VENDOR_HANDOVER: [u8; 112] = [
        0xa3, // CDI attest
        0x01, 0x58, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, // CDI seal
        0x02, 0x58, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, // DICE chain
        0x03, 0x82, 0xa6, 0x01, 0x02, 0x03, 0x27, 0x04, 0x02, 0x20, 0x01, 0x21, 0x40, 0x22, 0x40,
        // Last COSE_Sign1: [protected={1:-8}, unprotected={}, payload, signature=""]
        // payload bstr wraps {SubjectPublicKey(-4670552): bstr(COSE_Key{3:-8})} so
        // dice_android_handover_main_flow can recover the leaf subject key algorithm.
        0x84, 0x43, 0xa1, 0x01, 0x27, 0xa0, 0x4a, 0xa1, 0x3a, 0x00, 0x47, 0x44, 0x57, 0x43, 0xa1,
        0x03, 0x27, 0x40,
        // 8-bytes of trailing data that aren't part of the DICE chain.
        0x84, 0x41, 0x55, 0xa0, 0x42, 0x11, 0x22, 0x40,
    ];

    fn build_test_pvmfw_data(
        out_pvmfw_buf: &mut [u8],
        pvmfw_bin_size: usize,
        kernel_attrs: &KernelAttributes,
        dtbo_part: &[u8],
    ) -> Result<usize> {
        let storage = FakeGblOpsStorage::default();
        let mut ops = FakeGblOps::new(&storage);
        ops.avf_is_supported = true;
        ops.avb_ops.unlock_state = Ok(true);
        ops.avb_ops.rollbacks.insert(0, Ok(1));
        ops.avf_vendor_dice_handover = Some(&DUMMY_VENDOR_HANDOVER[..]);
        let testdigest = TestVerifyData::new(Some([1, 2, 3, 4, 5]), Some(0));
        let boot_info = BootInfo::new(false, false, BootStateColor::Green, &testdigest);
        build_pvmfw_data_region(
            &mut ops,
            out_pvmfw_buf,
            &dummy_pvmfw_binary(0xAB, pvmfw_bin_size),
            kernel_attrs,
            &boot_info,
            dtbo_part,
        )
    }

    #[test]
    fn test_build_pvmfw_data_region_aligned_to_kernel_page_size_4k() {
        const BIN_SIZE: usize = 0xc00;
        let attrs = KernelAttributes { reserved_size: 0, page_size: 4 * KiB!(1) };
        let mut out_pvmfw_buf = AlignedBuffer::new(0x100000, attrs.page_size);
        let used_bytes =
            build_test_pvmfw_data(&mut out_pvmfw_buf, BIN_SIZE, &attrs, &[][..]).unwrap();
        assert!(used_bytes > attrs.page_size);
        assert_eq!(used_bytes % attrs.page_size, 0);
        assert!(&out_pvmfw_buf[..BIN_SIZE].iter().all(|&b| b == 0xAB));
    }

    #[test]
    fn test_build_pvmfw_data_region_aligned_to_kernel_page_size_16k() {
        const BIN_SIZE: usize = 0xc00;
        let attrs = KernelAttributes { reserved_size: 0, page_size: 16 * KiB!(1) };
        let mut out_pvmfw_buf = AlignedBuffer::new(0x100000, attrs.page_size);
        let used_bytes =
            build_test_pvmfw_data(&mut out_pvmfw_buf, BIN_SIZE, &attrs, &[][..]).unwrap();
        assert_eq!(used_bytes % attrs.page_size, 0);
    }

    #[test]
    fn test_build_pvmfw_data_region_invalid_alignment() {
        const BIN_SIZE: usize = 0xc00;
        let attrs = KernelAttributes { reserved_size: 0, page_size: 4 * KiB!(1) };
        let mut out_pvmfw_buf = AlignedBuffer::new(0x100000, attrs.page_size);
        let unaligned_buf = &mut out_pvmfw_buf[1..];
        let err = build_test_pvmfw_data(unaligned_buf, BIN_SIZE, &attrs, &[][..]).unwrap_err();
        assert!(matches!(err, Error::InvalidAlignment));
    }

    fn parse_pvmfw_data_conf(
        pvmfw_data: &[u8],
        bin_size: usize,
    ) -> (&PvmfwConfHeader, [Vec<u8>; NUM_PVMFW_CONFIG_ENTRIES]) {
        let (_, conf_buf) = pvmfw_data.split_at_checked(bin_size).unwrap();
        let (conf_header_buf, _) = conf_buf.split_at_checked(size_of::<PvmfwConfHeader>()).unwrap();
        let header = PvmfwConfHeader::ref_from_bytes(conf_header_buf).unwrap();
        let mut entries: [Vec<u8>; NUM_PVMFW_CONFIG_ENTRIES] = std::array::from_fn(|_| Vec::new());
        for i in 0..NUM_PVMFW_CONFIG_ENTRIES {
            let size = header.entries[i].size as usize;
            let offset = header.entries[i].offset as usize;
            entries[i] = conf_buf[offset..offset + size].into();
        }
        (header, entries)
    }

    #[test]
    fn test_inject_vmdtbo_aligned_to_kernel_page_size_4k() {
        const BIN_SIZE: usize = 0x1000;
        const VMDTBO_ENTRY_IDX: usize = 2;
        let vmdtbo = [0xcd; 50];
        let dtbo_part = include_bytes!("../../testdata/android/dtbo_a.img").to_vec();
        let attrs = KernelAttributes { reserved_size: 0, page_size: 4 * KiB!(1) };
        let mut out_pvmfw_buf = AlignedBuffer::new(0x100000, attrs.page_size);
        build_test_pvmfw_data(&mut out_pvmfw_buf, BIN_SIZE, &attrs, &dtbo_part).unwrap();
        let (conf_header, mut conf_entries) = parse_pvmfw_data_conf(&out_pvmfw_buf, BIN_SIZE);
        let old_conf_size = conf_header.total_size;
        assert_eq!(conf_entries[VMDTBO_ENTRY_IDX].len(), 0);

        let total_sz = inject_vmdtbo(&mut out_pvmfw_buf, BIN_SIZE, &attrs, &vmdtbo).unwrap();
        let (conf_header, new_conf_entries) = parse_pvmfw_data_conf(&out_pvmfw_buf, BIN_SIZE);

        conf_entries[VMDTBO_ENTRY_IDX] = vmdtbo.into(); // VMDTBO entry should contain data now
        assert!(old_conf_size < conf_header.total_size);
        assert_eq!(conf_entries, new_conf_entries);
        assert_eq!(total_sz % attrs.page_size, 0);
    }

    #[test]
    fn test_inject_vmdtbo_aligned_to_kernel_page_size_16k() {
        const BIN_SIZE: usize = 0x1000;
        let vmdtbo = [0xcd; 50];
        let dtbo_part = include_bytes!("../../testdata/android/dtbo_a.img").to_vec();
        let attrs = KernelAttributes { reserved_size: 0, page_size: 16 * KiB!(1) };
        let mut out_pvmfw_buf = AlignedBuffer::new(0x100000, attrs.page_size);
        build_test_pvmfw_data(&mut out_pvmfw_buf, BIN_SIZE, &attrs, &dtbo_part).unwrap();
        let total_sz = inject_vmdtbo(&mut out_pvmfw_buf, BIN_SIZE, &attrs, &vmdtbo).unwrap();
        assert_eq!(total_sz % attrs.page_size, 0);
    }

    #[test]
    fn test_inject_vmdtbo_invalid_alignment() {
        const BIN_SIZE: usize = 0x1000;
        let vmdtbo = [0xcd; 50];
        let dtbo_part = include_bytes!("../../testdata/android/dtbo_a.img").to_vec();
        let attrs = KernelAttributes { reserved_size: 0, page_size: 4 * KiB!(1) };
        let mut out_pvmfw_buf = AlignedBuffer::new(0x100000, attrs.page_size);
        build_test_pvmfw_data(&mut out_pvmfw_buf, BIN_SIZE, &attrs, &dtbo_part).unwrap();
        let err = inject_vmdtbo(&mut out_pvmfw_buf[1..], BIN_SIZE, &attrs, &vmdtbo).unwrap_err();
        assert!(matches!(err, Error::InvalidAlignment));
    }

    #[test]
    fn test_pkvm_describe_pvmfw_resvmem() {
        let buf = AlignedBuffer::new(10, PVMFW_DATA_ALIGNMENT);
        let dummy_bin_len = 4usize;

        let mut fdt_buf = AlignedBuffer::new(1024, 8);
        let mut fdt = Fdt::new_empty(&mut fdt_buf[..]).unwrap();

        pkvm_describe_pvmfw_resvmem(&mut fdt, &buf, dummy_bin_len).unwrap();

        assert_eq!(
            fdt.get_property_u32("/reserved-memory", std_props::ADDRESS_CELLS).unwrap(),
            DEFAULT_ADDRESS_CELLS
        );
        assert_eq!(
            fdt.get_property_u32("/reserved-memory", std_props::SIZE_CELLS).unwrap(),
            DEFAULT_SIZE_CELLS
        );
        assert_eq!(fdt.get_property("/reserved-memory", std_props::RANGES).unwrap(), &[]);
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
        assert_eq!(&reg_prop[..8], (buf.as_ptr() as usize).to_be_bytes());
        assert_eq!(&reg_prop[8..], (buf.len() as u32).to_be_bytes());

        let conf_offset_prop = fdt
            .get_property("/reserved-memory/pkvm_guest_firmware", c"config-data-offset")
            .unwrap();
        assert_eq!(conf_offset_prop, (dummy_bin_len as u32).to_be_bytes());
    }

    #[test]
    fn test_write_pvmfw_config() {
        let mut buf = AlignedBuffer::new(2000, PVMFW_DATA_ALIGNMENT);
        let storage = FakeGblOpsStorage::default();
        let mut ops = FakeGblOps::new(&storage);
        ops.avf_is_supported = true;
        ops.avb_ops.unlock_state = Ok(true);
        ops.avb_ops.rollbacks.insert(0, Ok(1));
        ops.avf_vendor_dice_handover = Some(&DUMMY_VENDOR_HANDOVER[..]);
        let testdigest = TestVerifyData::new(Some([1, 2, 3, 4, 5]), Some(0));
        let boot_info = BootInfo::new(false, false, BootStateColor::Green, &testdigest);
        let mut scratch_buffer = [0u8; 256];

        let sz = write_pvmfw_config(&mut ops, &mut buf, &mut scratch_buffer, &boot_info).unwrap();
        let header = PvmfwConfHeader::ref_from_prefix(&buf).unwrap().0;

        let exp_refdt_size = 0x203u32;
        let exp_handover_size = 0x256u32;
        let exp_refdt_offset = (PvmfwConfHeader::PADDED_SIZE
            + align_up(exp_handover_size as usize, PvmfwConfEntry::ALIGNMENT).unwrap())
            as u32;
        let expected_entries = [
            PvmfwConfEntry { offset: PvmfwConfHeader::PADDED_SIZE as u32, size: exp_handover_size },
            PvmfwConfEntry { offset: exp_refdt_offset, size: 0 },
            PvmfwConfEntry { offset: exp_refdt_offset, size: 0 },
            PvmfwConfEntry { offset: exp_refdt_offset, size: exp_refdt_size },
        ];
        let expected_header = PvmfwConfHeader {
            magic: PvmfwConfHeader::MAGIC,
            version: PvmfwConfHeader::encode_pvmfw_config_version(1, 2),
            total_size: sz as u32,
            flags: PvmfwConfHeader::DEFAULT_FLAGS,
            entries: expected_entries,
        };
        assert_eq!(header, &expected_header);
    }

    #[test]
    fn test_write_avf_bootconfig() {
        let mut ops = FakeGblOps::new(&[][..]);
        let mut bootconf_buffer = [0u8; 256];
        let mut bootconfig = BootConfigBuilder::new(&mut bootconf_buffer).unwrap();

        let bootconf_str = bootconfig.config_str();
        assert!(!bootconf_str.contains(PROTECTED_PROP));
        assert!(!bootconf_str.contains(UNPROTECTED_PROP));

        avf_update_bootconfig(&mut ops, &mut bootconfig, None).unwrap();
        assert!(!bootconfig.config_str().contains(VMDTBO_IDX_PROP));
        assert!(!bootconfig.config_str().contains(VMDTBO_SOURCE_PROP));
        assert_eq!(bootconfig.config_str().matches(PROTECTED_PROP).count(), 1);
        assert_eq!(bootconfig.config_str().matches(UNPROTECTED_PROP).count(), 1);

        let metadata =
            DtComponentSourceMetadata { source: DtComponentSource::Dtbo, source_index: 5 };
        avf_update_bootconfig(&mut ops, &mut bootconfig, Some(&metadata)).unwrap();
        assert_eq!(bootconfig.config_str().matches(PROTECTED_PROP).count(), 1);
        assert_eq!(bootconfig.config_str().matches(UNPROTECTED_PROP).count(), 1);
        assert!(bootconfig.config_str().contains(&format!("{VMDTBO_IDX_PROP}=5")));
        assert!(bootconfig.config_str().contains(&format!("{VMDTBO_SOURCE_PROP}=dtbo")));
    }

    #[test]
    fn test_fixup_host_dt() {
        let test_digest = [5u8; 64];
        let digest = TestVerifyData::new(Some(&test_digest), None);
        let sk_key = FakeGblOps::GBL_TEST_AVF_SECRET_KEEPER_PUBLIC_KEY;
        let mut ops = FakeGblOps::new(&[][..]);
        ops.avf_is_supported = true;
        let dummy_buf = [0u8; 4];
        let dummy_len = 2;

        let mut hostdt_buf = AlignedBuffer::new(1024, 8);
        let mut fdt = Fdt::new_empty(&mut hostdt_buf[..]).unwrap();

        avf_fixup_host_dt(&mut ops, &mut fdt, &dummy_buf, dummy_len, &digest).unwrap();

        assert_eq!(fdt.get_property(HOST_DT_AVF_PATH, VENDOR_HASH_PROP).unwrap(), test_digest);
        assert_eq!(fdt.get_property(HOST_DT_AVF_PATH, SK_PUB_KEY_PROP).unwrap(), sk_key);
    }

    #[test]
    fn test_refdt_avb_prop_values() {
        let test_digest = [5u8; 64];
        let verify_data = TestVerifyData::new(Some(&test_digest), None);
        let boot_info = BootInfo::new(true, false, BootStateColor::Orange, &verify_data);
        let base_path = "/";

        let mut refdt_buf = AlignedBuffer::new(1024, 8);
        let mut refdt = Fdt::new_empty(&mut refdt_buf[..]).unwrap();
        boot_info.as_avb_dt_props(&mut refdt, base_path).unwrap();
        assert_eq!(
            refdt.get_property(base_path, std_props::COMPATIBLE).unwrap(),
            b"android,firmware\0"
        );
        assert_eq!(
            refdt.get_property(base_path, DEVICE_STATE_PROP).unwrap(),
            boot_info.device_state()
        );
        assert_eq!(refdt.get_property(base_path, VB_STATE_PROP).unwrap(), boot_info.vb_state());
        assert_eq!(
            refdt.get_property(base_path, VBMETA_DIGEST_PROP).unwrap(),
            boot_info.verify_data.vbmeta_digest_sha256(),
        );
        assert_eq!(
            refdt.get_property(base_path, VBMETA_PUBKEY_DIGEST_PROP).unwrap(),
            boot_info.pkey_digest().unwrap(),
        );
    }

    fn ensure_avb_props<T: AsRef<[u8]>>(dt: Fdt<T>, avb_node: &str) {
        for prop in [
            std_props::COMPATIBLE,
            DEVICE_STATE_PROP,
            VBMETA_DIGEST_PROP,
            VBMETA_PUBKEY_DIGEST_PROP,
            VB_STATE_PROP,
        ] {
            dt.get_property(avb_node, prop).unwrap();
        }
    }

    #[test]
    fn test_write_reference_dt() {
        let test_digest = [5u8; 64];
        let digest = TestVerifyData::new(Some(&test_digest), None);
        let boot_info = BootInfo::new(false, false, BootStateColor::Green, &digest);
        let sk_key = FakeGblOps::GBL_TEST_AVF_SECRET_KEEPER_PUBLIC_KEY;
        let mut ops = FakeGblOps::new(&[][..]);
        ops.avf_is_supported = true;

        let mut refdt_buf = AlignedBuffer::new(1024, 8);

        let (ref_dt_size, ref_dt_padded_size, _) =
            pvmfw_build_reference_dt(&mut ops, &mut refdt_buf, &boot_info).unwrap();
        assert!(ref_dt_padded_size % PvmfwConfEntry::ALIGNMENT == 0);

        let refdt = Fdt::new(&refdt_buf[..ref_dt_size]).unwrap();
        assert_eq!(refdt.get_property(REF_DT_AVF_PATH, VENDOR_HASH_PROP).unwrap(), test_digest);
        assert_eq!(refdt.get_property(REF_DT_AVF_PATH, SK_PUB_KEY_PROP).unwrap(), sk_key);
        ensure_avb_props(refdt, REF_DT_AVB_PATH);
    }

    #[test]
    fn test_write_empty_reference_dt() {
        let digest = TestVerifyData::default();
        let boot_info = BootInfo::new(false, false, BootStateColor::Green, &digest);
        let mut ops = FakeGblOps::new(&[][..]);
        ops.avf_is_supported = false;

        let mut refdt_buf = AlignedBuffer::new(1024, 8);
        let (ref_dt_size, ref_dt_padded_size, _) =
            pvmfw_build_reference_dt(&mut ops, &mut refdt_buf, &boot_info).unwrap();
        assert!(ref_dt_padded_size % PvmfwConfEntry::ALIGNMENT == 0);

        let refdt = Fdt::new(&refdt_buf[..ref_dt_size]).unwrap();
        refdt.get_property(REF_DT_AVF_PATH, VENDOR_HASH_PROP).unwrap_err();
        refdt.get_property(REF_DT_AVF_PATH, SK_PUB_KEY_PROP).unwrap_err();
        ensure_avb_props(refdt, REF_DT_AVB_PATH);
    }

    #[test]
    fn test_dice_inputs() {
        let verify_data = TestVerifyData::new(Some(&[][..]), Some(1));
        for (unlocked, is_recovery, exp_mode) in [
            (false, false, DiceMode::kDiceModeNormal),
            (true, false, DiceMode::kDiceModeDebug),
            (true, true, DiceMode::kDiceModeDebug),
            (false, true, DiceMode::kDiceModeMaintenance),
        ] {
            let (authority, code, hidden, mode, rollback_idx) =
                prepare_dice_inputs(&verify_data, unlocked, is_recovery).unwrap();
            assert_eq!(authority, digest::<Sha512>(&[5, 4, 3, 2, 1]));
            assert_eq!(hidden, [0u8; HIDDEN_SIZE]);
            assert_eq!(code, digest::<Sha512>(&[1, 2, 3, 4, 5]));
            assert_eq!(mode, exp_mode);
            assert_eq!(rollback_idx, Some(1));
        }
    }
}
