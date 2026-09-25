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

//! Integration test to verify existence of required and optional protocols.
//! Checks that if a protocol is present its methods and pointer fields are not null.
//!
//! Note: Most protocol methods are not called during the integration test,
//!       especially methods that modify persistent state.
//!
//! Note: Verifying method correctness is beyond the scope of these tests.
//!       Implementation codebases are better equipped to maintain unit and
//!       integration tests to verify method correctness.

#![cfg_attr(not(test), no_std)]

extern crate alloc;

use alloc::{ffi::CString, vec, vec::Vec};
use core::fmt::Write;
use efi::{
    efi_println,
    hash2::{HashAlgorithm, Hasher, Sha256, Sha512},
    protocol::{
        block_io::BlockIoProtocol,
        block_io2::BlockIo2Protocol,
        device_path::{DevicePathProtocol, DevicePathToTextProtocol},
        dt_fixup::DtFixupProtocol,
        erase_block::EraseBlockProtocol,
        gbl_efi_avb::GblAvbProtocol,
        gbl_efi_avf::GblAvfProtocol,
        gbl_efi_boot_control::GblBootControlProtocol,
        gbl_efi_boot_memory::GblBootMemoryProtocol,
        gbl_efi_debug::GblDebugProtocol,
        gbl_efi_fastboot::GblFastbootProtocol,
        gbl_efi_fastboot_transport::GblFastbootTransportProtocol,
        gbl_efi_os_configuration::GblOsConfigurationProtocol,
        loaded_image::LoadedImageProtocol,
        random_number_generator::RandomNumberGeneratorProtocol,
        random_number_generator::RngAlgorithm,
        simple_text_input::SimpleTextInputProtocol,
        simple_text_output::SimpleTextOutputProtocol,
        timestamp::TimestampProtocol,
        Protocol, ProtocolImpl,
    },
    utils::parse_fw_api_level,
    EfiEntry, GBL_EFI_FW_API_LEVEL, GBL_EFI_VENDOR_GUID,
};
use fastboot::MAX_RESPONSE_SIZE;
use liberror::{Error, Result};
use libgbl::{
    android_boot::device_tree::RNG_SEED_SIZE_BYTES, gbl_avb::MAX_SPECIALIZED_PARTITIONS,
    random::should_fallback_to_default_rng,
};
use libutils::base_type_name;

/// Pull in the sysdeps required by libavb so the linker can find them.
extern crate avb_sysdeps;
/// Pull in the sysdeps required by boringssl so the linker can find them.
extern crate boringssl_sysdeps;
/// Pull in the getentropy implementation.
extern crate efi_rng;

type TestEntry = (fn(&EfiEntry) -> Result<()>, &'static str);

macro_rules! test_entry {
    ($fn_name:ident) => {
        ($fn_name, stringify!($fn_name))
    };
}

macro_rules! field_check {
    ($protocol:ident, $( $field:ident ),+ $(,)?) => {{
        let mut res = Ok(());
        $(
            if $protocol.interface().$field.is_none() {
                efi_println!($protocol.efi_entry(), "field is null: {}", stringify!($field));
                res = Err(Error::InvalidInput);
            }
        )*

        res
    }};
}

fn expect_one_handle_for_protocol<'a, P: ProtocolImpl>(
    entry: &'a EfiEntry,
) -> Result<Protocol<'a, P>> {
    let boot_services = entry.system_table().boot_services();
    let handles = boot_services.locate_handle_buffer_by_protocol::<P>()?;
    let mut iter = handles.handles().iter();

    match iter.next() {
        None => {
            efi_println!(entry, "No handles found for protocol '{}'", base_type_name::<P>());
            Err(Error::InvalidInput)
        }
        Some(handle) => {
            match iter.next() {
                // Exactly one handle.
                None => boot_services.open_protocol::<P>(*handle).inspect_err(|_| {
                    efi_println!(entry, "Error opening protocol: {}", base_type_name::<P>())
                }),
                Some(_) => {
                    efi_println!(
                        entry,
                        "Expected exactly one handle for protocol '{}', found {}",
                        base_type_name::<P>(),
                        handles.handles().len()
                    );
                    Err(Error::InvalidInput)
                }
            }
        }
    }
}

fn test_simple_text_output(entry: &EfiEntry) -> Result<()> {
    let mut protocol =
        entry.system_table().boot_services().find_first_and_open::<SimpleTextOutputProtocol>()?;

    protocol.reset(false)?;
    writeln!(protocol, "Test string for SimpleTextOutputProtocol")?;

    Ok(())
}

fn test_block_io(entry: &EfiEntry) -> Result<()> {
    let boot_services = entry.system_table().boot_services();
    let block_dev_handles = boot_services.locate_handle_buffer_by_protocol::<BlockIoProtocol>()?;

    let mut res = Ok(());
    for (i, handle) in block_dev_handles.handles().iter().enumerate() {
        let Ok(block_io) = boot_services.open_protocol::<BlockIoProtocol>(*handle) else {
            efi_println!(
                entry,
                "Error opening protocol on handle '{}': {}",
                i,
                stringify!(BlockIoProtocol)
            );
            res = Err(Error::InvalidInput);
            continue;
        };

        efi_println!(entry, "Checking fields for {}th block_io dev handle", i);
        if let Err(e) = field_check!(block_io, reset, read_blocks, write_blocks, flush_blocks) {
            res = Err(e);
        }

        // Non-function pointers are represented as pointers, which can be NULL,
        // but for some reason bindgen turns function pointers into Options.
        // BlockIO `media` is one of the few non-function pointers, so just special case
        // it instead of complicating the `field_check!` macro.
        if block_io.interface().media == core::ptr::null_mut() {
            efi_println!(entry, "field is null: media");
            res = Err(Error::InvalidInput);
        }
    }
    res
}

fn test_random_number_generator(entry: &EfiEntry) -> Result<()> {
    let protocol = entry
        .system_table()
        .boot_services()
        .find_first_and_open::<RandomNumberGeneratorProtocol>()?;

    efi_println!(entry, "Checking getting 8 bytes of RNG");
    let x = protocol.get_rng::<u64>(RngAlgorithm::Default)?;
    let y = protocol.get_rng::<u64>(RngAlgorithm::Default)?;

    if x == y {
        efi_println!(
            entry,
            "Two random u64s are equal with value {x}. This is probably an implementation bug"
        );
        return Err(Error::Other(Some("Unlikely RNG collision")));
    }

    efi_println!(entry, "Checking getting {RNG_SEED_SIZE_BYTES} bytes of raw RNG.");
    let mut rng_bytes = [0u8; RNG_SEED_SIZE_BYTES];
    match protocol.get_rng_bytes(RngAlgorithm::Raw, &mut rng_bytes) {
        Ok(_) => Ok(()),
        Err(e) if should_fallback_to_default_rng(e) => {
            efi_println!(
                entry,
                "Warning: Obtaining {RNG_SEED_SIZE_BYTES} bytes of raw random data has failed: {e}. \
                Checking getting {RNG_SEED_SIZE_BYTES} of default RNG."
            );
            protocol.get_rng_bytes(RngAlgorithm::Default, &mut rng_bytes)
        }
        Err(e) => Err(e),
    }
}

#[cfg(target_arch = "riscv64")]
fn test_riscv_boot_protocol(entry: &EfiEntry) -> Result<()> {
    use efi::protocol::riscv::RiscvBootProtocol;

    let protocol = expect_one_handle_for_protocol::<RiscvBootProtocol>(entry)?;
    protocol.get_boot_hartid().map(|_| ())
}

fn test_gbl_avb(entry: &EfiEntry) -> Result<()> {
    let protocol = expect_one_handle_for_protocol::<GblAvbProtocol>(entry)?;

    let mut res = protocol
        .read_partition_attributes::<MAX_SPECIALIZED_PARTITIONS>()
        .map(|_| ())
        .inspect_err(|_| efi_println!(entry, "Call to 'read_partition_attributes' failed"));

    if let Err(e) = protocol.read_device_status().map(|_| ()) {
        efi_println!(entry, "Call to 'read_device_status' failed");
        res = Err(e);
    }

    if let Err(e) = field_check!(
        protocol,
        validate_vbmeta_public_key,
        read_rollback_index,
        write_rollback_index,
        read_persistent_value,
        write_persistent_value,
        handle_verification_result,
        write_lock_state,
    ) {
        res = Err(e);
    }

    res
}

fn test_gbl_uefi_variables(entry: &EfiEntry) -> Result<()> {
    let mut buf = [0u8; 32];
    let _: u64 = entry
        .system_table()
        .runtime_services()
        .get_variable(&GBL_EFI_VENDOR_GUID, GBL_EFI_FW_API_LEVEL, &mut buf)
        .and_then(|size| parse_fw_api_level(&buf[..size]))
        .inspect_err(|e| {
            efi_println!(entry, "Failed to get/parse UEFI variable {GBL_EFI_FW_API_LEVEL}: {e}")
        })?;

    Ok(())
}

/// Run tests for all required protocols
pub fn test_all_required_protocols(entry: &EfiEntry) -> Result<()> {
    let tests: &[TestEntry] = &[
        test_entry!(test_simple_text_output),
        test_entry!(test_block_io),
        test_entry!(test_random_number_generator),
        #[cfg(target_arch = "riscv64")]
        test_entry!(test_riscv_boot_protocol),
        test_entry!(test_gbl_avb),
        test_entry!(test_gbl_boot_control),
        test_entry!(test_gbl_uefi_variables),
    ];

    let mut res = Ok(());
    efi_println!(entry, "Running tests on required protocols");
    for (test, name) in tests {
        if let Err(e) = test(entry) {
            efi_println!(entry, "Test failed: {}", name);
            res = Err(e);
        } else {
            efi_println!(entry, "Test passed: {}", name);
        }
    }

    res
}

fn test_block_io2(entry: &EfiEntry) -> Result<()> {
    let boot_services = entry.system_table().boot_services();
    let block_dev_handles = boot_services.locate_handle_buffer_by_protocol::<BlockIo2Protocol>()?;

    let mut res = Ok(());

    for (i, handle) in block_dev_handles.handles().iter().enumerate() {
        let Ok(block_io2) = boot_services.open_protocol::<BlockIo2Protocol>(*handle) else {
            efi_println!(
                entry,
                "Error opening protocol on handle '{}': {}",
                i,
                stringify!(BlockIoProtocol)
            );
            res = Err(Error::InvalidInput);
            continue;
        };

        efi_println!(entry, "Checking fields for {}th block_io2 dev handle", i);
        if let Err(e) =
            field_check!(block_io2, reset, read_blocks_ex, write_blocks_ex, flush_blocks_ex)
        {
            res = Err(e);
        }

        if block_io2.interface().media == core::ptr::null_mut() {
            efi_println!(entry, "field is null: media");
            res = Err(Error::InvalidInput);
        }
    }

    res
}

fn test_erase_block(entry: &EfiEntry) -> Result<()> {
    let boot_services = entry.system_table().boot_services();
    let block_dev_handles =
        boot_services.locate_handle_buffer_by_protocol::<EraseBlockProtocol>()?;

    let mut res = Ok(());
    for (i, handle) in block_dev_handles.handles().iter().enumerate() {
        let Ok(erase_block) = boot_services.open_protocol::<EraseBlockProtocol>(*handle) else {
            efi_println!(
                entry,
                "Error opening protocol on handle '{}: {}",
                i,
                stringify!(EraseBlockProtocol)
            );
            res = Err(Error::InvalidInput);
            continue;
        };

        efi_println!(entry, "Checking fields for {}th erase_block dev handle", i);
        if let Err(e) = field_check!(erase_block, erase_blocks) {
            res = Err(e);
        }
    }

    res
}

fn test_gbl_boot_control(entry: &EfiEntry) -> Result<()> {
    let protocol = expect_one_handle_for_protocol::<GblBootControlProtocol>(entry)?;

    let mut res = Ok(());

    let slot_count = protocol
        .get_slot_count()
        .inspect_err(|_| efi_println!(entry, "Could not get number of boot slots"))?;
    for i in 0..slot_count {
        if let Err(e) = protocol.get_slot_info(i) {
            efi_println!(entry, "Could not load info for slot: {}", i);
            res = Err(e);
        }
    }

    if let Err(e) = protocol.get_current_slot() {
        efi_println!(entry, "Could not get current slot");
        res = Err(e);
    }

    if let Err(e) = protocol.get_one_shot_boot_mode() {
        efi_println!(entry, "Could not get one-shot boot mode");
        res = Err(e);
    }

    if let Err(e) = field_check!(protocol, set_active_slot) {
        res = Err(e);
    }

    res
}

fn test_gbl_avf(entry: &EfiEntry) -> Result<()> {
    let protocol = expect_one_handle_for_protocol::<GblAvfProtocol>(entry)?;

    field_check!(protocol, read_vendor_dice_handover, read_secretkeeper_public_key)
}

fn test_gbl_boot_memory(entry: &EfiEntry) -> Result<()> {
    let protocol = expect_one_handle_for_protocol::<GblBootMemoryProtocol>(entry)?;

    field_check!(protocol, get_partition_buffer, sync_partition_buffer, get_boot_buffer)
}

fn test_gbl_debug(entry: &EfiEntry) -> Result<()> {
    let protocol = expect_one_handle_for_protocol::<GblDebugProtocol>(entry)?;

    field_check!(protocol, fatal_error)
}

fn test_gbl_fastboot(entry: &EfiEntry) -> Result<()> {
    let protocol = expect_one_handle_for_protocol::<GblFastbootProtocol>(entry)?;

    let mut vars: Vec<Vec<CString>> = vec![];
    let _ = protocol
        .get_var_all(|args, _| vars.push(args.iter().map(|a| CString::from(*a)).collect()))
        .inspect_err(|_| efi_println!(entry, "get_var_all failed"));

    let mut res = if let Some(args) = vars.pop() {
        let mut buf = [0u8; MAX_RESPONSE_SIZE];
        protocol
            .get_var(args[0].as_c_str(), args[1..].iter().map(|a| a.as_c_str()), &mut buf)
            .map(|_| ())
    } else {
        efi_println!(entry, "No fastboot variables defined");
        Err(Error::NotFound)
    };

    // Anything that modifies persistent state is not something we really want to run.
    if let Err(e) = field_check!(protocol, get_staged, command_exec,) {
        res = Err(e);
    }

    res
}

fn test_gbl_fastboot_transport(entry: &EfiEntry) -> Result<()> {
    let boot_services = entry.system_table().boot_services();
    let transport_handles =
        boot_services.locate_handle_buffer_by_protocol::<GblFastbootTransportProtocol>()?;

    let mut res = Ok(());
    for (i, handle) in transport_handles.handles().iter().enumerate() {
        let Ok(transport) = boot_services.open_protocol::<GblFastbootTransportProtocol>(*handle)
        else {
            efi_println!(
                entry,
                "Error opening protocol on handle '{}': {}",
                i,
                stringify!(GblFastbootTransportProtocol)
            );
            res = Err(Error::InvalidInput);
            continue;
        };

        if let Err(e) = field_check!(transport, start, stop, receive, send, flush) {
            res = Err(e);
        }
    }

    res
}

fn test_gbl_os_configuration(entry: &EfiEntry) -> Result<()> {
    let protocol = expect_one_handle_for_protocol::<GblOsConfigurationProtocol>(entry)?;

    field_check!(protocol, fixup_bootconfig, select_device_trees, select_fit_configuration)
}

fn test_dt_fixup(entry: &EfiEntry) -> Result<()> {
    let protocol = expect_one_handle_for_protocol::<DtFixupProtocol>(entry)?;

    field_check!(protocol, fixup)
}

fn test_hash2(entry: &EfiEntry) -> Result<()> {
    const TEST_STRING: &'static str = "Sphinx of black quartz, judge my vow!";
    let mut res = Ok(());

    fn hasher_helper<Algo: HashAlgorithm>(
        entry: &EfiEntry,
        reference_digest: Algo::DigestType,
    ) -> Result<()> {
        let mut hasher = Hasher::<Algo>::new(entry)
            .inspect_err(|_| efi_println!(entry, "Hash2 protocol not supported"))?;

        hasher
            .update(TEST_STRING.as_bytes())
            .inspect_err(|_| efi_println!(entry, "Failed to update hash"))?;
        let digest =
            hasher.finalize().inspect_err(|_| efi_println!(entry, "Failed to finalize hash"))?;

        if digest == reference_digest {
            Ok(())
        } else {
            efi_println!(entry, "Digest mismatch");
            Err(Error::BadChecksum)
        }
    }

    const SHA256_EXPECTED_DIGEST: <Sha256 as HashAlgorithm>::DigestType = [
        0x41, 0x53, 0x7f, 0xea, 0x13, 0x62, 0xe8, 0x4c, 0x24, 0x6, 0x69, 0x5f, 0xff, 0x93, 0x4e,
        0x6e, 0xe8, 0x2a, 0x9a, 0xc7, 0x8b, 0xef, 0x29, 0x45, 0xef, 0x14, 0xc3, 0x4e, 0x52, 0x40,
        0x41, 0xee,
    ];
    if let Err(e) = hasher_helper::<Sha256>(entry, SHA256_EXPECTED_DIGEST) {
        efi_println!(entry, "Sha256 hash failed");
        res = Err(e);
    }

    const SHA512_EXPECTED_DIGEST: <Sha512 as HashAlgorithm>::DigestType = [
        0x12, 0x9b, 0x95, 0x27, 0xeb, 0x22, 0xc1, 0x41, 0x24, 0x4d, 0x7b, 0x25, 0x21, 0x58, 0xaa,
        0x6d, 0x63, 0x9c, 0x1e, 0x5e, 0x50, 0x6b, 0x84, 0x6e, 0x15, 0xd9, 0x7e, 0xa6, 0x18, 0xe2,
        0x6d, 0xf5, 0xda, 0x3b, 0x81, 0xe9, 0x2c, 0xe4, 0xad, 0xe7, 0x38, 0x91, 0x9, 0x15, 0x4b,
        0x63, 0x6b, 0x1c, 0x7f, 0xb1, 0xcd, 0x25, 0x1c, 0x81, 0xc, 0xe0, 0x9b, 0x3b, 0x7c, 0x2e,
        0x74, 0x29, 0x1e, 0xc1,
    ];
    if let Err(e) = hasher_helper::<Sha512>(entry, SHA512_EXPECTED_DIGEST) {
        efi_println!(entry, "Sha512 hash failed");
        res = Err(e);
    }

    if libboringssl::CRYPTO_has_asm() == 0 {
        efi_println!(entry, "BoringSSL is compiled with OPENSSL_NO_ASM!");
        res = Err(Error::InvalidInput);
    }

    res
}

fn test_device_path(entry: &EfiEntry) -> Result<()> {
    let boot_services = entry.system_table().boot_services();
    let protocol = boot_services
        .open_protocol::<LoadedImageProtocol>(entry.image_handle())
        .inspect_err(|_| {
            efi_println!(entry, "Optional protocol not found: {}", stringify!(LoadedImageProtocol))
        })?;
    let mut res = Ok(());

    if let Err(e) = boot_services.open_protocol::<DevicePathProtocol>(protocol.device_handle()) {
        efi_println!(entry, "{} not bound on loaded image", stringify!(DevicePathProtocol));
        res = Err(e);
    }

    if let Err(e) = protocol.file_path() {
        efi_println!(entry, "Could not get file_path");
        res = Err(e);
    }

    let Ok(dev_path_to_text) = boot_services.find_first_and_open::<DevicePathToTextProtocol>()
    else {
        efi_println!(
            entry,
            "Optional protocol not found: {}",
            stringify!(DevicePathToTextProtocol)
        );
        return res;
    };

    if let Err(e) =
        field_check!(dev_path_to_text, convert_device_node_to_text, convert_device_path_to_text)
    {
        res = Err(e);
    }

    res
}

fn test_simple_text_input(entry: &EfiEntry) -> Result<()> {
    let protocol = entry
        .system_table()
        .boot_services()
        .find_first_and_open::<SimpleTextInputProtocol>()
        .inspect_err(|_| {
            efi_println!(
                entry,
                "Optional protocol not found: {}",
                stringify!(SimpleTextInputProtocol)
            )
        })?;

    let mut res =
        protocol.reset(false).inspect_err(|_| efi_println!(entry, "Failed to reset console in"));
    if let Err(e) = protocol.read_key_stroke() {
        efi_println!(entry, "Failed to read keystroke beyond no keystroke being there");
        res = Err(e);
    }

    res
}

fn test_timestamp(entry: &EfiEntry) -> Result<()> {
    let protocol = entry
        .system_table()
        .boot_services()
        .find_first_and_open::<TimestampProtocol>()
        .inspect_err(|_| {
            efi_println!(entry, "Optional protocol not found: {}", stringify!(TimestampProtocol))
        })?;

    let _ = protocol
        .get_timestamp()
        .inspect_err(|_| efi_println!(entry, "No implementation for `get_timestamp`"))?;

    protocol
        .get_properties()
        .map(|_| ())
        .inspect_err(|_| efi_println!(entry, "Failed to get timestamp properties"))
}

/// Run tests for all optional protocols
pub fn test_all_optional_protocols(entry: &EfiEntry) -> Result<()> {
    let tests: &[TestEntry] = &[
        test_entry!(test_block_io2),
        test_entry!(test_dt_fixup),
        test_entry!(test_device_path),
        test_entry!(test_erase_block),
        test_entry!(test_gbl_avf),
        test_entry!(test_gbl_boot_memory),
        test_entry!(test_gbl_debug),
        test_entry!(test_gbl_fastboot),
        test_entry!(test_gbl_fastboot_transport),
        test_entry!(test_gbl_os_configuration),
        test_entry!(test_hash2),
        test_entry!(test_simple_text_input),
        test_entry!(test_timestamp),
    ];

    let mut res = Ok(());
    efi_println!(entry, "Running tests on optional protocols");
    for (test, name) in tests {
        if let Err(e) = test(entry) {
            efi_println!(entry, "Test failed: {}", name);
            res = Err(e);
        } else {
            efi_println!(entry, "Test passed: {}", name);
        }
    }

    res
}
