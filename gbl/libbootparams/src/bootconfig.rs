// Copyright 2023, The Android Open Source Project
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

//! Module for constructing bootconfig. See the following for more details:
//!
//! https://source.android.com/docs/core/architecture/bootloader/implementing-bootconfig#bootloader-changes

use crate::slice::SliceWriter;
use core::{fmt::Write, str::from_utf8};
use liberror::{Error, Result};

/// A class for constructing bootconfig section.
pub struct BootConfigBuilder<'a> {
    current_size: usize,
    buffer: &'a mut [u8],
}

const BOOTCONFIG_MAGIC: &str = "#BOOTCONFIG\n";
// Trailer structure:
// struct {
//     config_size: u32,
//     checksum: u32,
//     bootconfig_magic: [u8]
// }
/// Size of the bootconfig trailer.
pub const BOOTCONFIG_TRAILER_SIZE: usize = 4 + 4 + BOOTCONFIG_MAGIC.len();

impl<'a> BootConfigBuilder<'a> {
    /// Initialize with a given buffer.
    pub fn new(buffer: &'a mut [u8]) -> Result<Self> {
        if buffer.len() < BOOTCONFIG_TRAILER_SIZE {
            return Err(Error::BufferTooSmall(Some(BOOTCONFIG_TRAILER_SIZE)));
        }
        let mut ret = Self { current_size: 0, buffer: buffer };
        ret.update_trailer()?;
        Ok(ret)
    }

    /// Initializes from a given buffer with an existing bootconfig.
    ///
    /// # Args
    ///
    /// * `buffer`: The buffer containing an existing bootconfig.
    /// * `size`: The size including trailer.
    pub fn from_prefix_unchecked(buffer: &'a mut [u8], size: usize) -> Result<Self> {
        Ok(Self {
            buffer,
            current_size: size.checked_sub(BOOTCONFIG_TRAILER_SIZE).ok_or(Error::InvalidInput)?,
        })
    }

    /// Get the remaining capacity for adding new bootconfig.
    pub fn remaining_capacity(&self) -> usize {
        self.buffer
            .len()
            .checked_sub(self.current_size)
            .unwrap()
            .checked_sub(BOOTCONFIG_TRAILER_SIZE)
            .unwrap()
    }

    /// Get the whole config bytes including trailer.
    pub fn config_bytes(&self) -> &[u8] {
        // Arithmetic not expected to fail.
        &self.buffer[..self.current_size.checked_add(BOOTCONFIG_TRAILER_SIZE).unwrap()]
    }

    /// Append a new config via a reader callback.
    ///
    /// A `&mut [u8]` that covers the remaining space is passed to the callback for reading the
    /// config bytes. It should return the total size read if operation is successful or
    /// `Error::BufferTooSmall(Some(<minimum_buffer_size>))`. Attempting to return a size
    /// greater than the input will cause it to panic. Empty read is allowed. It's up to the caller
    /// to make sure the read content will eventually form a valid boot config.
    fn add_raw_with<F>(&mut self, reader: F) -> Result<()>
    where
        F: FnOnce(&[u8], &mut [u8]) -> Result<usize>,
    {
        let remaining = self.remaining_capacity();
        let (current_buffer, remaining_buffer) = self.buffer.split_at_mut(self.current_size);

        let res = reader(&current_buffer[..], &mut remaining_buffer[..remaining]);
        if let Ok(size) = res {
            assert!(size <= remaining);
            self.current_size += size;
        }
        // Update the trailer regardless of whether `reader` succeeded or not, since in either case
        // it may have overwritten part or all of the previous trailer, but prioritize `reader()`
        // error if both failed somehow.
        res.and(self.update_trailer())
    }

    /// Append raw config lines via a reader callback, ensuring newline termination.
    ///
    /// The callback reads config bytes into the provided remaining space (less one byte reserved
    /// for the termination) and returns the size read. If the read content does not end with a
    /// newline, one is appended, so that the parameters added next start on a new line. Empty
    /// read adds nothing.
    pub fn add_raw_lines_with<F>(&mut self, reader: F) -> Result<()>
    where
        F: FnOnce(&[u8], &mut [u8]) -> Result<usize>,
    {
        self.add_raw_with(|current, out| {
            let reserved = out.len().saturating_sub(1);
            let size = reader(current, &mut out[..reserved])?;
            assert!(size <= reserved);
            match out[..size].last() {
                None | Some(b'\n') => Ok(size),
                Some(_) => {
                    out[size] = b'\n';
                    Ok(size + 1)
                }
            }
        })
    }

    /// Append a single bootconfig item.
    pub fn add_item(
        &mut self,
        key: impl core::fmt::Display,
        value: impl core::fmt::Display,
    ) -> Result<()> {
        writeln!(self, "{}={}", key, value).map_err(|_| Error::BufferTooSmall(None))
    }

    /// Append a displayable item after passing a check on the serialized string.
    ///
    /// This is useful for callers which want to use the bootconfig buffer to serialize, but then
    /// do some checks on the final value before actually adding it to the bootconfig.
    ///
    /// # Arguments
    ///
    /// * `item`: an item that will be written via `Display`
    /// * `check`: a closure that will be called on the bootconfig line without the trailing
    ///            `\n`. Returning `Err` from the closure will cancel the insertion, leaving
    ///            the bootconfig unmodified.
    ///
    /// # Returns
    ///
    /// `Ok` on success, `Err` if the value failed to write or the check failed.
    pub fn add_checked_item<F>(&mut self, item: impl core::fmt::Display, check: F) -> Result<()>
    where
        F: FnOnce(&str) -> Result<()>,
    {
        self.add_raw_with(|_, out| {
            // Serialize the item to the buffer first.
            let mut writer = SliceWriter::new(out);
            writeln!(writer, "{}", item).map_err(|_| Error::BufferTooSmall(None))?;
            let len = writer.len();

            // `len - 1` to allow the caller to do their checks without the trailing `\n` added by
            // `writeln!()`.
            let s = from_utf8(&out[..len - 1]).map_err(|_| Error::InvalidInput)?;
            check(s)?;

            Ok(len)
        })
    }

    /// Append a bootconfig array item.
    pub fn add_array(
        &mut self,
        key: impl core::fmt::Display,
        items: impl IntoIterator<Item = impl core::fmt::Display>,
    ) -> Result<()> {
        let mut iter = items.into_iter().peekable();
        if iter.peek().is_none() {
            return Ok(());
        }

        self.add_raw_with(|_, out| {
            let mut writer = SliceWriter::new(out);
            write!(writer, "{}={}", key, iter.next().unwrap())
                .map_err(|_| Error::BufferTooSmall(None))?;
            for item in iter {
                write!(writer, ",{}", item).map_err(|_| Error::BufferTooSmall(None))?;
            }
            writeln!(writer).map_err(|_| Error::BufferTooSmall(None))?;
            Ok(writer.len())
        })
    }

    /// Update the boot config trailer at the end of parameter list.
    /// See specification at:
    /// https://source.android.com/docs/core/architecture/bootloader/implementing-bootconfig#bootloader-changes
    fn update_trailer(&mut self) -> Result<()> {
        // Config size
        let size: u32 = self.current_size.try_into().or(Err(Error::Other(None)))?;
        // Check sum.
        let checksum = self.checksum();
        let trailer = &mut self.buffer[self.current_size..];
        trailer[..4].clone_from_slice(&size.to_le_bytes());
        trailer[4..8].clone_from_slice(&checksum.to_le_bytes());
        trailer[8..][..BOOTCONFIG_MAGIC.len()].clone_from_slice(BOOTCONFIG_MAGIC.as_bytes());
        Ok(())
    }

    /// Compute the checksum value.
    fn checksum(&self) -> u32 {
        self.buffer[..self.current_size]
            .iter()
            .map(|v| *v as u32)
            .reduce(|acc, v| acc.overflowing_add(v).0)
            .unwrap_or(0)
    }

    /// Returns the bootcofnig string, excluding the trailer.
    pub fn config_str(&self) -> &str {
        from_utf8(&self.buffer[..self.current_size]).unwrap()
    }
}

/// Extracts bootconfig string from a buffer with bootconfig.
///
/// CRC is not checked.
pub fn extract_bootconfig(buffer: &[u8]) -> Result<&str> {
    let (buf, trailer) = buffer
        .split_last_chunk::<BOOTCONFIG_TRAILER_SIZE>()
        .ok_or(Error::BufferTooSmall(Some(BOOTCONFIG_TRAILER_SIZE)))?;
    let sz = usize::try_from(u32::from_le_bytes(trailer[..4].try_into().unwrap()))?;
    let off = buf.len().checked_sub(sz).ok_or(Error::BufferTooSmall(Some(sz)))?;
    from_utf8(&buf[off..]).map_err(|_| Error::InvalidInput)
}

impl core::fmt::Display for BootConfigBuilder<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let bytes = self.config_bytes();
        for val in &bytes[..bytes.len().checked_sub(BOOTCONFIG_TRAILER_SIZE).unwrap()] {
            write!(f, "{}", core::ascii::escape_default(*val))?;
        }
        Ok(())
    }
}

impl core::fmt::Write for BootConfigBuilder<'_> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.add_raw_with(|_, out| {
            out.get_mut(..s.len())
                .ok_or(Error::BufferTooSmall(Some(s.len())))?
                .clone_from_slice(s.as_bytes());
            Ok(s.len())
        })
        .map_err(|_| core::fmt::Error)?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use core::fmt::Write;

    // Taken from Cuttlefish on QEMU aarch64.
    const TEST_CONFIG: &str = "androidboot.hardware=cutf_cvm
kernel.mac80211_hwsim.radios=0
kernel.vmw_vsock_virtio_transport_common.virtio_transport_max_vsock_pkt_buf_size=16384
androidboot.vendor.apex.com.google.emulated.camera.provider.hal=com.google.emulated.camera.provider.hal
androidboot.slot_suffix=_a
androidboot.force_normal_boot=1
androidboot.hw_timeout_multiplier=50
androidboot.fstab_suffix=cf.f2fs.hctr2
androidboot.hypervisor.protected_vm.supported=0
androidboot.modem_simulator_ports=9600
androidboot.vsock_lights_port=6900
androidboot.lcd_density=320
androidboot.vendor.audiocontrol.server.port=9410
androidboot.vendor.audiocontrol.server.cid=3
androidboot.cuttlefish_config_server_port=6800
androidboot.hardware.gralloc=minigbm
androidboot.vsock_lights_cid=3
androidboot.enable_confirmationui=0
androidboot.hypervisor.vm.supported=0
androidboot.setupwizard_mode=DISABLED
androidboot.serialno=CUTTLEFISHCVD011
androidboot.enable_bootanimation=1
androidboot.hardware.hwcomposer.display_finder_mode=drm
androidboot.hardware.angle_feature_overrides_enabled=preferLinearFilterForYUV:mapUnspecifiedColorSpaceToPassThrough
androidboot.hardware.egl=mesa
androidboot.boot_devices=4010000000.pcie
androidboot.opengles.version=196608
androidboot.wifi_mac_prefix=5554
androidboot.vsock_tombstone_port=6600
androidboot.hardware.hwcomposer=ranchu
androidboot.hardware.hwcomposer.mode=client
androidboot.console=ttyAMA0
androidboot.ddr_size=4915MB
androidboot.cpuvulkan.version=0
androidboot.serialconsole=1
androidboot.vbmeta.device=PARTUUID=2b7e273a-42a1-654b-bbad-8cb6ab2b6911
androidboot.vbmeta.avb_version=1.1
androidboot.vbmeta.device_state=unlocked
androidboot.vbmeta.hash_alg=sha256
androidboot.vbmeta.size=23040
androidboot.vbmeta.digest=6d6cdbad779475dd945ed79e6bd79c0574541d34ff488fa5aeeb024d739dd0d2
androidboot.vbmeta.invalidate_on_error=yes
androidboot.veritymode=enforcing
androidboot.verifiedbootstate=orange
";

    const TEST_CONFIG_TRAILER: &[u8; BOOTCONFIG_TRAILER_SIZE] =
        b"i\x07\x00\x00\xf9\xc4\x02\x00#BOOTCONFIG\n";

    #[test]
    fn test_add() {
        let mut buffer = [0u8; TEST_CONFIG.len() + TEST_CONFIG_TRAILER.len()];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();
        write!(builder, "{}", TEST_CONFIG).unwrap();
        assert_eq!(
            builder.config_bytes().to_vec(),
            [TEST_CONFIG.as_bytes(), TEST_CONFIG_TRAILER].concat().to_vec()
        );

        assert_eq!(extract_bootconfig(&buffer[..]).unwrap(), TEST_CONFIG);
    }

    #[test]
    fn test_add_with_incremental() {
        let mut buffer = [0u8; TEST_CONFIG.len() + TEST_CONFIG_TRAILER.len()];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();

        let mut offset = 0;
        for ele in TEST_CONFIG.strip_suffix('\n').unwrap().split('\n') {
            let config = std::string::String::from(ele) + "\n";

            builder
                .add_raw_with(|current, out| {
                    assert_eq!(current, &TEST_CONFIG.as_bytes()[..offset]);

                    out[..config.len()].copy_from_slice(config.as_bytes());
                    Ok(config.len())
                })
                .unwrap();

            offset += config.len();
        }
        assert_eq!(
            builder.config_bytes().to_vec(),
            [TEST_CONFIG.as_bytes(), TEST_CONFIG_TRAILER].concat().to_vec()
        );
    }

    #[test]
    fn test_add_raw_with_failure_restores_trailer() {
        let mut buffer = [0u8; 1024];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();

        // Add some initial data so we have a non-empty config.
        assert_eq!(builder.add_item("foo", "bar"), Ok(()));
        let expected_config = "foo=bar\n";
        assert_eq!(extract_bootconfig(builder.config_bytes()).unwrap(), expected_config);

        // Call `add_raw_with()` which fails after clobbering the trailer.
        let res = builder.add_raw_with(|_, out| {
            out[..BOOTCONFIG_TRAILER_SIZE].fill(0xAA);
            Err(Error::OutOfResources)
        });
        assert_eq!(res, Err(Error::OutOfResources));

        // Verify that the trailer was restored and we can still extract the old config.
        assert_eq!(extract_bootconfig(builder.config_bytes()).unwrap(), expected_config);
    }

    fn add_lines(buffer: &mut [u8], chunk: &[u8]) -> Result<std::string::String> {
        let mut builder = BootConfigBuilder::new(buffer).unwrap();
        builder.add_raw_lines_with(|_, out| {
            out.get_mut(..chunk.len())
                .ok_or(Error::BufferTooSmall(Some(chunk.len())))?
                .clone_from_slice(chunk);
            Ok(chunk.len())
        })?;
        builder.add_item("androidboot.hardware", "cutf_cvm")?;
        Ok(extract_bootconfig(builder.config_bytes()).unwrap().into())
    }

    #[test]
    fn test_add_raw_lines_with_appends_missing_newline() {
        let mut buffer = [0u8; 1024];
        assert_eq!(
            add_lines(&mut buffer[..], b"androidboot.serialno=CUTTLEFISH").unwrap(),
            "androidboot.serialno=CUTTLEFISH\nandroidboot.hardware=cutf_cvm\n"
        );
    }

    #[test]
    fn test_add_raw_lines_with_terminated_lines_unchanged() {
        let mut buffer = [0u8; 1024];
        assert_eq!(
            add_lines(&mut buffer[..], b"androidboot.serialno=CUTTLEFISH\n").unwrap(),
            "androidboot.serialno=CUTTLEFISH\nandroidboot.hardware=cutf_cvm\n"
        );
    }

    #[test]
    fn test_add_raw_lines_with_empty_read_adds_nothing() {
        let mut buffer = [0u8; 1024];
        assert_eq!(add_lines(&mut buffer[..], b"").unwrap(), "androidboot.hardware=cutf_cvm\n");
    }

    #[test]
    fn test_add_raw_lines_with_reserves_newline_byte() {
        // The remaining capacity fits the chunk exactly, but one byte is reserved, so the reader
        // is offered one byte less and must report the shortage.
        let chunk = b"androidboot.serialno=CUTTLEFISH";
        let mut buffer = vec![0u8; chunk.len() + BOOTCONFIG_TRAILER_SIZE];
        assert_eq!(
            add_lines(&mut buffer[..], chunk),
            Err(Error::BufferTooSmall(Some(chunk.len())))
        );
    }

    #[test]
    fn test_add_incremental() {
        let mut buffer = [0u8; TEST_CONFIG.len() + TEST_CONFIG_TRAILER.len()];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();
        for ele in TEST_CONFIG.strip_suffix('\n').unwrap().split('\n') {
            write!(builder, "{}\n", ele).unwrap();
        }
        assert_eq!(
            builder.config_bytes().to_vec(),
            [TEST_CONFIG.as_bytes(), TEST_CONFIG_TRAILER].concat().to_vec()
        );
    }

    #[test]
    fn test_new_buffer_too_small() {
        let mut buffer = [0u8; BOOTCONFIG_TRAILER_SIZE - 1];
        assert!(BootConfigBuilder::new(&mut buffer[..]).is_err());
    }

    #[test]
    fn test_add_buffer_too_small() {
        let mut buffer = [0u8; BOOTCONFIG_TRAILER_SIZE + 1];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();
        assert!(write!(builder, "a\n").is_err());
    }

    #[test]
    fn test_add_empty_string() {
        let mut buffer = [0u8; BOOTCONFIG_TRAILER_SIZE + 1];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();
        write!(builder, "{}", "").unwrap();
    }

    #[test]
    fn test_add_with_error() {
        let mut buffer = [0u8; BOOTCONFIG_TRAILER_SIZE + 1];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();
        assert!(builder.add_raw_with(|_, _| Err(Error::Other(None))).is_err());
    }

    #[test]
    fn test_add_array() {
        let mut buffer = [0u8; 1024];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();
        builder.add_array("androidboot.dtbo_idx", [1, 2, 3]).unwrap();

        let expected_config = "androidboot.dtbo_idx=1,2,3\n";
        assert_eq!(extract_bootconfig(builder.config_bytes()).unwrap(), expected_config);
    }

    #[test]
    fn test_add_array_single() {
        let mut buffer = [0u8; 1024];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();
        builder.add_array("foo", ["bar"]).unwrap();

        let expected_config = "foo=bar\n";
        assert_eq!(extract_bootconfig(builder.config_bytes()).unwrap(), expected_config);
    }

    #[test]
    fn test_add_array_empty() {
        let mut buffer = [0u8; 1024];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();
        builder.add_array("foo", Vec::<u32>::new()).unwrap();

        // Empty array should not add anything.
        assert_eq!(extract_bootconfig(builder.config_bytes()).unwrap(), "");
    }

    #[test]
    fn test_add_item() {
        let mut buffer = [0u8; 1024];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();
        builder.add_item("foo", "bar").unwrap();
        builder.add_item("baz", 123).unwrap();

        assert_eq!(extract_bootconfig(builder.config_bytes()).unwrap(), "foo=bar\nbaz=123\n");
    }
    #[test]
    fn test_add_checked_item_success() {
        let mut buffer = [0u8; 1024];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();

        assert_eq!(builder.add_checked_item("foo=bar", |_| Ok(())), Ok(()));
        assert_eq!(extract_bootconfig(builder.config_bytes()).unwrap(), "foo=bar\n");
    }

    #[test]
    fn test_add_checked_item_failure() {
        let mut buffer = [0u8; 1024];
        let mut builder = BootConfigBuilder::new(&mut buffer[..]).unwrap();

        assert_eq!(
            builder.add_checked_item("foo=bar", |_| Err(Error::SecurityViolation)),
            Err(Error::SecurityViolation)
        );
        // Buffer should not have been modified.
        assert_eq!(extract_bootconfig(builder.config_bytes()).unwrap(), "");
    }
}
