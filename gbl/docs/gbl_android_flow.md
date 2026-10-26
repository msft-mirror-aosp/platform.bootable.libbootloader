# GBL Android Boot Flow

GBL boots Android in the following stages.

1. **Partition Discovery**: GBL scans block devices and syncs their GPT
   partition tables.
2. **Boot Mode & Slot Selection**: GBL reads the bootloader control
   block (BCB) in the `misc` partition and the platform one-shot boot mode
   (`GBL_EFI_BOOT_CONTROL_PROTOCOL`) to decide whether to enter Fastboot,
   Recovery, or Normal boot, and gets the current A/B slot from
   `GBL_EFI_BOOT_CONTROL_PROTOCOL`.
3. **Load & Verify**:
   - Loads `boot`, `init_boot`, `vendor_boot`, `vendor_kernel_boot`, `dtb`,
     `dtbo`, `pvmfw` (when AVF is supported), and any platform-specific
     partitions requested via `GBL_EFI_AVB_PROTOCOL` into firmware-designated
     buffers (`GBL_EFI_BOOT_MEMORY_PROTOCOL`).
   - Verifies loaded partitions via Android Verified Boot (`libavb` and
     `GBL_EFI_AVB_PROTOCOL`), enforcing lock state and rollback index updates.
   - Selects device tree components via `GBL_EFI_OS_CONFIGURATION_PROTOCOL`,
     applies the selected overlays, and applies final FDT fixups via
     `EFI_DT_FIXUP_PROTOCOL`.
   - Assembles kernel command line and `bootconfig` parameters (including AVB,
     slot, and AVF parameters) and applies platform fixups via
     `GBL_EFI_OS_CONFIGURATION_PROTOCOL`.
   - When AVF is enabled, builds the `pvmfw` configuration (a DICE handover
     derived from the vendor DICE handover and a VM reference device tree
     containing the Secretkeeper public key) via `GBL_EFI_AVF_PROTOCOL`.
4. **Kernel Handoff**: GBL calls
   `GBL_EFI_BOOT_CONTROL_PROTOCOL.HandleLoadedOs()` when implemented, then exits
   UEFI Boot Services and jumps to the kernel entry point.
