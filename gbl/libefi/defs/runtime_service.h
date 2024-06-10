#ifndef __RUNTIME_SERVICE_H__
#define __RUNTIME_SERVICE_H__

#include "types.h"

typedef struct {
  EfiTableHeader hdr;
  EfiStatus (*get_time)(EfiTime* time, EfiTimeCapabilities* capabilities);
  EfiStatus (*set_time)(EfiTime* time);
  EfiStatus (*get_wakeup_time)(bool* enabled, bool* pending, EfiTime* time);
  EfiStatus (*set_wakeup_time)(bool enable, EfiTime* time);
  EfiStatus (*set_virtual_address_map)(size_t memory_map_size,
                                       size_t descriptor_size,
                                       uint32_t descriptor_version,
                                       EfiMemoryDescriptor* virtual_map);
  EfiStatus (*convert_pointer)(size_t debug_disposition, void** address);
  EfiStatus (*get_variable)(const char16_t* variable_name,
                            const EfiGuid* vendor_guid, uint32_t* attributes,
                            size_t* data_size, void* data);
  EfiStatus (*get_next_variable_name)(size_t* variable_name_size,
                                      char16_t* variable_name,
                                      EfiGuid* vendor_guid);
  EfiStatus (*set_variable)(const char16_t* variable_name,
                            const EfiGuid* vendor_guid, uint32_t attributes,
                            size_t data_size, void* data);
  EfiStatus (*get_next_high_monotonic_count)(uint32_t* high_count);
  void (*reset_system)(EfiResetType reset_type, EfiStatus reset_status,
                       size_t data_size, void* reset_data);
  EfiStatus (*update_capsule)(EfiCapsuleHeader** capsule_header_array,
                              size_t capsule_count,
                              EfiPhysicalAddr scatter_gather_list);
  EfiStatus (*query_capsule_capabilities)(
      EfiCapsuleHeader** capsule_header_array, size_t capsule_count,
      uint64_t* maximum_capsule_size, EfiResetType* reset_type);
  EfiStatus (*query_variable_info)(uint32_t attributes,
                                   uint64_t* maximum_variable_storage_size,
                                   uint64_t* remaining_variable_storage_size,
                                   uint64_t* maximum_variable_size);
} EfiRuntimeService;

#endif  // __RUNTIME_SERVICE_H__