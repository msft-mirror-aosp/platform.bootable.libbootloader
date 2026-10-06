/*
 * Copyright (C) 2026 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#ifdef __GBL_LIBC_STUBS__

int errno = 0;

extern void* bsearch_rust(const void* key, const void* base, size_t nmemb,
                          size_t size, int (*compar)(const void*, const void*));

void* bsearch(const void* key, const void* base, size_t nmemb, size_t size,
              int (*compar)(const void*, const void*)) {
  return bsearch_rust(key, base, nmemb, size, compar);
}

extern void* gbl_malloc(size_t request_size, size_t alignment);
extern void gbl_free(void* ptr, size_t alignment);
extern void* gbl_realloc(void* ptr, size_t new_size, size_t alignment);

void* malloc(size_t size) { return gbl_malloc(size, 8); }
void free(void* ptr) { gbl_free(ptr, 8); }

void* realloc(void* ptr, size_t size) { return gbl_realloc(ptr, size, 8); }

char* getenv(const char* name) { return NULL; }

extern void gbl_panic_from_c(const char* msg);

static void* RtlVirtualUnwind_stub(void* HandlerType, void* ImageBase,
                                   void* ControlPc, void* FunctionEntry,
                                   void* ContextRecord, void** HandlerData,
                                   void* EstablisherFrame,
                                   void* ContextPointers) {
  gbl_panic_from_c("Unexpected call to RtlVirtualUnwind in baremetal assembly");
  return NULL;
}

void* __imp_RtlVirtualUnwind = (void*)&RtlVirtualUnwind_stub;

#endif  // __GBL_LIBC_STUBS__
