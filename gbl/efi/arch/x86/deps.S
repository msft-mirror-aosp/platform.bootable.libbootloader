/*
 * Copyright (C) 2024 The Android Open Source Project
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

/*
 * LLVM mangles the "___chkstk()" and "__alloca()" function from rust
 * libcompiler_builtins with an additional underscore, making them "___chkstk"
 * and "___alloca and causing the linker to fail finding them. We workaround by
 * defining the magled symbols that simply jump to the correct target.
 */

.global ___chkstk
.global __alloca

___chkstk:
    jmp ____chkstk

__alloca:
    jmp ___alloca
