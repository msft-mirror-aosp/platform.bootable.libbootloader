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
 * LLVM mangles the "void __chkstk()" function from rust libcompiler_builtins
 * with an additional underscore, making it "___chkstk" and causing the linker
 * to fail finding "__chkstk". We workaround by defining the magled symbol that
 * simply jumps to the correct target.
 */

.global __chkstk

__chkstk:
    jmp ___chkstk
