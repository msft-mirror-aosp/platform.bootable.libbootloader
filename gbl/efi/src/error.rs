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

use liberror::Error;
use smoltcp::socket::tcp::{ListenError, RecvError, SendError};

pub fn recv_to_unified(err: RecvError) -> Error {
    match err {
        RecvError::InvalidState => Error::InvalidState,
        RecvError::Finished => Error::Finished,
    }
}

pub fn send_to_unified(err: SendError) -> Error {
    match err {
        SendError::InvalidState => Error::InvalidState,
    }
}

pub fn listen_to_unified(err: ListenError) -> Error {
    match err {
        ListenError::InvalidState => Error::InvalidState,
        ListenError::Unaddressable => Error::Unaddressable,
    }
}
