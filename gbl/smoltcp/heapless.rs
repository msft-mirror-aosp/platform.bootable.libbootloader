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

//! Selective implementation of APIs from crate `heapless` 0.8.0 using alloc.
//! https://docs.rs/heapless/0.8.0/heapless/index.html
//!
//! The smoltcp crate depends on crate heapless. At the time this is written, the crate is either
//! still in the process of being imported to Android or abandoned. Since we only use them in the
//! EFI build which has alloc, we use a naive implementation of the needed APIs using heap
//! allocation as a workaround for now.

#![no_std]
#![no_main]

use core::ops::{Deref, DerefMut};

extern crate alloc;
use alloc::collections::BTreeMap;
use alloc::vec::Vec as AllocVec;

/// `heapless::Vec`
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Vec<T, const N: usize>(AllocVec<T>);

impl<T, const N: usize> Vec<T, N> {
    pub fn new() -> Self {
        Self(AllocVec::new())
    }

    pub fn capacity(&self) -> usize {
        N
    }

    pub fn push(&mut self, item: T) -> Result<(), T> {
        match self.0.len() < N {
            true => {
                self.0.push(item);
                Ok(())
            }
            _ => Err(item),
        }
    }
}

impl<T, const N: usize> Deref for Vec<T, N> {
    type Target = AllocVec<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T, const N: usize> DerefMut for Vec<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a Vec<T, N> {
    type Item = &'a T;
    type IntoIter = core::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

/// `heapless::LinearMap`
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct LinearMap<K, V, const N: usize>(BTreeMap<K, V>);

impl<K: core::cmp::Ord, V, const N: usize> LinearMap<K, V, N> {
    pub fn new() -> Self {
        Self(BTreeMap::new())
    }

    pub fn capacity(&self) -> usize {
        N
    }

    pub fn insert(&mut self, key: K, value: V) -> Result<Option<V>, (K, V)> {
        match self.0.len() < N {
            true => Ok(self.0.insert(key, value)),
            _ => Err((key, value)),
        }
    }
}

impl<K, V, const N: usize> Deref for LinearMap<K, V, N> {
    type Target = BTreeMap<K, V>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<K, V, const N: usize> DerefMut for LinearMap<K, V, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
