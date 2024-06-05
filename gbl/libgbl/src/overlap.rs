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

//! Helper functions to verify image buffers
use core::cmp::{max, min};
extern crate itertools_noalloc;
use itertools_noalloc::Itertools;

/// Check if provided buffers overlap in any way.
///
/// Note that zero length buffer is considered to contain no elements.
/// And would not overlap with any other buffer.
///
/// # Args
///
/// * `buffers`: slice of buffers to verify
///
/// # Returns
///
/// * true: if any of the buffers have common elements
/// * false: if there are no common elements in buffers
pub fn is_overlap(buffers: &[&[u8]]) -> bool {
    // Compare each with each since we can't use alloc and sort buffers.
    // Since the number of buffers we expect is not big, O(n^2) complexity will do.
    //
    // Note: this is nice way to find out if 2 ranges overlap:
    // max(a_start, b_start) > min(a_end, b_end)) -> no overlap
    buffers
        .iter()
        .filter(|buffer| !buffer.is_empty())
        .map(|slice: &&[u8]| (slice.as_ptr(), slice.last_chunk::<1>().unwrap().as_ptr()))
        .tuple_combinations()
        .any(|((a_start, a_end), (b_start, b_end))| !(max(a_start, b_start) > min(a_end, b_end)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use itertools::Itertools;

    // Creates slice of specified range: [first; last)
    // Max range value is SIZE = 64;
    fn get_range(first: usize, last: usize) -> &'static [u8] {
        const SIZE: usize = 64;
        assert!(first < SIZE);
        assert!(last <= SIZE);
        static BUFFER: &'static [u8; SIZE] = &[0; SIZE];
        &BUFFER[first..last]
    }

    // Check if ranges overlap, testing all permutations
    fn check_overlap(ranges_set: &[(usize, usize)]) -> bool {
        ranges_set.iter().permutations(ranges_set.len()).all(|ranges| {
            let ranges_slices: Vec<&[u8]> =
                ranges.iter().map(|&(start, end)| get_range(*start, *end)).collect();
            is_overlap(&ranges_slices)
        })
    }

    // Check if ranges don't overlap, testing all permutations
    fn check_not_overlap(ranges_set: &[(usize, usize)]) -> bool {
        ranges_set.iter().permutations(ranges_set.len()).all(|ranges| {
            let ranges_slices: Vec<&[u8]> =
                ranges.iter().map(|&(start, end)| get_range(*start, *end)).collect();
            !is_overlap(&ranges_slices)
        })
    }

    #[test]
    fn test_is_overlap_false() {
        assert!(check_not_overlap(&[(10, 15), (20, 25), (30, 35)]));
    }

    #[test]
    fn test_is_overlap_true() {
        assert!(check_overlap(&[(10, 19), (15, 25)]));
    }

    #[test]
    fn test_is_overlap_included() {
        assert!(check_overlap(&[(10, 11), (10, 11)]));
        assert!(check_overlap(&[(10, 12), (10, 12)]));
        assert!(check_overlap(&[(10, 13), (11, 12)]));
        assert!(check_overlap(&[(10, 14), (11, 13)]));
        assert!(check_overlap(&[(10, 20), (15, 18)]));
        assert!(check_overlap(&[(10, 20), (11, 19), (12, 18), (13, 17)]));
    }

    #[test]
    fn test_is_overlap_touching() {
        assert!(check_not_overlap(&[(10, 20), (20, 30), (30, 31)]));
    }

    #[test]
    fn test_is_overlap_last_element() {
        assert!(check_overlap(&[(10, 20), (19, 21)]));
    }

    #[test]
    fn test_is_overlap_short() {
        assert!(check_not_overlap(&[(10, 11), (11, 12), (12, 13)]));
    }

    #[test]
    fn test_is_overlap_empty_slice() {
        assert!(check_not_overlap(&[]));
        assert!(check_not_overlap(&[(10, 10)]));
        assert!(check_not_overlap(&[(10, 20), (10, 10), (20, 30), (11, 11), (23, 23)]));
    }
}
