// Copyright (C) 2024 The Android Open Source Project
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

//! # safemath library
//!
//! This library provides an API to safely work with unsigned integers. At a high level, all math
//! operations are checked by default rather than having to remember to call specific `checked_*`
//! functions, so that the burden is on the programmer if they want to perform unchecked math
//! rather than the other way around:
//!
//! ```
//! use safemath::SafeNum;
//!
//! let safe = SafeNum::from(0);
//! let result = safe - 1;
//! assert!(u32::try_from(result).is_err());
//!
//! let safe_chain = (SafeNum::from(BIG_NUMBER) * HUGE_NUMBER) / MAYBE_ZERO;
//! // If any operation would have caused an overflow or division by zero,
//! // the number is flagged and the lexical location is specified for logging.
//! if safe_chain.has_error() {
//!     eprintln!("safe_chain error = {:#?}", safe_chain);
//! }
//! ```
//!
//! In addition to checked-by-default arithmetic, the API exposed here support
//! more natural usage than the `checked_*` functions by allowing chaining
//! of operations without having to check the result at each step.
//! This is similar to how floating-point `NaN` works - you can continue to use the
//! value, but continued operations will just propagate `NaN`.
//!
//! ## Supported Operations
//!
//! ### Arithmetic
//! The basic arithmetic operations are supported:
//! addition, subtraction, multiplication, division, and remainder.
//! The right hand side may be another SafeNum or any integer,
//! and the result is always another SafeNum.
//! If the operation would result in an overflow or division by zero,
//! or if converting the right hand element to a `u64` would cause an error,
//! the result is an error-tagged SafeNum that tracks the lexical origin of the error.
//!
//! ### Conversion from and to SafeNum
//! SafeNums support conversion to and from all integer types.
//! Conversion to SafeNum from signed integers and from usize and u128
//! can fail, generating an error value that is then propagated.
//! Conversion from SafeNum to all integers is only exposed via `try_from`
//! in order to force the user to handle potential resultant errors.
//!
//! E.g.
//! ```
//! fn call_func(_: u32, _: u32) {
//! }
//!
//! fn do_a_thing(a: SafeNum) -> Result<(), safemath::Error> {
//!     call_func(16, a.try_into()?);
//!     Ok(())
//! }
//! ```
//!
//! ### Comparison
//! SafeNums can be checked for equality against each other.
//! Valid numbers are equal to other numbers of the same magnitude.
//! Errored SafeNums are only equal to themselves.
//! Note that because errors propagate from their first introduction in an
//! arithmetic chain this can lead to surprising results.
//!
//! E.g.
//! ```
//! let overflow = SafeNum::MAX + 1;
//! let otherflow = SafeNum::MAX + 1;
//!
//! assert_ne!(overflow, otherflow);
//! assert_eq!(overflow + otherflow, overflow);
//! assert_eq!(otherflow + overflow, otherflow);
//! ```
//!
//! Inequality comparison operators are deliberately not provided.
//! By necessity they would have similar caveats to floating point comparisons,
//! which are easy to use incorrectly and unintuitive to use correctly.
//!
//! The required alternative is to convert to a real integer type before comparing,
//! forcing any errors upwards.
//!
//! E.g.
//! ```
//! impl From<safemath::Error> for &'static str {
//!     fn from(_: safemath::Error) -> Self {
//!         "checked arithmetic error"
//!     }
//! }
//!
//! fn my_op(a: SafeNum, b: SafeNum, c: SafeNum, d: SafeNum) -> Result<bool, &'static str> {
//!     Ok(safemath::Primitive::try_from(a)? < b.try_into()?
//!        && safemath::Primitive::try_from(c)? >= d.try_into()?)
//! }
//! ```
//!
//! ### Miscellaneous
//! SafeNums also provide helper methods to round up or down
//! to the nearest multiple of another number
//! and helper predicate methods that indicate whether the SafeNum
//! is valid or is tracking an error.
//!
//! Also provided are constants `SafeNum::MAX`, `SafeNum::MIN`, and `SafeNum::ZERO`.
//!
//! Warning: SafeNums can help prevent, isolate, and detect arithmetic overflow
//!          but they are not a panacea. In particular, chains of different operations
//!          are not guaranteed to be associative or commutative.
//!
//! E.g.
//! ```
//! let a = SafeNum::MAX - 1 + 1;
//! let b = SafeNum::MAX + 1 - 1;
//! assert_ne!(a, b);
//! assert!(a.is_valid());
//! assert!(b.has_error());
//!
//! let c = (SafeNum::MAX + 31) / 31;
//! let d = SafeNum::MAX / 31 + 31 / 31;
//! assert_ne!(c, d);
//! assert!(c.has_error());
//! assert!(d.is_valid());
//! ```
//!
//! Note:    SafeNum arithmetic is much slower than arithmetic on integer primitives.
//!          If you are concerned about performance, be sure to run benchmarks.

#![cfg_attr(not(test), no_std)]

use core::convert::TryFrom;
use core::fmt;
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, RemAssign, Sub, SubAssign};
use core::panic::Location;

/// The underlying primitive type used for [SafeNum] operations.
pub type Primitive = u64;
/// Safe math error type, which points to the location of the original failed operation.
pub type Error = &'static Location<'static>;

/// Wraps a raw [Primitive] type for safe-by-default math. See module docs for info and usage.
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct SafeNum(Result<Primitive, Error>);

impl fmt::Debug for SafeNum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Ok(val) => write!(f, "{}", val),
            Err(location) => write!(f, "error at {}", location),
        }
    }
}

impl SafeNum {
    /// The maximum [SafeNum].
    pub const MAX: SafeNum = SafeNum(Ok(u64::MAX));
    /// The minimum [SafeNum].
    pub const MIN: SafeNum = SafeNum(Ok(u64::MIN));
    /// Zero as a [SafeNum].
    pub const ZERO: SafeNum = SafeNum(Ok(0));

    /// Round `self` down to the nearest multiple of `rhs`.
    #[track_caller]
    pub fn round_down<T>(self, rhs: T) -> Self
    where
        Self: Rem<T, Output = Self>,
    {
        self - (self % rhs)
    }

    /// Round `self` up to the nearest multiple of `rhs`.
    #[track_caller]
    pub fn round_up<T>(self, rhs: T) -> Self
    where
        Self: Add<T, Output = Self>,
        T: Copy + Into<Self>,
    {
        ((self + rhs) - 1).round_down(rhs)
    }

    /// Returns whether self is the result of an operation that has errored.
    pub const fn has_error(&self) -> bool {
        self.0.is_err()
    }

    /// Returns whether self represents a valid, non-overflowed integer.
    pub const fn is_valid(&self) -> bool {
        self.0.is_ok()
    }
}

macro_rules! try_conversion_func {
    ($other_type:tt) => {
        impl TryFrom<SafeNum> for $other_type {
            type Error = Error;

            #[track_caller]
            fn try_from(val: SafeNum) -> Result<Self, Self::Error> {
                Self::try_from(val.0?).map_err(|_| Location::caller())
            }
        }
    };
}

macro_rules! conversion_func {
    ($from_type:tt) => {
        impl From<$from_type> for SafeNum {
            fn from(val: $from_type) -> SafeNum {
                Self(Ok(val.into()))
            }
        }

        try_conversion_func!($from_type);
    };
}

macro_rules! conversion_func_maybe_error {
    ($from_type:tt) => {
        impl From<$from_type> for SafeNum {
            #[track_caller]
            fn from(val: $from_type) -> Self {
                Self(Primitive::try_from(val).map_err(|_| Location::caller()))
            }
        }

        try_conversion_func!($from_type);
    };
}

macro_rules! arithmetic_impl {
    ($trait_name:ident, $op:ident, $assign_trait_name:ident, $assign_op:ident, $func:ident) => {
        impl<T: Into<SafeNum>> $trait_name<T> for SafeNum {
            type Output = Self;
            #[track_caller]
            fn $op(self, rhs: T) -> Self {
                let rhs: Self = rhs.into();

                match (self.0, rhs.0) {
                    (Err(_), _) => self,
                    (_, Err(_)) => rhs,
                    (Ok(lhs), Ok(rhs)) => Self(lhs.$func(rhs).ok_or_else(Location::caller)),
                }
            }
        }

        impl<T> $assign_trait_name<T> for SafeNum
        where
            Self: $trait_name<T, Output = Self>,
        {
            #[track_caller]
            fn $assign_op(&mut self, rhs: T) {
                *self = self.$op(rhs)
            }
        }
    };
}

conversion_func!(u8);
conversion_func!(u16);
conversion_func!(u32);
conversion_func!(u64);
conversion_func_maybe_error!(usize);
conversion_func_maybe_error!(u128);
conversion_func_maybe_error!(i8);
conversion_func_maybe_error!(i16);
conversion_func_maybe_error!(i32);
conversion_func_maybe_error!(i64);
conversion_func_maybe_error!(i128);
conversion_func_maybe_error!(isize);
arithmetic_impl!(Add, add, AddAssign, add_assign, checked_add);
arithmetic_impl!(Sub, sub, SubAssign, sub_assign, checked_sub);
arithmetic_impl!(Mul, mul, MulAssign, mul_assign, checked_mul);
arithmetic_impl!(Div, div, DivAssign, div_assign, checked_div);
arithmetic_impl!(Rem, rem, RemAssign, rem_assign, checked_rem);

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_addition() {
        let a: SafeNum = 2100.into();
        let b: SafeNum = 12.into();
        assert_eq!(a + b, 2112.into());
    }

    #[test]
    fn test_subtraction() {
        let a: SafeNum = 667.into();
        let b: SafeNum = 1.into();
        assert_eq!(a - b, 666.into());
    }

    #[test]
    fn test_multiplication() {
        let a: SafeNum = 17.into();
        let b: SafeNum = 3.into();
        assert_eq!(a * b, 51.into());
    }

    #[test]
    fn test_division() {
        let a: SafeNum = 1066.into();
        let b: SafeNum = 41.into();
        assert_eq!(a / b, 26.into());
    }

    #[test]
    fn test_remainder() {
        let a: SafeNum = 613.into();
        let b: SafeNum = 10.into();
        assert_eq!(a % b, 3.into());
    }

    #[test]
    fn test_addition_poison() {
        let base: SafeNum = 2.into();
        let poison = base + SafeNum::MAX;
        assert!(u64::try_from(poison).is_err());

        let a = poison - 1;
        let b = poison - 2;

        assert_eq!(a, poison);
        assert_eq!(b, poison);
    }

    #[test]
    fn test_subtraction_poison() {
        let base: SafeNum = 2.into();
        let poison = base - SafeNum::MAX;
        assert!(u64::try_from(poison).is_err());

        let a = poison + 1;
        let b = poison + 2;

        assert_eq!(a, poison);
        assert_eq!(b, poison);
    }

    #[test]
    fn test_multiplication_poison() {
        let base: SafeNum = 2.into();
        let poison = base * SafeNum::MAX;
        assert!(u64::try_from(poison).is_err());

        let a = poison / 2;
        let b = poison / 4;

        assert_eq!(a, poison);
        assert_eq!(b, poison);
    }

    #[test]
    fn test_division_poison() {
        let base: SafeNum = 2.into();
        let poison = base / 0;
        assert!(u64::try_from(poison).is_err());

        let a = poison * 2;
        let b = poison * 4;

        assert_eq!(a, poison);
        assert_eq!(b, poison);
    }

    #[test]
    fn test_remainder_poison() {
        let base: SafeNum = 2.into();
        let poison = base % 0;
        assert!(u64::try_from(poison).is_err());

        let a = poison * 2;
        let b = poison * 4;

        assert_eq!(a, poison);
        assert_eq!(b, poison);
    }

    macro_rules! conversion_test {
        ($name:ident) => {
            mod $name {
                use super::*;
                use core::convert::TryInto;

                #[test]
                fn test_between_safenum() {
                    let var: $name = 16;
                    let sn: SafeNum = var.into();
                    let res: $name = sn.try_into().unwrap();
                    assert_eq!(var, res);
                }

                #[test]
                fn test_arithmetic_safenum() {
                    let primitive: $name = ((((0 + 11) * 11) / 3) % 32) - 3;
                    let safe = ((((SafeNum::ZERO + $name::try_from(11u8).unwrap())
                        * $name::try_from(11u8).unwrap())
                        / $name::try_from(3u8).unwrap())
                        % $name::try_from(32u8).unwrap())
                        - $name::try_from(3u8).unwrap();
                    assert_eq!($name::try_from(safe).unwrap(), primitive);
                }
            }
        };
    }

    conversion_test!(u8);
    conversion_test!(u16);
    conversion_test!(u32);
    conversion_test!(u64);
    conversion_test!(u128);
    conversion_test!(usize);
    conversion_test!(i8);
    conversion_test!(i16);
    conversion_test!(i32);
    conversion_test!(i64);
    conversion_test!(i128);
    conversion_test!(isize);

    macro_rules! correctness_tests {
        ($name:ident, $operation:ident, $assign_operation:ident) => {
            mod $operation {
                use super::*;
                use core::ops::$name;

                #[test]
                fn test_correctness() {
                    let normal = 300u64;
                    let safe: SafeNum = normal.into();
                    let rhs = 7u64;
                    assert_eq!(
                        u64::try_from(safe.$operation(rhs)).unwrap(),
                        normal.$operation(rhs)
                    );
                }

                #[test]
                fn test_assign() {
                    let mut var: SafeNum = 2112.into();
                    let rhs = 666u64;
                    let expect = var.$operation(rhs);
                    var.$assign_operation(rhs);
                    assert_eq!(var, expect);
                }

                #[test]
                fn test_assign_poison() {
                    let mut var = SafeNum::MIN - 1;
                    let expected = var - 1;
                    var.$assign_operation(2);
                    // Poison saturates and doesn't perform additional changes
                    assert_eq!(var, expected);
                }
            }
        };
    }

    correctness_tests!(Add, add, add_assign);
    correctness_tests!(Sub, sub, sub_assign);
    correctness_tests!(Mul, mul, mul_assign);
    correctness_tests!(Div, div, div_assign);
    correctness_tests!(Rem, rem, rem_assign);

    #[test]
    fn test_round_down() {
        let x: SafeNum = 255.into();
        assert_eq!(x.round_down(32), 224.into());
        assert_eq!((x + 1).round_down(64), 256.into());
        assert_eq!(x.round_down(256), SafeNum::ZERO);
        assert!(x.round_down(SafeNum::MIN).has_error());
    }

    #[test]
    fn test_round_up() {
        let x: SafeNum = 255.into();
        assert_eq!(x.round_up(32), 256.into());
        assert_eq!(x.round_up(51), x);
        assert_eq!(SafeNum::ZERO.round_up(x), SafeNum::ZERO);
        assert!(SafeNum::MAX.round_up(32).has_error());
    }
}
