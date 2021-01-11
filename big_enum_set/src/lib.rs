#![no_std]
#![forbid(missing_docs)]

//! A library for creating enum sets that are stored as compact bit sets. The code is
//! based on the [`enumset`](http:://docs.rs/enumset) crate, except that the backing
//! store used is an array of `usize`. This enables use with enums with large number
//! of variants. The API is very similar to that of `enumset`.
//!
//! For serde support, enable the `serde` feature.
//!
//! # Defining enums for use with `BigEnumSet`
//!
//! Enums to be used with [`BigEnumSet`] should be defined using `#[derive(BigEnumSetType)]`:
//!
//! ```rust
//! # use big_enum_set::*;
//! #[derive(BigEnumSetType, Debug)]
//! pub enum Enum {
//!    A, B, C, D, E, F, G,
//! }
//! ```
//!
//! For more information on more advanced use cases, see the documentation for [`BigEnumSetType`].
//!
//! # Working with `BigEnumSet`s
//!
//! BigEnumSets can be constructed via [`BigEnumSet::new()`] like a normal set. In addition,
//! `#[derive(BigEnumSetType)]` creates operator overloads that allow you to create BigEnumSets like so:
//!
//! ```rust
//! # use big_enum_set::*;
//! # #[derive(BigEnumSetType, Debug)] pub enum Enum { A, B, C, D, E, F, G }
//! let new_set = Enum::A | Enum::C | Enum::G;
//! assert_eq!(new_set.len(), 3);
//! ```
//!
//! All bitwise operations you would expect to work on bitsets also work on both BigEnumSets and
//! enums with `#[derive(BigEnumSetType)]`:
//! ```rust
//! # use big_enum_set::*;
//! # #[derive(BigEnumSetType, Debug)] pub enum Enum { A, B, C, D, E, F, G }
//! // Intersection of sets
//! assert_eq!((Enum::A | Enum::B) & Enum::C, BigEnumSet::empty());
//! assert_eq!((Enum::A | Enum::B) & Enum::A, Enum::A);
//! assert_eq!(Enum::A & Enum::B, BigEnumSet::empty());
//!
//! // Symmetric difference of sets
//! assert_eq!((Enum::A | Enum::B) ^ (Enum::B | Enum::C), Enum::A | Enum::C);
//! assert_eq!(Enum::A ^ Enum::C, Enum::A | Enum::C);
//!
//! // Difference of sets
//! assert_eq!((Enum::A | Enum::B | Enum::C) - Enum::B, Enum::A | Enum::C);
//!
//! // Complement of sets
//! assert_eq!(!(Enum::E | Enum::G), Enum::A | Enum::B | Enum::C | Enum::D | Enum::F);
//! ```
//!
//! The [`big_enum_set!`] macro allows you to create BigEnumSets in constant contexts:
//!
//! ```rust
//! # use big_enum_set::*;
//! # #[derive(BigEnumSetType, Debug)] pub enum Enum { A, B, C, D, E, F, G }
//! const CONST_SET: BigEnumSet<Enum> = big_enum_set!(Enum::A | Enum::B);
//! assert_eq!(CONST_SET, Enum::A | Enum::B);
//! ```
//!
//! Mutable operations on the [`BigEnumSet`] work similarly to Rust's builtin sets:
//!
//! ```rust
//! # use big_enum_set::*;
//! # #[derive(BigEnumSetType, Debug)] pub enum Enum { A, B, C, D, E, F, G }
//! let mut set = BigEnumSet::new();
//! set.insert(Enum::A);
//! set.insert_all(Enum::E | Enum::G);
//! assert!(set.contains(Enum::A));
//! assert!(!set.contains(Enum::B));
//! assert_eq!(set, Enum::A | Enum::E | Enum::G);
//! ```

pub use big_enum_set_derive::*;

use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt::{self, Debug};
use core::hash::{Hash, Hasher};
use core::iter::FromIterator;
use core::marker::PhantomData;
use core::mem;
use core::ops::*;

/// Everything in this module is internal API and may change at any time.
#[doc(hidden)]
pub mod __internal;

use __internal::{WORD_BITS, WORD_MASK, WORD_SHIFT};

#[cfg(feature = "serde")]
use crate::__internal::serde;

/// The trait used to define enum types that may be used with [`BigEnumSet`].
///
/// This trait should be implemented using `#[derive(BigEnumSetType)]`. Its internal structure is
/// not stable, and may change at any time.
///
/// # Custom Derive
///
/// Any C-like enum is supported, as long as there are no more than 65536 variants in the enum,
/// and no variant discriminant is larger than 65535.
///
/// The custom derive for [`BigEnumSetType`] automatically creates implementations of
/// [`Sub`], [`BitAnd`], [`BitOr`], [`BitXor`], and [`Not`] allowing the enum to be used as
/// if it were an [`BigEnumSet`] in expressions. This can be disabled by adding an `#[big_enum_set(no_ops)]`
/// attribute to the enum.
///
/// The custom derive for `BigEnumSetType` automatically implements [`Copy`], [`Clone`], [`Eq`], and
/// [`PartialEq`] on the enum. These are required for the [`BigEnumSet`] to function.
///
/// Attributes controlling the serialization of `BigEnumSet` are documented in
/// [its documentation](./struct.BigEnumSet.html#serialization).
///
/// # Examples
///
/// Deriving a plain BigEnumSetType:
///
/// ```rust
/// # use big_enum_set::*;
/// #[derive(BigEnumSetType)]
/// pub enum Enum {
///    A, B, C, D, E, F, G,
/// }
/// ```
///
/// Deriving a sparse BigEnumSetType:
///
/// ```rust
/// # use big_enum_set::*;
/// #[derive(BigEnumSetType)]
/// pub enum SparseEnum {
///    A = 10, B = 20, C = 30, D = 127,
/// }
/// ```
///
/// Deriving an BigEnumSetType without adding ops:
///
/// ```rust
/// # use big_enum_set::*;
/// #[derive(BigEnumSetType)]
/// #[big_enum_set(no_ops)]
/// pub enum NoOpsEnum {
///    A, B, C, D, E, F, G,
/// }
/// ```
pub unsafe trait BigEnumSetType: Copy + Eq + crate::__internal::BigEnumSetTypePrivate {}

/// An efficient set type for enums.
///
/// It is implemented using a bitset stored as `[usize; N]`, where N is the smallest number that
/// such that the array can fit all the bits of the underlying enum. An enum with discriminant `n`
/// is stored in the `n / WORD_SIZE` word at the `n % WORD_SIZE` least significant bit (corresponding
/// with as bit mask of `1 << (n % WORD_SIZE)`. `WORD_SIZE` is `mem::size_of::<usize>()`.
///
/// # Serialization
///
/// When the `serde` feature is enabled, [`BigEnumSet`]s can be serialized and deserialized using
/// the [`serde`](http://docs.rs/serde) crate. The exact serialization format can be controlled
/// with additional attributes on the enum type. These attributes are valid regardless of
/// whether the `serde` feature is enabled.
///
/// By default [`BigEnumSet`]s are serialized as `[u8; N]`, where N is smallest such that the array
/// can fit all bits that are part of the underlying enum. An enum with discriminant `n` is serialized
/// as `n % 8`th least significant bit in the `n / 8` byte. You can add a
/// `#[big_enum_set(serialize_bytes = N)]` attribute to your enum to control the number of bytes
/// in the serialization. This can be important for avoiding unintentional breaking changes when
/// `BigEnumSet`s are serialized with formats like [`bincode`](https:://docs.rs/bincode).
///
/// By default, unknown bits are ignored and silently removed from the bitset. To override this
/// behavior, you can add a `#[big_enum_set(serialize_deny_unknown)]` attribute. This will cause
/// deserialization to fail if an invalid bit is set.
///
/// In addition, the `#[big_enum_set(serialize_as_list)]` attribute causes the [`BigEnumSet`] to be
/// instead serialized as a list of enum variants. This requires your enum type implement
/// `Serialize` and `Deserialize`. Note that this is a breaking change.
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct BigEnumSet<T: BigEnumSetType> {
    #[doc(hidden)]
    /// This is public due to the [`big_enum_set!`] macro.
    /// This is **NOT** public API and may change at any time.
    pub __repr: T::Repr,
}

impl<T: BigEnumSetType> BigEnumSet<T> {
    fn has_bit(&self, bit: u16) -> bool {
        let word_idx = bit >> WORD_SHIFT;
        let bit_idx = bit & WORD_MASK;
        let mask = 1usize << bit_idx;
        self.__repr.as_ref()[usize::from(word_idx)] & mask == mask
    }
    fn set_bit(&mut self, bit: u16, val: bool) -> bool {
        let word_idx = bit >> WORD_SHIFT;
        let bit_idx = bit & WORD_MASK;
        let mask = 1usize << bit_idx;
        let word = &mut self.__repr.as_mut()[usize::from(word_idx)];
        let old = *word & mask != 0;
        if val {
            *word |= mask;
        } else {
            *word &= !mask;
        }
        old
    }

    /// Empty set.
    pub const EMPTY: BigEnumSet<T> = BigEnumSet { __repr: T::REPR_NONE };

    /// Creates an empty `BigEnumSet`.
    pub fn new() -> Self {
        Self::EMPTY
    }

    /// Returns a `BigEnumSet` containing a single element.
    pub fn only(t: T) -> Self {
        let mut set = Self::EMPTY;
        set.set_bit(t.enum_into_u16(), true);
        set
    }

    /// Creates an empty `BigEnumSet`.
    ///
    /// This is an alias for [`BigEnumSet::new`].
    pub fn empty() -> Self {
        Self::EMPTY
    }

    /// Returns a `BigEnumSet` containing all valid variants of the enum.
    pub fn all() -> Self {
        Self { __repr: T::REPR_ALL }
    }

    /// Total number of bits used by this type. Note that the actual amount of space used is
    /// rounded up to the next highest `usize`.
    ///
    /// This is the same as [`BigEnumSet::variant_count`] except in enums with "sparse" variants.
    /// (e.g. `enum Foo { A = 10, B = 20 }`)
    pub fn bit_width() -> u32 {
        let len = T::REPR_LEN;
        len as u32 * u32::from(WORD_BITS) - T::REPR_ALL.as_ref()[len - 1].leading_zeros()
    }

    /// The number of valid variants this type may contain.
    ///
    /// This is the same as [`BigEnumSet::bit_width`] except in enums with "sparse" variants.
    /// (e.g. `enum Foo { A = 10, B = 20 }`)
    pub fn variant_count() -> u32 {
        T::REPR_ALL.as_ref().iter().map(|w| w.count_ones()).sum()
    }

    /// Returns the raw bits of this set.
    pub fn as_bits(&self) -> &[usize] {
        self.__repr.as_ref()
    }

    /// Constructs a `BigEnumSet` from raw bits.
    ///
    /// Returns `None` if there are any invalid bits set in `bits`.
    /// The size of `bits` need not match the underlying representation.
    pub fn try_from_bits(bits: &[usize]) -> Option<Self> {
        let mut bits_valid = bits.iter()
            .zip(T::REPR_ALL.as_ref().iter())
            .all(|(w, all)| *w & !*all == 0);

        if bits.len() > T::REPR_LEN {
            bits_valid &= bits[T::REPR_LEN ..].iter().all(|w| *w == 0);
        }
        if !bits_valid {
            return None;
        }

        let mut set = Self::new();
        set.__repr.as_mut().iter_mut()
            .zip(bits.iter())
            .for_each(|(dst, src)| *dst = *src);
        Some(set)
    }

    /// Constructs a `BigEnumSet` from raw bits, ignoring any unknown variants.
    ///
    /// The size of `bits` need not match the underlying representation.
    pub fn from_bits_truncated(bits: &[usize]) -> Self {
        let all_set = T::REPR_ALL;
        let masked_bits = bits.iter()
            .zip(all_set.as_ref().iter())
            .map(|(w, all)| *w & *all);
        let mut set = Self::new();
        set.__repr.as_mut().iter_mut()
            .zip(masked_bits)
            .for_each(|(dst, src)| *dst = src);
        set
    }

    /// Returns the number of elements in this set.
    pub fn len(&self) -> usize {
        self.__repr.as_ref().iter().map(|w| w.count_ones() as usize).sum()
    }
    /// Returns `true` if the set contains no elements.
    pub fn is_empty(&self) -> bool {
        self.__repr == T::REPR_NONE
    }
    /// Removes all elements from the set.
    pub fn clear(&mut self) {
        self.__repr = T::REPR_NONE
    }

    fn check_all<F>(&self, other: &Self, f: F) -> bool
    where F: Fn(usize, usize) -> bool {
        self.__repr.as_ref().iter()
            .zip(other.__repr.as_ref().iter())
            .all(|(w1, w2)| f(*w1, *w2))
    }
    /// Returns `true` if `self` has no elements in common with `other`. This is equivalent to
    /// checking for an empty intersection.
    pub fn is_disjoint<O: Borrow<Self>>(&self, other: O) -> bool {
        self.check_all(other.borrow(), |w1, w2| w1 & w2 == 0)
    }
    /// Returns `true` if `self` is a superset of `other`, i.e., `self` contains at least all the
    /// elements in `other`.
    pub fn is_superset<O: Borrow<Self>>(&self, other: O) -> bool {
        self.check_all(other.borrow(), |w1, w2| w1 & w2 == w2)
    }
    /// Returns `true` if `self` is a subset of `other`, i.e., `other` contains at least all
    /// the elements in `self`.
    pub fn is_subset<O: Borrow<Self>>(&self, other: O) -> bool {
        other.borrow().is_superset(self)
    }

    fn apply_op<F>(&mut self, other: &Self, op: F)
    where F: Fn(usize, usize) -> usize {
        self.__repr.as_mut().iter_mut()
            .zip(other.__repr.as_ref().iter())
            .for_each(|(w1, w2)| *w1 = op(*w1, *w2));
    }
    /// Returns a set containing all elements present in either set.
    pub fn union<O: Borrow<Self>>(&self, other: O) -> Self {
        let mut result = self.clone();
        __internal::union(&mut result, other.borrow());
        result
    }
    /// Returns a set containing all elements present in both sets.
    pub fn intersection<O: Borrow<Self>>(&self, other: O) -> Self {
        let mut result = self.clone();
        __internal::intersection(&mut result, other.borrow());
        result
    }
    /// Returns a set containing all elements present in `self` but not in `other`.
    pub fn difference<O: Borrow<Self>>(&self, other: O) -> Self {
        let mut result = self.clone();
        __internal::difference(&mut result, other.borrow());
        result
    }
    /// Returns a set containing all elements present in either `self` or `other`, but is not present
    /// in both.
    pub fn symmetrical_difference<O: Borrow<Self>>(&self, other: O) -> Self {
        let mut result = self.clone();
        __internal::symmetrical_difference(&mut result, other.borrow());
        result
    }
    /// Returns a set containing all enum variants not present in this set.
    pub fn complement(&self) -> Self {
        let mut result = self.clone();
        __internal::complement(&mut result);
        result
    }

    /// Checks whether this set contains `value`.
    pub fn contains(&self, value: T) -> bool {
        self.has_bit(value.enum_into_u16())
    }

    /// Adds a value to this set.
    ///
    /// If the set did not have this value present, `true` is returned.
    ///
    /// If the set did have this value present, `false` is returned.
    pub fn insert(&mut self, value: T) -> bool {
        !self.set_bit(value.enum_into_u16(), true)
    }
    /// Removes a value from this set. Returns whether the value was present in the set.
    pub fn remove(&mut self, value: T) -> bool {
        self.set_bit(value.enum_into_u16(), false)
    }

    /// Adds all elements in another set to this one.
    pub fn insert_all<O: Borrow<Self>>(&mut self, other: O) {
        __internal::union(self, other.borrow());
    }
    /// Removes all values in another set from this one.
    pub fn remove_all<O: Borrow<Self>>(&mut self, other: O) {
        __internal::difference(self, other.borrow());
    }

    /// Creates an iterator over the values in this set.
    pub fn iter(&self) -> EnumSetIter<&BigEnumSet<T>, T> {
        EnumSetIter(self, 0, PhantomData)
    }
}

impl<T: BigEnumSetType> Default for BigEnumSet<T> {
    /// Returns an empty set.
    fn default() -> Self {
        Self::new()
    }
}
impl<T: BigEnumSetType> IntoIterator for BigEnumSet<T> {
    type Item = T;
    type IntoIter = EnumSetIter<BigEnumSet<T>, T>;

    fn into_iter(self) -> Self::IntoIter {
        EnumSetIter(self, 0, PhantomData)
    }
}

/// Helper macro for implementing binary operators between `BigEnumSet`s.
macro_rules! impl_op {
    ($op_trait:ident, $op_method:ident, $func:ident) => {
        impl<T: BigEnumSetType> $op_trait<BigEnumSet<T>> for BigEnumSet<T> {
            type Output = BigEnumSet<T>;
            fn $op_method(mut self, other: BigEnumSet<T>) -> Self::Output {
                __internal::$func(&mut self, &other);
                self
            }
        }
        impl<T: BigEnumSetType> $op_trait<BigEnumSet<T>> for &BigEnumSet<T> {
            type Output = BigEnumSet<T>;
            fn $op_method(self, other: BigEnumSet<T>) -> Self::Output {
                let mut result = self.clone();
                __internal::$func(&mut result, &other);
                result
            }
        }
        impl<T: BigEnumSetType> $op_trait<&BigEnumSet<T>> for BigEnumSet<T> {
            type Output = BigEnumSet<T>;
            fn $op_method(mut self, other: &BigEnumSet<T>) -> Self::Output {
                __internal::$func(&mut self, other);
                self
            }
        }
        impl<T: BigEnumSetType> $op_trait<&BigEnumSet<T>> for &BigEnumSet<T> {
            type Output = BigEnumSet<T>;
            fn $op_method(self, other: &BigEnumSet<T>) -> Self::Output {
                let mut result = self.clone();
                __internal::$func(&mut result, other);
                result
            }
        }
    };
}
impl_op!(BitOr, bitor, union);
impl_op!(BitAnd, bitand, intersection);
impl_op!(Sub, sub, difference);
impl_op!(BitXor, bitxor, symmetrical_difference);

/// Helper macro for implementing binary operators between `BigEnumSet` and an enum.
macro_rules! impl_op_enum {
    ($op_trait:ident, $op_method:ident, $func:ident) => {
        impl<T: BigEnumSetType> $op_trait<T> for BigEnumSet<T> {
            type Output = Self;
            fn $op_method(mut self, value: T) -> Self::Output {
                __internal::$func(&mut self, value);
                self
            }
        }
        impl<T: BigEnumSetType> $op_trait<T> for &BigEnumSet<T> {
            type Output = BigEnumSet<T>;
            fn $op_method(self, value: T) -> Self::Output {
                let mut result = self.clone();
                __internal::$func(&mut result, value);
                result
            }
        }
    };
}
impl_op_enum!(BitOr, bitor, union_enum);
impl_op_enum!(BitAnd, bitand, intersection_enum);
impl_op_enum!(Sub, sub, difference_enum);
impl_op_enum!(BitXor, bitxor, symmetrical_difference_enum);

/// Helper macro for implementing binary assignment operators between `BigEnumSet`s.
macro_rules! impl_assign_op {
    ($op_trait:ident, $op_method:ident, $func:ident) => {
        impl<T: BigEnumSetType> $op_trait<BigEnumSet<T>> for BigEnumSet<T> {
            fn $op_method(&mut self, other: BigEnumSet<T>) {
                __internal::$func(self, &other);
            }
        }
        impl<T: BigEnumSetType> $op_trait<&BigEnumSet<T>> for BigEnumSet<T> {
            fn $op_method(&mut self, other: &BigEnumSet<T>) {
                __internal::$func(self, other);
            }
        }
    };
}
impl_assign_op!(BitOrAssign, bitor_assign, union);
impl_assign_op!(BitAndAssign, bitand_assign, intersection);
impl_assign_op!(SubAssign, sub_assign, difference);
impl_assign_op!(BitXorAssign, bitxor_assign, symmetrical_difference);

/// Helper macro for implementing binary assignment operators between `BigEnumSet` and an enum.
macro_rules! impl_assign_op_enum {
    ($op_trait:ident, $op_method:ident, $func:ident) => {
        impl<T: BigEnumSetType> $op_trait<T> for BigEnumSet<T> {
            fn $op_method(&mut self, value: T) {
                __internal::$func(self, value);
            }
        }
    };
}
impl_assign_op_enum!(BitOrAssign, bitor_assign, union_enum);
impl_assign_op_enum!(BitAndAssign, bitand_assign, intersection_enum);
impl_assign_op_enum!(SubAssign, sub_assign, difference_enum);
impl_assign_op_enum!(BitXorAssign, bitxor_assign, symmetrical_difference_enum);

impl<T: BigEnumSetType> Not for BigEnumSet<T> {
    type Output = Self;
    fn not(mut self) -> Self::Output {
        __internal::complement(&mut self);
        self
    }
}
impl<T: BigEnumSetType> Not for &BigEnumSet<T> {
    type Output = BigEnumSet<T>;
    fn not(self) -> Self::Output {
        self.complement()
    }
}

impl<T: BigEnumSetType> From<T> for BigEnumSet<T> {
    fn from(t: T) -> Self {
        BigEnumSet::only(t)
    }
}

impl<T: BigEnumSetType> PartialEq<T> for BigEnumSet<T> {
    fn eq(&self, other: &T) -> bool {
        self == &Self::only(*other)
    }
}

impl<T: BigEnumSetType + Debug> Debug for BigEnumSet<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut is_first = true;
        f.write_str("BigEnumSet(")?;
        for v in self.iter() {
            if !is_first {
                f.write_str(" | ")?;
            }
            is_first = false;
            v.fmt(f)?;
        }
        f.write_str(")")?;
        Ok(())
    }
}

impl<T: BigEnumSetType> Hash for BigEnumSet<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.__repr.hash(state)
    }
}
impl<T: BigEnumSetType> PartialOrd for BigEnumSet<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.__repr.partial_cmp(&other.__repr)
    }
}
impl<T: BigEnumSetType> Ord for BigEnumSet<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.__repr.cmp(&other.__repr)
    }
}

#[cfg(feature = "serde")]
impl<T: BigEnumSetType> serde::Serialize for BigEnumSet<T> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        T::serialize(self, serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, T: BigEnumSetType> serde::Deserialize<'de> for BigEnumSet<T> {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        T::deserialize(deserializer)
    }
}

/// The iterator used by [`BigEnumSet`]s.
#[derive(Clone, Debug)]
pub struct EnumSetIter<S, T>(S, u32, PhantomData<T>)
where
    S: Borrow<BigEnumSet<T>>,
    T: BigEnumSetType;

impl<S, T> Iterator for EnumSetIter<S, T>
where
    S: Borrow<BigEnumSet<T>>,
    T: BigEnumSetType,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let set = self.0.borrow();
        while self.1 < BigEnumSet::<T>::bit_width() {
            let bit = self.1 as u16;
            self.1 += 1;
            if set.has_bit(bit) {
                return unsafe { Some(T::enum_from_u16(bit)) };
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let set = self.0.borrow();
        let left_idx = (self.1 >> WORD_SHIFT) as usize;
        let slice = &set.__repr.as_ref()[left_idx..];
        let left = if slice.is_empty() {
            0
        } else {
            let mask = !((1 << (self.1 & u32::from(WORD_MASK))) - 1);
            let mut left = (slice[0] & mask).count_ones();
            for w in &slice[1..] {
                left += w.count_ones();
            }
            left as usize
        };
        (left, Some(left))
    }
}

impl<S, T> ExactSizeIterator for EnumSetIter<S, T>
where
    S: Borrow<BigEnumSet<T>>,
    T: BigEnumSetType,
{
}

impl<T: BigEnumSetType> Extend<T> for BigEnumSet<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        iter.into_iter().for_each(|v| {
            self.insert(v);
        });
    }
}

impl<T: BigEnumSetType> FromIterator<T> for BigEnumSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut set = BigEnumSet::default();
        set.extend(iter);
        set
    }
}

/// Creates a [`BigEnumSet`] literal, which can be used in const contexts.
///
/// The syntax used is `big_enum_set!(Type::A | Type::B | Type::C)`. Each variant must be of the same
/// type, or a error will occur at compile-time.
///
/// # Examples
///
/// ```rust
/// # use big_enum_set::*;
/// # #[derive(BigEnumSetType, Debug)] enum Enum { A, B, C }
/// const CONST_SET: BigEnumSet<Enum> = big_enum_set!(Enum::A | Enum::B);
/// assert_eq!(CONST_SET, Enum::A | Enum::B);
/// ```
///
/// This macro is strongly typed. For example, the following will not compile:
///
/// ```compile_fail
/// # use big_enum_set::*;
/// # #[derive(BigEnumSetType, Debug)] enum Enum { A, B, C }
/// # #[derive(BigEnumSetType, Debug)] enum Enum2 { A, B, C }
/// let type_error = big_enum_set!(Enum::A | Enum2::B);
/// ```
#[macro_export]
macro_rules! big_enum_set {
    ( $( $value:path )|* $( | )? ) => {{
        let mut set = $crate::__internal::EnumSetSameTypeHack {
            unified: &[ $( $value ),* ],
            set: $crate::BigEnumSet::EMPTY,
        }.set;

        $(
            let bit = $value as u16;
            set.__repr[(bit >> $crate::__internal::WORD_SHIFT) as usize] |= 1 << (bit & $crate::__internal::WORD_MASK);
        )*
        set
    }};
}
