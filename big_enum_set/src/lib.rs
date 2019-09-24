#![no_std]
#![forbid(missing_docs)]

//! A library for defining enums that can be used in compact bit sets. It supports enums up to 128
//! variants, and has a macro to use these sets in constants.
//!
//! For serde support, enable the `serde` feature.
//!
//! # Defining enums for use with BigEnumSet
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
//! # Working with EnumSets
//!
//! EnumSets can be constructed via [`BigEnumSet::new()`] like a normal set. In addition,
//! `#[derive(BigEnumSetType)]` creates operator overloads that allow you to create EnumSets like so:
//!
//! ```rust
//! # use big_enum_set::*;
//! # #[derive(BigEnumSetType, Debug)] pub enum Enum { A, B, C, D, E, F, G }
//! let new_set = Enum::A | Enum::C | Enum::G;
//! assert_eq!(new_set.len(), 3);
//! ```
//!
//! All bitwise operations you would expect to work on bitsets also work on both EnumSets and
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
//! The [`big_enum_set!`] macro allows you to create EnumSets in constant contexts:
//!
//! ```rust
//! # use big_enum_set::*;
//! # #[derive(BigEnumSetType, Debug)] pub enum Enum { A, B, C, D, E, F, G }
//! const CONST_SET: BigEnumSet<Enum> = big_enum_set!(Enum::A | Enum::B);
//! assert_eq!(CONST_SET, Enum::A | Enum::B);
//! ```
//!
//! Mutable operations on the [`BigEnumSet`] otherwise work basically as expected:
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

use core::cmp::Ordering;
use core::fmt;
use core::fmt::{Debug, Formatter};
use core::hash::{Hash, Hasher};
use core::ops::*;

use num_traits::*;

#[doc(hidden)]
/// Everything in this module is internal API and may change at any time.
pub mod internal {
    use super::*;

    /// A struct used to type check [`big_enum_set!`].
    pub struct EnumSetSameTypeHack<'a, T: BigEnumSetType + 'static> {
        pub unified: &'a [T],
        pub enum_set: BigEnumSet<T>,
    }

    /// A reexport of core to allow our macros to be generic to std vs core.
    pub use ::core as core_export;

    /// A reexport of serde so there is no requirement to depend on serde.
    #[cfg(feature = "serde")] pub use serde2 as serde;

    /// The actual members of BigEnumSetType. Put here to avoid polluting global namespaces.
    pub unsafe trait EnumSetTypePrivate {
        type Repr: EnumSetTypeRepr;
        const ALL_BITS: Self::Repr;
        fn enum_into_u8(self) -> u8;
        unsafe fn enum_from_u8(val: u8) -> Self;

        #[cfg(feature = "serde")]
        fn serialize<S: serde::Serializer>(set: BigEnumSet<Self>, ser: S) -> Result<S::Ok, S::Error>
            where Self: BigEnumSetType;
        #[cfg(feature = "serde")]
        fn deserialize<'de, D: serde::Deserializer<'de>>(de: D) -> Result<BigEnumSet<Self>, D::Error>
            where Self: BigEnumSetType;
    }
}
use crate::internal::EnumSetTypePrivate;
#[cfg(feature = "serde")] use crate::internal::serde;
#[cfg(feature = "serde")] use crate::serde::{Serialize, Deserialize};

mod private {
    use super::*;
    pub trait EnumSetTypeRepr : PrimInt + FromPrimitive + WrappingSub + CheckedShl + Debug + Hash {
        const WIDTH: u8;
    }
    macro_rules! prim {
        ($name:ty, $width:expr) => {
            impl EnumSetTypeRepr for $name {
                const WIDTH: u8 = $width;
            }
        }
    }
    prim!(u8  , 8  );
    prim!(u16 , 16 );
    prim!(u32 , 32 );
    prim!(u64 , 64 );
    prim!(u128, 128);
}
use crate::private::EnumSetTypeRepr;

/// The trait used to define enum types that may be used with [`BigEnumSet`].
///
/// This trait should be implemented using `#[derive(BigEnumSetType)]`. Its internal structure is
/// not currently stable, and may change at any time.
///
/// # Custom Derive
///
/// The custom derive for [`BigEnumSetType`] automatically creates implementations of [`PartialEq`],
/// [`Sub`], [`BitAnd`], [`BitOr`], [`BitXor`], and [`Not`] allowing the enum to be used as
/// if it were an [`BigEnumSet`] in expressions. This can be disabled by adding an `#[big_enum_set(no_ops)]`
/// annotation to the enum.
///
/// The custom derive for `BigEnumSetType` automatically implements [`Copy`], [`Clone`], [`Eq`], and
/// [`PartialEq`] on the enum. These are required for the [`BigEnumSet`] to function.
///
/// Any C-like enum is supported, as long as there are no more than 128 variants in the enum,
/// and no variant discriminator is larger than 127.
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
pub unsafe trait BigEnumSetType: Copy + Eq + EnumSetTypePrivate { }

/// An efficient set type for enums.
///
/// # Serialization
///
/// The default representation serializes enumsets as an `u8`, `u16`, `u32`, `u64`, or `u128`,
/// whichever is the smallest that can contain all bits that are part of the set.
///
/// Unknown bits are ignored, and are simply dropped. To override this behavior, you can add a
/// `#[big_enum_set(serialize_deny_unknown)]` annotation to your enum.
///
/// You can add a `#[big_enum_set(serialize_repr = "u8")]` annotation to your enum to explicitly set
/// the bit width the `BigEnumSet` is serialized as. This can be used to avoid breaking changes in
/// certain serialization formats (such as `bincode`).
///
/// In addition, the `#[big_enum_set(serialize_as_list)]` annotation causes the `BigEnumSet` to be
/// instead serialized as a list. This requires your enum type implement [`Serialize`] and
/// [`Deserialize`].
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct BigEnumSet<T : BigEnumSetType> {
    #[doc(hidden)]
    /// This is public due to the [`big_enum_set!`] macro.
    /// This is **NOT** public API and may change at any time.
    pub __enumset_underlying: T::Repr
}
impl <T : BigEnumSetType> BigEnumSet<T> {
    fn mask(bit: u8) -> T::Repr {
        Shl::<usize>::shl(T::Repr::one(), bit as usize)
    }
    fn has_bit(&self, bit: u8) -> bool {
        let mask = Self::mask(bit);
        self.__enumset_underlying & mask == mask
    }
    fn partial_bits(bits: u8) -> T::Repr {
        T::Repr::one().checked_shl(bits.into())
            .unwrap_or(T::Repr::zero())
            .wrapping_sub(&T::Repr::one())
    }

    // Returns all bits valid for the enum
    fn all_bits() -> T::Repr {
        T::ALL_BITS
    }

    /// Returns an empty set.
    pub fn new() -> Self {
        BigEnumSet { __enumset_underlying: T::Repr::zero() }
    }

    /// Returns a set containing a single value.
    pub fn only(t: T) -> Self {
        BigEnumSet { __enumset_underlying: Self::mask(t.enum_into_u8()) }
    }

    /// Returns an empty set.
    pub fn empty() -> Self {
        Self::new()
    }
    /// Returns a set with all bits set.
    pub fn all() -> Self {
        BigEnumSet { __enumset_underlying: Self::all_bits() }
    }

    /// Total number of bits this enum set uses. Note that the actual amount of space used is
    /// rounded up to the next highest integer type (`u8`, `u16`, `u32`, `u64`, or `u128`).
    ///
    /// This is the same as [`BigEnumSet::variant_count`] except in enums with "sparse" variants.
    /// (e.g. `enum Foo { A = 10, B = 20 }`)
    pub fn bit_width() -> u8 {
        T::Repr::WIDTH - T::ALL_BITS.leading_zeros() as u8
    }

    /// The number of valid variants in this enum set.
    ///
    /// This is the same as [`BigEnumSet::bit_width`] except in enums with "sparse" variants.
    /// (e.g. `enum Foo { A = 10, B = 20 }`)
    pub fn variant_count() -> u8 {
        T::ALL_BITS.count_ones() as u8
    }

    /// Returns the raw bits of this set
    pub fn to_bits(&self) -> u128 {
        self.__enumset_underlying.to_u128()
            .expect("Impossible: Bits cannot be to converted into i128?")
    }

    /// Constructs a bitset from raw bits.
    ///
    /// # Panics
    /// If bits not in the enum are set.
    pub fn from_bits(bits: u128) -> Self {
        assert!((bits & !Self::all().to_bits()) == 0, "Bits not valid for the enum were set.");
        BigEnumSet {
            __enumset_underlying: T::Repr::from_u128(bits)
                .expect("Impossible: Valid bits too large to fit in repr?")
        }
    }

    /// Returns the number of values in this set.
    pub fn len(&self) -> usize {
        self.__enumset_underlying.count_ones() as usize
    }
    /// Checks if the set is empty.
    pub fn is_empty(&self) -> bool {
        self.__enumset_underlying.is_zero()
    }
    /// Removes all elements from the set.
    pub fn clear(&mut self) {
        self.__enumset_underlying = T::Repr::zero()
    }

    /// Checks if this set shares no elements with another.
    pub fn is_disjoint(&self, other: Self) -> bool {
        (*self & other).is_empty()
    }
    /// Checks if all elements in another set are in this set.
    pub fn is_superset(&self, other: Self) -> bool {
        (*self & other).__enumset_underlying == other.__enumset_underlying
    }
    /// Checks if all elements of this set are in another set.
    pub fn is_subset(&self, other: Self) -> bool {
        other.is_superset(*self)
    }

    /// Returns a set containing the union of all elements in both sets.
    pub fn union(&self, other: Self) -> Self {
        BigEnumSet { __enumset_underlying: self.__enumset_underlying | other.__enumset_underlying }
    }
    /// Returns a set containing all elements in common with another set.
    pub fn intersection(&self, other: Self) -> Self {
        BigEnumSet { __enumset_underlying: self.__enumset_underlying & other.__enumset_underlying }
    }
    /// Returns a set with all elements of the other set removed.
    pub fn difference(&self, other: Self) -> Self {
        BigEnumSet { __enumset_underlying: self.__enumset_underlying & !other.__enumset_underlying }
    }
    /// Returns a set with all elements not contained in both sets.
    pub fn symmetrical_difference(&self, other: Self) -> Self {
        BigEnumSet { __enumset_underlying: self.__enumset_underlying ^ other.__enumset_underlying }
    }
    /// Returns a set containing all elements not in this set.
    pub fn complement(&self) -> Self {
        BigEnumSet { __enumset_underlying: !self.__enumset_underlying & Self::all_bits() }
    }

    /// Checks whether this set contains a value.
    pub fn contains(&self, value: T) -> bool {
        self.has_bit(value.enum_into_u8())
    }

    /// Adds a value to this set.
    pub fn insert(&mut self, value: T) -> bool {
        let contains = self.contains(value);
        self.__enumset_underlying = self.__enumset_underlying | Self::mask(value.enum_into_u8());
        contains
    }
    /// Removes a value from this set.
    pub fn remove(&mut self, value: T) -> bool {
        let contains = self.contains(value);
        self.__enumset_underlying = self.__enumset_underlying & !Self::mask(value.enum_into_u8());
        contains
    }

    /// Adds all elements in another set to this one.
    pub fn insert_all(&mut self, other: Self) {
        self.__enumset_underlying = self.__enumset_underlying | other.__enumset_underlying
    }
    /// Removes all values in another set from this one.
    pub fn remove_all(&mut self, other: Self) {
        self.__enumset_underlying = self.__enumset_underlying & !other.__enumset_underlying
    }

    /// Creates an iterator over the values in this set.
    pub fn iter(&self) -> EnumSetIter<T> {
        EnumSetIter(*self, 0)
    }
}

impl <T: BigEnumSetType> Default for BigEnumSet<T> {
    /// Returns an empty set.
    fn default() -> Self {
        Self::new()
    }
}

impl <T : BigEnumSetType> IntoIterator for BigEnumSet<T> {
    type Item = T;
    type IntoIter = EnumSetIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl <T : BigEnumSetType, O: Into<BigEnumSet<T>>> Sub<O> for BigEnumSet<T> {
    type Output = Self;
    fn sub(self, other: O) -> Self::Output {
        self.difference(other.into())
    }
}
impl <T : BigEnumSetType, O: Into<BigEnumSet<T>>> BitAnd<O> for BigEnumSet<T> {
    type Output = Self;
    fn bitand(self, other: O) -> Self::Output {
        self.intersection(other.into())
    }
}
impl <T : BigEnumSetType, O: Into<BigEnumSet<T>>> BitOr<O> for BigEnumSet<T> {
    type Output = Self;
    fn bitor(self, other: O) -> Self::Output {
        self.union(other.into())
    }
}
impl <T : BigEnumSetType, O: Into<BigEnumSet<T>>> BitXor<O> for BigEnumSet<T> {
    type Output = Self;
    fn bitxor(self, other: O) -> Self::Output {
        self.symmetrical_difference(other.into())
    }
}

impl <T : BigEnumSetType, O: Into<BigEnumSet<T>>> SubAssign<O> for BigEnumSet<T> {
    fn sub_assign(&mut self, rhs: O) {
        *self = *self - rhs;
    }
}
impl <T : BigEnumSetType, O: Into<BigEnumSet<T>>> BitAndAssign<O> for BigEnumSet<T> {
    fn bitand_assign(&mut self, rhs: O) {
        *self = *self & rhs;
    }
}
impl <T : BigEnumSetType, O: Into<BigEnumSet<T>>> BitOrAssign<O> for BigEnumSet<T> {
    fn bitor_assign(&mut self, rhs: O) {
        *self = *self | rhs;
    }
}
impl <T : BigEnumSetType, O: Into<BigEnumSet<T>>> BitXorAssign<O> for BigEnumSet<T> {
    fn bitxor_assign(&mut self, rhs: O) {
        *self = *self ^ rhs;
    }
}

impl <T : BigEnumSetType> Not for BigEnumSet<T> {
    type Output = Self;
    fn not(self) -> Self::Output {
        self.complement()
    }
}

impl <T : BigEnumSetType> From<T> for BigEnumSet<T> {
    fn from(t: T) -> Self {
        BigEnumSet::only(t)
    }
}

impl <T : BigEnumSetType> PartialEq<T> for BigEnumSet<T> {
    fn eq(&self, other: &T) -> bool {
        self.__enumset_underlying == BigEnumSet::<T>::mask(other.enum_into_u8())
    }
}
impl <T : BigEnumSetType + Debug> Debug for BigEnumSet<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut is_first = true;
        f.write_str("BigEnumSet(")?;
        for v in self.iter() {
            if !is_first { f.write_str(" | ")?; }
            is_first = false;
            v.fmt(f)?;
        }
        f.write_str(")")?;
        Ok(())
    }
}

impl <T: BigEnumSetType> Hash for BigEnumSet<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.__enumset_underlying.hash(state)
    }
}
impl <T: BigEnumSetType> PartialOrd for BigEnumSet<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.__enumset_underlying.partial_cmp(&other.__enumset_underlying)
    }
}
impl <T: BigEnumSetType> Ord for BigEnumSet<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.__enumset_underlying.cmp(&other.__enumset_underlying)
    }
}

#[cfg(feature = "serde")]
impl <T : BigEnumSetType> Serialize for BigEnumSet<T> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        T::serialize(*self, serializer)
    }
}

#[cfg(feature = "serde")]
impl <'de, T : BigEnumSetType> Deserialize<'de> for BigEnumSet<T> {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        T::deserialize(deserializer)
    }
}

/// The iterator used by [`BigEnumSet`](./struct.BigEnumSet.html).
#[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Hash, Debug)]
pub struct EnumSetIter<T : BigEnumSetType>(BigEnumSet<T>, u8);
impl <T : BigEnumSetType> Iterator for EnumSetIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        while self.1 < BigEnumSet::<T>::bit_width() {
            let bit = self.1;
            self.1 += 1;
            if self.0.has_bit(bit) {
                return unsafe { Some(T::enum_from_u8(bit)) }
            }
        }
        None
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let left_mask = BigEnumSet::<T>::partial_bits(self.1);
        let left = (self.0.__enumset_underlying & left_mask).count_ones() as usize;
        (left, Some(left))
    }
}

/// Creates a BigEnumSet literal, which can be used in const contexts.
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
    () => {
        $crate::BigEnumSet { __enumset_underlying: 0 }
    };
    ($($value:path)|* $(|)*) => {
        $crate::internal::EnumSetSameTypeHack {
            unified: &[$($value,)*],
            enum_set: $crate::BigEnumSet {
                __enumset_underlying: 0 $(| (1 << ($value as u8)))*
            },
        }.enum_set
    };
}
