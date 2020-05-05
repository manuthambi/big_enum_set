use static_assertions::const_assert_eq;
use super::*;

/// A struct used to type check [`big_enum_set!`].
pub struct EnumSetSameTypeHack<'a, T: BigEnumSetType + 'static> {
    pub unified: &'a [T],
    pub set: BigEnumSet<T>,
}

/// A reexport of serde so there is no requirement to depend on serde.
#[cfg(feature = "serde")]
pub use serde2 as serde;

/// The actual members of BigEnumSetType. Put here to avoid polluting global namespaces.
pub unsafe trait BigEnumSetTypePrivate {
    type Repr: AsMut<[usize]> + AsRef<[usize]> + Copy + Clone + Hash + PartialEq + Eq + PartialOrd + Ord;
    const REPR_LEN: usize; // Length of the array
    const REPR_NONE: Self::Repr;
    const REPR_ALL: Self::Repr;

    fn enum_into_u16(self) -> u16;
    unsafe fn enum_from_u16(val: u16) -> Self;

    #[cfg(feature = "serde")]
    fn serialize<S: serde::Serializer>(set: BigEnumSet<Self>, ser: S) -> Result<S::Ok, S::Error>
    where Self: BigEnumSetType;
    #[cfg(feature = "serde")]
    fn deserialize<'de, D: serde::Deserializer<'de>>(de: D) -> Result<BigEnumSet<Self>, D::Error>
    where Self: BigEnumSetType;
}

// size of usize in bits
pub const WORD_BITS: u16 = mem::size_of::<usize>() as u16 * 8;
pub const WORD_MASK: u16 = WORD_BITS as u16 - 1;
pub const WORD_SHIFT: u8 = WORD_BITS.trailing_zeros() as u8; // number of bits to shift to get word index.
const_assert_eq!(word_bits_check; WORD_BITS.count_ones(), 1); // check power of 2
