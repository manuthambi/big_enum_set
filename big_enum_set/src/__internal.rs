use super::*;
use static_assertions::const_assert_eq;

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
    /// The array of type `[usize; N]` used to store the bitset.
    type Repr: AsMut<[usize]> + AsRef<[usize]> + Copy + Clone + Hash + PartialEq + Eq + PartialOrd + Ord;
    /// Length of `Self::Repr`
    const REPR_LEN: usize;
    /// Array of type `Self::Repr` with all 0s.
    const REPR_NONE: Self::Repr;
    /// Array of type `Self::Repr` with 1s in all valid bits, and 0s otherwise.
    const REPR_ALL: Self::Repr;

    /// Converts an enum of this type into its bit position.
    fn enum_into_u16(self) -> u16;
    /// Converts a bit position into an enum value.
    unsafe fn enum_from_u16(val: u16) -> Self;

    /// Serializes the `BigEnumSet`.
    ///
    /// This and `deserialize` are part of the `BigEnumSetTypePrivate` trait so the procedural derive
    /// can control how `BigEnumSet` is serialized.
    #[cfg(feature = "serde")]
    fn serialize<S: serde::Serializer>(set: &BigEnumSet<Self>, ser: S) -> Result<S::Ok, S::Error>
    where Self: BigEnumSetType;
    /// Deserializes the `BigEnumSet`.
    #[cfg(feature = "serde")]
    fn deserialize<'de, D: serde::Deserializer<'de>>(de: D) -> Result<BigEnumSet<Self>, D::Error>
    where Self: BigEnumSetType;
}

// size of usize in bits
pub const WORD_BITS: u16 = mem::size_of::<usize>() as u16 * 8;
pub const WORD_MASK: u16 = WORD_BITS as u16 - 1;
pub const WORD_SHIFT: u8 = WORD_BITS.trailing_zeros() as u8; // number of bits to shift to get word index.
const_assert_eq!(word_bits_check; WORD_BITS.count_ones(), 1); // check power of 2

// functions to help with implementing operators.
pub(crate) fn union<T: BigEnumSetType>(this: &mut BigEnumSet<T>, other: &BigEnumSet<T>) {
    this.apply_op(other, |w1, w2| w1 | w2);
}
pub(crate) fn intersection<T: BigEnumSetType>(this: &mut BigEnumSet<T>, other: &BigEnumSet<T>) {
    this.apply_op(other, |w1, w2| w1 & w2);
}
pub(crate) fn difference<T: BigEnumSetType>(this: &mut BigEnumSet<T>, other: &BigEnumSet<T>) {
    this.apply_op(other, |w1, w2| w1 & !w2);
}
pub(crate) fn symmetrical_difference<T: BigEnumSetType>(this: &mut BigEnumSet<T>, other: &BigEnumSet<T>) {
    this.apply_op(other, |w1, w2| w1 ^ w2);
}
pub(crate) fn complement<T: BigEnumSetType>(this: &mut BigEnumSet<T>) {
    this.apply_op(&BigEnumSet::all(), |w1, w2| !w1 & w2);
}

pub fn union_enum<T: BigEnumSetType>(this: &mut BigEnumSet<T>, value: T) {
    this.insert(value);
}
pub fn intersection_enum<T: BigEnumSetType>(this: &mut BigEnumSet<T>, value: T) {
    let present = this.contains(value);
    this.clear();
    if present {
        this.insert(value);
    }
}
pub(crate) fn difference_enum<T: BigEnumSetType>(this: &mut BigEnumSet<T>, value: T) {
    this.remove(value);
}
pub fn difference_enum_reverse<T: BigEnumSetType>(this: &mut BigEnumSet<T>, value: T) {
    let present = this.contains(value);
    this.clear();
    if !present {
        this.insert(value);
    }
}
pub fn symmetrical_difference_enum<T: BigEnumSetType>(this: &mut BigEnumSet<T>, value: T) {
    if this.contains(value) {
        this.remove(value);
    } else {
        this.insert(value);
    }
}

#[cfg(feature = "serde")]
pub mod serde_impl {
    use super::serde::{Deserialize, Deserializer};
    use super::serde::{Serialize, Serializer};
    use crate::{BigEnumSet, BigEnumSetType};
    use core::fmt;
    use core::mem;

    /// Serialize `BigEnumSet` as a list of enums. Used from proc-macro.
    pub fn serialize_as_list<S, T>(set: &BigEnumSet<T>, ser: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        T: Serialize + BigEnumSetType,
    {
        use super::serde::ser::SerializeSeq;
        let mut seq = ser.serialize_seq(Some(set.len()))?;
        for v in set.iter() {
            seq.serialize_element(&v)?;
        }
        seq.end()
    }

    pub fn deserialize_from_list<'de, D, T>(deser: D) -> Result<BigEnumSet<T>, D::Error>
    where
        D: Deserializer<'de>,
        T: BigEnumSetType + Deserialize<'de>,
    {
        use super::serde::de::{SeqAccess, Visitor};
        use core::any::type_name;
        use core::marker::PhantomData;

        struct SetVisitor<T>(PhantomData<T>);

        impl<'de, T> Visitor<'de> for SetVisitor<T>
        where T: BigEnumSetType + Deserialize<'de> {
            type Value = BigEnumSet<T>;
            fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "a list of {}", type_name::<T>())
            }
            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error> where A: SeqAccess<'de> {
                let mut accum = BigEnumSet::<T>::new();
                while let Some(val) = seq.next_element::<T>()? {
                    accum |= val;
                }
                Ok(accum)
            }
        }
        deser.deserialize_seq(SetVisitor(PhantomData))
    }

    const WORD_SIZE: usize = mem::size_of::<usize>();

    /// Serialize `BigEnumSet` as bit set. `n_bytes` is the number of bytes in the byte tuple.
    /// Used from proc-macro.
    pub fn serialize_as_bytes<S, T>(set: &BigEnumSet<T>, ser: S, n_bytes: usize) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        T: BigEnumSetType,
    {
        use super::serde::ser::SerializeTuple;
        let words = set.__repr.as_ref();
        debug_assert!(!words.is_empty());
        debug_assert!((words.len() - 1) * WORD_SIZE < n_bytes);

        let mut bytes_left = n_bytes;
        let mut seq = ser.serialize_tuple(n_bytes)?;

        let (last, rest) = words.split_last().unwrap();
        for word in rest.iter() {
            for b in word.to_le_bytes().iter() {
                seq.serialize_element(b)?;
            }
        }
        bytes_left -= rest.len() * WORD_SIZE;

        let last_bytes = bytes_left.min(WORD_SIZE);
        for b in last.to_le_bytes()[0 .. last_bytes].iter() {
            seq.serialize_element(b)?;
        }
        bytes_left -= last_bytes;

        for _i in 0 .. bytes_left {
            seq.serialize_element(&0u8)?;
        }
        seq.end()
    }

    pub fn deserialize_from_bytes<'de, D, T>(deser: D, n_bytes: usize, check_unknown: bool) -> Result<BigEnumSet<T>, D::Error>
    where
        D: Deserializer<'de>,
        T: BigEnumSetType,
    {
        use super::serde::de::{Error, SeqAccess, Visitor};
        use core::marker::PhantomData;

        struct SetVisitor<T> {
            n_bytes: usize,
            check_unknown: bool,
            pd: PhantomData<T>,
        }

        impl<T> SetVisitor<T>
        where T: BigEnumSetType {
            fn validate<E: Error>(&self, bytes_read: usize, mut set: BigEnumSet<T>) -> Result<BigEnumSet<T>, E> {
                if bytes_read != self.n_bytes {
                    return Err(Error::invalid_length(bytes_read, self));
                }

                if self.check_unknown {
                    // Error on any invalid bits.
                    let has_invalid = set.__repr.as_ref().iter()
                        .zip(T::REPR_ALL.as_ref().iter())
                        .any(|(&w1, &w2)| w1 & !w2 != 0);
                    if has_invalid {
                        return Err(Error::custom("BigEnumSet contains unknown bits"));
                    }
                } else {
                    // Clear any invalid bits.
                    set.__repr.as_mut().iter_mut()
                        .zip(T::REPR_ALL.as_ref().iter())
                        .for_each(|(w1, w2)| *w1 &= *w2);
                }
                Ok(set)
            }
        }

        impl<'de, T> Visitor<'de> for SetVisitor<T>
        where T: BigEnumSetType {
            type Value = BigEnumSet<T>;

            fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "a byte array of length {}", self.n_bytes)
            }
            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where A: SeqAccess<'de> {
                let mut set = BigEnumSet::<T>::default();
                let words = set.__repr.as_mut();

                let mut bytes_read = 0;
                for word in words.iter_mut() {
                    let mut word_arr = [0u8; WORD_SIZE];
                    for b in word_arr.iter_mut() {
                        *b = match seq.next_element::<u8>()? {
                            Some(b) => b,
                            None => {
                                *word = usize::from_le_bytes(word_arr);
                                return self.validate(bytes_read, set);
                            }
                        };
                        bytes_read += 1;
                    }
                    *word = usize::from_le_bytes(word_arr);
                }

                while let Some(b) = seq.next_element::<u8>()? {
                    if self.check_unknown && b != 0 {
                        return Err(Error::custom("BigEnumSet contains unknown bits"));
                    }
                    bytes_read += 1;
                }
                self.validate(bytes_read, set)
            }
        }

        deser.deserialize_tuple(n_bytes, SetVisitor { n_bytes, check_unknown, pd: PhantomData })
    }
}
