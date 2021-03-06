#![cfg(feature = "serde")]
#![allow(dead_code)]

use big_enum_set::*;
use serde_derive::*;
use core::{u8, usize};

// Test resistance against shadowed types.
type Some = ();
type None = ();
type Result = ();

#[derive(Serialize, Deserialize, BigEnumSetType, Debug)]
#[big_enum_set(serialize_as_list)]
#[serde(crate="serde2")]
pub enum ListEnum {
    A, B, C, D, E, F, G, H,
}

#[derive(BigEnumSetType, Debug)]
#[big_enum_set(serialize_bytes = 16)]
pub enum ReprEnum {
    A, B, C, D, E, F, G, H,
}

#[derive(BigEnumSetType, Debug)]
#[big_enum_set(serialize_bytes = 5)]
pub enum ReprEnum2 {
    A, B, C, D, E, F, G, H, I = 38, J,
}

#[derive(BigEnumSetType, Debug)]
#[big_enum_set(serialize_bytes = 11)]
pub enum ReprEnum3 {
    A, B, C, D, E, F, G, H,
}

#[derive(BigEnumSetType, Debug)]
#[big_enum_set(serialize_bytes = 2, serialize_deny_unknown)]
pub enum DenyUnknownEnum {
    A, B, C, D, E, F = 7, G, H,
}

#[derive(BigEnumSetType, Debug)]
#[big_enum_set(serialize_bytes = 16, serialize_deny_unknown)]
pub enum DenyUnknownEnum2 {
    A, B, C = 8, D, E, F, G = 20, H,
}

macro_rules! serde_test_simple {
    ($e:ident, $ser_size:expr) => {
        #[test]
        fn serialize_deserialize_test_bincode() {
            let value = $e::A | $e::C | $e::D | $e::F | $e::E | $e::G;
            let serialized = bincode::serialize(&value).unwrap();
            let deserialized = bincode::deserialize::<BigEnumSet<$e>>(&serialized).unwrap();
            assert_eq!(value, deserialized);
            if $ser_size != usize::MAX {
                assert_eq!(serialized.len(), $ser_size);
            }
        }

        #[test]
        fn serialize_deserialize_test_json() {
            let value = $e::A | $e::C | $e::D | $e::E | $e::G | $e::H;
            let serialized = serde_json::to_string(&value).unwrap();
            let deserialized = serde_json::from_str::<BigEnumSet<$e>>(&serialized).unwrap();
            assert_eq!(value, deserialized);
        }
    }
}
macro_rules! serde_test {
    ($e:ident, $ser_size:expr) => {
        serde_test_simple!($e, $ser_size);

        #[test]
        fn deserialize_all_test() {
            let serialized = bincode::serialize(&[u8::MAX; 32]).unwrap();
            let deserialized = bincode::deserialize::<BigEnumSet<$e>>(&serialized).unwrap();
            assert_eq!(BigEnumSet::<$e>::all(), deserialized);
        }
    }
}
macro_rules! tests {
    ($m:ident, $($tt:tt)*) => {
        mod $m {
            use super::*; $($tt)*;
        }
    }
}
tests!(list_enum, serde_test_simple!(ListEnum, usize::MAX));
tests!(repr_enum, serde_test!(ReprEnum, 16));
tests!(repr_enum2, serde_test!(ReprEnum2, 5));
tests!(repr_enum3, serde_test!(ReprEnum3, 11));
tests!(deny_unknown_enum, serde_test_simple!(DenyUnknownEnum, 2));
tests!(deny_unknown_enum2, serde_test_simple!(DenyUnknownEnum2, 16));

#[test]
fn test_deny_unknown() {
    let serialized = bincode::serialize(&[u8::MAX; 32]).unwrap();
    let deserialized = bincode::deserialize::<BigEnumSet<DenyUnknownEnum>>(&serialized);
    assert_eq!(deserialized.unwrap_err().to_string(), "BigEnumSet contains unknown bits");

    assert_eq!(
        serde_json::from_str::<BigEnumSet<DenyUnknownEnum>>("[13,0,0]").unwrap_err().to_string(),
        "invalid length 3, expected a byte array of length 2 at line 1 column 8",
    );
    assert_eq!(
        serde_json::from_str::<BigEnumSet<DenyUnknownEnum2>>("[13,0,0]").unwrap_err().to_string(),
        "invalid length 3, expected a byte array of length 16 at line 1 column 8",
    );

    assert_eq!(
        serde_json::from_str::<BigEnumSet<DenyUnknownEnum>>("[32,0]").unwrap_err().to_string(),
        "BigEnumSet contains unknown bits at line 1 column 6",
    );
    assert_eq!(
        serde_json::from_str::<BigEnumSet<DenyUnknownEnum>>("[16,4]").unwrap_err().to_string(),
        "BigEnumSet contains unknown bits at line 1 column 6",
    );

    assert_eq!(
        serde_json::from_str::<BigEnumSet<DenyUnknownEnum2>>("[0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0]").unwrap_err().to_string(),
        "BigEnumSet contains unknown bits at line 1 column 25",
    );
    assert_eq!(
        serde_json::from_str::<BigEnumSet<DenyUnknownEnum2>>("[128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]").unwrap_err().to_string(),
        "BigEnumSet contains unknown bits at line 1 column 35",
    );
}

#[test]
fn test_json_reprs() {
    assert_eq!(
        ListEnum::A | ListEnum::C | ListEnum::F,
        serde_json::from_str::<BigEnumSet<ListEnum>>(r#"["A","C","F"]"#).unwrap()
    );
    assert_eq!(
        ReprEnum::A | ReprEnum::C | ReprEnum::D,
        serde_json::from_str::<BigEnumSet<ReprEnum>>("[13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]").unwrap()
    );
    assert_eq!(
        ReprEnum2::A | ReprEnum2::C | ReprEnum2::D,
        serde_json::from_str::<BigEnumSet<ReprEnum2>>("[13,0,0,0,0]").unwrap()
    );
    assert_eq!(
        ReprEnum3::A | ReprEnum3::C | ReprEnum3::D,
        serde_json::from_str::<BigEnumSet<ReprEnum3>>("[13,0,0,0,0,0,0,0,0,0,0]").unwrap()
    );
    assert_eq!(
        r#"["A","C","F"]"#,
        serde_json::to_string(&(ListEnum::A | ListEnum::C | ListEnum::F)).unwrap()
    );
    assert_eq!(
        "[13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]",
        serde_json::to_string(&(ReprEnum::A | ReprEnum::C | ReprEnum::D)).unwrap()
    );
    assert_eq!(
        "[13,0,0,0,0]",
        serde_json::to_string(&(ReprEnum2::A | ReprEnum2::C | ReprEnum2::D)).unwrap()
    );
    assert_eq!(
        "[13,0,0,0,0,0,0,0,0,0,0]",
        serde_json::to_string(&(ReprEnum3::A | ReprEnum3::C | ReprEnum3::D)).unwrap()
    );
}

#[derive(BigEnumSetType, Debug)]
#[big_enum_set(serialize_deny_unknown)]
pub enum SingletonEnum {
    A = 9,
}

#[test]
fn test_singleton() {
    let value = BigEnumSet::from(SingletonEnum::A);
    let serialized = bincode::serialize(&value).unwrap();
    let deserialized = bincode::deserialize::<BigEnumSet<SingletonEnum>>(&serialized).unwrap();
    assert_eq!(value, deserialized);
    assert_eq!(serialized.len(), 2);
}
