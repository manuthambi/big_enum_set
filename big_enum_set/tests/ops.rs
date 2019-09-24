#![allow(dead_code)]

use big_enum_set::*;

#[derive(BigEnumSetType, Debug)]
pub enum SmallEnum {
    A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z,
}
#[derive(BigEnumSetType, Debug)]
pub enum LargeEnum {
    _00,  _01,  _02,  _03,  _04,  _05,  _06,  _07,
    _10,  _11,  _12,  _13,  _14,  _15,  _16,  _17,
    _20,  _21,  _22,  _23,  _24,  _25,  _26,  _27,
    _30,  _31,  _32,  _33,  _34,  _35,  _36,  _37,
    _40,  _41,  _42,  _43,  _44,  _45,  _46,  _47,
    _50,  _51,  _52,  _53,  _54,  _55,  _56,  _57,
    _60,  _61,  _62,  _63,  _64,  _65,  _66,  _67,
    _70,  _71,  _72,  _73,  _74,  _75,  _76,  _77,
    A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z,
}
#[derive(BigEnumSetType, Debug)]
pub enum Enum8 {
    A, B, C, D, E, F, G, H,
}
#[derive(BigEnumSetType, Debug)]
pub enum Enum128 {
    A, B, C, D, E, F, G, H, _8, _9, _10, _11, _12, _13, _14, _15,
    _16, _17, _18, _19, _20, _21, _22, _23, _24, _25, _26, _27, _28, _29, _30, _31,
    _32, _33, _34, _35, _36, _37, _38, _39, _40, _41, _42, _43, _44, _45, _46, _47,
    _48, _49, _50, _51, _52, _53, _54, _55, _56, _57, _58, _59, _60, _61, _62, _63,
    _64, _65, _66, _67, _68, _69, _70, _71, _72, _73, _74, _75, _76, _77, _78, _79,
    _80, _81, _82, _83, _84, _85, _86, _87, _88, _89, _90, _91, _92, _93, _94, _95,
    _96, _97, _98, _99, _100, _101, _102, _103, _104, _105, _106, _107, _108, _109,
    _110, _111, _112, _113, _114, _115, _116, _117, _118, _119, _120, _121, _122,
    _123, _124,  _125, _126, _127,
}
#[derive(BigEnumSetType, Debug)]
pub enum SparseEnum {
    A = 10, B = 20, C = 30, D = 40, E = 50, F = 60, G = 70, H = 80,
}

macro_rules! test_variants {
    ($enum_name:ident $all_empty_test:ident $($variant:ident,)*) => {
        #[test]
        fn $all_empty_test() {
            let all = BigEnumSet::<$enum_name>::all();
            let empty = BigEnumSet::<$enum_name>::empty();

            $(
                assert!(!empty.contains($enum_name::$variant));
                assert!(all.contains($enum_name::$variant));
            )*
        }
    }
}
test_variants! { SmallEnum small_enum_all_empty
    A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z,
}
test_variants! { LargeEnum large_enum_all_empty
    _00,  _01,  _02,  _03,  _04,  _05,  _06,  _07,
    _10,  _11,  _12,  _13,  _14,  _15,  _16,  _17,
    _20,  _21,  _22,  _23,  _24,  _25,  _26,  _27,
    _30,  _31,  _32,  _33,  _34,  _35,  _36,  _37,
    _40,  _41,  _42,  _43,  _44,  _45,  _46,  _47,
    _50,  _51,  _52,  _53,  _54,  _55,  _56,  _57,
    _60,  _61,  _62,  _63,  _64,  _65,  _66,  _67,
    _70,  _71,  _72,  _73,  _74,  _75,  _76,  _77,
    A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z,
}
test_variants! { SparseEnum sparse_enum_all_empty
    A, B, C, D, E, F, G,
}

macro_rules! test_enum {
    ($e:ident, $mem_size:expr) => {
        const CONST_SET: BigEnumSet<$e> = big_enum_set!($e::A | $e::C);
        const EMPTY_SET: BigEnumSet<$e> = big_enum_set!();
        #[test]
        fn const_set() {
            assert_eq!(CONST_SET.len(), 2);
            assert!(CONST_SET.contains($e::A));
            assert!(CONST_SET.contains($e::C));
            assert!(EMPTY_SET.is_empty());
        }

        #[test]
        fn basic_add_remove() {
            let mut set = BigEnumSet::new();
            set.insert($e::A);
            set.insert($e::B);
            set.insert($e::C);
            assert_eq!(set, $e::A | $e::B | $e::C);
            set.remove($e::B);
            assert_eq!(set, $e::A | $e::C);
            set.insert($e::D);
            assert_eq!(set, $e::A | $e::C | $e::D);
            set.insert_all($e::F | $e::E | $e::G);
            assert_eq!(set, $e::A | $e::C | $e::D | $e::F | $e::E | $e::G);
            set.remove_all($e::A | $e::D | $e::G);
            assert_eq!(set, $e::C | $e::F | $e::E);
            assert!(!set.is_empty());
            set.clear();
            assert!(set.is_empty());
        }

        #[test]
        fn empty_is_empty() {
            assert_eq!(BigEnumSet::<$e>::empty().len(), 0)
        }

        #[test]
        fn all_len() {
            assert_eq!(BigEnumSet::<$e>::all().len(), BigEnumSet::<$e>::variant_count() as usize)
        }

        #[test]
        fn basic_iter_test() {
            let mut set = BigEnumSet::new();
            set.insert($e::A);
            set.insert($e::B);
            set.insert($e::C);
            set.insert($e::E);

            let mut set_2 = BigEnumSet::new();
            let vec: Vec<$e> = set.iter().collect();
            for val in vec {
                assert!(!set_2.contains(val));
                set_2.insert(val);
            }
            assert_eq!(set, set_2);

            let mut set_3 = BigEnumSet::new();
            for val in set {
                assert!(!set_3.contains(val));
                set_3.insert(val);
            }
            assert_eq!(set, set_3);
        }

        #[test]
        fn basic_ops_test() {
            assert_eq!(($e::A | $e::B) | ($e::B | $e::C), $e::A | $e::B | $e::C);
            assert_eq!(($e::A | $e::B) & ($e::B | $e::C), $e::B);
            assert_eq!(($e::A | $e::B) ^ ($e::B | $e::C), $e::A | $e::C);
            assert_eq!(($e::A | $e::B) - ($e::B | $e::C), $e::A);
        }

        #[test]
        fn basic_set_status() {
            assert!(($e::A | $e::B | $e::C).is_disjoint($e::D | $e::E | $e::F));
            assert!(!($e::A | $e::B | $e::C | $e::D).is_disjoint($e::D | $e::E | $e::F));
            assert!(($e::A | $e::B).is_subset($e::A | $e::B | $e::C));
            assert!(!($e::A | $e::D).is_subset($e::A | $e::B | $e::C));
        }

        #[test]
        fn debug_impl() {
            assert_eq!(format!("{:?}", $e::A | $e::B | $e::D), "BigEnumSet(A | B | D)");
        }

        #[test]
        fn to_from_bits() {
            let value = $e::A | $e::C | $e::D | $e::F | $e::E | $e::G;
            assert_eq!(BigEnumSet::from_bits(value.to_bits()), value);
        }

        #[test]
        #[should_panic]
        fn too_many_bits() {
            if BigEnumSet::<$e>::variant_count() == 128 {
                panic!("(test skipped)")
            }
            BigEnumSet::<$e>::from_bits(!0);
        }

        #[test]
        fn match_const_test() {
            match CONST_SET {
                CONST_SET => { /* ok */ }
                _ => panic!("match fell through?"),
            }
        }

        #[test]
        fn check_size() {
            assert_eq!(::std::mem::size_of::<BigEnumSet<$e>>(), $mem_size);
        }
    }
}
macro_rules! tests {
    ($m:ident, $($tt:tt)*) => { mod $m { use super::*; $($tt)*; } }
}

tests!(small_enum, test_enum!(SmallEnum, 4));
tests!(large_enum, test_enum!(LargeEnum, 16));
tests!(enum8, test_enum!(Enum8, 1));
tests!(enum128, test_enum!(Enum128, 16));
tests!(sparse_enum, test_enum!(SparseEnum, 16));