#![no_std]
#![allow(dead_code)]

extern crate std as __renamed_std; // so we don't have compile issues, but ::std still errors.

use big_enum_set::*;

#[derive(BigEnumSetType)]
#[big_enum_set(serialize_bytes = 4)]
pub enum EmptyEnum { }

#[derive(BigEnumSetType)]
#[big_enum_set(serialize_bytes = 1)]
pub enum Enum1 {
    A,
}

#[derive(BigEnumSetType)]
pub enum SmallEnum {
    A, B, C = 0x5, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z,
}
#[derive(BigEnumSetType)]
pub enum LargeEnum {
    A, B, C = 0xFE, D,
}
#[derive(BigEnumSetType)]
pub enum SparseEnum {
    A = 0xA, B = 20, C = 30, D = 40, E = 50, F = 60, G = 70, H = 80,
}

#[repr(u32)]
#[derive(BigEnumSetType)]
pub enum ReprEnum {
    A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z,
}
#[repr(C)]
#[derive(BigEnumSetType)]
pub enum ReprEnum4 {
    A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z,
}

pub fn main() {}
