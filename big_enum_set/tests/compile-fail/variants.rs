use big_enum_set::*;

#[derive(BigEnumSetType)]
#[repr(i64)]
enum DiscriminantTooLarge {
    Variant = 0x100000,
}

#[derive(BigEnumSetType)]
enum DiscriminantTooLarge2 {
    _0, _1, _2, _3, _4, _5 = 65535, _6,
}

#[derive(BigEnumSetType)]
enum NegativeDiscriminant {
    Variant = -1,
}

#[derive(BigEnumSetType)]
enum HasFields {
    Variant(u32),
}

#[derive(BigEnumSetType)]
enum HasTypeParams<T> {
    A, B(T),
}

#[derive(BigEnumSetType)]
#[big_enum_set(serialize_bytes = 1)]
enum BadSerializationRepr {
    Variant = 8,
}

#[derive(BigEnumSetType)]
struct BadItemType {

}

fn main() { }
