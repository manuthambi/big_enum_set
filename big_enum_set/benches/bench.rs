use criterion::{black_box, criterion_group, criterion_main, Criterion};
use big_enum_set::*;
use big_enum_set::__internal::BigEnumSetTypePrivate;


#[allow(dead_code)]
#[derive(BigEnumSetType)]
enum EnumSmall {
    A, B, C, D, E, F, G, H,
}

#[allow(dead_code)]
#[derive(BigEnumSetType)]
enum EnumLarge {
    A = 0x40, B = 0x100, C, D = 0x300, E, F = 0x600, G, H,
}

fn enumset_ops(cr: &mut Criterion) {
    macro_rules! run {
        ($enum:ident, $cr:expr) => {{
            use $enum as Enum;
            let mut set = big_enum_set!(Enum::A | Enum::G | Enum::D);
            let set2 = big_enum_set!(Enum::B | Enum::C | Enum::E);
            $cr.bench_function(concat!(stringify!($enum), " set contains"), |b| b.iter(|| {
                black_box(&mut set).contains(black_box(Enum::G))
            }));
            $cr.bench_function(concat!(stringify!($enum), " set insert"), |b| b.iter(|| {
                black_box(&mut set).insert(black_box(Enum::C))
            }));
            $cr.bench_function(concat!(stringify!($enum), " set remove"), |b| b.iter(|| {
                black_box(&mut set).remove(black_box(Enum::C))
            }));
            $cr.bench_function(concat!(stringify!($enum), " set iter"), |b| b.iter(|| {
                black_box(&mut set).iter().map(|x| x as isize).sum::<isize>()
            }));
            $cr.bench_function(concat!(stringify!($enum), " set is_disjoint"), |b| b.iter(|| {
                black_box(&mut set).is_disjoint(black_box(&set2))
            }));
        }};
    }
    run!(EnumSmall, cr);
    run!(EnumLarge, cr);
}

#[derive(BigEnumSetType)]
#[repr(u8)]
#[allow(dead_code)]
enum Enum8 {
    A, B, C, D, E, F, G, H,
}

#[derive(BigEnumSetType)]
#[repr(u64)]
#[allow(dead_code)]
enum Enum64 {
    A, B, C, D, E, F, G, H,
}

#[derive(BigEnumSetType)]
#[repr(C)]
#[allow(dead_code)]
enum EnumC {
    A, B, C, D, E, F, G, H,
}

fn enum_from(c: &mut Criterion) {
    macro_rules! run {
        ($enum:ident, $cr:expr) => {{
            use $enum as Enum;
            c.bench_function(concat!(stringify!($enum), "::enum_from_u16"), |b| b.iter(|| {
                unsafe { <Enum as BigEnumSetTypePrivate>::enum_from_u16(black_box($enum::A as u16)) }
            }));
        }}
    }

    run!(Enum8, cr);
    run!(Enum64, cr);
    run!(EnumC, cr);
}

criterion_group!(all, enum_from, enumset_ops);
criterion_main!(all);
