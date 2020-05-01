#![recursion_limit = "256"]
#![cfg_attr(feature = "nightly", feature(proc_macro_diagnostic))]

extern crate proc_macro;

use bit_set::BitSet;
use bit_vec::BitBlock;
use darling::*;
use proc_macro::TokenStream;
use proc_macro2::{Literal, TokenStream as SynTokenStream};
use quote::*;
use syn::export::Span;
use syn::spanned::Spanned;
use syn::Error;
use syn::*;

use core::iter::FromIterator;

fn error(span: Span, msg: &str) -> TokenStream {
    Error::new(span, msg).to_compile_error().into()
}

fn enum_set_type_impl(
    name: &Ident,
    all_variants: &BitSet<usize>,
    max_variant: usize,
    max_variant_ident: Option<Ident>,
    attrs: EnumsetAttrs,
) -> SynTokenStream {
    let is_byte_enum = max_variant <= usize::from(core::u8::MAX);
    let is_uninhabited = all_variants.is_empty();
    let is_zst = all_variants.len() == 1;

    let typed_big_enum_set = quote!(::big_enum_set::BigEnumSet<#name>);

    #[cfg(feature = "serde")]
    let serde = quote!(::big_enum_set::internal::serde);

    let ops = if attrs.no_ops {
        quote! {}
    } else {
        quote! {
            impl <O : Into<#typed_big_enum_set>> ::core::ops::Sub<O> for #name {
                type Output = #typed_big_enum_set;
                fn sub(self, other: O) -> Self::Output {
                    ::big_enum_set::BigEnumSet::only(self) - other.into()
                }
            }
            impl <O : Into<#typed_big_enum_set>> ::core::ops::BitAnd<O> for #name {
                type Output = #typed_big_enum_set;
                fn bitand(self, other: O) -> Self::Output {
                    ::big_enum_set::BigEnumSet::only(self) & other.into()
                }
            }
            impl <O : Into<#typed_big_enum_set>> ::core::ops::BitOr<O> for #name {
                type Output = #typed_big_enum_set;
                fn bitor(self, other: O) -> Self::Output {
                    ::big_enum_set::BigEnumSet::only(self) | other.into()
                }
            }
            impl <O : Into<#typed_big_enum_set>> ::core::ops::BitXor<O> for #name {
                type Output = #typed_big_enum_set;
                fn bitxor(self, other: O) -> Self::Output {
                    ::big_enum_set::BigEnumSet::only(self) ^ other.into()
                }
            }
            impl ::core::ops::Not for #name {
                type Output = #typed_big_enum_set;
                fn not(self) -> Self::Output {
                    !::big_enum_set::BigEnumSet::only(self)
                }
            }
            impl ::core::cmp::PartialEq<#typed_big_enum_set> for #name {
                fn eq(&self, other: &#typed_big_enum_set) -> bool {
                    ::big_enum_set::BigEnumSet::only(*self) == *other
                }
            }
        }
    };

    #[cfg(feature = "serde")]
    let serde_ops = if attrs.serialize_as_list {
        let expecting_str = format!("a list of {}", name);
        quote! {
            fn serialize<S: #serde::Serializer>(
                set: ::big_enum_set::BigEnumSet<#name>, ser: S,
            ) -> ::core::result::Result<S::Ok, S::Error> {
                let mut seq = ser.serialize_seq(::core::option::Option::Some(set.len()))?;
                for bit in set {
                    #serde::ser::SerializeSeq::serialize_element(&mut seq, &bit)?;
                }
                #serde::ser::SerializeSeq::end(seq)
            }
            fn deserialize<'de, D: #serde::Deserializer<'de>>(
                de: D,
            ) -> ::core::result::Result<::big_enum_set::BigEnumSet<#name>, D::Error> {
                struct Visitor;
                impl <'de> #serde::de::Visitor<'de> for Visitor {
                    type Value = ::big_enum_set::BigEnumSet<#name>;
                    fn expecting(
                        &self, formatter: &mut ::core::fmt::Formatter,
                    ) -> ::core::fmt::Result {
                        write!(formatter, #expecting_str)
                    }
                    fn visit_seq<A>(
                        mut self, mut seq: A,
                    ) -> ::core::result::Result<Self::Value, A::Error> where A: #serde::de::SeqAccess<'de> {
                        let mut accum = ::big_enum_set::BigEnumSet::<#name>::new();
                        while let ::core::option::Option::Some(val) = seq.next_element::<#name>()? {
                            accum |= val;
                        }
                        ::core::result::Result::Ok(accum)
                    }
                }
                de.deserialize_seq(Visitor)
            }
        }
    } else {
        let min_bytes = max_variant / 8 + 1;
        let serialize_bytes = attrs.serialize_bytes.map(usize::from).unwrap_or(min_bytes);
        assert!(min_bytes <= serialize_bytes);

        let enum_type = quote!(<#name as ::big_enum_set::internal::EnumSetTypePrivate>);
        let check_unknown = if attrs.serialize_deny_unknown {
            quote! {
                if set.__repr.iter().zip(#enum_type::REPR_ALL.iter()).any(|(&w1, &w2)| w1 & !w2 != 0) ||
                    rem.iter().any(|&b| b != 0) {
                        return ::core::result::Result::Err(
                            <D::Error as #serde::de::Error>::custom("BigEnumSet contains unknown bits")
                        );
                    }
            }
        } else {
            quote! {}
        };
        quote! {
            fn serialize<S: #serde::Serializer>(
                set: ::big_enum_set::BigEnumSet<#name>, ser: S,
            ) -> ::core::result::Result<S::Ok, S::Error> {
                const WORD_SIZE: usize = ::core::mem::size_of::<usize>();
                let mut bytes = [0u8; #serialize_bytes];
                let mut chunks = bytes.chunks_exact_mut(WORD_SIZE);
                let mut words = set.__repr.iter();

                (&mut chunks).zip(&mut words)
                    .for_each(|(chunk, word)| chunk.copy_from_slice(&word.to_le_bytes()));

                if let Some(word) = words.next() {
                    let mut rem = chunks.into_remainder();
                    let len = rem.len().min(WORD_SIZE);
                    rem[0 .. len].copy_from_slice(&word.to_le_bytes()[0 .. len]);
                }
                #serde::Serialize::serialize(&bytes, ser)
            }
            fn deserialize<'de, D: #serde::Deserializer<'de>>(
                de: D,
            ) -> ::core::result::Result<::big_enum_set::BigEnumSet<#name>, D::Error> {
                const WORD_SIZE: usize = core::mem::size_of::<usize>();
                let bytes: [u8; #serialize_bytes] = #serde::Deserialize::deserialize(de)?;
                let mut chunks = bytes.chunks_exact(WORD_SIZE);

                let mut set = ::big_enum_set::BigEnumSet::<#name>::default();
                let mut words = set.__repr.iter_mut();

                (&mut chunks).zip(&mut words)
                    .for_each(|(chunk, word)| {
                        let mut v = [0u8; WORD_SIZE];
                        v.copy_from_slice(&chunk);
                        *word = usize::from_le_bytes(v);
                    });

                let mut rem = chunks.remainder();
                if let Some(word) = words.next() {
                    let mut v = [0u8; WORD_SIZE];
                    let len = rem.len().min(WORD_SIZE);
                    v[0 .. len].copy_from_slice(&rem[0 .. len]);
                    *word = usize::from_le_bytes(v);
                    rem = &rem[len ..];
                }

                #check_unknown
                set.__repr.iter_mut()
                    .zip(#enum_type::REPR_ALL.iter())
                    .for_each(|(w1, w2)| *w1 = *w1 & *w2);

                ::core::result::Result::Ok(set)
            }
        }
    };

    #[cfg(not(feature = "serde"))]
    let serde_ops = quote! {};

    let repr_len = if is_uninhabited {
        quote!(0usize)
    } else {
        quote!(#max_variant / (::core::mem::size_of::<usize>() * 8) + 1)
    };

    // Compute repr_all seperately like below to allow cross-compiling into a arch with
    // a different pointer width.
    fn repr_elems<B: BitBlock + Into<u64>>(all_variants: &BitSet<usize>) -> Vec<Literal> {
        BitSet::<B>::from_iter(all_variants)
            .get_ref()
            .blocks()
            .map(|w| Literal::u64_unsuffixed(w.into()))
            .collect()
    }
    let repr_elems_u16 = repr_elems::<u16>(all_variants);
    let repr_elems_u32 = repr_elems::<u32>(all_variants);
    let repr_elems_u64 = repr_elems::<u64>(all_variants);
    let repr_all = quote! {{
        #[cfg(target_pointer_width = "16")] { [ #( #repr_elems_u16 ),* ] }
        #[cfg(target_pointer_width = "32")] { [ #( #repr_elems_u32 ),* ] }
        #[cfg(target_pointer_width = "64")] { [ #( #repr_elems_u64 ),* ] }
        #[cfg(not(any(target_pointer_width = "16", target_pointer_width = "32", target_pointer_width = "64")))]
        { core::compile_error!("Invalid target_pointer_width") }
    }};

    let into_impl = if is_uninhabited {
        quote!(panic!(concat!(stringify!(#name), " is uninhabited.")))
    } else {
        quote!(self as u16)
    };

    let from_impl = if is_uninhabited {
        quote!(panic!(concat!(stringify!(#name), " is uninhabited.")))
    } else if is_zst {
        let variant = max_variant_ident.unwrap();
        quote!(#name::#variant)
    } else if is_byte_enum {
        quote!(::core::mem::transmute(val as u8))
    } else {
        quote!(::core::mem::transmute(val))
    };

    let eq_impl = if is_uninhabited {
        quote!(panic!(concat!(stringify!(#name), " is uninhabited.")))
    } else {
        quote!((*self as u16) == (*other as u16))
    };

    quote! {
        unsafe impl ::big_enum_set::internal::EnumSetTypePrivate for #name {
            type Repr = [usize; #repr_len];
            const REPR_LEN: usize = #repr_len;
            const REPR_NONE: Self::Repr = [0; #repr_len];
            const REPR_ALL: Self::Repr = #repr_all;

            fn enum_into_u16(self) -> u16 {
                #into_impl
            }
            unsafe fn enum_from_u16(val: u16) -> Self {
                #from_impl
            }

            #serde_ops
        }
        unsafe impl ::big_enum_set::BigEnumSetType for #name { }

        impl ::core::cmp::PartialEq for #name {
            fn eq(&self, other: &Self) -> bool {
                #eq_impl
            }
        }
        impl ::core::cmp::Eq for #name { }
        impl ::core::clone::Clone for #name {
            fn clone(&self) -> Self {
                *self
            }
        }
        impl ::core::marker::Copy for #name { }

        #ops
    }
}

#[derive(FromDeriveInput, Default)]
#[darling(attributes(big_enum_set), default)]
struct EnumsetAttrs {
    no_ops: bool,
    serialize_as_list: bool,
    serialize_deny_unknown: bool,
    #[darling(default)]
    serialize_bytes: Option<u8>,
}

// We put a limit, to avoid accidentally creating sets which use up large amounts of memory
// if one of the discriminants is large.
const MAX_VARIANT: usize = core::u16::MAX as usize;

/// Procedural derive generating `big_enum_set::BigEnumSetType` implementation.
///
/// # Examples
///
/// ```
/// use big_enum_set::BigEnumSetType;
///
/// #[derive(BigEnumSetType)]
/// #[big_enum_set(serialize_bytes="22")]
/// pub enum Enum {
///    A, B, C, D, E, F, G,
/// }
/// ```
///
/// The derivation may be customized by the following attributes.
/// * Use `#[big_enum_set(no_ops)]` to disable automatically implementing
///   [`Sub`], [`BitAnd`], [`BitOr`], [`BitXor`], [`Not`].
/// * With serde, use `#[big_enum_set(serialize_as_list)]` to serialize [`BigEnumSet`]
///   as list of elements instead of a bitset.
/// * With serde, use `#[big_enum_set(serialize_deny_unknown)]` to generate an
///   error during derserialization of [`BigEnumSet`] for an unknown variant of the enum.
/// * With serde, use `#[big_enum_set(serialize_bytes="N")]` to serialize [`BigEnumSet`]
///   to N bytes, rather than the minimum number of bytes needed to store the bitset.
///   N >= number of variants / 8.
#[proc_macro_derive(BigEnumSetType, attributes(big_enum_set))]
pub fn derive_enum_set_type(input: TokenStream) -> TokenStream {
    let input: DeriveInput = parse_macro_input!(input);
    if let Data::Enum(data) = &input.data {
        if !input.generics.params.is_empty() {
            error(
                input.generics.span(),
                "`#[derive(BigEnumSetType)]` cannot be used on enums with type parameters.",
            )
        } else {
            let mut all_variants = BitSet::default();
            let mut max_variant = 0_usize;
            let mut max_variant_ident = None;
            let mut current_variant = 0_usize;

            for variant in &data.variants {
                if let Fields::Unit = variant.fields {
                    let mut has_manual_discriminant = false;
                    if let Some((_, expr)) = &variant.discriminant {
                        if let Expr::Lit(ExprLit { lit: Lit::Int(i), .. }) = expr {
                            current_variant = match i.base10_parse::<usize>() {
                                Ok(v) => v,
                                Err(_e) => return error(variant.span(), "Unparseable discriminant for variant."),
                            };
                            has_manual_discriminant = true;
                        } else {
                            return error(variant.span(), "Unrecognized discriminant for variant.");
                        }
                    }

                    if current_variant > MAX_VARIANT {
                        let message = if has_manual_discriminant {
                            format!("`#[derive(BigEnumSetType)]` only supports enum discriminants up to {}.", MAX_VARIANT)
                        } else {
                            format!("`#[derive(BigEnumSetType)]` only supports enums up to {} variants.", MAX_VARIANT+1)
                        };
                        return error(variant.span(), &message);
                    }

                    if all_variants.contains(current_variant) {
                        return error(
                            variant.span(),
                            &format!("Duplicate enum discriminant: {}", current_variant),
                        );
                    }

                    all_variants.insert(current_variant);
                    if current_variant >= max_variant {
                        // use >= because max_variant is initialized to 0.
                        max_variant = current_variant;
                        max_variant_ident = Some(variant.ident.clone());
                    }
                    current_variant += 1;
                } else {
                    return error(
                        variant.span(),
                        "`#[derive(BigEnumSetType)]` can only be used on C-like enums.",
                    );
                }
            }

            let attrs: EnumsetAttrs = match EnumsetAttrs::from_derive_input(&input) {
                Ok(attrs) => attrs,
                Err(e) => return e.write_errors().into(),
            };

            if let Some(bytes) = attrs.serialize_bytes {
                if max_variant / 8 >= usize::from(bytes) {
                    return error(input.span(), &format!("Too many variants for serialization into {} bytes.", bytes))
                }
            }

            enum_set_type_impl(&input.ident, &all_variants, max_variant, max_variant_ident, attrs).into()
        }
    } else {
        error(input.span(), "`#[derive(BigEnumSetType)]` may only be used on enums")
    }
}
