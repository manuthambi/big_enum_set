#![recursion_limit = "256"]

extern crate proc_macro;

use darling::*;
use proc_macro2::{Literal, TokenStream};
use quote::*;
use syn::export::Span;
use syn::spanned::Spanned;
use syn::*;
use syn::{Error, Result};

use core::convert::TryInto;
use core::{u16, u32, u64};
use std::collections::HashSet;

macro_rules! bail {
    ($span:expr, $msg:expr) => {
        return Err(Error::new($span, $msg));
    };
    ($span:expr, $fmt:expr, $($arg:tt)*) => {
        return Err(Error::new($span, format!($fmt, $($arg)*)));
    };
}

fn enum_set_type_impl(
    name: &Ident,
    variants: &Vec<Variant>,
    max_discriminant: u16,
    attrs: EnumsetAttrs
) -> Result<TokenStream> {
    let is_uninhabited = variants.is_empty();
    let is_zst = variants.len() == 1;

    let typed_big_enum_set = quote!(::big_enum_set::BigEnumSet<#name>);

    let ops = if attrs.no_ops {
        quote! {}
    } else {
        let op_trait = &[ quote!(BitOr), quote!(BitAnd), quote!(Sub), quote!(BitXor) ];
        let op_method = &[ quote!(bitor), quote!(bitand), quote!(sub), quote!(bitxor) ];
        let func = &[
            quote!(union_enum),
            quote!(intersection_enum),
            quote!(difference_enum_reverse),
            quote!(symmetrical_difference_enum)
        ];
        quote! {
            #(
                impl ::core::ops::#op_trait<#typed_big_enum_set> for #name {
                    type Output = #typed_big_enum_set;
                    fn #op_method(self, mut other: #typed_big_enum_set) -> Self::Output {
                        ::big_enum_set::__internal::#func(&mut other, self);
                        other
                    }
                }
                impl ::core::ops::#op_trait<&#typed_big_enum_set> for #name {
                    type Output = #typed_big_enum_set;
                    fn #op_method(self, other: &#typed_big_enum_set) -> Self::Output {
                        let mut result = ::core::clone::Clone::clone(other);
                        ::big_enum_set::__internal::#func(&mut result, self);
                        result
                    }
                }
                impl ::core::ops::#op_trait for #name {
                    type Output = #typed_big_enum_set;
                    fn #op_method(self, other: Self) -> Self::Output {
                        let mut result = ::big_enum_set::BigEnumSet::only(other);
                        ::big_enum_set::__internal::#func(&mut result, self);
                        result
                    }
                }
            )*

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
    let serde_ops = {
        let serde = quote!(::big_enum_set::__internal::serde);
        let serde_impl = quote!(::big_enum_set::__internal::serde_impl);

        let (serialize_call, deserialize_call) = if attrs.serialize_as_list {
            (
                quote! { #serde_impl::serialize_as_list(set, ser) },
                quote! { #serde_impl::deserialize_from_list(de) },
            )
        } else {
            let min_bytes = usize::from(max_discriminant) / 8 + 1;
            let serialize_bytes = attrs.serialize_bytes.unwrap_or(min_bytes);
            assert!(min_bytes <= serialize_bytes);
            let check_unknown = attrs.serialize_deny_unknown;

            (
                quote! { #serde_impl::serialize_as_bytes(set, ser, #serialize_bytes) },
                quote! { #serde_impl::deserialize_from_bytes(de, #serialize_bytes, #check_unknown) },
            )
        };

        quote! {
            fn serialize<S>(set: &#typed_big_enum_set, ser: S) -> ::core::result::Result<S::Ok, S::Error>
            where S: #serde::Serializer {
                #serialize_call
            }
            fn deserialize<'de, D>(de: D) -> ::core::result::Result<#typed_big_enum_set, D::Error>
            where D: #serde::Deserializer<'de> {
                #deserialize_call
            }
        }
    };

    #[cfg(not(feature = "serde"))]
    let serde_ops = quote! {};

    let repr_len = if is_uninhabited {
        quote!(0usize)
    } else {
        let max_discriminant = usize::from(max_discriminant);
        quote!(#max_discriminant / (::core::mem::size_of::<usize>() * 8) + 1)
    };
    let repr_all = repr_all(variants, max_discriminant)?;

    let into_impl = if is_uninhabited {
        quote!(panic!(concat!(stringify!(#name), " is uninhabited.")))
    } else {
        quote!(self as u16)
    };

    let from_impl = if is_uninhabited {
        quote!(panic!(concat!(stringify!(#name), " is uninhabited.")))
    } else if is_zst {
        let variant = &variants[0].name;
        quote!(Self::#variant)
    } else {
        #[cfg(not(enum_match))]
        { from_impl_transmute(name) }
        #[cfg(enum_match)]
        { from_impl_match(variants) }
    };

    let eq_impl = if is_uninhabited {
        quote!(panic!(concat!(stringify!(#name), " is uninhabited.")))
    } else {
        quote!((*self as u16) == (*other as u16))
    };

    let result = quote! {
        unsafe impl ::big_enum_set::__internal::BigEnumSetTypePrivate for #name {
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
    };
    Ok(result)
}

fn repr_all(variants: &[Variant], max_discriminant: u16) -> Result<TokenStream> {
    use bit_vec::{BitVec, BitBlock};

    if variants.is_empty() {
        return Ok(quote!([]));
    }

    // Compute repr_all seperately like below to allow cross-compiling into an arch with
    // a different pointer width.
    fn repr_elems<B: BitBlock + Into<u64>>(variants: &[Variant], variant_count: usize) -> Vec<Literal> {
        let mut bits = BitVec::<B>::default();
        bits.grow(variant_count, false);
        for v in variants.iter() {
            bits.set(usize::from(v.discriminant), true);
        }
        bits.blocks().map(|w| Literal::u64_unsuffixed(w.into())).collect()
    }
    let variant_count = match usize::from(max_discriminant).checked_add(1) {
        Some(c) => c,
        None => {
            bail!(
                Span::call_site(),
                "Discriminant overflowed (discriminant cannot be `u16::MAX` when `mem::size_of::<usize>() == 2`)."
            );
        }
    };
    let repr_elems_u16 = repr_elems::<u16>(variants, variant_count);
    let repr_elems_u32 = repr_elems::<u32>(variants, variant_count);
    let repr_elems_u64 = repr_elems::<u64>(variants, variant_count);
    Ok(quote! {{
        #[cfg(target_pointer_width = "16")] { [ #( #repr_elems_u16 ),* ] }
        #[cfg(target_pointer_width = "32")] { [ #( #repr_elems_u32 ),* ] }
        #[cfg(target_pointer_width = "64")] { [ #( #repr_elems_u64 ),* ] }
        #[cfg(not(any(target_pointer_width = "16", target_pointer_width = "32", target_pointer_width = "64")))]
        { core::compile_error!("Invalid target_pointer_width") }
    }})
}

#[allow(dead_code)]
fn from_impl_transmute(name: &Ident) -> TokenStream {
    let const_field = ["IS_U8", "IS_U16", "IS_U32", "IS_U64", "IS_U128"]
        .iter().map(|f| Ident::new(f, Span::call_site())).collect::<Vec<_>>();
    let int_type = ["u8", "u16", "u32", "u64", "u128"]
        .iter().map(|t| Ident::new(t, Span::call_site())).collect::<Vec<_>>();
    quote! {
        // Use const fields so the branches they guard aren't generated even on -O0
        #(const #const_field: bool = ::core::mem::size_of::<#name>() == ::core::mem::size_of::<#int_type>();)*
        match val {
            // Use the right kind of transmute.
            #(x if #const_field => {
                let x = x as #int_type;
                *(&x as *const _ as *const Self)
            })*
            _ => ::core::hint::unreachable_unchecked(),
        }
    }
}

#[allow(dead_code)]
fn from_impl_match(variants: &[Variant]) -> TokenStream {
    let variant_name = variants.iter().map(|v| &v.name).collect::<Vec<_>>();
    let variant_value = variants.iter().map(|v| v.discriminant).collect::<Vec<_>>();
    quote! {
        match val {
            // Every valid variant value has an explicit branch. If they get optimized out,
            // great. If the representation has changed somehow, and they don't, oh well,
            // there's still no UB.
            #(#variant_value => Self::#variant_name,)*
            // Hint to LLVM that this match is effectively a transmute for optimization.
            _ => ::core::hint::unreachable_unchecked(),
        }
    }
}

#[derive(FromDeriveInput, Default)]
#[darling(attributes(big_enum_set), default)]
struct EnumsetAttrs {
    no_ops: bool,
    serialize_as_list: bool,
    serialize_deny_unknown: bool,
    #[darling(default)]
    serialize_bytes: Option<usize>,
}

// We put a limit, to avoid accidentally creating sets which use up large amounts of memory
// if one of the discriminants is large. This has to be <= u16::MAX, because we use u16
// to hold the bit positions in BigEnumSet.
const MAX_DISCRIMINANT: u32 = u16::MAX as u32;

struct Variant {
    name: Ident,
    discriminant: u16,
}

fn derive_big_enum_set_type_impl(input: DeriveInput) -> Result<TokenStream> {
    let data = if let Data::Enum(data) = &input.data {
        data
    } else {
        bail!(input.span(), "`#[derive(BigEnumSetType)]` may only be used on enums");
    };

    if !input.generics.params.is_empty() {
        bail!(input.generics.span(), "`#[derive(BigEnumSetType)]` cannot be used on enums with type parameters.");
    }

    let mut variants = Vec::new();
    let mut current_discriminant = 0_u32; // use u32 instead of u16 to avoid overflow issues.

    let extra_msg = format!("`#[derive(BigEnumSetType)]` only supports discriminants in the range `0 ..= {}`.", MAX_DISCRIMINANT);
    for variant in &data.variants {
        if let Fields::Unit = variant.fields {
            if let Some((_, expr)) = &variant.discriminant {
                if let Expr::Lit(ExprLit { lit: Lit::Int(i), .. }) = expr {
                    current_discriminant = match i.base10_parse::<u16>() {
                        Ok(v) => u32::from(v),
                        Err(_e) => bail!(variant.span(), "Unparseable discriminant. {}", extra_msg),
                    };
                    if current_discriminant > MAX_DISCRIMINANT {
                        bail!(variant.span(), "Discriminant too large. {}", extra_msg);
                    }
                } else {
                    bail!(variant.span(), "Unrecognized discriminant. {}", extra_msg);
                }
            } else if current_discriminant > MAX_DISCRIMINANT {
                bail!(variant.span(), "Discriminant too large. {}", extra_msg);
            }

            variants.push(Variant { name: variant.ident.clone(), discriminant: current_discriminant.try_into().unwrap() });

            current_discriminant += 1;
        } else {
            bail!(variant.span(), "`#[derive(BigEnumSetType)]` may only be used on fieldless enums.");
        }
    }

    validate(&variants)?;
    let max_discriminant = variants.iter().map(|v| v.discriminant).max().unwrap_or(0);

    let attrs: EnumsetAttrs = match EnumsetAttrs::from_derive_input(&input) {
        Ok(attrs) => attrs,
        Err(e) => return Ok(e.write_errors()),
    };

    if let Some(bytes) = attrs.serialize_bytes {
        if usize::from(max_discriminant) / 8 >= bytes {
            bail!(input.span(), "Too many variants for serialization into {} bytes.", bytes);
        }
    }

    enum_set_type_impl(&input.ident, &variants, max_discriminant, attrs)
}

fn validate(variants: &[Variant]) -> Result<()> {
    // These checks are probably not required, because Rust checks them anyways.
    let mut seen_names = HashSet::new();
    let mut seen_discriminants = HashSet::new();
    for v in variants.iter() {
        if !seen_names.insert(v.name.to_string()) {
            bail!(v.name.span(), "Duplicate variant name.");
        }
        if !seen_discriminants.insert(v.discriminant) {
            bail!(v.name.span(), "Duplicate discriminant.");
        }
    }
    Ok(())
}

/// Procedural derive generating `big_enum_set::BigEnumSetType` implementation.
///
/// # Examples
///
/// ```
/// use big_enum_set::BigEnumSetType;
///
/// #[derive(BigEnumSetType)]
/// #[big_enum_set(serialize_bytes=22)]
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
/// * With serde, use `#[big_enum_set(serialize_bytes=N)]` to serialize [`BigEnumSet`]
///   to N bytes, rather than the minimum number of bytes needed to store the bitset.
///   N >= number of variants / 8.
#[proc_macro_derive(BigEnumSetType, attributes(big_enum_set))]
pub fn derive_big_enum_set_type(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input: DeriveInput = parse_macro_input!(input);
    match derive_big_enum_set_type_impl(input) {
        Ok(v) => v.into(),
        Err(e) => e.to_compile_error().into(),
    }
}
