#![recursion_limit = "256"]

extern crate proc_macro;

use bit_set::BitSet;
use bit_vec::BitBlock;
use darling::*;
use proc_macro2::{Literal, TokenStream};
use quote::*;
use syn::export::Span;
use syn::spanned::Spanned;
use syn::*;
use syn::{Error, Result};

use core::convert::TryFrom;
use core::iter::FromIterator;
use core::{u16, u32, u64, u8};

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
    all_variants: &BitSet<usize>,
    max_variant: usize,
    max_variant_ident: Option<Ident>,
    enum_repr: Option<Ident>,
    attrs: EnumsetAttrs,
) -> TokenStream {
    let is_uninhabited = all_variants.is_empty();
    let is_zst = all_variants.len() == 1;

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
            let min_bytes = max_variant / 8 + 1;
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
        quote!(#max_variant / (::core::mem::size_of::<usize>() * 8) + 1)
    };

    // Compute repr_all seperately like below to allow cross-compiling into an arch with
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
    } else {
        let enum_repr = enum_repr.unwrap();
        quote!(::core::mem::transmute(val as #enum_repr))
    };

    let eq_impl = if is_uninhabited {
        quote!(panic!(concat!(stringify!(#name), " is uninhabited.")))
    } else {
        quote!((*self as u16) == (*other as u16))
    };

    quote! {
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
const MAX_VARIANT: usize = u16::MAX as usize;

fn derive_big_enum_set_type_impl(input: DeriveInput) -> Result<TokenStream> {
    let data = if let Data::Enum(data) = &input.data {
        data
    } else {
        bail!(input.span(), "`#[derive(BigEnumSetType)]` may only be used on enums");
    };

    if !input.generics.params.is_empty() {
        bail!(input.generics.span(), "`#[derive(BigEnumSetType)]` cannot be used on enums with type parameters.");
    }

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
                        Err(_e) => bail!(
                            variant.span(),
                            "Unparseable discriminant for variant (discriminants must be non-negative and fit in `u16`)."
                        ),
                    };
                    has_manual_discriminant = true;
                } else {
                    bail!(variant.span(), "Unrecognized discriminant for variant.");
                }
            }

            if current_variant > MAX_VARIANT {
                if has_manual_discriminant {
                    bail!(variant.span(), "`#[derive(BigEnumSetType)]` only supports enum discriminants up to {}.", MAX_VARIANT);
                } else {
                    bail!(variant.span(), "`#[derive(BigEnumSetType)]` only supports enums up to {} variants.", MAX_VARIANT+1);
                }
            }

            if all_variants.contains(current_variant) {
                bail!(variant.span(), "Duplicate enum discriminant: {}", current_variant);
            }

            all_variants.insert(current_variant);
            if current_variant >= max_variant {
                // use >= because max_variant is initialized to 0.
                max_variant = current_variant;
                max_variant_ident = Some(variant.ident.clone());
            }
            current_variant += 1;
        } else {
            bail!(variant.span(), "`#[derive(BigEnumSetType)]` can only be used on fieldless enums.");
        }
    }

    let attrs: EnumsetAttrs = match EnumsetAttrs::from_derive_input(&input) {
        Ok(attrs) => attrs,
        Err(e) => return Ok(e.write_errors()),
    };

    let mut enum_repr = None;
    for attr in &input.attrs {
        if attr.path.is_ident(&Ident::new("repr", Span::call_site())) {
            let meta: Ident = attr.parse_args()?;
            if enum_repr.is_some() {
                bail!(attr.span(), "Cannot duplicate #[repr(...)] annotations.");
            }
            match meta.to_string().as_str() {
                "Rust" | "C" => (), // We assume default repr in these cases.
                "u8"  | "i8" | "u16" | "i16" | "u32" | "i32" | "u64" | "i64" | "u128" | "i128" | "usize" | "isize" => {
                    enum_repr = Some(meta);
                }
                _ => bail!(attr.span(), "Unsupported repr."),
            }
        }
    }

    if enum_repr.is_none() && all_variants.len() > 1 {
        let repr_str = match max_variant {
            v if v <= usize::from(u8::MAX) => "u8",
            v if v <= usize::from(u16::MAX) => "u16",
            v if v <= usize::try_from(u32::MAX).unwrap_or(usize::MAX) => "u32", // never reached.
            _ => "u64", // never reached.
        };
        enum_repr = Some(Ident::new(repr_str, Span::call_site()));
    }

    if let Some(bytes) = attrs.serialize_bytes {
        if max_variant / 8 >= usize::from(bytes) {
            bail!(input.span(), "Too many variants for serialization into {} bytes.", bytes);
        }
    }

    Ok(enum_set_type_impl(&input.ident, &all_variants, max_variant, max_variant_ident, enum_repr, attrs))
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
