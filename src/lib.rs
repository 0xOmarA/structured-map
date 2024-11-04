use heck::ToPascalCase;
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use syn::{
    bracketed, parse::Parse, parse2, punctuated::Punctuated, token::Bracket,
    AttrStyle, Attribute, Ident, Meta, Result, Token, Visibility,
};

// TODO(docs): Add doc comments for what this macro does.
#[proc_macro]
pub fn structured_map(input: TokenStream) -> TokenStream {
    handle_structured_map(TokenStream2::from(input))
        .unwrap_or_else(|err| err.to_compile_error())
        .into()
}

fn handle_structured_map(input: TokenStream2) -> Result<TokenStream2> {
    // Parse the given input into a StructuredMapInput.
    let StructuredMapInput {
        structure_attributes,
        structure_visibility,
        structure_ident,
        key_set,
        ..
    } = parse2(input)?;
    let key_count = key_set.len();
    let key_set_idents =
        key_set.iter().map(|value| &value.ident).collect::<Vec<_>>();
    let key_set_attributes = key_set
        .iter()
        .map(|value| &value.attributes)
        .collect::<Vec<_>>();

    // Generating the struct
    let structure_definition = quote! {
        #(#structure_attributes)*
        #structure_visibility struct #structure_ident <T> {
            #(
                #(#key_set_attributes)*
                pub #key_set_idents: T,
            )*
        }
    };

    // Generating the keys of the struct - this is used in indexing and the
    // implementation of iterators.
    let structure_key_ident = format_ident!("{}Key", structure_ident);
    let key_set_idents_pascal = key_set_idents
        .iter()
        .map(|ident| {
            Ident::new(
                ident.to_string().to_pascal_case().as_str(),
                ident.span(),
            )
        })
        .collect::<Vec<_>>();
    let key_set_doc_attributes = key_set_attributes
        .iter()
        .map(|value| {
            value
                .iter()
                .filter(|attribute| {
                    let Attribute {
                        style: AttrStyle::Outer,
                        meta: Meta::NameValue(attribute_name_value),
                        ..
                    } = attribute
                    else {
                        return false;
                    };
                    attribute_name_value.path.is_ident("doc")
                })
                .cloned()
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let structure_key = quote! {
        // TODO(docs): Add comments here for what this enum is.
        #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
        #structure_visibility enum #structure_key_ident {
            #(
                #(#key_set_doc_attributes)*
                #key_set_idents_pascal
            ),*
        }
    };

    // Generating the impls for the struct.
    let struct_impl = quote! {
        impl<T> #structure_ident<T> {
            // TODO(docs): Add doc comments.
            pub const fn new(#(#key_set_idents: T),*) -> Self {
                Self {
                    #(#key_set_idents),*
                }
            }

            // TODO(docs): Add doc comments.
            pub fn from_fn(mut callback: impl FnMut() -> T) -> Self {
                Self {
                    #(#key_set_idents: callback()),*
                }
            }

            // TODO(docs): Add doc comments.
            pub fn zip<O>(
                self,
                other: #structure_ident<O>
            ) -> #structure_ident<(T, O)> {
                #structure_ident {
                    #(#key_set_idents: (
                        self.#key_set_idents,
                        other.#key_set_idents
                    )),*
                }
            }

            // TODO(docs): Add doc comments.
            pub fn map<O>(
                self,
                mut callback: impl FnMut(T) -> O
            ) -> #structure_ident<O> {
                #structure_ident {
                    #(#key_set_idents: callback(self.#key_set_idents)),*
                }
            }

            // TODO(docs): Add doc comments.
            pub fn try_map<O, E>(
                self,
                mut callback: impl FnMut(T) -> Result<O, E>
            ) -> Result<#structure_ident<O>, E> {
                Ok(#structure_ident {
                    #(#key_set_idents: callback(self.#key_set_idents)?),*
                })
            }

            // TODO(docs): Add doc comments.
            pub const fn as_ref(&self) -> #structure_ident<&T> {
                #structure_ident {
                    #(#key_set_idents: &self.#key_set_idents),*
                }
            }

            // TODO(docs): Add doc comments.
            pub fn as_mut(&mut self) -> #structure_ident<&mut T> {
                #structure_ident {
                    #(#key_set_idents: &mut self.#key_set_idents),*
                }
            }
        }
    };
    let indexing_impls = quote! {
        impl<T> std::ops::Index<#structure_key_ident> for #structure_ident<T> {
            type Output = T;

            fn index(&self, index: #structure_key_ident) -> &Self::Output {
                match index {
                    #(
                        #structure_key_ident::#key_set_idents_pascal => &self.#key_set_idents
                    ),*
                }
            }
        }

        impl<T> std::ops::IndexMut<#structure_key_ident> for #structure_ident<T> {
            fn index_mut(&mut self, index: #structure_key_ident) -> &mut Self::Output {
                match index {
                    #(
                        #structure_key_ident::#key_set_idents_pascal => &mut self.#key_set_idents
                    ),*
                }
            }
        }
    };
    let iter_impls = quote! {
        impl<T> #structure_ident<T> {
            pub fn iter(&self) -> impl Iterator<Item = &T> {
                [#(#structure_key_ident::#key_set_idents_pascal),*]
                    .into_iter()
                    .map(|key| std::ops::Index::index(self, key))
            }
        }

        impl<T> IntoIterator for #structure_ident<T> {
            type Item = T;
            type IntoIter = <[T; #key_count] as IntoIterator>::IntoIter;

            fn into_iter(self) -> Self::IntoIter {
                [#(self.#key_set_idents),*].into_iter()
            }
        }
    };

    Ok(quote! {
        #structure_definition
        #structure_key

        const _: () = {
            #struct_impl

            #indexing_impls

            #iter_impls
        };
    })
}

/// The syntax and structure of the [`structured_map`] macro inputs. The syntax
/// of the macro looks like the following:
///
/// ```rust,norun
/// structured_map! {
///     StructName => [
///         /// Attributes and doc-comments are supported on keys as well.
///         key1,
///         key2,
///         key3
///     ]
/// }
/// ```
#[expect(dead_code)]
struct StructuredMapInput {
    /// An invocation of the structured map macro can start with any amount of
    /// attributes that are being applied on the structured map ident. These are
    /// copied as is into the generated code.
    pub structure_attributes: Vec<Attribute>,

    /// The visibility of the structure.
    pub structure_visibility: Visibility,

    /// Following the attributes comes the [`Ident`] of the structured map that
    /// the macro should define. This will be used as the [`Ident`] of the
    /// generated struct.
    pub structure_ident: Ident,

    /// Following the [`Ident`] of the struct is an arrow before the caller is
    /// expected to provide the set of keys of the map.
    pub arrow: (Token![=], Token![>]),

    /// A bracket that starts the set of keys in the map.
    pub brace: Bracket,

    /// A comma separated list of keys that represents the key set of the
    /// structured map.
    pub key_set: Punctuated<StructuredMapKeyInput, Token![,]>,
}

impl Parse for StructuredMapInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let content;
        Ok(Self {
            structure_attributes: input.call(Attribute::parse_outer)?,
            structure_visibility: input.parse()?,
            structure_ident: input.parse()?,
            arrow: (input.parse()?, input.parse()?),
            brace: bracketed!(content in input),
            key_set: content
                .parse_terminated(StructuredMapKeyInput::parse, Token![,])?,
        })
    }
}

/// Represents the allowed syntax of the keys the caller specifies when calling
/// the macro.
#[derive(Clone)]
struct StructuredMapKeyInput {
    /// A vector of [`Attribute`]s applied to the key. This will be applied to
    /// the corresponding field of that key in the generated struct.
    pub attributes: Vec<Attribute>,

    /// An [`Ident`] used to identify the key. This will be the [`Ident`] used
    /// for the field of the struct.
    pub ident: Ident,
}

impl Parse for StructuredMapKeyInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(Self {
            attributes: input.call(Attribute::parse_outer)?,
            ident: input.parse()?,
        })
    }
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use proc_macro2::*;
    use quote::quote;

    #[test]
    fn macro_generates_expected_struct() {
        // Arrange
        let input = r#"
            #[derive(Example, Serialize, Deserialize)]
            #[doc="Doc on the struct"]
            pub(crate) MyStruct => [
                #[serde(flatten)]
                // Doc on key1,
                key1,
                #[serde(flatten)]
                // Doc on key2,
                key2,
                #[serde(flatten, rename = "key15")]
                // Doc on key3,
                key3
            ]
        "#;

        // Act
        let output =
            super::handle_structured_map(TokenStream::from_str(input).unwrap())
                .unwrap();

        // Assert
        let expected_output = quote! {
            #[derive(Example, Serialize, Deserialize)]
            #[doc="Doc on the struct"]
            pub(crate) struct MyStruct<T> {
                #[serde(flatten)]
                // Doc on key1,
                pub key1: T,
                #[serde(flatten)]
                // Doc on key2,
                pub key2: T,
                #[serde(flatten, rename = "key15")]
                // Doc on key3,
                pub key3: T,
            }
        };
        assert!(output
            .to_string()
            .contains(expected_output.to_string().as_str()))
    }
}
