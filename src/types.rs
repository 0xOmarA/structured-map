use heck::*;
use indoc::*;
use proc_macro2::*;
use quote::*;
use syn::parse::*;
use syn::punctuated::*;
use syn::token::*;
use syn::*;

/// The AST definition of the input into the [`structured_map`] macro which
/// allows the macro to be invoked with the following syntax.
///
/// ```rust,no_run,ignore
/// structured_map! {
///     /// Any number of attributes are allowed + the ident accepts a viability
///     /// for the generated struct.
///     #[derive(Serialize, Deserialize)]
///     pub(crate) StructName => [
///         /// Attributes and doc-comments are supported on keys as well.
///         #[serde(rename = "id")]
///         key1,
///         key2,
///         key3
///     ]
/// }
/// ```
///
/// [`structured_map`]: crate::structured_map
#[expect(dead_code)]
pub struct StructuredMapAst {
    /// An invocation of the structured map macro can start with any number of
    /// attributes before the [`Ident`] of the structured and they will be
    /// applied to the generated structured map.
    pub structure_attributes: Vec<Attribute>,

    /// The visibility to apply to the generated structured map struct.
    pub structure_visibility: Visibility,

    /// Following the attributes comes the [`Ident`] of the structured map that
    /// which will be carried over in the generated code as the [`Ident`] of the
    /// generated structure and will also be used for the Key type generated for
    /// indexing the map.
    pub structure_ident: Ident,

    /// Following the [`Ident`] of the struct is an arrow before the caller is
    /// expected to provide the set of keys of the map.
    pub arrow: (Token![=], Token![>]),

    /// A bracket that starts the set of keys in the map.
    pub brace: Bracket,

    /// A comma separated list of keys that represents the key set of the
    /// structured map.
    pub key_set: Punctuated<StructuredMapKeyAst, Token![,]>,
}

impl Parse for StructuredMapAst {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let content;
        let this = Self {
            structure_attributes: input.call(Attribute::parse_outer)?,
            structure_visibility: input.parse()?,
            structure_ident: input.parse()?,
            arrow: (input.parse()?, input.parse()?),
            brace: bracketed!(content in input),
            key_set: content
                .parse_terminated(StructuredMapKeyAst::parse, Token![,])?,
        };

        // A structured map with no keys is not a valid structured map and it is
        // not easy to deal with it. Therefore, we disallow the generation if we
        // find no keys were provided we error out. We error out during parsing
        // as this could be viewed as a validation error that is enforced in a
        // way such that no `StructuredMapAst` can be created unless there's at
        // least one key.
        if this.key_set.is_empty() {
            return Err(Error::new(
                this.brace.span.join(),
                "A structured map can't be created if it has no keys",
            ));
        }

        Ok(this)
    }
}

impl StructuredMapAst {
    /// Returns the length of the set of keys that this named struct has.
    pub fn keys_count(&self) -> usize {
        self.key_set.len()
    }

    /// Returns the [`Ident`] of the Key type generated for the structured map.
    /// This is a simple concatenation of the [`Ident`] provided by the caller
    /// for the structured map with `Key` at the end.
    pub fn key_type_ident(&self) -> Ident {
        format_ident!("{}Key", self.structure_ident)
    }

    /// Returns the [`Ident`] of a type that is used to implement iterators for
    /// the structured map. This is a concatenation of the `key_type_ident` and
    /// `Iterator` at the end.
    pub fn key_iterator_type_ident(&self) -> Ident {
        format_ident!("{}Iterator", self.key_type_ident())
    }

    /// Returns an [`Iterator`] of the key [`Ident`]s
    pub fn key_idents(&self) -> impl Iterator<Item = &Ident> {
        self.key_set.iter().map(|key| &key.ident)
    }

    /// Returns an [`Iterator`] of the pascal case key [`Ident`]s
    pub fn key_pascal_case_idents(&self) -> impl Iterator<Item = Ident> + '_ {
        self.key_set.iter().map(|key| {
            Ident::new(
                &key.ident.to_string().to_pascal_case(),
                key.ident.span(),
            )
        })
    }

    /// Returns an [`Iterator`] of the key [`Attribute`]s
    pub fn key_attributes(&self) -> impl Iterator<Item = &Vec<Attribute>> {
        self.key_set.iter().map(|key| &key.attributes)
    }

    /// Returns an [`Iterator`] of the key [`Attribute`]s that are doc comments.
    pub fn key_doc_comment_attributes(
        &self,
    ) -> impl Iterator<Item = impl Iterator<Item = &Attribute>> {
        self.key_set
            .iter()
            .map(|item| item.doc_comment_attributes())
    }

    /* Generation */

    /// Generates the struct definition of the structured map.
    pub fn generate_struct_type_definition(&self) -> TokenStream {
        let struct_visibility = &self.structure_visibility;
        let struct_ident = &self.structure_ident;
        let struct_attributes = &self.structure_attributes;
        let key_idents = self.key_idents();
        let key_attributes = self.key_attributes();

        quote! {
            #(#struct_attributes)*
            #struct_visibility struct #struct_ident<T> {
                #(
                    #(#key_attributes)*
                    #key_idents: T
                ),*
            }
        }
    }

    /// Generates the enum that is used to key the structured map dynamically
    /// at runtime.
    pub fn generate_key_enum_type_definition(&self) -> TokenStream {
        let struct_visibility = &self.structure_visibility;
        let struct_ident = &self.structure_ident;
        let key_type_ident = self.key_type_ident();
        let key_pascal_case_idents = self.key_pascal_case_idents();
        let key_doc_comment_attributes = self
            .key_doc_comment_attributes()
            .map(|item| item.collect())
            .collect::<Vec<Vec<_>>>();

        let doc_comment = formatdoc!(
            "
            An enum that is used to key the [`{0}`] structured map at runtime.

            This enum is used in the implementation of the [`Index`] and the
            [`IndexMut`] trait as the key which means that values in the [`{0}`]
            struct can be obtained through `{0}[{1}::SomeKey]` which returns
            `T`. The indexing is guaranteed to succeed and there should never 
            be errors relating to a key not having an associated value since 
            all of the struct fields are guaranteed to be initialized.

            This enum contains all of the keys that were provided in the macro
            invocation in pascal-case. So, if `key1` was provided as a key then
            it will be present in this macro as a variant of `Key1`.

            [`Index`]: ::core::ops::Index
            [`IndexMut`]: ::core::ops::IndexMut
            ",
            struct_ident.to_string(),
            key_type_ident.to_string()
        );
        quote! {
            #[doc = #doc_comment]
            #[allow(dead_code)]
            #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
            #struct_visibility enum #key_type_ident {
                #(
                    #(#key_doc_comment_attributes)*
                    #key_pascal_case_idents
                ),*
            }
        }
    }

    /// Generates a type used in iterating over the key enum.
    pub fn generate_key_iterator_type_definition(&self) -> TokenStream {
        let key_type_ident = self.key_type_ident();
        let key_iterator_type_ident = self.key_iterator_type_ident();
        let struct_visibility = &self.structure_visibility;

        let doc_string = formatdoc!(
            "
            A type that implements the iteration logic for [`{}`] and the
            required traits.
            ",
            key_type_ident.to_string()
        );

        quote! {
            #[doc = #doc_string]
            #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
            #struct_visibility struct #key_iterator_type_ident {
                /// The current value of the key.
                current_value: Option<#key_type_ident>,
                /// Specifies whether the iterator has completed iteration or
                /// not. Defaults to [`false`] if an iterator is created through
                /// the [`Default::default`] function.
                is_finished: bool
            }
        }
    }

    /// Generates the implementation of the structured map type.
    pub fn generate_struct_implementation(&self) -> TokenStream {
        let struct_method_implementation =
            self.generate_struct_method_implementation();
        let struct_iter_implementation =
            self.generate_struct_iter_implementation();
        let struct_index_implementation =
            self.generate_struct_index_implementation();

        quote! {
            #struct_method_implementation
            #struct_iter_implementation
            #struct_index_implementation
        }
    }

    /// Generates the main `impl` block of the structured map.
    pub fn generate_struct_method_implementation(&self) -> TokenStream {
        let structure_ident = &self.structure_ident;
        let key_idents = self.key_idents().collect::<Vec<_>>();
        let key_pascal_case_idents =
            self.key_pascal_case_idents().collect::<Vec<_>>();
        let key_type_ident = self.key_type_ident();

        quote! {
            impl<T> #structure_ident<T> {
                /// Instantiates the type from the given values.
                pub const fn new(#(#key_idents: T),*) -> Self {
                    Self{ #(#key_idents),* }
                }

                /// Instantiates the type from a function that takes the key.
                pub fn from_fn(
                    mut func: impl FnMut(#key_type_ident) -> T
                ) -> Self {
                    Self {
                        #(
                            #key_idents:
                                func(#key_type_ident::#key_pascal_case_idents)
                        ),*
                    }
                }

                /// Instantiates the type from a function that takes the key and
                /// that can potentially fail.
                pub fn try_from_fn<E>(
                    mut func: impl FnMut(#key_type_ident) -> Result<T, E>
                ) -> Result<Self, E> {
                    Ok(Self {
                        #(
                            #key_idents:
                                func(#key_type_ident::#key_pascal_case_idents)?
                        ),*
                    })
                }

                /// Maps all items of type `T` to type `O`.
                pub fn map<O>(
                    self,
                    mut func: impl FnMut(T) -> O
                ) -> #structure_ident<O> {
                    #structure_ident {
                        #(
                            #key_idents: func(self.#key_idents)
                        ),*
                    }
                }

                /// Maps all items of type `T` to type `O` fallibly.
                pub fn try_map<O, E>(
                    self,
                    mut func: impl FnMut(T) -> Result<O, E>
                ) -> Result<#structure_ident<O>, E> {
                    Ok(#structure_ident {
                        #(
                            #key_idents: func(self.#key_idents)?
                        ),*
                    })
                }

                /// Zips the structure with another one.
                pub fn zip<O>(
                    self,
                    other: #structure_ident<O>
                ) -> #structure_ident<(T, O)> {
                    #structure_ident {
                        #(
                            #key_idents: (self.#key_idents, other.#key_idents)
                        ),*
                    }
                }

                /// Attempts to construct the structured map from an iterator
                /// over a two tuple where the first item could be converted
                /// into a key and the second value is the value.
                pub fn try_from_iterator<I, K>(into_iter: I) -> Option<Self>
                where
                    K: TryInto<#key_type_ident>,
                    I: IntoIterator<Item = (K, T)>,
                {
                    let mut structure = #structure_ident::from_fn(|_| None::<T>);

                    for (maybe_key, value) in into_iter.into_iter() {
                        let key = maybe_key.try_into().ok()?;
                        match ::core::ops::IndexMut::index_mut(&mut structure, key)
                        {
                            // Item already exists - the iterator contains dupes
                            // so we fail.
                            Some(value) => return None,
                            // No a dupe - set the value.
                            mut_ref @ None => {
                                *mut_ref = Some(value)
                            }
                        }
                    }

                    structure.try_map(|value| value.ok_or(())).ok()
                }

                /// Creates a structure over &T
                pub fn as_ref(&self) -> #structure_ident<&T> {
                    #structure_ident {
                        #(
                            #key_idents: &self.#key_idents
                        ),*
                    }
                }

                /// Creates a structure over &mut T
                pub fn as_mut(&mut self) -> #structure_ident<&mut T> {
                    #structure_ident {
                        #(
                            #key_idents: &mut self.#key_idents
                        ),*
                    }
                }
            }
        }
    }

    /// Generates the iteration implementation for the struct type.
    pub fn generate_struct_iter_implementation(&self) -> TokenStream {
        let structure_ident = &self.structure_ident;
        let key_iterator_type_ident = self.key_iterator_type_ident();
        let key_idents = self.key_idents().collect::<Vec<_>>();
        let keys_count = self.keys_count();

        quote! {
            impl<T> IntoIterator for #structure_ident<T> {
                type Item = T;
                type IntoIter = <[T; #keys_count] as ::core::iter::IntoIterator>::IntoIter;

                fn into_iter(self) -> Self::IntoIter {
                    ::core::iter::IntoIterator::into_iter([
                        #(
                            self.#key_idents
                        ),*
                    ])
                }
            }

            impl<T> #structure_ident<T> {
                /// Returns an iterator over &T
                pub fn iter(&self) -> impl ::core::iter::Iterator<Item = &T> {
                    #key_iterator_type_ident::new()
                        .map(|key| ::core::ops::Index::index(self, key))
                }
            }
        }
    }

    /// Generates the implementation of [`Index`] and [`IndexMut`] traits for
    /// the struct types.
    ///
    /// [`Index`]: ::core::ops::Index
    /// [`IndexMut`]: ::core::ops::IndexMut
    pub fn generate_struct_index_implementation(&self) -> TokenStream {
        let structure_ident = &self.structure_ident;
        let key_type_ident = self.key_type_ident();
        let key_idents = self.key_idents().collect::<Vec<_>>();
        let key_pascal_case_idents =
            self.key_pascal_case_idents().collect::<Vec<_>>();

        quote! {
            impl<T> ::core::ops::Index<#key_type_ident> for #structure_ident<T> {
                type Output = T;

                fn index(&self, index: #key_type_ident) -> &Self::Output {
                    match index {
                        #(#key_type_ident::#key_pascal_case_idents => &self.#key_idents),*
                    }
                }
            }

            impl<T> ::core::ops::IndexMut<#key_type_ident> for #structure_ident<T> {
                fn index_mut(&mut self, index: #key_type_ident) -> &mut Self::Output {
                    match index {
                        #(#key_type_ident::#key_pascal_case_idents => &mut self.#key_idents),*
                    }
                }
            }
        }
    }

    /// Generates the implementation of the structured map key type.
    pub fn generate_key_enum_implementation(&self) -> TokenStream {
        let key_enum_str_implementation =
            self.generate_key_enum_str_implementation();
        let key_enum_next_implementation =
            self.generate_key_enum_next_implementation();
        let key_enum_iterator_implementation =
            self.generate_key_enum_iterator_implementation();

        quote! {
            #key_enum_str_implementation
            #key_enum_next_implementation
            #key_enum_iterator_implementation
        }
    }

    /// Generates the implementation of the [`FromStr`] and [`Display`] trait
    /// implementations for the key enum type.
    ///
    /// [`FromStr`]: ::core::str::FromStr
    /// [`Display`]: ::core::fmt::Display
    pub fn generate_key_enum_str_implementation(&self) -> TokenStream {
        let key_type_ident = self.key_type_ident();
        let key_pascal_case_idents =
            &self.key_pascal_case_idents().collect::<Vec<_>>();
        let key_idents = &self
            .key_idents()
            .map(|ident| ident.to_string())
            .collect::<Vec<_>>();

        quote! {
            impl ::core::str::FromStr for #key_type_ident {
                type Err = ();

                fn from_str(s: &str) -> Result<Self, Self::Err> {
                    match s {
                        #(#key_idents => Ok(Self::#key_pascal_case_idents),)*
                        _ => Err(())
                    }
                }
            }

            impl ::core::fmt::Display for #key_type_ident {
                fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                    let s = match self {
                        #(Self::#key_pascal_case_idents => #key_idents),*
                    };
                    write!(f, "{s}")
                }
            }
        }
    }

    /// Generates an implementation of `next` methods for the key enum.
    pub fn generate_key_enum_next_implementation(&self) -> TokenStream {
        let key_type_ident = self.key_type_ident();
        let key_pascal_case_idents =
            &self.key_pascal_case_idents().collect::<Vec<_>>();

        // INVARIANT(zero-keys-disallowed): This bit of the code can fail if the
        // invariant that zero-keys is disallowed fails since the sliding window
        // will panic if keys are zero and the first and last impl will also
        // panic in that case too.
        let first_key_pascal_case_ident = key_pascal_case_idents
            .first()
            .expect("INVARIANT(zero-keys-disallowed)");
        let last_key_pascal_case_ident = key_pascal_case_idents
            .last()
            .expect("INVARIANT(zero-keys-disallowed)");
        let (sliding_window_left, sliding_window_right) =
            key_pascal_case_idents
                .windows(2)
                .map(|window| (&window[0], &window[1]))
                .unzip::<_, _, Vec<&Ident>, Vec<&Ident>>();

        quote! {
            impl #key_type_ident {
                pub const FIRST_KEY: Self = Self::#first_key_pascal_case_ident;
                pub const LAST_KEY: Self = Self::#last_key_pascal_case_ident;

                /// This method returns the next key based on the current key.
                pub fn next(&self) -> Option<Self> {
                    match self {
                        #(
                            Self::#sliding_window_left =>
                            Some(Self::#sliding_window_right),
                        )*
                        // For the last key we return None, there's no next key.
                        &Self::LAST_KEY => None
                    }
                }

                /// This method returns the next key based on an optionally
                /// provided current key.
                pub fn next_on_option(maybe_current_key: Option<&Self>) -> Option<Self> {
                    match maybe_current_key {
                        Some(key) => key.next(),
                        // If the key was None then the next key is the first
                        // key.
                        None => Some(Self::FIRST_KEY)
                    }
                }
            }
        }
    }

    /// Generates the required iterator implementation for the key enum type.
    pub fn generate_key_enum_iterator_implementation(&self) -> TokenStream {
        let key_type_ident = self.key_type_ident();
        let key_iterator_type_ident = self.key_iterator_type_ident();

        quote! {
            impl ::core::iter::IntoIterator for #key_type_ident {
                type Item = Self;
                type IntoIter = #key_iterator_type_ident;

                fn into_iter(self) -> Self::IntoIter {
                    #key_iterator_type_ident {
                        current_value: Some(self),
                        is_finished: false,
                    }
                }
            }
        }
    }

    /// Generates the implementation of the key iterator type.
    pub fn generate_key_iterator_implementation(&self) -> TokenStream {
        let key_type_ident = self.key_type_ident();
        let key_iterator_type_ident = self.key_iterator_type_ident();

        quote! {
            impl #key_iterator_type_ident {
                /// Creates a new iterator starting from the first key.
                pub fn new() -> Self {
                    ::core::default::Default::default()
                }
            }

            impl ::core::default::Default for #key_iterator_type_ident {
                fn default() -> Self {
                    Self {
                        current_value: Some(#key_type_ident::FIRST_KEY),
                        is_finished: false,
                    }
                }
            }

            impl ::core::iter::Iterator for #key_iterator_type_ident {
                type Item = #key_type_ident;

                fn next(&mut self) -> Option<Self::Item> {
                    if self.is_finished {
                        return None;
                    }
                    let previous_value = self.current_value;
                    self.current_value = #key_type_ident::next_on_option(
                        self.current_value.as_ref()
                    );
                    if self.current_value.is_none() {
                        self.is_finished = true;
                    }
                    previous_value
                }
            }
        }
    }
}

/// Represents the allowed syntax of the keys the caller specifies when calling
/// the macro.
#[derive(Clone)]
pub struct StructuredMapKeyAst {
    /// A vector of [`Attribute`]s applied to the key. This will be applied to
    /// the corresponding field of that key in the generated struct. The doc
    /// comments from here will be carried over to all places including the
    /// generated Key enum.
    pub attributes: Vec<Attribute>,

    /// An [`Ident`] used to identify the key. This will be the [`Ident`] used
    /// for the field of the struct.
    pub ident: Ident,
}

impl Parse for StructuredMapKeyAst {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(Self {
            attributes: input.call(Attribute::parse_outer)?,
            ident: input.parse()?,
        })
    }
}

impl StructuredMapKeyAst {
    /// Filters for the doc comments applied to the key.
    pub fn doc_comment_attributes(&self) -> impl Iterator<Item = &Attribute> {
        filter_for_doc_comment_attributes(self.attributes.iter())
    }
}

fn filter_for_doc_comment_attributes<'a>(
    attributes: impl Iterator<Item = &'a Attribute>,
) -> impl Iterator<Item = &'a Attribute> {
    attributes.filter(|attribute| {
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
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn with_no_keys_fails_parsing() {
        // Arrange
        let input = quote!(MyStruct => []);

        // Act
        let result = parse2::<StructuredMapAst>(input);

        // Assert
        assert!(result.is_err_and(|error| {
            error
                .to_string()
                .contains("A structured map can't be created if it has no keys")
        }));
    }

    #[test]
    fn struct_generation_generates_expected_code() {
        // Arrange
        let input: StructuredMapAst = parse_quote! {
            /// Some documentation on the struct itself.
            #[derive(Serialize, Deserialize)]
            pub(crate) MyStruct => [
                /// Some docs on the first key.
                #[serde(rename = "key")]
                key1,
                /// Docs for the second key.
                key2,
                // A comment on the third key.
                key3
            ]
        };
        let expected_output = quote! {
            /// Some documentation on the struct itself.
            #[derive(Serialize, Deserialize)]
            pub(crate) struct MyStruct<T> {
                /// Some docs on the first key.
                #[serde(rename = "key")]
                key1: T,
                /// Docs for the second key.
                key2: T,
                // A comment on the third key.
                key3: T
            }
        };

        // Act
        let output = input.generate_struct_type_definition();

        // Assert
        assert_eq!(output.to_string(), expected_output.to_string());
    }

    #[test]
    fn key_enum_generation_generates_expected_code() {
        // Arrange
        let input: StructuredMapAst = parse_quote! {
            /// Some documentation on the struct itself.
            #[derive(Serialize, Deserialize)]
            pub(crate) MyStruct => [
                /// Some docs on the first key.
                #[serde(rename = "key")]
                key1,
                /// Docs for the second key.
                key2,
                // A comment on the third key.
                key3
            ]
        };
        let expected_doc_comment = indoc!(
            "
            An enum that is used to key the [`MyStruct`] structured map at runtime.

            This enum is used in the implementation of the [`Index`] and the
            [`IndexMut`] trait as the key which means that values in the [`MyStruct`]
            struct can be obtained through `MyStruct[MyStructKey::SomeKey]` which returns
            `T`. The indexing is guaranteed to succeed and there should never 
            be errors relating to a key not having an associated value since 
            all of the struct fields are guaranteed to be initialized.

            This enum contains all of the keys that were provided in the macro
            invocation in pascal-case. So, if `key1` was provided as a key then
            it will be present in this macro as a variant of `Key1`.

            [`Index`]: ::core::ops::Index
            [`IndexMut`]: ::core::ops::IndexMut
            "
        );
        let expected_output = quote! {
            #[doc = #expected_doc_comment]
            #[allow(dead_code)]
            #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
            pub(crate) enum MyStructKey {
                /// Some docs on the first key.
                Key1,
                /// Docs for the second key.
                Key2,
                // A comment on the third key.
                Key3
            }
        };

        // Act
        let output = input.generate_key_enum_type_definition();

        // Assert
        assert_eq!(output.to_string(), expected_output.to_string());
    }

    #[test]
    fn struct_iter_impl_generation_generates_expected_code() {
        // Arrange
        let input: StructuredMapAst = parse_quote! {
            /// Some documentation on the struct itself.
            #[derive(Serialize, Deserialize)]
            pub(crate) MyStruct => [
                /// Some docs on the first key.
                #[serde(rename = "key")]
                key1,
                /// Docs for the second key.
                key2,
                // A comment on the third key.
                key3
            ]
        };
        let expected_output = quote! {
            impl<T> IntoIterator for MyStruct<T> {
                type Item = T;
                type IntoIter = <[T; 3usize] as ::core::iter::IntoIterator>::IntoIter;

                fn into_iter(self) -> Self::IntoIter {
                    ::core::iter::IntoIterator::into_iter([
                        self.key1,
                        self.key2,
                        self.key3
                    ])
                }
            }

            impl<T> MyStruct<T> {
                /// Returns an iterator over &T
                pub fn iter(&self) -> impl ::core::iter::Iterator<Item = &T> {
                    MyStructKeyIterator::new()
                        .map(|key| ::core::ops::Index::index(self, key))
                }
            }
        };

        // Act
        let output = input.generate_struct_iter_implementation();

        // Assert
        assert_eq!(output.to_string(), expected_output.to_string());
    }

    #[test]
    fn struct_index_impl_generation_generates_expected_code() {
        // Arrange
        let input: StructuredMapAst = parse_quote! {
            /// Some documentation on the struct itself.
            #[derive(Serialize, Deserialize)]
            pub(crate) MyStruct => [
                /// Some docs on the first key.
                #[serde(rename = "key")]
                key1,
                /// Docs for the second key.
                key2,
                // A comment on the third key.
                key3
            ]
        };
        let expected_output = quote! {
            impl<T> ::core::ops::Index<MyStructKey> for MyStruct<T> {
                type Output = T;

                fn index(&self, index: MyStructKey) -> &Self::Output {
                    match index {
                        MyStructKey::Key1 => &self.key1,
                        MyStructKey::Key2 => &self.key2,
                        MyStructKey::Key3 => &self.key3
                    }
                }
            }

            impl<T> ::core::ops::IndexMut<MyStructKey> for MyStruct<T> {
                fn index_mut(&mut self, index: MyStructKey) -> &mut Self::Output {
                    match index {
                        MyStructKey::Key1 => &mut self.key1,
                        MyStructKey::Key2 => &mut self.key2,
                        MyStructKey::Key3 => &mut self.key3
                    }
                }
            }
        };

        // Act
        let output = input.generate_struct_index_implementation();

        // Assert
        assert_eq!(output.to_string(), expected_output.to_string());
    }

    #[test]
    fn key_enum_str_impl_generation_generates_expected_code() {
        // Arrange
        let input: StructuredMapAst = parse_quote! {
            /// Some documentation on the struct itself.
            #[derive(Serialize, Deserialize)]
            pub(crate) MyStruct => [
                /// Some docs on the first key.
                #[serde(rename = "key")]
                key1,
                /// Docs for the second key.
                key2,
                // A comment on the third key.
                key3
            ]
        };
        let expected_output = quote! {
            impl ::core::str::FromStr for MyStructKey {
                type Err = ();

                fn from_str(s: &str) -> Result<Self, Self::Err> {
                    match s {
                        "key1" => Ok(Self::Key1),
                        "key2" => Ok(Self::Key2),
                        "key3" => Ok(Self::Key3),
                        _ => Err(())
                    }
                }
            }

            impl ::core::fmt::Display for MyStructKey {
                fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                    let s = match self {
                        Self::Key1 => "key1",
                        Self::Key2 => "key2",
                        Self::Key3 => "key3"
                    };
                    write!(f, "{s}")
                }
            }
        };

        // Act
        let output = input.generate_key_enum_str_implementation();

        // Assert
        assert_eq!(output.to_string(), expected_output.to_string());
    }

    #[test]
    fn key_enum_next_impl_generation_generates_expected_code() {
        // Arrange
        let input: StructuredMapAst = parse_quote! {
            /// Some documentation on the struct itself.
            #[derive(Serialize, Deserialize)]
            pub(crate) MyStruct => [
                /// Some docs on the first key.
                #[serde(rename = "key")]
                key1,
                /// Docs for the second key.
                key2,
                // A comment on the third key.
                key3
            ]
        };
        let expected_output = quote! {
            impl MyStructKey {
                pub const FIRST_KEY: Self = Self::Key1;
                pub const LAST_KEY: Self = Self::Key3;

                /// This method returns the next key based on the current key.
                pub fn next(&self) -> Option<Self> {
                    match self {
                        Self::Key1 => Some(Self::Key2),
                        Self::Key2 => Some(Self::Key3),
                        // For the last key we return None, there's no next key.
                        &Self::LAST_KEY => None
                    }
                }

                /// This method returns the next key based on an optionally
                /// provided current key.
                pub fn next_on_option(maybe_current_key: Option<&Self>) -> Option<Self> {
                    match maybe_current_key {
                        Some(key) => key.next(),
                        // If the key was None then the next key is the first
                        // key.
                        None => Some(Self::FIRST_KEY)
                    }
                }
            }
        };

        // Act
        let output = input.generate_key_enum_next_implementation();

        // Assert
        assert_eq!(output.to_string(), expected_output.to_string());
    }

    #[test]
    fn key_enum_iter_impl_generation_generates_expected_code() {
        // Arrange
        let input: StructuredMapAst = parse_quote! {
            /// Some documentation on the struct itself.
            #[derive(Serialize, Deserialize)]
            pub(crate) MyStruct => [
                /// Some docs on the first key.
                #[serde(rename = "key")]
                key1,
                /// Docs for the second key.
                key2,
                // A comment on the third key.
                key3
            ]
        };
        let expected_output = quote! {
            impl ::core::iter::IntoIterator for MyStructKey {
                type Item = Self;
                type IntoIter = MyStructKeyIterator;

                fn into_iter(self) -> Self::IntoIter {
                    MyStructKeyIterator {
                        current_value: Some(self),
                        is_finished: false,
                    }
                }
            }
        };

        // Act
        let output = input.generate_key_enum_iterator_implementation();

        // Assert
        assert_eq!(output.to_string(), expected_output.to_string());
    }

    #[test]
    fn key_enum_iterator_impl_generation_generates_expected_code() {
        // Arrange
        let input: StructuredMapAst = parse_quote! {
            /// Some documentation on the struct itself.
            #[derive(Serialize, Deserialize)]
            pub(crate) MyStruct => [
                /// Some docs on the first key.
                #[serde(rename = "key")]
                key1,
                /// Docs for the second key.
                key2,
                // A comment on the third key.
                key3
            ]
        };
        let expected_doc_comment = indoc!(
            "
            A type that implements the iteration logic for [`MyStructKey`] and the
            required traits.
            "
        );
        let expected_output = quote! {
            #[doc = #expected_doc_comment]
            #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
            pub(crate) struct MyStructKeyIterator {
                /// The current value of the key.
                current_value: Option<MyStructKey>,
                /// Specifies whether the iterator has completed iteration or
                /// not. Defaults to [`false`] if an iterator is created through
                /// the [`Default::default`] function.
                is_finished: bool
            }
        };

        // Act
        let output = input.generate_key_iterator_type_definition();

        // Assert
        assert_eq!(output.to_string(), expected_output.to_string());
    }

    #[test]
    fn key_iterator_impl_generation_generates_expected_code() {
        // Arrange
        let input: StructuredMapAst = parse_quote! {
            /// Some documentation on the struct itself.
            #[derive(Serialize, Deserialize)]
            pub(crate) MyStruct => [
                /// Some docs on the first key.
                #[serde(rename = "key")]
                key1,
                /// Docs for the second key.
                key2,
                // A comment on the third key.
                key3
            ]
        };
        let expected_output = quote! {
            impl MyStructKeyIterator {
                /// Creates a new iterator starting from the first key.
                pub fn new() -> Self {
                    ::core::default::Default::default()
                }
            }

            impl ::core::default::Default for MyStructKeyIterator {
                fn default() -> Self {
                    Self {
                        current_value: Some(MyStructKey::FIRST_KEY),
                        is_finished: false,
                    }
                }
            }

            impl ::core::iter::Iterator for MyStructKeyIterator {
                type Item = MyStructKey;

                fn next(&mut self) -> Option<Self::Item> {
                    if self.is_finished {
                        return None;
                    }
                    let previous_value = self.current_value;
                    self.current_value = MyStructKey::next_on_option(
                        self.current_value.as_ref()
                    );
                    if self.current_value.is_none() {
                        self.is_finished = true;
                    }
                    previous_value
                }
            }
        };

        // Act
        let output = input.generate_key_iterator_implementation();

        // Assert
        assert_eq!(output.to_string(), expected_output.to_string());
    }
}
