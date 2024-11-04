//! The `structured_map` macro allows users of the macro to generate structured
//! maps with a known and finite set of keys that they can perform map functions
//! on such as `map`, `zip`, `iter` and much more.

mod handler;
mod types;

// TODO(docs)
#[proc_macro]
pub fn structured_map(
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    handler::handle_structured_map(proc_macro2::TokenStream::from(input))
        .unwrap_or_else(|err| err.to_compile_error())
        .into()
}
