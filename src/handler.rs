use crate::types::*;
use proc_macro2::*;
use quote::*;
use syn::*;

pub fn handle_structured_map(input: TokenStream) -> Result<TokenStream> {
    // Parse the macro's input into the expected AST.
    let ast = parse2::<StructuredMapAst>(input)?;

    // Generate the type definitions.
    let struct_type_definition = ast.generate_struct_type_definition();
    let key_enum_type_definition = ast.generate_key_enum_type_definition();
    let key_iterator_type_definition =
        ast.generate_key_iterator_type_definition();

    // Generate the implementations.
    let struct_implementation = ast.generate_struct_implementation();
    let key_enum_implementation = ast.generate_key_enum_implementation();
    let key_iterator_implementation =
        ast.generate_key_iterator_implementation();

    // Output the generated code.
    Ok(quote! {
        /* Type definitions */

        // The struct of the structured map.
        #struct_type_definition

        // The enum of the structured map key.
        #key_enum_type_definition

        // The type definition of the structured map key iterator.
        #key_iterator_type_definition

        /* Implementations */
        const _: () = {
            // The implementations of the structured map type.
            #struct_implementation

            // The implementations of the structured map key type.
            #key_enum_implementation

            // The implementations of the structured map key iterator type.
            #key_iterator_implementation
        };
    })
}
