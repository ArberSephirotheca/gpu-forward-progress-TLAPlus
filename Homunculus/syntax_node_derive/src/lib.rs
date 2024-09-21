extern crate proc_macro;

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

// Procedural macro to automatically implement ResultType
#[proc_macro_derive(ResultType)]
pub fn derive_result_type_trait(input: TokenStream) -> TokenStream {
    // Parse the input token stream into a DeriveInput (which represents a struct, enum, etc.)
    let input = parse_macro_input!(input as DeriveInput);

    // Get the name of the struct we are deriving for
    let name = input.ident;

    // Generate the code to implement Expr for the given struct
    let expanded = quote! {
        impl ResultType for #name {
            fn result_type(&self) -> Option<SyntaxToken> {
                self.0
                    .children_with_tokens()
                    .filter_map(|x| x.into_token())
                    .find(|x| x.kind() == TokenKind::Ident)
            }
        }
    };

    // Convert the generated code into a TokenStream and return it
    TokenStream::from(expanded)
}



// Procedural macro to automatically implement BinaryExpr
#[proc_macro_derive(BinaryExpr)]
pub fn derive_binary_expr_trait(input: TokenStream) -> TokenStream {
    // Parse the input token stream into a DeriveInput (which represents a struct, enum, etc.)
    let input = parse_macro_input!(input as DeriveInput);

    // Get the name of the struct we are deriving for
    let name = input.ident;

    // Generate the code to implement Expr for the given struct
    let expanded = quote! {
        impl BinaryExpr for #name {
            fn first_operand(&self) -> Option<SyntaxToken> {
                self.0
                .children_with_tokens()
                .filter_map(|x| x.into_token())
                .filter(|x| x.kind() == TokenKind::Ident)
                .nth(1)
            }
            fn second_operand(&self) -> Option<SyntaxToken> {
                self.0
                .children_with_tokens()
                .filter_map(|x| x.into_token())
                .filter(|x| x.kind() == TokenKind::Ident)
                .nth(2)
            }
        }
    };

    // Convert the generated code into a TokenStream and return it
    TokenStream::from(expanded)
}
