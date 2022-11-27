use proc_macro::TokenStream;
use quote::ToTokens;

extern crate proc_macro;

#[proc_macro]
pub fn expr(input: TokenStream) -> TokenStream {
    let expression = syn::parse_macro_input!(input as proof_core::expr::Expression);
    expression.into_token_stream().into()
}
