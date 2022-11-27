use quote::ToTokens;
use syn::{
    ext::IdentExt,
    parse::{Parse, ParseStream},
    Ident,
};

use crate::expr::{Expression, Variable};

fn get_binder_type_by_ident(ident: &Ident) -> Option<crate::expr::BinderType> {
    match ident.to_string().as_str() {
        "fun" => Some(crate::expr::BinderType::Abstraction),
        "for" => Some(crate::expr::BinderType::Product),
        _ => None,
    }
}

fn parse_binder(input: ParseStream) -> syn::Result<Expression> {
    let lookahead = input.fork();
    if !input.peek(Ident::peek_any) {
        Err(input.error("expected identifier"))
    } else {
        let binder_type = get_binder_type_by_ident(&lookahead.parse::<Ident>()?)
            .ok_or_else(|| input.error("expected binder type"))?;
        let variable = Variable::new(lookahead.parse::<Ident>()?.to_string().as_str());
        lookahead.parse::<syn::Token![:]>()?;
        let expression_type = input.parse::<Expression>()?;
        input.parse::<syn::Token![.]>()?;
        let expression_body = input.parse::<Expression>()?;
        Ok(Expression::binder(
            binder_type,
            variable,
            expression_type,
            expression_body,
        ))
    }
}

impl Parse for crate::expr::Expression {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if let Ok(token) = parse_binder(input) {
            Ok(token)
        } else {
            Err(input.error("expected expression"))
        }
    }
}

impl ToTokens for crate::expr::Expression {
    fn to_tokens(&self, _tokens: &mut proc_macro2::TokenStream) {
        todo!()
    }
}
