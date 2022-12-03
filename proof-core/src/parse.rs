use proc_macro2::Delimiter::Parenthesis;
use quote::{quote, ToTokens};
use syn::{
    parenthesized,
    parse::{Parse, ParseStream},
    Ident,
};

use crate::expr::{Binder, BinderType, Expression, SortRank, Variable};

fn get_binder_type_by_ident(ident: &Ident) -> Option<crate::expr::BinderType> {
    match ident.to_string().as_str() {
        "fun" => Some(crate::expr::BinderType::Abstraction),
        "for" => Some(crate::expr::BinderType::Product),
        _ => None,
    }
}

fn parse_binder(input: ParseStream) -> syn::Result<Expression> {
    let binder_type = input.step(|cursor| {
        if let Some((ident, cursor)) = cursor.ident() {
            get_binder_type_by_ident(&ident)
                .map(|binder_type| (binder_type, cursor))
                .ok_or_else(|| input.error("expected `fun` or `for` here"))
        } else {
            Err(input.error("expected `fun` or `for` here"))
        }
    })?;
    let variable = Variable::new(input.parse::<Ident>()?.to_string().as_str());
    input.parse::<syn::Token![:]>()?;
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

fn parse_variable(input: ParseStream) -> syn::Result<Expression> {
    Ok(Expression::variable(
        input.parse::<Ident>()?.to_string().as_str(),
    ))
}

fn parse_parens(input: ParseStream) -> syn::Result<Expression> {
    let content;
    parenthesized!(content in input);
    content.parse::<Expression>()
}

fn parse_sort(input: ParseStream) -> syn::Result<Expression> {
    input.parse::<syn::Token!(*)>()?;
    let rank = input
        .step(|cursor| {
            if let Some((inner_cursor, _, cursor)) = cursor.group(Parenthesis) {
                if let Some((lit, _)) = inner_cursor.literal() {
                    lit.to_string()
                        .parse::<u32>()
                        .map(|i| (i, cursor))
                        .map_err(|_| input.error("expected integer literal"))
                } else {
                    Err(input.error("expected literal"))
                }
            } else {
                Err(input.error("expected literal"))
            }
        })
        .unwrap_or_default();
    Ok(Expression::Sort(SortRank(rank)))
}

impl Parse for crate::expr::Expression {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut exprs = std::iter::repeat_with(|| {
            if let Ok(expr) = parse_binder(input) {
                Ok(expr)
            } else if let Ok(expr) = parse_variable(input) {
                Ok(expr)
            } else if input.parse::<syn::Token![?]>().is_ok() {
                Ok(Expression::Hole)
            } else if let Ok(expr) = parse_sort(input) {
                Ok(expr)
            } else if let Ok(expr) = parse_parens(input) {
                Ok(expr)
            } else {
                Err(input.error("expected expression"))
            }
        });

        let first = exprs.next().unwrap()?;
        let e = exprs
            .map_while(|expr: syn::Result<Expression>| match expr {
                Ok(e) => Some(e),
                Err(_) => None,
            })
            .fold(first, Expression::application);

        if input.peek(syn::Token![=>]) {
            input.parse::<syn::Token![=>]>()?;
            Ok(Expression::arrow(e, Self::parse(input)?))
        } else {
            Ok(e)
        }
    }
}

impl ToTokens for crate::expr::Expression {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        tokens.extend(match self {
            Expression::Hole => quote!(proof_core::expr::Expression::Hole),
            Expression::Sort(SortRank(i)) => {
                quote!(proof_core::expr::Expression::Sort(proof_core::expr::SortRank(#i)))
            }
            Expression::Variable(v) => quote!(proof_core::expr::Expression::Variable(#v)),
            Expression::Binder(binder_type, box Binder(var, type_, body)) => quote!(
                proof_core::expr::Expression::Binder(
                    #binder_type,
                    Box::new(proof_core::expr::Binder(#var, #type_, #body)),
            )),
            Expression::Application(box a, box b) => quote!(
                proof_core::expr::Expression::Application(
                    Box::new(#a), Box::new(#b)
                )
            ),
        })
    }
}

impl ToTokens for Variable {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        tokens.extend(match self {
            Variable(v, None) => quote!(
                proof_core::expr::Variable(#v.to_string(), None)
            ),
            Variable(v, Some(i)) => quote!(
                proof_core::expr::Variable(#v.to_string(), Some(#i))
            ),
        })
    }
}

impl ToTokens for BinderType {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        tokens.extend(match self {
            BinderType::Product => quote!(proof_core::expr::BinderType::Product),
            BinderType::Abstraction => quote!(proof_core::expr::BinderType::Abstraction),
        })
    }
}
