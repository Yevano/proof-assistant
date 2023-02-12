use proc_macro2::Delimiter::Parenthesis;
use quote::{quote, ToTokens};
use syn::{
    parenthesized,
    parse::{Lookahead1, Parse, ParseStream},
    token::Underscore,
    Ident, LitStr,
};

use crate::expr::{Binder, BinderType, Expression, SortRank, Variable};

fn get_binder_type_by_ident(ident: &Ident) -> Option<crate::expr::BinderType> {
    match ident.to_string().as_str() {
        "fun" => Some(crate::expr::BinderType::Abstraction),
        "for" => Some(crate::expr::BinderType::Product),
        _ => None,
    }
}

fn parse_binder(input: ParseStream, _lookahead: &Lookahead1) -> syn::Result<Expression> {
    let binder_type = input.step(|cursor| {
        if let Some((ident, cursor)) = cursor.ident() {
            get_binder_type_by_ident(&ident)
                .map(|binder_type| (binder_type, cursor))
                .ok_or_else(|| input.error("expected `fun` or `for` here"))
        } else {
            Err(input.error("expected `fun` or `for` here"))
        }
    })?;
    let variable = Variable::new(
        &input
            .parse::<Ident>()
            .map(|ident| ident.to_string())
            .or_else(|_| input.parse::<Underscore>().map(|_| "_".to_string()))
            .map_err(|_| input.error("expected identifier here"))?,
    );
    input
        .parse::<syn::Token![:]>()
        .map_err(|_| input.error("expected `:` here"))?;
    let expression_type = input.parse::<Expression>()?;
    input
        .parse::<syn::Token![.]>()
        .map_err(|_| input.error("expected `.` here"))?;
    let expression_body = input.parse::<Expression>()?;
    Ok(Expression::binder(
        binder_type,
        variable,
        expression_type,
        expression_body,
    ))
}

fn parse_variable(input: ParseStream, _lookahead: &Lookahead1) -> syn::Result<Expression> {
    Ok(Expression::variable(
        input
            .parse::<Ident>()
            .map_err(|_| input.error("expected identifier here"))?
            .to_string()
            .as_str(),
    ))
}

fn parse_parens(input: ParseStream, _lookahead: &Lookahead1) -> syn::Result<Expression> {
    let content;
    parenthesized!(content in input);
    content.parse::<Expression>()
}

fn parse_sort(input: ParseStream, _lookahead: &Lookahead1) -> syn::Result<Expression> {
    input
        .parse::<syn::Token!(*)>()
        .map_err(|_| input.error("expected `*` here"))?;
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

fn add_error<T>(errors: &mut Vec<syn::Error>, result: syn::Result<T>) -> syn::Result<T> {
    if let Err(ref e) = result {
        errors.push(e.clone());
    }
    result
}

impl Parse for crate::expr::Expression {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let exprs = std::iter::repeat_with(|| {
            let mut errors = vec![];
            let lookahead = input.lookahead1();
            if let Ok(expr) = add_error(&mut errors, parse_binder(input, &lookahead)) {
                Ok(expr)
            } else if let Ok(expr) = add_error(&mut errors, parse_variable(input, &lookahead)) {
                Ok(expr)
            } else if lookahead.peek(syn::Token![?]) {
                input.parse::<syn::Token![?]>()?;
                Ok(Expression::Hole)
            } else if let Ok(expr) = add_error(&mut errors, parse_sort(input, &lookahead)) {
                Ok(expr)
            } else if let Ok(expr) = add_error(&mut errors, parse_parens(input, &lookahead)) {
                Ok(expr)
            } else {
                /* Err(errors
                    .into_iter()
                    .fold(input.error("invalid expression"), |mut acc, e| {
                        acc.combine(e);
                        acc
                    })) */
                Err(lookahead.error())
            }
        });

        let first_result = exprs.take(1).last().unwrap()?;
        let exprs = std::iter::once(Ok(first_result)).chain(exprs);

        let e = exprs
            .take_while(Result::is_ok)
            .map(Result::unwrap)
            .reduce(Expression::application)
            .unwrap();

        let lookahead = input.lookahead1();
        if lookahead.peek(syn::Token![=>]) {
            input
                .parse::<syn::Token![=>]>()
                .map_err(|_| input.error("expected `=>` here"))?;
            Ok(Expression::arrow(e, Self::parse(input)?))
        /* } else if input. {
        todo!() */
        } else if let Ok(_lit) = input.parse::<LitStr>() {
            Ok(Expression::application(e, Self::parse(input)?))
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

pub struct StringToCharArray {
    string: String,
}

impl Parse for StringToCharArray {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let lit = input.parse::<syn::LitStr>()?;
        Ok(Self { string: lit.value() })
    }
}

impl ToTokens for StringToCharArray {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let mut comma_separated = proc_macro2::TokenStream::new();
        let chars: Vec<char> = self.string.chars().collect();
        if let Some((first, rest)) = chars.split_first() {
            comma_separated.extend(quote!(#first));
            for c in rest {
                comma_separated.extend(quote!(, #c))
            }
        }

        tokens.extend(quote!([#comma_separated]))
    }
}