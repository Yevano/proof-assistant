use std::{
    borrow::Cow,
    collections::HashSet,
    fmt::{Display, Formatter},
};

use crate::{eval::beta_reduce, result::Result};
use crate::{eval::substitute, result::ResultExt};
use crate::{
    expr::{Binder, BinderType, Expression, Variable},
    goals::expressions_match,
};

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub enum Context<'a> {
    Empty,
    Extend(Box<Context<'a>>, Variable, Cow<'a, Expression>),
}

impl<'a> Context<'a> {
    pub fn extend(self, variable: Variable, expression: Cow<'a, Expression>) -> Self {
        Context::Extend(Box::new(self), variable, expression)
    }

    pub fn get(&self, v: &Variable) -> Option<Expression> {
        match self {
            Context::Empty => None,
            Context::Extend(box context, variable, expression) => {
                if v == variable {
                    Some(expression.as_ref().clone())
                } else {
                    context.get(v)
                }
            }
        }
    }

    pub fn variables(&self) -> HashSet<Variable> {
        match self {
            Context::Empty => HashSet::new(),
            Context::Extend(box context, variable, _) => {
                let mut variables = context.variables();
                variables.insert(variable.clone());
                variables
            }
        }
    }

    pub fn iter(&self) -> ContextIter<'_> {
        ContextIter { context: self }
    }
}

// implement Display for Context
impl<'a> Display for Context<'a> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        match self {
            Context::Empty => Ok(()),
            Context::Extend(box Context::Empty, variable, expression) => {
                write!(f, "Γ")?;
                write!(f, " {}: {}", variable, expression)
            }
            Context::Extend(box context, variable, expression) => {
                write!(f, "{}    {}: {}", context, variable, expression)
            }
        }
    }
}

pub struct ContextIter<'a> {
    context: &'a Context<'a>,
}

impl<'a> Iterator for ContextIter<'a> {
    type Item = (Variable, Expression);

    fn next(&mut self) -> Option<Self::Item> {
        match self.context {
            Context::Empty => None,
            Context::Extend(box context, ref variable, ref expression) => {
                self.context = context;
                Some((variable.clone(), expression.clone().into_owned()))
            }
        }
    }
}

pub fn resolve_type(expr: &Expression, context: &Context) -> Result<Expression> {
    let result = || match expr {
        Expression::Hole => Result::Ok(Expression::Hole),
        Expression::Sort(i) => Result::Ok(Expression::sort(i.index() + 1)),

        Expression::Variable(v) => match context.get(v) {
            Some(t) => Result::Ok(t),
            None => error!("variable {} not found in context {}", v, context).into(),
        },

        Expression::Binder(binder_type, box Binder(v, type_, body)) => {
            let body_context = context.clone().extend(v.clone(), Cow::Borrowed(type_));
            match binder_type {
                BinderType::Abstraction => {
                    let body_type = resolve_type(body, &body_context).chain_error(|| {
                        error!("failed to resolve type of body of abstraction {}", expr)
                    })?;
                    Result::Ok(Expression::product(v.clone(), type_.clone(), body_type))
                }
                BinderType::Product => resolve_type(body, &body_context)
                    .chain_error(|| error!("failed to resolve type of body of product {}", expr)),
            }
        }

        Expression::Application(app_lhs, app_rhs) => {
            let app_lhs_type = resolve_type(app_lhs, context).chain_error(|| {
                error!("failed to resolve type of function in application {}", expr)
            })?;
            match app_lhs_type {
                Expression::Binder(BinderType::Product, box Binder(_v, type_, body)) => {
                    let app_rhs_type = resolve_type(app_rhs, context).chain_error(|| {
                        error!("failed to resolve type of argument in application {}", expr)
                    })?;

                    expressions_match(&type_, &app_rhs_type)
                        .map(|_| substitute(&body, _v, &app_rhs.clone()))
                        .chain_error(|| {
                            error!(
                                "type mismatch in application {}: expected {}, got {}",
                                expr, type_, app_rhs_type
                            )
                        })
                }
                _ => error!(
                    "expected abstraction in application {}, got {}",
                    expr, app_lhs_type
                )
                .into(),
            }
        }
    };

    result()
        .map(|x| beta_reduce(&x))
        .chain_error(|| error!("failed to resolve type of {}", expr))
}
