use std::{
    borrow::Cow,
    collections::HashSet,
    fmt::{Display, Formatter},
};

use crate::result::ResultExt;
use crate::{eval::beta_reduce, result::Result};
use crate::{
    eval::{alpha_eq, beta_reduce_step},
    expr::{Binder, BinderType, Expression, Variable},
};

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub enum Context<'a> {
    Empty,
    Extend(Box<Context<'a>>, Variable, Cow<'a, Expression>),
}

impl<'a> Context<'a> {
    pub fn extend(self, variable: Variable, expression: Cow<'a, Expression>) -> Self {
        Context::Extend(Box::new(self), variable.clone(), expression)
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

pub fn resolve_type(expr: &Expression, context: &Context) -> Result<Expression> {
    let result = || match expr {
        Expression::Hole => Result::Ok(Expression::Hole),
        Expression::Sort(i) => Result::Ok(Expression::sort(i.index() + 1)),
        Expression::Variable(v) => match context.get(v) {
            Some(t) => Result::Ok(t.clone()),
            None => error!("variable {} not found in context {}", v, context).into(),
        },
        Expression::Binder(binder_type, box Binder(v, type_, body)) => {
            let body_context = context.clone().extend(v.clone(), Cow::Borrowed(type_));
            match binder_type {
                BinderType::Abstraction => {
                    let body_type = resolve_type(body, &body_context).chain_error(|| {
                        error!("failed to resolve type of body of abstraction {}", expr)
                    })?;
                    // let product_variable = Variable::new("t").freshen_with_context(context);
                    Result::Ok(Expression::product(v.clone(), type_.clone(), body_type))
                }
                BinderType::Product => Result::Ok(Expression::sort(0)),
            }
        }
        Expression::Application(app_lhs, app_rhs) => {
            let app_lhs_type = resolve_type(app_lhs, context).chain_error(|| {
                error!("failed to resolve type of function in application {}", expr)
            })?;
            println!("NOTE: lhs = {} :: {}", app_lhs, app_lhs_type);
            match app_lhs_type {
                Expression::Binder(BinderType::Product, box Binder(_v, type_, body)) => {
                    let app_rhs_type = resolve_type(app_rhs, context).chain_error(|| {
                        error!("failed to resolve type of argument in application {}", expr)
                    })?;
                    println!("NOTE: rhs = {} :: {}", app_rhs, app_rhs_type);
                    /* let type_beta_reduced = beta_reduce(&type_);
                    let app_rhs_type_beta_reduced = beta_reduce(&app_rhs_type);
                    if alpha_eq(&type_beta_reduced, &app_rhs_type_beta_reduced) {
                        Ok(body.clone())
                    } else {
                        error!(
                            "type mismatch in application {}: expected {}, got {} (beta reduced to {} and {}, not α-equivalent)",
                            expr, type_, app_rhs_type, type_beta_reduced, app_rhs_type_beta_reduced
                        )
                        .into()
                    } */

                    types_match(&type_, &app_rhs_type).map(|_| body.clone()).chain_error(|| {
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

    result().chain_error(|| error!("failed to resolve type of {}", expr))
}

pub fn types_match(lhs: &Expression, rhs: &Expression) -> Result<()> {
    let lhs_beta_reduced = beta_reduce(&lhs);
    let rhs_beta_reduced = beta_reduce(&rhs);
    if lhs_beta_reduced == Expression::Hole || rhs_beta_reduced == Expression::Hole {
        Ok(())
    } else if alpha_eq(&lhs_beta_reduced, &rhs_beta_reduced) {
        Ok(())
    } else {
        error!(
            "{} does not match with {} (beta reduced to {} and {}, not α-equivalent)",
            lhs, rhs, lhs_beta_reduced, rhs_beta_reduced
        )
        .into()
    }
}

// #[test]
// fn it_
