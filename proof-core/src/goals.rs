use std::{
    borrow::{Borrow, Cow},
    fmt::{Display, Formatter},
};

use crate::{
    eval::{beta_reduce, beta_reduce_step, get_compatible_bound_variable, substitute},
    expr::{Binder, BinderType, Expression},
    result::*,
    types::{resolve_type, Context},
};

#[derive(Clone)]
pub struct Goal<'a> {
    context: Context<'a>,
    goal_constraint: Cow<'a, Constraint>,
}

impl<'a> Goal<'a> {
    pub fn new(context: Context<'a>, goal_constraint: Cow<'a, Constraint>) -> Self {
        Goal {
            context,
            goal_constraint,
        }
    }
}

impl Display for Goal<'_> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        for (variable, type_) in self.context.iter().collect::<Vec<_>>().iter().rev() {
            writeln!(f, "{} : {}", variable, type_)?;
        }
        write!(f, "⊢ {}", self.goal_constraint)
    }
}

#[derive(Clone, Debug)]
pub struct EqConstraint {
    /// The expression (possibly containing holes) to check for equality
    pub actual_value: Expression,
    /// The expected value
    pub expected_value: Expression,
}

#[derive(Clone, Debug)]
pub struct TypeConstraint {
    /// The expression (possibly containing holes) to type check
    pub expression: Expression,
    /// The expected type
    pub expected_type: Expression,
}

#[derive(Clone, Debug)]
pub enum Constraint {
    Equal(EqConstraint),
    HasType(TypeConstraint),
}

impl Display for Constraint {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        match self {
            Constraint::Equal(EqConstraint {
                actual_value,
                expected_value,
            }) => write!(f, "{} = {}", actual_value, beta_reduce(expected_value)),
            Constraint::HasType(TypeConstraint {
                expression,
                expected_type,
            }) => write!(f, "{} : {}", expression, beta_reduce(expected_type)),
        }
    }
}

pub fn find_goals<'a>(context: Context<'a>, constraint: &'a Constraint) -> Result<Vec<Goal<'a>>> {
    match constraint {
        Constraint::Equal(EqConstraint {
            actual_value,
            expected_value,
        }) => find_eq_goals(
            context,
            Cow::Borrowed(actual_value),
            Cow::Borrowed(expected_value),
        ),
        Constraint::HasType(TypeConstraint {
            expression,
            expected_type,
        }) => find_expected_type_goals(
            context,
            Cow::Borrowed(expression),
            Cow::Borrowed(expected_type),
        ),
    }
    .chain_error(|| error!("Failed to find goals for constraint {}", constraint))
}

fn find_eq_goals<'a>(
    context: Context<'a>,
    actual_value: Cow<'a, Expression>,
    expected_value: Cow<'a, Expression>,
) -> Result<Vec<Goal<'a>>> {
    let expected_value: Cow<'a, Expression> = Cow::Owned(beta_reduce(&expected_value));

    let result = match actual_value.borrow() {
        Expression::Hole => Ok(vec![Goal::new(
            context,
            Cow::Owned(Constraint::Equal(EqConstraint {
                actual_value: Expression::Hole,
                expected_value: <std::borrow::Cow<'_, Expression> as std::borrow::Borrow<
                    Expression,
                >>::borrow(&expected_value)
                .clone(),
            })),
        )]),
        Expression::Binder(
            binder_type,
            box Binder(actual_variable, actual_variable_type, actual_body),
        ) => match expected_value.borrow() {
            Expression::Hole => Ok(vec![Goal::new(
                context,
                Cow::Owned(Constraint::Equal(EqConstraint {
                    actual_value: actual_value.clone().into_owned(),
                    expected_value: Expression::Hole,
                })),
            )]),
            Expression::Binder(
                expected_binder_type,
                box Binder(_expected_variable, expected_variable_type, expected_body),
            ) => {
                if binder_type == expected_binder_type {
                    let mut goals = find_eq_goals(
                        context.clone(),
                        Cow::Owned(actual_variable_type.clone()),
                        Cow::Owned(expected_variable_type.clone()),
                    )?;
                    goals.append(&mut find_eq_goals(
                        context.extend(
                            actual_variable.clone(),
                            Cow::Owned(actual_variable_type.clone()),
                        ),
                        Cow::Owned(actual_body.clone()),
                        Cow::Owned(expected_body.clone()),
                    )?);
                    Ok(goals)
                } else {
                    error!("Binder types do not match").into()
                }
            }
            _ => error!("Expected value is not a binder").into(),
        },
        Expression::Application(a, b) => match expected_value.borrow() {
            Expression::Application(e, f) => {
                let lhs_goals_result = find_eq_goals(
                    context.clone(),
                    Cow::Owned(*a.clone()),
                    Cow::Owned(*e.clone()),
                );
                let rhs_goals_result = find_eq_goals(
                    context.clone(),
                    Cow::Owned(*b.clone()),
                    Cow::Owned(*f.clone()),
                );
                let mut error_list = ErrorList::new();
                error_list.push_if_error(|| lhs_goals_result.clone());
                error_list.push_if_error(|| rhs_goals_result.clone());
                error_list.into_result(
                    || {
                        let lhs_goals = lhs_goals_result.unwrap();
                        let rhs_goals = rhs_goals_result.unwrap();

                        let lhs_goals_iter = lhs_goals.iter();
                        let rhs_goals_iter = rhs_goals.iter();
                        let chained = lhs_goals_iter.chain(rhs_goals_iter);
                        let cloned_iter = chained.cloned();
                        cloned_iter.collect()
                    },
                    || error!("Failed to match application"),
                )
            }
            e => error!("Expected {}, got application {}", e, actual_value).into(),
        },
        _ => {
            if actual_value == Cow::Owned(beta_reduce_step(expected_value.borrow())) {
                Ok(vec![])
            } else {
                error!(
                    "Expected {} to be equal to {}",
                    actual_value, expected_value
                )
                .into()
            }
        }
    };

    result.chain_error(|| {
        let expected_value = &expected_value;
        error!(
            "Could not find goals for constraint {} = {}",
            actual_value,
            expected_value.clone()
        )
    })
}

fn find_expected_type_goals<'a>(
    context: Context<'a>,
    expression: Cow<'a, Expression>,
    expected_type: Cow<'a, Expression>,
) -> Result<Vec<Goal<'a>>> {
    let expression: Cow<'a, Expression> = Cow::Owned(beta_reduce(&expression));
    let expected_type: Cow<'a, Expression> = Cow::Owned(beta_reduce(&expected_type));

    let result = match expression.borrow() {
        Expression::Sort(_) => todo!("Sorts are not implemented yet"),
        Expression::Variable(variable) => {
            let actual_type = context
                .get(variable)
                .ok_or_else(|| error!("Variable {} not found in context", variable))?;
            let eq_goals = find_eq_goals(context, Cow::Owned(actual_type), expected_type.clone());
            eq_goals.chain_error(|| {
                error!(
                    "Failed to find goals for type constraint {} : {}",
                    expression, expected_type
                )
            })
        }
        Expression::Application(left, right) => {
            let left_type = resolve_type(left, &context).chain_error(|| {
                error!(
                    "Could not resolve type of left-hand-side in application {}",
                    expression
                )
            })?;
            let left_argument_type = match left_type {
                Expression::Binder(BinderType::Product, box Binder(_, argument_type, _)) => {
                    Result::Ok(argument_type)
                }
                Expression::Sort(_) => error!(
                    "Cannot match application of term {}, which has type {}",
                    left, left_type
                )
                .into(),
                _ => error!(
                    "Cannot match application of term {}, which has type {}",
                    left, left_type
                )
                .into(),
            }?;
            let mut error_list = ErrorList::new();
            let goals = find_expected_type_goals(
                context.clone(),
                Cow::Owned(*right.clone()),
                Cow::Owned(left_argument_type.clone()),
            )
            .chain_error(|| {
                error!(
                    "Could not find typing goal {} : {}",
                    right, left_argument_type
                )
            });
            let substituted_body =
                beta_reduce_step(&Expression::application(*left.clone(), *right.clone()));
            let body_type = resolve_type(&substituted_body, &context).chain_error(|| {
                error!(
                    "Could not resolve type of body in application {}",
                    expression
                )
            });
            error_list.push_if_error(|| goals.clone());
            error_list.push_if_error(|| body_type.clone());
            error_list.into_result(
                || goals.unwrap(),
                || error!("Could not find typing goal for application {}", expression),
            )
        }
        Expression::Binder(
            BinderType::Abstraction,
            box Binder(bound_variable, bound_variable_type, body),
        ) => {
            if let Expression::Binder(
                BinderType::Product,
                box Binder(expected_variable, expected_variable_type, expected_binder_body),
            ) = expected_type.borrow()
            {
                let mut goals = find_eq_goals(
                    context.clone(),
                    Cow::Owned(bound_variable_type.clone()),
                    Cow::Owned(expected_variable_type.clone()),
                )
                .chain_error(|| {
                    error!(
                        "Could not find goals for type of variable {} : {}. Expected type was {}.",
                        bound_variable, bound_variable_type, expected_variable_type,
                    )
                })?;

                let body_context = context.extend(
                    bound_variable.clone(),
                    Cow::Owned(bound_variable_type.clone()),
                );

                let substituted_expected_body = substitute(
                    expected_binder_body,
                    expected_variable.clone(),
                    &bound_variable.clone().into(),
                );

                let mut body_goals = find_expected_type_goals(
                    body_context,
                    Cow::Owned(body.clone()),
                    Cow::Owned(substituted_expected_body),
                )
                .chain_error(|| {
                    error!(
                        "Could not find goals for body of abstraction {}",
                        expression
                    )
                })?;
                goals.append(&mut body_goals);
                Ok(goals)
            } else if expected_type.clone().into_owned() == Expression::Hole {
                unimplemented!("not sure if this should ever happen")
            } else {
                error!("Expected type is not a product").into()
            }
        }
        Expression::Binder(
            BinderType::Product,
            box Binder(_bound_variable, _bound_variable_type, _body),
        ) => {
            todo!("find_expected_type_goals for product")
        }
        Expression::Hole => {
            let constraint = Constraint::HasType(TypeConstraint {
                expression:
                    <std::borrow::Cow<'_, Expression> as std::borrow::Borrow<Expression>>::borrow(
                        &expression,
                    )
                    .clone(),
                expected_type: <std::borrow::Cow<'_, Expression> as std::borrow::Borrow<
                    Expression,
                >>::borrow(&expected_type)
                .clone(),
            });
            Result::Ok(vec![Goal::new(context, Cow::Owned(constraint))])
        }
    };

    result.chain_error(|| {
        let expected_type = &expected_type;
        error!(
            "Could not find goals for constraint {} : {}",
            expression,
            expected_type.clone()
        )
    })
}

/// Determines whether two expressions are either equivalent or pattern match up to holes.
pub fn expressions_match(lhs: &Expression, rhs: &Expression) -> Result<()> {
    let lhs_beta_reduced = beta_reduce(lhs);
    let rhs_beta_reduced = beta_reduce(rhs);

    match (lhs_beta_reduced, rhs_beta_reduced) {
        (Expression::Hole, _) => Ok(()),
        (_, Expression::Hole) => Ok(()),
        (Expression::Sort(a), Expression::Sort(b)) => {
            if a == b {
                Ok(())
            } else {
                error!("{} != {}", a, b).into()
            }
        }
        (Expression::Variable(a), Expression::Variable(b)) => {
            if a == b {
                Ok(())
            } else {
                error!("variables {} and {} are not equivalent", a, b).into()
            }
        }
        (
            Expression::Binder(
                lhs_binder_type,
                box Binder(lhs_variable, lhs_variable_type, lhs_body),
            ),
            Expression::Binder(
                rhs_binder_type,
                box Binder(rhs_variable, rhs_variable_type, rhs_body),
            ),
        ) => {
            let variable =
                get_compatible_bound_variable(&lhs_variable, &lhs_body, &rhs_variable, &rhs_body);
            let lhs_body = substitute(
                &lhs_body,
                lhs_variable,
                &Expression::Variable(variable.clone()),
            );
            let rhs_body = substitute(&rhs_body, rhs_variable, &Expression::Variable(variable));

            if lhs_binder_type != rhs_binder_type {
                error!(
                    "binder types ({}, {}) do not match",
                    lhs_binder_type, rhs_binder_type
                )
                .into()
            } else {
                let mut error_list = ErrorList::new();
                error_list
                    .push_if_error(|| expressions_match(&lhs_variable_type, &rhs_variable_type));
                error_list.push_if_error(|| expressions_match(&lhs_body, &rhs_body));
                error_list.into_result(|| (), || error!("expressions do not match"))
            }
        }
        (Expression::Application(lhs_a, lhs_b), Expression::Application(rhs_a, rhs_b)) => {
            let mut error_list = ErrorList::new();
            error_list.push_if_error(|| expressions_match(&lhs_a, &rhs_a));
            error_list.push_if_error(|| expressions_match(&lhs_b, &rhs_b));
            error_list.into_result(|| (), || error!("expressions do not match"))
        }
        (a, b) => error!("{} and {} do not match", a, b).into(),
    }
    .chain_error(|| error!("{} and {} do not match", lhs, rhs))
}
