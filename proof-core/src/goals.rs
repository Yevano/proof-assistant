use std::{
    borrow::{Borrow, Cow},
    fmt::{Display, Formatter},
};

use crate::{
    eval::{beta_reduce_step},
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
        write!(f, "{}\n⊢ {}", self.context, self.goal_constraint)
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
            }) => write!(f, "{} = {}", actual_value, expected_value),
            Constraint::HasType(TypeConstraint {
                expression,
                expected_type,
            }) => write!(f, "{} : {}", expression, expected_type),
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
    match actual_value.borrow() {
        Expression::Hole => Ok(vec![Goal::new(
            context,
            Cow::Owned(Constraint::Equal(EqConstraint {
                actual_value: Expression::Hole,
                expected_value: expected_value.into_owned(),
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
        Expression::Application(_, _) => todo!(),
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
    }
}

fn find_expected_type_goals<'a>(
    context: Context<'a>,
    expression: Cow<'a, Expression>,
    expected_type: Cow<'a, Expression>,
) -> Result<Vec<Goal<'a>>> {
    match expression.borrow() {
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
            let substituted_body = beta_reduce_step(&Expression::application(*left.clone(), *right.clone()));
            let body_type = resolve_type(&substituted_body, &context).chain_error(|| {
                error!(
                    "Could not resolve type of body in application {}",
                    expression
                )
            });
            error_list.push_if_error(|| goals.clone());
            error_list.push_if_error(|| body_type.clone());
            error_list.into_result(|| goals.unwrap(), || error!("Could not find typing goal for application {}", expression))
        }
        Expression::Binder(
            BinderType::Abstraction,
            box Binder(bound_variable, bound_variable_type, body),
        ) => {
            let expected_type = expected_type.borrow();
            if let Expression::Binder(
                BinderType::Product,
                box Binder(_, expected_variable_type, expected_binder_body),
            ) = expected_type
            {
                let mut goals = find_eq_goals(
                    context.clone(),
                    Cow::Owned(bound_variable_type.clone()),
                    Cow::Owned(expected_variable_type.clone()),
                )
                .chain_error(|| {
                    error!(
                        "Could not find goals for type of variable bound by abstraction {}",
                        expression
                    )
                })?;
                let body_context = context.extend(
                    bound_variable.clone(),
                    Cow::Owned(bound_variable_type.clone()),
                );
                let mut body_goals = find_expected_type_goals(
                    body_context,
                    Cow::Owned(body.clone()),
                    Cow::Owned(expected_binder_body.clone()),
                )
                .chain_error(|| {
                    error!(
                        "Could not find goals for body of abstraction {}",
                        expression
                    )
                })?;
                goals.append(&mut body_goals);
                Ok(goals)
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
                expression: expression.into_owned(),
                expected_type: expected_type.into_owned(),
            });
            Result::Ok(vec![Goal::new(context, Cow::Owned(constraint))])
        }
    }
}
