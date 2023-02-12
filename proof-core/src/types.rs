use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
    fmt::{Display, Formatter},
    mem,
};

use crate::{
    eval::beta_reduce,
    expr::{ExpressionPath, SortRank},
    result::Result,
};
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

    pub fn resolve_type(&self, expr: &Expression) -> Result<Expression> {
        let result = || match expr {
            Expression::Hole => Result::Ok(Expression::Hole),
            Expression::Sort(i) => Result::Ok(Expression::sort(i.index() + 1)),

            Expression::Variable(v) => match self.get(v) {
                Some(t) => Result::Ok(t),
                None => error!("variable {} not found in context {}", v, self).into(),
            },

            Expression::Binder(binder_type, box Binder(v, type_, body)) => {
                let body_context = self.clone().extend(v.clone(), Cow::Borrowed(type_));
                match binder_type {
                    BinderType::Abstraction => {
                        let body_type = body_context.resolve_type(body).chain_error(|| {
                            error!("failed to resolve type of body of abstraction {}", expr)
                        })?;
                        Result::Ok(Expression::product(v.clone(), type_.clone(), body_type))
                    }
                    BinderType::Product => body_context.resolve_type(body).chain_error(|| {
                        error!("failed to resolve type of body of product {}", expr)
                    }),
                }
            }

            Expression::Application(app_lhs, app_rhs) => {
                let app_lhs_type = self.resolve_type(app_lhs).chain_error(|| {
                    error!(
                        "failed to resolve left-hand-side of application [{}] [{}]",
                        app_lhs, app_rhs,
                    )
                })?;
                match app_lhs_type {
                    Expression::Binder(BinderType::Product, box Binder(_v, type_, body)) => {
                        let app_rhs_type = self.resolve_type(app_rhs).chain_error(|| {
                            error!("failed to resolve type of argument in application {}", expr)
                        })?;

                        expressions_match(&type_, &app_rhs_type)
                            .map(|_| substitute(&body, _v, &app_rhs.clone()))
                            .chain_error(|| {
                                error!(
                                    "type mismatch in application [{}] [{}]: expected argument of type {}, got {}",
                                    app_lhs, app_rhs, type_, app_rhs_type
                                )
                            })
                    }
                    _ => error!(
                        "expected left-hand-side of application [{}] [{}] to be a product type, got {}",
                        app_lhs, app_rhs, app_lhs_type
                    )
                    .into(),
                }
            }
        };

        result()
            .map(|x| beta_reduce(&x))
            .chain_error(|| error!("failed to resolve type of {}", expr))
    }

    pub fn inhabits_type(&self, value: &Expression, typ: &Expression) -> Result<()> {
        let actual_type = self.resolve_type(value)?;
        expressions_match(&actual_type, typ)
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

#[derive(Debug, Clone)]
pub enum PathTypeConstraint {
    TermInhabitsType {
        term: ExpressionPath,
        type_of_term: ExpressionPath,
    },
    TermInhabitsProductType {
        term: ExpressionPath,
        inhabited_product_argument_type: ExpressionPath,
        inhabited_product_return_type: ExpressionPath,
    },
    TermsAreEqual {
        term_lhs: ExpressionPath,
        term_rhs: ExpressionPath,
    },
    TermsInhabitSameType {
        term_lhs: ExpressionPath,
        term_rhs: ExpressionPath,
    },
    TermInhabitsUnknownType(ExpressionPath),
    TermIsIllFormed(ExpressionPath),
    TermIsProductType(ExpressionPath),
    TermIsSort(ExpressionPath, SortRank),
}

impl Display for PathTypeConstraint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TermInhabitsType { term, type_of_term } => {
                write!(f, "[{}] : [{}]", term, type_of_term)
            }
            Self::TermInhabitsProductType {
                term,
                inhabited_product_argument_type,
                inhabited_product_return_type,
            } => {
                write!(
                    f,
                    "[{}] : (Π _ : [{}]. [{}])",
                    term, inhabited_product_argument_type, inhabited_product_return_type
                )
            }
            Self::TermsAreEqual { term_lhs, term_rhs } => {
                write!(f, "[{}] = [{}]", term_lhs, term_rhs)
            }
            Self::TermsInhabitSameType { term_lhs, term_rhs } => {
                write!(f, "∀ T ∈ Type, [{}] : T <=> [{}] : T", term_lhs, term_rhs)
            }
            Self::TermInhabitsUnknownType(_) => todo!(),
            Self::TermIsIllFormed(term) => write!(f, "ill-formed: [{}]", term),
            Self::TermIsProductType(term) => write!(f, "[{}] = Π...", term),
            Self::TermIsSort(term, sort_rank) => {
                write!(f, "[{}] = {}", term, Expression::Sort(*sort_rank))
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum PathTypeConstraintIntoExpression {
    TermInhabitsType {
        term: Expression,
        type_of_term: Expression,
    },
    TermInhabitsProductType {
        term: Expression,
        inhabited_product_argument_type: Expression,
        inhabited_product_return_type: Expression,
    },
    TermsAreEqual {
        term_lhs: Expression,
        term_rhs: Expression,
    },
    TermsInhabitSameType {
        term_lhs: Expression,
        term_rhs: Expression,
    },
    TermInhabitsUnknownType(Expression),
    TermIsIllFormed(Expression),
    TermIsProductType(Expression),
    TermIsSort(Expression, SortRank),
}

impl Display for PathTypeConstraintIntoExpression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TermInhabitsType { term, type_of_term } => {
                write!(f, "[{}] : [{}]", term, type_of_term)
            }
            Self::TermInhabitsProductType {
                term,
                inhabited_product_argument_type,
                inhabited_product_return_type,
            } => {
                write!(
                    f,
                    "[{}] : (Π _ : [{}]. [{}])",
                    term, inhabited_product_argument_type, inhabited_product_return_type
                )
            }
            Self::TermsAreEqual { term_lhs, term_rhs } => {
                write!(f, "[{}] = [{}]", term_lhs, term_rhs)
            }
            Self::TermsInhabitSameType { term_lhs, term_rhs } => {
                write!(f, "∀ T ∈ Type, [{}] : T <=> [{}] : T", term_lhs, term_rhs)
            }
            Self::TermInhabitsUnknownType(_) => todo!(),
            Self::TermIsIllFormed(term) => write!(f, "ill-formed: [{}]", term),
            Self::TermIsProductType(term) => write!(f, "[{}] = Π...", term),
            Self::TermIsSort(term, sort_rank) => {
                write!(f, "[{}] = {}", term, Expression::Sort(*sort_rank))
            }
        }
    }
}

pub fn map_path_type_constraint_from_paths(
    expression: &Expression,
    constraint: &PathTypeConstraint,
) -> PathTypeConstraintIntoExpression {
    match constraint {
        PathTypeConstraint::TermInhabitsType { term, type_of_term } => {
            PathTypeConstraintIntoExpression::TermInhabitsType {
                term: expression
                    .path_ref(term)
                    .unwrap_or(&Expression::Hole)
                    .clone(),
                type_of_term: expression
                    .path_ref(type_of_term)
                    .unwrap_or(&Expression::Hole)
                    .clone(),
            }
        }
        PathTypeConstraint::TermInhabitsProductType {
            term,
            inhabited_product_argument_type,
            inhabited_product_return_type,
        } => PathTypeConstraintIntoExpression::TermInhabitsProductType {
            term: expression
                .path_ref(term)
                .unwrap_or(&Expression::Hole)
                .clone(),
            inhabited_product_argument_type: expression
                .path_ref(inhabited_product_argument_type)
                .unwrap_or(&Expression::Hole)
                .clone(),
            inhabited_product_return_type: expression
                .path_ref(inhabited_product_return_type)
                .unwrap_or(&Expression::Hole)
                .clone(),
        },
        PathTypeConstraint::TermsAreEqual { term_lhs, term_rhs } => {
            PathTypeConstraintIntoExpression::TermsAreEqual {
                term_lhs: expression
                    .path_ref(term_lhs)
                    .unwrap_or(&Expression::Hole)
                    .clone(),
                term_rhs: expression
                    .path_ref(term_rhs)
                    .unwrap_or(&Expression::Hole)
                    .clone(),
            }
        }
        PathTypeConstraint::TermsInhabitSameType { term_lhs, term_rhs } => {
            PathTypeConstraintIntoExpression::TermsInhabitSameType {
                term_lhs: expression
                    .path_ref(term_lhs)
                    .unwrap_or(&Expression::Hole)
                    .clone(),
                term_rhs: expression
                    .path_ref(term_rhs)
                    .unwrap_or(&Expression::Hole)
                    .clone(),
            }
        }
        PathTypeConstraint::TermInhabitsUnknownType(term) => {
            PathTypeConstraintIntoExpression::TermInhabitsUnknownType(
                expression
                    .path_ref(term)
                    .unwrap_or(&Expression::Hole)
                    .clone(),
            )
        }
        PathTypeConstraint::TermIsIllFormed(term) => {
            PathTypeConstraintIntoExpression::TermIsIllFormed(
                expression
                    .path_ref(term)
                    .unwrap_or(&Expression::Hole)
                    .clone(),
            )
        }
        PathTypeConstraint::TermIsProductType(term) => {
            PathTypeConstraintIntoExpression::TermIsProductType(
                expression
                    .path_ref(term)
                    .unwrap_or(&Expression::Hole)
                    .clone(),
            )
        }
        PathTypeConstraint::TermIsSort(lhs, rhs) => PathTypeConstraintIntoExpression::TermIsSort(
            expression
                .path_ref(lhs)
                .unwrap_or(&Expression::Hole)
                .clone(),
            *rhs,
        ),
    }
}

#[derive(Default, Debug, Clone)]
pub struct PathContext {
    bindings: HashMap<Variable, ExpressionPath>,
}

impl PathContext {
    pub fn new() -> Self {
        Self {
            ..Default::default()
        }
    }

    pub fn get(&self, key: &Variable) -> Option<&ExpressionPath> {
        self.bindings.get(key)
    }

    pub fn get_mut(&mut self, key: &Variable) -> Option<&mut ExpressionPath> {
        self.bindings.get_mut(key)
    }

    fn set(&mut self, key: &Variable, value: &ExpressionPath) {
        self.bindings.insert(key.clone(), value.clone());
    }

    fn remove(&mut self, variable: &Variable) -> Option<ExpressionPath> {
        self.bindings.remove(variable)
    }
}

pub struct PositionWithContext<'a> {
    pub context: Context<'a>,
    pub position: ExpressionPath,
}

pub struct TypeEquation {
    pub lhs: Expression,
    pub rhs: Expression,
}

impl TypeEquation {
    pub fn new(lhs: &Expression, rhs: &Expression) -> Self {
        TypeEquation {
            lhs: lhs.clone(),
            rhs: rhs.clone(),
        }
    }
}

impl Display for TypeEquation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.lhs, self.rhs)
    }
}

pub trait InferenceSolver {
    fn solve_equations(&self, context: &Context, equations: &mut Vec<TypeEquation>) -> Result<()>;

    fn init_constraints(
        &self,
        context: &mut PathContext,
        focus_path: &ExpressionPath,
        constraints: &mut Vec<PathTypeConstraint>,
    );
}

impl InferenceSolver for Expression {
    /// Solve the type equations for the given expression in the given context.
    ///
    /// f : Πx : A. B
    /// y : C
    /// f y : B
    /// -------------
    /// A = C
    ///
    /// Infer type of function.
    /// f : F
    /// y : A
    /// f y : B
    /// -------------
    /// F = Πx : A. B
    ///
    fn solve_equations(&self, context: &Context, equations: &mut Vec<TypeEquation>) -> Result<()> {
        match self {
            Self::Binder(_, box Binder(variable, argument_type, body)) => {
                let mut binder_equations = mem::take(equations);
                argument_type.solve_equations(context, &mut binder_equations)?;

                let new_context = context
                    .clone()
                    .extend(variable.clone(), Cow::Borrowed(argument_type));
                body.solve_equations(&new_context, &mut binder_equations)?;

                mem::swap(equations, &mut binder_equations);

                Ok(())
            }
            Self::Application(f, x) => {
                let mut app_equations = mem::take(equations);
                f.solve_equations(context, &mut app_equations)?;
                x.solve_equations(context, &mut app_equations)?;
                mem::swap(equations, &mut app_equations);

                let fun_type = context.resolve_type(f)?;

                if let Self::Binder(BinderType::Product, box Binder(_, argument_type, _)) = fun_type
                {
                    let x_type = context.resolve_type(&x)?;
                    equations.push(TypeEquation::new(&argument_type, &x_type));
                    Ok(())
                } else {
                    Ok(())
                }
                // equations.push(TypeEquation::new());
            }
            _ => Ok(()),
        }
    }

    fn init_constraints(
        &self,
        context: &mut PathContext,
        focus_path: &ExpressionPath,
        constraints: &mut Vec<PathTypeConstraint>,
    ) {
        match self {
            Self::Hole => {}
            Self::Sort(rank_id) => {
                // Term is sort.
                let term_is_sort_constraint =
                    PathTypeConstraint::TermIsSort(focus_path.clone(), *rank_id);
                constraints.push(term_is_sort_constraint);
            }
            Self::Variable(variable) => {
                // Try to fetch type from context.
                let variable_type_term = context.get(variable);
                if let Some(variable_type_term) = variable_type_term {
                    constraints.push(PathTypeConstraint::TermInhabitsType {
                        term: focus_path.clone(),
                        type_of_term: variable_type_term.clone(),
                    });
                }
            }
            Self::Binder(binder_type, box Binder(variable, binder_argument_type, binder_body)) => {
                binder_argument_type.init_constraints(
                    context,
                    &focus_path.clone_with_binder_argument_type(),
                    constraints,
                );
                context.set(variable, &focus_path.clone_with_binder_argument_type());
                binder_body.init_constraints(
                    context,
                    &focus_path.clone_with_binder_body(),
                    constraints,
                );
                context.remove(variable);

                if *binder_type == BinderType::Product {
                    // Term is product.
                    constraints.push(PathTypeConstraint::TermIsProductType(focus_path.clone()));
                } else {
                    // Abstraction inhabits a product type.
                    constraints.push(PathTypeConstraint::TermInhabitsProductType {
                        term: focus_path.clone(),
                        inhabited_product_argument_type: focus_path
                            .clone_with_binder_argument_type(),
                        inhabited_product_return_type: focus_path.clone_with_binder_body(),
                    });
                }
            }
            Self::Application(box lhs, box rhs) => {
                let app_lhs_path = focus_path.clone_with_application_left();
                let app_rhs_path = focus_path.clone_with_application_right();
                lhs.init_constraints(context, &app_lhs_path, constraints);
                rhs.init_constraints(context, &app_rhs_path, constraints);

                match lhs {
                    Self::Variable(lhs_as_variable) => {
                        if let Some(lhs_variable_type) = context.get(lhs_as_variable) {
                            let binder_body_path = lhs_variable_type.clone_with_binder_body();
                            constraints.push(PathTypeConstraint::TermsInhabitSameType {
                                term_lhs: focus_path.clone(),
                                term_rhs: binder_body_path,
                            });
                            let binder_argument_type_path =
                                lhs_variable_type.clone_with_binder_argument_type();
                            let app_rhs_path = focus_path.clone_with_application_right();
                            constraints.push(PathTypeConstraint::TermInhabitsType {
                                term: app_rhs_path,
                                type_of_term: binder_argument_type_path,
                            });
                        }
                    }
                    Self::Binder(BinderType::Abstraction, box Binder(_, _, _)) => {
                        constraints.push(PathTypeConstraint::TermInhabitsType {
                            term: app_rhs_path.clone(),
                            type_of_term: app_lhs_path.clone_with_binder_argument_type(),
                        })
                    }
                    _ => {}
                }
            }
        }
    }
}

pub fn reduce_constraints_step(
    constraints: &[PathTypeConstraint],
) -> Vec<PathTypeConstraint> {
    let mut new_constraints = vec![];

    

    new_constraints
}
