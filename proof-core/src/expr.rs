use std::{collections::HashSet, fmt::Display};

use crate::{types::Context, eval::free_variables};

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub struct Variable(String, Option<u32>);

#[derive(Eq, Hash, PartialEq, Clone, Debug, Copy)]
pub struct SortRank(u32);

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub struct Binder(pub Variable, pub Expression, pub Expression);

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub enum Expression {
    /// A placeholder for a welltyped expression.
    Hole,

    /// A sort. P if rank is zero, or U(rank) otherwise.
    Sort(SortRank),

    /// A variable.
    Variable(Variable),

    /// A product type Πx:t.u or abstraction λx:t.y.
    Binder(BinderType, Box<Binder>),

    /// An application t1 t2.
    Application(Box<Expression>, Box<Expression>),
}

#[derive(Eq, Hash, PartialEq, Clone, Debug, Copy)]
pub enum BinderType {
    /// A product type Πx:t.t.
    Product,

    /// An abstraction λx:t.t.
    Abstraction,
}

impl Variable {
    pub fn new(name: &str) -> Self {
        Self(name.to_string(), None)
    }

    pub fn new_with_ss(name: &str, index: u32) -> Self {
        Self(name.to_string(), Some(index))
    }

    pub fn subscript(&self) -> Option<u32> {
        self.1
    }

    pub fn set_subscript(&mut self, index: u32) {
        self.1 = Some(index);
    }

    /// Find a fresh variable name by appending a subscript to the given name, such that the new name does not collide with any of the given variables.
    pub fn freshen(&self, disallowed_names: &HashSet<Variable>) -> Variable {
        let mut new_name = self.clone();
        let mut i = new_name.subscript().unwrap_or(0);

        loop {
            i += 1;
            new_name.set_subscript(i);

            if !disallowed_names.contains(&new_name) {
                return new_name;
            }
        }
    }

    /// Find a fresh variable name by appending a subscript to the given name, such that the new name does not collide with the enclosing context.
    pub fn freshen_with_context(&self, context: &Context) -> Variable {
        let mut new_name = self.clone();
        let mut i = new_name.subscript().unwrap_or(0);
        let variables = context.variables();

        loop {
            i += 1;
            new_name.set_subscript(i);

            if !variables.contains(&new_name) {
                return new_name;
            }
        }
    }
}

impl SortRank {
    pub fn new(rank: u32) -> Self {
        Self(rank)
    }

    pub fn index(&self) -> u32 {
        self.0
    }
}

impl Expression {
    pub fn hole() -> Self {
        Self::Hole
    }

    pub fn sort(rank: u32) -> Self {
        Self::Sort(SortRank::new(rank))
    }

    pub fn variable(variable: &str) -> Self {
        Self::Variable(Variable::new(variable))
    }

    pub fn variable_ss(variable: &str, ss: u32) -> Self {
        Self::Variable(Variable::new_with_ss(variable, ss))
    }

    pub fn product(variable: Variable, type_: Expression, body: Expression) -> Self {
        Self::Binder(BinderType::Product, Box::new(Binder(variable, type_, body)))
    }

    pub fn arrow(type_: Expression, body: Expression) -> Self {
        Self::product(Variable::new("t"), type_, body)
    }

    pub fn abstraction(variable: Variable, type_: Expression, body: Expression) -> Self {
        Self::Binder(
            BinderType::Abstraction,
            Box::new(Binder(variable, type_, body)),
        )
    }

    pub fn binder(
        binder_type: BinderType,
        variable: Variable,
        type_: Expression,
        body: Expression,
    ) -> Self {
        match binder_type {
            BinderType::Product => Self::product(variable, type_, body),
            BinderType::Abstraction => Self::abstraction(variable, type_, body),
        }
    }

    pub fn application(function: Expression, argument: Expression) -> Self {
        Self::Application(Box::new(function), Box::new(argument))
    }
}

fn to_subscript(n: u32) -> String {
    let mut s = String::new();
    for c in n.to_string().chars() {
        s.push(match c {
            '0' => '₀',
            '1' => '₁',
            '2' => '₂',
            '3' => '₃',
            '4' => '₄',
            '5' => '₅',
            '6' => '₆',
            '7' => '₇',
            '8' => '₈',
            '9' => '₉',
            _ => unreachable!(),
        });
    }
    s
}

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)?;
        if let Some(ss) = self.1 {
            write!(f, "{}", to_subscript(ss))?;
        }
        Ok(())
    }
}

impl Display for BinderType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinderType::Product => write!(f, "Π"),
            BinderType::Abstraction => write!(f, "λ"),
        }
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Hole => write!(f, "◻"),
            Self::Sort(rank) => {
                if rank.index() == 0 {
                    write!(f, "*")
                } else {
                    write!(f, "𝒰{}", to_subscript(rank.index()))
                }
            }
            Self::Variable(variable) => write!(f, "{}", variable),
            Self::Binder(BinderType::Abstraction, box Binder(variable, type_, body)) => {
                let type_ = match type_ {
                    Expression::Binder(_, _) => format!("({})", type_),
                    _ => format!("{}", type_),
                };
                write!(
                    f,
                    "λ{}:{}.{}",
                    variable,
                    type_,
                    body
                )
            }
            Self::Binder(BinderType::Product, box Binder(variable, type_, body)) => {
                let fvs_in_body = free_variables(body);
                let type_ = match type_ {
                    Expression::Binder(_, _) => format!("({})", type_),
                    _ => format!("{}", type_),
                };
                // Check if variable is free in body.
                if fvs_in_body.contains(variable) {
                    write!(
                        f,
                        "Π{}:{}.{}",
                        variable,
                        type_,
                        body
                    )
                } else {
                    write!(f, "{} ⭆ {}", type_, body)
                }
            }
            Self::Application(function, argument) => {
                // Put parentheses around function if it is a binder. Put parentheses around argument if it is an application.
                let function = match function {
                    box Expression::Binder(_, _) => format!("({})", function),
                    _ => format!("{}", function),
                };
                let argument = match argument {
                    box Expression::Application(_, _) => format!("({})", argument),
                    _ => format!("{}", argument),
                };
                write!(f, "{} {}", function, argument)
            },
        }
    }
}

impl From<&str> for Variable {
    fn from(s: &str) -> Self {
        Self::new(s)
    }
}

impl From<&str> for Expression {
    fn from(s: &str) -> Self {
        Self::variable(s)
    }
}

impl From<Variable> for Expression {
    fn from(variable: Variable) -> Self {
        Self::variable(&variable.to_string())
    }
}