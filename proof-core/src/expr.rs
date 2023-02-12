use std::{collections::HashSet, fmt::Display};

use crate::{eval::free_variables, types::Context};

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub struct Variable(pub String, pub Option<u32>);

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

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)?;
        if let Some(ss) = self.1 {
            write!(f, "{}", to_subscript(ss))?;
        }
        Ok(())
    }
}

impl From<&str> for Variable {
    fn from(s: &str) -> Self {
        Self::new(s)
    }
}

#[derive(Eq, Hash, PartialEq, Clone, Debug, Copy)]
pub struct SortRank(pub u32);

impl SortRank {
    pub fn new(rank: u32) -> Self {
        Self(rank)
    }

    pub fn index(&self) -> u32 {
        self.0
    }

    pub fn succ(&self) -> Self {
        Self::new(self.0 + 1)
    }
}

impl Display for SortRank {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.index() == 0 {
            write!(f, "*")
        } else {
            write!(f, "𝒰{}", to_subscript(self.index()))
        }
    }
}

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub struct Binder(pub Variable, pub Expression, pub Expression);

#[derive(Eq, Hash, PartialEq, Clone, Debug, Copy)]
pub enum BinderType {
    /// A product type Πx:t.t.
    Product,

    /// An abstraction λx:t.t.
    Abstraction,
}

impl Display for BinderType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinderType::Product => write!(f, "Π"),
            BinderType::Abstraction => write!(f, "λ"),
        }
    }
}

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

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub struct MappedBinder<T>(
    pub Variable,
    pub MappedExpression<T>,
    pub MappedExpression<T>,
);

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub enum MappedExpression<T> {
    Hole(T),
    Sort(T, SortRank),
    Variable(T, Variable),
    Binder(T, BinderType, Box<MappedBinder<T>>),
    Application(T, Box<MappedExpression<T>>, Box<MappedExpression<T>>),
}

impl<T> MappedExpression<T> {
    pub fn attachment(&self) -> &T {
        match self {
            MappedExpression::Hole(a) => a,
            MappedExpression::Sort(a, _) => a,
            MappedExpression::Variable(a, _) => a,
            MappedExpression::Binder(a, _, _) => a,
            MappedExpression::Application(a, _, _) => a,
        }
    }
}

impl<T> From<MappedExpression<T>> for Expression {
    fn from(value: MappedExpression<T>) -> Self {
        match value {
            MappedExpression::Hole(_) => Expression::Hole,
            MappedExpression::Sort(_, a) => Expression::Sort(a),
            MappedExpression::Variable(_, a) => Expression::Variable(a),
            MappedExpression::Binder(_, a, box MappedBinder(b, c, d)) => {
                Expression::Binder(a, Binder(b, c.into(), d.into()).into())
            }
            MappedExpression::Application(_, box a, box b) => {
                Expression::Application(Box::new(a.into()), Box::new(b.into()))
            }
        }
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
        Self::product(
            Variable::new("t").freshen(&free_variables(&body)),
            type_,
            body,
        )
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

    pub fn map<T, F: Fn(&Expression) -> T>(&self, mapper: &F) -> MappedExpression<T> {
        let attachment = mapper(self);
        match self {
            Expression::Hole => MappedExpression::Hole(attachment),
            Expression::Sort(a) => MappedExpression::Sort(attachment, *a),
            Expression::Variable(a) => MappedExpression::Variable(attachment, a.clone()),
            Expression::Binder(a, box Binder(b, c, d)) => MappedExpression::Binder(
                attachment,
                *a,
                MappedBinder(b.clone(), c.map(mapper), d.map(mapper)).into(),
            ),
            Expression::Application(box a, box b) => MappedExpression::Application(
                attachment,
                a.map(mapper).into(),
                b.map(mapper).into(),
            ),
        }
    }

    pub fn walk<F: Fn(&Expression)>(&self, walker: &F) {
        walker(self);
        match self {
            Self::Binder(_, box Binder(_, c, d)) => {
                c.walk(walker);
                d.walk(walker);
            }
            Self::Application(box a, box b) => {
                a.walk(walker);
                b.walk(walker);
            }
            _ => {}
        }
    }

    pub fn path_ref(&self, path: &ExpressionPath) -> Option<&Self> {
        match (self, path.as_ref()) {
            (_, []) => Some(self),
            (
                Self::Binder(_, box Binder(_, a, _)),
                [ExpressionPathPart::BinderArgumentType, end @ ..],
            ) => a.path_ref(&ExpressionPath::new(end)),
            (Self::Binder(_, box Binder(_, _, a)), [ExpressionPathPart::BinderBody, end @ ..]) => {
                a.path_ref(&ExpressionPath::new(end))
            }
            (Self::Application(box a, _), [ExpressionPathPart::ApplicationLeft, end @ ..]) => {
                a.path_ref(&ExpressionPath::new(end))
            }
            (Self::Application(_, box a), [ExpressionPathPart::ApplicationRight, end @ ..]) => {
                a.path_ref(&ExpressionPath::new(end))
            }
            _ => None,
        }
    }

    pub fn collect_paths_into(
        &self,
        parent_path: &ExpressionPath,
        paths: &mut Vec<ExpressionPath>,
    ) {
        paths.push(parent_path.clone());
        match self {
            Expression::Binder(_, box Binder(_, a, b)) => {
                a.collect_paths_into(&parent_path.clone_with_binder_argument_type(), paths);
                b.collect_paths_into(&parent_path.clone_with_binder_body(), paths);
            }
            Expression::Application(box a, box b) => {
                a.collect_paths_into(&parent_path.clone_with_application_left(), paths);
                b.collect_paths_into(&parent_path.clone_with_application_right(), paths);
            }
            _ => {}
        }
    }
}

const PRETTY_IFF: bool = false;
const PRETTY_AND: bool = false;
const PRETTY_OR: bool = false;
const PRETTY_NOT: bool = false;
const PRETTY_BOT: bool = false;

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Hole => write!(f, "◻"),
            Self::Sort(rank) => write!(f, "{}", rank),
            Self::Variable(variable) => write!(f, "{}", variable),
            // Πγ:*.((A => B) => (B => A) => γ) => γ
            Self::Binder(
                BinderType::Product,
                box Binder(
                    c1,
                    // *
                    Self::Sort(SortRank(0)),
                    // ((A => B) => (B => A) => γ) => γ
                    Self::Binder(
                        BinderType::Product,
                        box Binder(
                            _,
                            // (A => B) => (B => A) => γ
                            Self::Binder(
                                BinderType::Product,
                                box Binder(
                                    _,
                                    // (A => B)
                                    Self::Binder(
                                        BinderType::Product,
                                        box Binder(
                                            _,
                                            // A
                                            a1,
                                            // B
                                            b1,
                                        ),
                                    ),
                                    // (B => A) => γ
                                    Self::Binder(
                                        BinderType::Product,
                                        box Binder(
                                            _,
                                            // (B => A)
                                            Self::Binder(
                                                BinderType::Product,
                                                box Binder(
                                                    _,
                                                    // B
                                                    b2,
                                                    // A
                                                    a2,
                                                ),
                                            ),
                                            // γ
                                            Self::Variable(c2),
                                        ),
                                    ),
                                ),
                            ),
                            // γ
                            Self::Variable(c3),
                        ),
                    ),
                ),
            ) if PRETTY_IFF && c1 == c2 && c2 == c3 && a1 == a2 && b1 == b2 => {
                write!(f, "({}) <=> ({})", a1, b1)
            }
            // Πγ:*.(α => β => γ) => γ
            // Writes α ∧ β.
            Self::Binder(
                BinderType::Product,
                box Binder(
                    c1,
                    // *
                    Self::Sort(SortRank(0)),
                    // (α => β => γ) => γ
                    Self::Binder(
                        BinderType::Product,
                        box Binder(
                            _,
                            // α => β => γ
                            Self::Binder(
                                BinderType::Product,
                                box Binder(
                                    _,
                                    // α
                                    a1,
                                    // β => γ
                                    Self::Binder(
                                        BinderType::Product,
                                        box Binder(
                                            _,
                                            // β
                                            b1,
                                            // γ
                                            Self::Variable(c2),
                                        ),
                                    ),
                                ),
                            ),
                            // γ
                            Self::Variable(c3),
                        ),
                    ),
                ),
            ) if PRETTY_AND && c1 == c2 && c2 == c3 => write!(f, "({}) ∧ ({})", a1, b1),

            // Πγ:*.(α => γ) => (β => γ) => γ
            // Writes α ∨ β.
            Self::Binder(
                BinderType::Product,
                box Binder(
                    c1,
                    // *
                    Self::Sort(SortRank(0)),
                    // (α => γ) => (β => γ) => γ
                    Self::Binder(
                        BinderType::Product,
                        box Binder(
                            _,
                            // α => γ
                            Self::Binder(
                                BinderType::Product,
                                box Binder(
                                    _,
                                    // α
                                    a1,
                                    // γ
                                    Self::Variable(c2),
                                ),
                            ),
                            // (β => γ) => γ
                            Self::Binder(
                                BinderType::Product,
                                box Binder(
                                    _,
                                    // β => γ
                                    Self::Binder(
                                        BinderType::Product,
                                        box Binder(
                                            _,
                                            // β
                                            b1,
                                            // γ
                                            Self::Variable(c3),
                                        ),
                                    ),
                                    // γ
                                    Self::Variable(c4),
                                ),
                            ),
                        ),
                    ),
                ),
            ) if PRETTY_OR && c1 == c2 && c2 == c3 && c3 == c4 => write!(f, "({}) ∨ ({})", a1, b1),

            // α => Πβ:*.β
            // Writes ¬α.
            Self::Binder(
                BinderType::Product,
                box Binder(
                    _,
                    // α
                    a1,
                    // Πβ:*.β
                    Self::Binder(
                        BinderType::Product,
                        box Binder(
                            b1,
                            // *
                            Self::Sort(SortRank(0)),
                            // β
                            Self::Variable(b2),
                        ),
                    ),
                ),
            ) if PRETTY_NOT && b1 == b2 => write!(f, "¬({})", a1),

            // Πα:*.α
            // Writes ⊥.
            Self::Binder(
                BinderType::Product,
                box Binder(
                    a1,
                    // *
                    Self::Sort(SortRank(0)),
                    // α
                    Self::Variable(a2),
                ),
            ) if PRETTY_BOT && a1 == a2 => write!(f, "⊥"),

            Self::Binder(BinderType::Abstraction, box Binder(variable, type_, body)) => {
                let type_ = match type_ {
                    Expression::Binder(_, _) => format!("({})", type_),
                    _ => format!("{}", type_),
                };
                write!(f, "λ{}:{}.{}", variable, type_, body)
            }
            Self::Binder(BinderType::Product, box Binder(variable, type_, body)) => {
                let fvs_in_body = free_variables(body);
                let type_ = match type_ {
                    Expression::Binder(_, _) => format!("({})", type_),
                    _ => format!("{}", type_),
                };
                // Check if variable is free in body.
                if fvs_in_body.contains(variable) {
                    write!(f, "Π{}:{}.{}", variable, type_, body)
                } else {
                    write!(f, "{} => {}", type_, body)
                }
            }

            Self::Application(a, b) => {
                let lhs = match (*a).clone() {
                    box Expression::Application(_, _) => format!("{}", a),
                    box Expression::Binder(_, _) => format!("({})", a),
                    box Expression::Variable(_) => format!("{}", a),
                    _ => format!("({})", a),
                };
                let rhs = match b {
                    box Self::Application(_, _) => format!("({})", b),
                    box Self::Binder(_, _) => format!("({})", b),
                    _ => format!("{}", b),
                };
                write!(f, "{} {}", lhs, rhs)
            }
        }
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

pub enum PrettyExpression {
    /// <=> operator.
    Iff(Box<PrettyExpression>, Box<PrettyExpression>),

    /// Normal expression.
    Normal(Expression),
}

impl Display for PrettyExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Iff(a, b) => write!(f, "({}) <=> ({})", a, b),
            PrettyExpression::Normal(e) => write!(f, "{}", e),
        }
    }
}

impl From<Expression> for PrettyExpression {
    fn from(_expression: Expression) -> Self {
        todo!()
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

#[derive(Debug, Clone, Copy)]
pub enum ExpressionPathPart {
    Parent,
    BinderArgumentType,
    BinderBody,
    ApplicationLeft,
    ApplicationRight,
}

impl Display for ExpressionPathPart {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            ExpressionPathPart::Parent => "..",
            ExpressionPathPart::BinderArgumentType => "arg-type",
            ExpressionPathPart::BinderBody => "body",
            ExpressionPathPart::ApplicationLeft => "left",
            ExpressionPathPart::ApplicationRight => "right",
        };
        write!(f, "{}", s)
    }
}

#[derive(Debug, Clone)]
pub struct ExpressionPath {
    parts: Vec<ExpressionPathPart>,
}

impl ExpressionPath {
    pub fn new(parts: &[ExpressionPathPart]) -> Self {
        Self {
            parts: parts.into(),
        }
    }

    pub fn parent(&self) -> Option<Self> {
        match &self.parts[..] {
            [] => None,
            [start @ .., _] => Some(Self::new(start)),
        }
    }

    pub fn push(&mut self, path_part: ExpressionPathPart) {
        self.parts.push(path_part);
    }

    pub fn push_parent(&mut self) {
        self.parts.push(ExpressionPathPart::Parent)
    }

    pub fn push_binder_argument_type(&mut self) {
        self.parts.push(ExpressionPathPart::BinderArgumentType)
    }

    pub fn push_binder_body(&mut self) {
        self.parts.push(ExpressionPathPart::BinderBody)
    }

    pub fn push_application_left(&mut self) {
        self.parts.push(ExpressionPathPart::ApplicationLeft)
    }

    pub fn push_application_right(&mut self) {
        self.parts.push(ExpressionPathPart::ApplicationRight)
    }

    pub fn clone_with_parent(&self) -> Self {
        let mut parts = self.parts.clone();
        parts.push(ExpressionPathPart::Parent);
        Self::new(&parts)
    }

    pub fn clone_with_binder_argument_type(&self) -> Self {
        let mut parts = self.parts.clone();
        parts.push(ExpressionPathPart::BinderArgumentType);
        Self::new(&parts)
    }

    pub fn clone_with_binder_body(&self) -> Self {
        let mut parts = self.parts.clone();
        parts.push(ExpressionPathPart::BinderBody);
        Self::new(&parts)
    }

    pub fn clone_with_application_left(&self) -> Self {
        let mut parts = self.parts.clone();
        parts.push(ExpressionPathPart::ApplicationLeft);
        Self::new(&parts)
    }

    pub fn clone_with_application_right(&self) -> Self {
        let mut parts = self.parts.clone();
        parts.push(ExpressionPathPart::ApplicationRight);
        Self::new(&parts)
    }

    pub fn join(&self, other_path: &Self) -> Self {
        let mut new_path = vec![];
        for part in other_path.parts.clone().into_iter() {
            if let ExpressionPathPart::Parent = part {
                new_path.pop();
            } else {
                new_path.push(part);
            }
        }
        Self::new(&new_path)
    }

    pub fn join_mut(&mut self, mut other_path: Self) {
        self.parts.append(&mut other_path.parts);
    }
}

impl AsRef<[ExpressionPathPart]> for ExpressionPath {
    fn as_ref(&self) -> &[ExpressionPathPart] {
        &self.parts
    }
}

impl Display for ExpressionPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self
            .parts
            .iter()
            .map(|p| format!("{}", p))
            .intersperse("/".to_string())
            .collect::<String>();
        write!(f, "/{}", s)
    }
}
