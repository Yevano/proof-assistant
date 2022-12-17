use std::{collections::HashSet, fmt::Display, rc::Rc};

use crate::{term_writer::{BinderType, Universe, Variable, TermWriter, TermId, TermNode, Atom}, eval::free_variables};

/// A syntactic term.
pub enum Term {
    /// A placeholder for a welltyped expression.
    Hole,

    /// A sort. P if rank is zero, or U(rank) otherwise.
    Sort(Universe),

    /// A variable.
    Variable(Variable),

    /// A product type Πx:t.u or abstraction λx:t.y.
    Binder {
        binder_type: BinderType,
        variable: Variable,
        variable_type: Rc<Term>,
        body: Rc<Term>,
    },

    /// An application t1 t2.
    Application(Rc<Term>, Rc<Term>),
}

impl Term {
    pub fn free_variables(&self) -> HashSet<Variable> {
        match self {
            Term::Hole => HashSet::new(),
            Term::Sort(_) => HashSet::new(),
            Term::Variable(v) => {
                let v = v.to_owned();
                let mut set = HashSet::<Variable>::new();
                set.insert(v);
                set
            }
            Self::Binder {
                binder_type: _,
                variable,
                variable_type,
                body,
            } => {
                let mut set = variable_type.free_variables();
                set.extend(body.free_variables());
                set.remove(variable);
                set
            }
            Term::Application(e1, e2) => {
                let mut set = e1.free_variables();
                set.extend(e2.free_variables());
                set
            }
        }
    }

    pub fn from_atom(term_writer: &TermWriter, atom: &Atom) -> Term {
        match atom {
            Atom::Hole => Term::Hole,
            Atom::Sort(rank) => Term::Sort(*rank),
            Atom::TermId(term_id) => Term::from_term_node(term_writer, *term_id),
            Atom::BoundVariable(bound_variable_id) => {
                Term::Variable(term_writer.variable(*bound_variable_id).clone())
            }
        }
    }

    pub fn from_term_node(term_writer: &TermWriter, term_id: TermId) -> Term {
        match term_writer.term_node(term_id) {
            TermNode::Atom(atom) => match atom {
                Atom::Hole => Term::Hole,
                Atom::Sort(rank) => Term::Sort(*rank),
                Atom::TermId(term_id) => Term::from_term_node(term_writer, *term_id),
                Atom::BoundVariable(bound_variable_id) => {
                    Term::Variable(term_writer.variable(*bound_variable_id).clone())
                }
            },
            TermNode::Binder {
                binder_type,
                variable_binding,
                variable_type,
                body,
            } => {
                let binder_type = *binder_type;
                let body = Rc::new(Term::from_atom(term_writer, body));
                let variable = match variable_binding {
                    Some(bound_variable_id) => term_writer.variable(*bound_variable_id).clone(),
                    // None => Variable::from("_").freshen(&free_variables(body.as_ref())),
                    None => Variable::from("_"),
                };
                let variable_type = Rc::new(Term::from_atom(term_writer, variable_type));
                
                Term::Binder {
                    binder_type,
                    variable,
                    variable_type,
                    body,
                }
            }
            TermNode::Application { lhs, rhs } => {
                let function = Rc::new(Term::from_atom(term_writer, lhs));
                let argument = Rc::new(Term::from_atom(term_writer, rhs));
                Term::Application(function, argument)
            }
        }
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Hole => write!(f, "◻"),
            Self::Sort(rank) => write!(f, "{}", rank),
            Self::Variable(variable) => write!(f, "{}", variable),
            Self::Binder {
                binder_type: BinderType::Abstraction,
                variable,
                variable_type,
                body,
            } => {
                let fvs_in_body = body.free_variables();
                let variable_type = match variable_type.as_ref() {
                    Term::Binder { .. } => format!("({})", variable_type),
                    _ => format!("{}", variable_type),
                };
                // Check if variable is free in body.
                if fvs_in_body.contains(variable) {
                    write!(f, "λ{}:{}.{}", variable, variable_type, body)
                } else {
                    write!(f, "{} => {}", variable_type, body)
                }
            }
            Self::Binder {
                binder_type: BinderType::Product,
                variable,
                variable_type: type_,
                body,
            } => {
                let fvs_in_body = body.free_variables();
                let type_ = match type_.as_ref() {
                    Term::Binder { .. } => format!("({})", type_),
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
                let lhs = match a.as_ref() {
                    Term::Application(_, _) => format!("{}", a),
                    Term::Binder { .. } => format!("({})", a),
                    Term::Variable(_) => format!("{}", a),
                    _ => format!("({})", a),
                };
                let rhs = match b.as_ref() {
                    Self::Application(_, _) => format!("({})", b),
                    Self::Binder { .. } => format!("({})", b),
                    _ => format!("{}", b),
                };
                write!(f, "{} {}", lhs, rhs)
            }
        }
    }
}
