use std::{
    collections::HashMap,
    fmt::{Display, Formatter},
    rc::Rc,
};

use super::{
    arena::{Arena, ArenaRef},
    parse::{ExpressionTree, ParseTree},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinderType {
    Abstraction,
    Product,
}

impl Display for BinderType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BinderType::Abstraction => write!(f, "λ"),
            BinderType::Product => write!(f, "Π"),
        }
    }
}

pub enum TermNode {
    Sort(ArenaRef<SortNode>),
    Hole(ArenaRef<HoleNode>),
    Variable(ArenaRef<VariableNode>),
    Application(ArenaRef<ApplicationNode>),
    Binder(ArenaRef<BinderNode>),
}

pub struct SortNode {
    universe: u32,
}

pub struct HoleNode {
    name: String,
}

pub struct VariableNode {
    name: String,
}

pub struct ApplicationNode {
    applicant: ArenaRef<TermNode>,
    applicand: ArenaRef<TermNode>,
}

pub struct BinderNode {
    binder_type: BinderType,
    bound_name: Option<ArenaRef<VariableNode>>,
    binder_body: ArenaRef<TermNode>,
}

pub struct TermGraph {
    sorts: Arena<SortNode>,
    holes: Arena<HoleNode>,
    variables: Arena<VariableNode>,
    applications: Arena<ApplicationNode>,
    binders: Arena<BinderNode>,
    term_nodes: Arena<TermNode>,
}

impl TermGraph {
    pub fn new() -> Self {
        Self {
            sorts: Arena::new(),
            holes: Arena::new(),
            variables: Arena::new(),
            applications: Arena::new(),
            binders: Arena::new(),
            term_nodes: Arena::new(),
        }
    }

    pub fn term_from_tree(
        &mut self,
        tree: &ExpressionTree,
    ) -> Result<ArenaRef<TermNode>, TermFromTreeError> {
        self.term_from_tree_and_vars(tree, &mut HashMap::new())
    }

    pub fn term_from_tree_and_vars(
        &mut self,
        tree: &ExpressionTree,
        vars: &mut HashMap<String, ArenaRef<VariableNode>>,
    ) -> Result<ArenaRef<TermNode>, TermFromTreeError> {
        match tree {
            ExpressionTree::Hole(hole) => {
                let hole_node = self.new_hole(hole.ident().to_string().clone());
                Ok(self.new_term(TermNode::Hole(hole_node)))
            }
            ExpressionTree::Variable(variable) => {
                let variable_name = variable.ident().to_string();
                let variable_node = vars
                    .get(&variable_name)
                    .ok_or(TermFromTreeError::UnboundVariable(variable_name))?
                    .clone();
                Ok(self.new_term(TermNode::Variable(variable_node)))
            }
            ExpressionTree::Sort(sort) => {
                let sort_node = self.new_sort(sort.universe());
                Ok(self.new_term(TermNode::Sort(sort_node)))
            }
            ExpressionTree::Application(app) => {
                let applicant = self.term_from_tree_and_vars(app.applicant(), vars)?;
                let applicand = self.term_from_tree_and_vars(app.applicand(), vars)?;
                let application_node = self.new_application(applicant, applicand);
                Ok(self.new_term(TermNode::Application(application_node)))
            }
            ExpressionTree::Binder(binder) => {
                let name = binder.variable_name().to_string().clone();
                let bound_name = self.new_variable(name.clone());
                let old_name_ref = vars.get(&binder.variable_name().to_string()).cloned();
                vars.insert(name, bound_name);
                let binder_body = self.term_from_tree(&binder.body())?;
                if let Some(old_name) = old_name_ref {
                    vars.insert(binder.variable_name().to_string(), old_name.clone());
                } else {
                    vars.remove(&binder.variable_name().to_string());
                }
                let binder_type = binder.binder_type();
                let binder_node = self.new_binder(binder_type, Some(bound_name), binder_body);
                Ok(self.new_term(TermNode::Binder(binder_node)))
            }
            // A => B is the same as Π x : A. B where x ∉ FV(B)
            ExpressionTree::Arrow(arrow) => {
                let binder_body = self.term_from_tree_and_vars(&arrow.return_type(), vars)?;
                let binder_node = self.new_binder(BinderType::Product, None, binder_body);
                Ok(self.new_term(TermNode::Binder(binder_node)))
            }
        }
    }

    pub fn new_term(&mut self, term: TermNode) -> ArenaRef<TermNode> {
        self.term_nodes.alloc(term)
    }

    pub fn new_hole(&mut self, name: String) -> ArenaRef<HoleNode> {
        self.holes.alloc(HoleNode { name })
    }

    pub fn new_variable(&mut self, name: String) -> ArenaRef<VariableNode> {
        self.variables.alloc(VariableNode { name })
    }

    pub fn new_sort(&mut self, universe: u32) -> ArenaRef<SortNode> {
        self.sorts.alloc(SortNode { universe })
    }

    pub fn new_application(
        &mut self,
        applicant: ArenaRef<TermNode>,
        applicand: ArenaRef<TermNode>,
    ) -> ArenaRef<ApplicationNode> {
        self.applications.alloc(ApplicationNode {
            applicant,
            applicand,
        })
    }

    pub fn new_binder(
        &mut self,
        binder_type: BinderType,
        bound_name: Option<ArenaRef<VariableNode>>,
        binder_body: ArenaRef<TermNode>,
    ) -> ArenaRef<BinderNode> {
        self.binders.alloc(BinderNode {
            binder_type,
            bound_name,
            binder_body,
        })
    }
}

pub enum TermFromTreeError {
    InvalidTree,
    UnboundVariable(String),
}
