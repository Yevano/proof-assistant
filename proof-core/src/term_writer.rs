use std::{fmt::Display, collections::HashSet, mem};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Variable {
    pub name: String,
    pub subscript: Option<u32>,
}

impl Variable {
    pub fn new(name: &str, index: u32) -> Self {
        Self { name: name.to_string(), subscript: Some(index) }
    }

    /// Find a fresh variable name by appending a subscript to the given name, such that the new name does not collide with any of the given variables.
    pub fn freshen(&self, disallowed_names: &HashSet<Variable>) -> Variable {
        let mut new_name = self.clone();
        let mut i = new_name.subscript.unwrap_or(0);

        loop {
            i += 1;
            new_name.subscript = Some(i);

            if !disallowed_names.contains(&new_name) {
                return new_name;
            }
        }
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

impl From<&str> for Variable {
    fn from(name: &str) -> Self {
        Self { name: name.to_string(), subscript: None }
    }
}

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        if let Some(subscript) = self.subscript {
            write!(f, "{}", to_subscript(subscript))?;
        }
        Ok(())
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct Universe {
    index: u32,
}

impl Universe {
    pub fn new(index: u32) -> Self {
        Self { index }
    }

    pub fn zero() -> Self {
        Self::new(0)
    }

    pub fn succ(self) -> Self {
        Self::new(self.index + 1)
    }

    pub fn imax(self, other: Self) -> Self {
        if other == Self::zero() {
            self
        } else {
            self.max(other)
        }
    }
}

impl AsRef<u32> for Universe {
    fn as_ref(&self) -> &u32 {
        &self.index
    }
}

impl AsMut<u32> for Universe {
    fn as_mut(&mut self) -> &mut u32 {
        &mut self.index
    }
}

impl Display for Universe {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.index {
            0 => write!(f, "*"),
            _ => write!(f, "Type {}", self.index),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TermId {
    index: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BoundVariableId {
    index: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Atom {
    // A hole to be filled in
    Hole,

    // A sort Type u
    Sort(Universe),

    // A term id
    TermId(TermId),

    // A bound variable
    BoundVariable(BoundVariableId),
}

impl From<Universe> for Atom {
    fn from(universe: Universe) -> Self {
        Self::Sort(universe)
    }
}

impl From<TermId> for Atom {
    fn from(term_id: TermId) -> Self {
        Self::TermId(term_id)
    }
}

impl From<BoundVariableId> for Atom {
    fn from(bound_variable_id: BoundVariableId) -> Self {
        Self::BoundVariable(bound_variable_id)
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
struct TermList {
    // Maps variable ids to names.
    variables: Vec<Variable>,

    // Maps term ids to terms.
    term_nodes: Vec<TermNode>,

    // Maps variable ids to lists of term ids in which they occur.
    variable_occurrences: Vec<Vec<TermId>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinderType {
    Abstraction,
    Product,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TermNode {
    Atom(Atom),
    Binder {
        // The type of binder (abstraction or product)
        binder_type: BinderType,

        // The variable being bound, or none if the variable is unused
        variable_binding: Option<BoundVariableId>,
        variable_type: Atom,
        body: Atom,
    },
    Application {
        lhs: Atom,
        rhs: Atom,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TermPathNode {
    BinderVariableType,
    BinderBody,
    ApplicationLeft,
    ApplicationRight,
}

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct TermPath {
    nodes: Vec<TermPathNode>,
}

impl TermPath {
    pub fn new() -> Self {
        Self { nodes: Vec::new() }
    }

    pub fn iter(&self) -> impl Iterator<Item = &TermPathNode> {
        self.nodes.iter()
    }

    pub fn as_mut_ref(&mut self) -> &mut [TermPathNode] {
        &mut self.nodes
    }

    pub fn push(&mut self, node: TermPathNode) {
        self.nodes.push(node);
    }

    pub fn pop(&mut self) -> Option<TermPathNode> {
        self.nodes.pop()
    }
}

impl AsRef<[TermPathNode]> for TermPath {
    fn as_ref(&self) -> &[TermPathNode] {
        &self.nodes
    }
}

impl AsMut<[TermPathNode]> for TermPath {
    fn as_mut(&mut self) -> &mut [TermPathNode] {
        &mut self.nodes
    }
}

impl IntoIterator for TermPath {
    type Item = TermPathNode;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.nodes.into_iter()
    }
}

impl From<&[TermPathNode]> for TermPath {
    fn from(nodes: &[TermPathNode]) -> Self {
        Self {
            nodes: nodes.to_vec(),
        }
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct TermWriter {
    term_list: TermList,
}

impl TermWriter {
    pub fn new() -> Self {
        Self {
            term_list: TermList {
                variables: Vec::new(),
                term_nodes: Vec::new(),
                variable_occurrences: Vec::new(),
            },
        }
    }

    fn add_term(&mut self, term_node: TermNode) -> TermId {
        let term_id = TermId {
            index: self.term_list.term_nodes.len() as u32,
        };
        self.term_list.term_nodes.push(term_node);
        term_id
    }

    fn add_variable(&mut self, variable: Variable) -> BoundVariableId {
        let variable_id = BoundVariableId {
            index: self.term_list.variables.len() as u32,
        };
        self.term_list.variables.push(variable);
        self.term_list
            .variable_occurrences
            .push(Vec::new());
        variable_id
    }

    pub fn write_binder(
        &mut self,
        binder_type: BinderType,
        variable_binding: Option<Variable>,
        variable_type: Atom,
        body: Atom,
    ) -> (Option<BoundVariableId>, TermId) {
        let variable_id = variable_binding.map(|variable_binding| self.add_variable(variable_binding));
        let binder_id = self.add_term(TermNode::Binder {
            binder_type,
            variable_binding: variable_id,
            variable_type,
            body,
        });
        (variable_id, binder_id)
    }

    pub fn write_application(&mut self, lhs: Atom, rhs: Atom) -> TermId {
        self.add_term(TermNode::Application { lhs, rhs })
    }

    pub fn write_variable_occurrence(&mut self, variable_id: BoundVariableId) -> TermId {
        let term_id = self.add_term(TermNode::Atom(variable_id.into()));
        self.term_list
            .variable_occurrences
            .get_mut(variable_id.index as usize)
            .unwrap()
            .push(term_id);
        term_id
    }

    pub fn term_node(&self, term_id: TermId) -> &TermNode {
        &self.term_list.term_nodes[term_id.index as usize]
    }

    pub fn term_node_mut(&mut self, term_id: TermId) -> &mut TermNode {
        &mut self.term_list.term_nodes[term_id.index as usize]
    }

    pub fn variable(&self, variable_id: BoundVariableId) -> &Variable {
        &self.term_list.variables[variable_id.index as usize]
    }

    pub fn variable_mut(&mut self, variable_id: BoundVariableId) -> &mut Variable {
        &mut self.term_list.variables[variable_id.index as usize]
    }

    pub fn occurrences(&self, variable_id: BoundVariableId) -> &[TermId] {
        &self.term_list
            .variable_occurrences
            .get(variable_id.index as usize)
            .unwrap()
    }

    pub fn occurrences_mut(&mut self, variable_id: BoundVariableId) -> &mut Vec<TermId> {
        self.term_list
            .variable_occurrences
            .get_mut(variable_id.index as usize)
            .unwrap()
    }

    pub fn free_variables(&self, term_node: &TermNode) -> HashSet<BoundVariableId> {
        let mut free_variables = HashSet::<BoundVariableId>::new();
        // match term_node
        todo!()
    }

    pub fn replace_variable(&mut self, variable_to_replace: BoundVariableId, replacement: TermId) {
        let mut occurrence_ids = mem::take(self.occurrences_mut(variable_to_replace));
        for occurrence_id in occurrence_ids.as_slice() {
            let occurrence_node = self.term_node_mut(*occurrence_id);
            match occurrence_node {
                TermNode::Atom(atom) => {
                    if let Atom::BoundVariable(variable_id) = atom {
                        if *variable_id == variable_to_replace {
                            *atom = Atom::TermId(replacement);
                        }
                    }
                }
                TermNode::Binder {
                    variable_binding,
                    body,
                    ..
                } => {
                    if let Some(variable_id) = variable_binding {
                        if *variable_id == variable_to_replace {
                            *variable_binding = None;
                        }
                    }
                    if *body == Atom::BoundVariable(variable_to_replace) {
                        *body = Atom::TermId(replacement);
                    }
                }
                TermNode::Application { lhs, rhs } => {
                    if *lhs == Atom::BoundVariable(variable_to_replace) {
                        *lhs = Atom::TermId(replacement);
                    }
                    if *rhs == Atom::BoundVariable(variable_to_replace) {
                        *rhs = Atom::TermId(replacement);
                    }
                }
            }
        }
        mem::swap(self.occurrences_mut(variable_to_replace), &mut occurrence_ids);
    }
}