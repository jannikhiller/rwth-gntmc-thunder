use bit_vec::BitVec;
use itertools::Either;
use log::*;
use std::cmp::max;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::hash::Hash;

use crate::common::sparse_matrix::{SparseMatrix, SparseMatrixElement};

#[derive(Debug, Clone)]
pub enum PropertyType<ValueType> {
    Invariant(FormulaTreeNode<ValueType>),
    Persistence(FormulaTreeNode<ValueType>),
    RegularSafety(FiniteAutomaton<ValueType>),
    OmegaRegular(FiniteAutomaton<ValueType>),
    Ltl(FormulaTreeNode<ValueType>),
}

/// A tree structure representing a property with logical expressions.
///
/// The `Property` contains a root node (`FormulaTreeNode`), a type of property
/// (`PropertyType`), and a name to identify the property.
#[derive(Debug)]
pub struct Property<ValueType> {
    /// The type of property represented by this tree.
    pub property_type: PropertyType<ValueType>,
    /// The name of the property.
    pub name: String,
}

/// Creates a new `Property` with a given name, property type, and root node.
/// The given `ValueType` specifies the datatype of the label.
///
/// # Parameters
/// - `name`: A `String` representing the name of the property.
/// - `property_type`: The `PropertyType` specifying the type of the property.
/// - `root`: The root `FormulaTreeNode` of the tree.
///
/// # Returns
/// - A new instance of `Property`.
impl Property<String> {
    /// Creates a new `Property` with a given name, property type, and root node.
    ///
    /// # Parameters
    /// - `name`: A `String` representing the name of the property.
    /// - `property_type`: The `PropertyType` specifying the type of the property.
    /// - `root`: The root `FormulaTreeNode` of the tree.
    ///
    /// # Returns
    /// - A new instance of `Property`.
    pub fn new(name: String, property_type: PropertyType<String>) -> Self {
        Property {
            name,
            property_type,
        }
    }

    /// Evaluates the property tree against a list of labels.
    ///
    /// This function evaluates the logical expression defined by the property tree,
    /// using the `labels` vector as input to determine the result.
    ///
    /// # Parameters
    /// - `labels`: A vector of `String` labels representing the atomic propositions of the state.
    ///
    /// # Returns
    /// - A `bool` representing the result of the evaluation.
    ///
    /// # Panics
    /// - If nodes required for the evaluation are missing in the tree.
    pub fn evaluate(&self, labels: &Vec<String>) -> bool {
        trace!(
            "Evaluating property {:?} of kind {:?}",
            self.name,
            self.property_type
        );
        match &self.property_type {
            PropertyType::Invariant(formula) | PropertyType::Persistence(formula) => {
                formula.evaluate(labels)
            }
            PropertyType::OmegaRegular(_) | PropertyType::RegularSafety(_) => panic!(
                "This is an automaton property, use the automatons member functions instead."
            ),
            PropertyType::Ltl(_) => {
                panic!("This is a ltl property, which is used to create a GNBA and not to evaluate")
            }
        }
    }

    /// Negates the given property and makes sure that no double-negations are inside the formula
    /// tree. At this point, we assume that only the `AND`, `NOT`, `NEXT`, and `UNTIL` operators are
    /// present in the formula tree.
    ///
    /// # Panics
    /// - If the given property is not of type LTL.
    pub fn negate(&mut self) {
        match &mut self.property_type {
            PropertyType::Invariant(_)
            | PropertyType::Persistence(_)
            | PropertyType::OmegaRegular(_)
            | PropertyType::RegularSafety(_) => {
                panic!("Negation of a property is currently only allowed for LTL properties.")
            }
            PropertyType::Ltl(formula_tree_node) => {
                debug!("Before adding negation: \n{}", formula_tree_node);
                // if the formula tree starts with one or more `NOT`'s, then we have to handle this
                // accordingly when negating the whole formula
                Property::handle_leading_nots_when_negating_from_root(formula_tree_node);
                debug!("After adding negation: \n{}", formula_tree_node);

                debug!("Before removing double negations: \n{}", formula_tree_node);
                // remove remaining double negations recursively
                formula_tree_node.remove_double_negations();
                debug!("After removing double negations: \n{}", formula_tree_node);
            }
        }
    }

    fn handle_leading_nots_when_negating_from_root(
        formula_tree_node: &mut FormulaTreeNode<String>,
    ) {
        let mut number_of_nots = 0; // no leading `NOT` nodes in the beginning
        let mut current_node = Some(Box::new(formula_tree_node.clone()));
        if FormulaTreeNodeType::Not == formula_tree_node.node_type {
            current_node = formula_tree_node.left.clone();
            number_of_nots += 1; // here we include the root node

            // count the number of consecutive `NOT`s starting from the root
            while current_node.is_some()
                && current_node.as_ref().unwrap().node_type == FormulaTreeNodeType::Not
            {
                number_of_nots += 1;
                current_node = current_node.clone().unwrap().left;
            }
        }

        if number_of_nots % 2 == 0 {
            // if we have an even number of `NOT` nodes, then one single `NOT` node
            // is sufficient to add, while omitting all others from the formula tree
            // create `NOT` node as new root
            let not_node = FormulaTreeNode::new(
                Some(Box::new(*current_node.clone().unwrap())),
                None,
                None,
                FormulaTreeNodeType::Not,
            );

            // replace the original formula tree with the new `NOT` node
            *formula_tree_node = not_node;
        } else {
            // if we have an odd number of `NOT` nodes, then we can omit them all,
            // as they would have been resolved when removing double negations
            *formula_tree_node = *current_node.clone().unwrap();
        }
    }
}

/// A node in a `FormulaTreeNode` representing a logical expression or label.
///
/// Each node can represent different logical operations (e.g. `AND`, `OR`, `NOT`) or a single
/// atomic label. Nodes can have left and right children to build expressions recursively.
/// The given `ValueType` specifies the datatype of the label.
#[derive(Debug, Default, Clone, PartialEq)]
pub struct FormulaTreeNode<ValueType> {
    /// The left child of this node (if any).
    left: Option<Box<FormulaTreeNode<ValueType>>>,
    /// The right child of this node (if any).
    right: Option<Box<FormulaTreeNode<ValueType>>>,
    /// An optional label for atomic expressions.
    label: Option<ValueType>,
    /// The type of operation or node this represents.
    node_type: FormulaTreeNodeType,
}

impl FormulaTreeNode<String> {
    pub fn new(
        left: Option<Box<FormulaTreeNode<String>>>,
        right: Option<Box<FormulaTreeNode<String>>>,
        label: Option<String>,
        node_type: FormulaTreeNodeType,
    ) -> Self {
        FormulaTreeNode {
            left,
            right,
            label,
            node_type,
        }
    }

    /// Recursively evaluates this node and its children based on the provided labels.
    /// Note that for NOT nodes only the left child will get evaluated.
    ///
    /// # Parameters
    /// - `labels`: A vector of `String` labels representing the atomic propositions of the state.
    ///
    /// # Returns
    /// - A `bool` representing the result of the evaluation.
    ///
    /// # Panics
    /// - If nodes required for the evaluation are missing in the tree.
    fn evaluate(&self, labels: &Vec<String>) -> bool {
        trace!("Evaluating subformula of type {:?}", self.node_type);
        match self.node_type {
            FormulaTreeNodeType::And => {
                if self.left.as_ref().is_none() {
                    panic!(
                        "Missing left node when evaluating AND expression! \
                        Your formula tree is most likely invalid."
                    );
                } else if self.right.as_ref().is_none() {
                    panic!(
                        "Missing right node when evaluating AND expression! \
                        Your formula tree is most likely invalid."
                    );
                }

                self.left.as_ref().unwrap().evaluate(labels)
                    && self.right.as_ref().unwrap().evaluate(labels)
            }
            FormulaTreeNodeType::Or => {
                if self.left.as_ref().is_none() {
                    panic!(
                        "Missing left node when evaluating OR expression! \
                        Your formula tree is most likely invalid."
                    );
                } else if self.right.as_ref().is_none() {
                    panic!(
                        "Missing right node when evaluating OR expression! \
                        Your formula tree is most likely invalid."
                    );
                }

                self.left.as_ref().unwrap().evaluate(labels)
                    || self.right.as_ref().unwrap().evaluate(labels)
            }
            FormulaTreeNodeType::Not => self.left.as_ref().map_or_else(
                || {
                    panic!(
                        "Missing left node when evaluating NOT expression! \
                    Your formula tree is most likely invalid."
                    );
                },
                |l| !l.evaluate(labels),
            ),
            FormulaTreeNodeType::Atomic => {
                if self.label.as_ref().is_none() {
                    labels.is_empty()
                } else {
                    labels.contains(self.label.as_ref().unwrap())
                }
            }
            FormulaTreeNodeType::True => true,
            FormulaTreeNodeType::Until => {
                panic!("This operator is only used for LTL. Thus, no evaluation.")
            }
            FormulaTreeNodeType::Next => {
                panic!("This operator is only used for LTL. Thus, no evaluation.")
            }
        }
    }

    /// Traverses the formula tree in post order and applies the given function to each node.
    ///
    /// # Parameters
    /// - `f`: The function that shall be applied.
    fn post_order_traversal<F>(&self, f: &mut F)
    where
        F: FnMut(&Self),
    {
        if let Some(left) = &self.left {
            left.post_order_traversal(f);
        }
        if let Some(right) = &self.right {
            right.post_order_traversal(f);
        }
        f(self);
    }

    /// Recursively removes all double negations from this formula tree. We assume that the current
    /// node is not a `NOT` node.
    ///
    /// # Returns
    /// - A `bool` representing the result of the evaluation.
    fn remove_double_negations(&mut self) {
        if let FormulaTreeNodeType::Atomic = self.node_type {
            // reached a leaf node, return
            return;
        }

        // check if there is a left child and if it is also a `NOT` node
        if let Some(left_child) = self.left.as_ref() {
            if FormulaTreeNodeType::Not == left_child.node_type {
                // check if it is followed by another `NOT` node
                if let Some(child_of_left_child) = left_child.left.as_ref() {
                    if let FormulaTreeNodeType::Not = child_of_left_child.node_type {
                        // found two consecutive `NOT` nodes
                        self.left = child_of_left_child.left.clone();
                    }
                }
            }
        }

        // check if there is a right child and if it is also a `NOT` node
        if let Some(right_child) = self.right.as_ref() {
            if let FormulaTreeNodeType::Not = right_child.node_type {
                // check if it is followed by another `NOT` node
                if let Some(child_of_right_child) = right_child.left.as_ref() {
                    if let FormulaTreeNodeType::Not = child_of_right_child.node_type {
                        // found two consecutive `NOT` nodes
                        self.right = child_of_right_child.left.clone();
                    }
                }
            }
        }

        if self.left.is_some() {
            self.left.as_mut().unwrap().remove_double_negations();
        }

        if self.right.is_some() {
            self.right.as_mut().unwrap().remove_double_negations();
        }
    }

    /// Recursively formats the formula tree as an ASCII tree for display purposes.
    ///
    /// # Parameters
    /// - `f`: A mutable reference to a `fmt::Formatter`, which handles the formatted output.
    /// - `depth`: The current depth of the node in the tree, used to determine the level
    ///   of indentation for visualizing the hierarchy.
    ///
    /// # Returns
    /// - A `fmt::Result` indicating whether the formatting was successful.
    fn fmt_with_depth(&self, f: &mut fmt::Formatter<'_>, depth: usize) -> fmt::Result {
        // create an indentation based on the depth
        let indent = "    ".repeat(depth);
        let node_repr = match self.node_type {
            FormulaTreeNodeType::And => "AND",
            FormulaTreeNodeType::Or => "OR",
            FormulaTreeNodeType::Not => "NOT",
            FormulaTreeNodeType::Atomic => self.label.as_deref().unwrap_or("Atomic(None)"),
            FormulaTreeNodeType::True => "TRUE",
            FormulaTreeNodeType::Until => "UNTIL",
            FormulaTreeNodeType::Next => "NEXT",
        };

        // write the current node's representation
        writeln!(f, "{}└── {}", indent, node_repr)?;

        // recursively format the left child if it exists
        if let Some(left) = &self.left {
            left.fmt_with_depth(f, depth + 1)?;
        }

        // recursively format the right child if it exists
        if let Some(right) = &self.right {
            right.fmt_with_depth(f, depth + 1)?;
        }

        Ok(())
    }
}

impl fmt::Display for FormulaTreeNode<String> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Start with the root node
        self.fmt_with_depth(f, 0)
    }
}

/// Represents the type of node within a `FormulaTreeNode`.
///
/// This enum defines the possible logical operations or atomic values that a node can represent,
/// including `AND`, `OR`, `NOT`, and `ATOMIC`.
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, Hash)]
pub enum FormulaTreeNodeType {
    And,
    Or,
    Not,
    //ltl-types
    Next,
    Until,
    #[default]
    Atomic,
    True,
}

#[derive(Debug, Copy, Clone)]
pub enum AcceptanceType {
    /// An NFA accepts once it reaches a final state.
    Nfa,
    /// A Buchi automaton accepts if accepting states are reached infinitely
    /// often.
    Buchi,
}

/// A finite automaton that can be used to represent regular safety or omega-regular properties.
#[derive(Debug, Clone)]
pub struct FiniteAutomaton<ValueType> {
    /// The type of acceptance for this automaton.
    acceptance: AcceptanceType,
    /// The transition matrix of the automaton.
    transition_matrix: SparseMatrix<Vec<FormulaTreeNode<ValueType>>>,
    /// Highest state index in the automaton.
    last_state: usize,
    /// The initial state of the automaton represented as element of the powerset of indexes
    initial_state: BitVec,
    /// The accepting states of the automaton.
    accepting_states: BitVec,
}

impl FiniteAutomaton<String> {
    pub fn new(
        acceptance: AcceptanceType,
        transition_matrix: SparseMatrix<Vec<FormulaTreeNode<String>>>,
        last_state: usize,
        initial_state: BitVec,
        accepting_states: BitVec,
    ) -> Self {
        FiniteAutomaton {
            acceptance,
            transition_matrix,
            last_state,
            initial_state,
            accepting_states,
        }
    }
    #[allow(dead_code)]
    pub fn is_accepting(&self, state: BitVec) -> bool {
        let mut res = state;
        res.and(&self.accepting_states);
        res.any()
    }

    #[allow(dead_code)]
    pub fn step(&mut self, state: BitVec, label: &Vec<String>) -> BitVec {
        let get_successors_of_index = |index: usize| {
            self.transition_matrix
                .get_row(index)
                .into_iter()
                .map(|SparseMatrixElement { col_index, value }| {
                    value.into_iter().map(move |tree| (tree, col_index))
                })
                .flatten()
        };

        let state_successors = state
            .into_iter()
            .enumerate()
            .filter_map(|(i, value)| if value { Some(i) } else { None })
            .map(get_successors_of_index)
            .flatten();

        let mut new_state = BitVec::from_elem(self.last_state + 1, false);
        for (tree, col_index) in state_successors {
            if tree.evaluate(label) {
                new_state.set(col_index, true);
            }
        }
        new_state
    }

    #[allow(dead_code)]
    pub fn get_initial_state(&self) -> &BitVec {
        &self.initial_state
    }

    #[allow(dead_code)]
    pub fn get_last_state(&self) -> usize {
        self.last_state
    }

    #[allow(dead_code)]
    pub fn get_acceptance_type(&self) -> AcceptanceType {
        self.acceptance
    }

    pub fn get_accepting_states(&self) -> &BitVec {
        &self.accepting_states
    }
}

/// Internal struct to handle elements of the closure during the computation of elementary sets
/// in a more succinct and compact way.
#[derive(Eq, Hash, PartialEq, Debug, Clone)]
struct ElementaryNode {
    is_atomic: bool,
    // Either the index in the BitVec or the Node representing a negation (not part of closure bitvec)
    left_value: Either<usize, Box<ElementaryNode>>,
    right_value: Either<usize, Box<ElementaryNode>>,
    operator: FormulaTreeNodeType,
    formula: String,
}

impl ElementaryNode {
    pub fn new(
        is_atomic: bool,
        left_value: Either<usize, Box<ElementaryNode>>,
        right_value: Either<usize, Box<ElementaryNode>>,
        operator: FormulaTreeNodeType,
        formula: String,
    ) -> Self {
        Self {
            is_atomic,
            left_value,
            right_value,
            operator,
            formula,
        }
    }

    fn set_left_value(&mut self, left_value: Either<usize, Box<ElementaryNode>>) {
        self.left_value = left_value;
    }

    fn set_right_value(&mut self, right_value: Either<usize, Box<ElementaryNode>>) {
        self.right_value = right_value;
    }

    /// Derives the value of this node according to the given `state` where this node is expected
    /// to be at the given `index`. The value is derived such that it is *maximally* and *locally*
    /// consistent. If it is not possible to derive a value, all possibilities are returned.
    ///
    /// # Parameters
    /// - `state`: The state from which the value shall be derived.
    /// - `index`: The index that represents this node. I.e., the index to which the result shall be written.
    fn derive(self, mut state: BitVec, index: usize) -> Vec<BitVec> {
        /// Helper function that derives the value of a given sub formula. I.e. this handles the `Either`.
        fn compute_value(
            sub_form: Either<usize, Box<ElementaryNode>>,
            state: &BitVec,
            err_msg: &str,
        ) -> bool {
            match sub_form {
                Either::Left(index) => state.get(index).expect(err_msg),
                Either::Right(node) => !compute_value(node.left_value, state, err_msg),
            }
        }

        let err_msg = "Index out of bounds during elementary subset computation";
        let value_of = |sub_form: Either<usize, Box<ElementaryNode>>| -> bool {
            compute_value(sub_form, &state, err_msg)
        };

        match self.operator {
            FormulaTreeNodeType::True => {
                state.set(index, true);
                vec![state]
            }
            FormulaTreeNodeType::Atomic => {
                let mut new_state = state.clone();
                state.set(index, false);
                new_state.set(index, true);
                vec![state, new_state]
            }
            FormulaTreeNodeType::Next => {
                let mut new_state = state.clone();
                state.set(index, false);
                new_state.set(index, true);
                vec![state, new_state]
            }
            FormulaTreeNodeType::Not => {
                state.set(index, !value_of(self.left_value));
                vec![state]
            }
            FormulaTreeNodeType::Until => {
                if value_of(self.right_value) {
                    state.set(index, true);
                    vec![state]
                } else if !value_of(self.left_value) {
                    state.set(index, false);
                    vec![state]
                } else {
                    let mut new_state = state.clone();
                    state.set(index, false);
                    new_state.set(index, true);
                    vec![state, new_state]
                }
            }
            FormulaTreeNodeType::And => {
                state.set(
                    index,
                    value_of(self.left_value) && value_of(self.right_value),
                );
                vec![state]
            }
            _ => panic!("Only and, not, next and until are allowed in elementary subsets"),
        }
    }
}

/// Computes the elementary sets of a given LTL property. I.e. all maximally and locally consistent
/// subsets of its closure. Only positive elements are considered.
/// Note: This only works for LTL-formulae.
///
/// # Parameters
/// - `property`: The Property for which the elementary sets shall be computed.
///
/// # Returns
/// - A HashMap that maps from the indices of the bitvecs to the represented formula.
/// - A vector of bitvecs each representing an elementary set. If `true` is contained in the
///   given formula, it is also contained in the binary sets.
///
/// # Panics
/// If the given property is not an LTL-formula.
pub fn comp_elementary_sets(
    property: &Property<String>,
) -> (HashMap<usize, FormulaTreeNode<String>>, Vec<BitVec>) {
    let formula = match &property.property_type {
        PropertyType::Ltl(formula) => formula,
        _ => panic!("Cannot compute elementary sets of something other than an LTL formula."),
    };

    trace!("Computing elementary sets for formula {}", formula);

    let mut closure_formula_indices: HashMap<String, usize> = HashMap::new();
    let mut indices_to_formula: HashMap<usize, FormulaTreeNode<String>> = HashMap::new();
    let mut closure: Vec<ElementaryNode> = Vec::new();
    let mut not_nodes: HashMap<String, ElementaryNode> = HashMap::new();

    // Traverse the formula to capture all nodes and map them into the intermediate struct (`ElementaryNode`)
    FormulaTreeNode::post_order_traversal(&formula, &mut |node: &FormulaTreeNode<String>| {
        let is_atomic = node.node_type == FormulaTreeNodeType::True
            || node.node_type == FormulaTreeNodeType::Atomic
            || node.node_type == FormulaTreeNodeType::Next;

        if node.node_type != FormulaTreeNodeType::Not {
            let insert = closure_formula_indices.insert(node.to_string(), closure.len());
            // As `try_insert` is not yet stable, we have to manually reinsert the old value
            // such that the map does not change in case a value was already present
            if let Some(index) = insert {
                closure_formula_indices.insert(node.to_string(), index);
            } else {
                indices_to_formula.insert(closure.len(), node.clone());

                /*
                 * For both (left and right) children:
                 * if the current node is atomic, the children do not matter => we set them to index 0
                 * if the curren node is a not node, we have to point to the not_nodes data structure (Either::Right)
                 * else we can just point to the index of the predecessor
                 */
                let left_child = if is_atomic {
                    Either::Left(0)
                } else if node.clone().left.unwrap().node_type == FormulaTreeNodeType::Not {
                    Either::Right(Box::from(
                        not_nodes
                            .get(&node.clone().left.unwrap().to_string())
                            .unwrap()
                            .clone(),
                    ))
                } else {
                    let left_node =
                        closure_formula_indices.get(&node.clone().left.unwrap().to_string());
                    Either::Left(*left_node.unwrap())
                };
                let right_child = if is_atomic {
                    Either::Left(0)
                } else if node.clone().right.unwrap().node_type == FormulaTreeNodeType::Not {
                    Either::Right(Box::from(
                        not_nodes
                            .get(&node.clone().right.unwrap().to_string())
                            .unwrap()
                            .clone(),
                    ))
                } else {
                    let right_node =
                        closure_formula_indices.get(&node.clone().right.unwrap().to_string());
                    Either::Left(*right_node.unwrap())
                };

                closure.push(ElementaryNode::new(
                    is_atomic,
                    left_child,
                    right_child,
                    node.node_type,
                    node.to_string(),
                ));
                trace!("Added subformula {} to closure.", node);
            }
        } else {
            let child_index = closure_formula_indices
                .get(&node.clone().left.unwrap().to_string())
                .unwrap();
            not_nodes.insert(
                node.to_string(),
                ElementaryNode::new(
                    false,
                    Either::Left(*child_index),
                    Either::Left(0),
                    node.node_type,
                    node.to_string(),
                ),
            );
            trace!(
                "Added subformula {} to helper structure because it is negated.",
                node
            );
        }
    });

    trace!("Closure consists of {} positive elements.", closure.len());

    let mut stack: Vec<BitVec> = vec![BitVec::from_elem(closure.len(), false)];
    let mut res: Vec<BitVec> = Vec::new();

    // Compute initial states. I.e., a vector of state that contains all possible combinations
    // for the atomic elements (e.g., a; b; next b; true).
    trace!("Compute all possible combinations for atomic subformulas in the closure...");
    closure
        .iter()
        .filter(|node| node.is_atomic)
        .for_each(|node| {
            let mut helper = Vec::new();
            for state in stack.iter() {
                helper.append(&mut node.clone().derive(
                    state.clone(),
                    *closure_formula_indices.get(&node.formula).unwrap(),
                ));
            }
            stack = helper;
        });

    // Based on the initial states, derive all elementary sets
    while let Some(s) = stack.pop() {
        trace!(
            "Computing elementary set based on atomic combination: {:?}",
            s
        );
        let mut sets = vec![s];
        for closure_elem in closure.iter().filter(|node| !node.is_atomic) {
            trace!("\tconsider formula {}", closure_elem.formula);
            let news = sets
                .iter()
                .flat_map(|set| {
                    closure_elem.clone().derive(
                        set.clone(),
                        *closure_formula_indices.get(&closure_elem.formula).unwrap(),
                    )
                })
                .collect::<Vec<_>>();

            sets = news;
            trace!("\tobtained new sets {:?}", sets);
        }

        res.append(&mut sets);
        trace!("Obtained following intermediate result: {:?}", res);
    }

    trace!("Found the following {} elementary sets:", res.len());
    trace!("{:?}", res);

    (indices_to_formula, res)
}

pub struct LtlGnba {
    transition_matrix: SparseMatrix<bool>,
    // in this construction, states only have successors if the APs they match
    // the label, so we store the APs for each state to decide if there is an outgoing transition
    aps_of_state: Vec<Vec<String>>,
    initial_state: BitVec,
    accepting_states: Vec<BitVec>,
    last_state: usize,
}

fn filter_succesors_with_next(
    set: &BitVec,
    elementary_sets: &Vec<BitVec>,
    index_of_formula: usize,
    index_of_subformula_of_next: &HashMap<usize, (bool, usize)>,
    successors: &mut BitVec,
) {
    let (inverted, subformula_index) = index_of_subformula_of_next[&index_of_formula];
    if set[index_of_formula] {
        for successor_index in 0..successors.len() {
            if !elementary_sets[successor_index][subformula_index] != inverted {
                successors.set(successor_index, false);
            }
        }
    } else {
        for successor_index in 0..successors.len() {
            if elementary_sets[successor_index][subformula_index] != inverted {
                successors.set(successor_index, false);
            }
        }
    }
}

fn filter_successors_with_until(
    set: &BitVec,
    elementary_sets: &Vec<BitVec>,
    index_of_formula: usize,
    index_of_subformula_of_until: &HashMap<usize, ((bool, usize), (bool, usize))>,
    successors: &mut BitVec,
) {
    // Until(f, g) \in set <==> g \in set or (f \in set and Until(f, g) \in successor)
    trace!(
        "filtering successors with until formula: {}",
        index_of_formula
    );

    let ((f_inverted, f_index), (g_inverted, g_index)) =
        index_of_subformula_of_until[&index_of_formula];
    trace!(
        "f: {} {}, g: {} {}",
        f_index,
        f_inverted,
        g_index,
        g_inverted
    );
    if set[index_of_formula] {
        trace!("set contains until formula");
        if !set[g_index] != g_inverted {
            trace!("g is not in set");
            if !set[f_index] != f_inverted {
                trace!("f is not in set");
                successors.clear();
            } else {
                for successor_index in 0..successors.len() {
                    if !elementary_sets[successor_index][index_of_formula] {
                        trace!("g is not in successor {}", successor_index);
                        successors.set(successor_index, false);
                    }
                }
            }
        }
    } else {
        // Until(f, g) \notin set => g \notin set and (f \notin set or Until(f, g) \notin successor)
        trace!("set does not contain until formula");
        if set[g_index] != g_inverted {
            successors.clear();
        } else if set[f_index] != f_inverted {
            trace!("f is in set");
            for successor_index in 0..successors.len() {
                if elementary_sets[successor_index][index_of_formula] {
                    trace!("g is in successor {}", successor_index);
                    successors.set(successor_index, false);
                }
            }
        }
    }
    trace!("successors after until: {:?}", successors);
}

impl LtlGnba {
    pub fn from_ltl_property(ltl_prop: &Property<String>) -> LtlGnba {
        let (indices_to_formula, elementary_sets) = comp_elementary_sets(ltl_prop);
        let last_state = elementary_sets.len() - 1;

        let ltl_formula = if let PropertyType::Ltl(formula) = &ltl_prop.property_type {
            formula
        } else {
            panic!("This is not an LTL formula.");
        };

        // we precompute the indexes of the subformulas for next and until
        let index_of_subformula_of_next: HashMap<usize, (bool, usize)> = indices_to_formula
            .iter()
            .filter(|(_, formula)| formula.node_type == FormulaTreeNodeType::Next)
            .map(|(index, formula)| {
                let mut subformula = formula.left.as_ref().unwrap();
                let mut inverted = false;
                if subformula.node_type == FormulaTreeNodeType::Not {
                    inverted = true;
                    subformula = subformula.left.as_ref().unwrap();
                }
                (
                    *index,
                    (
                        inverted,
                        *indices_to_formula
                            .iter()
                            .find(|(_, f)| **f == **subformula)
                            .unwrap()
                            .0,
                    ),
                )
            })
            .collect();

        let index_of_subformula_of_until: HashMap<usize, ((bool, usize), (bool, usize))> =
            indices_to_formula
                .iter()
                .filter(|(_, formula)| formula.node_type == FormulaTreeNodeType::Until)
                .map(|(index, formula)| {
                    let mut left_subformula = formula.left.as_ref().unwrap();
                    let mut left_inverted = false;
                    if left_subformula.node_type == FormulaTreeNodeType::Not {
                        left_subformula = left_subformula.left.as_ref().unwrap();
                        left_inverted = true;
                    }
                    let mut right_subformula = formula.right.as_ref().unwrap();
                    let mut right_inverted = false;
                    if right_subformula.node_type == FormulaTreeNodeType::Not {
                        right_subformula = right_subformula.left.as_ref().unwrap();
                        right_inverted = true;
                    }
                    (
                        *index,
                        (
                            (
                                left_inverted,
                                *indices_to_formula
                                    .iter()
                                    .find(|(_, f)| **f == **left_subformula)
                                    .unwrap()
                                    .0,
                            ),
                            (
                                right_inverted,
                                *indices_to_formula
                                    .iter()
                                    .find(|(_, f)| **f == **right_subformula)
                                    .unwrap()
                                    .0,
                            ),
                        ),
                    )
                })
                .collect();

        let mut entries = vec![];
        let mut aps_of_state = vec![];

        trace!("indices to formula:");
        for (i, f) in indices_to_formula.iter() {
            trace!("{}: {}", i, f);
        }

        for (i, set) in elementary_sets.iter().enumerate() {
            // the only outgoing transition a set has is with the label corresponding to the APs in
            // it, so we determine this label
            let mut aps: Vec<_> = set
                .iter()
                .enumerate()
                .filter_map(|(j, value)| {
                    let is_atomic =
                        value && indices_to_formula[&j].node_type == FormulaTreeNodeType::Atomic;
                    is_atomic.then(|| indices_to_formula[&j].label.as_ref().unwrap().clone())
                })
                .collect();
            aps.sort();
            aps_of_state.push(aps);

            // now we narrow down possible successors
            let mut successors = BitVec::from_elem(elementary_sets.len(), true);
            trace!("finding successors for set: {:?} {:?}", i, set);

            for (&j, formula) in indices_to_formula.iter() {
                match formula.node_type {
                    FormulaTreeNodeType::Next => {
                        filter_succesors_with_next(
                            set,
                            &elementary_sets,
                            j,
                            &index_of_subformula_of_next,
                            &mut successors,
                        );
                    }
                    FormulaTreeNodeType::Until => {
                        filter_successors_with_until(
                            set,
                            &elementary_sets,
                            j,
                            &index_of_subformula_of_until,
                            &mut successors,
                        );
                    }
                    _ => {}
                }
            }
            trace!("successors: {:?}", successors);
            entries.extend(
                successors
                    .iter()
                    .enumerate()
                    .filter_map(|(j, value)| value.then_some((i, j, true))),
            );
        }
        let transition_matrix =
            SparseMatrix::from_list_of_entries(last_state + 1, last_state + 1, &entries);
        let index_of_ltl_formula = *indices_to_formula
            .iter()
            .find(|(_, formula)| **formula == *ltl_formula)
            .unwrap()
            .0;
        let mut initial_state = BitVec::from_elem(last_state + 1, false);
        for (i, set) in elementary_sets.iter().enumerate() {
            if set[index_of_ltl_formula] {
                initial_state.set(i, true);
            }
        }
        let accepting_states: Vec<_> = indices_to_formula
            .iter()
            .filter_map(|(i, formula)| {
                (formula.node_type == FormulaTreeNodeType::Until).then_some(i)
            })
            .map(|&i| {
                let mut f = BitVec::from_elem(last_state + 1, false);
                let (_, (g_inverted, g)) = index_of_subformula_of_until[&i];
                for (j, set) in elementary_sets.iter().enumerate() {
                    if !set[i] || (set[g] != g_inverted) {
                        f.set(j, true);
                    }
                }
                f
            })
            .collect();

        LtlGnba {
            transition_matrix,
            aps_of_state,
            initial_state,
            accepting_states,
            last_state,
        }
    }

    fn step(&self, state: BitVec, label: &Vec<String>) -> BitVec {
        let mut sorted_label = label.clone();
        sorted_label.sort();

        let mut new_state = BitVec::from_elem(self.last_state + 1, false);
        for i in state
            .iter()
            .enumerate()
            .filter_map(|(i, value)| value.then_some(i))
        {
            if self.aps_of_state[i] != sorted_label {
                continue;
            }
            for &j in self.transition_matrix.get_col_indexes_in_row(i) {
                new_state.set(j, true);
            }
        }
        new_state
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_atomic_node_evaluation() {
        let atomic_node = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::Atomic,
        );

        let labels = vec!["A".to_string()];
        assert!(
            atomic_node.evaluate(&labels),
            "Atomic node with label 'A' should evaluate to true."
        );

        let labels = vec!["B".to_string()];
        assert!(
            !atomic_node.evaluate(&labels),
            "Atomic node with label 'A' should evaluate to false when 'A' is not in labels."
        );
    }

    #[test]
    fn test_not_node_evaluation() {
        let atomic_node = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let not_node = FormulaTreeNode::new(
            Some(Box::new(atomic_node)),
            None,
            None,
            FormulaTreeNodeType::Not,
        );

        let labels = vec!["A".to_string()];
        assert!(
            !not_node.evaluate(&labels),
            "NOT node should invert the evaluation of the atomic node."
        );

        let labels = vec!["B".to_string()];
        assert!(
            not_node.evaluate(&labels),
            "NOT node should return true when the atomic node evaluates to false."
        );
    }

    #[test]
    fn test_and_node_evaluation() {
        let atomic_a = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let atomic_b = FormulaTreeNode::new(
            None,
            None,
            Some("B".to_string()),
            FormulaTreeNodeType::Atomic,
        );

        let and_node = FormulaTreeNode::new(
            Some(Box::new(atomic_a)),
            Some(Box::new(atomic_b)),
            None,
            FormulaTreeNodeType::And,
        );

        let labels = vec!["A".to_string(), "B".to_string()];
        assert!(
            and_node.evaluate(&labels),
            "AND node should evaluate to true when both children evaluate to true."
        );

        let labels = vec!["A".to_string()];
        assert!(
            !and_node.evaluate(&labels),
            "AND node should evaluate to false when only one child evaluates to true."
        );

        let labels = vec!["C".to_string()];
        assert!(
            !and_node.evaluate(&labels),
            "AND node should evaluate to false when neither child evaluates to true."
        );
    }

    #[test]
    fn test_or_node_evaluation() {
        let atomic_a = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let atomic_b = FormulaTreeNode::new(
            None,
            None,
            Some("B".to_string()),
            FormulaTreeNodeType::Atomic,
        );

        let or_node = FormulaTreeNode::new(
            Some(Box::new(atomic_a)),
            Some(Box::new(atomic_b)),
            None,
            FormulaTreeNodeType::Or,
        );

        let labels = vec!["A".to_string(), "B".to_string()];
        assert!(
            or_node.evaluate(&labels),
            "OR node should evaluate to true when both children evaluate to true."
        );

        let labels = vec!["A".to_string()];
        assert!(
            or_node.evaluate(&labels),
            "OR node should evaluate to true when at least one child evaluates to true."
        );

        let labels = vec!["C".to_string()];
        assert!(
            !or_node.evaluate(&labels),
            "OR node should evaluate to false when neither child evaluates to true."
        );
    }

    #[test]
    fn test_property_evaluation() {
        let atomic_a = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let atomic_b = FormulaTreeNode::new(
            None,
            None,
            Some("B".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let not_b = FormulaTreeNode::new(
            Some(Box::new(atomic_b)),
            None,
            None,
            FormulaTreeNodeType::Not,
        );
        let root = FormulaTreeNode::new(
            Some(Box::new(atomic_a)),
            Some(Box::new(not_b)),
            None,
            FormulaTreeNodeType::And,
        );
        let property = Property::new("ExampleTree".to_string(), PropertyType::Invariant(root));

        let labels = vec!["A".to_string()];
        assert!(
            property.evaluate(&labels),
            "Property should evaluate to true when labels satisfy the AND condition with NOT."
        );

        let labels = vec!["B".to_string()];
        assert_eq!(false, property.evaluate(&labels), "Property should evaluate to false when labels do not satisfy the AND condition with NOT.");
    }

    #[test]
    #[should_panic(expected = "Missing left node when evaluating AND expression!")]
    fn test_and_node_missing_left_child() {
        let atomic_b = FormulaTreeNode::new(
            None,
            None,
            Some("B".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let and_node = FormulaTreeNode::new(
            None,
            Some(Box::new(atomic_b)),
            None,
            FormulaTreeNodeType::And,
        );

        let labels = vec!["B".to_string()];
        and_node.evaluate(&labels); // This should panic due to missing left child
    }

    #[test]
    #[should_panic(expected = "Missing right node when evaluating AND expression!")]
    fn test_and_node_missing_right_child() {
        let atomic_a = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let and_node = FormulaTreeNode::new(
            Some(Box::new(atomic_a)),
            None,
            None,
            FormulaTreeNodeType::And,
        );

        let labels = vec!["A".to_string()];
        and_node.evaluate(&labels); // This should panic due to missing right child
    }

    #[test]
    #[should_panic(expected = "Missing left node when evaluating OR expression!")]
    fn test_or_node_missing_left_child() {
        let atomic_b = FormulaTreeNode::new(
            None,
            None,
            Some("B".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let or_node = FormulaTreeNode::new(
            None,
            Some(Box::new(atomic_b)),
            None,
            FormulaTreeNodeType::Or,
        );

        let labels = vec!["B".to_string()];
        or_node.evaluate(&labels); // This should panic due to missing left child
    }

    #[test]
    #[should_panic(expected = "Missing right node when evaluating OR expression!")]
    fn test_or_node_missing_right_child() {
        let atomic_a = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let or_node = FormulaTreeNode::new(
            Some(Box::new(atomic_a)),
            None,
            None,
            FormulaTreeNodeType::Or,
        );

        let labels = vec!["A".to_string()];
        or_node.evaluate(&labels); // This should panic due to missing right child
    }

    #[test]
    #[should_panic(expected = "Missing left node when evaluating NOT expression!")]
    fn test_not_node_missing_child() {
        let not_node = FormulaTreeNode::new(None, None, None, FormulaTreeNodeType::Not);

        let labels = vec!["A".to_string()];
        not_node.evaluate(&labels); // This should panic due to missing left child
    }

    #[test]
    fn test_finite_automaton() {
        let atomic_a = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let atomic_b = FormulaTreeNode::new(
            None,
            None,
            Some("B".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let atomic_c = FormulaTreeNode::new(
            None,
            None,
            Some("C".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let atomic_d = FormulaTreeNode::new(
            None,
            None,
            Some("D".to_string()),
            FormulaTreeNodeType::Atomic,
        );

        let transition_matrix = SparseMatrix::from_list_of_entries(
            4,
            4,
            &vec![
                (0, 1, vec![atomic_a]),
                (1, 2, vec![atomic_b]),
                (2, 3, vec![atomic_c]),
                (3, 0, vec![atomic_d]),
            ],
        );
        println!("{:?}", transition_matrix);

        let mut initial_state = BitVec::from_elem(4, false);
        initial_state.set(0, true);

        let mut accepting_states = BitVec::from_elem(4, false);
        accepting_states.set(0, true);
        accepting_states.set(3, true);

        let mut automaton = FiniteAutomaton::new(
            AcceptanceType::Buchi,
            transition_matrix,
            3,
            initial_state,
            accepting_states,
        );

        let labels = vec![
            "A".to_string(),
            "B".to_string(),
            "C".to_string(),
            "D".to_string(),
        ];
        assert!(
            automaton.is_accepting(automaton.get_initial_state().clone()),
            "Initial state should be accepting."
        );

        let automaton_state = automaton.get_initial_state();
        println!("{:?}", automaton_state);
        let automaton_state = automaton.step(automaton_state.clone(), &labels);
        println!("{:?}", automaton_state);
        assert!(
            !automaton.is_accepting(automaton_state.clone()),
            "State should not be accepting after one step."
        );

        let automaton_state = &automaton.step(automaton_state.clone(), &labels);
        println!("{:?}", automaton_state);
        assert!(
            !automaton.is_accepting(automaton_state.clone()),
            "State should not be accepting after two steps."
        );

        let automaton_state = automaton.step(automaton_state.clone(), &labels);
        println!("{:?}", automaton_state);
        assert!(
            automaton.is_accepting(automaton_state),
            "State should be accepting after three steps."
        );
    }

    #[test]
    fn test_negation_ltl1() {
        let atomic_a = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let atomic_b = FormulaTreeNode::new(
            None,
            None,
            Some("B".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let a_and_b = FormulaTreeNode::new(
            Some(Box::new(atomic_a)),
            Some(Box::new(atomic_b)),
            None,
            FormulaTreeNodeType::And,
        );
        let not_a_and_b = FormulaTreeNode::new(
            Some(Box::new(a_and_b)),
            None,
            None,
            FormulaTreeNodeType::Not,
        );
        let root = FormulaTreeNode::new(
            Some(Box::new(not_a_and_b)),
            None,
            None,
            FormulaTreeNodeType::Not,
        );

        let mut property = Property::new(
            "Example LTL Property".to_string(),
            PropertyType::Ltl(root.clone()),
        );

        println!("Tree before negating: \n {}", &root);

        property.negate();

        match property.property_type {
            PropertyType::Invariant(_)
            | PropertyType::Persistence(_)
            | PropertyType::OmegaRegular(_)
            | PropertyType::RegularSafety(_) => {
                panic!("Invalid property type inside test. Really impressive!")
            }
            PropertyType::Ltl(formula_tree_node) => {
                println!("Tree after negating: \n {}", &formula_tree_node);

                let root_node = &formula_tree_node;
                assert_eq!(FormulaTreeNodeType::Not, root_node.node_type);

                let left_child_of_root = formula_tree_node.left.as_ref().unwrap();
                assert_eq!(FormulaTreeNodeType::And, left_child_of_root.node_type);

                let left_and = left_child_of_root.left.as_ref().unwrap();
                assert_eq!(FormulaTreeNodeType::Atomic, left_and.node_type);

                let right_and = left_child_of_root.right.as_ref().unwrap();
                assert_eq!(FormulaTreeNodeType::Atomic, right_and.node_type);
            }
        }
    }

    #[test]
    fn test_negation_ltl2() {
        let atomic_a = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let atomic_b = FormulaTreeNode::new(
            None,
            None,
            Some("B".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let a_and_b = FormulaTreeNode::new(
            Some(Box::new(atomic_a)),
            Some(Box::new(atomic_b)),
            None,
            FormulaTreeNodeType::And,
        );
        let not_a_and_b = FormulaTreeNode::new(
            Some(Box::new(a_and_b)),
            None,
            None,
            FormulaTreeNodeType::Not,
        );
        let not_not_a_and_b = FormulaTreeNode::new(
            Some(Box::new(not_a_and_b)),
            None,
            None,
            FormulaTreeNodeType::Not,
        );
        let root = FormulaTreeNode::new(
            Some(Box::new(not_not_a_and_b)),
            None,
            None,
            FormulaTreeNodeType::Not,
        );

        let mut property = Property::new(
            "Example LTL Property".to_string(),
            PropertyType::Ltl(root.clone()),
        );

        println!("Tree before negating: \n {}", &root);

        property.negate();

        match property.property_type {
            PropertyType::Invariant(_)
            | PropertyType::Persistence(_)
            | PropertyType::OmegaRegular(_)
            | PropertyType::RegularSafety(_) => {
                panic!("Invalid property type inside test. Really impressive!")
            }
            PropertyType::Ltl(formula_tree_node) => {
                println!("Tree after negating: \n {}", &formula_tree_node);

                let root_node = &formula_tree_node;
                assert_eq!(FormulaTreeNodeType::And, root_node.node_type);

                let left_child_of_root = root_node.left.as_ref().unwrap();
                assert_eq!(FormulaTreeNodeType::Atomic, left_child_of_root.node_type);

                let right_child_of_root = root_node.right.as_ref().unwrap();
                assert_eq!(FormulaTreeNodeType::Atomic, right_child_of_root.node_type);
            }
        }
    }

    #[test]
    fn test_negation_ltl3() {
        let atomic_a = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let atomic_b = FormulaTreeNode::new(
            None,
            None,
            Some("B".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let not_atomic_b = FormulaTreeNode::new(
            Some(Box::new(atomic_b)),
            None,
            None,
            FormulaTreeNodeType::Not,
        );
        let not_not_atomic_b = FormulaTreeNode::new(
            Some(Box::new(not_atomic_b)),
            None,
            None,
            FormulaTreeNodeType::Not,
        );
        let a_and_b = FormulaTreeNode::new(
            Some(Box::new(atomic_a)),
            Some(Box::new(not_not_atomic_b)),
            None,
            FormulaTreeNodeType::And,
        );
        let not_a_and_b = FormulaTreeNode::new(
            Some(Box::new(a_and_b)),
            None,
            None,
            FormulaTreeNodeType::Not,
        );
        let not_not_a_and_b = FormulaTreeNode::new(
            Some(Box::new(not_a_and_b)),
            None,
            None,
            FormulaTreeNodeType::Not,
        );
        let root = FormulaTreeNode::new(
            Some(Box::new(not_not_a_and_b)),
            None,
            None,
            FormulaTreeNodeType::Not,
        );

        let mut property = Property::new(
            "Example LTL Property".to_string(),
            PropertyType::Ltl(root.clone()),
        );

        println!("Tree before negating: \n {}", &root);

        property.negate();

        match property.property_type {
            PropertyType::Invariant(_)
            | PropertyType::Persistence(_)
            | PropertyType::OmegaRegular(_)
            | PropertyType::RegularSafety(_) => {
                panic!("Invalid property type inside test. Really impressive!")
            }
            PropertyType::Ltl(formula_tree_node) => {
                println!("Tree after negating: \n {}", &formula_tree_node);

                let root_node = &formula_tree_node;
                assert_eq!(FormulaTreeNodeType::And, root_node.node_type);

                let left_child_of_root = root_node.left.as_ref().unwrap();
                assert_eq!(FormulaTreeNodeType::Atomic, left_child_of_root.node_type);

                let right_child_of_root = root_node.right.as_ref().unwrap();
                assert_eq!(FormulaTreeNodeType::Atomic, right_child_of_root.node_type);
            }
        }
    }

    #[test]
    fn test_negation_ltl4() {
        let atomic_a = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let not_atomic_a = FormulaTreeNode::new(
            Some(Box::new(atomic_a.clone())),
            None,
            None,
            FormulaTreeNodeType::Not,
        );
        let atomic_b = FormulaTreeNode::new(
            None,
            None,
            Some("B".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let not_atomic_b = FormulaTreeNode::new(
            Some(Box::new(atomic_b)),
            None,
            None,
            FormulaTreeNodeType::Not,
        );
        let not_not_atomic_b = FormulaTreeNode::new(
            Some(Box::new(not_atomic_b)),
            None,
            None,
            FormulaTreeNodeType::Not,
        );
        let next_a = FormulaTreeNode::new(
            Some(Box::new(not_atomic_a.clone())),
            None,
            None,
            FormulaTreeNodeType::Next,
        );
        let not_not_b_until_next_a = FormulaTreeNode::new(
            Some(Box::new(not_not_atomic_b.clone())),
            Some(Box::new(next_a)),
            None,
            FormulaTreeNodeType::Until,
        );
        let a_and_b = FormulaTreeNode::new(
            Some(Box::new(not_not_b_until_next_a)),
            Some(Box::new(not_not_atomic_b)),
            None,
            FormulaTreeNodeType::And,
        );
        let not_a_and_b = FormulaTreeNode::new(
            Some(Box::new(a_and_b)),
            None,
            None,
            FormulaTreeNodeType::Not,
        );
        let root = FormulaTreeNode::new(
            Some(Box::new(not_a_and_b)),
            None,
            None,
            FormulaTreeNodeType::Not,
        );

        let mut property = Property::new(
            "Example LTL Property".to_string(),
            PropertyType::Ltl(root.clone()),
        );

        println!("Tree before negating: \n {}", &root);

        property.negate();

        match property.property_type {
            PropertyType::Invariant(_)
            | PropertyType::Persistence(_)
            | PropertyType::OmegaRegular(_)
            | PropertyType::RegularSafety(_) => {
                panic!("Invalid property type inside test. Really impressive!")
            }
            PropertyType::Ltl(formula_tree_node) => {
                println!("Tree after negating: \n {}", &formula_tree_node);

                let root_node = &formula_tree_node;
                assert_eq!(FormulaTreeNodeType::Not, root_node.node_type);

                let left_child_of_root = root_node.left.as_ref().unwrap();
                assert_eq!(FormulaTreeNodeType::And, left_child_of_root.node_type);

                let left_child_of_and = left_child_of_root.left.as_ref().unwrap();
                assert_eq!(FormulaTreeNodeType::Until, left_child_of_and.node_type);

                let right_child_of_and = left_child_of_root.right.as_ref().unwrap();
                assert_eq!(FormulaTreeNodeType::Atomic, right_child_of_and.node_type);
                assert_eq!("B", right_child_of_and.label.as_ref().unwrap());

                let left_child_of_until = left_child_of_and.left.as_ref().unwrap();
                assert_eq!(FormulaTreeNodeType::Atomic, left_child_of_until.node_type);
                assert_eq!("B", left_child_of_until.label.as_ref().unwrap());

                let right_child_of_until = left_child_of_and.right.as_ref().unwrap();
                assert_eq!(FormulaTreeNodeType::Next, right_child_of_until.node_type);

                let left_child_of_next = right_child_of_until.left.as_ref().unwrap();
                assert_eq!(FormulaTreeNodeType::Not, left_child_of_next.node_type);

                let left_child_of_not_a = left_child_of_next.left.as_ref().unwrap();
                assert_eq!(FormulaTreeNodeType::Atomic, left_child_of_not_a.node_type);
                assert_eq!("A", left_child_of_not_a.label.as_ref().unwrap());
            }
        }
    }

    #[test]
    fn test_negation_ltl5() {
        let atomic_a = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let atomic_b = FormulaTreeNode::new(
            None,
            None,
            Some("B".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let root = FormulaTreeNode::new(
            Some(Box::new(atomic_a)),
            Some(Box::new(atomic_b)),
            None,
            FormulaTreeNodeType::And,
        );

        let mut property = Property::new(
            "Example LTL Property".to_string(),
            PropertyType::Ltl(root.clone()),
        );

        println!("Tree before negating: \n {}", &root);

        property.negate();

        match property.property_type {
            PropertyType::Invariant(_)
            | PropertyType::Persistence(_)
            | PropertyType::OmegaRegular(_)
            | PropertyType::RegularSafety(_) => {
                panic!("Invalid property type inside test. Really impressive!")
            }
            PropertyType::Ltl(formula_tree_node) => {
                println!("Tree after negating: \n {}", &formula_tree_node);

                let root_node = &formula_tree_node;
                assert_eq!(FormulaTreeNodeType::Not, root_node.node_type);

                let left_child_of_root = formula_tree_node.left.as_ref().unwrap();
                assert_eq!(FormulaTreeNodeType::And, left_child_of_root.node_type);

                let left_and = left_child_of_root.left.as_ref().unwrap();
                assert_eq!(FormulaTreeNodeType::Atomic, left_and.node_type);

                let right_and = left_child_of_root.right.as_ref().unwrap();
                assert_eq!(FormulaTreeNodeType::Atomic, right_and.node_type);
            }
        }
    }

    #[test]
    fn test_compute_elementary_sets_of_ltl1() {
        // In this test case we heavily rely on exercise 3 of the 5th exercise sheet from the model
        // checking course. Hence, we check if the elementary sets given in the sample solution are
        // equivalent to our computation. Note that we now consider elementary sets with 7 truth
        // values, different from the sample solution of the exercise, as we consider `true` as an
        // atomic value with its own entry inside our bitvectors, which represent the elementary sets.

        // phi' = true UNTIL (a AND NOT ((NOT b) UNTIL (a AND b)))
        let ltl_tree = FormulaTreeNode::new(
            Some(Box::from(FormulaTreeNode::new(
                None,
                None,
                None,
                FormulaTreeNodeType::True,
            ))),
            Some(Box::from(FormulaTreeNode::new(
                Some(Box::from(FormulaTreeNode::new(
                    None,
                    None,
                    Some("a".to_string()),
                    FormulaTreeNodeType::Atomic,
                ))),
                Some(Box::from(FormulaTreeNode::new(
                    Some(Box::from(FormulaTreeNode::new(
                        Some(Box::from(FormulaTreeNode::new(
                            Some(Box::from(FormulaTreeNode::new(
                                None,
                                None,
                                Some("b".to_string()),
                                FormulaTreeNodeType::Atomic,
                            ))),
                            None,
                            None,
                            FormulaTreeNodeType::Not,
                        ))),
                        Some(Box::from(FormulaTreeNode::new(
                            Some(Box::from(FormulaTreeNode::new(
                                None,
                                None,
                                Some("a".to_string()),
                                FormulaTreeNodeType::Atomic,
                            ))),
                            Some(Box::from(FormulaTreeNode::new(
                                None,
                                None,
                                Some("b".to_string()),
                                FormulaTreeNodeType::Atomic,
                            ))),
                            None,
                            FormulaTreeNodeType::And,
                        ))),
                        None,
                        FormulaTreeNodeType::Until,
                    ))),
                    None,
                    None,
                    FormulaTreeNodeType::Not,
                ))),
                None,
                FormulaTreeNodeType::And,
            ))),
            None,
            FormulaTreeNodeType::Until,
        );

        // create elementary sets based on exercise solution
        let mut b1 = BitVec::from_elem(7, false);
        b1.set(0, true);
        let mut b2 = BitVec::from_elem(7, false);
        b2.set(0, true);
        b2.set(6, true);
        let mut b3 = BitVec::from_elem(7, false);
        b3.set(0, true);
        b3.set(4, true);
        let mut b4 = BitVec::from_elem(7, false);
        b4.set(0, true);
        b4.set(4, true);
        b4.set(6, true);
        let mut b5 = BitVec::from_elem(7, false);
        b5.set(0, true);
        b5.set(2, true);
        let mut b6 = BitVec::from_elem(7, false);
        b6.set(0, true);
        b6.set(2, true);
        b6.set(6, true);
        let mut b7 = BitVec::from_elem(7, false);
        b7.set(0, true);
        b7.set(1, true);
        b7.set(5, true);
        b7.set(6, true);
        let mut b8 = BitVec::from_elem(7, false);
        b8.set(0, true);
        b8.set(1, true);
        b8.set(4, true);
        let mut b9 = BitVec::from_elem(7, false);
        b9.set(0, true);
        b9.set(1, true);
        b9.set(4, true);
        b9.set(6, true);
        let mut b10 = BitVec::from_elem(7, false);
        b10.set(0, true);
        b10.set(1, true);
        b10.set(2, true);
        b10.set(3, true);
        b10.set(4, true);
        let mut b11 = BitVec::from_elem(7, false);
        b11.set(0, true);
        b11.set(1, true);
        b11.set(2, true);
        b11.set(3, true);
        b11.set(4, true);
        b11.set(6, true);

        let (indices_to_subformulas, elementary_sets) = comp_elementary_sets(&Property::new(
            "ltl property1".to_string(),
            PropertyType::Ltl(ltl_tree.clone()),
        ));

        assert_eq!(11, elementary_sets.len());
        assert!(elementary_sets.contains(&b1));
        assert!(elementary_sets.contains(&b2));
        assert!(elementary_sets.contains(&b3));
        assert!(elementary_sets.contains(&b4));
        assert!(elementary_sets.contains(&b5));
        assert!(elementary_sets.contains(&b6));
        assert!(elementary_sets.contains(&b7));
        assert!(elementary_sets.contains(&b8));
        assert!(elementary_sets.contains(&b9));
        assert!(elementary_sets.contains(&b10));
        assert!(elementary_sets.contains(&b11));
    }

    #[test]
    fn test_compute_elementary_sets_of_ltl2() {
        // In this test case we heavily rely on exercise 1 of the 6th exercise sheet from the model
        // checking course. Hence, we check if the elementary sets given in the sample solution are
        // equivalent to our computation.

        // phi' = (NOT (a AND (NEXT b)) AND NOT (a AND b)) UNTIL ((a AND (NEXT b)) AND NOT (a AND b))
        let ltl_tree = FormulaTreeNode::new(
            Some(Box::from(FormulaTreeNode::new(
                // UNTIL
                Some(Box::from(FormulaTreeNode::new(
                    // NOT (a AND (NEXT b))
                    Some(Box::from(FormulaTreeNode::new(
                        Some(Box::from(FormulaTreeNode::new(
                            None,
                            None,
                            Some("a".to_string()),
                            FormulaTreeNodeType::Atomic,
                        ))),
                        Some(Box::from(FormulaTreeNode::new(
                            Some(Box::from(FormulaTreeNode::new(
                                None,
                                None,
                                Some("b".to_string()),
                                FormulaTreeNodeType::Atomic,
                            ))),
                            None,
                            None,
                            FormulaTreeNodeType::Next,
                        ))),
                        None,
                        FormulaTreeNodeType::And,
                    ))),
                    None,
                    None,
                    FormulaTreeNodeType::Not,
                ))),
                Some(Box::from(FormulaTreeNode::new(
                    // NOT (a AND b)
                    Some(Box::from(FormulaTreeNode::new(
                        Some(Box::from(FormulaTreeNode::new(
                            None,
                            None,
                            Some("a".to_string()),
                            FormulaTreeNodeType::Atomic,
                        ))),
                        Some(Box::from(FormulaTreeNode::new(
                            None,
                            None,
                            Some("b".to_string()),
                            FormulaTreeNodeType::Atomic,
                        ))),
                        None,
                        FormulaTreeNodeType::And,
                    ))),
                    None,
                    None,
                    FormulaTreeNodeType::Not,
                ))),
                Some("a".to_string()),
                FormulaTreeNodeType::And,
            ))),
            Some(Box::from(FormulaTreeNode::new(
                Some(Box::from(FormulaTreeNode::new(
                    // (a AND (NEXT b))
                    Some(Box::from(FormulaTreeNode::new(
                        None,
                        None,
                        Some("a".to_string()),
                        FormulaTreeNodeType::Atomic,
                    ))),
                    Some(Box::from(FormulaTreeNode::new(
                        Some(Box::from(FormulaTreeNode::new(
                            None,
                            None,
                            Some("b".to_string()),
                            FormulaTreeNodeType::Atomic,
                        ))),
                        None,
                        None,
                        FormulaTreeNodeType::Next,
                    ))),
                    None,
                    FormulaTreeNodeType::And,
                ))),
                Some(Box::from(FormulaTreeNode::new(
                    // NOT (a AND b)
                    Some(Box::from(FormulaTreeNode::new(
                        Some(Box::from(FormulaTreeNode::new(
                            None,
                            None,
                            Some("a".to_string()),
                            FormulaTreeNodeType::Atomic,
                        ))),
                        Some(Box::from(FormulaTreeNode::new(
                            None,
                            None,
                            Some("b".to_string()),
                            FormulaTreeNodeType::Atomic,
                        ))),
                        None,
                        FormulaTreeNodeType::And,
                    ))),
                    None,
                    None,
                    FormulaTreeNodeType::Not,
                ))),
                None,
                FormulaTreeNodeType::And,
            ))),
            None,
            FormulaTreeNodeType::Until,
        );

        let (indices_to_subformulas, elementary_sets) = comp_elementary_sets(&Property::new(
            "ltl property2".to_string(),
            PropertyType::Ltl(ltl_tree.clone()),
        ));

        // create elementary sets based on exercise solution
        let mut b1 = BitVec::from_elem(8, false);
        b1.set(5, true);
        let mut b2 = BitVec::from_elem(8, false);
        b2.set(5, true);
        b2.set(7, true);
        let mut b3 = BitVec::from_elem(8, false);
        b3.set(2, true);
        b3.set(5, true);
        let mut b4 = BitVec::from_elem(8, false);
        b4.set(2, true);
        b4.set(5, true);
        b4.set(7, true);
        let mut b5 = BitVec::from_elem(8, false);
        b5.set(1, true);
        b5.set(5, true);
        let mut b6 = BitVec::from_elem(8, false);
        b6.set(1, true);
        b6.set(5, true);
        b6.set(7, true);
        let mut b7 = BitVec::from_elem(8, false);
        b7.set(1, true);
        b7.set(2, true);
        b7.set(5, true);
        let mut b8 = BitVec::from_elem(8, false);
        b8.set(1, true);
        b8.set(2, true);
        b8.set(5, true);
        b8.set(7, true);
        let mut b9 = BitVec::from_elem(8, false);
        b9.set(0, true);
        b9.set(5, true);
        let mut b10 = BitVec::from_elem(8, false);
        b10.set(0, true);
        b10.set(5, true);
        b10.set(7, true);
        let mut b11 = BitVec::from_elem(8, false);
        b11.set(0, true);
        b11.set(2, true);
        b11.set(3, true);
        b11.set(6, true);
        b11.set(7, true);
        let mut b12 = BitVec::from_elem(8, false);
        b12.set(0, true);
        b12.set(1, true);
        b12.set(4, true);
        let mut b13 = BitVec::from_elem(8, false);
        b13.set(0, true);
        b13.set(1, true);
        b13.set(2, true);
        b13.set(3, true);
        b13.set(4, true);

        println!("{:?}", elementary_sets.len());
        println!("{:?}", elementary_sets);

        assert_eq!(13, elementary_sets.len());
        assert!(elementary_sets.contains(&b1));
        assert!(elementary_sets.contains(&b2));
        assert!(elementary_sets.contains(&b3));
        assert!(elementary_sets.contains(&b4));
        assert!(elementary_sets.contains(&b5));
        assert!(elementary_sets.contains(&b6));
        assert!(elementary_sets.contains(&b7));
        assert!(elementary_sets.contains(&b8));
        assert!(elementary_sets.contains(&b9));
        assert!(elementary_sets.contains(&b10));
        assert!(elementary_sets.contains(&b11));
        assert!(elementary_sets.contains(&b12));
        assert!(elementary_sets.contains(&b13));
    }

    #[test]
    fn test_ltl_gnba_next() {
        // phi' = NEXT a
        let ltl_tree = FormulaTreeNode::new(
            Some(Box::from(FormulaTreeNode::new(
                None,
                None,
                Some("a".to_string()),
                FormulaTreeNodeType::Atomic,
            ))),
            None,
            None,
            FormulaTreeNodeType::Next,
        );
        let ltl_gnba = LtlGnba::from_ltl_property(&Property::new(
            "ltl property".to_string(),
            PropertyType::Ltl(ltl_tree.clone()),
        ));

        assert_eq!(ltl_gnba.transition_matrix.rows(), 4);
        assert_eq!(ltl_gnba.transition_matrix.cols(), 4);
        let mut initial_state = BitVec::from_elem(4, false);
        initial_state.set(0, true);
        initial_state.set(2, true);
        assert_eq!(ltl_gnba.initial_state, initial_state);

        let transition_matrix = SparseMatrix::from_2d_vec(&vec![
            vec![true, true, false, false],
            vec![false, false, true, true],
            vec![true, true, false, false],
            vec![false, false, true, true],
        ]);
        assert_eq!(ltl_gnba.transition_matrix, transition_matrix);
        assert_eq!(ltl_gnba.accepting_states, vec![]);
        assert_eq!(
            ltl_gnba.aps_of_state,
            vec![vec!["a"], vec!["a"], vec![], vec![]]
        );
    }

    #[test]
    fn test_ltl_gnba_complex() {
        // phi = true U (a AND (NOT ((NOT b) U (a AND b))))
        let ltl_tree = FormulaTreeNode::new(
            Some(Box::from(FormulaTreeNode::new(
                None,
                None,
                None,
                FormulaTreeNodeType::True,
            ))),
            Some(Box::from(FormulaTreeNode::new(
                Some(Box::from(FormulaTreeNode::new(
                    None,
                    None,
                    Some("a".to_string()),
                    FormulaTreeNodeType::Atomic,
                ))),
                Some(Box::from(FormulaTreeNode::new(
                    Some(Box::from(FormulaTreeNode::new(
                        Some(Box::from(FormulaTreeNode::new(
                            Some(Box::from(FormulaTreeNode::new(
                                None,
                                None,
                                Some("b".to_string()),
                                FormulaTreeNodeType::Atomic,
                            ))),
                            None,
                            None,
                            FormulaTreeNodeType::Not,
                        ))),
                        Some(Box::from(FormulaTreeNode::new(
                            Some(Box::from(FormulaTreeNode::new(
                                None,
                                None,
                                Some("a".to_string()),
                                FormulaTreeNodeType::Atomic,
                            ))),
                            Some(Box::from(FormulaTreeNode::new(
                                None,
                                None,
                                Some("b".to_string()),
                                FormulaTreeNodeType::Atomic,
                            ))),
                            None,
                            FormulaTreeNodeType::And,
                        ))),
                        None,
                        FormulaTreeNodeType::Until,
                    ))),
                    None,
                    None,
                    FormulaTreeNodeType::Not,
                ))),
                None,
                FormulaTreeNodeType::And,
            ))),
            None,
            FormulaTreeNodeType::Until,
        );

        let ltl_gnba = LtlGnba::from_ltl_property(&Property::new(
            "ltl property".to_string(),
            PropertyType::Ltl(ltl_tree.clone()),
        ));

        let transition_matrix_b_sets = SparseMatrix::from_2d_vec(&vec![
            vec![
                true, false, false, false, true, false, false, false, false, false, false,
            ],
            vec![
                false, true, false, false, false, true, true, false, false, false, false,
            ],
            vec![
                false, false, true, false, false, false, false, true, false, true, false,
            ],
            vec![
                false, false, false, true, false, false, false, false, true, false, true,
            ],
            vec![
                true, false, true, false, true, false, false, true, false, true, false,
            ],
            vec![
                false, true, false, true, false, true, true, false, true, false, true,
            ],
            vec![
                true, true, false, false, true, true, true, false, false, false, false,
            ],
            vec![
                false, false, true, false, false, false, false, true, false, true, false,
            ],
            vec![
                false, false, false, true, false, false, false, false, true, false, true,
            ],
            vec![
                true, false, true, false, true, false, false, true, false, true, false,
            ],
            vec![
                false, true, false, true, false, true, true, false, true, false, true,
            ],
        ]);

        let translation_to_index = vec![7, 8, 9, 10, 5, 6, 2, 3, 4, 0, 1];

        let mut matrix = vec![vec![false; 11]; 11];
        for row in 0..11 {
            for col in 0..11 {
                matrix[translation_to_index[row]][translation_to_index[col]] =
                    transition_matrix_b_sets[(row, col)];
            }
        }
        let transition_matrix = SparseMatrix::from_2d_vec(&matrix);

        for i in 0..transition_matrix.rows() {
            println!("{:?}", ltl_gnba.transition_matrix.get_col_indexes_in_row(i));
        }

        assert_eq!(ltl_gnba.transition_matrix, transition_matrix);
        let aps_of_state_b_sets = vec![
            vec![],
            vec![],
            vec![],
            vec![],
            vec!["b"],
            vec!["b"],
            vec!["a"],
            vec!["a"],
            vec!["a"],
            vec!["a", "b"],
            vec!["a", "b"],
        ];
        let mut aps_of_state = vec![vec![]; 11];
        for i in 0..11 {
            aps_of_state[translation_to_index[i]] = aps_of_state_b_sets[i].clone();
        }

        assert_eq!(ltl_gnba.aps_of_state, aps_of_state);
        let init_state_indexes_b_sets = vec![1, 3, 5, 6, 8, 10];
        let mut initial_state = BitVec::from_elem(11, false);
        for i in init_state_indexes_b_sets {
            initial_state.set(translation_to_index[i], true);
        }
        assert_eq!(ltl_gnba.initial_state, initial_state);
        print!("{:?}", ltl_gnba.accepting_states);

        let accepting_states_b_sets = vec![vec![0, 1, 4, 5, 6, 9, 10], vec![0, 2, 4, 6, 7, 9]];
        let mut accepting_states = vec![BitVec::from_elem(11, false); 2];

        for i in 0..2 {
            for j in accepting_states_b_sets[i].iter() {
                accepting_states[i].set(translation_to_index[*j], true);
            }
        }
        let mut ltl_accepting_states = ltl_gnba.accepting_states.clone();
        ltl_accepting_states.sort();
        accepting_states.sort();

        assert_eq!(ltl_accepting_states, accepting_states);
    }
}
