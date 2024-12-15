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
}

impl fmt::Display for FormulaTreeNode<String> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.node_type {
            FormulaTreeNodeType::And => write!(
                f,
                "({}) AND ({})",
                self.clone().left.unwrap(),
                self.clone().right.unwrap()
            ),
            FormulaTreeNodeType::Or => write!(
                f,
                "({}) OR ({})",
                self.clone().left.unwrap(),
                self.clone().right.unwrap()
            ),
            FormulaTreeNodeType::Until => write!(
                f,
                "({}) UNTIL ({})",
                self.clone().left.unwrap(),
                self.clone().right.unwrap()
            ),
            FormulaTreeNodeType::Next => write!(f, "NEXT ({})", self.clone().left.unwrap()),
            FormulaTreeNodeType::Not => write!(f, "NOT ({})", self.clone().left.unwrap()),
            FormulaTreeNodeType::Atomic => write!(f, "ATOMIC ({})", self.clone().label.unwrap()),
            FormulaTreeNodeType::True => write!(f, "TRUE"),
        }
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
    property: Property<String>,
) -> (HashMap<usize, FormulaTreeNode<String>>, Vec<BitVec>) {
    let formula = match property.property_type {
        PropertyType::Ltl(formula) => formula,
        _ => panic!("Cannot compute elementary sets of something other than an LTL formula."),
    };

    trace!("Computing elementary sets for formula {}", formula);

    let mut closure_formula_indices: HashMap<String, usize> = HashMap::new();
    let mut indices_to_formula: HashMap<usize, FormulaTreeNode<String>> = HashMap::new();
    let mut closure: Vec<ElementaryNode> = Vec::new();
    let mut not_nodes: HashMap<String, ElementaryNode> = HashMap::new();

    // Traverse the formula to capture all nodes and map them into the intermediate struct
    FormulaTreeNode::post_order_traversal(&formula, &mut |node: &FormulaTreeNode<String>| {
        if node.node_type != FormulaTreeNodeType::Not {
            let insert = closure_formula_indices.insert(node.to_string(), closure.len());
            // As `try_insert` is not yet stable, we have to manually reinsert the old value
            // such that the map does not change in case a value was already present
            if let Some(index) = insert {
                closure_formula_indices.insert(node.to_string(), index);
            } else {
                indices_to_formula.insert(closure.len(), node.clone());
                closure.push(ElementaryNode::new(
                    node.node_type == FormulaTreeNodeType::True
                        || node.node_type == FormulaTreeNodeType::Atomic
                        || node.node_type == FormulaTreeNodeType::Next,
                    Either::Left(0),
                    Either::Left(0),
                    node.node_type,
                    node.to_string(),
                ));
                trace!("Added subformula {} to closure.", node);
            }
        } else {
            not_nodes.insert(
                node.to_string(),
                ElementaryNode::new(
                    false,
                    Either::Left(0),
                    Either::Left(0),
                    node.node_type,
                    node.to_string(),
                ),
            );
            trace!("Added subformula {} to helper structure because it is negated.", node);
        }


        // Update indices in elemenatry node
        let is_atomic = node.node_type == FormulaTreeNodeType::True
            || node.node_type == FormulaTreeNodeType::Atomic
            || node.node_type == FormulaTreeNodeType::Next;

        if !is_atomic && node.node_type != FormulaTreeNodeType::Not {
            let left_node = closure_formula_indices.get(&node.clone().left.unwrap().to_string());
            let right_node = closure_formula_indices.get(&node.clone().right.unwrap().to_string());
            let node_index = *closure_formula_indices.get(&node.to_string()).unwrap();

            closure[node_index].set_left_value(
                if node.clone().left.unwrap().node_type != FormulaTreeNodeType::Not {
                    Either::Left(*left_node.unwrap())
                } else {
                    Either::Right(Box::from(
                        not_nodes
                            .get(&node.clone().left.unwrap().to_string())
                            .unwrap()
                            .clone(),
                    ))
                },
            );
            closure[node_index].set_right_value(
                if node.clone().right.unwrap().node_type != FormulaTreeNodeType::Not {
                    Either::Left(*right_node.unwrap())
                } else {
                    Either::Right(Box::from(
                        not_nodes
                            .get(&node.clone().right.unwrap().to_string())
                            .unwrap()
                            .clone(),
                    ))
                },
            );
        } else if node.node_type == FormulaTreeNodeType::Not {
            let elem_node = not_nodes.get_mut(&node.to_string()).unwrap();
            let child_index = closure_formula_indices
                .get(&node.clone().left.unwrap().to_string())
                .unwrap();
            elem_node.set_left_value(
                if node.clone().left.unwrap().node_type != FormulaTreeNodeType::Not {
                    Either::Left(*child_index)
                } else {
                    panic!(
                        "There should be no double negations when constructing elementary sets."
                    );
                },
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
        trace!("Computing elementary set based on atomic combination: {:?}", s);
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

        let (indices_to_subformulas, elementary_sets) = comp_elementary_sets(Property::new(
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
        // equivalent to our computation. Note that we now consider elementary sets with 7 truth
        // values, different from the sample solution of the exercise, as we consider `true` as an
        // atomic value with its own entry inside our bitvectors, which represent the elementary sets.

        // phi' = (NOT (a AND (NEXT b)) AND NOT (a AND b)) UNTIL ((a AND (NEXT b)) AND NOT (a AND b))
        let ltl_tree = FormulaTreeNode::new(
            Some(Box::from(FormulaTreeNode::new( // UNTIL
                Some(Box::from(FormulaTreeNode::new( // NOT (a AND (NEXT b))
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
                Some(Box::from(FormulaTreeNode::new( // NOT (a AND b)
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
                Some(Box::from(FormulaTreeNode::new( // (a AND (NEXT b))
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
                Some(Box::from(FormulaTreeNode::new( // NOT (a AND b)
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

        let (indices_to_subformulas, elementary_sets) = comp_elementary_sets(Property::new(
            "ltl property1".to_string(),
            PropertyType::Ltl(ltl_tree.clone()),
        ));
    }
}
