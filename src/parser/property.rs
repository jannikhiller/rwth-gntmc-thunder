use bit_vec::BitVec;
use log::*;

use crate::common::sparse_matrix::{SparseMatrix, SparseMatrixElement};

#[derive(Debug)]
pub enum PropertyType<ValueType> {
    Invariant(FormulaTreeNode<ValueType>),
    Persistence(FormulaTreeNode<ValueType>),
    RegularSafety(FiniteAutomaton<ValueType>),
    OmegaRegular(FiniteAutomaton<ValueType>),
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
            PropertyType::Invariant(formula) => formula.evaluate(labels),
            PropertyType::Persistence(formula) => formula.evaluate(labels),
            PropertyType::OmegaRegular(_) | PropertyType::RegularSafety(_) => panic!(
                "This is an automaton property, use the automatons member functions instead."
            ),
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
            FormulaTreeNodeType::Atomic => labels.contains(self.label.as_ref().unwrap()),
        }
    }
}

/// Represents the type of node within a `FormulaTreeNode`.
///
/// This enum defines the possible logical operations or atomic values that a node can represent,
/// including `AND`, `OR`, `NOT`, and `ATOMIC`.
#[derive(Debug, Copy, Clone, Default, PartialEq)]
pub enum FormulaTreeNodeType {
    And,
    Or,
    Not,
    #[default]
    Atomic,
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
#[derive(Debug)]
pub struct FiniteAutomaton<ValueType> {
    /// The type of acceptance for this automaton.
    acceptance: AcceptanceType,
    /// The transition matrix of the automaton.
    transition_matrix: SparseMatrix<FormulaTreeNode<ValueType>>,
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
        transition_matrix: SparseMatrix<FormulaTreeNode<String>>,
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
        let mut new_state = BitVec::from_elem(self.last_state + 1, false);
        for (i, value) in state.iter().enumerate() {
            if !value {
                continue;
            }
            trace!("Determining successors of {:?}", i);
            for SparseMatrixElement {
                col_index,
                value: formula,
            } in self.transition_matrix.get_row(i as usize)
            {
                trace!(
                    "   Evaluating formula {:?} for possible successor {:?}",
                    formula,
                    col_index
                );
                if formula.evaluate(label) {
                    new_state.set(col_index, true);
                }
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
                (0, 1, atomic_a),
                (1, 2, atomic_b),
                (2, 3, atomic_c),
                (3, 0, atomic_d),
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
}
