use std::fmt;
use bit_vec::BitVec;
use log::*;

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
            PropertyType::Ltl(_)  => panic!("This is a ltl property, which is used to create a GNBA and not to evaluate"),
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
            | PropertyType::RegularSafety(_) => panic!(
                "Negation of a property is currently only allowed for LTL properties."
            ),
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

    fn handle_leading_nots_when_negating_from_root(formula_tree_node: &mut FormulaTreeNode<String>) {
        let mut number_of_nots = 0; // no leading `NOT` nodes in the beginning
        let mut current_node = Some(Box::new(formula_tree_node.clone()));
        if FormulaTreeNodeType::Not == formula_tree_node.node_type {
            current_node = formula_tree_node.left.clone();
            number_of_nots += 1; // here we include the root node

            // count the number of consecutive `NOT`s starting from the root
            while current_node.is_some()
                && current_node.as_ref().unwrap().node_type == FormulaTreeNodeType::Not {
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
            FormulaTreeNodeType::Until => panic!("This operator is only used for LTL. Thus, no evaluation."),
            FormulaTreeNodeType::Next => panic!("This operator is only used for LTL. Thus, no evaluation."),
        }
    }

    /// Recursively removes all double negations from this formula tree. We assume that the current
    /// node is not a `NOT` node.
    ///
    /// # Returns
    /// - A `bool` representing the result of the evaluation.
    fn remove_double_negations(&mut self) {
        if let FormulaTreeNodeType::Atomic = self.node_type {
            // reached a leaf node, return
            return
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
#[derive(Debug, Copy, Clone, Default, PartialEq)]
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

        let mut property = Property::new("Example LTL Property".to_string(), PropertyType::Ltl(root.clone()));

        println!("Tree before negating: \n {}", &root);

        property.negate();

        match property.property_type {
            PropertyType::Invariant(_)
            | PropertyType::Persistence(_)
            | PropertyType::OmegaRegular(_)
            | PropertyType::RegularSafety(_) => panic!(
                "Invalid property type inside test. Really impressive!"
            ),
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

        let mut property = Property::new("Example LTL Property".to_string(), PropertyType::Ltl(root.clone()));

        println!("Tree before negating: \n {}", &root);

        property.negate();

        match property.property_type {
            PropertyType::Invariant(_)
            | PropertyType::Persistence(_)
            | PropertyType::OmegaRegular(_)
            | PropertyType::RegularSafety(_) => panic!(
                "Invalid property type inside test. Really impressive!"
            ),
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

        let mut property = Property::new("Example LTL Property".to_string(), PropertyType::Ltl(root.clone()));

        println!("Tree before negating: \n {}", &root);

        property.negate();

        match property.property_type {
            PropertyType::Invariant(_)
            | PropertyType::Persistence(_)
            | PropertyType::OmegaRegular(_)
            | PropertyType::RegularSafety(_) => panic!(
                "Invalid property type inside test. Really impressive!"
            ),
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
            FormulaTreeNodeType::Next
        );
        let not_not_b_until_next_a = FormulaTreeNode::new(
            Some(Box::new(not_not_atomic_b.clone())),
            Some(Box::new(next_a)),
            None,
            FormulaTreeNodeType::Until
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

        let mut property = Property::new("Example LTL Property".to_string(), PropertyType::Ltl(root.clone()));

        println!("Tree before negating: \n {}", &root);

        property.negate();

        match property.property_type {
            PropertyType::Invariant(_)
            | PropertyType::Persistence(_)
            | PropertyType::OmegaRegular(_)
            | PropertyType::RegularSafety(_) => panic!(
                "Invalid property type inside test. Really impressive!"
            ),
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
    fn test_negation_ltl6() {
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

        let mut property = Property::new("Example LTL Property".to_string(), PropertyType::Ltl(root.clone()));

        println!("Tree before negating: \n {}", &root);

        property.negate();

        match property.property_type {
            PropertyType::Invariant(_)
            | PropertyType::Persistence(_)
            | PropertyType::OmegaRegular(_)
            | PropertyType::RegularSafety(_) => panic!(
                "Invalid property type inside test. Really impressive!"
            ),
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
}
