use crate::common::sparse_matrix::*;
use bit_vec::BitVec;
use std::collections::HashMap;
use crate::parser::property::{Property, PropertyType};

/// Represents a transition system with states, transitions, and labels.
///
/// A transition system is defined by its states, initial states, transitions between states,
/// and labels on states. Atomic propositions (APs) are associated with states through labels.
///
/// The `TransitionSystem` uses sparse matrices to efficiently represent the transition relations.
pub struct TransitionSystem {
    /// Transition matrix representing the transitions from each state.
    transition_matrix: SparseMatrix<bool>,
    /// Reverse transition matrix representing the transitions to each state.
    reverse_transition_matrix: SparseMatrix<bool>,
    /// Name of the last state in the transition system.
    last_state: usize,
    /// Indices of the initial states.
    initial_states: Vec<usize>,
    /// Labels associated with each state, encoded as `BitVec`.
    /// Each bit represents the presence of an atomic proposition (AP) in the state.
    state_labels: Vec<BitVec>, // labels are BitVecs encoding a set of ap indexes
    /// Mapping from labels to the list of states that have that label.
    label_state_map: HashMap<BitVec, Vec<usize>>,
    /// List of atomic propositions (APs) in the transition system.
    ap: Vec<String>, // this means creating a label takes linear time. We don't expect this to be an
                     // issue but if it becomes one, we can store a HashMap<String, usize>
}

impl TransitionSystem {
    /// Creates a new `TransitionSystem`.
    ///
    /// # Parameters
    /// - `transition_matrix`: Sparse matrix representing transitions from states.
    /// - `reverse_transition_matrix`: Sparse matrix representing transitions to states.
    /// - `num_states`: Total number of states.
    /// - `inital_states`: Vector of indices representing initial states.
    /// - `state_labels`: Vector of `BitVec` labels for each state.
    /// - `label_state_map`: HashMap mapping labels to the states that have them.
    /// - `ap`: Vector of atomic propositions.
    pub fn new(
        transition_matrix: SparseMatrix<bool>,
        reverse_transition_matrix: SparseMatrix<bool>,
        last_state: usize,
        initial_states: Vec<usize>,
        state_labels: Vec<BitVec>,
        label_state_map: HashMap<BitVec, Vec<usize>>,
        ap: Vec<String>,
    ) -> Self {
        TransitionSystem {
            transition_matrix,
            reverse_transition_matrix,
            last_state,
            initial_states,
            state_labels,
            label_state_map,
            ap,
        }
    }

    /// Returns the total number of states in the transition system.
    pub fn get_num_states(&self) -> usize {
        self.last_state + 1
    }

    /// Returns a Vec containing the names of all states of the transition system.
    pub fn get_states(&self) -> Vec<usize> {
        (0..self.get_num_states()).collect()
    }

    pub fn get_initial_states(&self) -> &Vec<usize> {
        &self.initial_states
    }

    /// Retrieves the label associated with a given state.
    ///
    /// # Parameters
    /// - `state`: Index of the state.
    ///
    /// # Returns
    /// A reference to the `BitVec` label of the state.
    ///
    /// # Panics
    ///  if the `state` index is out of bounds.
    pub fn get_state_label(&self, state: usize) -> &BitVec {
        if state > self.last_state {
            panic!("{state} is not a valid state.");
        }
        &self.state_labels[state]
    }

    /// Retrieves the list of states that have a given label.
    ///
    /// # Parameters
    /// - `label`: Reference to a `BitVec` representing the label.
    ///
    /// # Returns
    /// A reference to a vector of state indices that have the specified label.
    ///
    /// # Panics
    ///  if the label length does not match the expected length.
    pub fn get_states_with_label(&self, label: &BitVec) -> &Vec<usize> {
        if label.len() != self.state_labels.len() {
            panic!("{label:?} is not a valid label as the BitVec as a different size.");
        }
        static EMPTY_VEC: Vec<usize> = vec![];
        self.label_state_map.get(label).unwrap_or(&EMPTY_VEC)
    }

    /// Returns a reference to the list of atomic propositions (APs).
    pub fn get_ap(&self) -> &Vec<String> {
        &self.ap
    }

    /// Creates a label `BitVec` from a slice of atomic proposition strings.
    ///
    /// # Parameters
    /// - `aps`: Slice of strings representing the atomic propositions to include in the label.
    ///
    /// # Returns
    /// A `BitVec` where bits corresponding to the specified APs are set to `true`.
    pub fn get_label_from_aps(&self, aps: &[String]) -> BitVec {
        let mut label = BitVec::from_elem(self.ap.len(), false);
        for s in aps {
            label.set(self.ap.binary_search(s).unwrap(), true);
        }
        label
    }

    /// Returns an iterator over the successor states of a given state.
    ///
    /// # Parameters
    /// - `state`: Index of the state.
    ///
    /// # Returns
    /// An iterator over state indices that are reachable from the given state.
    pub fn get_successor_states(&self, state: usize) -> impl Iterator<Item = usize> + '_ {
        self.transition_matrix.get_row(state).map(
            |SparseMatrixElement {
                 col_index,
                 value: _,
             }| col_index,
        )
    }

    /// Returns an iterator over the predecessor states of a given state.
    ///
    /// # Parameters
    /// - `state`: Index of the state.
    ///
    /// # Returns
    /// An iterator over state indices that can reach the given state.
    pub fn get_predeccessor_states(&self, state: usize) -> impl Iterator<Item = usize> + '_ {
        self.reverse_transition_matrix.get_row(state).map(
            |SparseMatrixElement {
                 col_index,
                 value: _,
             }| col_index,
        )
    }
}

// tests written by claude
#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::sparse_matrix::SparseMatrix;
    use crate::parser::property::{FormulaTreeNode, FormulaTreeNodeType};

    fn create_test_transition_system() -> TransitionSystem {
        let transitions = vec![
            vec![false, true, false], // State 0 -> State 1
            vec![false, false, true], // State 1 -> State 2
            vec![true, false, false], // State 2 -> State 0
        ];
        let transition_matrix = SparseMatrix::from_2d_vec(&transitions);
        let reverse_transitions = vec![
            vec![false, false, true], // State 0 <- State 2
            vec![true, false, false], // State 1 <- State 0
            vec![false, true, false], // State 2 <- State 1
        ];
        let reverse_transition_matrix = SparseMatrix::from_2d_vec(&reverse_transitions);
        let mut state_labels = Vec::new();
        let ap = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let mut label0 = BitVec::from_elem(3, false);
        label0.set(0, true);
        state_labels.push(label0.clone());
        let mut label1 = BitVec::from_elem(3, false);
        label1.set(1, true);
        state_labels.push(label1.clone());
        let mut label2 = BitVec::from_elem(3, false);
        label2.set(0, true);
        label2.set(2, true);
        state_labels.push(label2.clone());
        let mut label_state_map = HashMap::new();
        label_state_map.insert(label0, vec![0]);
        label_state_map.insert(label1, vec![1]);
        label_state_map.insert(label2, vec![2]);
        TransitionSystem::new(
            transition_matrix,
            reverse_transition_matrix,
            2,       // last_state
            vec![0], // initial_states
            state_labels,
            label_state_map,
            ap,
        )
    }
    #[test]
    fn test_get_num_states() {
        let ts = create_test_transition_system();
        assert_eq!(ts.get_num_states(), 3);
    }
    #[test]
    fn test_get_states() {
        let ts = create_test_transition_system();
        assert_eq!(ts.get_states(), vec![0, 1, 2]);
    }
    #[test]
    fn test_get_state_label() {
        let ts = create_test_transition_system();
        let label0 = ts.get_state_label(0);
        assert!(label0.get(0).unwrap()); // "a" is true
        assert!(!label0.get(1).unwrap()); // "b" is false
        assert!(!label0.get(2).unwrap()); // "c" is false
        let label2 = ts.get_state_label(2);
        assert!(label2.get(0).unwrap()); // "a" is true
        assert!(!label2.get(1).unwrap()); // "b" is false
        assert!(label2.get(2).unwrap()); // "c" is true
    }
    #[test]
    #[should_panic(expected = "is not a valid state")]
    fn test_get_state_label_invalid_state() {
        let ts = create_test_transition_system();
        ts.get_state_label(3); // Should panic
    }
    #[test]
    fn test_get_states_with_label() {
        let ts = create_test_transition_system();
        let mut label = BitVec::from_elem(3, false);
        label.set(0, true);
        let states = ts.get_states_with_label(&label);
        assert_eq!(states, &vec![0]);
    }
    #[test]
    fn test_get_label_from_aps() {
        let ts = create_test_transition_system();
        let aps = vec!["a".to_string(), "c".to_string()];
        let label = ts.get_label_from_aps(&aps);
        assert!(label.get(0).unwrap()); // "a" is true
        assert!(!label.get(1).unwrap()); // "b" is false
        assert!(label.get(2).unwrap()); // "c" is true
    }
    #[test]
    fn test_get_successor_states() {
        let ts = create_test_transition_system();
        let successors0: Vec<_> = ts.get_successor_states(0).collect();
        assert_eq!(successors0, vec![1]);
        let successors1: Vec<_> = ts.get_successor_states(1).collect();
        assert_eq!(successors1, vec![2]);
        let successors2: Vec<_> = ts.get_successor_states(2).collect();
        assert_eq!(successors2, vec![0]);
    }
    #[test]
    fn test_get_predecessor_states() {
        let ts = create_test_transition_system();
        let predecessors0: Vec<_> = ts.get_predeccessor_states(0).collect();
        assert_eq!(predecessors0, vec![2]);
        let predecessors1: Vec<_> = ts.get_predeccessor_states(1).collect();
        assert_eq!(predecessors1, vec![0]);
        let predecessors2: Vec<_> = ts.get_predeccessor_states(2).collect();
        assert_eq!(predecessors2, vec![1]);
    }
    #[test]
    fn test_get_ap() {
        let ts = create_test_transition_system();
        assert_eq!(
            ts.get_ap(),
            &vec!["a".to_string(), "b".to_string(), "c".to_string()]
        );
    }
}
