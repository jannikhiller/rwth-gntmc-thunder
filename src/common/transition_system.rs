use crate::common::sparse_matrix::*;
use bit_vec::BitVec;
use std::collections::HashMap;

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
    /// Total number of states in the transition system.
    num_states: usize,
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
        num_states: usize,
        initial_states: Vec<usize>,
        state_labels: Vec<BitVec>,
        label_state_map: HashMap<BitVec, Vec<usize>>,
        ap: Vec<String>,
    ) -> Self {
        TransitionSystem {
            transition_matrix,
            reverse_transition_matrix,
            num_states,
            initial_states: inital_states,
            state_labels,
            label_state_map,
            ap,
        }
    }

    /// Returns the total number of states in the transition system.
    pub fn get_num_states(&self) -> usize {
        self.num_states
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
    /// Panics if the `state` index is out of bounds.
    pub fn get_state_label(&self, state: usize) -> &BitVec {
        if state > self.num_states {
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
    /// Panics if the label length does not match the expected length.
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
        let mut label = BitVec::with_capacity(self.ap.len());
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
