use crate::common::sparse_matrix::*;
use bit_vec::BitVec;
use std::collections::{HashSet, HashMap, VecDeque};
use crate::checker::invariant::bit_vec_to_ap_strings;
use crate::parser::property::FiniteAutomaton;

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
    /// - `last_state`: Name of the last state. States are modelled as list from `0 .. last_state` (inclusively).
    /// - `initial_states`: Vector of indices representing initial states.
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
    #[allow(dead_code)]
    pub fn get_num_states(&self) -> usize {
        self.last_state + 1
    }

    /// Returns a Vec containing the names of all states of the transition system.
    #[allow(dead_code)]
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

    pub fn get_num_transitions(&self) -> usize {
        self.transition_matrix.get_num_values()
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
    #[allow(dead_code)]
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
    #[allow(dead_code)]
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
    pub fn get_successor_states(&self, state: usize) -> &[usize] {
        self.transition_matrix.get_col_indexes_in_row(state)
    }

    /// Returns an iterator over the predecessor states of a given state.
    ///
    /// # Parameters
    /// - `state`: Index of the state.
    ///
    /// # Returns
    /// An iterator over state indices that can reach the given state.
    #[allow(dead_code)]
    pub fn get_predeccessor_states(&self, state: usize) -> &[usize] {
        self.reverse_transition_matrix.get_col_indexes_in_row(state)
    }

    pub fn product_with(&self, mut auto: FiniteAutomaton<String>) -> TransitionSystem {
        let orig_init_states = self.initial_states.clone();
        let mut bitvecs_to_states: HashMap<BitVec, Vec<String>> = HashMap::new();
        let mut new_states: HashSet<(usize, usize)> = HashSet::new();
        let mut new_state_labels: HashMap<((usize, usize)), usize> = HashMap::new();
        let mut new_trans: Vec<((usize, usize), (usize, usize))> = vec![];
        let new_init_states: HashSet<(usize, usize)>;

        for state in orig_init_states {
            let bv_label = self.get_state_label(state);
            let labels = bitvecs_to_states.get(bv_label)
                .unwrap_or_else(|| &bit_vec_to_ap_strings(self, bv_label));

            let auto_states = auto.step(auto.get_initial_state().clone(), labels);

            for (i, s) in auto_states.iter().enumerate() {
                if !s {continue}

                new_states.insert((state, i));
                new_state_labels.insert((state, i), i);
            }
        }

        new_init_states = new_states.clone();

        let mut deque = VecDeque::from_iter(new_init_states.into_iter());

        while let Some((ts_state, auto_state)) = deque.pop_front() {
            let ts_succs = self.get_successor_states(*ts_state);

            for &ts_succ in ts_succs {
                let ts_succ_label = self.get_state_label(ts_succ);
                let labels = bitvecs_to_states.get(ts_succ_label)
                    .unwrap_or_else(|| &bit_vec_to_ap_strings(self, ts_succ_label));
                let mut current_auto_state = BitVec::from_elem(auto.get_last_state() + 1, false);
                current_auto_state.set(*auto_state, true);
                let auto_states = auto.step(current_auto_state, labels);

                for (auto_succ, s) in auto_states.iter().enumerate() {
                    if !s {continue}

                    let not_been_seen = new_states.insert((ts_succ, auto_succ));
                    new_state_labels.insert((ts_succ, auto_succ), auto_succ);
                    new_trans.push(((ts_state, auto_state), (ts_succ, auto_succ)));

                    if !not_been_seen {
                        deque.push_back((ts_succ, auto_succ));
                    }
                }
            }
        }

        let to_state_name_index = new_states.iter()
            .enumerate()
            .map(|(i, state)| (state, i))
            .collect::<HashMap<_, _>>();
        let num_of_new_states = to_state_name_index.len() - 1;

        let tmatrix = SparseMatrix::from_list_of_entries(
            num_of_new_states,
            num_of_new_states,
            &*new_trans
                .iter()
                .map(|(inp, out)| (to_state_name_index.get(inp).unwrap(), to_state_name_index.get(out).unwrap(), true))
                .collect::<Vec<_>>(),
        );
        let reverse_tmatrix = SparseMatrix::from_list_of_entries(
            num_of_new_states,
            num_of_new_states,
            &*new_trans
                .iter()
                .map(|(inp, out)| (to_state_name_index.get(out).unwrap(), to_state_name_index.get(inp).unwrap(), true))
                .collect::<Vec<_>>(),
        );
        let mapped_new_init_states = new_init_states.iter().map(|s| to_state_name_index.get(s).unwrap()).collect();
        let ap = 0 .. auto.get_last_state() + 1;
        let mut mapped_new_state_labels = vec![BitVec::from_elem(ap.len(), false); num_of_new_states];
        // iterate over mnsl
        // set elems in bvs

        TransitionSystem::new(
            tmatrix,
            reverse_tmatrix,
            num_of_new_states,
            mapped_new_init_states,

        )
    }
}

// tests written by claude
#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::sparse_matrix::SparseMatrix;

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
        let successors0: Vec<_> = ts.get_successor_states(0).to_vec();
        assert_eq!(successors0, vec![1]);
        let successors1: Vec<_> = ts.get_successor_states(1).to_vec();
        assert_eq!(successors1, vec![2]);
        let successors2: Vec<_> = ts.get_successor_states(2).to_vec();
        assert_eq!(successors2, vec![0]);
    }
    #[test]
    fn test_get_predecessor_states() {
        let ts = create_test_transition_system();
        let predecessors0: Vec<_> = ts.get_predeccessor_states(0).to_vec();
        assert_eq!(predecessors0, vec![2]);
        let predecessors1: Vec<_> = ts.get_predeccessor_states(1).to_vec();
        assert_eq!(predecessors1, vec![0]);
        let predecessors2: Vec<_> = ts.get_predeccessor_states(2).to_vec();
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
    #[test]
    fn test_get_num_transitions() {
        let ts = create_test_transition_system();
        assert_eq!(ts.get_num_transitions(), 3);
    }
}
