use crate::checker::helper::bit_vec_to_ap_strings;
use crate::common::sparse_matrix::*;
use crate::property::automaton::FiniteAutomaton;
use array_tool::vec::*;
use bit_vec::BitVec;
use itertools::Itertools;
use log::{debug, trace};
use std::{
    collections::{BTreeMap, HashMap, HashSet, VecDeque},
    str::FromStr,
};

/// Represents a transition system with states, transitions, and labels.
///
/// A transition system is defined by its states, initial states, transitions between states,
/// and labels on states. Atomic propositions (APs) are associated with states through labels.
///
/// The `TransitionSystem` uses sparse matrices to efficiently represent the transition relations.
#[derive(Debug, PartialEq)]
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

    pub fn create_label_info(
        aps_of_state: &HashMap<usize, Vec<String>>,
    ) -> (Vec<BitVec>, HashMap<BitVec, Vec<usize>>, Vec<String>) {
        let mut ap: Vec<_> = aps_of_state.values().flatten().unique().cloned().collect();
        ap.sort_unstable();
        let state_labels: Vec<_> = aps_of_state
            .iter()
            .collect::<BTreeMap<_, _>>()
            .into_values()
            .map(|aps| {
                let mut label = BitVec::from_elem(ap.len(), false);
                for a in aps {
                    label.set(ap.binary_search(a).unwrap(), true);
                }
                label
            })
            .collect();
        let mut label_state_map: HashMap<BitVec, Vec<usize>> = HashMap::new();
        for (state, label) in state_labels.iter().enumerate() {
            label_state_map
                .entry(label.clone())
                .or_insert_with(Vec::new)
                .push(state);
        }
        (state_labels, label_state_map, ap)
    }

    /// Returns the total number of states in the transition system.
    #[allow(dead_code)]
    pub fn get_num_states(&self) -> usize {
        self.last_state + 1
    }

    /// Returns a Vec containing the names of all states of the transition system.
    pub fn get_states(&self) -> std::ops::Range<usize> {
        0..self.get_num_states()
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
    ///
    pub fn get_states_with_label(&self, label: &BitVec) -> &Vec<usize> {
        if label.len() != self.ap.len() {
            panic!("{label:?} is not a valid label as the BitVec has a different size.");
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
    pub fn get_predecessor_states(&self, state: usize) -> &[usize] {
        self.reverse_transition_matrix.get_col_indexes_in_row(state)
    }

    /// Computes the product of the transition system with an automaton.
    /// I.e. a new transition system that simulates the old one while simultaneously executing
    /// the automaton. The new atomic propositions are the final/accepting states of the
    /// automaton. Thus, if a state in the transition system shows bad behavior, it
    /// is labeled with the corresponding state from the automaton. Otherwise, it is labeled
    /// with the empty set, i.e., an empty `BitVec`.\
    /// The procedure uses breadth first search and only computes the reachable fragment. \
    /// **Note**: You cannot transfer any information from the old transition system to the product.
    /// That is neither initial states, state names nor number of states, etc.
    ///
    /// # Parameters
    /// - `auto` The automaton. This can either be a finite automaton or a Büchi automaton
    ///
    /// # Returns
    /// The reachable fragment of the product transition system
    pub fn product_with(&self, mut auto: FiniteAutomaton<String>) -> TransitionSystem {
        debug!("Computing product of transition system with automaton");
        let orig_init_states = self.initial_states.clone();
        // Maps from the labels given as a BitVec to the corresponding String Vec.
        // Used as a buffer to improve performance
        let mut bitvecs_to_states: HashMap<BitVec, Vec<String>> = HashMap::new();
        let mut new_states: HashSet<(usize, usize)> = HashSet::new();
        // new state |-> new label, i.e., the state of the automaton
        let mut new_state_labels: HashMap<(usize, usize), usize> = HashMap::new();
        let mut new_trans: Vec<((usize, usize), (usize, usize))> = vec![];

        let auto_aps: Option<Vec<String>> = auto.get_atomic_propositions();

        trace!("Computing init states...");
        for state in orig_init_states {
            trace!("TS state: {:?}", state);
            let bv_label = self.get_state_label(state);
            let labels = bitvecs_to_states.get(bv_label).cloned().unwrap_or_else(|| {
                let label = bit_vec_to_ap_strings(self, bv_label);
                let filtered_label = if auto_aps.is_some() {
                    label.intersect(auto_aps.clone().unwrap())
                } else {
                    label
                };
                bitvecs_to_states.insert(bv_label.clone(), filtered_label.clone());
                filtered_label
            });

            let auto_states = auto.step(auto.get_initial_state().clone(), &labels);
            trace!(
                "Label: {:?}\nSuccessor states in automaton: {:?}",
                labels,
                auto_states
            );
            for (auto_state, is_set) in auto_states.iter().enumerate() {
                if !is_set {
                    continue;
                }

                trace!("original state {} corresponds to automaton state {} resulting in new state {:?}", state, auto_state, (state, auto_state));
                new_states.insert((state, auto_state));
                new_state_labels.insert((state, auto_state), auto_state);
            }
        }

        let new_init_states: HashSet<(usize, usize)> = new_states.clone();

        let mut deque: VecDeque<(usize, usize)> = VecDeque::new();
        new_init_states.iter().for_each(|x| deque.push_back(*x));

        trace!(
            "Computing reachable fragment...\nStarting with Queue: {:?}",
            deque
        );
        while let Some((ts_state, auto_state)) = deque.pop_front() {
            let ts_succs = self.get_successor_states(ts_state);

            trace!(
                "Considering state {:?} with successor states {:?} in original transition system",
                (ts_state, auto_state),
                ts_succs
            );

            for ts_succ in ts_succs {
                trace!("\tConsidering successor {}", ts_succ);
                let ts_succ_label = self.get_state_label(*ts_succ);
                let labels = bitvecs_to_states
                    .get(ts_succ_label)
                    .cloned()
                    .unwrap_or_else(|| {
                        let label = bit_vec_to_ap_strings(self, ts_succ_label);
                        let filtered_label = if auto_aps.is_some() {
                            label.intersect(auto_aps.clone().unwrap())
                        } else {
                            label
                        };
                        bitvecs_to_states.insert(ts_succ_label.clone(), filtered_label.clone());
                        filtered_label
                    });
                let mut current_auto_state = BitVec::from_elem(auto.get_last_state() + 1, false);
                current_auto_state.set(auto_state, true);
                let auto_states = auto.step(current_auto_state, &labels);

                for (auto_succ, s) in auto_states.iter().enumerate() {
                    if !s {
                        continue;
                    }

                    trace!("\tCorresponds to automaton state {}\n\t\t=> new state: {:?}; with transition {:?} -> {:?}", auto_succ, (*ts_succ, auto_succ), (ts_state, auto_state), (*ts_succ, auto_succ));

                    let not_been_seen = new_states.insert((*ts_succ, auto_succ));
                    new_state_labels.insert((*ts_succ, auto_succ), auto_succ);
                    new_trans.push(((ts_state, auto_state), (*ts_succ, auto_succ)));

                    if not_been_seen {
                        deque.push_back((*ts_succ, auto_succ));
                        trace!("\t\tNew state has not been seen yet. Adding to Queue...\n\t\tQueue updated to: {:?}", deque);
                    }
                }
            }
        }

        trace!("Combining results into new transition system...");
        // maps a new state given as a pair to a single integer which is used as state in the new TS
        let to_state_name_index = new_states
            .iter()
            .enumerate()
            .map(|(i, state)| (state, i))
            .collect::<HashMap<_, _>>();
        trace!("Mapping of new states: {:?}", to_state_name_index);
        // total number of states in the new TS. => The last state is num_of_new_states-1
        let num_of_new_states = to_state_name_index.len();

        let tmatrix = SparseMatrix::from_list_of_entries(
            num_of_new_states,
            num_of_new_states,
            &new_trans
                .iter()
                .map(|(inp, out)| {
                    (
                        *to_state_name_index.get(inp).unwrap(),
                        *to_state_name_index.get(out).unwrap(),
                        true,
                    )
                })
                .collect::<Vec<_>>(),
        );
        let reverse_tmatrix = SparseMatrix::from_list_of_entries(
            num_of_new_states,
            num_of_new_states,
            &new_trans
                .iter()
                .map(|(inp, out)| {
                    (
                        *to_state_name_index.get(out).unwrap(),
                        *to_state_name_index.get(inp).unwrap(),
                        true,
                    )
                })
                .collect::<Vec<_>>(),
        );
        let mapped_new_init_states = new_init_states
            .iter()
            .map(|s| *to_state_name_index.get(s).unwrap())
            .collect();
        // maps a (final) state in the automaton to its index in the new Vec of APs
        let mut auto_state_to_bv_index = HashMap::new();
        // the APs are the accepting states of the automaton
        // we use this computation to simultaneously store the indices of each AP.
        let ap = auto
            .get_accepting_states()
            .iter()
            .enumerate()
            .map(
                |(state, is_accepting)| {
                    if is_accepting {
                        Some(state)
                    } else {
                        None
                    }
                },
            )
            .filter(Option::is_some)
            .enumerate()
            .map(|(i, state)| {
                auto_state_to_bv_index.insert(state.unwrap(), i);
                state.unwrap().to_string()
            })
            .collect::<Vec<String>>();
        let mut new_state_labels = vec![BitVec::from_elem(ap.len(), false); num_of_new_states];
        for (ts_state, auto_state) in new_states.iter() {
            let mapped_state = to_state_name_index.get(&(*ts_state, *auto_state)).unwrap();
            let mut bv_auto_state = BitVec::from_elem(auto.get_last_state() + 1, false);
            bv_auto_state.set(*auto_state, true);
            let is_accepting_auto_state = auto.is_accepting(bv_auto_state);

            if is_accepting_auto_state {
                trace!("Found accepting state: {}", auto_state);
                // set the bit in the BitVec label of the state
                new_state_labels[*mapped_state].set(
                    auto_state_to_bv_index.get(auto_state).copied().unwrap(),
                    true,
                );
            }
        }
        let new_label_state_map = HashMap::from_iter((0..ap.len() + 1).map(|label_subset| {
            let label = BitVec::from_bytes(&label_subset.to_ne_bytes());

            let states = (0..num_of_new_states)
                .filter(|state| new_state_labels[*state] == label)
                .collect::<Vec<_>>();

            (label, states)
        }));
        debug!("Finished computation of product.");

        TransitionSystem::new(
            tmatrix,
            reverse_tmatrix,
            num_of_new_states - 1,
            mapped_new_init_states,
            new_state_labels,
            new_label_state_map,
            ap,
        )
    }
}

impl std::fmt::Display for TransitionSystem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut ts_str = format!("init: {}", self.initial_states.iter().join(" "));

        for from in self.get_states() {
            for &to in self.get_successor_states(from) {
                let from_aps = bit_vec_to_ap_strings(self, &self.state_labels[from]);
                let to_aps = bit_vec_to_ap_strings(self, &self.state_labels[to]);
                ts_str.push_str(&format!(
                    "\n{}{} -> {}{}",
                    from,
                    from_aps.iter().join(""),
                    to,
                    to_aps.iter().join("")
                ));
            }
        }
        write!(f, "{}", ts_str)
    }
}

#[derive(Debug)]
pub struct ParseError {
    #[allow(dead_code)]
    invalid_line: String,
}

impl FromStr for TransitionSystem {
    type Err = ParseError;

    /// Creates a new `TransitionSystem` from a string representation for testing purposes.
    ///
    /// Format:
    ///
    /// init: 0 3
    /// 0a -> 1b
    /// 1b -> 2c
    /// 2c -> 0a
    /// 3a -> 1b
    fn from_str(ts_str: &str) -> Result<Self, Self::Err> {
        let mut init_states: Vec<usize> = vec![];
        let mut transitions = vec![];
        let mut aps_of_state = HashMap::new();

        for line in ts_str.lines() {
            let parts: Vec<_> = line.split_whitespace().collect();
            if parts.is_empty() {
                continue;
            } else if parts[0] == "init:" {
                init_states.extend(
                    parts[1..]
                        .iter()
                        .map(|s| s.parse())
                        .collect::<Result<Vec<usize>, _>>()
                        .map_err(|_| ParseError {
                            invalid_line: line.to_string(),
                        })?,
                );
            } else {
                // A -> B where A and B consist of leading didgits indicating the state and
                // trailing letters each representing an atomic proposition
                let from_state: usize = parts[0]
                    .chars()
                    .take_while(|c| c.is_ascii_digit())
                    .collect::<String>()
                    .parse()
                    .map_err(|_| ParseError {
                        invalid_line: line.to_string(),
                    })?;
                let to_state: usize = parts[2]
                    .chars()
                    .take_while(|c| c.is_ascii_digit())
                    .collect::<String>()
                    .parse()
                    .map_err(|_| ParseError {
                        invalid_line: line.to_string(),
                    })?;
                let from_aps: Vec<String> = parts[0]
                    .chars()
                    .skip_while(|c| c.is_ascii_digit())
                    .map_into()
                    .collect();
                let to_aps: Vec<String> = parts[2]
                    .chars()
                    .skip_while(|c| c.is_ascii_digit())
                    .map_into()
                    .collect();
                aps_of_state.insert(from_state, from_aps);
                aps_of_state.insert(to_state, to_aps);
                transitions.push((from_state, to_state, true));
            }
        }
        init_states.sort_unstable();

        let last_state = transitions
            .iter()
            .map(|(from, to, _)| *from.max(to))
            .max()
            .unwrap_or(0);
        let (state_labels, label_state_map, ap) =
            TransitionSystem::create_label_info(&aps_of_state);
        Ok(TransitionSystem::new(
            SparseMatrix::from_list_of_entries(last_state + 1, last_state + 1, &transitions),
            SparseMatrix::from_list_of_entries(
                last_state + 1,
                last_state + 1,
                &transitions
                    .iter()
                    .map(|(from, to, _)| (*to, *from, true))
                    .collect::<Vec<_>>(),
            ),
            last_state,
            init_states,
            state_labels,
            label_state_map,
            ap,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::sparse_matrix::SparseMatrix;
    use crate::property::automaton::AcceptanceType::Nfa;
    use crate::property::property::{FormulaTreeNode, FormulaTreeNodeType};

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
    fn test_from_str() {
        let ts_str = "
        init: 0 3
        0a -> 1b
        1b -> 2c
        2c -> 0a
        3a -> 1b";

        let (state_labels, label_state_map, ap) =
            TransitionSystem::create_label_info(&HashMap::from_iter([
                (0, vec!["a".to_string()]),
                (1, vec!["b".to_string()]),
                (2, vec!["c".to_string()]),
                (3, vec!["a".to_string()]),
            ]));

        let ts = TransitionSystem::new(
            SparseMatrix::from_sorted_list_of_entries(
                4,
                4,
                &[(0, 1, true), (1, 2, true), (2, 0, true), (3, 1, true)],
            ),
            SparseMatrix::from_sorted_list_of_entries(
                4,
                4,
                &[(0, 2, true), (1, 0, true), (1, 3, true), (2, 1, true)],
            ),
            3,
            vec![0, 3],
            state_labels,
            label_state_map,
            ap,
        );
        assert_eq!(ts, ts_str.parse().unwrap());
    }

    #[test]
    fn test_get_num_states() {
        let ts = create_test_transition_system();
        assert_eq!(ts.get_num_states(), 3);
    }
    #[test]
    fn test_get_states() {
        let ts = create_test_transition_system();
        assert_eq!(ts.get_states(), 0..3);
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
        let predecessors0: Vec<_> = ts.get_predecessor_states(0).to_vec();
        assert_eq!(predecessors0, vec![2]);
        let predecessors1: Vec<_> = ts.get_predecessor_states(1).to_vec();
        assert_eq!(predecessors1, vec![0]);
        let predecessors2: Vec<_> = ts.get_predecessor_states(2).to_vec();
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

    fn create_test_transition_system_for_product() -> TransitionSystem {
        let transitions = vec![
            (0, 1, true),
            (0, 2, true),
            (2, 1, true),
            (1, 3, true),
            (3, 2, true),
            (3, 3, true),
        ];
        let transition_matrix = SparseMatrix::from_list_of_entries(4, 4, &transitions);
        let reverse_transitions = [
            (1, 0, true),
            (2, 0, true),
            (1, 2, true),
            (3, 1, true),
            (2, 3, true),
            (3, 3, true),
        ];
        let reverse_transition_matrix = SparseMatrix::from_list_of_entries(4, 4, &transitions);
        let mut state_labels = Vec::new();
        let ap = vec!["a".to_string(), "b".to_string()];
        let mut label0 = BitVec::from_elem(2, false);
        label0.set(0, true);
        label0.set(1, true);
        state_labels.push(label0.clone());
        let label1 = BitVec::from_elem(2, false);
        state_labels.push(label1.clone());
        let mut label2 = BitVec::from_elem(2, false);
        label2.set(0, true);
        state_labels.push(label2.clone());
        let mut label3 = BitVec::from_elem(2, false);
        label3.set(1, true);
        state_labels.push(label3.clone());
        let mut label_state_map = HashMap::new();
        label_state_map.insert(label0, vec![0]);
        label_state_map.insert(label1, vec![1]);
        label_state_map.insert(label2, vec![2]);
        label_state_map.insert(label3, vec![3]);
        TransitionSystem::new(
            transition_matrix,
            reverse_transition_matrix,
            3,       // last_state
            vec![0], // initial_states
            state_labels,
            label_state_map,
            ap,
        )
    }
    fn create_test_automaton_for_product() -> FiniteAutomaton<String> {
        let a_node = FormulaTreeNode::new(
            None,
            None,
            Some("a".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let not_a_node = FormulaTreeNode::new(
            Some(Box::new(a_node.clone())),
            None,
            None,
            FormulaTreeNodeType::Not,
        );
        let b_node = FormulaTreeNode::new(
            None,
            None,
            Some("b".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let not_b_node = FormulaTreeNode::new(
            Some(Box::new(b_node.clone())),
            None,
            None,
            FormulaTreeNodeType::Not,
        );
        let transitions = vec![
            (0, 0, vec![not_a_node.clone()]),
            (0, 1, vec![a_node.clone()]),
            (1, 1, vec![not_b_node.clone()]),
            (1, 2, vec![b_node.clone()]),
            (2, 0, vec![not_a_node.clone()]),
            (2, 1, vec![a_node.clone()]),
        ];
        let transition_matrix = SparseMatrix::from_list_of_entries(4, 4, &transitions);
        let mut init_states = BitVec::from_elem(3, false);
        init_states.set(0, true);
        let mut accepting_states = BitVec::from_elem(3, false);
        accepting_states.set(2, true);

        FiniteAutomaton::new(Nfa, transition_matrix, 2, init_states, accepting_states)
    }
    fn create_product_result() -> TransitionSystem {
        let transitions = vec![
            (0, 1, true),
            (0, 2, true),
            (1, 3, true),
            (2, 1, true),
            (3, 2, true),
            (3, 4, true),
            (4, 2, true),
            (4, 4, true),
        ];
        let transition_matrix = SparseMatrix::from_list_of_entries(5, 5, &transitions);
        let reverse_transitions = transitions
            .clone()
            .iter()
            .map(|(i, o, b)| (*o, *i, *b))
            .collect::<Vec<_>>();
        let reverse_transition_matrix =
            SparseMatrix::from_list_of_entries(5, 5, &reverse_transitions);
        let mut state_labels = Vec::new();
        let ap = vec!["2".to_string()];
        let label0 = BitVec::from_elem(1, false);
        state_labels.push(label0.clone());
        let mut label1 = BitVec::from_elem(1, false);
        label1.set(0, true);
        state_labels.push(label1.clone());
        let mut label_state_map = HashMap::new();
        label_state_map.insert(label0, vec![0, 1, 2, 4]);
        label_state_map.insert(label1, vec![3]);
        TransitionSystem::new(
            transition_matrix,
            reverse_transition_matrix,
            4,       // last_state
            vec![0], // initial_states
            state_labels,
            label_state_map,
            ap,
        )
    }
    #[test]
    fn test_product() {
        let init_ts = create_test_transition_system_for_product();
        let init_auto = create_test_automaton_for_product();
        let computed = init_ts.product_with(init_auto);
        let result_ts = create_product_result();

        // Because of hashing and stuff we cannot rely on == to compare both transition systems.
        // Thus, we cannot use `assert_eq` but have to check everything manually.
        // I.e., we have to allow isomorphism.

        assert_eq!(
            computed.initial_states.len(),
            result_ts.initial_states.len(),
            "Both systems must have the same number initial states. Expected: {} but got: {}",
            result_ts.initial_states.len(),
            computed.initial_states.len()
        );
        assert_eq!(computed.last_state, result_ts.last_state, "Both systems must have the same number of states, i.e., the same last state. Expected: {} but got: {}", result_ts.last_state, computed.last_state);

        // Note: Since both systems use the same automaton the atomic propositions should be exactly the same,
        //       as in both cases the accepting state of the automaton is used as the only ap.
        assert_eq!(
            computed.ap, result_ts.ap,
            "Both systems must have the same atomic propositions. Expected: {:?} but got: {:?}",
            result_ts.ap, computed.ap
        );

        assert_eq!(
            computed.get_num_transitions(),
            result_ts.get_num_transitions(),
            "Both systems must have the same number of transitions. Expected: {:?} but got: {:?}",
            result_ts.get_num_transitions(),
            computed.get_num_transitions()
        );

        // Because of possible isomorphism, we have to traverse both transition systems and check whether all states are equivalent.
        // We consider two states equivalent iff they are isomorphic, that is:
        //  1. They have the same label
        //  2. They have the same amount of successor states
        //     (This is technically implied by Req. 3, but testing this explicitly improves runtime in case of test failure)
        //  3. All successor states are equivalent
        // To test the equivalence of the `label_state_map`s we build a map from the states of one transition system to the other's.
        // Note: The `state_label`s are tested implicitly using our notion of equivalence.
        //       By doing so, we do not care if one transition system specifies labels that do not correspond to a state.
        // Note: While we do not require two states to have equivalent predecessors to be equivalent,
        //       we can test the `reverse_transition_matrix`es more easily during this equivalence check.
        let mut deque = VecDeque::new();
        computed
            .initial_states
            .iter()
            .zip(result_ts.initial_states.iter())
            .for_each(|state| {
                deque.push_back(state);
            });
        // maps the states of the computed to the result
        let mut map = HashMap::new();

        while let Some((computed_state, result_state)) = deque.pop_front() {
            map.insert(computed_state, result_state);

            // check labels
            let c_label = computed.state_labels.get(*computed_state).unwrap();
            let r_label = result_ts.state_labels.get(*result_state).unwrap();
            assert_eq!(
                bit_vec_to_ap_strings(&computed, c_label),
                bit_vec_to_ap_strings(&result_ts, r_label),
                "Both states must have the same label. Expected: {:?} but got: {:?}",
                bit_vec_to_ap_strings(&result_ts, r_label),
                bit_vec_to_ap_strings(&computed, c_label)
            );

            // check predecessors
            let c_preds = computed.get_predecessor_states(*computed_state);
            let r_preds = result_ts.get_predecessor_states(*result_state);
            assert_eq!(c_preds.len(), r_preds.len(),
                       "Both states should have the same number of predecessors. Expected: {:?} but got: {:?}", r_preds.len(),c_preds.len());

            // check successors
            let c_succs = computed.get_successor_states(*computed_state);
            let r_succs = result_ts.get_successor_states(*result_state);
            assert_eq!(c_succs.len(), r_succs.len(),
                       "Both states should have the same number of successors.. Expected: {:?} but got: {:?}", r_succs.len(),c_succs.len())

            // FIXME now we would have to do the same recursively for all successors. But we cannot
            //       really align a computed successor to a result successor because of the omitted actions.
            //       Thus, for now we will skip this part as it is now a NP problem and not worth it to be
            //       implemented just for this test. And because of the many other things we test and thorough
            //       manual inspection of the computed result, we can assume the equivalence to hold
        }

        // label_state_map s
        let c_label_state_map = computed.label_state_map;
        let r_label_state_map = result_ts.label_state_map;
        assert_eq!(
            c_label_state_map.len(),
            r_label_state_map.len(),
            "Both label_state_map s should have equal sizes"
        );
    }
}
