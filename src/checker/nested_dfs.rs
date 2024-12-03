use crate::common::transition_system::TransitionSystem;
use crate::parser::property::Property;

use crate::checker::helper::bit_vec_to_ap_strings;
use log::{debug, trace};
use std::collections::{HashSet, VecDeque};

/// Checks if the given transition system satisfies the given persistence property by applying the
/// nested DFS algorithm presented in the lecture.
///
/// # Parameters
///
/// - `transition_system`: The given transition system which gets checked.
/// - `property`: The property to be checked on the given transition system.
///
/// # Returns
/// A Result with `Ok` if the property is fulfilled and Err with a path and a trace otherwise.
pub fn persistence_checking_with_nested_dfs(
    transition_system: &TransitionSystem,
    property: &Property<String>,
) -> Result<bool, (Vec<Vec<String>>, Vec<usize>)> {
    outer_dfs(transition_system, property)
}

fn outer_dfs(
    transition_system: &TransitionSystem,
    property: &Property<String>,
) -> Result<bool, (Vec<Vec<String>>, Vec<usize>)> {
    let mut set_u = HashSet::new(); // set U
    let mut pi = VecDeque::new(); // stack pi
    let mut set_v = HashSet::new(); // set V
    let mut xi = VecDeque::new(); // stack xi

    trace!(
        "Found initial states: {:?}",
        transition_system.get_initial_states()
    );
    trace!(
        "Successor states of initial state: {:?}",
        transition_system
            .get_successor_states(*transition_system.get_initial_states().first().unwrap())
    );

    let initial_states_set = transition_system
        .get_initial_states()
        .iter()
        .cloned()
        .collect::<HashSet<usize>>();

    while !initial_states_set.is_subset(&set_u) {
        let difference = initial_states_set
            .difference(&set_u)
            .cloned()
            .collect::<HashSet<_>>();
        let s_0 = *difference.iter().next().unwrap(); // choose s_0 \in S_0 \setminus U
        set_u.insert(s_0);
        pi.push_back(s_0);

        while !pi.is_empty() {
            let s = pi.back().cloned().unwrap();

            let successor_states = transition_system
                .get_successor_states(s)
                .iter()
                .cloned()
                .collect::<HashSet<_>>();
            if !successor_states.is_subset(&set_u) {
                let s_prime = successor_states.difference(&set_u).cloned().next().unwrap(); // choose s' \in Post(s) \setminus U
                trace!("Chose {} for s'", s_prime);
                set_u.insert(s_prime);
                pi.push_back(s_prime);
            } else {
                pi.pop_back();

                if !check_property_on_state(s, transition_system, property)
                    && cycle_check(s, &mut set_v, &mut xi, transition_system)
                {
                    trace!("{:?}", transition_system.get_state_label(s));
                    debug!("Found violation of persistence property.");
                    return Err(reconstruct_path(&mut pi, &mut xi, transition_system));
                }
            }
        }
    }

    Ok(true)
}

fn check_property_on_state(
    state: usize,
    transition_system: &TransitionSystem,
    property: &Property<String>,
) -> bool {
    let bit_label = transition_system.get_state_label(state);
    let string_labels_of_current = bit_vec_to_ap_strings(transition_system, bit_label);

    property.evaluate(&string_labels_of_current)
}

fn cycle_check(
    state: usize,
    set_v: &mut HashSet<usize>,
    xi: &mut VecDeque<usize>,
    transition_system: &TransitionSystem,
) -> bool {
    xi.push_back(state);
    while !xi.is_empty() {
        let current_state = *xi.back().unwrap();

        let successor_states_of_current_state = transition_system
            .get_successor_states(current_state)
            .iter()
            .cloned()
            .collect::<HashSet<usize>>();
        if successor_states_of_current_state.contains(&state) {
            xi.push_back(state);
            return true;
        } else if !successor_states_of_current_state.is_subset(&set_v) {
            let &s_pprime = successor_states_of_current_state.iter().next().unwrap();
            trace!("Chose {} for s''", s_pprime);
            set_v.insert(s_pprime);
            xi.push_back(s_pprime);
        } else {
            xi.pop_back();
        }
    }

    false
}

fn reconstruct_path(
    pi: &mut VecDeque<usize>,
    xi: &mut VecDeque<usize>,
    transition_system: &TransitionSystem,
) -> (Vec<Vec<String>>, Vec<usize>) {
    trace!("Constructing counterexample...");

    let mut trace = Vec::new();
    let mut path = Vec::new();

    while !pi.is_empty() {
        path.push(pi.pop_front().unwrap());
    }

    debug!("Looping part of counterexample:");
    while !xi.is_empty() {
        let state = xi.pop_front().unwrap();
        debug!("{}, ", state);
        path.push(state);
    }

    debug!("Length of counterexample: {:?}", path.len());
    for state in &path {
        trace.push(bit_vec_to_ap_strings(
            transition_system,
            transition_system.get_state_label(*state),
        ));
        debug!("{:?}, ", state);
    }

    (trace, path)
}

#[cfg(test)]
mod tests {
    use crate::checker::nested_dfs::persistence_checking_with_nested_dfs;
    use crate::common::sparse_matrix::SparseMatrix;
    use crate::common::transition_system::TransitionSystem;
    use crate::parser::property::{FormulaTreeNode, FormulaTreeNodeType, Property, PropertyType};
    use bit_vec::BitVec;
    use std::collections::HashMap;

    #[test]
    fn test_nested_dfs_true() {
        let transition_system = create_test_transition_system_1();

        // create formula with only "a"
        let root = FormulaTreeNode::new(
            None,
            None,
            Some("a".to_string()),
            FormulaTreeNodeType::Atomic,
        );

        let property = Property::new(
            "PersistenceProperty".to_string(),
            PropertyType::Persistence(root),
        );

        assert!(persistence_checking_with_nested_dfs(&transition_system, &property).is_ok());
    }

    #[test]
    fn test_nested_dfs_false() {
        let transition_system = create_test_transition_system_2();

        // create formula with only "a"
        let root = FormulaTreeNode::new(
            None,
            None,
            Some("a".to_string()),
            FormulaTreeNodeType::Atomic,
        );

        let property = Property::new(
            "PersistenceProperty".to_string(),
            PropertyType::Persistence(root),
        );

        let result = persistence_checking_with_nested_dfs(&transition_system, &property);

        match &result {
            Ok(success) => {
                panic!("Property should fail!")
            }
            Err((counterexample, trace_indexes)) => {
                println!("The property does not hold.");
                println!("Counterexample: {:?}", counterexample);
                println!("Trace indexes: {:?}", trace_indexes);

                // Optionally include assertions to validate the counterexample.
                assert!(
                    !counterexample.is_empty(),
                    "Expected non-empty counterexample."
                );
            }
        }

        assert!(result.is_err());
    }

    fn create_test_transition_system_1() -> TransitionSystem {
        let transitions = vec![
            vec![false, true], // State 0 -> State 1
            vec![false, true], // State 1 -> State 1
        ];
        let transition_matrix = SparseMatrix::from_2d_vec(&transitions);
        let reverse_transitions = vec![
            vec![false, false],
            vec![true, true], // State 1 <- State 0, State 1 <- State 1
        ];
        let reverse_transition_matrix = SparseMatrix::from_2d_vec(&reverse_transitions);
        let mut state_labels = Vec::new();
        let ap = vec!["a".to_string()];
        let label0 = BitVec::from_elem(1, false);
        state_labels.push(label0.clone());
        let mut label1 = BitVec::from_elem(1, false);
        label1.set(0, true);
        state_labels.push(label1.clone());
        let mut label_state_map = HashMap::new();
        label_state_map.insert(label0, vec![0]);
        label_state_map.insert(label1, vec![1]);
        TransitionSystem::new(
            transition_matrix,
            reverse_transition_matrix,
            1,       // last_state
            vec![0], // initial_states
            state_labels,
            label_state_map,
            ap,
        )
    }

    fn create_test_transition_system_2() -> TransitionSystem {
        let transitions = vec![
            vec![false, true, true],  // State 0 -> State 1, State 0 -> State 2
            vec![false, true, false], // State 1 -> State 1
            vec![false, false, true], // State 2 -> State 2
        ];
        let transition_matrix = SparseMatrix::from_2d_vec(&transitions);
        let reverse_transitions = vec![
            vec![false, false, false],
            vec![true, true, false], // State 1 <- State 0, State 1 <- State 1
            vec![true, false, true], // State 2 <- State 0, State 2 <- State 2
        ];
        let reverse_transition_matrix = SparseMatrix::from_2d_vec(&reverse_transitions);
        let mut state_labels = Vec::new();
        let ap = vec!["a".to_string(), "b".to_string()];
        let label0 = BitVec::from_elem(2, false);
        state_labels.push(label0.clone());
        let mut label1 = BitVec::from_elem(2, false);
        label1.set(0, true);
        state_labels.push(label1.clone());
        let mut label2 = BitVec::from_elem(2, false);
        label2.set(1, true);
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
}
