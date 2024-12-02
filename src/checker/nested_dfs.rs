use crate::common::transition_system::TransitionSystem;
use crate::parser::property::{Property, PropertyType};

use std::collections::{HashSet, VecDeque};
use log::{debug, trace};
use crate::checker::helper::bit_vec_to_ap_strings;

/// Checks if the given transition system satisfies the given persistence property by applying the
/// nested DFS algorithm presented in the lecture. Hence, it takes a transition system and an NBA,
/// constructs the product of both and checks whether there is a loop, containing an accepting state
/// of the NBA, reachable within this product.
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
    property: &Property<String>) -> Result<bool, (Vec<Vec<String>>, Vec<usize>)> {
    match property.property_type.clone() {
        PropertyType::Persistence(automaton) => {
            let product_of_ts_and_nba = transition_system.product_with(automaton.clone());
            outer_dfs(&product_of_ts_and_nba)
        }
        | PropertyType::RegularSafety(_) | PropertyType::OmegaRegular(_) | PropertyType::Invariant(_) =>
            panic!("Wrong model checking algorithm chosen for the given property.")
    }
}

fn outer_dfs(transition_system: &TransitionSystem) -> Result<bool, (Vec<Vec<String>>, Vec<usize>)> {
    let mut set_u = HashSet::new(); // set U
    let mut pi = VecDeque::new(); // stack pi
    let mut set_v = HashSet::new(); // set V
    let mut xi = VecDeque::new(); // stack xi

    trace!("Found initial states: {:?}", transition_system.get_initial_states());
    trace!("Successor states of initial state: {:?}",
             transition_system.get_successor_states(*transition_system.get_initial_states().first().unwrap()));

    let initial_states_set = transition_system.get_initial_states()
        .into_iter()
        .cloned()
        .collect::<HashSet<usize>>();

    while !initial_states_set.is_subset(&set_u) {
        let difference = initial_states_set.difference(&set_u).cloned().collect::<HashSet<_>>();
        let s_0 = *difference.iter().next().unwrap(); // choose s_0 \in S_0 \setminus U
        set_u.insert(s_0);
        pi.push_back(s_0);

        while !pi.is_empty() {
            let s = pi.back().cloned().unwrap();

            let successor_states = transition_system.get_successor_states(s)
                .into_iter()
                .cloned()
                .collect::<HashSet<_>>();
            if !successor_states.is_subset(&set_u) {
                let s_prime = successor_states.difference(&set_u)
                    .cloned()
                    .next()
                    .unwrap(); // choose s' \in Post(s) \setminus U
                trace!("Chose {} for s'", s_prime);
                set_u.insert(s_prime);
                pi.push_back(s_prime);
            } else {
                pi.pop_back();

                if !transition_system.get_state_label(s).none()
                    // here we check if the state has any label
                    // this is only the case if it is an accepting state.
                    && cycle_check(s, &mut set_v, &mut xi, transition_system) {
                    trace!("{:?}", transition_system.get_state_label(s));
                    debug!("Found violation of persistence property.");
                    return Err(reconstruct_path(&mut pi, &mut xi, transition_system));
                }
            }
        }
    }

    Ok(true)
}

fn cycle_check(state: usize, visited: &mut HashSet<usize>,
               queue: &mut VecDeque<usize>,
               transition_system: &TransitionSystem) -> bool {
    queue.push_back(state);
    while !queue.is_empty() {
        let current_state = *queue.back().unwrap();

        let successor_states_of_current_state = transition_system.get_successor_states(current_state)
            .into_iter()
            .cloned()
            .collect::<HashSet<usize>>();
        if successor_states_of_current_state.contains(&state) {
            queue.push_back(state);
            return true;
        } else if !successor_states_of_current_state.is_subset(&visited) {
            let &s_pprime =
                successor_states_of_current_state.iter().next().unwrap();
            trace!("Chose {} for s''", s_pprime);
            visited.insert(s_pprime);
            queue.push_back(s_pprime);
        }
    }

    false
}

fn reconstruct_path(pi: &mut VecDeque<usize>, xi: &mut VecDeque<usize>,
                    transition_system: &TransitionSystem) -> (Vec<Vec<String>>, Vec<usize>) {
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
        trace.push(bit_vec_to_ap_strings(transition_system, transition_system.get_state_label(*state)));
        debug!("{:?}, ", state);
    }

    (trace, path)
}

#[cfg(test)]
mod tests {
    use crate::common::sparse_matrix::SparseMatrix;
    use crate::common::transition_system::TransitionSystem;
    use crate::parser::property::{FiniteAutomaton, FormulaTreeNode, FormulaTreeNodeType, Property, PropertyType};
    use bit_vec::BitVec;
    use std::collections::HashMap;
    use log::info;
    use crate::checker::nested_dfs::persistence_checking_with_nested_dfs;
    use crate::parser::property::AcceptanceType::Nfa;

    fn create_test_transition_system_for_product(is_true: bool) -> TransitionSystem {
        let transitions = vec![
            (0, 1, true),
            (0, 2, true),
            (2, 1, true),
            (1, 3, true),
            (3, 2, true),
            (3, 3, true),
        ];
        let transition_matrix = SparseMatrix::from_list_of_entries(4, 4, &transitions);
        let reverse_transition_matrix = SparseMatrix::from_list_of_entries(4, 4, &transitions);
        let mut state_labels = Vec::new();
        let ap = vec!["a".to_string(), "b".to_string()];
        let mut label0 = BitVec::from_elem(2, false);
        if !is_true { // the "a" labels violate the property
            label0.set(0, true);
        }
        label0.set(1, true);
        state_labels.push(label0.clone());
        let label1 = BitVec::from_elem(2, false);
        state_labels.push(label1.clone());
        let mut label2 = BitVec::from_elem(2, false);
        if !is_true {  // the "a" labels violate the property
            label2.set(0, true);
        }
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
            (0, 0, not_a_node.clone()),
            (0, 1, a_node.clone()),
            (1, 1, not_b_node.clone()),
            (1, 2, b_node.clone()),
            (2, 0, not_a_node.clone()),
            (2, 1, a_node.clone()),
        ];
        let transition_matrix = SparseMatrix::from_list_of_entries(4, 4, &transitions);
        let mut init_states = BitVec::from_elem(3, false);
        init_states.set(0, true);
        let mut accepting_states = BitVec::from_elem(3, false);
        accepting_states.set(2, true);

        FiniteAutomaton::new(
            Nfa,
            transition_matrix,
            2,
            init_states,
            accepting_states,
        )
    }

    #[test]
    fn check_persistence_not_satisfied() {
        let transition_system: TransitionSystem = create_test_transition_system_for_product(false);
        let finite_automaton: FiniteAutomaton<String> = create_test_automaton_for_product();

        let property: Property<String> = Property::new("Persistence property".to_string(),
                                                       PropertyType::Persistence(finite_automaton));

        match persistence_checking_with_nested_dfs(&transition_system, &property) {
            Ok(_) => panic!("Expected persistence checking to return an error."),
            Err(_) => println!("Persistence checking failed with an error, as expected.")
        }
    }

    #[test]
    fn check_persistence_satisfied() {
        let transition_system: TransitionSystem = create_test_transition_system_for_product(true);
        let finite_automaton: FiniteAutomaton<String> = create_test_automaton_for_product();

        let property: Property<String> = Property::new("Persistence property".to_string(),
                                                       PropertyType::Persistence(finite_automaton));

        match persistence_checking_with_nested_dfs(&transition_system, &property) {
            Ok(_) => println!("Persistence checking was successful, as label a never occurs and hence the implication is true."),
            Err(_) => panic!("Persistence checking failed with an error.s")
        }
    }
}