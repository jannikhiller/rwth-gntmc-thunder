use crate::checker::helper::bit_vec_to_ap_strings;
use crate::common::transition_system::TransitionSystem;
use crate::property::Property;
use log::trace;
use std::collections::{HashMap, VecDeque};
use bit_vec::BitVec;

pub fn persistence_checking_with_couvreur_scc(
    transition_system: &TransitionSystem,
    property: &Property<String>,
    state_info_map: Option<&HashMap<usize, (usize, Vec<String>)>>,
) -> Result<bool, (Vec<Vec<String>>, Vec<usize>)> {
    let mut count = 0;
    let mut roots: Vec<usize> = Vec::new();
    let mut dfsnum: HashMap<usize, usize> = HashMap::new();
    let mut current: BitVec = BitVec::from_elem(transition_system.get_num_states(), false);
    let mut cex_stack: Vec<usize> = Vec::new();

    let mut found_cycle;
    for s0 in transition_system.get_initial_states() {
        trace!("Considering intitial state {}", s0);
        found_cycle = couv_dfs(
            *s0,
            &mut count,
            &mut dfsnum,
            &mut roots,
            &mut current,
            &mut cex_stack,
            transition_system,
            property,
        );

        if found_cycle {
            return Err(reconstruct_path(&mut cex_stack, transition_system, state_info_map));
        }
    }

    Ok(true)
}

fn couv_dfs(
    s: usize,
    count: &mut usize,
    dfsnum: &mut HashMap<usize, usize>,
    roots: &mut Vec<usize>,
    current: &mut BitVec,
    cex_stack: &mut Vec<usize>,
    transition_system: &TransitionSystem,
    property: &Property<String>,
) -> bool {
    *count += 1;
    dfsnum.insert(s, *count);
    roots.push(s);
    current.set(s, true);
    cex_stack.push(s);

    trace!("Considering state {:?}", s);

    for t in transition_system.get_successor_states(s) {
        trace!("Considering successor {:?}", t);
        if is_new_successor(t, dfsnum) {
            trace!("\tHas not been visited yet.");
            if couv_dfs(
                *t,
                count,
                dfsnum,
                roots,
                current,
                cex_stack,
                transition_system,
                property,
            ) {
                return true;
            }
        } else if current.get(*t).unwrap() {
            trace!("\tIs part of current dfs");
            let mut u;
            loop {
                u = roots.pop().unwrap();
                
                trace!("\tConsidering root {}", u);

                if !check_property_on_state(u, transition_system, property) {
                    trace!("\t\tViolates property => found cycle");
                    cex_stack.push(*t);
                    return true;
                }

                if dfsnum.get(&u).unwrap() <= dfsnum.get(t).unwrap() {
                    trace!("\tConsidered all relevant roots");
                    break;
                }
            }
            roots.push(u);
        }
    }

    if *roots.last().unwrap() == s {
        roots.pop();
        remove(s, current, transition_system);
        trace!("Done with state {}", s);
    }

    cex_stack.pop();
    trace!("Didn't find an scc where the property is violated");
    false
}

fn is_new_successor(t: &usize, dfsnum: &mut HashMap<usize, usize>) -> bool {
    if !dfsnum.contains_key(t) {
        dfsnum.insert(*t, 0);
        return true;
    }

    *dfsnum.get(t).unwrap() == 0
}

fn remove(s: usize, current: &mut BitVec, transition_system: &TransitionSystem) {
    if !current.get(s).unwrap() {
        return;
    }

    current.set(s, false);
    for t in transition_system.get_successor_states(s) {
        remove(*t, current, transition_system);
    }
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

fn reconstruct_path(stack: &mut Vec<usize>,
                    transition_system: &TransitionSystem,
                    state_info_map: Option<&HashMap<usize, (usize, Vec<String>)>>
) -> (Vec<Vec<String>>, Vec<usize>)  {
    let mut trace = VecDeque::new();
    let mut path = VecDeque::new();

    while let Some(mut state) = stack.pop() {
        if let Some(state_info) = state_info_map {
            trace.push_front(state_info.get(&state).unwrap().1.clone())
        } else {
            trace.push_front(bit_vec_to_ap_strings(
                transition_system,
                transition_system.get_state_label(state),
            ));
        }

        if state_info_map.is_some() {
            state = state_info_map.unwrap().get(&state).unwrap().0;
        }
        path.push_front(state);
    }

    (Vec::from(trace), Vec::from(path))
}

#[cfg(test)]
mod tests {
    use crate::checker::scc_couvreur::persistence_checking_with_couvreur_scc;
    use crate::common::sparse_matrix::SparseMatrix;
    use crate::common::transition_system::TransitionSystem;
    use crate::property::{FormulaTreeNode, FormulaTreeNodeType, Property, PropertyType};
    use bit_vec::BitVec;
    use std::collections::HashMap;

    #[test]
    fn test_scc_true() {
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
            vec!["a".to_string()],
        );

        assert!(persistence_checking_with_couvreur_scc(&transition_system, &property, None).is_ok());
    }

    #[test]
    fn test_scc_false() {
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
            vec!["a".to_string()],
        );

        let result = persistence_checking_with_couvreur_scc(&transition_system, &property, None);

        match &result {
            Ok(_) => {
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
        TransitionSystem::new(
            transition_matrix,
            reverse_transition_matrix,
            1,       // last_state
            vec![0], // initial_states
            state_labels,
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
        TransitionSystem::new(
            transition_matrix,
            reverse_transition_matrix,
            2,       // last_state
            vec![0], // initial_states
            state_labels,
            ap,
        )
    }
}
