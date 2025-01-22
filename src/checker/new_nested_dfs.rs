use std::cmp::PartialEq;
use crate::common::transition_system::TransitionSystem;
use crate::property::property::Property;

use crate::checker::helper::bit_vec_to_ap_strings;
use log::{debug, trace};
use std::collections::{VecDeque};
use bit_vec::BitVec;


/// Checks if the given transition system satisfies the given persistence property by applying the
/// nested DFS algorithm as proposed by Stefan Schwoon and Javier Esparza in their
/// paper `A Note on On-The-Fly Verification Algorithms`. <br />
/// Note that we reimplemented their algorithm into an iterative version to deal with the
/// limitations of the stack size. <br />
/// While the basic of the is outlined here, we refer to the corresponding paper for a
/// more thorough explanation. <br />
/// 
/// ## Idea of the algorithm
/// The main idea of the algorithm is the same as for a traditional nested dfs but each
/// state is annotated with more information. Each state is in one of the following categories:
/// - Visited by neither the outer nor an inner dfs.
/// - Visited by the outer dfs, but it is not yet finished.
/// - The outer dfs on a state is finished. The state has not yet been visited in an inner dfs.
/// - The state has been visited in the outer and an inner dfs.
/// 
/// Each information is represented by a different color represented using 2 bits.
/// For (memory-) efficient representation we use two `BitVec`s for this representation.
///
/// # Parameters
/// - `transition_system`: The given transition system which gets checked.
/// - `property`: The property to be checked on the given transition system.
///
/// # Returns
/// A Result with `Ok` if the property is fulfilled and Err with a path and a trace otherwise.
pub fn persistence_checking_with_nested_dfs(
    transition_system: &TransitionSystem,
    property: &Property<String>,
) -> Result<bool, (Vec<Vec<String>>, Vec<usize>)> {
    let num_ts_states = transition_system.get_num_states();
    let mut bv_one = BitVec::from_elem(num_ts_states, false);
    let mut bv_two = BitVec::from_elem(num_ts_states, false);

    debug!("Starting ndfs.");
    for init_state in transition_system.get_initial_states() {
        trace!("Considering initial state: {}", init_state);

        bv_one.clear();
        bv_two.clear();
        let res = outer_dfs(transition_system, property, *init_state, &mut bv_one, &mut bv_two);

        if res.is_err() {
            return res;
        }
    }
    
    Ok(true)
}

/// Performs the outer dfs used to find states that violate the given property. <br />
/// A state is annotated `Cyan` once it is considered in the outer dfs once. <br />
/// For each state each successor is considered: <br/>
/// If the successor is annotated `Cyan` its outer dfs is not yet finished.
/// If the current state or that successor violates the property,
/// an invalid cycle is found and can be reported.
/// If the successor has not yet been visited by the outer dfs, i.e., it is annotated `White`,
/// that successor is now visited.
/// If the outer dfs on the successor is already finished, or it was even considered in an inner dfs,
/// it does not need to be considered any further. <br />
/// Once a state is fully expanded and it violates the given property,
/// an inner dfs is started on this state. Afterward, the state is annotated `Red` to indicate that
/// an inner dfs was already performed on this state. If the state satisfies the property, it is
/// annotated `Blue` to indicate that the outer dfs has been finished on this state.
fn outer_dfs(
    transition_system: &TransitionSystem,
    property: &Property<String>,
    init_state: usize,
    bv_one: &mut BitVec,
    bv_two: &mut BitVec,
) -> Result<bool, (Vec<Vec<String>>, Vec<usize>)> {
    trace!("Starting outer dfs with state {}", init_state);
    let mut outer_stack = vec![init_state];
    let mut inner_stack = vec![];

    while let Some(state) = outer_stack.pop() {
        if get_color(state, bv_one, bv_two) == Color::White {
            outer_stack.push(state);
            set_color(state, Color::Cyan, bv_one, bv_two);

            for succ in transition_system.get_successor_states(state) {
                trace!("Considering successor {} in outer dfs", succ);
                if get_color(*succ, bv_one, bv_two) == Color::Cyan &&
                    (!check_property_on_state(state, transition_system, property) ||
                        !check_property_on_state(*succ, transition_system, property)) {
                    debug!("Found a cycle in NDFS during outer dfs.");
                    return Err(reconstruct_path(&mut outer_stack, &mut inner_stack, transition_system));
                } else if get_color(*succ, bv_one, bv_two) == Color::White {
                    outer_stack.push(*succ);
                }
            }
        } else if get_color(state, bv_one, bv_two) == Color::Cyan {
            if !check_property_on_state(state, transition_system, property) {
                trace!("Property fulfilled on state {} in outer dfs => starting inner dfs", state);
                let found_cycle = inner_dfs(state, bv_one, bv_two, &mut inner_stack, transition_system);

                if found_cycle {
                    debug!("Found a cycle in NDFS during inner dfs.");
                    return Err(reconstruct_path(&mut outer_stack, &mut inner_stack, transition_system));
                }

                set_color(state, Color::Red, bv_one, bv_two);
            } else {
                trace!("Property not fulfilled on state {} in outer dfs", state);
                set_color(state, Color::Blue, bv_one, bv_two);
            }
        }
    }

    Ok(true)
}

/// Performs the inner dfs used to find cycles. <br />
/// It visits each successor of the given state.
/// If the successor is annotated `Cyan`, its outer dfs is not yet finished. Thus, a cycle that
/// violates the property has been found and can be reported.
/// If it is annotated `Blue`, its outer dfs is finished. Thus, it can be annotated `Red`
/// (since it has now been visited by an inner dfs) and used as the starting point for the next
/// iteration of the inner dfs. 
fn inner_dfs(
    init_state: usize,
    bv_one: &mut BitVec,
    bv_two: &mut BitVec,
    stack: &mut Vec<usize>,
    transition_system: &TransitionSystem,
) -> bool {
    stack.clear();
    stack.push(init_state);

    while let Some(state) = stack.pop() {
        // Add state again in case it is needed for the counterexample
        stack.push(state);

        for succ in transition_system.get_successor_states(state) {
            trace!("Visiting state {} in inner dfs", state);
            if get_color(*succ, bv_one, bv_two) == Color::Cyan {
                return true;
            } else if get_color(*succ, bv_one, bv_two) == Color::Blue {
                set_color(*succ, Color::Red, bv_one, bv_two);
                stack.push(*succ);
            }
        }
        // Pop state again as it is not needed anymore
        stack.pop();
    }

    false
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

fn reconstruct_path(
    outer_stack: &mut Vec<usize>,
    inner_stack: &mut Vec<usize>,
    transition_system: &TransitionSystem,
) -> (Vec<Vec<String>>, Vec<usize>) {
    debug!("Constructing counterexample...");

    let mut trace = Vec::new();
    let mut path = VecDeque::new();

    while let Some(state) = outer_stack.pop() {
        path.push_front(state);
    }

    trace!("Looping part of counterexample:");
    while let Some(state) = inner_stack.pop() {
        trace!("{}, ", state);
        path.push_front(state);
    }

    trace!("Length of counterexample: {:?}", path.len());
    for state in &path {
        trace.push(bit_vec_to_ap_strings(
            transition_system,
            transition_system.get_state_label(*state),
        ));
        trace!("{:?}, ", state);
    }

    (trace, Vec::from(path))
}


/// The algorithm uses colors to encode certain information about each state.
/// The available colors are listed in this enum.
/// - `White`: The initial color of each state. The state has not yet been visited by any dfs.
/// - `Cyan`: A state whose outer dfs has not yet terminated.
/// - `Blue`: A state whose outer dfs has terminated but was not yet reached in an inner dfs.
/// - `Red`: A state that has been considered in an outer and an inner dfs.
#[derive(PartialEq, Debug)]
enum Color {
    White,
    Cyan,
    Blue,
    Red,
}

/// Sets the color of the given `state` to the given value in the given `BitVec`s <br />
/// Note that `bv_two` is the highest-order bit.
fn set_color(state: usize, color: Color, bv_one: &mut BitVec, bv_two: &mut BitVec) {
    match color {
        Color::White => {
            bv_one.set(state, false);
            bv_two.set(state, false);
        }
        Color::Cyan => {
            bv_one.set(state, true);
            bv_two.set(state, false);
        }
        Color::Blue => {
            bv_one.set(state, false);
            bv_two.set(state, true);
        }
        Color::Red => {
            bv_one.set(state, true);
            bv_two.set(state, true);
        }
    }
}

/// Returns the color of the given `state` as stored in the given `BitVec`s <br />
/// Note that `bv_two` is the highest-order bit.
fn get_color(state: usize, bv_one: &BitVec, bv_two: &BitVec) -> Color {
    let bit_one = bv_one.get(state).unwrap();
    let bit_two = bv_two.get(state).unwrap();

    if !bit_one && !bit_two {
        Color::White
    } else if bit_one && !bit_two {
        Color::Cyan
    } else if !bit_one && bit_two {
        Color::Blue
    } else {
        Color::Red
    }
}


#[cfg(test)]
mod tests {
    use crate::checker::new_nested_dfs::persistence_checking_with_nested_dfs;
    use crate::common::sparse_matrix::SparseMatrix;
    use crate::common::transition_system::TransitionSystem;
    use crate::property::property::{FormulaTreeNode, FormulaTreeNodeType, Property, PropertyType};
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
