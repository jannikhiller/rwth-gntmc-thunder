use crate::checker::helper::bit_vec_to_ap_strings;
use crate::common::transition_system::TransitionSystem;
use crate::property::property::{FormulaTreeNode, FormulaTreeNodeType, Property, PropertyType};
use bit_vec::BitVec;
use std::collections::HashMap;
use std::ops::Shl;
use itertools::Itertools;
use log::{debug, trace};

pub fn ctl_checking(
    transition_system: &TransitionSystem,
    property: &Property<String>,
) -> Result<bool, (Vec<Vec<String>>, Vec<usize>)> {
    let mut cache: HashMap<String, BitVec> = HashMap::new();

    match &property.property_type {
        PropertyType::Ctl(formula) => {
            debug!("Checking CTL-formula: \n{}", formula);
            // check if all initial states are in the sat set of the given formula
            let sat_set = compute_sat_set(transition_system, &formula.clone(), &mut cache);
            // trace!("Obtained satisfaction set as bitvector: {}", sat_set);
            for init_state in transition_system.get_initial_states() {
                if !sat_set.get(*init_state).unwrap() {
                    // found initial state that is not part of the satisfaction set => violation
                    return Err((vec![], vec![]));
                }
            }
            Ok(true)
        }
        _ => {
            panic!("Computing the satisfaction set is only possible for CTL formulae.");
        }
    }
}

fn compute_sat_set(
    transition_system: &TransitionSystem,
    formula: &FormulaTreeNode<String>,
    cache: &mut HashMap<String, BitVec>
) -> BitVec {
    debug!("Computing satisfaction set for formula \n{}", formula.to_string());

    if cache.contains_key(&formula.to_string()) {
        debug!("Found satisfaction set in cache for formula: \n{}", formula.to_string());
        return cache.get(&formula.to_string()).unwrap().clone();
    }

    let res = match formula.node_type {
        FormulaTreeNodeType::True => compute_sat_set_true(transition_system),
        FormulaTreeNodeType::Atomic => compute_sat_set_atomic(transition_system, formula.clone()),
        FormulaTreeNodeType::Not => compute_sat_set_not(transition_system, formula.clone(), cache),
        FormulaTreeNodeType::And => compute_sat_set_and(transition_system, formula.clone(), cache),
        FormulaTreeNodeType::Exists => {
            let left_node = formula
                .clone()
                .left
                .expect("Left child of exists nodes must be set.");
            match left_node.node_type {
                FormulaTreeNodeType::Next => compute_sat_set_of_exists_next(transition_system, *formula.left.clone().unwrap(), cache),
                FormulaTreeNodeType::Until => compute_sat_set_of_exists_until(transition_system, *formula.left.clone().unwrap(), cache),
                FormulaTreeNodeType::Globally => compute_sat_set_of_exists_globally(transition_system, *formula.left.clone().unwrap(), cache),
                _ => panic!("Invalid property: Exists may not be followed by something other than NEXT, UNTIL, or GLOBALLY."),
            }
        }
        _ => panic!("Tried to check a CTL property that is not in ENF"),
    };

    cache.insert(formula.to_string(), res.clone());

    trace!("Finished satisfaction set");

    res
}

fn compute_sat_set_true(transition_system: &TransitionSystem) -> BitVec {
    trace!("Computing satisfaction sets for TRUE...");
    BitVec::from_elem(transition_system.get_num_states(), true)
}

fn compute_sat_set_atomic(
    transition_system: &TransitionSystem,
    formula: FormulaTreeNode<String>,
) -> BitVec {
    trace!("Computing satisfaction sets for ATOMIC...");
    let mut set = BitVec::from_elem(transition_system.get_num_states(), false);
    for state in 0..transition_system.get_num_states() {
        let label =
            bit_vec_to_ap_strings(transition_system, transition_system.get_state_label(state));
        set.set(state, formula.evaluate(&label));
    }
    set
}

fn compute_sat_set_not(
    transition_system: &TransitionSystem,
    formula: FormulaTreeNode<String>,
    cache: &mut HashMap<String, BitVec>
) -> BitVec {
    trace!("Computing satisfaction sets for NOT...");
    let child = formula.left.unwrap();
    let mut set = compute_sat_set(transition_system, &*child, cache);
    set.negate();
    trace!("Finished satisfaction sets for NOT");
    set
}

fn compute_sat_set_and(
    transition_system: &TransitionSystem,
    formula: FormulaTreeNode<String>,
    cache: &mut HashMap<String, BitVec>
) -> BitVec {
    trace!("Computing satisfaction sets for AND...");
    let left = formula.left.unwrap();
    let right = formula.right.unwrap();

    trace!("Computing left satisfaction set...");
    let mut set_left = compute_sat_set(transition_system, &*left, cache);
    trace!("Finished left satisfaction sets.\nStarting righ...");
    let set_right = compute_sat_set(transition_system, &*right, cache);
    trace!("Finished right satisfaction set.");

    set_left.and(&set_right);
    trace!("Finished satisfaction sets for AND");
    set_left
}

fn compute_sat_set_of_exists_until(
    transition_system: &TransitionSystem,
    formula: FormulaTreeNode<String>,
    cache: &mut HashMap<String, BitVec>
) -> BitVec {
    trace!("Computing satisfaction sets for EXISTS UNTIL...");
    let left = formula.left.unwrap();
    let right = formula.right.unwrap();

    trace!("Computing satisfaction set of right subformula.");
    let mut set_t = compute_sat_set(transition_system, &right, cache);
    trace!("Finished satisfaction set of right subformula.");
    let mut set_e = set_t.clone();
    trace!("Computing satisfaction set of left subformula.");
    let sat_left = compute_sat_set(transition_system, &left, cache);
    trace!("Finished satisfaction set of left subformula.");

    while set_e.any() {
        let mut s_prime = 0;
        for (state_index, b) in set_e.iter().enumerate() {
            if b {
                s_prime = state_index;
                trace!("Chose state {} as s'", s_prime);
                set_e.set(state_index, false);
                break;
            }
        }

        for state in transition_system.get_predecessor_states(s_prime) {
            trace!("Checking predecessor state {}", state);
            let mut sat_left_minus_set_t = sat_left.clone();
            sat_left_minus_set_t.difference(&set_t);

            if sat_left_minus_set_t.get(*state).unwrap() {
                set_t.set(*state, true);
                set_e.set(*state, true);
            }
        }
    }

    set_t
}

/// Function to compute the satisfaction set for a CTL-(sub)formula of form exists globally phi
/// incorporating the linear-time algorithm using counters from the lecture (lecture #11, slide 31).
///
/// # Parameters
///
/// - `transition_system`: The given transition system to compute the satisfaction set on.
/// - `formula`: The CTL-(sub)formula in question.
///
/// # Returns
/// The satisfaction set with respect to the given CTL-(sub)formula
fn compute_sat_set_of_exists_globally(
    transition_system: &TransitionSystem,
    formula: FormulaTreeNode<String>,
    cache: &mut HashMap<String, BitVec>
) -> BitVec {
    trace!("Computing satisfaction sets for EXISTS GLOBALLY...");
    let mut set_t = compute_sat_set(transition_system, &formula.left.unwrap(), cache);
    let mut set_e = set_t.clone();
    set_e.negate();

    let mut c = HashMap::new();
    for (curr_state, b) in set_t.iter().enumerate() {
        if b {
            // count and store number of successors of current state
            c.insert(
                curr_state,
                transition_system.get_successor_states(curr_state).len(),
            );
            trace!("Inserted state c[{}] = {}", curr_state,
                transition_system.get_successor_states(curr_state).len());
        }
    }

    while set_e.any() {
        let mut s_prime = 0;
        for (curr_state, b) in set_e.iter().enumerate() {
            if b {
                s_prime = curr_state;
                trace!("Chose state {} as s'", s_prime);
                set_e.set(s_prime, false);
                break;
            }
        }

        for predecessor_state in transition_system.get_predecessor_states(s_prime) {
            trace!("Checking predecessor state {}", predecessor_state);
            if set_t.get(*predecessor_state).unwrap() {
                trace!("Predecessor state {} is in satisfaction set of phi", predecessor_state);
                c.insert(*predecessor_state, c.get(predecessor_state).unwrap() - 1);
                if *c.get(predecessor_state).unwrap() == 0 {
                    set_t.set(*predecessor_state, false);
                    set_e.set(*predecessor_state, true);
                }
            }
        }
    }

    set_t
}

fn compute_sat_set_of_exists_next(
    transition_system: &TransitionSystem,
    formula: FormulaTreeNode<String>,
    cache: &mut HashMap<String, BitVec>
) -> BitVec {
    trace!("Computing satisfaction sets for EXISTS NEXT...");
    let sat_set = compute_sat_set(transition_system, &formula.left.unwrap(), cache);
    let mut result_set = BitVec::from_elem(transition_system.get_num_states(), false);

    for state in 0..transition_system.get_num_states() {
        let successor_states = transition_system.get_successor_states(state);
        'inner: for successor_state in successor_states.iter() {
            if sat_set.get(*successor_state).unwrap() {
                result_set.set(state, true);
                // it suffices to find one such successor state, as we only check for not \emptyset
                break 'inner;
            }
        }
    }

    result_set
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use bit_vec::BitVec;
    use crate::checker::ctl::*;
    use crate::common::sparse_matrix::SparseMatrix;
    use crate::common::transition_system::TransitionSystem;
    use crate::property::property::{FormulaTreeNode, FormulaTreeNodeType};

    fn build_test_ts() -> TransitionSystem {
        let transitions = vec![
            (0, 1, true),
            (0, 3, true),
            (1, 2, true),
            (2, 2, true),
            (2, 3, true),
            (3, 0, true),
        ];
        let transition_matrix = SparseMatrix::from_list_of_entries(6, 6, &transitions);
        let reverse_transitions = vec![
            (1, 0, true),
            (3, 0, true),
            (1, 2, true),
            (2, 2, true),
            (3, 2, true),
            (0, 3, true),
        ];
        let reverse_transition_matrix = SparseMatrix::from_list_of_entries(6, 6, &reverse_transitions);

        let mut state_labels = Vec::new();
        let ap = vec!["a".to_string(), "b".to_string(), "c".to_string(), "d".to_string(), "e".to_string()];

        let mut label0 = BitVec::from_elem(5, false);
        label0.set(0, true);
        label0.set(4, true);
        state_labels.push(label0.clone());
        let mut label1 = BitVec::from_elem(5, false);
        label1.set(1, true);
        state_labels.push(label1.clone());
        let mut label2 = BitVec::from_elem(5, false);
        label2.set(2, true);
        state_labels.push(label2.clone());
        let mut label3 = BitVec::from_elem(5, false);
        label3.set(3, true);
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

    #[test]
    fn test_true() {
        let ts = build_test_ts();
        let sat_set = compute_sat_set_true(&ts);

        assert_eq!(sat_set, BitVec::from_elem(ts.get_num_states(), true));
    }
    
    #[test]
    fn test_atomic() {
        let ts = build_test_ts();
        let formula_a = FormulaTreeNode::new(
            None, None, Some("a".to_string()), FormulaTreeNodeType::Atomic
        );
        let mut res_a = BitVec::from_elem(ts.get_num_states(), false);
        res_a.set(0, true);
        let formula_e = FormulaTreeNode::new(
            None, None, Some("e".to_string()), FormulaTreeNodeType::Atomic
        );
        let mut res_e = BitVec::from_elem(ts.get_num_states(), false);
        res_e.set(0, true);
        let formula_b = FormulaTreeNode::new(
            None, None, Some("b".to_string()), FormulaTreeNodeType::Atomic
        );
        let mut res_b = BitVec::from_elem(ts.get_num_states(), false);
        res_b.set(1, true);
        
        assert_eq!(compute_sat_set_atomic(&ts, formula_a), res_a);
        assert_eq!(compute_sat_set_atomic(&ts, formula_e), res_e);
        assert_eq!(compute_sat_set_atomic(&ts, formula_b), res_b);
    }
    
    #[test]
    fn test_not() {
        let mut cache: HashMap<String, BitVec> = HashMap::new();
        let ts = build_test_ts();
        let formula_a = FormulaTreeNode::new(
            None, None, Some("a".to_string()), FormulaTreeNodeType::Atomic
        );
        let not = FormulaTreeNode::new(
            Some(Box::from(formula_a)), None, None, FormulaTreeNodeType::Not
        );
        let mut res_a = BitVec::from_elem(ts.get_num_states(), true);
        res_a.set(0, false);
        
        assert_eq!(compute_sat_set_not(&ts, not, &mut cache), res_a);
    }

    #[test]
    fn test_and() {
        let mut cache: HashMap<String, BitVec> = HashMap::new();
        let ts = build_test_ts();
        let formula_a = FormulaTreeNode::new(
            None, None, Some("a".to_string()), FormulaTreeNodeType::Atomic
        );
        let formula_e = FormulaTreeNode::new(
            None, None, Some("e".to_string()), FormulaTreeNodeType::Atomic
        );
        let formula_b = FormulaTreeNode::new(
            None, None, Some("b".to_string()), FormulaTreeNodeType::Atomic
        );
        let a_and_e = FormulaTreeNode::new(
            Some(Box::from(formula_a.clone())), Some(Box::from(formula_e.clone())), None, FormulaTreeNodeType::And
        );
        let b_and_e = FormulaTreeNode::new(
            Some(Box::from(formula_b.clone())), Some(Box::from(formula_e.clone())), None, FormulaTreeNodeType::And
        );
        let a_and_b = FormulaTreeNode::new(
            Some(Box::from(formula_a.clone())), Some(Box::from(formula_b.clone())), None, FormulaTreeNodeType::And
        );
        let mut res_a_and_e = BitVec::from_elem(ts.get_num_states(), false);
        res_a_and_e.set(0, true);
        let mut res_b_and_e = BitVec::from_elem(ts.get_num_states(), false);
        let mut res_a_and_b = BitVec::from_elem(ts.get_num_states(), false);

        assert_eq!(compute_sat_set_and(&ts, a_and_e, &mut cache), res_a_and_e);
        assert_eq!(compute_sat_set_and(&ts, b_and_e, &mut cache), res_b_and_e);
        assert_eq!(compute_sat_set_and(&ts, a_and_b, &mut cache), res_a_and_b);
    }

    #[test]
    fn test_exists_until() {
        let mut cache: HashMap<String, BitVec> = HashMap::new();
        let ts = build_test_ts();
        let formula_a = FormulaTreeNode::new(
            None, None, Some("a".to_string()), FormulaTreeNodeType::Atomic
        );
        let formula_b = FormulaTreeNode::new(
            None, None, Some("b".to_string()), FormulaTreeNodeType::Atomic
        );
        let until = FormulaTreeNode::new(
            Some(Box::from(formula_a)), Some(Box::from(formula_b)), None, FormulaTreeNodeType::Until
        );
        let mut res = BitVec::from_elem(ts.get_num_states(), false);
        res.set(0, true);
        res.set(1, true);
        
        assert_eq!(compute_sat_set_of_exists_until(&ts, until, &mut cache), res);
    }

    #[test]
    fn test_exists_globally() {
        let mut cache: HashMap<String, BitVec> = HashMap::new();
        let ts = build_test_ts();
        let formula_a = FormulaTreeNode::new(
            None, None, Some("a".to_string()), FormulaTreeNodeType::Atomic
        );
        let formula_c = FormulaTreeNode::new(
            None, None, Some("c".to_string()), FormulaTreeNodeType::Atomic
        );
        let globally_a = FormulaTreeNode::new(
            Some(Box::from(formula_a)), None, None, FormulaTreeNodeType::Globally
        );
        let globally_c = FormulaTreeNode::new(
            Some(Box::from(formula_c)), None, None, FormulaTreeNodeType::Globally
        );
        let res = BitVec::from_elem(ts.get_num_states(), false);

        assert_eq!(compute_sat_set_of_exists_globally(&ts, globally_a, &mut cache), res);
        assert_eq!(compute_sat_set_of_exists_globally(&ts, globally_c, &mut cache), res);
    }
    
    #[test]
    fn test_exists_next() {
        let mut cache: HashMap<String, BitVec> = HashMap::new();
        let ts = build_test_ts();
        let formula_a = FormulaTreeNode::new(
            None, None, Some("a".to_string()), FormulaTreeNodeType::Atomic
        );
        let formula_b = FormulaTreeNode::new(
            None, None, Some("b".to_string()), FormulaTreeNodeType::Atomic
        );
        let next_a = FormulaTreeNode::new(
            Some(Box::from(formula_a)), None, None, FormulaTreeNodeType::Next
        );
        let next_b = FormulaTreeNode::new(
            Some(Box::from(formula_b)), None, None, FormulaTreeNodeType::Next
        );
        let mut res_a = BitVec::from_elem(ts.get_num_states(), false);
        res_a.set(3, true);
        let mut res_b = BitVec::from_elem(ts.get_num_states(), false);
        res_b.set(0, true);

        assert_eq!(compute_sat_set_of_exists_next(&ts, next_a, &mut cache), res_a);
        assert_eq!(compute_sat_set_of_exists_next(&ts, next_b, &mut cache), res_b);
    }
}

