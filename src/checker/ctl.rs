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
    match &property.property_type {
        PropertyType::Ctl(formula) => {
            debug!("Checking CTL-formula: \n{}", formula);
            // check if all initial states are in the sat set of the given formula
            let sat_set = compute_sat_set(transition_system, &formula.clone());
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
) -> BitVec {
    trace!("Computing satisfaction set...");
    let mut cache: HashMap<String, BitVec> = HashMap::new();

    if cache.contains_key(&formula.to_string()) {
        trace!("Found satisfaction set in cache.");
        return cache.get(&formula.to_string()).unwrap().clone();
    }

    let res = match formula.node_type {
        FormulaTreeNodeType::True => compute_sat_set_true(transition_system),
        FormulaTreeNodeType::Atomic => compute_sat_set_atomic(transition_system, formula.clone()),
        FormulaTreeNodeType::Not => compute_sat_set_not(transition_system, formula.clone()),
        FormulaTreeNodeType::And => compute_sat_set_and(transition_system, formula.clone()),
        FormulaTreeNodeType::Exists => {
            let left_node = formula
                .clone()
                .left
                .expect("Left child of exists nodes must be set.");
            match left_node.node_type {
                FormulaTreeNodeType::Next => compute_sat_set_of_exists_next(transition_system, *formula.left.clone().unwrap()),
                FormulaTreeNodeType::Until => compute_sat_set_of_exists_until(transition_system, *formula.left.clone().unwrap()),
                FormulaTreeNodeType::Globally => compute_sat_set_of_exists_globally(transition_system, *formula.left.clone().unwrap()),
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
    let label_index = transition_system.get_ap().iter().position(|x| *x == formula.label.clone().unwrap());

    let mut states_with_label = Vec::new();
    (0 .. 2_usize.pow(transition_system.get_ap().len() as u32)).for_each(|label_subset| {
        let mut label = BitVec::from_bytes(&label_subset.shl(usize::BITS - transition_system.get_ap().len() as u32).to_be_bytes());
        label.truncate(transition_system.get_ap().len());

        if label.get(label_index.unwrap()).unwrap() { // This might be optimized later using an
        // elegant bit shift or something similar to make the iteration start at the appropriate bit
            for state in transition_system.get_states_with_label(&label) {
                states_with_label.push(*state);
            };
        }
    });

    let res = BitVec::from_fn(transition_system.get_num_states(), |index| {
        states_with_label.contains(&index)
    });
    trace!("Finished satisfaction sets for ATOMIC");

    res
}

fn compute_sat_set_not(
    transition_system: &TransitionSystem,
    formula: FormulaTreeNode<String>,
) -> BitVec {
    trace!("Computing satisfaction sets for NOT...");
    let child = formula.left.unwrap();
    let mut set = compute_sat_set(transition_system, &*child);
    set.negate();
    trace!("Finished satisfaction sets for NOT");
    set
}

fn compute_sat_set_and(
    transition_system: &TransitionSystem,
    formula: FormulaTreeNode<String>,
) -> BitVec {
    trace!("Computing satisfaction sets for AND...");
    let left = formula.left.unwrap();
    let right = formula.right.unwrap();

    trace!("Computing left satisfaction set...");
    let mut set_left = compute_sat_set(transition_system, &*left);
    trace!("Finished left satisfaction sets.\nStarting righ...");
    let set_right = compute_sat_set(transition_system, &*right);
    trace!("Finished right satisfaction set.");

    set_left.and(&set_right);
    trace!("Finished satisfaction sets for AND");
    set_left
}

fn compute_sat_set_of_exists_until(
    transition_system: &TransitionSystem,
    formula: FormulaTreeNode<String>,
) -> BitVec {
    trace!("Computing satisfaction sets for EXISTS UNTIL...");
    let left = formula.left.unwrap();
    let right = formula.right.unwrap();

    trace!("Computing satisfaction set of right subformula.");
    let mut set_t = compute_sat_set(transition_system, &*right);
    trace!("Finished satisfaction set of right subformula.");
    let mut set_e = set_t.clone();
    trace!("Computing satisfaction set of left subformula.");
    let sat_left = compute_sat_set(transition_system, &*left);
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
) -> BitVec {
    trace!("Computing satisfaction sets for EXISTS GLOBALLY...");
    let mut set_t = compute_sat_set(transition_system, &formula.left.unwrap());
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
) -> BitVec {
    trace!("Computing satisfaction sets for EXISTS NEXT...");
    let sat_set = compute_sat_set(transition_system, &formula.left.unwrap());
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
