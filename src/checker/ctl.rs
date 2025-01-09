use std::collections::HashMap;
use bit_vec::BitVec;
use crate::common::transition_system::TransitionSystem;
use crate::property::property::{FormulaTreeNode, Property, PropertyType, FormulaTreeNodeType};

pub fn ctl_checking(
    transition_system: &TransitionSystem,
    property: &Property<String>,
) -> Result<bool, (Vec<Vec<String>>, Vec<usize>)> {
    match &property.property_type {
        PropertyType::Ctl(formula) => {
            // check if all initial states are in the sat set of the given formula
            let sat_set = compute_sat_set(transition_system, formula.clone());
            for init_state in transition_system.get_initial_states() {
                if !sat_set.get(*init_state) {
                    // found initial state that is not part of the satisfaction set => violation
                    return Err((vec![], vec![]))
                }
            }
            Ok(true)
        },
        _ => {
            panic!("Computing the satisfaction set is only possible for CTL formulae.");
        },
    }
}

fn compute_sat_set(transition_system: &TransitionSystem, formula: &FormulaTreeNode<String>) -> BitVec {
    let mut cache: HashMap<String, BitVec> = HashMap::new();

    if cache.contains_key(&formula.to_string()) {
        return cache.get(&formula.to_string()).unwrap().clone();
    }

    let res = match formula.node_type {
        FormulaTreeNodeType::True => todo!(),
        FormulaTreeNodeType::Atomic => todo!(),
        FormulaTreeNodeType::Not => todo!(),
        FormulaTreeNodeType::And => todo!(),
        FormulaTreeNodeType::Exists => {
            match formula.clone().left.expect("Left child of exists nodes must be set") {
                Some(FormulaTreeNodeType::Next) => todo!(),
                Some(FormulaTreeNodeType::Until) => compute_sat_set_of_exists_until(transition_system, formula),
                Some(FormulaTreeNodeType::Globally) => compute_sat_set_of_exists_globally(transition_system, formula),
                _ => panic!("Invalid property: Exists may not be followed by something other than NEXT, UNTIL or GLOBALLY.")
            }
        }
        _ => panic!("Tried to check a CTL property that is not in ENF")
    };

    cache.insert(formula.to_string(), res.clone());
    res
}

fn compute_sat_set_of_exists_until(transition_system: &TransitionSystem, formula: FormulaTreeNode<String>) -> BitVec {
    let left = formula.left.unwrap();
    let right = formula.right.unwrap();

    let mut set_t = compute_sat_set(transition_system, &*right);
    let mut set_e = set_t.clone();
    let sat_left = compute_sat_set(transition_system, &*left);

    while !set_e.is_empty() {
        let mut s_prime = 0;
        for (state_index, b) in set_e.iter().enumerate() {
            if b {
                s_prime = state_index;
                set_e.insert(state_index, false);
                break;
            }
        }

        for state in transition_system.get_predecessor_states(s_prime) {
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

fn compute_sat_set_of_exists_globally(transition_system: &TransitionSystem, formula: &FormulaTreeNode<String>) -> BitVec {
    let set_t = compute_sat_set(transition_system, formula);
    let mut set_e = set_t.clone();
    set_e.negate();

    let mut c = HashMap::new();

    for (curr_state, b) in set_e.iter().enumerate() {
        if b {
            // count and store number of successor of current state
            c.insert(curr_state, transition_system.get_successor_states(curr_state).len());
        }
    }

    while set_e.any() {
        
    }

    set_e
}
