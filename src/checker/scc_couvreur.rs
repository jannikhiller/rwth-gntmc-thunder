use std::collections::{HashMap, HashSet, VecDeque};
use log::trace;
use crate::checker::helper::bit_vec_to_ap_strings;
use crate::common::transition_system::TransitionSystem;
use crate::property::Property;

pub fn persistence_checking_with_couvreur_scc(
    transition_system: &TransitionSystem,
    property: &Property<String>,
    state_info_map: Option<&HashMap<usize, (usize, Vec<String>)>>,
) -> Result<bool, (Vec<Vec<String>>, Vec<usize>)> {

    let mut count = 0;
    let mut roots: VecDeque<usize> = VecDeque::new();
    let mut dfsnum: HashMap<usize, usize> = HashMap::new();
    let mut current: HashSet<usize> = HashSet::new();

    let mut found_cycle;
    for s0 in transition_system.get_initial_states() {
        trace!("Considering initial state {:?}", s0);
        found_cycle = couv_dfs(*s0, &mut count, &mut dfsnum, &mut roots, &mut current, transition_system, property);

        if found_cycle {
            return Err((vec![], vec![]));
        }
    }

    Ok(true)
}

fn couv_dfs(s: usize, count: &mut usize, dfsnum: &mut HashMap<usize, usize>,
            roots: &mut VecDeque<usize>, current: &mut HashSet<usize>,
            transition_system: &TransitionSystem, property: &Property<String>) -> bool {
    *count += 1;
    dfsnum.insert(s, *count);
    roots.push_back(s);
    current.insert(s);

    println!("Size of roots: {}", roots.len());

    for t in transition_system.get_successor_states(s) {
        if is_new_successor(t, dfsnum) {
            couv_dfs(*t, count, dfsnum, roots, current, transition_system, property);
        } else if current.contains(t) {
            let mut u;
            loop {
                u = roots.pop_back().unwrap();

                if !check_property_on_state(u, transition_system, property) {
                    println!("Found violation of property on state: {}", u);
                    return true
                }

                if dfsnum.get(&u).unwrap() > dfsnum.get(t).unwrap() {
                    println!("Breaking loop as dfsnum of state {} is larger than dfsnum of state {}", u, t);
                    break;
                }
            }
            roots.push_back(u);
        }
    }

    if *roots.back().unwrap() == s {
        roots.pop_back();
        remove(s, current, transition_system);
    }

    false
}

fn is_new_successor(t: &usize, dfsnum: &mut HashMap<usize, usize>) -> bool {
    if !dfsnum.contains_key(t) {
        dfsnum.insert(*t, 0);
        return true
    }
    false
}

fn remove(s: usize, current: &mut HashSet<usize>, transition_system: &TransitionSystem) {
    if !current.contains(&s) {
        return;
    }
    current.remove(&s);
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