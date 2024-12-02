use crate::common::transition_system::TransitionSystem;
use std::collections::{HashMap, HashSet, VecDeque};
use crate::checker::helper::bit_vec_to_ap_strings;
use crate::parser::property::{Property, PropertyType};

/// Searches for SCCs in the given transition system and checks whether it contains an SCC which
/// contains an accepting state. Once such an SCC is found, and it is reachable within the product
/// transition system, we know that the property is violated by the original transition system.
///
/// # Parameters
///
/// - `product_ts`: The given product transition system which gets checked.
///
/// # Returns
/// A Result with `Ok` if the property is fulfilled and Err with a path and a trace otherwise.
pub fn find_scc_in_ts(product_ts: &TransitionSystem)
                                -> Result<bool, (Vec<Vec<String>>, Vec<usize>)> {
    // wrapper struct used to find and store SCCs in the given transition system
    let mut scc = SCC::new();
    scc.find_sccs(product_ts);
    scc.print_sccs();

    for cluster in scc.sccs {
        for state in cluster {
            // if label is not empty, we encountered a -f state
            if !product_ts.get_state_label(state).none() {
                // we have a state which satisfies -f in a cluster
                // check if state is reachable from start
                if let Ok(came_from) = is_reachable(product_ts, product_ts.get_initial_states(), state) {
                    // if its reachable, we found an SCC containing a bad state
                    // => give counterexample
                    return Err(reconstruct_path(
                        product_ts,
                        &came_from,
                        state
                    ));
                }
            }
        }
    }
    Ok(true)
}

pub fn persistence_checking_with_scc(transition_system: &TransitionSystem, property: &Property<String>)
    -> Result<bool, (Vec<Vec<String>>, Vec<usize>)> {
    let automaton;

    match property.property_type.clone(){
        PropertyType::Invariant(_) => {panic!("wrong property type")},
        PropertyType::Persistence(prop) => {automaton = prop}
        PropertyType::RegularSafety(_) => {panic!("wrong property type")}
        PropertyType::OmegaRegular(_) => {panic!("wrong property type")}
    }
    let product_ts = transition_system.product_with(automaton);

    find_scc_in_ts(&product_ts)
}

fn is_reachable(transition_system: &TransitionSystem,
                    starts: &Vec<usize>,
                    target: usize
) -> Result<HashMap<usize, usize>, bool> {
    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();
    let mut came_from: HashMap<usize, usize> = HashMap::new(); // save predecessor

    for &start in starts {
        queue.push_back(start);
        visited.insert(start);
    }

    while let Some(current) = queue.pop_front() {
        if current == target {
            return Ok(came_from);
        }

        if let neighbors = transition_system.get_successor_states(current).to_vec() {
            for neighbor in neighbors {
                if !visited.contains(&neighbor) {
                    visited.insert(neighbor);
                    queue.push_back(neighbor);
                    came_from.insert(neighbor, current); // save predecessor
                }
            }
        }
    }

    Err(false)
}

struct SCC {
    max_dfs: usize,
    dfs_num: HashMap<usize, usize>,
    low_link: HashMap<usize, usize>,
    visited: HashSet<usize>,
    stack: Vec<usize>,
    sccs: Vec<Vec<usize>>
}
impl SCC {
    fn new() -> Self {
        SCC {
            max_dfs: 0,
            dfs_num: HashMap::new(),
            low_link: HashMap::new(),
            visited: HashSet::new(),
            stack: Vec::new(),
            sccs: Vec::new(),
        }
    }
    fn tarjan(&mut self, v: usize, transition_system: &TransitionSystem) {
        self.dfs_num.insert(v, self.max_dfs);
        self.low_link.insert(v, self.max_dfs);
        self.max_dfs += 1;
        self.stack.push(v);
        self.visited.insert(v); // this could be renamed to 'on_stack' for clarity

        let neighbors = transition_system.get_successor_states(v).to_vec();
        for &v_prime in &neighbors {
            if !self.dfs_num.contains_key(&v_prime) {
                // node not visited yet
                self.tarjan(v_prime, transition_system);
                let new_low = std::cmp::min(
                    *self.low_link.get(&v).unwrap(),
                    *self.low_link.get(&v_prime).unwrap()
                );
                self.low_link.insert(v, new_low);
            } else if self.visited.contains(&v_prime) { // check if v_prime is on stack
                // node already visited and is on stack
                let new_low = std::cmp::min(
                    *self.low_link.get(&v).unwrap(),
                    self.dfs_num[&v_prime],
                );
                self.low_link.insert(v, new_low);
            }
        }

        // if v is a root node, pop the stack and generate an SCC
        if self.dfs_num[&v] == self.low_link[&v] {
            let mut scc = Vec::new();
            loop {
                let v_prime = self.stack.pop().unwrap();
                self.visited.remove(&v_prime); // Remove from stack tracking
                scc.push(v_prime);
                if v_prime == v {
                    break;
                }
            }
            // check if scc is a trivial cluster (no self transition and size 1)
            if scc.len() == 1 && transition_system.get_successor_states(scc[0]).contains(&scc[0]) || scc.len() > 1 {
                self.sccs.push(scc);
            }
        }
    }

    fn find_sccs(&mut self, transition_system: &TransitionSystem ) {
        for node in transition_system.get_states() {
            if !self.dfs_num.contains_key(&node) {
                self.tarjan(node, transition_system);
            }
        }
    }
    fn print_sccs(&self) {
        for scc in &self.sccs {
            println!("SCC: {:?}", scc);
        }
    }
}

/// Construct a counterexample in the case that the property was violated by the given transition
/// system.
///
/// # Parameters
/// - `transition_system`: The transition system that violated the property.
/// - `came_from`: A HashMap used to follow the path that caused the violation.
/// - `end_state`: Last state of the counterexample, which finally violates the property.
///
/// # Returns
/// A pair consisting of the path and the trace of the counterexample.
fn reconstruct_path(
    ts: &TransitionSystem,
    came_from: &HashMap<usize, usize>,
    end_state: usize) -> (Vec<Vec<String>>, Vec<usize>) {
    let mut path = Vec::new();
    let mut states = Vec::new();
    let mut current = end_state;

    // push label of last state
    path.push(bit_vec_to_ap_strings(ts, ts.get_state_label(current)));
    states.push(current);

    // reconstruct path backwards
    while let Some(&prev) = came_from.get(&current) {
        path.push(bit_vec_to_ap_strings(ts, ts.get_state_label(prev)));
        states.push(prev);
        current = prev;
    }

    // reverse path, as we have built it up from behind
    path.reverse();
    states.reverse();

    (path, states)
}
