use crate::common::transition_system::TransitionSystem;
use std::collections::{HashMap, HashSet, VecDeque};
use crate::checker::helper::bit_vec_to_ap_strings;
use crate::parser::property::{Property};

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
pub fn find_scc_in_ts(transition_system: &TransitionSystem, property: &Property<String>)
                      -> Result<bool, (Vec<Vec<String>>, Vec<usize>)> {
    // wrapper struct used to find and store SCCs in the given transition system
    let mut scc = SCC::new();
    scc.find_sccs(transition_system);
    scc.print_sccs();

    for cluster in scc.sccs {
        for state in cluster {
            // if label is not empty, we encountered a -f state
            if !check_property_on_state(state, transition_system, property) {
                // we have a state which satisfies -f in a cluster
                // check if state is reachable from start
                if let Ok(came_from) = is_reachable(transition_system, transition_system.get_initial_states(), state) {
                    // if its reachable, we found an SCC containing a bad state
                    // => give counterexample
                    return Err(reconstruct_path(
                        transition_system,
                        &came_from,
                        state
                    ));
                }
            }
        }
    }
    Ok(true)
}

fn check_property_on_state(state: usize, transition_system: &TransitionSystem, property: &Property<String>) -> bool {
    let bit_label = transition_system.get_state_label(state);
    let string_labels_of_current = bit_vec_to_ap_strings(transition_system, bit_label);

    property.evaluate(&string_labels_of_current)
}

pub fn persistence_checking_with_scc(transition_system: &TransitionSystem, property: &Property<String>)
    -> Result<bool, (Vec<Vec<String>>, Vec<usize>)> {
    find_scc_in_ts(transition_system, property)
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

        let neighbors = transition_system.get_successor_states(current).to_vec();
        for neighbor in neighbors {
            if !visited.contains(&neighbor) {
                visited.insert(neighbor);
                queue.push_back(neighbor);
                came_from.insert(neighbor, current); // save predecessor
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

#[cfg(test)]
mod tests {
    use crate::common::sparse_matrix::SparseMatrix;
    use crate::common::transition_system::TransitionSystem;
    use crate::parser::property::{FormulaTreeNode, FormulaTreeNodeType, Property, PropertyType};
    use bit_vec::BitVec;
    use std::collections::HashMap;
    use crate::checker::scc::persistence_checking_with_scc;

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

        let property = Property::new("PersistenceProperty".to_string(), PropertyType::Persistence(root));

        assert!(persistence_checking_with_scc(&transition_system, &property).is_ok());
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

        let property = Property::new("PersistenceProperty".to_string(), PropertyType::Persistence(root));

        let result = persistence_checking_with_scc(&transition_system, &property);

        match &result {
            Ok(success) => {
                panic!("Property should fail!")
            }
            Err((counterexample, trace_indexes)) => {
                println!("The property does not hold.");
                println!("Counterexample: {:?}", counterexample);
                println!("Trace indexes: {:?}", trace_indexes);

                // Optionally include assertions to validate the counterexample.
                assert!(!counterexample.is_empty(), "Expected non-empty counterexample.");
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
            ap
        )
    }

    fn create_test_transition_system_2() -> TransitionSystem {
        let transitions = vec![
            vec![false, true, true], // State 0 -> State 1, State 0 -> State 2
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
            ap
        )
    }
}