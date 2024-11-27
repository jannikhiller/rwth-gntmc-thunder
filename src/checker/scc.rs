use crate::common::transition_system::TransitionSystem;

use std::collections::{HashMap, HashSet, VecDeque};
use bit_vec::BitVec;
use crate::common::sparse_matrix::SparseMatrix;
use crate::parser::property::{Property};

pub fn persistence_checking_scc(transition_system: &TransitionSystem, property: Property<String>)-> bool{
    //toDo: build the product with property before finding scc
    let mut scc = SCC::new();
    scc.find_scc(transition_system);
    scc.print_sccs();
    for cluster in scc.sccs{
        for state in cluster{
            //if labels not empty, we have -f state
            if !transition_system.get_state_label(state).none(){
                //we have a state which hold -f in a cluster
                //check if state is reachable from start
                if is_reachable(transition_system, transition_system.get_initial_states(), state){
                    //if its reachable, it isnt reachable
                    return false;
                }
            }
        }
    }
    true
}
pub fn is_reachable(transition_system: &TransitionSystem,
                    starts: &Vec<usize>,
                    target: usize
) -> bool {
    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();
    for &start in starts
    {
        queue.push_back(start);
        visited.insert(start);
    }

    while let Some(current) = queue.pop_front() {
        if current == target {
            return true;
        }

        if let neighbors = transition_system.get_successor_states(current).to_vec() {
            for neighbor in neighbors {
                if !visited.contains(&neighbor) {
                    visited.insert(neighbor);
                    queue.push_back(neighbor);
                }
            }
        }
    }

    false
}
struct SCC {

    max_dfs: usize,
    dfs_num: HashMap<usize, usize>,
    low_link: HashMap<usize, usize>,
    visited: HashSet<usize>,
    stack: Vec<usize>,
    sccs: Vec<Vec<usize>>,
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
        self.visited.insert(v);  // This could be renamed to 'on_stack' for clarity

        let neighbors = transition_system.get_successor_states(v).to_vec();
        for &v_prime in &neighbors {
            if !self.dfs_num.contains_key(&v_prime) {
                // Node not visited yet
                self.tarjan(v_prime, transition_system);
                let new_low = std::cmp::min(
                    *self.low_link.get(&v).unwrap(),
                    *self.low_link.get(&v_prime).unwrap()
                );
                self.low_link.insert(v, new_low);
            } else if self.visited.contains(&v_prime) {  // Check if v_prime is on stack
                // Node already visited and is on stack
                let new_low = std::cmp::min(
                    *self.low_link.get(&v).unwrap(),
                    self.dfs_num[&v_prime],
                );
                self.low_link.insert(v, new_low);
            }
        }

        // If v is a root node, pop the stack and generate an SCC
        if self.dfs_num[&v] == self.low_link[&v] {
            let mut scc = Vec::new();
            loop {
                let v_prime = self.stack.pop().unwrap();
                self.visited.remove(&v_prime);  // Remove from stack tracking
                scc.push(v_prime);
                if v_prime == v {
                    break;
                }
            }
            self.sccs.push(scc);
        }
    }


    fn find_scc(&mut self,transition_system: &TransitionSystem ){
        for node in transition_system.get_states()
        {
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

#[test]
fn test_scc(){
    let ts = create_test_transition_system();
    persistence_checking_scc(&ts,)

}

fn create_test_transition_system() -> TransitionSystem {
    let transitions = vec![
        vec![false, true, false], // State 0 -> State 1
        vec![false, false, true], // State 1 -> State 2
        vec![true, false, false], // State 2 -> State 0
    ];
    let transition_matrix = SparseMatrix::from_2d_vec(&transitions);
    let reverse_transitions = vec![
        vec![false, false, true], // State 0 <- State 2
        vec![true, false, false], // State 1 <- State 0
        vec![false, true, false], // State 2 <- State 1
    ];
    let reverse_transition_matrix = SparseMatrix::from_2d_vec(&reverse_transitions);
    let mut state_labels = Vec::new();
    let ap = vec!["a".to_string(), "b".to_string(), "c".to_string()];
    let mut label0 = BitVec::from_elem(3, false);
    label0.set(0, true);
    state_labels.push(label0.clone());
    let mut label1 = BitVec::from_elem(3, false);
    label1.set(1, true);
    state_labels.push(label1.clone());
    let mut label2 = BitVec::from_elem(3, false);
    label2.set(0, true);
    label2.set(2, true);
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