use crate::common::transition_system::TransitionSystem;
use crate::checker::helper::reconstruct_path;
use std::collections::{HashMap, HashSet, VecDeque};
use bit_vec::BitVec;
use crate::common::sparse_matrix::SparseMatrix;
use crate::parser::property::{Property, PropertyType, FiniteAutomaton, FormulaTreeNode, FormulaTreeNodeType};
use crate::parser::property::AcceptanceType::Nfa;

pub fn persistence_checking_scc(transition_system: &TransitionSystem, property: &Property<String>)
                                -> Result<bool, (Vec<Vec<String>>, Vec<usize>)>{
    //toDo: build the product with property before finding scc
    let mut automaton;
    match property.property_type.clone() {
        PropertyType::Invariant(_) => {panic!("Wrong Datatype")}
        PropertyType::Persistence(_) => {panic!("Wrong Datatype")}
        PropertyType::RegularSafety(_) => {panic!("Wrong Datatype")}
        PropertyType::OmegaRegular(finiteAutomata) => {automaton = finiteAutomata.clone()}
    }
    let mut product_ts = &transition_system.product_with(automaton);
    let mut scc = SCC::new();
    scc.find_scc(product_ts);
    scc.print_sccs();
    for cluster in scc.sccs{
        for state in cluster{
            //if labels not empty, we have -f state
            if !product_ts.get_state_label(state).none(){
                //we have a state which hold -f in a cluster
                //check if state is reachable from start
                if let Ok(came_from) = is_reachable(product_ts, product_ts.get_initial_states(), state){
                    //if its reachable, it isnt reachable
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
pub fn is_reachable(transition_system: &TransitionSystem,
                    starts: &Vec<usize>,
                    target: usize
) -> Result<HashMap<usize, usize>, bool> {
    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();
    let mut came_from: HashMap<usize, usize> = HashMap::new(); // save predecessor
    for &start in starts
    {
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
                    came_from.insert(neighbor, current); //save predecessor
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::sparse_matrix::SparseMatrix;
    #[test]
    fn test_scc(){
        let ts = create_test_transition_system_for_product();
        let automaton = create_test_automaton_for_product();
        let omega_prop = Property::new("Test".to_string(), PropertyType::OmegaRegular(automaton));
        match persistence_checking_scc(&ts, &omega_prop) {
            Ok(result) => println!("Die Invariantenprüfung war erfolgreich: {}", result),
            Err((error_details, indices)) => {
                println!("Hält nicht");
                println!("Details zum Fehler: {:?}", error_details);
                println!("Indizes der Probleme: {:?}", indices);
            }}
        assert!(true);
    }

    fn create_test_transition_system_for_product() -> TransitionSystem {
        let transitions = vec![
            (0, 1, true),
            (0, 2, true),
            (2, 1, true),
            (1, 3, true),
            (3, 2, true),
            (3, 3, true),
        ];
        let transition_matrix = SparseMatrix::from_list_of_entries(4, 4, &transitions);
        let reverse_transitions = vec![
            (1, 0, true),
            (2, 0, true),
            (1, 2, true),
            (3, 1, true),
            (2, 3, true),
            (3, 3, true),
        ];
        let reverse_transition_matrix = SparseMatrix::from_list_of_entries(4, 4, &transitions);
        let mut state_labels = Vec::new();
        let ap = vec!["a".to_string(), "b".to_string()];
        let mut label0 = BitVec::from_elem(2, false);
        label0.set(0, true);
        label0.set(1, true);
        state_labels.push(label0.clone());
        let label1 = BitVec::from_elem(2, false);
        state_labels.push(label1.clone());
        let mut label2 = BitVec::from_elem(2, false);
        label2.set(0, true);
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
}
fn create_test_automaton_for_product() -> FiniteAutomaton<String> {
    let a_node = FormulaTreeNode::new(
        None,
        None,
        Some("a".to_string()),
        FormulaTreeNodeType::Atomic
    );
    let not_a_node = FormulaTreeNode::new(
        Some(Box::new(a_node.clone())),
        None,
        None,
        FormulaTreeNodeType::Not
    );
    let b_node = FormulaTreeNode::new(
        None,
        None,
        Some("b".to_string()),
        FormulaTreeNodeType::Atomic
    );
    let not_b_node = FormulaTreeNode::new(
        Some(Box::new(b_node.clone())),
        None,
        None,
        FormulaTreeNodeType::Not
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
