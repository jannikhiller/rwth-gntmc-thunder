use crate::common::transition_system::TransitionSystem;
use crate::parser::property::Property;
use bit_vec::BitVec;
use std::collections::{HashSet, VecDeque};

/// Returns a boolean over the given Transition System and property.
///
/// # Parameters
/// - `property`: The Invariant which gets checked.
///
/// # Returns
/// A boolean over the given Transition System and property.
pub fn bfs_invariant_checking(
    transition_system: &TransitionSystem,
    property: &Property<String>,
) -> bool {
    let mut visited = HashSet::new(); // visited states
    let mut queue = VecDeque::new(); // states we are going to visit
    let mut visited_labels: HashSet<BitVec> = HashSet::new(); // only accepted labels

    // add all initial states
    for &initial_state in transition_system.get_initial_states() {
        queue.push_back(initial_state);
        visited.insert(initial_state);
    }

    while let Some(current_state) = queue.pop_front() {
        let current_bit_label = transition_system.get_state_label(current_state);
        let string_labels_of_current = bit_vec_to_ap_strings(&transition_system, current_bit_label);

        // check if the current label has been already checked
        let labels_been_visited = visited_labels
            .iter()
            .any(|visited_label| (current_bit_label == visited_label));
        // else check if the current label is correct
        if !labels_been_visited {
            if !property.evaluate(&string_labels_of_current) {
                return false; //if property doesn't hold, return false
            }
            visited_labels.insert(current_bit_label.clone());
        }

        // get next states and add them to queue
        for next_state in transition_system.get_successor_states(current_state) {
            if !visited.contains(&next_state) {
                visited.insert(next_state);
                queue.push_back(next_state);
            }
        }
    }

    true
}

/// Returns a string vec for the given bit vec.
///
/// # Parameters
/// - `label`: The BitVec which gets translated into string vec.
///
/// # Returns
/// A Vec<String> for the given AP-BitVec.
pub fn bit_vec_to_ap_strings(transition_system: &TransitionSystem, label: &BitVec) -> Vec<String> {
    // get all ap names
    let ap_names = transition_system.get_ap();

    label
        .iter()
        .enumerate() // add index to bit
        .filter(|(_, bit)| *bit) // only true bits
        .map(|(index, _)| ap_names[index].clone()) // get according AP-String
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::checker::invariant::bfs_invariant_checking;
    use crate::common::sparse_matrix::SparseMatrix;
    use crate::common::transition_system::TransitionSystem;
    use crate::parser::property::{FormulaTreeNode, FormulaTreeNodeType, Property, PropertyType};
    use bit_vec::BitVec;
    use std::collections::HashMap;

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

    #[test]
    fn test_invariant_bfs_true() {
        //get the ts system
        let ts = create_test_transition_system();

        //now we build our property
        //we want to build:  a or b or c
        let atomic_a = FormulaTreeNode::new(
            None,
            None,
            Some("a".to_string()),
            FormulaTreeNodeType::ATOMIC,
        );
        let atomic_b = FormulaTreeNode::new(
            None,
            None,
            Some("b".to_string()),
            FormulaTreeNodeType::ATOMIC,
        );
        let atomic_c = FormulaTreeNode::new(
            None,
            None,
            Some("c".to_string()),
            FormulaTreeNodeType::ATOMIC,
        );
        let or = FormulaTreeNode::new(
            Some(Box::new(atomic_b)),
            Some(Box::new(atomic_c)),
            None,
            FormulaTreeNodeType::OR,
        );
        let root = FormulaTreeNode::new(
            Some(Box::new(atomic_a)),
            Some(Box::new(or)),
            None,
            FormulaTreeNodeType::OR,
        );
        let property = Property::new("ExampleTree".to_string(), PropertyType::Invariant, root);
        assert!(bfs_invariant_checking(&ts, &property));
    }
    #[test]
    fn test_invariant_bfs_false() {
        //get the ts system
        let ts = create_test_transition_system();

        //now we build our property
        //we want to build:  a
        let root = FormulaTreeNode::new(
            None,
            None,
            Some("a".to_string()),
            FormulaTreeNodeType::ATOMIC,
        );
        let property = Property::new("ExampleTree".to_string(), PropertyType::Invariant, root);
        assert!(!bfs_invariant_checking(&ts, &property));
    }
}
