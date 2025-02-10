// The quotienting is our interface to be called, needs an Option struct to determine whether the
// simple or advanced refinement should be used.
use crate::bisimulation::advanced_refinement::advanced_refinement;
use crate::bisimulation::partition::{get_successors, Partition};
use crate::bisimulation::simple_refinement::simple_selection_strategy;
use crate::checker::checker::{Options, QuotientingAlgorithm};
use crate::common::sparse_matrix::SparseMatrix;
use crate::common::transition_system::TransitionSystem;
use bit_vec::BitVec;
use std::collections::HashMap;

pub fn quotienting(
    transition_system: &TransitionSystem,
    options: &Options,
    ap: Option<&Vec<String>>,
) -> TransitionSystem {
    let eq_classes: Partition<usize>;
    match options.quotienting_algorithm {
        QuotientingAlgorithm::AdvancedRefinement => {
            eq_classes = advanced_refinement(transition_system, ap);
        }
        QuotientingAlgorithm::SimpleRefinement => {
            eq_classes = simple_selection_strategy(transition_system, ap);
        }
        QuotientingAlgorithm::Without => {
            panic!("We cannot be here, if flag was set to `without`");
        }
    }
    //this is new state space
    //get new transitions for every block
    let mut new_relations: Vec<(usize, usize)> = Vec::new();
    let mut new_reverse_relations: Vec<(usize, usize)> = Vec::new();
    let mut slice_to_index: HashMap<&[usize], usize> = HashMap::new();
    let mut new_lable_state_map: HashMap<BitVec, Vec<usize>> = HashMap::new();
    let mut new_state_labels: Vec<BitVec> = Vec::new();
    let mut last_state: usize = 0;
    //initialize Hashmap for new states
    //initialize Hashmap for new_lable_state_map
    for (k, slice) in eq_classes.to_slices().enumerate() {
        //get label of slice
        let labels = transition_system.get_state_label(slice[0]).clone();
        //add label to new state labels
        new_state_labels.push(labels.clone());

        //add new index
        slice_to_index.insert(slice, k);
        //init new_lable_state_map
        if let Some(vector) = new_lable_state_map.get_mut(&labels) {
            vector.push(k);
        } else {
            new_lable_state_map.insert(labels.clone(), vec![k]);
        }

        last_state = k;
    }

    let mut successor_buffer = Vec::new();
    for (new_state, slice) in eq_classes.to_slices().enumerate() {
        get_successors(transition_system, slice, &mut successor_buffer);

        for succ in &successor_buffer {
            if let Some(val) = eq_classes.get_block_of_state(&succ) {
                if let Some(new_succ) = slice_to_index.get(val) {
                    let value = (new_state, *new_succ);
                    if !new_relations.contains(&value) {
                        new_relations.push(value);
                        new_reverse_relations.push((*new_succ, new_state));
                    }
                }
            }
        }
    }

    let transformed = new_relations
        .clone()
        .iter()
        .map(|(s1, s2)| (*s1, *s2, true))
        .collect::<Vec<_>>();

    let reverse_transformed = new_reverse_relations
        .clone()
        .iter()
        .map(|(s1, s2)| (*s1, *s2, true))
        .collect::<Vec<_>>();

    let new_tmatrix =
        SparseMatrix::from_list_of_entries(new_relations.len(), new_relations.len(), &transformed);

    let new_reverse_matrix = SparseMatrix::from_list_of_entries(
        new_reverse_relations.len(),
        new_reverse_relations.len(),
        &reverse_transformed,
    ); //build new initial states new indexes
    let mut new_init_states: Vec<usize> = vec![];
    for init_state in transition_system.get_initial_states() {
        if let Some(slice) = eq_classes.get_block_of_state(&init_state) {
            if let Some(new_index) = slice_to_index.get(slice) {
                if !new_init_states.contains(&new_index) {
                    new_init_states.push(*new_index);
                }
            }
        }
    }

    let aps = transition_system.get_ap().clone();
    TransitionSystem::new(
        new_tmatrix,
        new_reverse_matrix,
        last_state,
        new_init_states,
        new_state_labels,
        new_lable_state_map,
        aps,
    )
}

#[cfg(test)]
mod tests {
    use crate::bisimulation::quotienting::quotienting;
    use crate::checker::checker::{Options, QuotientingAlgorithm};
    use crate::checker::invariant::bfs_invariant_checking;
    use crate::property::property::{FormulaTreeNode, FormulaTreeNodeType, Property, PropertyType};

    fn sorted_partition(mut partition: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
        partition.iter_mut().for_each(|class| class.sort());
        partition.sort();
        partition
    }

    fn test_partitioning() {
        // taken from model checking 2023 exercise 9
        let ts = "init: 0 1 6 9
        0a -> 2b
        1a -> 2b
        1a -> 3b
        2b -> 4b
        2b -> 5b
        3b -> 1a
        3b -> 5b
        4b -> 2b
        4b -> 5b

        6a -> 7b
        6a -> 8b
        7b -> 10b
        8b -> 6a
        8b -> 11b
        9a -> 8b
        9a -> 11b
        10b -> 10b
        10b -> 11b
        "
        .parse()
        .unwrap();
        let mut options = Options::new();
        options.set_quotienting_algorithm(QuotientingAlgorithm::SimpleRefinement);
        let quotiened_ts = quotienting(&ts, &options, None);
        println!("{:?}", quotiened_ts.get_states());
        assert_eq!(quotiened_ts.get_states().len(), 9);
        assert_eq!(quotiened_ts.get_num_transitions(), 14);

        //now we build our property
        //we want to build:  a or b or c
        let atomic_a = FormulaTreeNode::new(
            None,
            None,
            Some("a".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let atomic_b = FormulaTreeNode::new(
            None,
            None,
            Some("b".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let atomic_c = FormulaTreeNode::new(
            None,
            None,
            Some("c".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let or = FormulaTreeNode::new(
            Some(Box::new(atomic_b)),
            Some(Box::new(atomic_c)),
            None,
            FormulaTreeNodeType::Or,
        );
        let root = FormulaTreeNode::new(
            Some(Box::new(atomic_a)),
            Some(Box::new(or)),
            None,
            FormulaTreeNodeType::Or,
        );
        let property_1 = Property::new(
            "ExampleTree".to_string(),
            PropertyType::Invariant(root),
            vec!["a".to_string(), "b".to_string(), "c".to_string()],
        );
        assert_eq!(
            bfs_invariant_checking(&ts, &property_1),
            bfs_invariant_checking(&quotiened_ts, &property_1)
        );

        let root = FormulaTreeNode::new(
            None,
            None,
            Some("a".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let property_2 = Property::new(
            "ExampleTree".to_string(),
            PropertyType::Invariant(root),
            vec!["a".to_string()],
        );
        //we test on is_ok here, since name states differ-> traces differ
        assert_eq!(
            bfs_invariant_checking(&ts, &property_2).is_ok(),
            bfs_invariant_checking(&quotiened_ts, &property_2).is_ok()
        );
    }

    fn aps(str: &str) -> Vec<String> {
        str.chars().map(String::from).collect()
    }

    #[test]
    fn test_simple_selection_strategy() {
        test_partitioning();
    }
}
