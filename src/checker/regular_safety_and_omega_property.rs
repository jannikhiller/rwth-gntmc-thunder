use crate::checker::checker::{Options, PersistenceCheckingAlgorithm};
use crate::checker::invariant::bfs_invariant_checking;
use crate::checker::nested_dfs::persistence_checking_with_nested_dfs;
use crate::checker::scc::persistence_checking_with_scc;
use crate::common::sparse_matrix::SparseMatrix;
use crate::common::transition_system::TransitionSystem;
use crate::property::automaton::AcceptanceType::Nfa;
use crate::property::automaton::FiniteAutomaton;
use crate::property::property::FormulaTreeNode;
use crate::property::property::PropertyType;
use crate::property::property::{FormulaTreeNodeType, Property};
use bit_vec::BitVec;
use std::collections::HashMap;

/// Checks if the given transition system satisfies the given property. It accepts regular safety
/// properties and omega regular properties. For regular safety properties it builds the sync.
/// product and then runs an invariant check on this product. For omega regular properties, it
/// builds a product as well and runs a persistence check afterwards.
///
/// # Parameters
///
/// - `transition_system`: The given transition system which gets checked.
/// - `property`: The property to be checked on the given transition system.
///
/// # Returns
/// A Result with `Ok` if the property is fulfilled and Err with a path and a trace otherwise.
pub fn regular_safety_and_omega_checking(
    transition_system: &TransitionSystem,
    property: &Property<String>,
    options: &Options,
) -> Result<bool, (Vec<Vec<String>>, Vec<usize>)> {
    let automaton: FiniteAutomaton<String>;
    let is_omega: bool;
    match property.property_type.clone() {
        PropertyType::Invariant(_) | PropertyType::Persistence(_) => {
            panic!("Wrong Datatype")
        }
        // TODO: here we can also differentiate by the acceptance criteria and hence do not need
        // two separate match cases
        PropertyType::RegularSafety(finite_automata) => {
            // if cloned would be needed here, the compiler would not be satisfied, and we don't need
            // a copy anyways
            automaton = finite_automata;
            is_omega = false;
        }
        PropertyType::OmegaRegular(finite_automata) => {
            automaton = finite_automata;
            is_omega = true;
        }
        PropertyType::Ltl(_) => panic!("Wrong Propertytype"),
        PropertyType::Ctl(_) => panic!("Wrong Propertytype"),
    }

    let product_ts = &transition_system.product_with(automaton);

    // here we construct a property to check if every state in the reachable part of
    // the transitions system does not have a label
    // if one does, then we know that a bad state is reachable
    let node = FormulaTreeNode::new(None, None, None, FormulaTreeNodeType::Atomic);

    if is_omega {
        let empty_property =
            Property::new("emptyProperty".to_string(), PropertyType::Persistence(node));
        // distinguish according to the persistence algorithm set in the options
        match options.persistence_algorithm {
            PersistenceCheckingAlgorithm::Scc => {
                persistence_checking_with_scc(product_ts, &empty_property)
            }
            PersistenceCheckingAlgorithm::NestedDfs => {
                persistence_checking_with_nested_dfs(product_ts, &empty_property)
            }
        }
    } else {
        let empty_property =
            Property::new("emptyProperty".to_string(), PropertyType::Invariant(node));
        bfs_invariant_checking(product_ts, &empty_property)
    }
}
fn create_test_automaton_for_product() -> FiniteAutomaton<String> {
    let a_node = FormulaTreeNode::new(
        None,
        None,
        Some("a".to_string()),
        FormulaTreeNodeType::Atomic,
    );
    let not_a_node = FormulaTreeNode::new(
        Some(Box::new(a_node.clone())),
        None,
        None,
        FormulaTreeNodeType::Not,
    );
    let b_node = FormulaTreeNode::new(
        None,
        None,
        Some("b".to_string()),
        FormulaTreeNodeType::Atomic,
    );
    let not_b_node = FormulaTreeNode::new(
        Some(Box::new(b_node.clone())),
        None,
        None,
        FormulaTreeNodeType::Not,
    );
    let transitions = vec![
        (0, 0, vec![not_a_node.clone()]),
        (0, 1, vec![a_node.clone()]),
        (1, 1, vec![not_b_node.clone()]),
        (1, 2, vec![b_node.clone()]),
        (2, 0, vec![not_a_node.clone()]),
        (2, 1, vec![a_node.clone()]),
    ];
    let transition_matrix = SparseMatrix::from_list_of_entries(4, 4, &transitions);
    let mut init_states = BitVec::from_elem(3, false);
    init_states.set(0, true);
    let mut accepting_states = BitVec::from_elem(3, false);
    accepting_states.set(2, true);

    FiniteAutomaton::new(Nfa, transition_matrix, 2, init_states, accepting_states)
}
fn create_test_transition_system_for_regular_expression() -> TransitionSystem {
    let transitions = vec![
        (0, 1, true),
        (0, 3, true),
        (1, 4, true),
        (2, 1, true),
        (3, 1, true),
        (4, 1, true),
        (4, 5, true),
        (5, 1, true),
        (5, 2, true),
    ];
    let transition_matrix = SparseMatrix::from_list_of_entries(6, 6, &transitions);
    let reverse_transitions = vec![
        (1, 0, true),
        (3, 0, true),
        (4, 1, true),
        (1, 2, true),
        (1, 3, true),
        (1, 4, true),
        (5, 4, true),
        (1, 5, true),
        (2, 5, true),
    ];
    let reverse_transition_matrix = SparseMatrix::from_list_of_entries(6, 6, &reverse_transitions);
    let mut state_labels = Vec::new();
    let ap = vec!["a".to_string(), "b".to_string(), "c".to_string()];
    let mut label0 = BitVec::from_elem(3, false);
    label0.set(0, true);
    label0.set(1, true);
    state_labels.push(label0.clone());
    let mut label1 = BitVec::from_elem(3, false);
    label1.set(0, true);
    label1.set(1, true);
    label1.set(2, true);
    state_labels.push(label1.clone());
    let mut label2 = BitVec::from_elem(3, false);
    label2.set(1, true);
    label2.set(2, true);
    state_labels.push(label2.clone());
    let mut label3 = BitVec::from_elem(3, false);
    label3.set(0, true);
    label3.set(2, true);
    state_labels.push(label3.clone());
    let mut label4 = BitVec::from_elem(3, false);
    label4.set(0, true);
    label4.set(1, true);
    state_labels.push(label4.clone());
    let mut label5 = BitVec::from_elem(3, false);
    label5.set(0, true);
    label5.set(2, true);
    state_labels.push(label5.clone());
    let mut label_state_map = HashMap::new();
    label_state_map.insert(label0, vec![0]);
    label_state_map.insert(label1, vec![1]);
    label_state_map.insert(label2, vec![2]);
    label_state_map.insert(label3, vec![3]);
    label_state_map.insert(label4, vec![4]);
    label_state_map.insert(label5, vec![5]);
    TransitionSystem::new(
        transition_matrix,
        reverse_transition_matrix,
        5,       // last_state
        vec![0], // initial_states
        state_labels,
        label_state_map,
        ap,
    )
}
fn create_test_automaton_for_regular_expression() -> FiniteAutomaton<String> {
    let a_node = FormulaTreeNode::new(
        None,
        None,
        Some("a".to_string()),
        FormulaTreeNodeType::Atomic,
    );
    let not_a_node = FormulaTreeNode::new(
        Some(Box::new(a_node.clone())),
        None,
        None,
        FormulaTreeNodeType::Not,
    );
    //we check on always a so I build automata for alawys not a
    let transitions = vec![
        (0, 0, vec![not_a_node.clone()]),
        (0, 1, vec![a_node.clone()]),
        (1, 0, vec![not_a_node.clone()]),
        (1, 1, vec![a_node.clone()]),
    ];
    let transition_matrix = SparseMatrix::from_list_of_entries(2, 2, &transitions);
    let mut init_states = BitVec::from_elem(2, false);
    init_states.set(0, true);
    let mut accepting_states = BitVec::from_elem(2, false);
    accepting_states.set(1, true);

    FiniteAutomaton::new(Nfa, transition_matrix, 1, init_states, accepting_states)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::sparse_matrix::SparseMatrix;

    #[test]
    fn test_regular_safety_check() {
        let ts = create_test_transition_system_for_regular_expression();
        let automaton: FiniteAutomaton<String> = create_test_automaton_for_regular_expression();
        let reg_prop = Property::new("Test".to_string(), PropertyType::RegularSafety(automaton));
        let mut options = Options::new();
        options.set_persistence_algorithm(PersistenceCheckingAlgorithm::Scc);
        match regular_safety_and_omega_checking(&ts, &reg_prop, &options) {
            Ok(result) => println!("The invariant checking was successful: {}", result),
            Err((error_details, indices)) => {
                println!("Property does not hold");
                println!("Further information: {:?}", error_details);
                println!("Indices of the violation: {:?}", indices);
            }
        }
        assert!(true);
    }
    #[test]
    fn test_scc() {
        let ts = create_test_transition_system_for_product();
        let automaton = create_test_automaton_for_product();
        let omega_prop = Property::new("Test".to_string(), PropertyType::OmegaRegular(automaton));
        let mut options = Options::new();
        options.set_persistence_algorithm(PersistenceCheckingAlgorithm::Scc);
        match regular_safety_and_omega_checking(&ts, &omega_prop, &options) {
            Ok(result) => println!("The invariant checking was successful: {}", result),
            Err((error_details, indices)) => {
                println!("Property does not hold");
                println!("Further information: {:?}", error_details);
                println!("Indices of the violation: {:?}", indices);
            }
        }
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
        let reverse_transitions = [
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
