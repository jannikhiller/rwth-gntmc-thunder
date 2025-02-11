use crate::checker::invariant::bfs_invariant_checking;
use crate::checker::new_nested_dfs;
use crate::checker::scc::persistence_checking_with_scc;
use crate::checker::{nested_dfs, scc_couvreur};
use crate::checker::{Options, PersistenceCheckingAlgorithm};
use crate::common::transition_system::TransitionSystem;
use crate::property::automaton::FiniteAutomaton;
use crate::property::*;

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
            // a copy anyway
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

    let (product_ts, old_state_new_state_map) = &transition_system.product_with(automaton);

    // here we construct a property to check if every state in the reachable part of
    // the transitions system does not have a label
    // if one does, then we know that a bad state is reachable
    let node = FormulaTreeNode::new(None, None, None, FormulaTreeNodeType::Atomic);

    if is_omega {
        let empty_property = Property::new(
            "emptyProperty".to_string(),
            PropertyType::Persistence(node),
            vec![],
        );
        // distinguish according to the persistence algorithm set in the options
        match options.persistence_algorithm {
            PersistenceCheckingAlgorithm::Scc => persistence_checking_with_scc(
                product_ts,
                &empty_property,
                Some(old_state_new_state_map),
            ),
            PersistenceCheckingAlgorithm::NestedDfs => {
                nested_dfs::persistence_checking_with_nested_dfs(
                    product_ts,
                    &empty_property,
                    Some(old_state_new_state_map),
                )
            }
            PersistenceCheckingAlgorithm::NewNestedDfs => {
                new_nested_dfs::persistence_checking_with_nested_dfs(
                    product_ts,
                    &empty_property,
                    Some(old_state_new_state_map),
                )
            }
            PersistenceCheckingAlgorithm::SccCouvreur => {
                scc_couvreur::persistence_checking_with_couvreur_scc(
                    product_ts,
                    &empty_property,
                    Some(old_state_new_state_map),
                )
            }
        }
    } else {
        let empty_property = Property::new(
            "emptyProperty".to_string(),
            PropertyType::Invariant(node),
            vec![],
        );
        bfs_invariant_checking(product_ts, &empty_property)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::sparse_matrix::SparseMatrix;
    use crate::property::automaton::AcceptanceType::*;
    use crate::property::automaton::*;
    use bit_vec::BitVec;

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

    #[test]
    fn test_regular_safety_check() {
        let ts = "init: 0
        0ab -> 1abc
        0ab -> 3ac
        1abc -> 4ab
        2bc -> 1abc
        3ac -> 1abc
        4ab -> 1abc
        4bc -> 5ac
        5ac -> 1abc
        5bc -> 2bc
        "
        .parse()
        .unwrap();
        let automaton: FiniteAutomaton<String> = create_test_automaton_for_regular_expression();
        let reg_prop = Property::new(
            "Test".to_string(),
            PropertyType::RegularSafety(automaton),
            vec![],
        );
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
    }
    #[test]
    fn test_scc() {
        let ts = "init: 0
        0ab -> 1
        0ab -> 2a
        2a -> 1
        1 -> 3b
        3b -> 2a
        3b -> 3b
        "
        .parse()
        .unwrap();
        let automaton = create_test_automaton_for_product();
        let omega_prop = Property::new(
            "Test".to_string(),
            PropertyType::OmegaRegular(automaton),
            vec![],
        );
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
    }
}
