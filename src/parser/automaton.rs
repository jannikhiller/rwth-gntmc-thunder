use crate::common::sparse_matrix::{SparseMatrix, SparseMatrixElement};
use crate::parser::property::{
    comp_elementary_sets, FormulaTreeNode, FormulaTreeNodeType, Property, PropertyType,
};
use array_tool::vec::*;
use bit_vec::BitVec;
use log::{debug, trace};
use std::collections::HashMap;

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum AcceptanceType {
    /// An NFA accepts once it reaches a final state.
    Nfa,
    /// A Buchi automaton accepts if accepting states are reached infinitely
    /// often.
    Buchi,
}

/// A finite automaton that can be used to represent regular safety or omega-regular properties.
#[derive(Debug, Clone, PartialEq)]
pub struct FiniteAutomaton<ValueType> {
    /// The type of acceptance for this automaton.
    acceptance: AcceptanceType,
    /// The transition matrix of the automaton.
    transition_matrix: SparseMatrix<Vec<FormulaTreeNode<ValueType>>>,
    /// Highest state index in the automaton.
    last_state: usize,
    /// The initial state of the automaton represented as element of the powerset of indexes
    initial_state: BitVec,
    /// The accepting states of the automaton.
    accepting_states: BitVec,
    /// The set of atomic propositions on which the automaton operates. It should be the least alphabet of this automaton.
    /// It is optional as it is only necessary for Buchi automata derived from LTL formulae.
    atomic_propositions: Option<Vec<ValueType>>,
}

impl FiniteAutomaton<String> {
    pub fn new(
        acceptance: AcceptanceType,
        transition_matrix: SparseMatrix<Vec<FormulaTreeNode<String>>>,
        last_state: usize,
        initial_state: BitVec,
        accepting_states: BitVec,
    ) -> Self {
        FiniteAutomaton {
            acceptance,
            transition_matrix,
            last_state,
            initial_state,
            accepting_states,
            atomic_propositions: None,
        }
    }
    /*
    pub fn new_with_aps(
        acceptance: AcceptanceType,
        transition_matrix: SparseMatrix<Vec<FormulaTreeNode<String>>>,
        last_state: usize,
        initial_state: BitVec,
        accepting_states: BitVec,
        atomic_propositions: Option<Vec<String>>,
    ) -> Self {
        FiniteAutomaton {
            acceptance,
            transition_matrix,
            last_state,
            initial_state,
            accepting_states,
            atomic_propositions,
        }
    }
    */

    pub fn from_gnba(mut gnba: LtlGnba) -> Self {
        fn create_formula_from_state_aps(aps: Vec<String>) -> FormulaTreeNode<String> {
            let res = if aps.is_empty() {
                FormulaTreeNode::new(None, None, None, FormulaTreeNodeType::Atomic)
            } else if aps.len() == 1 {
                FormulaTreeNode::new(
                    None,
                    None,
                    Some(aps[0].to_string()),
                    FormulaTreeNodeType::Atomic,
                )
            } else {
                FormulaTreeNode::new(
                    Some(Box::from(FormulaTreeNode::new(
                        None,
                        None,
                        Some(aps[0].to_string()),
                        FormulaTreeNodeType::Atomic,
                    ))),
                    Some(Box::from(create_formula_from_state_aps(
                        aps[1..].to_owned(),
                    ))),
                    None,
                    FormulaTreeNodeType::And,
                )
            };
            trace!("Formula: {}", res);
            res
        }

        // If the gnba does not contain any accepting sets, the property does not specify any
        // infinite behavior, i.e., it does not contain any until. Thus, all states (= all
        // behavior) is acceptable.
        if gnba.accepting_states.is_empty() {
            gnba.accepting_states = vec![BitVec::from_elem(gnba.last_state + 1, true)];
        }

        let num_accepting_sets = gnba.accepting_states.len();
        let num_of_gnba_states = gnba.last_state + 1;
        let nba_last_state = (num_of_gnba_states * num_accepting_sets) - 1; // - 1 because 0 is the first state
        let initial_state = BitVec::from_fn(nba_last_state + 1, |index| {
            gnba.initial_state.get(index).unwrap_or_default()
        });
        let accepting_states = BitVec::from_fn(nba_last_state + 1, |index| {
            gnba.accepting_states[0].get(index).unwrap_or_default()
        });
        let acceptance = AcceptanceType::Buchi;
        let mut list_of_entries = vec![];

        debug!("Number of states: {}", num_of_gnba_states);
        debug!("Number of accepting sets: {}", num_accepting_sets);
        debug!("Number of initial states: {}", initial_state.count_ones());
        debug!("Last state: {}", nba_last_state);

        for current_accepting_set in 0..num_accepting_sets {
            trace!(
                "Current accepting set, i.e., copy of the gnba: {}",
                current_accepting_set
            );
            for gnba_state in 0..num_of_gnba_states {
                let state_copy_offset = current_accepting_set * num_of_gnba_states;
                let nba_state = gnba_state + state_copy_offset;

                trace!(
                    "Current NBA state {:?} equals GNBA state {:?} in copy {:?}",
                    nba_state,
                    gnba_state,
                    current_accepting_set
                );

                // we need this to construct our transition matrix
                let formula = create_formula_from_state_aps(gnba.aps_of_state[gnba_state].clone());

                // check if state is an accepting state in the current copy of the GNBA
                if gnba.accepting_states[current_accepting_set][gnba_state] {
                    trace!("Found transition to next partition");
                    // use step from gnba
                    // give current state in bitvec and aps as label
                    // iterate over enumerated result
                    // if contained in result => we found a successor
                    // calculate modulo sum and add to list of entries

                    let mut gstate_bv = BitVec::from_elem(gnba.last_state + 1, false);
                    gstate_bv.set(gnba_state, true);

                    let target_states = gnba.step(gstate_bv, &gnba.aps_of_state[gnba_state]);
                    target_states.iter().enumerate().for_each(
                        |(gnba_successor_state, is_reachable)| {
                            if is_reachable {
                                // gnba_successor_state + state_copy_offset => corresponding state in the current copy/partition
                                // + num_of_gnba_states => switch to corresponding state in next partition
                                trace!(
                                    "({} + {} + {}) % ({} * {}) = {}",
                                    gnba_successor_state,
                                    state_copy_offset,
                                    num_of_gnba_states,
                                    num_accepting_sets,
                                    num_of_gnba_states,
                                    (gnba_successor_state + state_copy_offset + num_of_gnba_states)
                                        % (num_accepting_sets * num_of_gnba_states)
                                );
                                let next_nba_state =
                                    (gnba_successor_state + state_copy_offset + num_of_gnba_states)
                                        % (num_accepting_sets * num_of_gnba_states);
                                list_of_entries.push((
                                    nba_state,
                                    next_nba_state,
                                    vec![formula.clone()],
                                ));
                            }
                        },
                    )
                } else {
                    let mut gstate_bv = BitVec::from_elem(gnba.last_state + 1, false);
                    gstate_bv.set(gnba_state, true);

                    let target_states = gnba.step(gstate_bv, &gnba.aps_of_state[gnba_state]);
                    target_states.iter().enumerate().for_each(
                        |(gnba_successor_state, is_reachable)| {
                            if is_reachable {
                                let next_nba_state = gnba_successor_state + state_copy_offset;
                                list_of_entries.push((
                                    nba_state,
                                    next_nba_state,
                                    vec![formula.clone()],
                                ));
                            }
                        },
                    )
                }
            }
        }

        let transition_matrix = SparseMatrix::from_list_of_entries(
            nba_last_state + 1,
            nba_last_state + 1,
            &list_of_entries,
        );

        Self {
            acceptance,
            transition_matrix,
            last_state: nba_last_state,
            initial_state,
            accepting_states,
            atomic_propositions: Some(
                gnba.aps_of_state
                    .iter()
                    .fold(Vec::new(), |acc, val| acc.union(val.clone())),
            ),
        }
    }

    #[allow(dead_code)]
    pub fn is_accepting(&self, state: BitVec) -> bool {
        let mut res = state;
        res.and(&self.accepting_states);
        res.any()
    }

    pub fn get_atomic_propositions(&self) -> Option<Vec<String>> {
        self.atomic_propositions.clone()
    }

    #[allow(dead_code)]
    pub fn step(&mut self, state: BitVec, label: &Vec<String>) -> BitVec {
        trace!("State {} with label {:?}", state, label);
        let get_successors_of_index = |index: usize| {
            self.transition_matrix.get_row(index).flat_map(
                |SparseMatrixElement { col_index, value }| {
                    value.iter().map(move |tree| (tree, col_index))
                },
            )
        };

        let state_successors = state
            .into_iter()
            .enumerate()
            .filter_map(|(i, value)| if value { Some(i) } else { None })
            .flat_map(get_successors_of_index);

        let mut new_state = BitVec::from_elem(self.last_state + 1, false);
        for (tree, col_index) in state_successors {
            trace!("Tree: {}", tree);
            if tree.evaluate(label) {
                new_state.set(col_index, true);
                trace!("Formula fullfilled => found successors: {:?}", new_state);
            }
        }

        trace!("all successors: {:?}", new_state);
        new_state
    }

    #[allow(dead_code)]
    pub fn get_initial_state(&self) -> &BitVec {
        &self.initial_state
    }

    #[allow(dead_code)]
    pub fn get_last_state(&self) -> usize {
        self.last_state
    }

    #[allow(dead_code)]
    pub fn get_acceptance_type(&self) -> AcceptanceType {
        self.acceptance
    }

    pub fn get_accepting_states(&self) -> &BitVec {
        &self.accepting_states
    }
}

pub struct LtlGnba {
    pub transition_matrix: SparseMatrix<bool>,
    // in this construction, states only have successors if their APs match
    // the label, so we store the APs for each state to decide if there is an outgoing transition
    pub aps_of_state: Vec<Vec<String>>,
    pub initial_state: BitVec,
    pub accepting_states: Vec<BitVec>,
    last_state: usize,
}

#[derive(Debug, Clone, PartialEq, Copy)]
struct SubFormulaIndex {
    index: usize,
    inverted: bool,
}

fn filter_successors_with_next(
    set: &BitVec,
    elementary_sets: &[BitVec],
    index_of_formula: usize,
    index_of_subformula: SubFormulaIndex,
    successors: &mut BitVec,
) {
    let SubFormulaIndex {
        index: subformula_index,
        inverted,
    } = index_of_subformula;
    if set[index_of_formula] {
        for (successor_index, elementary_set) in elementary_sets.iter().enumerate() {
            if elementary_set[subformula_index] == inverted {
                successors.set(successor_index, false);
            }
        }
    } else {
        for (successor_index, elementary_set) in elementary_sets.iter().enumerate() {
            if elementary_set[subformula_index] != inverted {
                successors.set(successor_index, false);
            }
        }
    }
}

fn filter_successors_with_until(
    set: &BitVec,
    elementary_sets: &[BitVec],
    index_of_formula: usize,
    index_of_subformulas: (SubFormulaIndex, SubFormulaIndex),
    successors: &mut BitVec,
) {
    // Until(f, g) \in set <==> g \in set or (f \in set and Until(f, g) \in successor)
    trace!(
        "filtering successors with until formula: {}",
        index_of_formula
    );

    let (
        SubFormulaIndex {
            index: f_index,
            inverted: f_inverted,
        },
        SubFormulaIndex {
            index: g_index,
            inverted: g_inverted,
        },
    ) = index_of_subformulas;
    trace!(
        "f: {} {}, g: {} {}",
        f_index,
        f_inverted,
        g_index,
        g_inverted
    );
    if set[index_of_formula] {
        trace!("set contains until formula");
        if set[g_index] == g_inverted {
            trace!("g is not in set");
            if set[f_index] == f_inverted {
                trace!("f is not in set");
                successors.clear();
            } else {
                for (successor_index, elementary_set) in elementary_sets.iter().enumerate() {
                    if !elementary_set[index_of_formula] {
                        trace!("g is not in successor {}", successor_index);
                        successors.set(successor_index, false);
                    }
                }
            }
        }
    } else {
        // Until(f, g) \notin set => g \notin set and (f \notin set or Until(f, g) \notin successor)
        trace!("set does not contain until formula");
        if set[g_index] != g_inverted {
            successors.clear();
        } else if set[f_index] != f_inverted {
            trace!("f is in set");
            for (successor_index, elementary_set) in elementary_sets.iter().enumerate() {
                if elementary_set[index_of_formula] {
                    trace!("g is in successor {}", successor_index);
                    successors.set(successor_index, false);
                }
            }
        }
    }
    trace!("successors after until: {:?}", successors);
}

impl LtlGnba {
    pub fn from_ltl_property(ltl_prop: &Property<String>) -> LtlGnba {
        let (indices_to_formula, elementary_sets) = comp_elementary_sets(ltl_prop);
        let last_state = elementary_sets.len() - 1;

        let ltl_formula = if let PropertyType::Ltl(formula) = &ltl_prop.property_type {
            formula
        } else {
            panic!("This is not an LTL formula.");
        };

        // we precompute the indexes of the subformulas for next and until
        let index_of_subformula_of_next: HashMap<usize, SubFormulaIndex> = indices_to_formula
            .iter()
            .filter(|(_, formula)| formula.node_type == FormulaTreeNodeType::Next)
            .map(|(index, formula)| {
                let mut subformula = formula.left.as_ref().unwrap();
                let mut inverted = false;
                if subformula.node_type == FormulaTreeNodeType::Not {
                    inverted = true;
                    subformula = subformula.left.as_ref().unwrap();
                }
                (
                    *index,
                    SubFormulaIndex {
                        index: *indices_to_formula
                            .iter()
                            .find(|(_, f)| **f == **subformula)
                            .unwrap()
                            .0,
                        inverted,
                    },
                )
            })
            .collect();

        let index_of_subformulas_of_until: HashMap<usize, (SubFormulaIndex, SubFormulaIndex)> =
            indices_to_formula
                .iter()
                .filter(|(_, formula)| formula.node_type == FormulaTreeNodeType::Until)
                .map(|(index, formula)| {
                    let mut left_subformula = formula.left.as_ref().unwrap();
                    let mut left_inverted = false;
                    if left_subformula.node_type == FormulaTreeNodeType::Not {
                        left_subformula = left_subformula.left.as_ref().unwrap();
                        left_inverted = true;
                    }
                    let mut right_subformula = formula.right.as_ref().unwrap();
                    let mut right_inverted = false;
                    if right_subformula.node_type == FormulaTreeNodeType::Not {
                        right_subformula = right_subformula.left.as_ref().unwrap();
                        right_inverted = true;
                    }
                    (
                        *index,
                        (
                            SubFormulaIndex {
                                index: *indices_to_formula
                                    .iter()
                                    .find(|(_, f)| **f == **left_subformula)
                                    .unwrap()
                                    .0,
                                inverted: left_inverted,
                            },
                            SubFormulaIndex {
                                index: *indices_to_formula
                                    .iter()
                                    .find(|(_, f)| **f == **right_subformula)
                                    .unwrap()
                                    .0,
                                inverted: right_inverted,
                            },
                        ),
                    )
                })
                .collect();

        let mut entries = vec![];
        let mut aps_of_state = vec![];

        trace!("indices to formula:");
        for (i, f) in indices_to_formula.iter() {
            trace!("{}: {}", i, f);
        }

        for (i, set) in elementary_sets.iter().enumerate() {
            // the only outgoing transition a set has is with the label corresponding to the APs in
            // it, so we determine this label
            let mut aps: Vec<_> = set
                .iter()
                .enumerate()
                .filter_map(|(j, value)| {
                    let is_atomic =
                        value && indices_to_formula[&j].node_type == FormulaTreeNodeType::Atomic;
                    is_atomic.then(|| indices_to_formula[&j].label.as_ref().unwrap().clone())
                })
                .collect();
            aps.sort();
            aps_of_state.push(aps);

            // now we narrow down possible successors
            let mut successors = BitVec::from_elem(elementary_sets.len(), true);
            trace!("finding successors for set: {:?} {:?}", i, set);

            for (&j, formula) in indices_to_formula.iter() {
                match formula.node_type {
                    FormulaTreeNodeType::Next => {
                        filter_successors_with_next(
                            set,
                            &elementary_sets,
                            j,
                            index_of_subformula_of_next[&j],
                            &mut successors,
                        );
                    }
                    FormulaTreeNodeType::Until => {
                        filter_successors_with_until(
                            set,
                            &elementary_sets,
                            j,
                            index_of_subformulas_of_until[&j],
                            &mut successors,
                        );
                    }
                    _ => {}
                }
            }
            trace!("successors: {:?}", successors);
            entries.extend(
                successors
                    .iter()
                    .enumerate()
                    .filter_map(|(j, value)| value.then_some((i, j, true))),
            );
        }
        let transition_matrix =
            SparseMatrix::from_list_of_entries(last_state + 1, last_state + 1, &entries);

        let index_of_ltl_formula = *indices_to_formula
            .iter()
            .find(|(_, formula)| **formula == *ltl_formula)
            .unwrap()
            .0;
        let mut initial_state = BitVec::from_elem(last_state + 1, false);
        for (i, set) in elementary_sets.iter().enumerate() {
            if set[index_of_ltl_formula] {
                initial_state.set(i, true);
            }
        }
        let accepting_states: Vec<_> = indices_to_formula
            .iter()
            .filter_map(|(i, formula)| {
                (formula.node_type == FormulaTreeNodeType::Until).then_some(i)
            })
            .map(|&i| {
                let mut f = BitVec::from_elem(last_state + 1, false);
                let (
                    _,
                    SubFormulaIndex {
                        index: g,
                        inverted: g_inverted,
                    },
                ) = index_of_subformulas_of_until[&i];
                for (j, set) in elementary_sets.iter().enumerate() {
                    if !set[i] || (set[g] != g_inverted) {
                        f.set(j, true);
                    }
                }
                f
            })
            .collect();

        LtlGnba {
            transition_matrix,
            aps_of_state,
            initial_state,
            accepting_states,
            last_state,
        }
    }

    fn step(&self, state: BitVec, label: &[String]) -> BitVec {
        let mut sorted_label = label.to_vec();
        sorted_label.sort();

        let mut new_state = BitVec::from_elem(self.last_state + 1, false);
        for i in state
            .iter()
            .enumerate()
            .filter_map(|(i, value)| value.then_some(i))
        {
            if self.aps_of_state[i] != sorted_label {
                continue;
            }
            for &j in self.transition_matrix.get_col_indexes_in_row(i) {
                new_state.set(j, true);
            }
        }
        new_state
    }
}

#[cfg(test)]
mod tests {
    use crate::common::sparse_matrix::SparseMatrix;
    use crate::parser::automaton::{AcceptanceType, FiniteAutomaton, LtlGnba};
    use crate::parser::property::{FormulaTreeNode, FormulaTreeNodeType, Property, PropertyType};
    use bit_vec::BitVec;

    #[test]
    fn test_finite_automaton() {
        let atomic_a = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let atomic_b = FormulaTreeNode::new(
            None,
            None,
            Some("B".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let atomic_c = FormulaTreeNode::new(
            None,
            None,
            Some("C".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let atomic_d = FormulaTreeNode::new(
            None,
            None,
            Some("D".to_string()),
            FormulaTreeNodeType::Atomic,
        );

        let transition_matrix = SparseMatrix::from_list_of_entries(
            4,
            4,
            &[
                (0, 1, vec![atomic_a]),
                (1, 2, vec![atomic_b]),
                (2, 3, vec![atomic_c]),
                (3, 0, vec![atomic_d]),
            ],
        );

        let mut initial_state = BitVec::from_elem(4, false);
        initial_state.set(0, true);

        let mut accepting_states = BitVec::from_elem(4, false);
        accepting_states.set(0, true);
        accepting_states.set(3, true);

        let mut automaton = FiniteAutomaton::new(
            AcceptanceType::Buchi,
            transition_matrix,
            3,
            initial_state,
            accepting_states,
        );

        let labels = vec![
            "A".to_string(),
            "B".to_string(),
            "C".to_string(),
            "D".to_string(),
        ];
        assert!(
            automaton.is_accepting(automaton.get_initial_state().clone()),
            "Initial state should be accepting."
        );

        let automaton_state = automaton.get_initial_state();
        println!("{:?}", automaton_state);
        let automaton_state = automaton.step(automaton_state.clone(), &labels);
        println!("{:?}", automaton_state);
        assert!(
            !automaton.is_accepting(automaton_state.clone()),
            "State should not be accepting after one step."
        );

        let automaton_state = &automaton.step(automaton_state.clone(), &labels);
        println!("{:?}", automaton_state);
        assert!(
            !automaton.is_accepting(automaton_state.clone()),
            "State should not be accepting after two steps."
        );

        let automaton_state = automaton.step(automaton_state.clone(), &labels);
        println!("{:?}", automaton_state);
        assert!(
            automaton.is_accepting(automaton_state),
            "State should be accepting after three steps."
        );
    }

    #[test]
    fn test_ltl_gnba_next() {
        // phi' = NEXT a
        let ltl_tree = FormulaTreeNode::new(
            Some(Box::from(FormulaTreeNode::new(
                None,
                None,
                Some("a".to_string()),
                FormulaTreeNodeType::Atomic,
            ))),
            None,
            None,
            FormulaTreeNodeType::Next,
        );
        let ltl_gnba = LtlGnba::from_ltl_property(&Property::new(
            "ltl property".to_string(),
            PropertyType::Ltl(ltl_tree.clone()),
            vec!["a".to_string()],
        ));

        assert_eq!(ltl_gnba.transition_matrix.rows(), 4);
        assert_eq!(ltl_gnba.transition_matrix.cols(), 4);
        let mut initial_state = BitVec::from_elem(4, false);
        initial_state.set(0, true);
        initial_state.set(2, true);
        assert_eq!(ltl_gnba.initial_state, initial_state);

        let transition_matrix = SparseMatrix::from_2d_vec(&[
            vec![true, true, false, false],
            vec![false, false, true, true],
            vec![true, true, false, false],
            vec![false, false, true, true],
        ]);
        assert_eq!(ltl_gnba.transition_matrix, transition_matrix);
        assert_eq!(ltl_gnba.accepting_states, vec![]);
        assert_eq!(
            ltl_gnba.aps_of_state,
            vec![vec!["a"], vec!["a"], vec![], vec![]]
        );
    }

    #[test]
    fn test_ltl_gnba_complex() {
        // phi = true U (a AND (NOT ((NOT b) U (a AND b))))
        let ltl_tree = FormulaTreeNode::new(
            Some(Box::from(FormulaTreeNode::new(
                None,
                None,
                None,
                FormulaTreeNodeType::True,
            ))),
            Some(Box::from(FormulaTreeNode::new(
                Some(Box::from(FormulaTreeNode::new(
                    None,
                    None,
                    Some("a".to_string()),
                    FormulaTreeNodeType::Atomic,
                ))),
                Some(Box::from(FormulaTreeNode::new(
                    Some(Box::from(FormulaTreeNode::new(
                        Some(Box::from(FormulaTreeNode::new(
                            Some(Box::from(FormulaTreeNode::new(
                                None,
                                None,
                                Some("b".to_string()),
                                FormulaTreeNodeType::Atomic,
                            ))),
                            None,
                            None,
                            FormulaTreeNodeType::Not,
                        ))),
                        Some(Box::from(FormulaTreeNode::new(
                            Some(Box::from(FormulaTreeNode::new(
                                None,
                                None,
                                Some("a".to_string()),
                                FormulaTreeNodeType::Atomic,
                            ))),
                            Some(Box::from(FormulaTreeNode::new(
                                None,
                                None,
                                Some("b".to_string()),
                                FormulaTreeNodeType::Atomic,
                            ))),
                            None,
                            FormulaTreeNodeType::And,
                        ))),
                        None,
                        FormulaTreeNodeType::Until,
                    ))),
                    None,
                    None,
                    FormulaTreeNodeType::Not,
                ))),
                None,
                FormulaTreeNodeType::And,
            ))),
            None,
            FormulaTreeNodeType::Until,
        );

        let ltl_gnba = LtlGnba::from_ltl_property(&Property::new(
            "ltl property".to_string(),
            PropertyType::Ltl(ltl_tree.clone()),
            vec!["a".to_string(), "b".to_string()],
        ));

        let transition_matrix_b_sets = SparseMatrix::from_2d_vec(&vec![
            vec![
                true, false, false, false, true, false, false, false, false, false, false,
            ],
            vec![
                false, true, false, false, false, true, true, false, false, false, false,
            ],
            vec![
                false, false, true, false, false, false, false, true, false, true, false,
            ],
            vec![
                false, false, false, true, false, false, false, false, true, false, true,
            ],
            vec![
                true, false, true, false, true, false, false, true, false, true, false,
            ],
            vec![
                false, true, false, true, false, true, true, false, true, false, true,
            ],
            vec![
                true, true, false, false, true, true, true, false, false, false, false,
            ],
            vec![
                false, false, true, false, false, false, false, true, false, true, false,
            ],
            vec![
                false, false, false, true, false, false, false, false, true, false, true,
            ],
            vec![
                true, false, true, false, true, false, false, true, false, true, false,
            ],
            vec![
                false, true, false, true, false, true, true, false, true, false, true,
            ],
        ]);

        let translation_to_index = [7, 8, 9, 10, 5, 6, 2, 3, 4, 0, 1];

        let mut matrix = vec![vec![false; 11]; 11];
        for row in 0..11 {
            for col in 0..11 {
                matrix[translation_to_index[row]][translation_to_index[col]] =
                    transition_matrix_b_sets[(row, col)];
            }
        }
        let transition_matrix = SparseMatrix::from_2d_vec(&matrix);

        assert_eq!(ltl_gnba.transition_matrix, transition_matrix);
        let aps_of_state_b_sets = vec![
            vec![],
            vec![],
            vec![],
            vec![],
            vec!["b"],
            vec!["b"],
            vec!["a"],
            vec!["a"],
            vec!["a"],
            vec!["a", "b"],
            vec!["a", "b"],
        ];
        let mut aps_of_state = vec![vec![]; 11];
        for i in 0..11 {
            aps_of_state[translation_to_index[i]] = aps_of_state_b_sets[i].clone();
        }

        assert_eq!(ltl_gnba.aps_of_state, aps_of_state);
        let init_state_indexes_b_sets = vec![1, 3, 5, 6, 8, 10];
        let mut initial_state = BitVec::from_elem(11, false);
        for i in init_state_indexes_b_sets {
            initial_state.set(translation_to_index[i], true);
        }
        assert_eq!(ltl_gnba.initial_state, initial_state);
        print!("{:?}", ltl_gnba.accepting_states);

        let accepting_states_b_sets = [vec![0, 1, 4, 5, 6, 9, 10], vec![0, 2, 4, 6, 7, 9]];
        let mut accepting_states = vec![BitVec::from_elem(11, false); 2];

        for i in 0..2 {
            for j in accepting_states_b_sets[i].iter() {
                accepting_states[i].set(translation_to_index[*j], true);
            }
        }
        let mut ltl_accepting_states = ltl_gnba.accepting_states.clone();
        ltl_accepting_states.sort();
        accepting_states.sort();

        assert_eq!(ltl_accepting_states, accepting_states);
    }

    #[test]
    fn test_gnba_to_nba() {
        let mut gnba_initial = BitVec::from_elem(3, false);
        gnba_initial.set(0, true);
        let mut gnba_accept1 = BitVec::from_elem(3, false);
        gnba_accept1.set(1, true);
        let mut gnba_accept2 = BitVec::from_elem(3, false);
        gnba_accept2.set(2, true);
        let gnba = LtlGnba {
            transition_matrix: SparseMatrix::from_2d_vec(&[
                vec![true, true, true],
                vec![true, false, false],
                vec![true, false, false],
            ]),
            aps_of_state: vec![
                vec!["q0".to_string()],
                vec!["q1".to_string()],
                vec!["q2".to_string()],
            ],
            initial_state: gnba_initial,
            accepting_states: vec![gnba_accept1, gnba_accept2],
            last_state: 2,
        };

        // q0,1 -> 0, q1,1 -> 1, q2,1 -> 2
        // q0,2 -> 3, q1,2 -> 4, q2,2 -> 5
        let mut initial_state_bitvec = BitVec::from_elem(6, false);
        initial_state_bitvec.set(0, true);
        let mut accepting_states_bitvec = BitVec::from_elem(6, false);
        accepting_states_bitvec.set(1, true);

        let q0_formula = FormulaTreeNode::new(
            None,
            None,
            Some("q0".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let q1_formula = FormulaTreeNode::new(
            None,
            None,
            Some("q1".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let q2_formula = FormulaTreeNode::new(
            None,
            None,
            Some("q2".to_string()),
            FormulaTreeNodeType::Atomic,
        );
        let nba_transitions = SparseMatrix::from_2d_vec(&[
            vec![
                vec![q0_formula.clone()],
                vec![q0_formula.clone()],
                vec![q0_formula.clone()],
                vec![],
                vec![],
                vec![],
            ],
            vec![
                vec![],
                vec![],
                vec![],
                vec![q1_formula.clone()],
                vec![],
                vec![],
            ],
            vec![
                vec![q2_formula.clone()],
                vec![],
                vec![],
                vec![],
                vec![],
                vec![],
            ],
            vec![
                vec![],
                vec![],
                vec![],
                vec![q0_formula.clone()],
                vec![q0_formula.clone()],
                vec![q0_formula.clone()],
            ],
            vec![
                vec![],
                vec![],
                vec![],
                vec![q1_formula.clone()],
                vec![],
                vec![],
            ],
            vec![
                vec![q2_formula.clone()],
                vec![],
                vec![],
                vec![],
                vec![],
                vec![],
            ],
        ]);
        let nba = FiniteAutomaton {
            acceptance: AcceptanceType::Buchi,
            transition_matrix: nba_transitions,
            last_state: 5,
            initial_state: initial_state_bitvec,
            accepting_states: accepting_states_bitvec,
            atomic_propositions: Some(vec!["q0".to_string(), "q1".to_string(), "q2".to_string()]),
        };

        assert_eq!(nba, FiniteAutomaton::from_gnba(gnba));
    }
}
