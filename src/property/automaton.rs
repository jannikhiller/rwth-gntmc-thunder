use std::collections::HashMap;
use bit_vec::BitVec;
use log::trace;
use crate::common::sparse_matrix::{SparseMatrix, SparseMatrixElement};
use crate::property::property::{comp_elementary_sets, FormulaTreeNode, FormulaTreeNodeType, Property, PropertyType};

#[derive(Debug, Copy, Clone)]
pub enum AcceptanceType {
    /// An NFA accepts once it reaches a final state.
    Nfa,
    /// A Buchi automaton accepts if accepting states are reached infinitely
    /// often.
    Buchi,
}

/// A finite automaton that can be used to represent regular safety or omega-regular properties.
#[derive(Debug, Clone)]
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
        }
    }
    #[allow(dead_code)]
    pub fn is_accepting(&self, state: BitVec) -> bool {
        let mut res = state;
        res.and(&self.accepting_states);
        res.any()
    }

    #[allow(dead_code)]
    pub fn step(&mut self, state: BitVec, label: &Vec<String>) -> BitVec {
        let get_successors_of_index = |index: usize| {
            self.transition_matrix
                .get_row(index)
                .into_iter()
                .map(|SparseMatrixElement { col_index, value }| {
                    value.into_iter().map(move |tree| (tree, col_index))
                })
                .flatten()
        };

        let state_successors = state
            .into_iter()
            .enumerate()
            .filter_map(|(i, value)| if value { Some(i) } else { None })
            .map(get_successors_of_index)
            .flatten();

        let mut new_state = BitVec::from_elem(self.last_state + 1, false);
        for (tree, col_index) in state_successors {
            if tree.evaluate(label) {
                new_state.set(col_index, true);
            }
        }
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
    // in this construction, states only have successors if the APs they match
    // the label, so we store the APs for each state to decide if there is an outgoing transition
    pub aps_of_state: Vec<Vec<String>>,
    pub initial_state: BitVec,
    pub accepting_states: Vec<BitVec>,
    last_state: usize,
}

fn filter_succesors_with_next(
    set: &BitVec,
    elementary_sets: &Vec<BitVec>,
    index_of_formula: usize,
    index_of_subformula_of_next: &HashMap<usize, (bool, usize)>,
    successors: &mut BitVec,
) {
    let (inverted, subformula_index) = index_of_subformula_of_next[&index_of_formula];
    if set[index_of_formula] {
        for successor_index in 0..successors.len() {
            if !elementary_sets[successor_index][subformula_index] != inverted {
                successors.set(successor_index, false);
            }
        }
    } else {
        for successor_index in 0..successors.len() {
            if elementary_sets[successor_index][subformula_index] != inverted {
                successors.set(successor_index, false);
            }
        }
    }
}

fn filter_successors_with_until(
    set: &BitVec,
    elementary_sets: &Vec<BitVec>,
    index_of_formula: usize,
    index_of_subformula_of_until: &HashMap<usize, ((bool, usize), (bool, usize))>,
    successors: &mut BitVec,
) {
    // Until(f, g) \in set <==> g \in set or (f \in set and Until(f, g) \in successor)
    trace!(
        "filtering successors with until formula: {}",
        index_of_formula
    );

    let ((f_inverted, f_index), (g_inverted, g_index)) =
        index_of_subformula_of_until[&index_of_formula];
    trace!(
        "f: {} {}, g: {} {}",
        f_index,
        f_inverted,
        g_index,
        g_inverted
    );
    if set[index_of_formula] {
        trace!("set contains until formula");
        if !set[g_index] != g_inverted {
            trace!("g is not in set");
            if !set[f_index] != f_inverted {
                trace!("f is not in set");
                successors.clear();
            } else {
                for successor_index in 0..successors.len() {
                    if !elementary_sets[successor_index][index_of_formula] {
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
            for successor_index in 0..successors.len() {
                if elementary_sets[successor_index][index_of_formula] {
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
        let index_of_subformula_of_next: HashMap<usize, (bool, usize)> = indices_to_formula
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
                    (
                        inverted,
                        *indices_to_formula
                            .iter()
                            .find(|(_, f)| **f == **subformula)
                            .unwrap()
                            .0,
                    ),
                )
            })
            .collect();

        let index_of_subformula_of_until: HashMap<usize, ((bool, usize), (bool, usize))> =
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
                            (
                                left_inverted,
                                *indices_to_formula
                                    .iter()
                                    .find(|(_, f)| **f == **left_subformula)
                                    .unwrap()
                                    .0,
                            ),
                            (
                                right_inverted,
                                *indices_to_formula
                                    .iter()
                                    .find(|(_, f)| **f == **right_subformula)
                                    .unwrap()
                                    .0,
                            ),
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
                        filter_succesors_with_next(
                            set,
                            &elementary_sets,
                            j,
                            &index_of_subformula_of_next,
                            &mut successors,
                        );
                    }
                    FormulaTreeNodeType::Until => {
                        filter_successors_with_until(
                            set,
                            &elementary_sets,
                            j,
                            &index_of_subformula_of_until,
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
                let (_, (g_inverted, g)) = index_of_subformula_of_until[&i];
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

    fn step(&self, state: BitVec, label: &Vec<String>) -> BitVec {
        let mut sorted_label = label.clone();
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
    use bit_vec::BitVec;
    use crate::common::sparse_matrix::SparseMatrix;
    use crate::property::automaton::{AcceptanceType, FiniteAutomaton, LtlGnba};
    use crate::property::property::{FormulaTreeNode, FormulaTreeNodeType, Property, PropertyType};

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
            &vec![
                (0, 1, vec![atomic_a]),
                (1, 2, vec![atomic_b]),
                (2, 3, vec![atomic_c]),
                (3, 0, vec![atomic_d]),
            ],
        );
        println!("{:?}", transition_matrix);

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
        ));

        assert_eq!(ltl_gnba.transition_matrix.rows(), 4);
        assert_eq!(ltl_gnba.transition_matrix.cols(), 4);
        let mut initial_state = BitVec::from_elem(4, false);
        initial_state.set(0, true);
        initial_state.set(2, true);
        assert_eq!(ltl_gnba.initial_state, initial_state);

        let transition_matrix = SparseMatrix::from_2d_vec(&vec![
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

        let translation_to_index = vec![7, 8, 9, 10, 5, 6, 2, 3, 4, 0, 1];

        let mut matrix = vec![vec![false; 11]; 11];
        for row in 0..11 {
            for col in 0..11 {
                matrix[translation_to_index[row]][translation_to_index[col]] =
                    transition_matrix_b_sets[(row, col)];
            }
        }
        let transition_matrix = SparseMatrix::from_2d_vec(&matrix);

        for i in 0..transition_matrix.rows() {
            println!("{:?}", ltl_gnba.transition_matrix.get_col_indexes_in_row(i));
        }

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

        let accepting_states_b_sets = vec![vec![0, 1, 4, 5, 6, 9, 10], vec![0, 2, 4, 6, 7, 9]];
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
}