use crate::common::sparse_matrix::*;
use bit_vec::BitVec;
use std::collections::HashMap;

pub struct TransitionSystem {
    transition_matrix: SparseMatrix<bool>,
    reverse_transition_matrix: SparseMatrix<bool>,
    num_states: usize,
    state_names: Vec<String>,
    state_labels: Vec<BitVec>, // labels are BitVecs encoding a set of ap_indexes
    label_state_map: HashMap<BitVec, Vec<usize>>,
    ap: Vec<String>, // this means creating a label takes linear time. We dont expect this to be an
                     // issue but if it becomes one, we can store a HashMap<String, usize>
}

impl TransitionSystem {
    pub fn from_json() -> Self {
        panic!("Not implemented")
    }

    pub fn get_num_states(&self) -> usize {
        self.num_states
    }

    pub fn get_state_name(&self, state: usize) -> &String {
        if state > self.num_states {
            panic!("{state} is not a valid state.");
        }
        &self.state_names[state]
    }

    pub fn get_state_label(&self, state: usize) -> &BitVec {
        if state > self.num_states {
            panic!("{state} is not a valid state.");
        }
        &self.state_labels[state]
    }

    pub fn get_states_with_label(&self, label: &BitVec) -> &Vec<usize> {
        if label.len() != self.state_labels.len() {
            panic!("{label:?} is not a valid label as the BitVec as a different size.");
        }
        static EMPTY_VEC: Vec<usize> = vec![];
        self.label_state_map.get(label).unwrap_or(&EMPTY_VEC)
    }

    pub fn get_ap(&self) -> &Vec<String> {
        &self.ap
    }

    pub fn get_label_from_aps(&self, aps: &[String]) -> BitVec {
        let mut label = BitVec::with_capacity(self.ap.len());
        for s in aps {
            label.set(self.ap.binary_search(s).unwrap(), true);
        }
        return label;
    }

    pub fn get_successor_states(&self, state: usize) -> impl Iterator<Item = usize> + '_ {
        self.transition_matrix.get_row(state).map(
            |SparseMatrixElement {
                 col_index,
                 value: _,
             }| col_index,
        )
    }

    pub fn get_predeccessor_states(&self, state: usize) -> impl Iterator<Item = usize> + '_ {
        self.reverse_transition_matrix.get_row(state).map(
            |SparseMatrixElement {
                 col_index,
                 value: _,
             }| col_index,
        )
    }
}
