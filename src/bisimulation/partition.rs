#![allow(dead_code)]

use index_list::{IndexList, ListIndex};
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::Debug;
use std::hash::Hash;
use bit_vec::BitVec;
use itertools::{kmerge, Itertools};
use crate::common::transition_system::TransitionSystem;
use crate::common::vec_helper::{intersect, setminus};

#[derive(Debug, Copy, Clone)]
#[derive(PartialEq)]
struct PartitionBlock {
    start: usize,
    /// exclusive
    end: usize,
}

#[derive(Debug)]
pub struct Partition<T> {
    elements: Vec<T>,
    blocks: IndexList<PartitionBlock>,
    block_map: HashMap<T, ListIndex>,
}

impl Partition<usize> {
    pub fn from_state_space_by_aps(transition_system: &TransitionSystem, filter_aps: Option<&Vec<String>>) -> Self {
        let ap_bitmask = if filter_aps.is_some() {
            transition_system.get_label_from_aps(filter_aps.unwrap()).unwrap_or(BitVec::from_elem(transition_system.get_ap().len(), false))
        } else {
            BitVec::from_elem(transition_system.get_ap().len(), true)
        };

        let states_grouped_by_label = transition_system.get_states()
            .into_group_map_by(|&state| {
                let mut label = transition_system.get_state_label(state).clone();
                label.and(&ap_bitmask);
                label
            })
            .into_values()
            .collect();

        Self::from_vecs(&states_grouped_by_label)
    }

    fn get_predecessor_states_of_block(&self, ts: &TransitionSystem, block: PartitionBlock) -> Vec<usize> {
        let start_index = block.start;
        let end_index = block.end;
        let mut predecessors = Vec::new();

        for current_state_idx in start_index .. end_index {
            let predecessors_of_current_state = ts.get_predecessor_states(self.elements[current_state_idx]);
            predecessors.append(predecessors_of_current_state.to_vec().as_mut());
        }

        predecessors
    }

}

impl<T: Hash + Eq + Clone + Debug + Ord> Partition<T> {
    /// Create a partition from a list of vectors
    pub fn from_vecs(vecs: &Vec<Vec<T>>) -> Self {
        let mut elements = Vec::new();
        let mut blocks = IndexList::new();
        let mut block_map = HashMap::new();
        for v in vecs {
            let start = elements.len();
            elements.extend_from_slice(v);
            let end = elements.len();
            let index = blocks.insert_last(PartitionBlock { start, end });
            for e in v {
                block_map.insert(e.clone(), index);
            }
        }
        Partition {
            elements,
            blocks,
            block_map,
        }
    }

    fn find_in_block(&self, block_index: ListIndex, item: &T) -> usize {
        // TODO: panics here if element is not in block
        let block = self.blocks.get(block_index).unwrap();
        // this is a linear search, if it becomes a bottleneck, we can consider
        // keeping each block sorted
        self.elements[block.start..block.end]
            .iter()
            .position(|e| e == item)
            .unwrap()
            + block.start
    }

    fn move_item_to_next_block(&mut self, block_index: ListIndex, item: &T) {
        let next_block_index = self.blocks.next_index(block_index);
        let block_end = self.blocks.get_mut(block_index).unwrap().end;
        let item_index = self.find_in_block(block_index, item);

        self.elements.swap(item_index, block_end - 1);
        self.blocks.get_mut(block_index).unwrap().end -= 1;
        self.blocks.get_mut(next_block_index).unwrap().start -= 1;
        self.block_map.insert(item.clone(), next_block_index);
    }

    /// Refine the partition wrt a set `splitter`
    /// Returns `true` if the partition has changed
    pub fn refine(&mut self, splitter: &[T]) -> bool {
        let mut changed_blocks = HashSet::new();

        for splitter_item in splitter {
            let &block_index = self.block_map.get(splitter_item).unwrap_or_else(|| {
                panic!("Splitter element {splitter_item:?} is not part of the partition.")
            });
            let block_end = self.blocks.get(block_index).unwrap().end;
            if !changed_blocks.contains(&block_index) {
                self.blocks.insert_after(
                    block_index,
                    PartitionBlock {
                        start: block_end,
                        end: block_end,
                    },
                );
                changed_blocks.insert(block_index);
            }
            self.move_item_to_next_block(block_index, splitter_item);
            let block = self.blocks.get(block_index).unwrap();
            if block.start == block.end {
                self.blocks.remove(block_index);
                changed_blocks.remove(&block_index);
            }
        }

        !changed_blocks.is_empty()
    }

    pub fn ternary_refine(&mut self, pre_c: &Vec<T>, pre_c_prime: &Vec<T>, pre_c_prime_diff_c: &Vec<T>) {
        let mut new_blocks = IndexList::new();

        for block in self.blocks.iter() {
            let states_of_b = self.elements[block.start..block.end].to_vec();

            let b1 = intersect(intersect(states_of_b.as_ref(), pre_c).as_ref(), pre_c_prime_diff_c); // B \cap Pre(C) \cap Pre(C' \setminus C)
            let b2 = setminus(intersect(states_of_b.as_ref(), pre_c).as_ref(), pre_c_prime_diff_c); // (B \cap Pre(C)) \setminus Pre(C' \setminus C)
            let b3 = setminus(intersect(states_of_b.as_ref(), pre_c_prime_diff_c).as_ref(), pre_c); // (B \cap Pre(C' \setminus C)) \setminus Pre(C)
            let b4 = setminus(states_of_b.as_ref(), pre_c_prime); // B \setminus Pre(C')


            let mut offset = block.start;
            let mut marker = block.start;

            let split_blocks = [&b1, &b2, &b3, &b4];
            'inner: for b_i in split_blocks {
                if b_i.is_empty() {
                    continue 'inner;
                }


                let mut b_i_marker = 0;
                let new_block = PartitionBlock {
                    start: marker,
                    end: marker + b_i.len()
                };

                let new_list_index: ListIndex = new_blocks.insert_last(new_block);

                while marker < b_i.len() + offset {
                    self.elements[marker] = b_i[b_i_marker].clone();
                    self.block_map.insert(self.elements[marker].clone(), new_list_index);
                    marker += 1;
                    b_i_marker += 1;
                }

                offset += b_i.len();
            }
        }

        self.blocks = new_blocks;
    }

    pub fn get_block_of_state(&self, state: &T) -> Option<&[T]> {
        let list_index = self.block_map.get(state);

        list_index?;

        let block = &self.blocks.get(*list_index.unwrap());

        list_index?;

        Some(&self.elements[block.unwrap().start..block.unwrap().end])
    }


    /// Return the partition as an iterator over its sets
    pub fn to_slices(&self) -> impl Iterator<Item = &[T]> {
        self.blocks
            .iter()
            .map(|block| &self.elements[block.start..block.end])
    }

    pub fn to_sorted_vecs(&self) -> Vec<Vec<T>> {
        self.to_slices().map(|slice| {
            let mut res = slice.to_vec();
            res.sort();
            res
        }).collect()
    }

    pub fn to_vecs(&self) -> Vec<Vec<T>> {
        self.to_slices().map(|slice| slice.to_vec()).collect()
    }

    pub fn num_blocks(&self) -> usize {
        self.blocks.len()
    }
}

impl fmt::Display for Partition<usize> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for block in self.blocks.iter() {
            writeln!(f, "Block starting at {} to {}:", block.start, block.end);
            write!(f, "[");
            for state in block.start .. block.end {
                write!(f, "{}, ", self.elements[state]);
            }
            writeln!(f, "]");
        }

        Ok(())
    }
}

impl PartialEq for Partition<usize> {
    fn eq(&self, other: &Self) -> bool {
        let mut self_vecs = self.to_sorted_vecs();
        let mut other_vecs = other.to_sorted_vecs();

        self_vecs.sort();
        other_vecs.sort();

        self_vecs == other_vecs
    }
}

pub fn get_predecessors(ts: &TransitionSystem, states: &[usize], result_buffer: &mut Vec<usize>) {
    result_buffer.clear();
    result_buffer.extend(
        kmerge(
            states
                .iter()
                .map(|&state| ts.get_predecessor_states(state).iter()),
        )
            .dedup(),
    );
}

pub fn get_successors(ts: &TransitionSystem, states: &[usize], result_buffer: &mut Vec<usize>) {
    result_buffer.clear();
    result_buffer.extend(
        kmerge(
            states
                .iter()
                .map(|&state| ts.get_successor_states(state).iter()),
        )
            .dedup(),
    );
}

#[cfg(test)]
mod tests {
    use crate::common::sparse_matrix::SparseMatrix;
    use super::*;

    #[test]
    fn test_partition() {
        let partition = Partition::from_vecs(&vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]]);

        let mut partition = partition;
        assert_eq!(
            partition.to_slices().collect::<Vec<_>>(),
            vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9],]
        );

        assert!(partition.refine(&[2, 5]));
        assert_eq!(
            partition.to_slices().collect::<Vec<_>>(),
            vec![vec![1, 3], vec![2], vec![4, 6], vec![5], vec![7, 8, 9],]
        );

        assert!(!partition.refine(&[2, 5]));
        assert_eq!(
            partition.to_slices().collect::<Vec<_>>(),
            vec![vec![1, 3], vec![2], vec![4, 6], vec![5], vec![7, 8, 9],]
        );

        assert!(partition.refine(&[1, 4, 7]));
        assert_eq!(
            partition.to_slices().collect::<Vec<_>>(),
            vec![
                vec![3],
                vec![1],
                vec![2],
                vec![6],
                vec![4],
                vec![5],
                vec![9, 8],
                vec![7],
            ]
        );
        assert!(!partition.refine(&[8, 9]));
        assert_eq!(
            partition.to_slices().collect::<Vec<_>>(),
            vec![
                vec![3],
                vec![1],
                vec![2],
                vec![6],
                vec![4],
                vec![5],
                vec![9, 8],
                vec![7],
            ]
        );
    }

    #[test]
    fn test_ap_partition_from_ts() {
        let transitions = vec![
            (0, 1, true),
            (0, 2, true),
            (2, 1, true),
            (1, 3, true),
            (3, 2, true),
            (3, 3, true),
            (4, 4, true)
        ];
        let transition_matrix = SparseMatrix::from_list_of_entries(5, 5, &transitions);
        let reverse_transitions = [
            (1, 0, true),
            (2, 0, true),
            (1, 2, true),
            (3, 1, true),
            (2, 3, true),
            (3, 3, true),
            (4, 4, true),
        ];
        let reverse_transition_matrix = SparseMatrix::from_list_of_entries(5, 5, &transitions);
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
        let label4 = BitVec::from_elem(2, true);
        state_labels.push(label4.clone());
        let mut label_state_map = HashMap::new();
        let ts = TransitionSystem::new(
            transition_matrix,
            reverse_transition_matrix,
            4,       // last_state
            vec![0], // initial_states
            state_labels,
            label_state_map,
            ap,
        );

        let partition = Partition::from_state_space_by_aps(&ts, Option::None);

        assert_eq!(partition.blocks.len(), 4);

        println!("{}", partition);
    }

    fn aps(str: &str) -> Vec<String> {
        str.chars().map(String::from).collect()
    }

    fn sorted_partition(mut partition: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
        partition.iter_mut().for_each(|class| class.sort());
        partition.sort();
        partition
    }

    #[test]
    fn test_get_initial_partition() {
        let ts = "init: 0 3
        0a -> 1b
        1b -> 2c
        2c -> 0a
        3a -> 1b"
            .parse()
            .unwrap();

        let partition = Partition::from_state_space_by_aps(&ts, Option::from(&aps("ab")));
        assert_eq!(
            sorted_partition(partition.to_vecs()),
            vec![vec![0, 3], vec![1], vec![2]]
        );

        let ts = "init: 0 3
        0ac -> 1a
        1a -> 2ad
        2ad -> 3b
        3b -> 4bz"
            .parse()
            .unwrap();

        let partition = Partition::from_state_space_by_aps(&ts, Option::from(&aps("ab")));
        assert_eq!(
            sorted_partition(partition.to_vecs()),
            vec![vec![0, 1, 2,], vec![3, 4],]
        );
    }
}
