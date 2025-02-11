#![allow(dead_code)]

use crate::common::transition_system::TransitionSystem;
use bit_vec::BitVec;
use index_list::{IndexList, ListIndex};
use itertools::EitherOrBoth::{Both, Left, Right};
use itertools::{kmerge, Itertools};
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Debug, Copy, Clone, PartialEq)]
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
    pub fn from_state_space_by_aps(
        transition_system: &TransitionSystem,
        filter_aps: Option<&Vec<String>>,
    ) -> Self {
        let ap_bitmask = if let Some(aps) = filter_aps {
            transition_system
                .get_label_from_aps(aps)
                .unwrap_or(BitVec::from_elem(transition_system.get_ap().len(), false))
        } else {
            BitVec::from_elem(transition_system.get_ap().len(), true)
        };

        let states_grouped_by_label = transition_system
            .get_states()
            .into_group_map_by(|&state| {
                let mut label = transition_system.get_state_label(state).clone();
                label.and(&ap_bitmask);
                label
            })
            .into_values()
            .collect();

        Self::from_vecs(&states_grouped_by_label)
    }

    fn get_predecessor_states_of_block(
        &self,
        ts: &TransitionSystem,
        block: PartitionBlock,
    ) -> Vec<usize> {
        let start_index = block.start;
        let end_index = block.end;
        let mut predecessors = Vec::new();

        for current_state_idx in start_index..end_index {
            let predecessors_of_current_state =
                ts.get_predecessor_states(self.elements[current_state_idx]);
            predecessors.append(predecessors_of_current_state.to_vec().as_mut());
        }

        predecessors
    }
}

impl<T: Hash + Eq + Clone + Debug + Ord + fmt::Display> Partition<T> {
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

    /// Returns the index of the next block and the index of the moved item
    fn move_item_to_next_block(
        &mut self,
        block_index: ListIndex,
        item_index: usize,
    ) -> (ListIndex, usize) {
        let next_block_index = self.blocks.next_index(block_index);
        let new_item_index = self.blocks.get_mut(block_index).unwrap().end - 1;

        self.elements.swap(item_index, new_item_index);
        self.blocks.get_mut(block_index).unwrap().end -= 1;
        self.blocks.get_mut(next_block_index).unwrap().start -= 1;
        self.block_map
            .insert(self.elements[new_item_index].clone(), next_block_index);

        (next_block_index, new_item_index)
    }

    /// Refine the partition w.r.t. a set `splitter`
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
            let item_index = self.find_in_block(block_index, splitter_item);
            self.move_item_to_next_block(block_index, item_index);
            let block = self.blocks.get(block_index).unwrap();
            if block.start == block.end {
                self.blocks.remove(block_index);
                changed_blocks.remove(&block_index);
            }
        }

        !changed_blocks.is_empty()
    }

    /// Executes one iteration of the ternary refinement algorithm w.r.t. some C and C'.
    ///
    /// # Parameters
    ///
    /// - `pre_c`: Predecessor states of the block C.
    /// - `pre_c_prime_diff_c`: Predecessor states of the block (C'\C)
    ///
    /// # Returns
    /// True, if some block was split; False, otherwise.
    pub fn ternary_refine(&mut self, pre_c: &[T], pre_c_prime_diff_c: &[T]) -> bool {
        let mut changed_blocks = HashSet::new();

        let splitter = pre_c
            .iter()
            .cloned()
            .merge_join_by(pre_c_prime_diff_c.iter().cloned(), |a, b| a.cmp(b))
            .map(|result| {
                match result {
                    Both(state, _) => (state, 1), // B_1 = B \cap Pre(C) \cap Pre(C' \setminus C)
                    Left(state) => (state, 2), // B_2 = (B \cap Pre(C)) \setminus Pre(C' \setminus C)
                    Right(state) => (state, 3), // B_3 = (B \cap Pre(C' \setminus C)) \setminus Pre(C)
                    // the items that are not in the splitter are in B_4 and remain in the same block
                }
            });

        for (state, set) in splitter {
            let &block_index = self
                .block_map
                .get(&state)
                .unwrap_or_else(|| panic!("State {state:?} is not part of the partition."));
            let block_end = self.blocks.get(block_index).unwrap().end;
            if !changed_blocks.contains(&block_index) {
                for _ in 0..3 {
                    // three new blocks
                    self.blocks.insert_after(
                        block_index,
                        PartitionBlock {
                            start: block_end,
                            end: block_end,
                        },
                    );
                }
                changed_blocks.insert(block_index);
            }

            let mut block_index = block_index;
            let mut item_index = self.find_in_block(block_index, &state);
            for _ in 0..set {
                (block_index, item_index) = self.move_item_to_next_block(block_index, item_index);
            }
        }

        // clean up empty blocks
        let mut partition_changed = false;
        for mut block_index in changed_blocks {
            let mut num_empty_blocks = 0;
            for _ in 0..4 {
                let next_block_index = self.blocks.next_index(block_index);
                let block = self.blocks.get(block_index).unwrap();
                if block.start == block.end {
                    self.blocks.remove(block_index);
                    num_empty_blocks += 1;
                }
                block_index = next_block_index;
            }
            if num_empty_blocks != 3 {
                partition_changed = true;
            }
        }

        partition_changed
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

    fn to_sorted_vecs(&self) -> Vec<Vec<T>> {
        self.to_slices()
            .map(|slice| {
                let mut res = slice.to_vec();
                res.sort();
                res
            })
            .collect()
    }

    pub fn to_vecs(&self) -> Vec<Vec<T>> {
        self.to_slices().map(|slice| slice.to_vec()).collect()
    }

    pub fn num_blocks(&self) -> usize {
        self.blocks.len()
    }
}

impl<T: fmt::Display> fmt::Display for Partition<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for block in &self.blocks {
            writeln!(
                f,
                "Block {} starting at {} to {}:",
                self.blocks.index_of(*block),
                block.start,
                block.end
            )?;
            write!(f, "[")?;
            for state in block.start..block.end {
                write!(f, "{}, ", self.elements[state])?;
            }
            writeln!(f, "]")?;
        }

        Ok(())
    }
}

impl<T: Hash + Eq + Clone + Debug + Ord + fmt::Display> PartialEq for Partition<T> {
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
        let ts = "init: 0
        0ab -> 1
        0ab -> 2a
        2a -> 1
        1 -> 3b
        3b -> 2a
        3b -> 3b
        4 -> 4"
            .parse()
            .unwrap();
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

    #[test]
    fn test_ternary_refine() {
        let mut partition = Partition::from_vecs(&vec![vec![1, 2, 3, 4], vec![5]]);
        let pre_c = vec![1, 2];
        let pre_c_prime_diff_c = vec![1, 3];
        let changed = partition.ternary_refine(&pre_c, &pre_c_prime_diff_c);
        assert!(changed);
        assert_eq!(
            sorted_partition(partition.to_vecs()),
            vec![vec![1], vec![2], vec![3], vec![4], vec![5]]
        );
        let changed = partition.ternary_refine(&pre_c, &pre_c_prime_diff_c);
        println!("{}", partition);
        assert!(!changed);
        assert_eq!(
            sorted_partition(partition.to_vecs()),
            vec![vec![1], vec![2], vec![3], vec![4], vec![5]]
        );
    }
}
