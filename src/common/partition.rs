#![allow(dead_code)]

use index_list::{IndexList, ListIndex};
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Debug, Copy, Clone)]
struct PartitionBlock {
    start: usize,
    end: usize,
}

#[derive(Debug)]
struct Partition<T> {
    elements: Vec<T>,
    blocks: IndexList<PartitionBlock>,
    block_map: HashMap<T, ListIndex>,
}

impl<T: Hash + Eq + Clone + Debug> Partition<T> {
    ///! Create a partition from a list of vectors
    pub fn from_vecs(vecs: &[Vec<T>]) -> Self {
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

    ///! Return the partition as an iterator over it's sets
    pub fn to_slices(&self) -> impl Iterator<Item = &[T]> {
        self.blocks
            .iter()
            .map(|block| &self.elements[block.start..block.end])
    }

    fn find_in_block(&self, block_index: ListIndex, item: &T) -> usize {
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

    ///! Refine the partition wrt a set `splitter`
    ///! Returns `true` if the partition has changed
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

    fn ternary_refine(&mut self, splitter_a: &[T], splitter_b: &[T]) -> bool {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_partition() {
        let partition = Partition::from_vecs(&[vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]]);

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
}
