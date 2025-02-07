use crate::common::transition_system::TransitionSystem;
use crate::bisimulation::partition::Partition;
use array_tool::vec::*;
use itertools::Itertools;

// pub fn advanced_refinement(transition_system: &TransitionSystem) -> Partition<usize> {
//     let all_ts_states: Vec<usize> = transition_system.get_states();
//     let mut old_partition = Partition::from_vecs(&vec![all_ts_states]); // can probably be deleted
//     let mut current_partition = Partition::from_state_space_by_aps(transition_system);
//     current_partition.refine(&*(0..transition_system.get_num_states()).collect::<Vec<_>>());
// 
//     loop {
//         let splitter_block = vec![];
//         let parent_splitter_superblock = vec![];
// 
//         let changed = current_partition.ternary_refine(splitter_block, parent_splitter_superblock.uniq(splitter_block));
// 
//         if changed.is_none() {
//             break;
//         }
//     }
// 
//     current_partition
// }

