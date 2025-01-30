#![allow(dead_code)]

use itertools::kmerge;
use itertools::Itertools;

use crate::common::partition::Partition;
use crate::common::transition_system::TransitionSystem;

fn get_initial_partition(ts: &TransitionSystem, aps: &[String]) -> Vec<Vec<usize>> {
    let ap_bitmask = ts.get_label_from_aps(aps);
    ts.get_states()
        .into_group_map_by(|&state| {
            let mut label = ts.get_state_label(state).clone();
            label.and(&ap_bitmask);
            label
        })
        .into_values()
        .collect()
}

fn get_predecessors(ts: &TransitionSystem, states: &[usize], buffer: &mut Vec<usize>) {
    buffer.clear();
    buffer.extend(
        kmerge(
            states
                .iter()
                .map(|&state| ts.get_predecessor_states(state).iter()),
        )
        .dedup(),
    );
}

fn simple_selection_strategy(ts: &TransitionSystem, aps: &[String]) -> Vec<Vec<usize>> {
    let mut pi = Partition::from_vecs(&get_initial_partition(ts, aps));
    let mut splitter_buffer = Vec::with_capacity(ts.get_num_states());

    'outer: loop {
        // we have to make a copy here, because we mutate pi in the loop. to avoid this, we could
        // check if p_i is a splitter and give up the reference to pi if it is, but i think that
        // the overhead of this check would be bigger than the overhead of copying
        let parts = pi.to_vecs();
        for p_i in &parts {
            get_predecessors(ts, p_i, &mut splitter_buffer);
            let changed = pi.refine(&splitter_buffer);
            if changed {
                continue 'outer;
            }
        }
        break;
    }

    pi.to_vecs()
}

pub fn reduce_ts(_ts: &TransitionSystem) -> TransitionSystem {
    Partition::<usize>::from_vecs(&Vec::new()).ternary_refine(&[], &[]);
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sorted_partition(mut partition: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
        partition.iter_mut().for_each(|class| class.sort());
        partition.sort();
        partition
    }

    fn aps(str: &str) -> Vec<String> {
        str.chars().map(String::from).collect()
    }

    fn test_partitioning(partitioning_method: fn(&TransitionSystem, &[String]) -> Vec<Vec<usize>>) {
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
        let partition = partitioning_method(&ts, &aps("ab"));
        let expected_partition = vec![
            vec![0],
            vec![1],
            vec![6],
            vec![9],
            vec![3],
            vec![8],
            vec![2, 4, 10],
            vec![7],
            vec![5, 11],
        ];
        assert_eq!(
            sorted_partition(partition),
            sorted_partition(expected_partition)
        );
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

        let partition = get_initial_partition(&ts, &aps("ab"));
        assert_eq!(
            sorted_partition(partition),
            vec![vec![0, 3], vec![1], vec![2]]
        );

        let ts = "init: 0 3
        0ac -> 1a
        1a -> 2ad
        2ad -> 3b
        3b -> 4bz"
            .parse()
            .unwrap();

        let partition = get_initial_partition(&ts, &aps("ab"));
        assert_eq!(
            sorted_partition(partition),
            vec![vec![0, 1, 2,], vec![3, 4],]
        );
    }

    #[test]
    fn test_simple_selection_strategy() {
        test_partitioning(simple_selection_strategy);
    }
}
