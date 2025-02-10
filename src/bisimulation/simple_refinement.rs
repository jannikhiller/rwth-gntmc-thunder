use crate::bisimulation::partition::*;
use crate::common::transition_system::TransitionSystem;

pub fn simple_selection_strategy(
    ts: &TransitionSystem,
    aps: Option<&Vec<String>>,
) -> Partition<usize> {
    let mut pi = Partition::from_state_space_by_aps(ts, aps);
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

    pi
}

#[cfg(test)]
mod tests {
    use crate::bisimulation::partition::Partition;
    use crate::bisimulation::simple_refinement::simple_selection_strategy;
    use crate::common::transition_system::TransitionSystem;

    fn sorted_partition(mut partition: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
        partition.iter_mut().for_each(|class| class.sort());
        partition.sort();
        partition
    }

    fn test_partitioning(
        partitioning_method: fn(&TransitionSystem, Option<&Vec<String>>) -> Partition<usize>,
    ) {
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
        let partition = partitioning_method(&ts, Option::from(&aps("ab")));
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
            sorted_partition(partition.to_vecs()),
            sorted_partition(expected_partition)
        );
    }

    fn aps(str: &str) -> Vec<String> {
        str.chars().map(String::from).collect()
    }

    #[test]
    fn test_simple_selection_strategy() {
        test_partitioning(simple_selection_strategy);
    }
}
