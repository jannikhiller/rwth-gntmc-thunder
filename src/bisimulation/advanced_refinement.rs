use std::collections::{VecDeque};
use array_tool::vec::*;
use crate::common::transition_system::TransitionSystem;
use crate::bisimulation::partition::{Partition};
use crate::common::vec_helper::setminus;

fn get_predecessor_states_of_block(transition_system: &TransitionSystem, block: &Vec<usize>) -> Vec<usize> {
    let mut result = Vec::new();

    for state in block {
        for pred in transition_system.get_predecessor_states(*state) {
            result.push(*pred);
        }
    }

    result.unique()
}

pub fn advanced_refinement(transition_system: &TransitionSystem, aps: Option<&Vec<String>>) -> Partition<usize> {
    let mut queue = VecDeque::new();
    let mut c_prime = transition_system.get_states().collect::<Vec<_>>();
    let mut current_partition = Partition::from_state_space_by_aps(transition_system, aps);
    current_partition.refine(&c_prime);

    loop {
        let mut c = vec![];
        for c_candidate in current_partition.to_slices() {
            if c_candidate.len() > c_prime.len() / 2 {
                continue;
            }

            if c_candidate.iter().all(|elem| c_prime.contains(elem)) {
                c = c_candidate.to_vec();
                break;
            }
        }

        let c_prime_diff_c = setminus(&c_prime, &c);


        let pre_c = get_predecessor_states_of_block(transition_system, &c);
        let pre_c_prime = get_predecessor_states_of_block(transition_system, &c_prime);
        let pre_c_prime_diff_c = get_predecessor_states_of_block(transition_system, &c_prime_diff_c);

        current_partition.ternary_refine(&pre_c, &pre_c_prime, &pre_c_prime_diff_c);

        if !c.is_empty() {
            queue.push_back(c);
        }
        if !c_prime_diff_c.is_empty() {
            queue.push_back(c_prime_diff_c);
        }

        if current_partition.num_blocks() == queue.len() {
            break;
        } else { 
            c_prime = queue.pop_front().unwrap();
        }
    }

    current_partition
}


#[cfg(test)]
mod tests {
    use crate::bisimulation::advanced_refinement::advanced_refinement;
    use crate::bisimulation::partition::Partition;
    use crate::common::transition_system::TransitionSystem;

    fn sorted_partition(mut partition: Vec<Vec<usize>>) -> Vec<Vec<usize>> {
        partition.iter_mut().for_each(|class| class.sort());
        partition.sort();
        partition
    }

    fn test_partitioning(partitioning_method: fn(&TransitionSystem, Option<&Vec<String>>) -> Partition<usize>) {
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
    fn test_advanced_selection_strategy() {
        test_partitioning(advanced_refinement);
    }
}