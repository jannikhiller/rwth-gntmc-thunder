use crate::bisimulation::partition::{get_predecessors, Partition};
use crate::common::transition_system::TransitionSystem;
use crate::common::vec_helper::setminus;
use std::collections::VecDeque;
use log::{debug, trace};

/// Implements the advanced refinement algorithm by Paige & Tarjan from the lecture.
/// Note that the working_queue represents the old partition.
///
/// # Parameters
///
/// - `transition_system`: The given transition system for which the quotient shall be computed.
/// - `aps`: The atomic propositions to be considered during computation of the quotient.
///
/// # Returns
/// A partition, which represents the state space of the quotient.
pub fn advanced_refinement(
    transition_system: &TransitionSystem,
    aps: Option<&Vec<String>>,
) -> Partition<usize> {
    let mut working_queue = VecDeque::new();

    // initial refinement
    let mut c_prime = transition_system.get_states().collect::<Vec<_>>();
    let mut current_partition = Partition::from_state_space_by_aps(transition_system, aps);
    current_partition.refine(&c_prime);

    // create buffers for Pre(C) and Pre(C'\C)
    let mut pre_c = Vec::with_capacity(transition_system.get_num_states());
    let mut pre_c_prime_diff_c = Vec::with_capacity(transition_system.get_num_states());

    let mut iterations = 0;
    loop {
        // search for a fitting C'
        while c_prime.len() < 2 {
            trace!("C' candidate has size 1 => skip to next...");
            working_queue.push_back(c_prime);
            c_prime = working_queue.pop_front().unwrap();
        }

        // choose a C s.t. C \subseteq C' and C <= C'/2
        let mut c = Vec::new();
        let mut found_suitable_candidate = false;
        for c_candidate in current_partition.to_slices() {
            if c_candidate.len() > c_prime.len() / 2 {
                trace!("C candidate is larger than |C'|/2 => skip to next...");
                continue;
            }
            if c_candidate.iter().all(|elem| c_prime.contains(elem)) {
                c = c_candidate.to_vec();
                found_suitable_candidate = true;
                break;
            }
        }

        if !found_suitable_candidate {
            trace!("No suitable candidate found for C...");
            let temp = c_prime.clone();
            working_queue.push_back(c_prime);
            c_prime = working_queue.pop_front().unwrap();
            if c_prime == temp {
                debug!("No candidate found for C, and there is only one element on the queue! Refinement finished as there is no splitter.");
                break;
            }
            continue;
        }

        let c_prime_diff_c = setminus(&c_prime, &c);

        get_predecessors(transition_system, &c, &mut pre_c);
        get_predecessors(transition_system, &c_prime_diff_c, &mut pre_c_prime_diff_c);

        trace!("Calling ternary refinement for C ({:?}) and C'({:?})...", c, c_prime);
        current_partition.ternary_refine(&pre_c, &pre_c_prime_diff_c);
        iterations += 1;

        if !c.is_empty() {
            working_queue.push_back(c);
        }
        if !c_prime_diff_c.is_empty() {
            // push (C' \ C) to the front as a heuristic, which seems to work quite well
            working_queue.push_front(c_prime_diff_c);
        }

        if current_partition.num_blocks() == working_queue.len() {
            break;
        } else {
            c_prime = working_queue.pop_front().unwrap();
        }
    }

    debug!("Finished advanced refinement in {} iterations!", iterations);

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
    fn test_advanced_selection_strategy() {
        test_partitioning(advanced_refinement);
    }
}
