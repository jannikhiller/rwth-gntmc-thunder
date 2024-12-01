use std::collections::HashMap;
use bit_vec::BitVec;
use crate::common::transition_system::TransitionSystem;

// helper function to reconstruct the path
pub fn reconstruct_path(
    ts: &TransitionSystem,
    came_from: &HashMap<usize, usize>,
    end_state: usize,
) -> (Vec<Vec<String>>, Vec<usize>) {
    let mut path = Vec::new();
    let mut states = Vec::new();
    let mut current = end_state;

    // push label of last state
    path.push(bit_vec_to_ap_strings(ts, ts.get_state_label(current)));
    states.push(current);

    // reconstruct path backwards
    while let Some(&prev) = came_from.get(&current) {
        path.push(bit_vec_to_ap_strings(ts, ts.get_state_label(prev)));
        states.push(prev);
        current = prev;
    }

    // reverse path, as we have built it up from behind
    path.reverse();
    states.reverse();

    (path, states)
}
/// Returns a string vec for the given bit vec.
///
/// # Parameters
/// - `label`: The BitVec which gets translated into string vec.
///
/// # Returns
/// A Vec<String> for the given AP-BitVec.
pub fn bit_vec_to_ap_strings(transition_system: &TransitionSystem, label: &BitVec) -> Vec<String> {
    // get all ap names
    let ap_names = transition_system.get_ap();

    label
        .iter()
        .enumerate() // add index to bit
        .filter(|(_, bit)| *bit) // only true bits
        .map(|(index, _)| ap_names[index].clone()) // get according AP-String
        .collect()
}

