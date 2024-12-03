use crate::common::transition_system::TransitionSystem;
use bit_vec::BitVec;

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
