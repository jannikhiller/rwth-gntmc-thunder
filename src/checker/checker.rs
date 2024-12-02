use crate::checker::invariant::bfs_invariant_checking;
use crate::common::transition_system::TransitionSystem;
use crate::parser::property::{Property, PropertyType};
use crate::checker::regular_safety_and_omega_property::regular_safety_and_omega_checking;
use crate::checker::scc::{persistence_checking_with_scc};

/// Wrapper function which acts as an interface to correctly handle checking different types of
/// properties on a given transition system.
///
/// # Parameters
///
/// - `transition_system`: The given transition system which gets checked.
/// - `property`: The property to be checked on the given transition system.
///
/// # Returns
/// A Result with `Ok` if the property is fulfilled and Err with a path and a trace otherwise.
pub fn check(transition_system: &TransitionSystem,
             property: &Property<String>,
            ) -> Result<bool, (Vec<Vec<String>>, Vec<usize>)>{
    match property.property_type {
        PropertyType::Invariant(_) => {bfs_invariant_checking(transition_system,property)}
        PropertyType::Persistence(_) => {persistence_checking_with_scc(transition_system, property)}
        PropertyType::RegularSafety(_) => {regular_safety_and_omega_checking(transition_system,property)}
        PropertyType::OmegaRegular(_) => {regular_safety_and_omega_checking(transition_system,property)}
    }
}