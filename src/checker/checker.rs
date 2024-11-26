use thunder::checker::invariant::bfs_invariant_checking;
use crate::common::transition_system::TransitionSystem;
use crate::parser::property::{Property, PropertyType};
use crate::checker::regular_safety_and_omega_property::regular_safety_and_omega_checking;

pub fn check(transition_system: &TransitionSystem,
             property: &Property<String>,
            ) -> Result<bool, (Vec<Vec<String>>, Vec<usize>)>{
    match property.property_type {
        PropertyType::Invariant(_) => {bfs_invariant_checking(transition_system,property)}
        PropertyType::Persistence(_) => {}
        PropertyType::RegularSafety(_) => {regular_safety_checking(transition_system,property,false)}
        PropertyType::OmegaRegular(_) => {regular_safety_and_omega_checking(transition_system,property,true)}
    }
}