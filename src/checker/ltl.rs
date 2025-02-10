use crate::checker::checker::Options;
use crate::checker::regular_safety_and_omega_property::regular_safety_and_omega_checking;
use crate::common::transition_system::TransitionSystem;
use crate::parser::automaton::{FiniteAutomaton, LtlGnba};
use crate::parser::property::{Property, PropertyType};

pub fn ltl_checking(
    transition_system: &TransitionSystem,
    property: &Property<String>,
    options: &Options,
) -> Result<bool, (Vec<Vec<String>>, Vec<usize>)> {
    let aps = property.get_aps();
    let mut negated_property = property.clone();
    negated_property.negate();
    let gnba = LtlGnba::from_ltl_property(&negated_property);
    let nba = FiniteAutomaton::from_gnba(gnba);
    let property_name = property.name.clone();
    let omega_regular_property = Property::new(property_name, PropertyType::OmegaRegular(nba), aps);
    regular_safety_and_omega_checking(transition_system, &omega_regular_property, options)
}
