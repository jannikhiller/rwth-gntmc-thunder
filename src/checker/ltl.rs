use crate::checker::regular_safety_and_omega_property::regular_safety_and_omega_checking;
use crate::checker::Options;
use crate::common::transition_system::TransitionSystem;
use crate::property::automaton::{FiniteAutomaton, LtlGnba};
use crate::property::{Property, PropertyType};

/// LTL-checks the given property on the given transition system.
///
/// # Parameters
///
/// - `transition_system`: The given transition system for which the property gets checked.
/// - `property`: The given property, which gets checked.
/// - `options`: Given options, how the ltl checking should be done.
///
/// # Returns
///  if the given property holds, if not a counter example will be given.
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
