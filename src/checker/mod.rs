mod ctl;
pub mod helper;
pub mod invariant;
mod ltl;
mod nested_dfs;
mod new_nested_dfs;
mod regular_safety_and_omega_property;
mod scc;
mod scc_couvreur;

use crate::common::transition_system::TransitionSystem;
use crate::property::{Property, PropertyType};
use ctl::ctl_checking;
use invariant::bfs_invariant_checking;
use ltl::ltl_checking;
use nested_dfs::persistence_checking_with_nested_dfs;
use regular_safety_and_omega_property::regular_safety_and_omega_checking;
use scc::persistence_checking_with_scc;
use std::fmt;
use std::fmt::Formatter;

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
pub fn check(
    transition_system: &TransitionSystem,
    property: &Property<String>,
    options: &Options,
) -> Result<bool, (Vec<Vec<String>>, Vec<usize>)> {
    match property.property_type {
        PropertyType::Invariant(_) => bfs_invariant_checking(transition_system, property),
        PropertyType::Persistence(_) => {
            // differentiate according to the persistence algorithm set in the options
            match options.persistence_algorithm {
                PersistenceCheckingAlgorithm::Scc => {
                    persistence_checking_with_scc(transition_system, property, None)
                }
                PersistenceCheckingAlgorithm::NestedDfs => {
                    persistence_checking_with_nested_dfs(transition_system, property, None)
                }
                PersistenceCheckingAlgorithm::NewNestedDfs => {
                    new_nested_dfs::persistence_checking_with_nested_dfs(
                        transition_system,
                        property,
                        None,
                    )
                }
                PersistenceCheckingAlgorithm::SccCouvreur => {
                    scc_couvreur::persistence_checking_with_couvreur_scc(
                        transition_system,
                        property,
                        None,
                    )
                }
            }
        }
        PropertyType::RegularSafety(_) | PropertyType::OmegaRegular(_) => {
            regular_safety_and_omega_checking(transition_system, property, options)
        }
        PropertyType::Ltl(_) => ltl_checking(transition_system, property, options),
        PropertyType::Ctl(_) => ctl_checking(transition_system, property),
    }
}

pub struct Options {
    pub persistence_algorithm: PersistenceCheckingAlgorithm,
    pub quotienting_algorithm: QuotientingAlgorithm,
    pub visualize_cex: Option<String>,
}

impl Default for Options {
    fn default() -> Self {
        Self::new()
    }
}

impl Options {
    pub fn new() -> Self {
        // default algorithm is set here
        Options {
            persistence_algorithm: PersistenceCheckingAlgorithm::NestedDfs,
            quotienting_algorithm: QuotientingAlgorithm::Without,
            visualize_cex: None,
        }
    }

    pub fn set_persistence_algorithm(
        &mut self,
        persistence_algorithm: PersistenceCheckingAlgorithm,
    ) {
        self.persistence_algorithm = persistence_algorithm
    }

    pub fn set_quotienting_algorithm(&mut self, quotienting_algorithm: QuotientingAlgorithm) {
        self.quotienting_algorithm = quotienting_algorithm
    }

    pub fn set_visualize_cex(&mut self, visualize_cex: Option<String>) {
        self.visualize_cex = visualize_cex;
    }
}

#[derive(clap::ValueEnum, Default, Debug, Clone)]
pub enum PersistenceCheckingAlgorithm {
    Scc,
    #[default]
    NestedDfs,
    NewNestedDfs,
    SccCouvreur,
}

#[derive(clap::ValueEnum, Default, Debug, Clone, PartialEq)]
pub enum QuotientingAlgorithm {
    AdvancedRefinement,
    SimpleRefinement,
    #[default]
    Without,
}

impl fmt::Display for QuotientingAlgorithm {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            QuotientingAlgorithm::AdvancedRefinement => write!(f, "advanced refinement"),
            QuotientingAlgorithm::SimpleRefinement => write!(f, "simple refinement"),
            QuotientingAlgorithm::Without => write!(f, "without quotienting"),
        }
    }
}
