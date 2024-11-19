use bit_vec::BitVec;
use serde::Deserialize;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{BufRead, BufReader};

use log::*;

use crate::common::sparse_matrix::SparseMatrix;
use crate::common::transition_system::*;
use crate::parser::property::*;

#[derive(Debug, Deserialize)]
struct InputTs {
    states: Vec<u64>,
    actions: Vec<u64>,
    transitions: Vec<(u64, u64, u64)>,
    initial_states: Vec<u64>,
    labelling: HashMap<u64, Vec<String>>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "lowercase")]
enum InputPropositionalFormula {
    Atom(String),
    Not(Box<InputPropositionalFormula>),
    And(Vec<InputPropositionalFormula>),
    Or(Vec<InputPropositionalFormula>),
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "lowercase")]
enum InputPropertyKind {
    Invariant(InputPropositionalFormula),
    // RegularSafety(FiniteAutomaton),
    // OmegaRegular(FiniteAutomaton)
}

#[derive(Debug, Deserialize)]
struct InputProperties {
    name: String,
    #[serde(flatten)]
    kind: InputPropertyKind,
    #[serde(skip_serializing_if = "is_none")]
    #[allow(dead_code)]
    pub is_true: Option<bool>,
}

#[derive(Debug, Deserialize)]
struct InputJSON {
    #[allow(dead_code)]
    name: String,
    lts: InputTs,
    properties: Vec<InputProperties>,
}

fn parse_file(path: &str) -> InputJSON {
    let file = File::open(path).expect(&format!("Could not open file {}.\n\t", path));
    let reader = BufReader::new(file);
    let mut input_string = "".to_string();

    trace!("Reading lines of input file...");
    reader
        .lines()
        .map(|l| l.expect(&format!("Could not read from file {}.\n\t", path)))
        .for_each(|s| {
            input_string.push('\n');
            input_string.push_str(&s)
        });

    trace!("Done.");
    trace!("Mapping...");

    if let Ok(input) = serde_json::from_str(&*input_string) {
        input
    } else {
        panic!(
            "Could not parse file {}. Are you using the correct format?\n\t",
            path
        );
    }
}

fn build_ts(input: InputTs) -> TransitionSystem {
    if input.states.len() > usize::MAX {
        panic!(
            "Could not build transition system as the number of states ({:?})\
            exceeds the maximum possible number of states ({:?}).\nIf you are
            using a 32bit system the limit can be raised by switching to a 64bit system.",
            input.states.len(),
            usize::MAX
        );
    }
    if input.actions.len() == 0 {
        panic!("Transition systems must have at least one state")
    }

    let last_state = input.states.len() - 1;
    let num_states = last_state + 1;
    trace!("Built state info.");
    let tmatrix = SparseMatrix::from_list_of_entries(
        num_states,
        num_states,
        &input
            .transitions
            .iter()
            .map(|(s1, _ac, s2)| (*s1 as usize, *s2 as usize, true))
            .collect::<Vec<_>>(),
    );
    trace!("Built transition matrix.");
    let reverse_tmatrix = SparseMatrix::from_list_of_entries(
        num_states,
        num_states,
        &input
            .transitions
            .iter()
            .map(|(s1, _ac, s2)| (*s2 as usize, *s1 as usize, true))
            .collect::<Vec<_>>(),
    );

    trace!("Built reverse transition matrix.");
    let initial_states = input
        .initial_states
        .iter()
        .map(|&i| i as usize)
        .collect::<Vec<_>>();
    trace!("Built initial state info.");

    let atomic_props: Vec<_> = input
        .labelling
        .values()
        .flatten()
        .collect::<HashSet<_>>()
        .into_iter()
        .cloned()
        .collect();

    trace!("Built atomic propositions.");

    let get_state_label = |state: usize| -> BitVec {
        static EMPTY_VEC: Vec<String> = vec![];
        let labels = input.labelling.get(&(state as u64)).unwrap_or(&EMPTY_VEC);

        let mut bv = BitVec::from_elem(atomic_props.len(), false);
        for label in labels {
            let i = atomic_props
                .iter()
                .position(|a| a == label)
                .expect(&format!("State {:?} has no label", state));
            bv.set(i, true);
        }
        bv
    };

    let state_labels: Vec<BitVec> = (0..num_states).map(get_state_label).collect();

    trace!("Built state labels.");
    let label_states = HashMap::from_iter((0..atomic_props.len() + 1).map(|label_subset| {
        let label = BitVec::from_bytes(&label_subset.to_ne_bytes());

        let states = (0..num_states)
            .filter(|state| state_labels[*state] == label)
            .collect::<Vec<_>>();

        (label, states)
    }));
    trace!("Built reverse state label info.");

    TransitionSystem::new(
        tmatrix,
        reverse_tmatrix,
        last_state,
        initial_states,
        state_labels,
        label_states,
        atomic_props,
    )
}

fn map_formula(form: &InputPropositionalFormula) -> FormulaTreeNode<String> {
    match form {
        InputPropositionalFormula::Atom(ref f) => {
            FormulaTreeNode::new(None, None, Some(f.to_string()), FormulaTreeNodeType::ATOMIC)
        }
        InputPropositionalFormula::Not(ref f) => FormulaTreeNode::new(
            Some(Box::from(map_formula(f))),
            None,
            None,
            FormulaTreeNodeType::NOT,
        ),
        InputPropositionalFormula::And(ref f) => {
            if f.len() < 2 {
                panic!("Not enough elements in formula")
            } else if f.len() == 2 {
                FormulaTreeNode::new(
                    Some(Box::from(map_formula(f.first().unwrap()))),
                    Some(Box::from(map_formula(f.last().unwrap()))),
                    None,
                    FormulaTreeNodeType::AND,
                )
            } else {
                FormulaTreeNode::new(
                    Some(Box::from(map_formula(f.first().unwrap()))),
                    Some(Box::from(map_formula(&InputPropositionalFormula::And(
                        f[1..].to_vec(),
                    )))),
                    None,
                    FormulaTreeNodeType::AND,
                )
            }
        }
        InputPropositionalFormula::Or(ref f) => {
            if f.len() < 2 {
                panic!("Not enough elements in formula")
            } else if f.len() == 2 {
                FormulaTreeNode::new(
                    Some(Box::from(map_formula(f.first().unwrap()))),
                    Some(Box::from(map_formula(f.last().unwrap()))),
                    None,
                    FormulaTreeNodeType::OR,
                )
            } else {
                FormulaTreeNode::new(
                    Some(Box::from(map_formula(f.first().unwrap()))),
                    Some(Box::from(map_formula(&InputPropositionalFormula::Or(
                        f[1..].to_vec(),
                    )))),
                    None,
                    FormulaTreeNodeType::OR,
                )
            }
        }
    }
}

fn build_formula(props: Vec<InputProperties>) -> (Vec<Property<String>>, Vec<Option<bool>>) {
    props
        .iter()
        .map(|p| {
            trace!("Found property {:?} of kind {:?}.", p.name, p.kind);
            (
                Property::new(
                    (*p).name.clone(),
                    // TODO currently we only support invariants; later this has to be extended
                    match p.kind {
                        InputPropertyKind::Invariant(_) => PropertyType::Invariant,
                    },
                    match &p.kind {
                        InputPropertyKind::Invariant(form) => map_formula(form),
                    },
                ),
                p.is_true,
            )
        })
        .collect()
}

/// Takes a filepath to a gntmc file and parses the content into a Transition System
/// and a vector of properties, respectively.
///
/// # Parameters
/// * `path` - The path to the .gntmc file that shall be parsed
///
/// # Returns
/// A tuple consisting of the transition system and a vector of properties.
///
/// # Panics
/// If an error during the parsing of the file or the mapping afterward occurs.
pub fn parse_gntmc_file(
    path: &str,
) -> (TransitionSystem, Vec<Property<String>>, Vec<Option<bool>>) {
    if !path.ends_with(".gntmc") {
        panic!("Entered file path does not point to a gntmc file.");
    }

    debug!("Parsing file: {:?}...", path);
    let input = parse_file(path);
    debug!("Done.");
    debug!("Building TS...");
    let ts = build_ts(input.lts);
    debug!("Done.");
    debug!("Parsing Properties...");
    let properties = build_formula(input.properties);
    debug!("Done. Found {:?} properties in total.", properties.0.len());

    (ts, properties.0, properties.1)
}
