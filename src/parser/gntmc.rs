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
    #[serde(skip_serializing_if = "Option::is_none")]
    pub is_true: Option<bool>,
}

#[derive(Debug, Deserialize)]
struct InputJSON {
    name: String,
    lts: InputTs,
    properties: Vec<InputProperties>,
}

fn parse_file(path: &str) -> InputJSON {
    let file = File::open(path).expect(&format!("Could not open file {}.\n\t", path));
    let reader = BufReader::new(file);
    let mut input_string = "".to_string();

    reader
        .lines()
        .map(|l| l.expect(&format!("Could not read from file {}.\n\t", path)))
        .for_each(|s| {
            input_string.push('\n');
            input_string.push_str(&s)
        });

    let input: InputJSON = serde_json::from_str(&*input_string).expect(&format!(
        "Could not parse file {}. Are you using the correct format?\n\t",
        path
    ));

    input
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

    let tmatrix = SparseMatrix::from_list_of_entries(
        num_states,
        num_states,
        &input
            .transitions
            .iter()
            .map(|(s1, _ac, s2)| (*s1 as usize, *s2 as usize, true))
            .collect::<Vec<_>>(),
    );
    let reverse_tmatrix = SparseMatrix::from_list_of_entries(
        num_states,
        num_states,
        &input
            .transitions
            .iter()
            .map(|(s1, _ac, s2)| (*s2 as usize, *s1 as usize, true))
            .collect::<Vec<_>>(),
    );
    let initial_states = input
        .initial_states
        .iter()
        .map(|&i| i as usize)
        .collect::<Vec<_>>();
    let atomic_props = input
        .labelling
        .values()
        .cloned()
        .reduce(|mut acc, mut s| {
            acc.append(&mut s);
            acc
        })
        .unwrap()
        .iter()
        .collect::<HashSet<_>>()
        .iter()
        .map(|s| s.clone().clone())
        .collect::<Vec<_>>();
    let state_labels: Vec<BitVec> = (0..num_states)
        .map(|state| {
            let mut bv = BitVec::from_elem(atomic_props.len(), false);
            let lifehack = Vec::new();
            let labels = input.labelling.get(&(state as u64)).unwrap_or(&lifehack);

            labels
                .iter()
                .map(|s| {
                    atomic_props
                        .iter()
                        .position(|a| *a == *s)
                        .expect(&format!("State {:?} has no label", s))
                })
                .for_each(|i| bv.set(i, true));

            bv
        })
        .collect();
    let label_states = HashMap::from_iter((0..atomic_props.len() + 1).map(|label_subset| {
        let label = BitVec::from_bytes(&label_subset.to_ne_bytes());

        let states = (0..num_states)
            .filter(|state| state_labels[*state] == label)
            .collect::<Vec<_>>();

        (label, states)
    }));

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
        InputPropositionalFormula::Atom(ref f) => FormulaTreeNode::new(
            Option::None,
            Option::None,
            Option::Some(f.to_string()),
            FormulaTreeNodeType::ATOMIC,
        ),
        InputPropositionalFormula::Not(ref f) => FormulaTreeNode::new(
            Option::Some(Box::from(map_formula(f))),
            Option::None,
            Option::None,
            FormulaTreeNodeType::NOT,
        ),
        InputPropositionalFormula::And(ref f) => {
            if f.len() < 2 {
                panic!("Not enough elements in formula")
            } else if f.len() == 2 {
                FormulaTreeNode::new(
                    Option::Some(Box::from(map_formula(f.first().unwrap()))),
                    Option::Some(Box::from(map_formula(f.last().unwrap()))),
                    Option::None,
                    FormulaTreeNodeType::AND,
                )
            } else {
                FormulaTreeNode::new(
                    Option::Some(Box::from(map_formula(f.first().unwrap()))),
                    Option::Some(Box::from(map_formula(&InputPropositionalFormula::And(
                        f[1..].to_vec(),
                    )))),
                    Option::None,
                    FormulaTreeNodeType::AND,
                )
            }
        }
        InputPropositionalFormula::Or(ref f) => {
            if f.len() < 2 {
                panic!("Not enough elements in formula")
            } else if f.len() == 2 {
                FormulaTreeNode::new(
                    Option::Some(Box::from(map_formula(f.first().unwrap()))),
                    Option::Some(Box::from(map_formula(f.last().unwrap()))),
                    Option::None,
                    FormulaTreeNodeType::OR,
                )
            } else {
                FormulaTreeNode::new(
                    Option::Some(Box::from(map_formula(f.first().unwrap()))),
                    Option::Some(Box::from(map_formula(&InputPropositionalFormula::Or(
                        f[1..].to_vec(),
                    )))),
                    Option::None,
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
            return (Property::new(
                (*p).name.clone(),
                // TODO currently we only support invariants; later this has to be extended
                match p.kind {
                    InputPropertyKind::Invariant(_) => PropertyType::Invariant,
                    _ => panic!("Unsupported property type: {:?}", p.kind)
                },
                match &p.kind {
                    InputPropertyKind::Invariant(form) => map_formula(form)
                }), p.is_true)
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
pub fn parse_gntmc_file(path: &str) -> (TransitionSystem, Vec<Property<String>>, Vec<Option<bool>>) {
    if !path.ends_with(".gntmc") {
        panic!("Entered file path does not point to a gntmc file.");
    }

    let input = parse_file(path);
    let ts = build_ts(input.lts);
    let properties = build_formula(input.properties);

    (ts, properties.0, properties.1)
}
