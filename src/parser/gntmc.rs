use bit_vec::BitVec;
use itertools::Itertools;
use log::*;
use serde::Deserialize;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::BufReader;

use crate::common::sparse_matrix::SparseMatrix;
use crate::common::transition_system::*;
use crate::property::automaton::{AcceptanceType, FiniteAutomaton};
use crate::property::property::*;

#[derive(Debug, Deserialize)]
struct GntmcTransitionSystem {
    states: Vec<u64>,
    actions: Vec<u64>,
    transitions: Vec<(u64, u64, u64)>,
    initial_states: Vec<u64>,
    labelling: HashMap<u64, Vec<String>>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "lowercase")]
enum GntmcPropositionalFormula {
    Atom(String),
    Not(Box<GntmcPropositionalFormula>),
    And(Vec<GntmcPropositionalFormula>),
    Or(Vec<GntmcPropositionalFormula>),
    True,
}

impl GntmcPropositionalFormula {
    fn translate(&self, aps: &mut Vec<String>) -> FormulaTreeNode<String> {
        match self {
            GntmcPropositionalFormula::Atom(ref f) => {
                if !aps.contains(&f.to_string()) {
                    aps.push(f.to_string());
                }
                FormulaTreeNode::new(None, None, Some(f.to_string()), FormulaTreeNodeType::Atomic)
            }
            GntmcPropositionalFormula::Not(ref f) => FormulaTreeNode::new(
                Some(Box::from(f.translate(aps))),
                None,
                None,
                FormulaTreeNodeType::Not,
            ),
            GntmcPropositionalFormula::And(ref f) => match f.len() {
                ..=1 => panic!("Not enough elements in formula"),
                2 => FormulaTreeNode::new(
                    Some(Box::from(f.first().unwrap().translate(aps))),
                    Some(Box::from(f.last().unwrap().translate(aps))),
                    None,
                    FormulaTreeNodeType::And,
                ),
                3.. => FormulaTreeNode::new(
                    Some(Box::from(f.first().unwrap().translate(aps))),
                    Some(Box::from(
                        GntmcPropositionalFormula::And(f[1..].to_vec()).translate(aps),
                    )),
                    None,
                    FormulaTreeNodeType::And,
                ),
            },
            GntmcPropositionalFormula::Or(ref f) => match f.len() {
                ..=1 => panic!("Not enough elements in formula"),
                2 => FormulaTreeNode::new(
                    Some(Box::from(f.first().unwrap().translate(aps))),
                    Some(Box::from(f.last().unwrap().translate(aps))),
                    None,
                    FormulaTreeNodeType::Or,
                ),
                3.. => FormulaTreeNode::new(
                    Some(Box::from(f.first().unwrap().translate(aps))),
                    Some(Box::from(
                        GntmcPropositionalFormula::Or(f[1..].to_vec()).translate(aps),
                    )),
                    None,
                    FormulaTreeNodeType::Or,
                ),
            },
            GntmcPropositionalFormula::True => {
                FormulaTreeNode::new(None, None, None, FormulaTreeNodeType::True)
            }
        }
    }
}

/// The acceptance condition may be either that of an NFA or a Buchi automaton.
#[derive(Debug, Deserialize)]
#[serde(rename_all = "lowercase")]
enum Acceptance {
    /// An NFA accepts once it reaches a final state.
    Nfa,
    /// A Buchi automaton accepts if accepting states are reached infinitely
    /// often.
    Buchi,
}

/// An edge in a finite automaton represents a set of transitions.
///
/// This corresponds to an edge drawn in the graphical representation in the
/// model checking lecture, e.g. on slide 27 of lecture 4, where each edge
/// represents a set of transitions in the NFA.
#[derive(Debug, Deserialize)]
struct Edge {
    start: usize,
    /// We represent the set of transitions as a propositional formula. It
    /// represents the sets of sets of atomic propositions: those sets of atomic
    /// propositions which correspond to true assignments of the formula.
    actions: GntmcPropositionalFormula,
    destination: usize,
}

/// A struct to represent a finite automaton, which can either be an NFA or a
/// Buchi automaton, for model checking labelled transition systems.
#[derive(Debug, Deserialize)]
struct GntmcFiniteAutomaton {
    /// The type of the finite automaton (NFA or Buchi).
    acceptance: Acceptance,
    /// The states of the automaton.
    states: Vec<usize>,
    /// The alphabet of the automaton is given by the powerset of atomic propositions.
    #[allow(dead_code)]
    atomic_propositions: Vec<String>,
    /// We store the transitions of finite automata as a list of "edges", which
    /// represent a set of transitions each.
    edges: Vec<Edge>,
    /// The initial states of the automaton.
    initial_states: Vec<usize>,
    /// The accepting states of the automaton.
    accepting_states: Vec<usize>,
}

impl GntmcFiniteAutomaton {
    fn translate(&self, aps: &mut Vec<String>) -> FiniteAutomaton<String> {
        for ap in self.atomic_propositions.clone() {
            if !aps.contains(&ap) {
                aps.push(ap.to_string());
            }
        }
        let acceptance = match self.acceptance {
            Acceptance::Nfa => AcceptanceType::Nfa,
            Acceptance::Buchi => AcceptanceType::Buchi,
        };
        let mut transitions: Vec<_> = self
            .edges
            .iter()
            .map(|e| (e.start, e.destination, e.actions.translate(&mut vec![]))) //the argument will not be used here
            .collect();

        transitions.sort_by_key(|(src, _, _)| *src);
        let transitions: Vec<_> = transitions
            .into_iter()
            .chunk_by(|(src, dst, _)| (*src, *dst))
            .into_iter()
            .map(|((src, dst), group)| {
                let actions = group.into_iter().map(|(_, _, t)| t).collect();
                (src, dst, actions)
            })
            .collect();

        let last_state = self.states.len() - 1;
        let mut current_state = BitVec::from_elem(last_state + 1, false);
        for &state in &self.initial_states {
            current_state.set(state, true);
        }
        let mut accepting_states = BitVec::from_elem(last_state + 1, false);
        for &state in &self.accepting_states {
            accepting_states.set(state, true);
        }
        FiniteAutomaton::new(
            acceptance,
            SparseMatrix::from_sorted_list_of_entries(last_state + 1, last_state + 1, &transitions),
            last_state,
            current_state,
            accepting_states,
        )
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum GntmcLtlFormula {
    Atom(String),
    Not(Box<GntmcLtlFormula>),
    And(Box<GntmcLtlFormula>, Box<GntmcLtlFormula>),
    Or(Box<GntmcLtlFormula>, Box<GntmcLtlFormula>),
    Next(Box<GntmcLtlFormula>),
    Until(Box<GntmcLtlFormula>, Box<GntmcLtlFormula>),
    Implies(Box<GntmcLtlFormula>, Box<GntmcLtlFormula>),
    Finally(Box<GntmcLtlFormula>),
    Globally(Box<GntmcLtlFormula>),
    True,
}

impl GntmcLtlFormula {
    fn translate(&self, aps: &mut Vec<String>) -> FormulaTreeNode<String> {
        match self {
            GntmcLtlFormula::Atom(ref f) => {
                if !aps.contains(&f.to_string()) {
                    aps.push(f.to_string());
                }
                FormulaTreeNode::new(None, None, Some(f.to_string()), FormulaTreeNodeType::Atomic)
            }
            GntmcLtlFormula::Not(ref f) => FormulaTreeNode::new(
                Some(Box::from(f.translate(aps))),
                None,
                None,
                FormulaTreeNodeType::Not,
            ),
            GntmcLtlFormula::And(ref left, ref right) => FormulaTreeNode::new(
                Some(Box::from(left.translate(aps))),
                Some(Box::from(right.translate(aps))),
                None,
                FormulaTreeNodeType::And,
            ),
            // A Or B <=> not(not A and not b)
            GntmcLtlFormula::Or(ref left, ref right) => FormulaTreeNode::new(
                Some(Box::from(
                    GntmcLtlFormula::And(
                        Box::from(GntmcLtlFormula::Not(left.clone())),
                        Box::from(GntmcLtlFormula::Not(right.clone())),
                    )
                    .translate(aps),
                )),
                None,
                None,
                FormulaTreeNodeType::Not,
            ),
            // we handle the Next, like the Not-Operator and save them on the left side, of the tree
            GntmcLtlFormula::Next(ref f) => FormulaTreeNode::new(
                Some(Box::from(f.translate(aps))),
                None,
                None,
                FormulaTreeNodeType::Next,
            ),
            GntmcLtlFormula::Until(ref left, ref right) => FormulaTreeNode::new(
                Some(Box::from(left.translate(aps))),
                Some(Box::from(right.translate(aps))),
                None,
                FormulaTreeNodeType::Until,
            ),
            // A Implies B <=> not A or B
            GntmcLtlFormula::Implies(ref left, ref right) => {
                GntmcLtlFormula::Or(Box::from(GntmcLtlFormula::Not(left.clone())), right.clone())
                    .translate(aps)
            }
            //Finally A <=> true Until A
            GntmcLtlFormula::Finally(ref f) => FormulaTreeNode::new(
                Some(Box::from(GntmcLtlFormula::True.translate(aps))),
                Some(Box::from(f.translate(aps))),
                None,
                FormulaTreeNodeType::Until,
            ),
            //globally A <=> not Finally not A
            GntmcLtlFormula::Globally(ref f) => FormulaTreeNode::new(
                Some(Box::from(
                    GntmcLtlFormula::Finally(Box::from(GntmcLtlFormula::Not(f.clone())))
                        .translate(aps),
                )),
                None,
                None,
                FormulaTreeNodeType::Not,
            ),
            GntmcLtlFormula::True => {
                FormulaTreeNode::new(None, None, None, FormulaTreeNodeType::True)
            }
        }
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum GntmcCtlStateFormula {
    Atom(String),
    Not(Box<GntmcCtlStateFormula>),
    And(Box<GntmcCtlStateFormula>, Box<GntmcCtlStateFormula>),
    Or(Box<GntmcCtlStateFormula>, Box<GntmcCtlStateFormula>),
    Implies(Box<GntmcCtlStateFormula>, Box<GntmcCtlStateFormula>),
    Exists(Box<GntmcCtlPathFormula>),
    Forall(Box<GntmcCtlPathFormula>),
    True,
}

impl GntmcCtlStateFormula {
    fn translate(&self, aps: &mut Vec<String>) -> FormulaTreeNode<String> {
        match self {
            GntmcCtlStateFormula::Atom(ref f) => {
                if !aps.contains(&f.to_string()) {
                    aps.push(f.to_string());
                }
                FormulaTreeNode::new(None, None, Some(f.to_string()), FormulaTreeNodeType::Atomic)
            }
            GntmcCtlStateFormula::Not(ref f) => {
                match &**f {
                    //Case ¬¬Φ ≡ Φ
                    GntmcCtlStateFormula::Not(inner_f) => {
                        //If double negation, just translate inner formula (ignore double)
                        inner_f.translate(aps)
                    }
                    _ => FormulaTreeNode::new(
                        Some(Box::from(f.translate(aps))),
                        None,
                        None,
                        FormulaTreeNodeType::Not,
                    ),
                }
            }
            GntmcCtlStateFormula::And(ref left, ref right) => FormulaTreeNode::new(
                Some(Box::from(left.translate(aps))),
                Some(Box::from(right.translate(aps))),
                None,
                FormulaTreeNodeType::And,
            ),
            // A Or B <=> not(not A and not b)
            GntmcCtlStateFormula::Or(ref left, ref right) => FormulaTreeNode::new(
                Some(Box::from(
                    GntmcCtlStateFormula::And(
                        Box::from(GntmcCtlStateFormula::Not(left.clone())),
                        Box::from(GntmcCtlStateFormula::Not(right.clone())),
                    )
                    .translate(aps),
                )),
                None,
                None,
                FormulaTreeNodeType::Not,
            ),
            // A => B <=> not A or B
            GntmcCtlStateFormula::Implies(ref left, ref right) => GntmcCtlStateFormula::Or(
                Box::from(GntmcCtlStateFormula::Not(left.clone())),
                right.clone(),
            )
            .translate(aps),
            // Exists are fine, as we transform the eventually to an Until,
            // always, next and globally are fine in ENF
            GntmcCtlStateFormula::Exists(ref path) => FormulaTreeNode::new(
                Some(Box::from(path.translate(aps))),
                None,
                None,
                FormulaTreeNodeType::Exists,
            ),
            // No Foralls in ENF, they have 4 following types of PathFormulas, following
            GntmcCtlStateFormula::Forall(ref path) => {
                match &**path {
                    // Case ∀◯ Φ <=> ¬∃◯ ¬Φ
                    GntmcCtlPathFormula::Next(inner_path) => GntmcCtlStateFormula::Not(Box::new(
                        GntmcCtlStateFormula::Exists(Box::new(GntmcCtlPathFormula::Next(
                            Box::new(GntmcCtlStateFormula::Not(inner_path.clone())),
                        ))),
                    ))
                    .translate(aps),
                    // Case ∀(Φ U Ψ) = ¬∃(¬Ψ U (¬Φ ∧ ¬Ψ)) ∧ ¬∃□¬Ψ
                    GntmcCtlPathFormula::Until(left_inner_path, right_inner_path) => {
                        GntmcCtlStateFormula::And(
                            Box::from(GntmcCtlStateFormula::Not(Box::from(
                                GntmcCtlStateFormula::Exists(Box::from(
                                    GntmcCtlPathFormula::Until(
                                        Box::from(GntmcCtlStateFormula::Not(
                                            right_inner_path.clone(),
                                        )),
                                        Box::from(GntmcCtlStateFormula::And(
                                            Box::from(GntmcCtlStateFormula::Not(
                                                left_inner_path.clone(),
                                            )),
                                            Box::from(GntmcCtlStateFormula::Not(
                                                right_inner_path.clone(),
                                            )),
                                        )),
                                    ),
                                )),
                            ))),
                            Box::from(GntmcCtlStateFormula::Not(Box::from(
                                GntmcCtlStateFormula::Exists(Box::from(
                                    GntmcCtlPathFormula::Globally(Box::from(
                                        GntmcCtlStateFormula::Not(right_inner_path.clone()),
                                    )),
                                )),
                            ))),
                        )
                        .translate(aps)
                    }
                    // Case ∀♦Φ ≡ ∀(true U Φ)
                    GntmcCtlPathFormula::Finally(inner_path) => {
                        GntmcCtlStateFormula::Forall(Box::from(GntmcCtlPathFormula::Until(
                            Box::from(GntmcCtlStateFormula::True),
                            inner_path.clone(),
                        )))
                        .translate(aps)
                    }
                    // Case ∀□Φ ≡ ¬∃♦¬Φ
                    GntmcCtlPathFormula::Globally(inner_path) => {
                        GntmcCtlStateFormula::Not(Box::from(GntmcCtlStateFormula::Exists(
                            Box::from(GntmcCtlPathFormula::Finally(Box::from(
                                GntmcCtlStateFormula::Not(inner_path.clone()),
                            ))),
                        )))
                        .translate(aps)
                    }
                }
            }
            GntmcCtlStateFormula::True => {
                FormulaTreeNode::new(None, None, None, FormulaTreeNodeType::True)
            }
        }
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum GntmcCtlPathFormula {
    Next(Box<GntmcCtlStateFormula>),
    Until(Box<GntmcCtlStateFormula>, Box<GntmcCtlStateFormula>),
    Finally(Box<GntmcCtlStateFormula>),
    Globally(Box<GntmcCtlStateFormula>),
}
impl GntmcCtlPathFormula {
    fn translate(&self, aps: &mut Vec<String>) -> FormulaTreeNode<String> {
        // until, next and globally are fine in ENF
        match self {
            // ∃◯
            GntmcCtlPathFormula::Next(ref state) => FormulaTreeNode::new(
                Some(Box::from(state.translate(aps))),
                None,
                None,
                FormulaTreeNodeType::Next,
            ),
            // ∃(Ψ U Φ) is fine and can stay
            GntmcCtlPathFormula::Until(ref left, ref right) => FormulaTreeNode::new(
                Some(Box::from(left.translate(aps))),
                Some(Box::from(right.translate(aps))),
                None,
                FormulaTreeNodeType::Until,
            ),
            // ∃♦Φ ≡ ∃(true U Φ) finally gets broken down to an Until
            GntmcCtlPathFormula::Finally(ref left) => FormulaTreeNode::new(
                Some(Box::from(GntmcCtlStateFormula::True.translate(aps))),
                Some(Box::from(left.translate(aps))),
                None,
                FormulaTreeNodeType::Until,
            ),
            // ∃□ is fine, so it can stay
            GntmcCtlPathFormula::Globally(ref left) => FormulaTreeNode::new(
                Some(Box::from(left.translate(aps))),
                None,
                None,
                FormulaTreeNodeType::Globally,
            ),
        }
    }
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "lowercase")]
enum GntmcPropertyKind {
    Invariant(GntmcPropositionalFormula),
    RegularSafety(GntmcFiniteAutomaton),
    Persistence(GntmcPropositionalFormula),
    OmegaRegular(GntmcFiniteAutomaton),
    Ltl(GntmcLtlFormula),
    Ctl(GntmcCtlStateFormula),
}

#[derive(Debug, Deserialize)]
struct GntmcProperty {
    name: String,
    #[serde(flatten)]
    kind: GntmcPropertyKind,
    #[serde(skip_serializing_if = "is_none")]
    #[allow(dead_code)]
    pub is_true: Option<bool>,
}

#[derive(Debug, Deserialize)]
struct GntmcStruct {
    #[allow(dead_code)]
    name: String,
    lts: GntmcTransitionSystem,
    properties: Vec<GntmcProperty>,
}

fn parse_file(path: &str) -> GntmcStruct {
    let reader = BufReader::new(
        File::open(path).unwrap_or_else(|_| panic!("Could not read from file {}.\n\t", path)),
    );
    trace!("Reading...");
    serde_json::from_reader(reader).unwrap_or_else(|_| {
        panic!(
            "Could not parse file {}. Are you using the correct format?\n\t",
            path
        );
    })
}

fn build_ts(input: GntmcTransitionSystem) -> TransitionSystem {
    if input.states.is_empty() {
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
        .sorted()
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
                .unwrap_or_else(|| panic!("State {:?} has no label", state));
            bv.set(i, true);
        }
        bv
    };

    let state_labels: Vec<BitVec> = (0..num_states).map(get_state_label).collect();

    trace!("Built state labels.");
    let label_states = HashMap::new(); // from_iter((0 .. 2_usize.pow(atomic_props.len() as u32)).map(|label_subset| {
                                       // The shifting pushes the labels, i.e., the bits that might be set, into the area that is not truncated in the following
                                       //     let mut label = BitVec::from_bytes(&label_subset.shl(usize::BITS - atomic_props.len() as u32).to_be_bytes());
                                       //     label.truncate(atomic_props.len());
                                       //
                                       //     let states = (0..num_states)
                                       //         .filter(|state| state_labels[*state] == label)
                                       //         .collect::<Vec<_>>();
                                       //
                                       //     (label, states)
                                       // }));
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

fn build_properties(props: Vec<GntmcProperty>) -> (Vec<Property<String>>, Vec<Option<bool>>) {
    props
        .into_iter()
        .map(|p| {
            trace!("Found property {:?} of kind {:?}.", p.name, p.kind);
            let aps: &mut Vec<String> = &mut vec![];
            (
                Property::new(
                    p.name.clone(),
                    match p.kind {
                        GntmcPropertyKind::Invariant(formula) => {
                            PropertyType::Invariant(formula.translate(aps))
                        }
                        GntmcPropertyKind::RegularSafety(automaton) => {
                            PropertyType::RegularSafety(automaton.translate(aps))
                        }
                        GntmcPropertyKind::Persistence(formula) => {
                            PropertyType::Persistence(formula.translate(aps))
                        }
                        GntmcPropertyKind::OmegaRegular(automaton) => {
                            PropertyType::OmegaRegular(automaton.translate(aps))
                        }
                        GntmcPropertyKind::Ltl(formula) => {
                            PropertyType::Ltl(formula.translate(aps))
                        }
                        GntmcPropertyKind::Ctl(formula) => {
                            let mut formula = formula.translate(aps);
                            formula.remove_double_negations();
                            PropertyType::Ctl(formula)
                        }
                    },
                    (*aps).clone(),
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
    let properties = build_properties(input.properties);
    debug!("Done. Found {:?} properties in total.", properties.0.len());

    (ts, properties.0, properties.1)
}
