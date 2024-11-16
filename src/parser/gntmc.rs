use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{BufRead, BufReader};
use serde::Deserialize;
use bit_vec::BitVec;

use crate::common::sparse_matrix::SparseMatrix;
use crate::common::transition_system::*;

#[derive(Debug, Deserialize)]
struct InputTs {
    states: Vec<u64>,
    actions: Vec<u64>,
    transitions: Vec<(u64, u64, u64)>,
    initial_states: Vec<u64>,
    labelling: HashMap<u64, Vec<String>>
}

#[derive(Debug, Deserialize)]
struct InputProps {

}

#[derive(Debug, Deserialize)]
struct InputJSON {
    name: String,
    lts: InputTs,
    // properties: InputProps,
}

fn parse_file(path: &str) -> InputJSON {
    let file = File::open(path).expect(&format!("Could not open file {}.\n\t", path));
    let reader = BufReader::new(file);
    let mut input_string = "".to_string();

    reader.lines()
        .map(|l| l.expect(&format!("Could not read from file {}.\n\t", path)))
        .for_each(|s| {
            input_string.push('\n');
            input_string.push_str(&s)
        });
    
    let input: InputJSON = serde_json::from_str(&*input_string)
        .expect(&format!("Could not parse file {}. Are you using the correct format?\n\t", path));

    input
}

fn build_ts(input: InputTs) -> TransitionSystem {
    if input.states.len() > usize::MAX {
        panic!("Could not build transition system as the number of states ({:?})\
            exceeds the maximum possible number of states ({:?}).\nIf you are
            using a 32bit system the limit can be raised by switching to a 64bit system.",
               input.states.len(), usize::MAX);
    }
    if input.actions.len() == 0 {
        panic!("Transition systems must have at least one state")
    }

    let last_state = input.states.len() - 1;
    let num_states = last_state + 1;
    let tmatrix = SparseMatrix::from_list_of_entries(num_states, num_states, 
                                                     &input.transitions.iter()
                                                         .map(|(s1, _ac, s2)| (*s1 as usize, *s2 as usize, true))
                                                         .collect::<Vec<_>>());
    let reverse_tmatrix = SparseMatrix::from_list_of_entries(num_states, num_states,
                                                             &input.transitions.iter()
                                                                 .map(|(s1, _ac, s2)| (*s2 as usize, *s1 as usize, true))
                                                                 .collect::<Vec<_>>());
    let initial_states = input.initial_states.iter().map(|&i| i as usize).collect::<Vec<_>>();
    let atomic_props = input.labelling.values()
        .cloned()
        .reduce(|mut acc, mut s| { acc.append(&mut s); acc })
        .unwrap()
        .iter().collect::<HashSet<_>>()
        .iter().map(|s| s.clone().clone()).collect::<Vec<_>>();
    let state_labels: Vec<BitVec> = (0 ..num_states).map(|state| {
        let mut bv = BitVec::from_elem(atomic_props.len(), false);
        let lifehack = Vec::new();
        let labels = input.labelling.get(&(state as u64)).unwrap_or(&lifehack);

        labels.iter()
            .map(|s|
                atomic_props.iter()
                    .position(|a| *a == *s)
                    .expect(&format!("State {:?} has no label", s)))
            .for_each(|i| bv.set(i, true));

        bv
    }).collect();
    let label_states = HashMap::from_iter((0 .. atomic_props.len()+1).map(|label_subset| {
        let label = BitVec::from_bytes(&label_subset.to_ne_bytes());
        
        let states = (0 .. num_states).filter(|state| state_labels[*state] == label).collect::<Vec<_>>();

        (label, states)
    }));

    TransitionSystem::new(
        tmatrix,
        reverse_tmatrix,
        last_state,
        initial_states,
        state_labels,
        label_states,
        atomic_props
    )
}

// fn build_formula(props: InputProps) -> Formula {}

#[cfg(test)]
mod tests {
    use bit_vec::BitVec;
    use crate::parser::gntmc::{build_ts, parse_file};

    #[test]
    fn test_parse_file() {
        println!("{:?}", parse_file("./tests/res/test.gntmc"))
    }

    #[test]
    fn test_foo() {
        let inp = parse_file("./tests/res/test.gntmc");
        build_ts(inp.lts);
    }

    #[test]
    fn test_bar() {
        (0 .. 10usize).for_each(|label_subset| {
            let bv = BitVec::from_bytes(&label_subset.to_be_bytes());

            println!("{:?}", bv)

        });
    }
}
