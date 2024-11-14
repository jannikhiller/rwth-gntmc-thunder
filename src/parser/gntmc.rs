use std::collections::HashMap;
use std::fs::File;
use std::io::{BufRead, BufReader};
use serde::Deserialize;

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
    properties: InputProps,
}

pub fn parse_file(path: &str) -> InputJSON {
    let file = File::open(path).expect(&format!("Could not open file {}.\n\t", path));
    let reader = BufReader::new(file);
    let mut input_string = "".to_string();

    reader.lines()
        .map(|l| l.expect(&format!("Could not read from file {}.\n\t", path)))
        .for_each(|s| {
            input_string.push('\n');
            input_string.push_str(&s)
        });

    println!("Input: {}", input_string);
    
    let input: InputJSON = serde_json::from_str(&*input_string)
        .expect(&format!("Could not parse file {}. Are you using the correct format?\n\t", path));

    input
}
