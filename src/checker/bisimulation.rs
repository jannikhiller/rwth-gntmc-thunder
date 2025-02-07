#![allow(dead_code)]

use itertools::kmerge;
use itertools::Itertools;

use crate::common::transition_system::TransitionSystem;

#[cfg(test)]
mod tests {
    use super::*;

    fn aps(str: &str) -> Vec<String> {
        str.chars().map(String::from).collect()
    }

    
}
