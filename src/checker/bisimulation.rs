use itertools::iproduct;
use itertools::Itertools;

use crate::common::transition_system::TransitionSystem;

fn get_initial_partition(ts: &TransitionSystem, aps: &[String]) -> Vec<Vec<(usize, usize)>> {
    let ap_bitmask = ts.get_label_from_aps(aps);
    let label_classes = ts.get_states().into_group_map_by(|&state| {
        let mut label = ts.get_state_label(state).clone();
        label.and(&ap_bitmask);
        label
    });
    label_classes
        .into_values()
        .map(|class| {
            iproduct!(class.iter(), class.iter())
                .map(|(&a, &b)| (a, b))
                .collect()
        })
        .collect()
}

fn simple_selection_strategy(ts: &TransitionSystem, aps: &[String]) -> Vec<Vec<(usize, usize)>> {
    todo!()
}

pub fn reduce_ts(ts: &TransitionSystem) -> TransitionSystem {
    todo!()
}

/*
 * init: 0
 *
 * 0a -> 1b
 * 1b -> 2c
 * 2c -> 0a
 * 3a -> 1b
 */

#[cfg(test)]
mod tests {}
