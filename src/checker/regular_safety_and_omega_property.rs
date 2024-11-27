// use crate::common::transition_system::TransitionSystem;
// use crate::parser::property::{FormulaTreeNodeType, Property};
// use bit_vec::BitVec;
// use log::trace;
// use std::collections::{HashMap, HashSet, VecDeque};
// use crate::checker::invariant::bfs_invariant_checking;
// use crate::parser::property::PropertyType;
// use crate::parser::property::FormulaTreeNode;
//
// /// Returns a boolean over the given Transition System and property.
// ///
// /// # Parameters
// /// - `property`: The Invariant which gets checked.
// ///
// /// # Returns
// /// A Result with `Ok` if the property is fulfilled and Err with a path and a trace otherwise.
// pub fn regular_safety_and_omega_checking(
//     transition_system: &TransitionSystem,
//     property: &Property<String>,
//     is_omga: bool,
// ) -> Result<bool, (Vec<Vec<String>>, Vec<usize>)> {
//     //toDo: implement product of transition system
//     //product_transition_system = product(transition_system, property);
//     let node = FormulaTreeNode::new(
//         None,
//         None,
//         Some("".to_string()),
//         FormulaTreeNodeType::Atomic,
//     );
//     let empty_property = Property::new("emptyProperty".to_string(), PropertyType::Invariant(node));
//     if is_omga{
//         return persistance_checking(product_transition_system, &empty_property);
//     }
//     else {
//         return bfs_invariant_checking(product_transition_system, &empty_property);
//     }
//
// }

