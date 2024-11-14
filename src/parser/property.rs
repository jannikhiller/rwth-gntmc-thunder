use log::*;

/// A tree structure representing a property with logical expressions.
///
/// The `PropertyTree` contains a root node (`PropertyTreeNode`), a type of property
/// (`PropertyType`), and a name to identify the property.
pub struct PropertyTree<ValueType> {
    /// The root node of the property tree.
    root: PropertyTreeNode<ValueType>,
    /// The type of property represented by this tree.
    property_type: PropertyType,
    /// The name of the property.
    name: String,
}

/// Creates a new `PropertyTree` with a given name, property type, and root node.
///
/// # Parameters
/// - `name`: A `String` representing the name of the property.
/// - `property_type`: The `PropertyType` specifying the type of the property.
/// - `root`: The root `PropertyTreeNode` of the tree.
///
/// # Returns
/// - A new instance of `PropertyTree`.
impl PropertyTree<String> {

    /// Creates a new `PropertyTree` with a given name, property type, and root node.
    ///
    /// # Parameters
    /// - `name`: A `String` representing the name of the property.
    /// - `property_type`: The `PropertyType` specifying the type of the property.
    /// - `root`: The root `PropertyTreeNode` of the tree.
    ///
    /// # Returns
    /// - A new instance of `PropertyTree`.
    pub fn new(
        name: String,
        property_type: PropertyType,
        root: PropertyTreeNode<String>,
    ) -> Self {
        PropertyTree {
            name,
            property_type,
            root,
        }
    }

    /// Evaluates the property tree against a list of labels.
    ///
    /// This function evaluates the logical expression defined by the property tree,
    /// using the `labels` vector as input to determine the result.
    ///
    /// # Parameters
    /// - `labels`: A vector of `String` labels representing the atomic propositions of the state.
    ///
    /// # Returns
    /// - A `bool` representing the result of the evaluation.
    ///
    /// # Panics
    /// - If nodes required for the evaluation are missing in the tree.
    pub(crate) fn evaluate(&self, labels: &Vec<String>) -> bool {
        match self.property_type {
            PropertyType::Invariant => self.root.evaluate(labels)
        }
    }
}

/// A node in a `PropertyTree` representing a logical expression or label.
///
/// Each node can represent different logical operations (e.g. `AND`, `OR`, `NOT`) or a single
/// atomic label. Nodes can have left and right children to build expressions recursively.
pub struct PropertyTreeNode<ValueType> {
    /// The left child of this node (if any).
    left: Option<Box<PropertyTreeNode<ValueType>>>,
    /// The right child of this node (if any).
    right: Option<Box<PropertyTreeNode<ValueType>>>,
    /// An optional label for atomic expressions.
    label: Option<ValueType>,
    /// The type of operation or node this represents.
    node_type: PropertyNodeType,
}

impl PropertyTreeNode<String> {

    pub fn new(left: Option<Box<PropertyTreeNode<String>>>,
           right: Option<Box<PropertyTreeNode<String>>>,
           label: Option<String>,
           node_type: PropertyNodeType) -> Self {
        PropertyTreeNode {
            left,
            right,
            label,
            node_type
        }
    }

    /// Recursively evaluates this node and its children based on the provided labels.
    ///
    /// # Parameters
    /// - `labels`: A vector of `String` labels representing the atomic propositions of the state.
    ///
    /// # Returns
    /// - A `bool` representing the result of the evaluation.
    ///
    /// # Panics
    /// - If nodes required for the evaluation are missing in the tree.
    fn evaluate(&self, labels: &Vec<String>) -> bool {
        match self.node_type {
            PropertyNodeType::AND => {
                let left_eval = self.left.as_ref().map_or_else(|| {
                    panic!("Missing left node when evaluating AND expression! \
                        Your formula tree is most likely invalid.");
                }, |l| l.evaluate(labels));

                let right_eval = self.right.as_ref().map_or_else(|| {
                    panic!("Missing right node when evaluating AND expression! \
                        Your formula tree is most likely invalid.");
                }, |r| r.evaluate(labels));

                left_eval && right_eval
            },
            PropertyNodeType::OR => {
                let left_eval = self.left.as_ref().map_or_else(|| {
                    panic!("Missing left node when evaluating OR expression! \
                        Your formula tree is most likely invalid.");
                }, |l| l.evaluate(labels));

                let right_eval = self.right.as_ref().map_or_else(|| {
                    panic!("Missing right node when evaluating OR expression! \
                        Your formula tree is most likely invalid.");
                }, |r| r.evaluate(labels));

                left_eval || right_eval
            },
            PropertyNodeType::NOT => !self.left.as_ref().map_or_else(|| {
                panic!("Missing left node when evaluating NOT expression! \
                    Your formula tree is most likely invalid.");
            }, |l| !l.evaluate(labels)),
            PropertyNodeType::ATOMIC => labels.contains(&self.label.as_ref().unwrap())
        }
    }
}

/// Specifies the type of property in a `PropertyTree`.
///
/// Currently only supports `Invariant` but can be extended to include other property types.
pub enum PropertyType {
    Invariant
}

/// Represents the type of node within a `PropertyTreeNode`.
///
/// This enum defines the possible logical operations or atomic values that a node can represent,
/// including `AND`, `OR`, `NOT`, and `ATOMIC`.
pub enum PropertyNodeType {
    AND,
    OR,
    NOT,
    ATOMIC
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_atomic_node_evaluation() {
        let atomic_node = PropertyTreeNode::new(None, None, Some("A".to_string()), PropertyNodeType::ATOMIC);

        let labels = vec!["A".to_string()];
        assert!(atomic_node.evaluate(&labels), "Atomic node with label 'A' should evaluate to true.");

        let labels = vec!["B".to_string()];
        assert!(!atomic_node.evaluate(&labels), "Atomic node with label 'A' should evaluate to false when 'A' is not in labels.");
    }

    #[test]
    fn test_not_node_evaluation() {
        let atomic_node = PropertyTreeNode::new(None, None, Some("A".to_string()), PropertyNodeType::ATOMIC);
        let not_node = PropertyTreeNode::new(Some(Box::new(atomic_node)), None, None, PropertyNodeType::NOT);

        let labels = vec!["A".to_string()];
        assert!(!not_node.evaluate(&labels), "NOT node should invert the evaluation of the atomic node.");

        let labels = vec!["B".to_string()];
        assert!(not_node.evaluate(&labels), "NOT node should return true when the atomic node evaluates to false.");
    }

    #[test]
    fn test_and_node_evaluation() {
        let atomic_a = PropertyTreeNode::new(None, None, Some("A".to_string()), PropertyNodeType::ATOMIC);
        let atomic_b = PropertyTreeNode::new(None, None, Some("B".to_string()), PropertyNodeType::ATOMIC);

        let and_node = PropertyTreeNode::new(
            Some(Box::new(atomic_a)),
            Some(Box::new(atomic_b)),
            None,
            PropertyNodeType::AND,
        );

        let labels = vec!["A".to_string(), "B".to_string()];
        assert!(and_node.evaluate(&labels), "AND node should evaluate to true when both children evaluate to true.");

        let labels = vec!["A".to_string()];
        assert!(!and_node.evaluate(&labels), "AND node should evaluate to false when only one child evaluates to true.");

        let labels = vec!["C".to_string()];
        assert!(!and_node.evaluate(&labels), "AND node should evaluate to false when neither child evaluates to true.");
    }

    #[test]
    fn test_or_node_evaluation() {
        let atomic_a = PropertyTreeNode::new(None, None, Some("A".to_string()), PropertyNodeType::ATOMIC);
        let atomic_b = PropertyTreeNode::new(None, None, Some("B".to_string()), PropertyNodeType::ATOMIC);

        let or_node = PropertyTreeNode::new(
            Some(Box::new(atomic_a)),
            Some(Box::new(atomic_b)),
            None,
            PropertyNodeType::OR,
        );

        let labels = vec!["A".to_string(), "B".to_string()];
        assert!(or_node.evaluate(&labels), "OR node should evaluate to true when both children evaluate to true.");

        let labels = vec!["A".to_string()];
        assert!(or_node.evaluate(&labels), "OR node should evaluate to true when at least one child evaluates to true.");

        let labels = vec!["C".to_string()];
        assert!(!or_node.evaluate(&labels), "OR node should evaluate to false when neither child evaluates to true.");
    }

    #[test]
    fn test_property_tree_evaluation() {
        let atomic_a = PropertyTreeNode::new(None, None, Some("A".to_string()), PropertyNodeType::ATOMIC);
        let atomic_b = PropertyTreeNode::new(None, None, Some("B".to_string()), PropertyNodeType::ATOMIC);
        let not_b = PropertyTreeNode::new(Some(Box::new(atomic_b)), None, None, PropertyNodeType::NOT);
        let root = PropertyTreeNode::new(Some(Box::new(atomic_a)), Some(Box::new(not_b)), None, PropertyNodeType::AND);
        let property_tree = PropertyTree::new("ExampleTree".to_string(), PropertyType::Invariant, root);

        let labels = vec!["A".to_string()];
        assert!(property_tree.evaluate(&labels), "PropertyTree should evaluate to true when labels satisfy the AND condition with NOT.");

        let labels = vec!["B".to_string()];
        assert!(!property_tree.evaluate(&labels), "PropertyTree should evaluate to false when labels do not satisfy the AND condition with NOT.");
    }

    #[test]
    #[should_panic(expected = "Missing left node when evaluating AND expression!")]
    fn test_and_node_missing_left_child() {
        let atomic_b = PropertyTreeNode::new(None, None, Some("B".to_string()), PropertyNodeType::ATOMIC);
        let and_node = PropertyTreeNode::new(None, Some(Box::new(atomic_b)), None, PropertyNodeType::AND);

        let labels = vec!["B".to_string()];
        and_node.evaluate(&labels); // This should panic due to missing left child
    }

    #[test]
    #[should_panic(expected = "Missing right node when evaluating AND expression!")]
    fn test_and_node_missing_right_child() {
        let atomic_a = PropertyTreeNode::new(None, None, Some("A".to_string()), PropertyNodeType::ATOMIC);
        let and_node = PropertyTreeNode::new(Some(Box::new(atomic_a)), None, None, PropertyNodeType::AND);

        let labels = vec!["A".to_string()];
        and_node.evaluate(&labels); // This should panic due to missing right child
    }

    #[test]
    #[should_panic(expected = "Missing left node when evaluating OR expression!")]
    fn test_or_node_missing_left_child() {
        let atomic_b = PropertyTreeNode::new(None, None, Some("B".to_string()), PropertyNodeType::ATOMIC);
        let or_node = PropertyTreeNode::new(None, Some(Box::new(atomic_b)), None, PropertyNodeType::OR);

        let labels = vec!["B".to_string()];
        or_node.evaluate(&labels); // This should panic due to missing left child
    }

    #[test]
    #[should_panic(expected = "Missing right node when evaluating OR expression!")]
    fn test_or_node_missing_right_child() {
        let atomic_a = PropertyTreeNode::new(None, None, Some("A".to_string()), PropertyNodeType::ATOMIC);
        let or_node = PropertyTreeNode::new(Some(Box::new(atomic_a)), None, None, PropertyNodeType::OR);

        let labels = vec!["A".to_string()];
        or_node.evaluate(&labels); // This should panic due to missing right child
    }

    #[test]
    #[should_panic(expected = "Missing left node when evaluating NOT expression!")]
    fn test_not_node_missing_child() {
        let not_node = PropertyTreeNode::new(None, None, None, PropertyNodeType::NOT);

        let labels = vec!["A".to_string()];
        not_node.evaluate(&labels); // This should panic due to missing left child
    }
}
