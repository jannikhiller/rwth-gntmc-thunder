use log::*;

/// A tree structure representing a property with logical expressions.
///
/// The `Property` contains a root node (`FormulaTreeNode`), a type of property
/// (`PropertyType`), and a name to identify the property.
pub struct Property<ValueType> {
    /// The root node of the formula tree.
    root: FormulaTreeNode<ValueType>,
    /// The type of property represented by this tree.
    property_type: PropertyType,
    /// The name of the property.
    name: String,
}

/// Creates a new `Property` with a given name, property type, and root node.
/// The given `ValueType` specifies the datatype of the label.
///
/// # Parameters
/// - `name`: A `String` representing the name of the property.
/// - `property_type`: The `PropertyType` specifying the type of the property.
/// - `root`: The root `FormulaTreeNode` of the tree.
///
/// # Returns
/// - A new instance of `Property`.
impl Property<String> {
    /// Creates a new `Property` with a given name, property type, and root node.
    ///
    /// # Parameters
    /// - `name`: A `String` representing the name of the property.
    /// - `property_type`: The `PropertyType` specifying the type of the property.
    /// - `root`: The root `FormulaTreeNode` of the tree.
    ///
    /// # Returns
    /// - A new instance of `Property`.
    pub fn new(name: String, property_type: PropertyType, root: FormulaTreeNode<String>) -> Self {
        Property {
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
            PropertyType::Invariant => self.root.evaluate(labels),
        }
    }
}

/// A node in a `FormulaTreeNode` representing a logical expression or label.
///
/// Each node can represent different logical operations (e.g. `AND`, `OR`, `NOT`) or a single
/// atomic label. Nodes can have left and right children to build expressions recursively.
/// The given `ValueType` specifies the datatype of the label.
pub struct FormulaTreeNode<ValueType> {
    /// The left child of this node (if any).
    left: Option<Box<FormulaTreeNode<ValueType>>>,
    /// The right child of this node (if any).
    right: Option<Box<FormulaTreeNode<ValueType>>>,
    /// An optional label for atomic expressions.
    label: Option<ValueType>,
    /// The type of operation or node this represents.
    node_type: FormulaTreeNodeType,
}

impl FormulaTreeNode<String> {
    pub fn new(
        left: Option<Box<FormulaTreeNode<String>>>,
        right: Option<Box<FormulaTreeNode<String>>>,
        label: Option<String>,
        node_type: FormulaTreeNodeType,
    ) -> Self {
        FormulaTreeNode {
            left,
            right,
            label,
            node_type,
        }
    }

    /// Recursively evaluates this node and its children based on the provided labels.
    /// Note that for NOT nodes only the left child will get evaluated.
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
            FormulaTreeNodeType::AND => {
                if self.left.as_ref().is_none() {
                    panic!(
                        "Missing left node when evaluating AND expression! \
                        Your formula tree is most likely invalid."
                    );
                } else if self.right.as_ref().is_none() {
                    panic!(
                        "Missing right node when evaluating AND expression! \
                        Your formula tree is most likely invalid."
                    );
                }

                self.left.as_ref().unwrap().evaluate(&labels)
                    && self.right.as_ref().unwrap().evaluate(&labels)
            }
            FormulaTreeNodeType::OR => {
                if self.left.as_ref().is_none() {
                    panic!(
                        "Missing left node when evaluating OR expression! \
                        Your formula tree is most likely invalid."
                    );
                } else if self.right.as_ref().is_none() {
                    panic!(
                        "Missing right node when evaluating OR expression! \
                        Your formula tree is most likely invalid."
                    );
                }

                self.left.as_ref().unwrap().evaluate(&labels)
                    || self.right.as_ref().unwrap().evaluate(&labels)
            }
            FormulaTreeNodeType::NOT => self.left.as_ref().map_or_else(
                || {
                    panic!(
                        "Missing left node when evaluating NOT expression! \
                    Your formula tree is most likely invalid."
                    );
                },
                |l| !l.evaluate(labels),
            ),
            FormulaTreeNodeType::ATOMIC => labels.contains(&self.label.as_ref().unwrap()),
        }
    }
}

/// Specifies the type of property.
///
/// Currently only supports `Invariant` but can be extended to include other property types.
pub enum PropertyType {
    Invariant,
}

/// Represents the type of node within a `FormulaTreeNode`.
///
/// This enum defines the possible logical operations or atomic values that a node can represent,
/// including `AND`, `OR`, `NOT`, and `ATOMIC`.
pub enum FormulaTreeNodeType {
    AND,
    OR,
    NOT,
    ATOMIC,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_atomic_node_evaluation() {
        let atomic_node = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::ATOMIC,
        );

        let labels = vec!["A".to_string()];
        assert_eq!(
            true,
            atomic_node.evaluate(&labels),
            "Atomic node with label 'A' should evaluate to true."
        );

        let labels = vec!["B".to_string()];
        assert_eq!(
            false,
            atomic_node.evaluate(&labels),
            "Atomic node with label 'A' should evaluate to false when 'A' is not in labels."
        );
    }

    #[test]
    fn test_not_node_evaluation() {
        let atomic_node = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::ATOMIC,
        );
        let not_node = FormulaTreeNode::new(
            Some(Box::new(atomic_node)),
            None,
            None,
            FormulaTreeNodeType::NOT,
        );

        let labels = vec!["A".to_string()];
        assert_eq!(
            false,
            not_node.evaluate(&labels),
            "NOT node should invert the evaluation of the atomic node."
        );

        let labels = vec!["B".to_string()];
        assert_eq!(
            true,
            not_node.evaluate(&labels),
            "NOT node should return true when the atomic node evaluates to false."
        );
    }

    #[test]
    fn test_and_node_evaluation() {
        let atomic_a = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::ATOMIC,
        );
        let atomic_b = FormulaTreeNode::new(
            None,
            None,
            Some("B".to_string()),
            FormulaTreeNodeType::ATOMIC,
        );

        let and_node = FormulaTreeNode::new(
            Some(Box::new(atomic_a)),
            Some(Box::new(atomic_b)),
            None,
            FormulaTreeNodeType::AND,
        );

        let labels = vec!["A".to_string(), "B".to_string()];
        assert_eq!(
            true,
            and_node.evaluate(&labels),
            "AND node should evaluate to true when both children evaluate to true."
        );

        let labels = vec!["A".to_string()];
        assert_eq!(
            false,
            and_node.evaluate(&labels),
            "AND node should evaluate to false when only one child evaluates to true."
        );

        let labels = vec!["C".to_string()];
        assert_eq!(
            false,
            and_node.evaluate(&labels),
            "AND node should evaluate to false when neither child evaluates to true."
        );
    }

    #[test]
    fn test_or_node_evaluation() {
        let atomic_a = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::ATOMIC,
        );
        let atomic_b = FormulaTreeNode::new(
            None,
            None,
            Some("B".to_string()),
            FormulaTreeNodeType::ATOMIC,
        );

        let or_node = FormulaTreeNode::new(
            Some(Box::new(atomic_a)),
            Some(Box::new(atomic_b)),
            None,
            FormulaTreeNodeType::OR,
        );

        let labels = vec!["A".to_string(), "B".to_string()];
        assert_eq!(
            true,
            or_node.evaluate(&labels),
            "OR node should evaluate to true when both children evaluate to true."
        );

        let labels = vec!["A".to_string()];
        assert_eq!(
            true,
            or_node.evaluate(&labels),
            "OR node should evaluate to true when at least one child evaluates to true."
        );

        let labels = vec!["C".to_string()];
        assert_eq!(
            false,
            or_node.evaluate(&labels),
            "OR node should evaluate to false when neither child evaluates to true."
        );
    }

    #[test]
    fn test_property_evaluation() {
        let atomic_a = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::ATOMIC,
        );
        let atomic_b = FormulaTreeNode::new(
            None,
            None,
            Some("B".to_string()),
            FormulaTreeNodeType::ATOMIC,
        );
        let not_b = FormulaTreeNode::new(
            Some(Box::new(atomic_b)),
            None,
            None,
            FormulaTreeNodeType::NOT,
        );
        let root = FormulaTreeNode::new(
            Some(Box::new(atomic_a)),
            Some(Box::new(not_b)),
            None,
            FormulaTreeNodeType::AND,
        );
        let property = Property::new("ExampleTree".to_string(), PropertyType::Invariant, root);

        let labels = vec!["A".to_string()];
        assert_eq!(
            true,
            property.evaluate(&labels),
            "Property should evaluate to true when labels satisfy the AND condition with NOT."
        );

        let labels = vec!["B".to_string()];
        assert_eq!(false, property.evaluate(&labels), "Property should evaluate to false when labels do not satisfy the AND condition with NOT.");
    }

    #[test]
    #[should_panic(expected = "Missing left node when evaluating AND expression!")]
    fn test_and_node_missing_left_child() {
        let atomic_b = FormulaTreeNode::new(
            None,
            None,
            Some("B".to_string()),
            FormulaTreeNodeType::ATOMIC,
        );
        let and_node = FormulaTreeNode::new(
            None,
            Some(Box::new(atomic_b)),
            None,
            FormulaTreeNodeType::AND,
        );

        let labels = vec!["B".to_string()];
        and_node.evaluate(&labels); // This should panic due to missing left child
    }

    #[test]
    #[should_panic(expected = "Missing right node when evaluating AND expression!")]
    fn test_and_node_missing_right_child() {
        let atomic_a = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::ATOMIC,
        );
        let and_node = FormulaTreeNode::new(
            Some(Box::new(atomic_a)),
            None,
            None,
            FormulaTreeNodeType::AND,
        );

        let labels = vec!["A".to_string()];
        and_node.evaluate(&labels); // This should panic due to missing right child
    }

    #[test]
    #[should_panic(expected = "Missing left node when evaluating OR expression!")]
    fn test_or_node_missing_left_child() {
        let atomic_b = FormulaTreeNode::new(
            None,
            None,
            Some("B".to_string()),
            FormulaTreeNodeType::ATOMIC,
        );
        let or_node = FormulaTreeNode::new(
            None,
            Some(Box::new(atomic_b)),
            None,
            FormulaTreeNodeType::OR,
        );

        let labels = vec!["B".to_string()];
        or_node.evaluate(&labels); // This should panic due to missing left child
    }

    #[test]
    #[should_panic(expected = "Missing right node when evaluating OR expression!")]
    fn test_or_node_missing_right_child() {
        let atomic_a = FormulaTreeNode::new(
            None,
            None,
            Some("A".to_string()),
            FormulaTreeNodeType::ATOMIC,
        );
        let or_node = FormulaTreeNode::new(
            Some(Box::new(atomic_a)),
            None,
            None,
            FormulaTreeNodeType::OR,
        );

        let labels = vec!["A".to_string()];
        or_node.evaluate(&labels); // This should panic due to missing right child
    }

    #[test]
    #[should_panic(expected = "Missing left node when evaluating NOT expression!")]
    fn test_not_node_missing_child() {
        let not_node = FormulaTreeNode::new(None, None, None, FormulaTreeNodeType::NOT);

        let labels = vec!["A".to_string()];
        not_node.evaluate(&labels); // This should panic due to missing left child
    }
}
