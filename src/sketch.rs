use egg::{Id, Language, RecExpr};
use std::{fmt::{self, Display, Formatter}};
use thiserror::Error;

/// A [`Sketch`] is a program pattern that is satisfied by a family of programs.
///
/// It can also be seen as an incomplete or partial program as it can leave details unspecified.
pub type Sketch<L> = RecExpr<SketchNode<L>>;

/// The language of [`Sketch`]es.
///
#[derive(Debug, Hash, PartialEq, Eq, Clone, PartialOrd, Ord)]
pub enum SketchNode<L> {
    /// Any program of the underlying [`Language`].
    ///
    /// Corresponds to the `?` syntax.
    Any,
    /// Programs made from this [`Language`] node whose children satisfy the given sketches.
    ///
    /// Corresponds to the `(language_node s1 .. sn)` syntax.
    Node(L),
    /// Programs that contain sub-programs satisfying the given sketch.
    ///
    /// Corresponds to the `(contains s)` syntax.
    Contains(Id),
    /// Programs that satisfy any of these sketches.
    ///
    /// Corresponds to the `(or s1 .. sn)` syntax.
    Or(Vec<Id>),
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum SketchDiscriminant<L: Language> {
    Any,
    Node(L::Discriminant),
    Contains,
    Or,
}

impl<L: Language> Language for SketchNode<L> {
    type Discriminant = SketchDiscriminant<L>;

    #[inline(always)]
    fn discriminant(&self) -> Self::Discriminant {
        match self {
            SketchNode::Any => SketchDiscriminant::Any,
            SketchNode::Node(n) => SketchDiscriminant::Node(n.discriminant()),
            SketchNode::Contains(_) => SketchDiscriminant::Contains,
            SketchNode::Or(_) => SketchDiscriminant::Or
        }
    }

    fn matches(&self, _other: &Self) -> bool {
        panic!("Should never call this")
    }

    fn children(&self) -> &[Id] {
        match self {
            Self::Any => &[],
            Self::Node(n) => n.children(),
            Self::Contains(s) => std::slice::from_ref(s),
            Self::Or(ss) => ss.as_slice(),
        }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        match self {
            Self::Any => &mut [],
            Self::Node(n) => n.children_mut(),
            Self::Contains(s) => std::slice::from_mut(s),
            Self::Or(ss) => ss.as_mut_slice(),
        }
    }
}

impl<L: Language + Display> Display for SketchNode<L> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Any => write!(f, "?"),
            Self::Node(node) => Display::fmt(node, f),
            Self::Contains(_) => write!(f, "contains"),
            Self::Or(_) => write!(f, "or"),
        }
    }
}

#[derive(Debug, Error)]
pub enum SketchParseError<E> {
    #[error("wrong number of children: {0:?}")]
    BadChildren(egg::FromOpError),

    #[error(transparent)]
    BadOp(E),
}

impl<L: egg::FromOp> egg::FromOp for SketchNode<L> {
    type Error = SketchParseError<L::Error>;

    fn from_op(op: &str, children: Vec<Id>) -> Result<Self, Self::Error> {
        match op {
            "?" => {
                if children.len() == 0 {
                    Ok(Self::Any)
                } else {
                    Err(SketchParseError::BadChildren(egg::FromOpError::new(
                        op, children,
                    )))
                }
            }
            "contains" => {
                if children.len() == 1 {
                    Ok(Self::Contains(children[0]))
                } else {
                    Err(SketchParseError::BadChildren(egg::FromOpError::new(
                        op, children,
                    )))
                }
            }
            "or" => Ok(Self::Or(children)),
            _ => L::from_op(op, children)
                .map(Self::Node)
                .map_err(SketchParseError::BadOp),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;

    #[test]
    fn parse_and_print() {
        let string = "(contains (f ?))";
        let sketch = string.parse::<Sketch<SymbolLang>>().unwrap();

        let mut sketch_ref = RecExpr::default();
        let any = sketch_ref.add(SketchNode::Any);
        let f = sketch_ref.add(SketchNode::Node(SymbolLang::new("f", vec![any])));
        let _ = sketch_ref.add(SketchNode::Contains(f));

        assert_eq!(sketch, sketch_ref);
        assert_eq!(sketch.to_string(), string);
    }
}
