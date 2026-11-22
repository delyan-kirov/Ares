//! Booleans in types: the values a proposition's sides may compute.
//!
//! A boolean in a type is a constant `true`/`false` or an application of a
//! [`BoolOp`] to sizes or booleans. Folding one
//! evaluates what its operands decide: a comparison of two constant sizes,
//! a comparison of a size with itself, and `not`, `&&`, `||` of constants.
//! What is left is a neutral boolean, equal only to one written the same way.
//!
//! Entry point: [`Unifier::fold_bool`], which [`Unifier::unify`] calls before
//! it compares a boolean.
//! See Note [Propositions].

use utilities::StrId;

use super::Unifier;
use crate::typing::types::{BoolOp, Type, TypeNode, FALSE, TRUE};

impl Unifier {
    /// The boolean operation `ty` applies, with its operands, if it is one.
    pub fn bool_op(&self, ty: Type) -> Option<(BoolOp, Vec<Type>)> {
        let mut args = Vec::new();
        let mut cur = self.resolve(ty);
        while let TypeNode::App(head, arg) = self.types.node(cur) {
            args.push(arg);
            cur = self.resolve(head);
        }
        args.reverse();
        let TypeNode::Con(name) = self.types.node(cur) else { return None };
        let op = BoolOp::named(name.as_str())?;
        (args.len() == op.arity()).then_some((op, args))
    }

    /// The constant `ty` is, if it is `true` or `false`.
    pub fn bool_const(&self, ty: Type) -> Option<bool> {
        match self.head(ty) {
            TypeNode::Con(name) if name == StrId::intern(TRUE) => Some(true),
            TypeNode::Con(name) if name == StrId::intern(FALSE) => Some(false),
            _ => None,
        }
    }

    /// Evaluate a boolean as far as its operands decide it, or `None` when
    /// nothing reduces (so a caller comparing two booleans stops folding).
    // Rule [Frontend-Bool-Conversion]
    pub fn fold_bool(&self, ty: Type) -> Option<Type> {
        let (op, args) = self.bool_op(ty)?;
        let folded: Vec<(Type, bool)> = args.iter().map(|&a| match self.fold_bool(a) {
            Some(f) => (f, true),
            None => (a, false),
        }).collect();
        let changed = folded.iter().any(|(_, c)| *c);
        let args: Vec<Type> = folded.into_iter().map(|(a, _)| a).collect();
        let konst = |u: &Unifier, b: bool| Some(u.types.bool_lit(b));
        match (op, args.as_slice()) {
            (BoolOp::Lt | BoolOp::Eq, &[a, b]) => {
                let (pa, pb) = (self.normalize_size(a), self.normalize_size(b));
                if pa == pb {
                    return konst(self, op == BoolOp::Eq);
                }
                if let (Some(x), Some(y)) = (self.nat_value(a), self.nat_value(b)) {
                    return konst(self, if op == BoolOp::Lt { x < y } else { x == y });
                }
            }
            (BoolOp::Not, &[x]) => {
                if let Some(b) = self.bool_const(x) {
                    return konst(self, !b);
                }
                if let Some((BoolOp::Not, inner)) = self.bool_op(x) {
                    return Some(inner[0]);
                }
            }
            (BoolOp::And | BoolOp::Or, &[a, b]) => {
                // `&&` is decided by a `false` operand and `||` by a `true`
                // one; the other constant leaves the other operand.
                let decides = op == BoolOp::Or;
                for (x, other) in [(a, b), (b, a)] {
                    match self.bool_const(x) {
                        Some(c) if c == decides => return konst(self, decides),
                        Some(_) => return Some(other),
                        None => {}
                    }
                }
            }
            _ => unreachable!("an operator applied to its arity"),
        }
        changed.then(|| self.types.bool_op(op, &args))
    }
}
