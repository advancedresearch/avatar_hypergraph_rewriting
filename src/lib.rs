#![deny(missing_docs)]

//! # Avatar Hypergraph Rewriting
//! Hypergraph rewriting system with avatars for symbolic distinction
//!
//! Based on paper [Avatar Hypergraph Rewriting](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/avatar-hypergraph-rewriting.pdf).
//!
//! Avatars can be used on the left side of rewriting rules to control
//! symbolic distinction of nodes in the hypergraph evolution.
//! They can be used on any hyperedge.
//!
//! ### Example: Wolfram vs Avatar
//!
//! ```rust
//! use avatar_hypergraph_rewriting::*;
//!
//! use Expr::*;
//!
//! fn main() {
//!     // `{0,0}`
//!    let a = vec![Nat(0), Nat(0)];
//!
//!     // `{1,2} -> {}`
//!     let wolfram_rule = Rule(vec![Nat(1), Nat(2)], vec![]);
//!     // prints `{}` because `{0,0}` is reduced.
//!     println!("{}", format(&wolfram_rule.parallel(&a)));
//!
//!     // `{a'(1),b'(2)} -> {}`
//!     let avatar_rule = Rule(vec![ava("a", 1), ava("b", 2)], vec![]);
//!     // prints `{0,0}` because avatars "a" and "b" must be different nodes.
//!     println!("{}", format(&avatar_rule.parallel(&a)));
//! }
//! ```
//!
//! ### Motivation
//!
//! Avatar Hypergraph Rewriting (AHR) is an attempt to find an
//! [Avatar Extension](https://advancedresearch.github.io/avatar-extensions/summary.html)
//! of Wolfram models that satisfies the assumptions in the paper
//! [Consciousness in Wolfram Models](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/consciousness-in-wolfram-models.pdf).
//!
//! Wolfram models are used in the [Wolfram Physics Project](https://wolframphysics.org/),
//! which seeks to explain fundamental physics
//! using a hypergraph rewriting system.
//!
//! Wolfram models correspond to theorem proving with
//! [Intuitionistic Propositional Logic](https://en.wikipedia.org/wiki/Intuitionistic_logic) (IPL),
//! which can be generalised to Homotopy Type Theory.
//! For more information, see [this paper](https://arxiv.org/abs/2111.03460) by
//! Xerxes D. Arsiwalla and Jonathan Gorard.
//!
//! IPL is the foundation for Type Theory and modern mathematical foundations.
//! IPL is weaker than
//! [Propositional Logic](https://en.wikipedia.org/wiki/Propositional_calculus) (PL).
//!
//! - PL is called "classical" logic and satisfies a Boolean algebra
//! - IPL is called "constructive" logic and satisfies a Heyting algebra
//!
//! However, in [Path Semantics](https://github.com/advancedresearch/path_semantics)
//! there is an even weaker logic called Path Semantical Intuitionistic Propositional Logic (PSI).
//!
//! PSI is much less understood than IPL and PL,
//! but is relevant for the philosophy of mathematical language design.
//! One thing that makes PSI different from IPL is that a quality operator `~~`
//! lifts biconditions with symbolic distinction (quality is a partial equivalence).
//!
//! A closely related research topic to PSI is
//! [Avatar Extensions](https://advancedresearch.github.io/avatar-extensions/summary.html).
//!
//! This hypergraph rewriting system combines the property of symbolic distinction with avatars.
//! The avatars is a design choice to express symbolic distinction efficiently.

use std::sync::Arc;
use std::collections::HashMap;
use std::fmt;

use Expr::*;

/// Stores a hyper graph.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expr {
    /// A natural number.
    Nat(u64),
    /// A hyper edge.
    Hyp(Vec<Expr>),
    /// An avatar.
    Ava(Arc<String>, Box<Expr>),
}

impl fmt::Display for Expr {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Nat(n) => write!(w, "{}", n)?,
            Hyp(vs) => {
                write!(w, "{{")?;
                for (i, v) in vs.iter().enumerate() {
                    if i != 0 {write!(w, ",")?};
                    write!(w, "{}", v)?;
                }
                write!(w, "}}")?;
            }
            Ava(name, h) => write!(w, "{}'({})", name, h)?,
        }
        Ok(())
    }
}

/// An avatar.
pub fn ava<T: Into<String>, U: Into<Expr>>(a: T, b: U) -> Expr {
    Ava(Arc::new(a.into()), Box::new(b.into()))
}

impl From<u64> for Expr {
    fn from(v: u64) -> Expr {Nat(v)}
}

impl Expr {
    /// Returns a new natural number that does not exist in the hyper graph.
    pub fn new_nat(&self) -> u64 {
        match self {
            Nat(n) => n + 1,
            Hyp(v) => v.iter().map(|n| n.new_nat()).max().unwrap_or(0),
            Ava(_, h) => h.new_nat(),
        }
    }

    /// Substitute values.
    pub fn substitute(&self, f: &mut impl FnMut(u64) -> u64) -> Expr {
        match self {
            Nat(n) => Nat(f(*n)),
            Hyp(v) => Hyp(v.iter().map(|n| n.substitute(f)).collect()),
            Ava(_, h) => h.substitute(f),
        }
    }

    /// Generates a map to the first match.
    pub fn matches(
        &self,
        s: &Expr,
        f: &mut HashMap<u64, u64>
    ) -> bool {
        match (&self, s) {
            (Nat(n), Nat(m)) => modify(f, *n, *m),
            (Hyp(_), Nat(_)) => false,
            (Nat(_), Hyp(_)) => false,
            (Hyp(an), Hyp(bn)) => {
                if an.len() != bn.len() {return false}
                for (a, b) in an.iter().zip(bn.iter()) {
                    if !a.matches(b, f) {
                        return false;
                    }
                }
                true
            }
            (Ava(_, a), b) => a.matches(b, f),
            (_, Ava(_, _)) => panic!("Avatars not allowed in state"),
        }
    }
}

/// Formats a slice of the hypergraph.
pub fn format(h: &[Expr]) -> String {
    use std::fmt::Write;

    let mut w = String::new();
    write!(w, "{{").unwrap();
    for (i, v) in h.iter().enumerate() {
        if i != 0 {write!(w, ",").unwrap()};
        write!(w, "{}", v).unwrap();
    }
    write!(w, "}}").unwrap();
    w
}

/// Stores a rewriting rule for hypergraphs.
pub struct Rule(pub Vec<Expr>, pub Vec<Expr>);

impl fmt::Display for Rule {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(w, "{} -> {}", format(&self.0), format(&self.1))
    }
}

// Helper function for modifying map.
fn modify(
    f: &mut HashMap<u64, u64>,
    old: u64,
    new: u64
) -> bool {
    if let Some(&n) = f.get(&old) {
        if n == new {true} else {false}
    } else {
        f.insert(old, new);
        true
    }
}

// Helper function to generate a map to the first match.
fn match_first(
    an: &[Expr],
    bn: &[Expr],
    f: &mut HashMap<u64, u64>
) -> (bool, Vec<Expr>) {
    let mut ava: HashMap<Expr, Arc<String>> = HashMap::new();
    let mut matched: HashMap<usize, ()> = HashMap::new();
    let mut f2 = f.clone();
    for a in an {
        let mut found = false;
        for (i, b) in bn.iter().enumerate() {
            if matched.contains_key(&i) {continue};
            let mut g = f2.clone();
            if a.matches(b, &mut g) {
                if let Ava(name, _) = a {
                    if let Some(old_name) = ava.get(b) {
                        if name != old_name {continue}
                    } else {
                        ava.insert(b.clone(), name.clone());
                    }
                }
                f2 = g;
                matched.insert(i, ());
                found = true;
                break;
            }
        }
        if !found {
            return (false, vec![]);
        }
    }
    *f = f2;
    (true, bn.into_iter().enumerate().filter(|(i, _)| !matched.contains_key(i))
            .map(|(_, b)| b.clone()).collect())
}

impl Rule {
    /// Rewrites a state using the first match of the rule.
    pub fn first(&self, s: &[Expr]) -> Vec<Expr> {
        let ref mut offset = s.iter().map(|s| s.new_nat()).max().unwrap_or(0);
        self.first_offset(s, offset)
    }

    /// Rewrites a state using the first match of the rule, with offset.
    pub fn first_offset(&self, s: &[Expr], offset: &mut u64) -> Vec<Expr> {
        let mut f = HashMap::new();
        if let (true, mut rest) = match_first(&self.0, s, &mut f) {
            let res: Vec<Expr> = self.1.iter().map(|n| n.substitute(&mut |x| {
                if let Some(&y) = f.get(&x) {y}
                else {
                    let res = *offset;
                    *offset += 1;
                    f.insert(x, res);
                    res
                }
            })).collect();
            for v in res.into_iter() {
                rest.push(v);
            }
            rest
        } else {
            s.into()
        }
    }

    /// Rewrites a state using parallel non-overlapping matches.
    pub fn parallel(&self, s: &[Expr]) -> Vec<Expr> {
        let ref mut offset = s.iter().map(|s| s.new_nat()).max().unwrap_or(0);
        self.parallel_offset(s, offset)
    }

    /// Rewrites a state using parallel non-overlapping matches.
    pub fn parallel_offset(&self, s: &[Expr], offset: &mut u64) -> Vec<Expr> {
        let mut f = HashMap::new();
        let mut list = vec![];
        let mut final_rest: Vec<Expr> = s.into();
        while let (true, rest) = match_first(&self.0, &final_rest, &mut f) {
            let res: Vec<Expr> = self.1.iter().map(|n| n.substitute(&mut |x| {
                if let Some(&y) = f.get(&x) {y}
                else {
                    let res = *offset;
                    *offset += 1;
                    f.insert(x, res);
                    res
                }
            })).collect();
            for v in res.into_iter() {
                list.push(v);
            }
            final_rest = rest;
            f = HashMap::new();
        }
        for v in final_rest.into_iter() {
            list.push(v);
        }
        list
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_normal() {
        let a = vec![Nat(0)];
        let rule = Rule(vec![Nat(1)], vec![Nat(1)]);
        assert_eq!(rule.first(&a), vec![Nat(0)]);

        let a = vec![Nat(0)];
        let rule = Rule(vec![Nat(0)], vec![Nat(1)]);
        assert_eq!(rule.first(&a), vec![Nat(1)]);

        let a = vec![Nat(0)];
        let rule = Rule(vec![Nat(1)], vec![Nat(1), Nat(1)]);
        assert_eq!(rule.first(&a), vec![Nat(0), Nat(0)]);

        let a = vec![Nat(0)];
        let rule = Rule(vec![Nat(1)], vec![Nat(1), Nat(2)]);
        assert_eq!(rule.first(&a), vec![Nat(0), Nat(1)]);

        let a = vec![Nat(0)];
        let rule = Rule(vec![Nat(0)], vec![Nat(0)]);
        assert_eq!(rule.first(&a), vec![Nat(0)]);

        let a = vec![Nat(0)];
        let rule = Rule(vec![Nat(0)], vec![Nat(1)]);
        assert_eq!(rule.first(&a), vec![Nat(1)]);

        let a = vec![Hyp(vec![Nat(0)])];
        let rule = Rule(vec![Nat(0)], vec![Nat(1)]);
        assert_eq!(rule.first(&a), vec![Hyp(vec![Nat(0)])]);

        let a = vec![Nat(0), Nat(0)];
        let rule = Rule(vec![Nat(1), Nat(1)], vec![Nat(1)]);
        assert_eq!(rule.first(&a), vec![Nat(0)]);

        let a = vec![Nat(0)];
        let rule = Rule(vec![Nat(1), Nat(1)], vec![Nat(1)]);
        assert_eq!(rule.first(&a), vec![Nat(0)]);
    }

    #[test]
    fn test_parallel() {
        let a = vec![Nat(0), Nat(0)];
        let rule = Rule(vec![Nat(0)], vec![Nat(1)]);
        assert_eq!(rule.first(&a), vec![Nat(0), Nat(1)]);
        assert_eq!(rule.parallel(&a), vec![Nat(1), Nat(2)]);
    }

    #[test]
    fn test_avatar() {
        let a = vec![Nat(0)];
        let rule = Rule(vec![ava("a", 1)], vec![Nat(1)]);
        assert_eq!(rule.first(&a), vec![Nat(0)]);

        let a = vec![Nat(0)];
        let rule = Rule(vec![ava("a", 1), ava("b", 2)], vec![Nat(3)]);
        assert_eq!(rule.first(&a), vec![Nat(0)]);

        let a = vec![Nat(0)];
        let rule = Rule(vec![ava("a", 1), ava("a", 2)], vec![Nat(3)]);
        assert_eq!(rule.first(&a), vec![Nat(0)]);

        let a = vec![Nat(0), Nat(0)];
        let rule = Rule(vec![ava("a", 1), ava("a", 2)], vec![Nat(3)]);
        assert_eq!(rule.first(&a), vec![Nat(1)]);

        let a = vec![Nat(0), Nat(0)];
        let rule = Rule(vec![ava("a", 1), ava("b", 2)], vec![Nat(3)]);
        assert_eq!(rule.first(&a), vec![Nat(0), Nat(0)]);

        let a = vec![Nat(0), Nat(0)];
        let rule = Rule(vec![ava("a", 1), Nat(1)], vec![Nat(2)]);
        assert_eq!(rule.first(&a), vec![Nat(1)]);

        let a = vec![Nat(0), Nat(0)];
        let rule = Rule(vec![Nat(1), ava("a", 1)], vec![Nat(2)]);
        assert_eq!(rule.first(&a), vec![Nat(1)]);
    }

    #[test]
    fn test_format() {
        let a = Nat(0);
        assert_eq!(format!("{}", a), "0".to_string());

        let a = Hyp(vec![Nat(0), Nat(1)]);
        assert_eq!(format!("{}", a), r#"{0,1}"#.to_string());

        let a = ava("a", 0);
        assert_eq!(format!("{}", a), "a'(0)".to_string());

        let rule = Rule(vec![ava("a", 0), ava("b", 1)], vec![Nat(2)]);
        assert_eq!(format!("{}", rule), r#"{a'(0),b'(1)} -> {2}"#.to_string());
    }

    #[test]
    fn test_binary_tree() {
        let a = vec![Hyp(vec![Nat(0), Nat(0)])];
        assert_eq!(format(&a), r#"{{0,0}}"#.to_string());
        let rule = Rule(vec![Hyp(vec![Nat(0), Nat(0)])],
                        vec![
                            Hyp(vec![Nat(1), Nat(1)]),
                            Hyp(vec![Nat(1), Nat(1)]),
                            Hyp(vec![Nat(0), Nat(1)]),
                        ]);
        assert_eq!(format!("{}", rule), r#"{{0,0}} -> {{1,1},{1,1},{0,1}}"#.to_string());
        let a2 = rule.parallel(&a);
        assert_eq!(format(&a2), r#"{{1,1},{1,1},{0,1}}"#.to_string());
        let a3 = rule.parallel(&a2);
        assert_eq!(format(&a3), r#"{{2,2},{2,2},{1,2},{3,3},{3,3},{1,3},{0,1}}"#.to_string());
    }

    #[test]
    fn test_binary_tree_avatar() {
        let a = vec![Hyp(vec![Nat(0), Nat(0)]), Hyp(vec![Nat(1), Nat(1)])];
        assert_eq!(format(&a), r#"{{0,0},{1,1}}"#.to_string());
        let rule = Rule(vec![
                            ava("a", Hyp(vec![Nat(0), Nat(0)])),
                            ava("b", Hyp(vec![Nat(1), Nat(1)]))
                        ],
                        vec![
                            Hyp(vec![Nat(2), Nat(2)]),
                            Hyp(vec![Nat(2), Nat(2)]),
                            Hyp(vec![Nat(0), Nat(2)]),
                            Hyp(vec![Nat(3), Nat(3)]),
                            Hyp(vec![Nat(3), Nat(3)]),
                            Hyp(vec![Nat(1), Nat(3)]),
                        ]);
        assert_eq!(format!("{}", rule),
            r#"{a'({0,0}),b'({1,1})} -> {{2,2},{2,2},{0,2},{3,3},{3,3},{1,3}}"#.to_string());

        let a = rule.parallel(&a);
        assert_eq!(format(&a), r#"{{2,2},{2,2},{0,2},{3,3},{3,3},{1,3}}"#.to_string());
        let a = rule.parallel(&a);
        assert_eq!(format(&a), r#"{{4,4},{4,4},{2,4},{5,5},{5,5},{3,5},{6,6},{6,6},{2,6},{7,7},{7,7},{3,7},{0,2},{1,3}}"#.to_string());
    }

    #[test]
    fn test_binary_tree_avatar2() {
        let a = vec![Hyp(vec![Nat(0), Nat(0)]), Hyp(vec![Nat(1), Nat(1)])];
        assert_eq!(format(&a), r#"{{0,0},{1,1}}"#.to_string());
        let rule = Rule(vec![
                            ava("a", Hyp(vec![Nat(0), Nat(0)])),
                            ava("b", Hyp(vec![Nat(1), Nat(1)]))
                        ],
                        vec![
                            Hyp(vec![Nat(2), Nat(2)]),
                            Hyp(vec![Nat(2), Nat(2)]),
                            Hyp(vec![Nat(0), Nat(2)]),
                            Hyp(vec![Nat(1), Nat(3)]),
                        ]);
        assert_eq!(format!("{}", rule),
            r#"{a'({0,0}),b'({1,1})} -> {{2,2},{2,2},{0,2},{1,3}}"#.to_string());

        let a = rule.parallel(&a);
        assert_eq!(format(&a), r#"{{2,2},{2,2},{0,2},{1,3}}"#.to_string());
        let a = rule.parallel(&a);
        assert_eq!(format(&a), r#"{{2,2},{2,2},{0,2},{1,3}}"#.to_string());
    }

    #[test]
    fn test_skip() {
        let a = vec![Hyp(vec![Nat(0), Nat(0), Nat(0)])];
        let rule = Rule(vec![Hyp(vec![Nat(0), Nat(0)])], vec![Nat(0)]);
        assert_eq!(format(&rule.parallel(&a)), r#"{{0,0,0}}"#.to_string());

        let a = vec![Hyp(vec![Nat(0), Nat(1), Hyp(vec![Nat(2), Nat(3)])])];
        let rule = Rule(vec![Hyp(vec![Hyp(vec![Nat(2), Nat(3)]), Nat(0), Nat(1)])], vec![Nat(0)]);
        assert_eq!(format(&rule.parallel(&a)), r#"{{0,1,{2,3}}}"#.to_string());
    }
}
