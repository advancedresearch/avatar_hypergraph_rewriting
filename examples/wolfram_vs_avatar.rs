# Avatar Hypergraph Rewriting
Hypergraph rewriting system with avatars for symbolic distinction

Based on paper [Avatar Hypergraph Rewriting](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/avatar-hypergraph-rewriting.pdf).

Avatars can be used on the left side of rewriting rules to control
symbolic distinction of nodes in the hypergraph evolution.
They can be used on any hyperedge.

### Example: Wolfram vs Avatar

```rust
use avatar_hypergraph_rewriting::*;

use Expr::*;

fn main() {
    // `{0,0}`
   let a = vec![Nat(0), Nat(0)];

    // `{1,2} -> {}`
    let wolfram_rule = Rule(vec![Nat(1), Nat(2)], vec![]);
    // prints `{}` because `{0,0}` is reduced.
    println!("{}", format(&wolfram_rule.parallel(&a)));

    // `{a'(1),b'(2)} -> {}`
    let avatar_rule = Rule(vec![ava("a", 1), ava("b", 2)], vec![]);
    // prints `{0,0}` because avatars "a" and "b" must be different nodes.
    println!("{}", format(&avatar_rule.parallel(&a)));
}
```

### Motivation

Avatar Hypergraph Rewriting (AHR) is an attempt to find an
[Avatar Extension](https://advancedresearch.github.io/avatar-extensions/summary.html)
of Wolfram models that satisfies the assumptions in the paper
[Consciousness in Wolfram Models](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/consciousness-in-wolfram-models.pdf).

Wolfram models are used in the [Wolfram Physics Project](https://wolframphysics.org/),
which seeks to explain fundamental physics
using a hypergraph rewriting system.

Wolfram models correspond to theorem proving with
[Intuitionistic Propositional Logic](https://en.wikipedia.org/wiki/Intuitionistic_logic) (IPL),
which can be generalised to Homotopy Type Theory.
For more information, see [this paper](https://arxiv.org/abs/2111.03460) by
Xerxes D. Arsiwalla and Jonathan Gorard.

IPL is the foundation for Type Theory and modern mathematical foundations.
IPL is weaker than
[Propositional Logic](https://en.wikipedia.org/wiki/Propositional_calculus) (PL).

- PL is called "classical" logic and satisfies a Boolean algebra
- IPL is called "constructive" logic and satisifes a Heyting algebra

However, in [Path Semantics](https://github.com/advancedresearch/path_semantics)
there is an even weaker logic called Path Semantical Intuitionistic Propositional Logic (PSI).

PSI is much less understood than IPL and PL,
but is relevant for the philosophy of mathematical language design.
One thing that makes PSI different from IPL is that a quality operator `~~`
lifts biconditions with symbolic distinction (quality is a partial equivalence).

A closely related research topic to PSI is
[Avatar Extensions](https://advancedresearch.github.io/avatar-extensions/summary.html).

This hypergraph rewriting system combines the property of symbolic distinction with avatars.
The avatars is a design choice to express symbolic distinction efficiently.
