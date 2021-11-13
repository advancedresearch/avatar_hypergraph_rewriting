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
