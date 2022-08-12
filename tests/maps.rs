use egg::{rewrite, CostFunction, Id, Language};
use egg_sketches::eclass_extract_sketch;

type Lang = egg::SymbolLang;
type EGraph = egg::EGraph<Lang, ()>;
type Rewrite = egg::Rewrite<Lang, ()>;
type Expr = egg::RecExpr<Lang>;
type Sketch = egg_sketches::Sketch<Lang>;

// f o g = (o f g)
// semantic: \x. f (g x)
// map n f = (m n f)
// semantic: [x1, .., xn]
//        => [f x1, .., f xn]
// transpose = T
// semantic: [[x11, .., x1n], .., [xm1, .., xmn]]
//        => [[x11, .., xm1], .., [x1n, .., xmn]]
// split n = (s n)
// semantic: [x1, .., xn, .., xm]
//        => [[x1, .., xn], .., [.., xm]]
// join = j
// semantic: [[x11, .., x1n], .., [xm1, .., xmn]]
//        => [x11, .., x1n, .., xm1, .., xmn]

// T o T = id
// j o (s n) = id

#[rustfmt::skip]
pub fn common_rules() -> Vec<Rewrite> { vec![
    rewrite!("o-assoc1"; "(o (o ?f ?g) ?h)" => "(o ?f (o ?g ?h))"),
    rewrite!("o-assoc2"; "(o ?f (o ?g ?h))" => "(o (o ?f ?g) ?h)"),
    rewrite!("map-fusion"; "(o (m ?n ?f) (m ?n ?g))" => "(m ?n (o ?f ?g))"),
    rewrite!("map-fission"; "(m ?n (o ?f ?g))" =>  "(o (m ?n ?f) (m ?n ?g))"),
    // unused rules:
    // rewrite!("transpose-before-maps"; "(o T (m ?n1 (m ?n2 ?f)))" => "(o (m ?n1 (m ?n2 ?f)) T)"),
    // rewrite!("transpose-after-maps"; "(o (m ?n1 (m ?n2 ?f)) T)" => "(o T (m ?n1 (m ?n2 ?f)))"),
] }

#[rustfmt::skip]
fn transpose_maps() -> Vec<Rewrite> { vec![
    rewrite!("transpose-maps"; "(m ?n1 (m ?n2 ?f))" => "(o T (o (m ?n2 (m ?n1 ?f)) T))"),
    // shortcut rules:
    // rewrite!("transpose-maps-2"; "(m ?n1 (m ?n2 (m ?n3 ?f)))" => "(o (m ?n1 T) (o (m ?n1 (m ?n3 (m ?n2 ?f))) (m ?n1 T))"),
    // rewrite!("transpose-maps-3"; "(m ?n1 (m ?n2 (m ?n3 (m ?n4 ?f))))" => "(o (m ?n1 (m ?n2 T)) (o (m ?n1 (m ?n2 (m ?n4 (m ?n3 ?f)))) (m ?n1 (m ?n2 T))"),
] }

fn split_map() -> Rewrite {
    rewrite!("split-map"; "(m (* ?n1 ?n2) ?f)" => "(o j (o (m ?n1 (m ?n2 ?f)) (s ?n2)))")
}

#[test]
pub fn reorder_3d() {
    let mut rules = common_rules();
    rules.extend(transpose_maps().into_iter());

    // 3 nested maps that we want to reorder:
    let start: Expr = "(m n1 (m n2 (m n3 f)))".parse().unwrap();

    // sketches for the reordered map nests we are looking for:
    #[rustfmt::skip]
    let sketches: &[Sketch] = &[
        "(contains (m n1 (m n3 (m n2 f))))".parse().unwrap(),
        "(contains (m n2 (m n1 (m n3 f))))".parse().unwrap(),
        "(contains (m n2 (m n3 (m n1 f))))".parse().unwrap(),
        "(contains (m n3 (m n2 (m n1 f))))".parse().unwrap(),
        "(contains (m n3 (m n1 (m n2 f))))".parse().unwrap(),
    ];

    // the corresponding full programs that we expect to find:
    #[rustfmt::skip]
    let goals: &[Expr] = &[
        "(o (m n1 T) (o (m n1 (m n3 (m n2 f))) (m n1 T)))".parse().unwrap(),
        "(o T (o (m n2 (m n1 (m n3 f))) T))".parse().unwrap(),
        "(o (o T (m n2 T)) (o (m n2 (m n3 (m n1 f))) (o (m n2 T) T)))".parse().unwrap(),
        // "(o (m n1 T) (o (o T (o (o (m n3 T) (o (m n3 (m n2 (m n1 f))) (m n3 T))) T)) (m n1 T)))".parse().unwrap(),
        // eqsat found better:
        "(o (o (o (o T (m n2 T)) T) (o (m n3 (m n2 (m n1 f))) (o T (m n2 T)))) T)".parse().unwrap(),
        "(o (m n1 T) (o (o T (o (m n3 (m n1 (m n2 f))) T)) (m n1 T)))".parse().unwrap(),
    ];

    // grow an e-graph to explore different ways to rewrite `start`
    let mut egraph = EGraph::default();
    let eclass = egraph.add_expr(&start);
    let egraph = grow_egraph(egraph, 50_000, &rules[..]);

    // extract the smallest programs from the e-graph that satisfy our sketches,
    // and check that they correspond to the expected full programs:
    for (sketch, goal) in sketches.iter().zip(goals.iter()) {
        sketch_extract_and_check(&egraph, eclass, sketch, goal);
    }
}

#[test]
#[ignore] // takes > 1mn
pub fn tile_3d() {
    // 3 nested maps that we want to tile (split + reorder):
    let start: Expr = "(m (* n1 32) (m (* n2 32) (m (* n3 32) f)))"
        .parse()
        .unwrap();

    // sketches for the splitted map nests we are looking for:
    #[rustfmt::skip]
    let split_sketches: &[Sketch] = &[
        "(contains (m n1 (m 32 (m (* n2 32) (m (* n3 32) f)))))".parse().unwrap(),
        "(contains (m (* n1 32) (m n2 (m 32 (m (* n3 32) f)))))".parse().unwrap(),
        "(contains (m (* n1 32) (m (* n2 32) (m n3 (m 32 f)))))".parse().unwrap(),
        "(contains (m n1 (m 32 (contains (m n2 (m 32 (m (* n3 32) f))))))))".parse().unwrap(),
        "(contains (m (* n1 32) (contains (m n2 (m 32 (contains (m n3 (m 32 f)))))))))".parse().unwrap(),
        "(contains (m n1 (m 32 (contains (m n2 (m 32 (contains (m n3 (m 32 f))))))))))".parse().unwrap(),
    ];

    // the corresponding full programs that we expect to find:
    #[rustfmt::skip]
    let split_goals: &[Expr] = &[
        "(o (o j (m n1 (m 32 (m (* n2 32) (m (* n3 32) f))))) (s 32))".parse().unwrap(),
        "(o (m (* n1 32) j) (o (m (* n1 32) (m n2 (m 32 (m (* n3 32) f)))) (m (* n1 32) (s 32))))".parse().unwrap(),
        "(o (m (* n1 32) (m (* n2 32) j)) (o (m (* n1 32) (m (* n2 32) (m n3 (m 32 f)))) (m (* n1 32) (m (* n2 32) (s 32)))))".parse().unwrap(),
        "(o (o j (m n1 (m 32 (o j (o (m n2 (m 32 (m (* n3 32) f))) (s 32)))))) (s 32))".parse().unwrap(),
        "(m (* n1 32) (o j (o (m n2 (m 32 (o j (o (m n3 (m 32 f)) (s 32))))) (s 32))))".parse().unwrap(),
        "(o (o j (m n1 (m 32 (o j (o (m n2 (m 32 (o j (o (m n3 (m 32 f)) (s 32))))) (s 32)))))) (s 32))".parse().unwrap(),
    ];

    let mut split_rules = common_rules();
    split_rules.push(split_map());

    // grow an e-graph to explore different ways to rewrite `start`
    let mut egraph = EGraph::default();
    let eclass = egraph.add_expr(&start);
    let egraph = grow_egraph(egraph, 50_000, &split_rules[..]);

    // extract the smallest programs from the e-graph that satisfy our sketches,
    // and check that they correspond to the expected full programs:
    let split_exprs: Vec<_> = split_sketches
        .iter()
        .zip(split_goals.iter())
        .map(|(sketch, goal)| sketch_extract_and_check(&egraph, eclass, sketch, goal))
        .collect();

    // sketches for the tiled map nests we are looking for:
    #[rustfmt::skip]
    let sketches: &[Sketch] = &[
        "(contains (m n1 (m 32 (m (* n2 32) (m (* n3 32) f)))))".parse().unwrap(),
        "(contains (m (* n1 32) (m n2 (m 32 (m (* n3 32) f)))))".parse().unwrap(),
        "(contains (m (* n1 32) (m (* n2 32) (m n3 (m 32 f)))))".parse().unwrap(),
        "(contains (m n1 (contains (m n2 (m 32 (m 32 (m (* n3 32) f))))))))".parse().unwrap(),
        "(contains (m (* n1 32) (contains (m n2 (contains (m n3 (m 32 (m 32 f)))))))))".parse().unwrap(),
        "(contains (m n1 (contains (m n2 (contains (m n3 (contains (m 32 (m 32 (m 32 f)))))))))))".parse().unwrap(),
    ];

    // the corresponding full programs that we expect to find:
    #[rustfmt::skip]
    let goals: &[Expr] = &[
        "(o j (o (m n1 (m 32 (m (* n2 32) (m (* n3 32) f)))) (s 32)))".parse().unwrap(),
        "(o (m (* n1 32) j) (o (m (* n1 32) (m n2 (m 32 (m (* n3 32) f)))) (m (* n1 32) (s 32))))".parse().unwrap(),
        "(o (o (m (* n1 32) (m (* n2 32) j)) (m (* n1 32) (m (* n2 32) (m n3 (m 32 f))))) (m (* n1 32) (m (* n2 32) (s 32))))".parse().unwrap(),
        "(o j (o (m n1 (o (m 32 j) (o (o T (m n2 (m 32 (m 32 (m (* n3 32) f))))) (o T (m 32 (s 32)))))) (s 32)))".parse().unwrap(),
        "(m (* n1 32) (o j (o (m n2 (o (o (o (m 32 j) T) (m n3 (m 32 (m 32 f)))) (o T (m 32 (s 32))))) (s 32))))".parse().unwrap(),
        "(o j (o (m n1 (o (o (o (m 32 j) T) (o (m n2 (o (m 32 (o (m 32 j) T)) (o (o T (o (m n3 (m 32 (m 32 (m 32 f)))) T)) (m 32 (o T (m 32 (s 32))))))) T)) (m 32 (s 32)))) (s 32)))".parse().unwrap(),
    ];

    let mut reorder_rules = common_rules();
    reorder_rules.extend(transpose_maps().into_iter());

    // grow an e-graph to explore different ways to rewrite `split_exprs`
    let mut egraph = EGraph::default();
    let split_eclasses: Vec<_> = split_exprs.iter().map(|e| egraph.add_expr(e)).collect();
    let egraph = grow_egraph(egraph, 500_000, &reorder_rules[..]);

    // extract the smallest programs from the e-graph that satisfy our sketches,
    // and check that they correspond to the expected full programs:
    for (sketch, (eclass, goal)) in sketches.iter().zip(split_eclasses.iter().zip(goals.iter())) {
        sketch_extract_and_check(&egraph, *eclass, sketch, goal);
    }
}

fn grow_egraph(egraph: EGraph, node_limit: usize, rules: &[Rewrite]) -> EGraph {
    let runner = egg::Runner::default()
        .with_scheduler(egg::SimpleScheduler)
        .with_iter_limit(20)
        .with_node_limit(node_limit)
        .with_egraph(egraph)
        .run(&rules[..]);
    runner.print_report();
    runner.egraph
}

fn sketch_extract_and_check(egraph: &EGraph, eclass: Id, sketch: &Sketch, goal: &Expr) -> Expr {
    let canonic_eclass = egraph.find(eclass);
    assert_eq!(egraph.lookup_expr(goal), Some(canonic_eclass));

    let res = eclass_extract_sketch(sketch, egg::AstSize, &egraph, canonic_eclass);
    let (best_cost, best) = res.unwrap();
    let bs = string_of_expr(&best);
    let gs = string_of_expr(goal);
    println!("{}", bs);
    println!("{}", gs);
    assert_eq!(best_cost, egg::AstSize.cost_rec(&goal));
    assert_eq!(bs, gs);

    best
}

fn string_of_expr(e: &Expr) -> String {
    let mut res = String::new();
    string_of_expr_rec(e.as_ref(), e.as_ref().len() - 1, &mut res);
    res
}

fn string_of_expr_rec(nodes: &[Lang], i: usize, acc: &mut String) {
    use std::fmt::Write;

    let node = &nodes[i];
    let op = node.to_string();

    if op == "o" {
        let cs = node.children();
        string_of_expr_rec(nodes, usize::from(cs[0]), acc);
        write!(acc, " o ").unwrap();
        string_of_expr_rec(nodes, usize::from(cs[1]), acc);
        return;
    }

    if node.is_leaf() {
        write!(acc, "{}", op).unwrap();
        return;
    }

    write!(acc, "({}", op).unwrap();
    for child in node.children().iter().map(|i| usize::from(*i)) {
        write!(acc, " ").unwrap();
        string_of_expr_rec(nodes, child, acc);
    }
    write!(acc, ")").unwrap();
}
