use std::env;

use egg::{rewrite, CostFunction, Id, Language};
use egg_sketches::*;

use memory_stats::memory_stats;

type Lang = egg::SymbolLang;
type EGraph = egg::EGraph<Lang, ()>;
type Rewrite = egg::Rewrite<Lang, ()>;
type Runner = egg::Runner<Lang, ()>;
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

fn reach_sketches_from_exprs(
    starts: &[Expr],
    rules: &[Rewrite],
    sketch_goals: &[Sketch],
    expected_goals: &[Expr]) -> Vec<Expr>
{
    let mut egraph = EGraph::default();
    let eclass = starts.iter()
        .map(|e| egraph.add_expr(e))
        .collect::<Vec<_>>().into_iter()
        .reduce(|a, b| { egraph.union(a, b); a })
        .expect("need at least one starting expression");
    let sketches_hook = sketch_goals.to_owned();
    let egraph = grow_egraph_until(egraph, rules, move |r| {
        let cano_eclass = r.egraph.find(eclass);
        sketches_hook.iter().all(|s| {
            eclass_extract_sketch(s, egg::AstSize, &r.egraph, cano_eclass).is_some()
            // FIXME:
            // eclass_satisfies_sketch(s, &r.egraph, cano_eclass)
        })
    });
    
    let cano_eclass = egraph.find(eclass);
    sketch_goals.iter().zip(expected_goals.iter())
        .map(|(sketch, expected)| sketch_extract_and_check(&egraph, cano_eclass, sketch, expected))
        .collect()
}

pub fn tile(
    start: &str,
    split_sketches: &[&str],
    split_expected: &[&str],
    reorder_sketches: &[&str],
    reorder_expected: &[&str],
) -> Vec<Expr> {

    let mut split_rules = common_rules();
    split_rules.push(split_map());
    let ss: Vec<Sketch> = split_sketches.iter().map(|s| s.parse::<Sketch>().unwrap()).collect();
    let se: Vec<Expr> = split_expected.iter().map(|&s| s.parse::<Expr>().unwrap()).collect();

    let mut reorder_rules = common_rules();
    reorder_rules.extend(transpose_maps().into_iter());
    let rs: Vec<Sketch> = reorder_sketches.iter().map(|&s| s.parse::<Sketch>().unwrap()).collect();
    let re: Vec<Expr> = reorder_expected.iter().map(|&s| s.parse::<Expr>().unwrap()).collect();

    let split_exprs = reach_sketches_from_exprs(
        &[start.parse().unwrap()],
        &split_rules[..], &ss[..], &se[..]
    );
    reach_sketches_from_exprs(
        &split_exprs[..],
        &reorder_rules[..], &rs[..], &re[..]
    )
}

pub fn tile_1d() -> Vec<Expr> {
    vec![]
}

pub fn tile_2d() -> Vec<Expr> {
    vec![]
}

#[rustfmt::skip]
pub fn reorder_3d() -> Vec<Expr> {
    let mut rules = common_rules();
    rules.extend(transpose_maps().into_iter());

    reach_sketches_from_exprs(
        // 3 nested maps that we want to reorder:
        &[ "(m n1 (m n2 (m n3 f)))".parse().unwrap() ],
        &rules[..],
        // sketches for the reordered map nests we are looking for:
        &[
            "(contains (m n1 (m n3 (m n2 f))))".parse().unwrap(),
            "(contains (m n2 (m n1 (m n3 f))))".parse().unwrap(),
            "(contains (m n2 (m n3 (m n1 f))))".parse().unwrap(),
            "(contains (m n3 (m n2 (m n1 f))))".parse().unwrap(),
            "(contains (m n3 (m n1 (m n2 f))))".parse().unwrap(),
        ],
        // the corresponding full programs that we expect to find:
        &[
            "(o (m n1 T) (o (m n1 (m n3 (m n2 f))) (m n1 T)))".parse().unwrap(),
            "(o T (o (m n2 (m n1 (m n3 f))) T))".parse().unwrap(),
            "(o (o T (m n2 T)) (o (m n2 (m n3 (m n1 f))) (o (m n2 T) T)))".parse().unwrap(),
            "(o (o (o (o T (m n2 T)) T) (o (m n3 (m n2 (m n1 f))) (o T (m n2 T)))) T)".parse().unwrap(),
            "(o (m n1 T) (o (o T (o (m n3 (m n1 (m n2 f))) T)) (m n1 T)))".parse().unwrap(),
        ]
    )
}

#[rustfmt::skip]
pub fn tile_3d() -> Vec<Expr> {
    tile(
        // 3 nested maps that we want to tile (split + reorder):
        "(m (* n1 32) (m (* n2 32) (m (* n3 32) f)))",
        // sketches for the splitted map nests we are looking for:
        &[
            "(contains (m n1 (m 32 (m (* n2 32) (m (* n3 32) f)))))",
            "(contains (m (* n1 32) (m n2 (m 32 (m (* n3 32) f)))))",
            "(contains (m (* n1 32) (m (* n2 32) (m n3 (m 32 f)))))",
            "(contains (m n1 (m 32 (contains (m n2 (m 32 (m (* n3 32) f))))))))",
            "(contains (m (* n1 32) (contains (m n2 (m 32 (contains (m n3 (m 32 f)))))))))",
            "(contains (m n1 (m 32 (contains (m n2 (m 32 (contains (m n3 (m 32 f))))))))))",
        ],
        // the corresponding full programs that we expect to find:
        &[
            "(o (o j (m n1 (m 32 (m (* n2 32) (m (* n3 32) f))))) (s 32))",
            "(o (m (* n1 32) j) (o (m (* n1 32) (m n2 (m 32 (m (* n3 32) f)))) (m (* n1 32) (s 32))))",
            "(o (m (* n1 32) (m (* n2 32) j)) (o (m (* n1 32) (m (* n2 32) (m n3 (m 32 f)))) (m (* n1 32) (m (* n2 32) (s 32)))))",
            "(o (o j (m n1 (m 32 (o j (o (m n2 (m 32 (m (* n3 32) f))) (s 32)))))) (s 32))",
            "(m (* n1 32) (o j (o (m n2 (m 32 (o j (o (m n3 (m 32 f)) (s 32))))) (s 32))))",
            "(o (o j (m n1 (m 32 (o j (o (m n2 (m 32 (o j (o (m n3 (m 32 f)) (s 32))))) (s 32)))))) (s 32))",
        ],
        // sketches for the tiled map nests we are looking for:
        &[
            "(contains (m n1 (m 32 (m (* n2 32) (m (* n3 32) f)))))",
            "(contains (m (* n1 32) (m n2 (m 32 (m (* n3 32) f)))))",
            "(contains (m (* n1 32) (m (* n2 32) (m n3 (m 32 f)))))",
            "(contains (m n1 (contains (m n2 (m 32 (m 32 (m (* n3 32) f))))))))",
            "(contains (m (* n1 32) (contains (m n2 (contains (m n3 (m 32 (m 32 f)))))))))",
            "(contains (m n1 (contains (m n2 (contains (m n3 (contains (m 32 (m 32 (m 32 f)))))))))))",
        ],
        // the corresponding full programs that we expect to find:
        &[
            "(o j (o (m n1 (m 32 (m (* n2 32) (m (* n3 32) f)))) (s 32)))",
            "(o (m (* n1 32) j) (o (m (* n1 32) (m n2 (m 32 (m (* n3 32) f)))) (m (* n1 32) (s 32))))",
            "(o (o (m (* n1 32) (m (* n2 32) j)) (m (* n1 32) (m (* n2 32) (m n3 (m 32 f))))) (m (* n1 32) (m (* n2 32) (s 32))))",
            "(o j (o (m n1 (o (m 32 j) (o (o T (m n2 (m 32 (m 32 (m (* n3 32) f))))) (o T (m 32 (s 32)))))) (s 32)))",
            "(m (* n1 32) (o j (o (m n2 (o (o (o (m 32 j) T) (m n3 (m 32 (m 32 f)))) (o T (m 32 (s 32))))) (s 32))))",
            "(o j (o (m n1 (o (o (o (m 32 j) T) (o (m n2 (o (m 32 (o (m 32 j) T)) (o (o T (o (m n3 (m 32 (m 32 (m 32 f)))) T)) (m 32 (o T (m 32 (s 32))))))) T)) (m 32 (s 32)))) (s 32)))",
        ],
    )
}

fn grow_egraph_until<S>(egraph: EGraph, rules: &[Rewrite], mut satisfied: S) -> EGraph
  where S: FnMut(&mut Runner) -> bool + 'static
{
    let runner = egg::Runner::default()
        .with_scheduler(egg::SimpleScheduler)
        .with_iter_limit(100)
        .with_node_limit(10_000_000)
        .with_time_limit(std::time::Duration::from_secs(5 * 60))
        .with_hook(move |runner| {
          let memory = memory_stats().expect("could not get current memory usage");
          let out_of_memory = memory.virtual_mem > 8_000_000_000;
          println!("current physical memory usage: {}", memory.physical_mem);
          println!("current virtual memory usage: {}", memory.virtual_mem);

          if let Some(it) = runner.iterations.last() {
            println!("current e-graph nodes: {}", it.egraph_nodes);
            println!("current e-graph classes: {}", it.egraph_classes);
            println!("applied rules: {}", it.applied.iter().map(|(_, &n)| n).sum::<usize>());
            println!("time spent: {} ({} hook + {} search + {} apply + {} rebuild)", it.total_time, it.hook_time, it.search_time, it.apply_time, it.rebuild_time);
          }

          if satisfied(runner) {
            Err(String::from("Satisfied"))
          } else if out_of_memory {
            Err(String::from("Out of Memory"))
          } else {
            Ok(())
          }
        })
        .with_egraph(egraph)
        .run(&rules[..]);
    runner.print_report();
    runner.egraph
}

fn sketch_extract_and_check(egraph: &EGraph, eclass: Id, sketch: &Sketch, goal: &Expr) -> Expr {
    let canonic_eclass = egraph.find(eclass);

    let res = eclass_extract_sketch(sketch, egg::AstSize, &egraph, canonic_eclass);
    let (best_cost, best) = res.unwrap();
    let bs = string_of_expr(&best);
    let gs = string_of_expr(goal);
    // println!("{}", bs);
    // println!("{}", gs);
    assert_eq!(best_cost, egg::AstSize.cost_rec(&goal));
    assert_eq!(bs, gs);
    // assert_eq!(egraph.lookup_expr(goal), Some(canonic_eclass));

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

fn main() {
    let args: Vec<String> = env::args().collect();
    assert_eq!(args.len(), 2);

    match args[1].as_str() {
        // "split_1d" => split_1d(),
        // "reorder_1d" => reorder_1d(),
        "tile_1d" => tile_1d(),
        // "split_2d" => split_2d(),
        // "reorder_2d" => reorder_2d(),
        "tile_2d" => tile_2d(),
        // "split_3d" => split_3d(),
        "reorder_3d" => reorder_3d(),
        "tile_3d" => tile_3d(),
        _ => panic!("unknown parameter")
    };
}