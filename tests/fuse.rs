use egg::{rewrite, CostFunction, Id, Language};
use egg_sketches::eclass_extract_sketch;

type Lang = egg::SymbolLang;
type EGraph = egg::EGraph<Lang, ()>;
type Rewrite = egg::Rewrite<Lang, ()>;
type Expr = egg::RecExpr<Lang>;
type Sketch = egg_sketches::Sketch<Lang>;

// f o g = (o f g)
// semantic: \x. f (g x)
// map f = (m f)
// semantic: [x1, .., xn]
//        => [f x1, .., f xn]
// transpose = T
// semantic: [[x11, .., x1n], .., [xm1, .., xmn]]
//        => [[x11, .., xm1], .., [x1n, .., xmn]]
// split n = S
// semantic: [x1, .., xn, .., xm]
//        => [[x1, .., xn], .., [.., xm]]
// join = J
// semantic: [[x11, .., x1n], .., [xm1, .., xmn]]
//        => [x11, .., x1n, .., xm1, .., xmn]

#[rustfmt::skip]
pub fn common_rules() -> Vec<Rewrite> { vec![
  rewrite!("o-assoc1"; "(o (o ?f ?g) ?h)" => "(o ?f (o ?g ?h))"),
  rewrite!("o-assoc2"; "(o ?f (o ?g ?h))" => "(o (o ?f ?g) ?h)"),
  rewrite!("map-fusion"; "(o (m ?f) (m ?g))" => "(m (o ?f ?g))"),
  rewrite!("map-fission"; "(m (o ?f ?g))" => "(o (m ?f) (m ?g))"),
] }

#[rustfmt::skip]
pub fn m_t_commute() -> Vec<Rewrite> { vec![
  rewrite!("map2-transpose-commute"; "(o (m (m ?f)) T)" => "(o T (m (m ?f)))"),
  rewrite!("transpose-map2-commute"; "(o T (m (m ?f)))" => "(o (m  (m ?f)) T)"),
] }

fn split_map() -> Rewrite {
  rewrite!("split-map"; "(m ?f)" => "(o J (o (m (m ?f)) S))")
}

#[test]
pub fn fuse_through_transpose() {
  let mut rules = common_rules();
  rules.extend(m_t_commute());
  let start: Expr = "(o (o (m (m f)) T) (m (m g)))".parse().unwrap();
  let sketch: Sketch = "(o (m (m ?)) T)".parse().unwrap();
  let goal: Expr = "(o (m (m (o f g))) T)".parse().unwrap();
  let mut egraph = EGraph::default();
  let eclass = egraph.add_expr(&start);
  let egraph = grow_egraph(egraph, 50_000, &rules[..]);
  sketch_extract_and_check(&egraph, eclass, &sketch, &goal);
}

#[test]
pub fn fuse_through_transpose3() {
  let mut rules = common_rules();
  rules.extend(m_t_commute());
  let start: Expr = "(o (o (m (m (m (m f)))) (o (o (m (m T)) (m T)) T)) (m (m (m (m g)))))".parse().unwrap();
  let sketch: Sketch = "(contains (o f g))".parse().unwrap();
  let goal: Expr = "(o (m (o (m (o T (m (m (o f g))))) T)) T)".parse().unwrap();
  let mut egraph = EGraph::default();
  let eclass = egraph.add_expr(&start);
  let egraph = grow_egraph(egraph, 50_000, &rules[..]);
  sketch_extract_and_check(&egraph, eclass, &sketch, &goal);
}

#[test]
pub fn split_join_2() {
  let mut rules = common_rules();
  rules.push(split_map());
  let start: Expr = "(m (m f))".parse().unwrap();
  let sketch: Sketch = "(o (m J) (o (m (m (m f))) (m S)))".parse().unwrap();
  let goal: Expr = "(o (m J) (o (m (m (m f))) (m S)))".parse().unwrap();
  let mut egraph = EGraph::default();
  let eclass = egraph.add_expr(&start);
  let egraph = grow_egraph(egraph, 50_000, &rules[..]);
  sketch_extract_and_check(&egraph, eclass, &sketch, &goal);
}

#[test]
pub fn split_join_4() {
  let mut rules = common_rules();
  rules.push(split_map());
  let start: Expr = "(m (m (m (m f))))".parse().unwrap();
  let sketch: Sketch = "(o (m (m (m J))) (o (m (m (m (m (m f))))) (m (m (m S)))))".parse().unwrap();
  let goal: Expr = "(o (m (m (m J))) (o (m (m (m (m (m f))))) (m (m (m S)))))".parse().unwrap();
  let mut egraph = EGraph::default();
  let eclass = egraph.add_expr(&start);
  let egraph = grow_egraph(egraph, 100_000, &rules[..]);
  sketch_extract_and_check(&egraph, eclass, &sketch, &goal);
}

#[test]
pub fn split_join_6() {
  let mut rules = common_rules();
  rules.push(split_map());
  let start: Expr = "(m (m (m (m (m (m f))))))".parse().unwrap();
  
  let sketch: Sketch = "(m (m (m (o (m (m J)) (o (m (m (m (m f)))) (m (m S)))))))".parse().unwrap();
  let goal: Expr = "(m (m (m (o (m (m J)) (o (m (m (m (m f)))) (m (m S)))))))".parse().unwrap();
  let mut egraph = EGraph::default();
  let eclass = egraph.add_expr(&start);
  let egraph = grow_egraph(egraph, 50_000, &rules[..]);
  sketch_extract_and_check(&egraph, eclass, &sketch, &goal);
  
  let start = goal;
  let sketch: Sketch = "(o (m (m (m (m (m J))))) (o (m (m (m (m (m (m (m f))))))) (m (m (m (m (m S)))))))".parse().unwrap();
  let goal: Expr = "(o (m (m (m (m (m J))))) (o (m (m (m (m (m (m (m f))))))) (m (m (m (m (m S)))))))".parse().unwrap();
  let mut egraph = EGraph::default();
  let eclass = egraph.add_expr(&start);
  let egraph = grow_egraph(egraph, 50_000, &rules[..]);
  sketch_extract_and_check(&egraph, eclass, &sketch, &goal);
}

// FIXME: following code is duplicated from 'tile.rs'

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

  let res = eclass_extract_sketch(sketch, egg::AstSize, &egraph, canonic_eclass);
  let (best_cost, best) = res.unwrap();
  let bs = string_of_expr(&best);
  let gs = string_of_expr(goal);
  println!("{}", bs);
  println!("{}", gs);
  assert_eq!(egraph.lookup_expr(goal), Some(canonic_eclass));
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
