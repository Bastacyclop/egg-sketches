use egg::{rewrite as rw, *};
use ordered_float::NotNan;
use egg_sketches::eclass_extract_sketch;


define_language! {
    pub enum Lang {
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        //"/" = Div([Id; 2]),
        "pow" = Pow([Id; 2]),
        Constant(Constant),
        Symbol(Symbol), // Would this maybe work for unknowns/variables?
    }
}

pub type EGraph = egg::EGraph<Lang, ConstantFold>;
pub type Rewrite = egg::Rewrite<Lang, ConstantFold>;
pub type Constant = NotNan<f64>;
type Expr = egg::RecExpr<Lang>;
type Sketch = egg_sketches::Sketch<Lang>;

// You could use egg::AstSize, but this is useful for debugging, since
// it will really try to get rid of the Diff operator

#[derive(Default)]
pub struct ConstantFold;
impl Analysis<Lang> for ConstantFold {
    type Data = Option<(Constant, PatternAst<Lang>)>;

    fn make(egraph: &EGraph, enode: &Lang) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.as_ref().map(|d| d.0);
        Some(match enode {
            Lang::Constant(c) => (*c, format!("{}", c).parse().unwrap()),
            Lang::Add([a, b]) => (
                x(a)? + x(b)?,
                format!("(+ {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            Lang::Sub([a, b]) => (
                x(a)? - x(b)?,
                format!("(- {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            Lang::Mul([a, b]) => (
                x(a)? * x(b)?,
                format!("(* {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            //Lang::Div([a, b]) if x(b) != Some(NotNan::new(0.0).unwrap()) => (
            //    x(a)? / x(b)?,
            //    format!("(/ {} {})", x(a)?, x(b)?).parse().unwrap(),
            //),
            _ => return None,
        })
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        merge_option(to, from, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            DidMerge(false, false)
        })
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        let class = egraph[id].clone();
        if let Some((c, pat)) = class.data {
            if egraph.are_explanations_enabled() {
                egraph.union_instantiations(
                    &pat,
                    &format!("{}", c).parse().unwrap(),
                    &Default::default(),
                    "constant_fold".to_string(),
                );
            } else {
                let added = egraph.add(Lang::Constant(c));
                egraph.union(id, added);
            }
            // to not prune, comment this out
            egraph[id].nodes.retain(|n| n.is_leaf());

            #[cfg(debug_assertions)]
            egraph[id].assert_unique_leaves();
        }
    }
}

fn is_const_or_distinct_var(v: &str, w: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let v = v.parse().unwrap();
    let w = w.parse().unwrap();
    move |egraph, _, subst| {
        egraph.find(subst[v]) != egraph.find(subst[w])
            && (egraph[subst[v]].data.is_some()
                || egraph[subst[v]]
                    .nodes
                    .iter()
                    .any(|n| matches!(n, Lang::Symbol(..))))
    }
}

fn is_const(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| egraph[subst[var]].data.is_some()
}

fn is_sym(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        egraph[subst[var]]
            .nodes
            .iter()
            .any(|n| matches!(n, Lang::Symbol(..)))
    }
}

fn is_not_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some(n) = &egraph[subst[var]].data {
            *(n.0) != 0.0
        } else {
            true
        }
    }
}

#[rustfmt::skip]
pub fn rules() -> Vec<Rewrite> { vec![
    rw!("comm-add";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
    rw!("comm-mul";  "(* ?a ?b)"        => "(* ?b ?a)"),
    rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
    rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
    rw!("add-assoc"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
    rw!("mul-assoc"; "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),

    rw!("sub-canon"; "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
    rw!("canon-sub"; "(+ ?a (* -1 ?b))" => "(- ?a ?b)" ),
    //rw!("div-canon"; "(/ ?a ?b)" => "(* ?a (pow ?b -1))" if is_not_zero("?b")),
    // rw!("canon-sub"; "(+ ?a (* -1 ?b))"   => "(- ?a ?b)"),
    // rw!("canon-div"; "(* ?a (pow ?b -1))" => "(/ ?a ?b)" if is_not_zero("?b")),

    rw!("zero-add"; "(+ ?a 0)" => "?a"),
    rw!("zero-mul"; "(* ?a 0)" => "0"),
    rw!("one-mul";  "(* ?a 1)" => "?a"),

    rw!("add-zero"; "?a" => "(+ ?a 0)"),
    rw!("mul-one";  "?a" => "(* ?a 1)"),

    rw!("cancel-sub"; "(- ?a ?a)" => "0"),
    //rw!("cancel-div"; "(/ ?a ?a)" => "1" if is_not_zero("?a")),

    rw!("distribute"; "(* ?a (+ ?b ?c))"        => "(+ (* ?a ?b) (* ?a ?c))"),
    rw!("factor"    ; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),

    rw!("pow-mul"; "(* (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (+ ?b ?c))"),
    rw!("pow0"; "(pow ?x 0)" => "1"
        if is_not_zero("?x")),
    rw!("pow1"; "(pow ?x 1)" => "?x"), // do we need the converse?
    rw!("pow2"; "(pow ?x 2)" => "(* ?x ?x)"),
    rw!("pow3"; "(pow ?x 3)" => "(* ?x (pow ?x 2))"),
    rw!("pow4"; "(pow ?x 4)" => "(* (pow ?x 2) (pow ?x 2))"),
    rw!("1pow"; "?x" => "(pow ?x 1)"),
    rw!("2pow"; "(* ?x ?x)" => "(pow ?x 2)"),
    rw!("3pow"; "(* ?x (pow ?x 2))" => "(pow ?x 3)"),
    rw!("4pow"; "(* (pow ?x 2) (pow ?x 2))" => "(pow ?x 4)"),
    //rw!("pow-recip"; "(pow ?x -1)" => "(/ 1 ?x)"
    //    if is_not_zero("?x")),
    //rw!("recip-mul-div"; "(* ?x (/ 1 ?x))" => "1" if is_not_zero("?x")),

    //rw!("d-variable"; "(d ?x ?x)" => "1" if is_sym("?x")),
    //rw!("d-constant"; "(d ?x ?c)" => "0" if is_sym("?x") if is_const_or_distinct_var("?c", "?x")),

    //rw!("d-add"; "(d ?x (+ ?a ?b))" => "(+ (d ?x ?a) (d ?x ?b))"),
    //rw!("d-mul"; "(d ?x (* ?a ?b))" => "(+ (* ?a (d ?x ?b)) (* ?b (d ?x ?a)))"),

    //rw!("d-sin"; "(d ?x (sin ?x))" => "(cos ?x)"),
    //rw!("d-cos"; "(d ?x (cos ?x))" => "(* -1 (sin ?x))"),

    //rw!("d-ln"; "(d ?x (ln ?x))" => "(/ 1 ?x)" if is_not_zero("?x")),

    //rw!("d-power";
    //    "(d ?x (pow ?f ?g))" =>
    //    "(* (pow ?f ?g)
    //        (+ (* (d ?x ?f)
    //              (/ ?g ?f))
    //           (* (d ?x ?g)
    //              (ln ?f))))"
    //    if is_not_zero("?f")
    //    if is_not_zero("?g")
    //),

    //rw!("i-one"; "(i 1 ?x)" => "?x"),
    //rw!("i-power-const"; "(i (pow ?x ?c) ?x)" =>
    //    "(/ (pow ?x (+ ?c 1)) (+ ?c 1))" if is_const("?c")),
    //rw!("i-cos"; "(i (cos ?x) ?x)" => "(sin ?x)"),
    //rw!("i-sin"; "(i (sin ?x) ?x)" => "(* -1 (cos ?x))"),
    //rw!("i-sum"; "(i (+ ?f ?g) ?x)" => "(+ (i ?f ?x) (i ?g ?x))"),
    //rw!("i-dif"; "(i (- ?f ?g) ?x)" => "(- (i ?f ?x) (i ?g ?x))"),
    //rw!("i-parts"; "(i (* ?a ?b) ?x)" =>
    //    "(- (* ?a (i ?b ?x)) (i (* (d ?x ?a) (i ?b ?x)) ?x))"),
]}

//#[test]
//fn dump_graph() {
//    let expr: RecExpr<Lang> = "(pow (+ x y) 3)".parse().unwrap();
//
//    let runner: Runner<Lang, ConstantFold> = Runner::default()
//        .with_expr(&expr)
//        .run(&rules());
//
//    runner.egraph.dot().to_dot("egraph_dump.dot").unwrap();
//    //assert!(matches!(runner.stop_reason, Some(StopReason::Saturated)));
//}

egg::test_fn! {binomial_squared, rules(), "(pow (+ x y) 2)" => "(+ (pow x 2) (+ (* 2 (* x y)) (pow y 2)))" }
egg::test_fn! {
    #[should_panic(expected = "Could not prove goal 0")]
    square_difference, rules(), "(- (pow x 2) (pow y 2))" => "(* (+ x y) (- x y) )"
}
egg::test_fn! {square_difference_inv, rules(), "(* (+ x y) (- x y) )" => "(- (pow x 2) (pow y 2))" }
egg::test_fn! {square_difference_inv_step1, rules(), "(* (+ x y) (- x y) )" => "(+ (pow x 2) (- (- (* y x) (* x y) ) (pow y 2)))" }
egg::test_fn! {square_difference_inv_step2, rules(), "(+ (pow x 2) (- (- (* y x) (* x y) ) (pow y 2)))" => "(- (pow x 2) (pow y 2))" }
egg::test_fn! {square_difference_inv_intermediate_step, rules(), "(- (* y x) (* x y) )" => "0" }
egg::test_fn! {square_difference_inv_step3, rules(), "(+ (pow x 2) (- 0 (pow y 2)))" => "(- (pow x 2) (pow y 2))" }

egg::test_fn! {
    sum_cubed, rules(),
    runner = Runner::default()
        .with_time_limit(std::time::Duration::from_secs(10))
        .with_iter_limit(60)
        .with_node_limit(100_000),
    "(pow (+ x y) 3)"
    =>
    "(+ (+ (pow x 3) (pow y 3)) (* (* (* 3 x) y) (+ x y)))"
}

egg::test_fn! {
    sum_cubed_step1, rules(),
    runner = Runner::default()
        .with_time_limit(std::time::Duration::from_secs(10))
        .with_iter_limit(60)
        .with_node_limit(100_000),
    "(pow (+ x y) 3)"
    =>
    "(* (+ x y) (pow (+ x y) 2))"
}

egg::test_fn! {sum_cubed_step2, rules(), "(* (+ x y) (pow (+ x y) 2))" => "(* (+ x y) (+ (pow x 2) (+ (* 2 (* x y)) (pow y 2))))"}
egg::test_fn! {sum_cubed_step3, rules(), "(* (+ x y) (+ (pow x 2) (+ (* 2 (* x y)) (pow y 2))))" => "(+ (pow x 3) (+ (* 2 (* (pow x 2) y)) (+ (* x (pow y 2)) (+ (* y (pow x 2)) (+ (* 2 (* x (pow y 2))) (pow y 3))))))"}
egg::test_fn! {sum_cubed_intermediate_step, rules(), "(+ (* 2 (* (pow x 2) y)) (+ (* x (pow y 2)) (+ (* y (pow x 2)) (* 2 (* x (pow y 2))) )))" => "(* (* (* 3 x) y) (+ x y)))"}
//egg::test_fn! {
//    sum_cubed_step2, rules(),
//    runner = Runner::default()
//        .with_time_limit(std::time::Duration::from_secs(10))
//        .with_iter_limit(60)
//        .with_node_limit(100_000),
//    "(* (+ x y) (pow (+ x y) 2))"
//    =>
//    "(* (+ x y) (+ (pow x 2) (+ (* 2 (* x y)) (pow y 2))))"
//}

egg::test_fn! {
    #[should_panic(expected = "Could not prove goal 0")]
    sum_cubed_inv, rules(), "(+ (+ (pow x 3) (pow y 3)) (* (* (* 3 x) y) (+ x y)))" => "(pow (+ x y) 3)"
}

egg::test_fn! {
    #[should_panic(expected = "Could not prove goal 0")]
    binomial4, rules(),
    runner = Runner::default()
        .with_time_limit(std::time::Duration::from_secs(30))
        .with_iter_limit(120)
        .with_node_limit(200_000),
    "(pow (+ x y) 4)"
    =>
    "(+ (pow x 4) (+ (* 4 (* (pow x 3) y)) (+ (* 6 (* (pow x 2) (pow y 2))) (+ (* 4 (* x (pow y 3))) (pow y 4)))))"
}

egg::test_fn! {binomial4_step1, rules(), "(pow (+ x y) 4)" => "(* (pow (+ x y) 2) (pow (+ x y) 2))"}
egg::test_fn! {binomial4_step2, rules(), "(* (pow (+ x y) 2) (pow (+ x y) 2))" => "(* (+ (pow x 2) (+ (* 2 (* x y)) (pow y 2))) (+ (pow x 2) (+ (* 2 (* x y)) (pow y 2))))"}
egg::test_fn! {
    binomial4_step3, rules(),
    runner = Runner::default()
        .with_time_limit(std::time::Duration::from_secs(30))
        .with_iter_limit(120)
        .with_node_limit(200_000),
    "(* (+ (pow x 2) (+ (* 2 (* x y)) (pow y 2))) (+ (pow x 2) (+ (* 2 (* x y)) (pow y 2))))"
    =>
    //"(+ (pow x 4) (+ (pow y 4) (+ (* 4 (* (pow x 3) y)) (+ (* 6 (* (pow x 2) (pow y 2))) (* 4 (* x (pow y 3)))))))"
    "(+ (pow x 4) (+ (* 4 (* (pow x 3) y)) (+ (* 6 (* (pow x 2) (pow y 2))) (+ (* 4 (* x (pow y 3))) (pow y 4)))))"
}

#[test]
pub fn binomial4_sketches() {
    let mut rules = rules();

    // 3 nested maps that we want to reorder:
    let start: Expr = "(pow (+ x y) 4)".parse().unwrap();

    // sketches for the reordered map nests we are looking for:
    #[rustfmt::skip]
    let sketches: &[Sketch] = &[
        "(contains (* (pow (+ x y) 2) (pow (+ x y) 2)))".parse().unwrap(),
        "(contains (* (+ (pow x 2) (+ (* 2 (* x y)) (pow y 2))) (+ (pow x 2) (+ (* 2 (* x y)) (pow y 2)))))".parse().unwrap(),
        "(contains (+ (pow x 4) (+ ? (+ ? (+ ? (pow y 4))))))".parse().unwrap(),
        //"(contains (+ (pow x 4) (+ (* 4 (* (pow x 3) y)) (+ (* 6 (* (pow x 2) (pow y 2))) (+ (* 4 (* x (pow y 3))) (pow y 4))))))".parse().unwrap(),

    ];

    // the corresponding full programs that we expect to find:
    #[rustfmt::skip]
    let goals: &[Expr] = &[
        "(* (pow (+ x y) 2) (pow (+ x y) 2))".parse().unwrap(),
        "(* (+ (pow x 2) (+ (* 2 (* x y)) (pow y 2))) (+ (pow x 2) (+ (* 2 (* x y)) (pow y 2))))".parse().unwrap(),
        "(+ (pow x 4) (+ (* 4 (* (pow x 3) y)) (+ (* 6 (* (pow x 2) (pow y 2))) (+ (* 4 (* x (pow y 3))) (pow y 4)))))".parse().unwrap(),
        //"(+ (pow x 4) (+ (pow y 4) (+ (* 4 (* (pow x 3) y)) (+ (* 6 (* (pow x 2) (pow y 2))) (* 4 (* x (pow y 3)))))))".parse().unwrap(),
    ];

    // grow an e-graph to explore different ways to rewrite `start`
    let mut egraph = EGraph::default();
    let eclass = egraph.add_expr(&start);
    let egraph = grow_egraph(egraph, 1_000_000, &rules[..]);

    // extract the smallest programs from the e-graph that satisfy our sketches,
    // and check that they correspond to the expected full programs:
    for (sketch, goal) in sketches.iter().zip(goals.iter()) {
        sketch_extract_and_check(&egraph, eclass, sketch, goal);
    }
}

fn grow_egraph(egraph: EGraph, node_limit: usize, rules: &[Rewrite]) -> EGraph {
    let runner = egg::Runner::default()
        //.with_scheduler(egg::SimpleScheduler)
        .with_iter_limit(120)
        .with_node_limit(node_limit)
        .with_time_limit(std::time::Duration::from_secs(30))
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
