use egg::{rewrite as rw, *};
use ordered_float::NotNan;
use egg_sketches::{eclass_extract_sketch};
use egg_sketches::util::grow_egraph_until;
//use egg_sketches::sketch_guided_search;

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

pub type N = ConstantFold;
pub type L = Lang;
// insprired on https://github.com/opencompl/egg-tactic-code/blob/8b4aa748047a43213fc2c0dfca6b7af4a475f785/json-egg/src/main.rs#L368
pub fn find_sketch(search_name: &str, sketch: &egg_sketches::Sketch<L>, start : &RecExpr<L>,
    rewrites : &[Rewrite]) -> Result< (RecExpr<L>,() ), String> { // FIXME: return explanation
    let mut graph : egg::EGraph<L,N> = EGraph::default().with_explanations_enabled();
    let lhs_id = graph.add_expr(&start);
    let sketch_clone = sketch.clone();
    let egraph = grow_egraph_until(search_name, graph, rewrites,
        move |runner :  &mut Runner<Lang, ConstantFold>| {
        // use bool
        if let Some(rhs_id) = eclass_extract_sketch(&sketch_clone, egg::AstSize, &runner.egraph, lhs_id){
            true
        } else {
            false
        }
    });
    let mut egraph = egraph.without_explanation_length_optimization();
    //FIXME: we're computing this twice, once in the hook and once here.
    let op_rhs = eclass_extract_sketch(&sketch.clone(), egg::AstSize, &egraph, lhs_id); 
    if let Some( (_ ,rhs_expr)) = op_rhs {
        let mut explanation : Explanation<L> = egraph.explain_equivalence(&start,
            & rhs_expr);
        let flat_explanation : &FlatExplanation<L> = explanation.make_flat_explanation();
        return Result::Ok((rhs_expr, ()))
    } else {
        return Result::Err("sketch not found".to_string())
    }
}

pub fn sketch_guided_search(
    name: &str,
    sub_search: Option<usize>, // 0 for first guide, None for unguided
    start: &RecExpr<L>,
    sketches: &[egg_sketches::Sketch<L>],
    expected: &[RecExpr<L>],
    rewrites : &[Rewrite]
) {  
    let (search_name, sketch, expected, cur) = match sub_search {
        None => (format!("{}_unguided", name), sketches.last().unwrap(), expected.last().unwrap(), start),
        Some(i) => {
            let cur = if i == 0 { start } else { &expected[i - 1] };
            (format!("{}_{}", name, i), &sketches[i], &expected[i], cur)
        }
    };
    
    // TODO: check expected result?
    let (result, _) = find_sketch(&search_name, sketch, cur, rewrites)
        .expect("find sketch failed");

    let bs = string_of_expr(&result);
    let gs = string_of_expr(expected);
    //println!("{} == {}", bs, gs);
    assert_eq!(bs, gs);
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

pub fn binomial4_sketches(sub_search: Option<usize>) {
    let mut rules = rules();

    // 3 nested maps that we want to reorder:
    let start: Expr = "(pow (+ x y) 4)".parse().unwrap();

    // sketches for the reordered map nests we are looking for:
    #[rustfmt::skip]
    let sketches: &[Sketch] = &[
        "(contains (* (pow (+ x y) 2) (pow (+ x y) 2)))".parse().unwrap(),
        "(contains (* (+ (pow x 2) (+ (* 2 (* x y)) (pow y 2))) (+ (pow x 2) (+ (* 2 (* x y)) (pow y 2)))))".parse().unwrap(),
        // misguide:
        //"(contains (+ (pow x 4) (+ ? (+ ? (+ ? (pow y 4))))))".parse().unwrap(),
        "(contains (+ (pow x 4) (+ (* 4 (* (pow x 3) y)) (+ (* 6 (* (pow x 2) (pow y 2))) (+ (* 4 (* x (pow y 3))) (pow y 4))))))".parse().unwrap(),

    ];

    // the corresponding full programs that we expect to find:
    #[rustfmt::skip]
    let goals: &[Expr] = &[
        "(* (pow (+ x y) 2) (pow (+ x y) 2))".parse().unwrap(),
        "(* (+ (pow x 2) (+ (* 2 (* x y)) (pow y 2))) (+ (pow x 2) (+ (* 2 (* x y)) (pow y 2))))".parse().unwrap(),
        //"(+ (pow x 4) (+ (* (* (pow x 3) 2) y) (+ (* (* y (+ (* 2 x) y)) (* x (+ x (* 2 y)))) (+ (* (* x (+ x (* 2 y))) (pow y 2)) (pow y 4)))))".parse().unwrap(),
        // "(+ (pow x 4) (+ (* (pow x 2) (* y (+ (* 2 x) y))) (+ (* (* y (+ (* 2 x) y)) (* x (+ x (* 2 y)))) (+ (* (* (* 2 (* x y)) y) y) (pow y 4)))))".parse().unwrap(),
        "(+ (pow x 4) (+ (* 4 (* (pow x 3) y)) (+ (* 6 (* (pow x 2) (pow y 2))) (+ (* 4 (* x (pow y 3))) (pow y 4)))))".parse().unwrap(),
    ];

    // grow an e-graph to explore different ways to rewrite `start`
    sketch_guided_search("binomial4", sub_search, &start, sketches, goals, &rules[..]);
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
    let args: Vec<String> = std::env::args().collect();
    assert!(args.len() >= 2);

    let name = args[1].as_str();
    let sub_search = args.get(2).map(|s|
        s.parse::<usize>().expect("expected sub search number"));
    match name {
        "binomial4" => binomial4_sketches(sub_search),
        _ =>  panic!("unknown parameter")
    }
}