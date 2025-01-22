use egg::{rewrite as rw, *};
use ordered_float::NotNan;
//use egg_sketches::sketch_guided_search;


define_language! {
    pub enum Lang {
        "sqcup" = SqCup([Id; 2]),
        "sqcap" = SqCap([Id; 2]),
        "setminus" = SetMinus([Id; 2]),
        Constant(Constant),
        Symbol(Symbol), // Would this maybe work for unknowns/variables?
    }
}

pub type EGraph = egg::EGraph<Lang, ConstantFold>;
pub type Rewrite = egg::Rewrite<Lang, ConstantFold>;
pub type Constant = NotNan<f64>;
// type Expr = egg::RecExpr<Lang>;
// type Sketch = egg_sketches::Sketch<Lang>;

// You could use egg::AstSize, but this is useful for debugging, since
// it will really try to get rid of the Diff operator

// FIXME: should Clone be required?
#[derive(Default, Clone)]
pub struct ConstantFold;
impl Analysis<Lang> for ConstantFold {
    type Data = Option<(Constant, PatternAst<Lang>)>;

    fn make(egraph: &mut EGraph, enode: &Lang) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.as_ref().map(|d| d.0);
        Some(match enode {
            Lang::Constant(c) => (*c, format!("{}", c).parse().unwrap()),
            Lang::SqCup([a, b]) => (
                x(a)? + x(b)?,
                format!("(sqcup {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            Lang::SqCap([a, b]) => (
                x(a)? - x(b)?,
                format!("(sqcap {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            Lang::SetMinus([a, b]) => (
                x(a)? * x(b)?,
                format!("(setminus {} {})", x(a)?, x(b)?).parse().unwrap(),
            ),
            _ => return None,
        })
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        merge_option(to, from, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            DidMerge(false, false)
        })
    }

}

pub type N = ConstantFold;
pub type L = Lang;
// insprired on https://github.com/opencompl/egg-tactic-code/blob/8b4aa748047a43213fc2c0dfca6b7af4a475f785/json-egg/src/main.rs#L368
pub fn find_sketch(sketch: &egg_sketches::Sketch<L>, start : &RecExpr<L>,
    rewrites : &[Rewrite], iter_limit: usize, node_limit: usize,
    time_limit: std::time::Duration,) -> Result< (RecExpr<L>,() ), String> { // FIXME: return explanation
    let mut graph : egg::EGraph<L,N> = EGraph::default().with_explanations_enabled();
    let lhs_id = graph.add_expr(&start);
    let sketch_clone = sketch.clone();
    let hook = move |runner :  &mut Runner<Lang, ConstantFold>| {
        // use bool
        if let Some(_rhs_id) = egg_sketches::util::comparing_eclass_extract_sketch(&sketch_clone, egg::AstSize, egg::AstSize, &runner.egraph, lhs_id){
            // panic!("same equivalence class".to_string());
            Result::Err("now in same equivalence class".to_string())
        } else {
            Result::Ok(())
        }
    };
    let runner : Runner<L, N> = Runner::default()
      .with_node_limit(node_limit)
      .with_time_limit(time_limit)
      .with_iter_limit(iter_limit)
      .with_scheduler(SimpleScheduler)
      .with_egraph(graph)
      //.with_explanations_enabled()
      .with_hook(hook)
      .run(rewrites);
    runner.print_report();
    let mut egraph = runner.egraph.without_explanation_length_optimization();
    //FIXME: we're computing this twice, once in the hook and once here.
    let op_rhs = egg_sketches::util::comparing_eclass_extract_sketch(&sketch.clone(), egg::AstSize, egg::AstSize, &egraph, lhs_id);
    if let Some( (_ ,rhs_expr)) = op_rhs {
        let mut explanation : Explanation<L> = egraph.explain_equivalence(&start,
            & rhs_expr);
        let _flat_explanation : &FlatExplanation<L> = explanation.make_flat_explanation();
        return Result::Ok((rhs_expr, ()))
    } else {
        return Result::Err("sketch not found".to_string())
    }
}

pub fn sketch_guided_search( sketches: &[egg_sketches::Sketch<L>], start: &RecExpr<L>,
    rewrites : &[Rewrite], iter_limit: usize, node_limit: usize,
    time_limit: std::time::Duration,) -> Result< Vec<(RecExpr<L>,())>, String> {
        let mut res : Vec<(RecExpr<L>,())> = Vec::new(); // FIXME: we're not using the explanation because I don't know enough Rust
        let mut cur : RecExpr<L> = start.clone();
        for sketch in sketches {
            let result = find_sketch(sketch, &cur, rewrites, iter_limit, node_limit, time_limit);
            if let Ok((expr,_s)) = result {
                cur = expr.clone();
                res.push((expr,()));
            }
            else {
                return Result::Err("sketch not found".to_string());
            }
        }
        if res.len() == sketches.len() {
            return Result::Ok(res);
        } else {
            return Result::Err("function called with empty list of sketches".to_string())
        }
    }

#[rustfmt::skip]
pub fn rules() -> Vec<Rewrite> {
  let mut rules = vec![
    rw!("sup_inf_left"; "(sqcup ?x (sqcap ?y ?z))" <=> "(sqcap (sqcup ?x ?y) (sqcup ?x ?z))"),
    rw!("inf_sup_left"; "(sqcap ?x (sqcup ?y ?z))" <=> "(sqcup (sqcap ?x ?y) (sqcap ?x ?z))"),
    rw!("sup_assoc"; "(sqcap ?a (sqcap ?b ?c))" <=> "(sqcap (sqcap ?a ?b) ?c)"),
    rw!("inf_assoc"; "(sqcup ?a (sqcup ?b ?c))" <=> "(sqcup (sqcup ?a ?b) ?c)"),
    rw!("sup_comm"; "(sqcup ?a ?b)" <=> "(sqcup ?b ?a)"),
    rw!("inf_comm"; "(sqcap ?a ?b)" <=> "(sqcap ?b ?a)"),
    rw!("sup_assoc'"; "(sqcap (sqcap ?a ?b) ?c)" <=> "(sqcap ?a (sqcap ?b ?c))"),
    rw!("inf_assoc'"; "(sqcup (sqcup ?a ?b) ?c)" <=> "(sqcup ?a (sqcup ?b ?c))"),
    rw!("sup_comm'"; "(sqcup ?b ?a)" <=> "(sqcup ?a ?b)"),
    rw!("inf_comm'"; "(sqcap ?b ?a)" <=> "(sqcap ?a ?b)")
  ].concat();
  rules.extend(vec![
    rw!("sup_inf_sdiff"; "(sqcup (sqcap ?x ?y) (setminus ?x ?y))" => "(?x)"),
    rw!("sup_inf_self"; "(sqcup ?a (sqcap ?a ?b))" => "(?a)"),
    rw!("inf_idem"; "(sqcap ?a ?a)" => "(?a)"),
  ]);
  rules
}

test_fn! {
  sdiff_sup1, rules(),
  runner = Runner::default()
      .with_time_limit(std::time::Duration::from_secs(30))
      .with_iter_limit(120)
      .with_scheduler(SimpleScheduler)
      .with_node_limit(200_000),
    "(sqcup (sqcap y (sqcup x z)) (sqcap (setminus y x) (setminus y z)))" => "(y)" }
test_fn! {
  subgoal1, rules(),
  runner = Runner::default()
      .with_time_limit(std::time::Duration::from_secs(30))
      .with_iter_limit(120)
      .with_scheduler(SimpleScheduler)
      .with_node_limit(200_000),
    "(sqcup (sqcap y (sqcup x z)) (sqcap (setminus y x) (setminus y z)))" => "(sqcap (sqcap y (sqcup (sqcup x z) (setminus y x))) (sqcap y (sqcup (sqcup x z) (setminus y z))))" }
test_fn! {
  subgoal2, rules(),
  runner = Runner::default()
      .with_time_limit(std::time::Duration::from_secs(30))
      .with_iter_limit(120)
      .with_scheduler(SimpleScheduler)
      .with_node_limit(200_000),
    "(sqcap (sqcap y (sqcup (sqcup x z) (setminus y x))) (sqcap y (sqcup (sqcup x z) (setminus y z))))" => "(sqcap (sqcap y (sqcup x (sqcap y (sqcup z (setminus y x))))) (sqcap y (sqcup x (sqcap y (sqcup z (setminus y z))))))" }
test_fn! {
  subgoal3, rules(),
  runner = Runner::default()
      .with_time_limit(std::time::Duration::from_secs(30))
      .with_iter_limit(120)
      .with_scheduler(SimpleScheduler)
      .with_node_limit(200_000),
    "(sqcap (sqcap y (sqcup x (sqcap y (sqcup z (setminus y x))))) (sqcap y (sqcup x (sqcap y (sqcup z (setminus y z))))))" => "(sqcap (sqcap y (sqcup z (sqcap y (sqcup x (setminus y x))))) (sqcap y (sqcup x (sqcap y (sqcup z (setminus y z))))))" }
test_fn! {
  subgoal4, rules(),
  runner = Runner::default()
      .with_time_limit(std::time::Duration::from_secs(30))
      .with_iter_limit(120)
      .with_scheduler(SimpleScheduler)
      .with_node_limit(200_000),
    "(sqcap (sqcap y (sqcup z (sqcap y (sqcup x (setminus y x))))) (sqcap y (sqcup x (sqcap y (sqcup z (setminus y z))))))" => "(sqcap (sqcap y (sqcup z y)) (sqcap y (sqcup x y)))" }
test_fn! {
  subgoal5, rules(),
  runner = Runner::default()
      .with_time_limit(std::time::Duration::from_secs(30))
      .with_iter_limit(120)
      .with_scheduler(SimpleScheduler)
      .with_node_limit(200_000),
    "(sqcap (sqcap y (sqcup z y)) (sqcap y (sqcup x y)))" => "(sqcap (sqcup y (sqcap y z)) (sqcup y (sqcap y x)))" }
test_fn! {
  subgoal6, rules(),
  runner = Runner::default()
      .with_time_limit(std::time::Duration::from_secs(30))
      .with_iter_limit(120)
      .with_scheduler(SimpleScheduler)
      .with_node_limit(200_000),
    "(sqcap (sqcup y (sqcap y z)) (sqcup y (sqcap y x)))" => "(y)" }
