use egg::*;
use egg_sketches::analysis::{one_shot_analysis, SemiLatticeAnalysis};
use hashbrown::HashMap;
use std::time::Instant;

// Runtime is extremely sensitive to this argument
const SIZE: usize = 14;

struct MyAnalysis;

impl Analysis<SymbolLang> for MyAnalysis {
    type Data = ();

    fn make(_: &EGraph<SymbolLang, Self>, _: &SymbolLang) {}
    fn merge(&mut self, _: &mut (), _: ()) -> DidMerge {
        DidMerge(true, true)
    }
}

impl SemiLatticeAnalysis<SymbolLang, ()> for MyAnalysis {
    type Data = ();

    fn make<'a>(&mut self, _: &EGraph<SymbolLang, ()>, _: &SymbolLang, _: &'a impl Fn(Id) -> &'a Self::Data) {}
    fn merge(&mut self, _: &mut (), _: ()) -> DidMerge {
        DidMerge(true, true)
    }
}

fn wrap<A: Analysis<SymbolLang>>(egraph: &mut EGraph<SymbolLang, A>, mut v: Id) {
    for _ in 0..SIZE {
        let f = egraph.add(SymbolLang { op: "f".into(), children: vec![v] });
        let g = egraph.add(SymbolLang { op: "g".into(), children: vec![v] });
        egraph.union(f, g);
        v = f;
    }
}

fn print_time<F: FnOnce() -> ()>(msg: &str, f: F) {
  let start = Instant::now();
  f();
  let elapsed = start.elapsed();
  println!("{}: {}.{:03}s", msg, elapsed.as_secs(), elapsed.subsec_millis());
}

fn original_analysis() {
    println!("---- original analysis");

    let mut egraph = EGraph::new(MyAnalysis);
    let x = egraph.add(SymbolLang { op: "x".into(), children: vec![] });
    let y = egraph.add(SymbolLang { op: "y".into(), children: vec![] });
    wrap(&mut egraph, x);
    wrap(&mut egraph, y);

    print_time("first rebuild", || { egraph.rebuild(); });

    egraph.union(x, y);
    print_time("second rebuild", || { egraph.rebuild(); });
}

fn custom_analysis() {
    println!("---- custom analysis");

    let mut egraph = EGraph::new(());
    let x = egraph.add(SymbolLang { op: "x".into(), children: vec![] });
    let y = egraph.add(SymbolLang { op: "y".into(), children: vec![] });
    wrap(&mut egraph, x);
    wrap(&mut egraph, y);

    print_time("first rebuild", || { egraph.rebuild(); });

    egraph.union(x, y);
    print_time("second rebuild", || { egraph.rebuild(); });

    print_time("analysis", || {
        let mut data = HashMap::default();
        one_shot_analysis(&egraph, MyAnalysis, &mut data);
    });
}

#[test]
#[ignore] // this is more of a benchmark
fn compare_analyses() {
    original_analysis();
    custom_analysis();
    panic!("");
}