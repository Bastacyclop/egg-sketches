use crate::*;
use sketch::SketchNode;
use analysis::{SemiLatticeAnalysis, one_shot_analysis};

pub fn eclass_satisfies_sketch<L: Language, A: Analysis<L>>(s: &Sketch<L>, egraph: &EGraph<L, A>, id: Id) -> bool {
    satisfies_sketch(&s, egraph).contains(&id)
}

pub fn satisfies_sketch<L: Language, A: Analysis<L>>(s: &Sketch<L>, egraph: &EGraph<L, A>) -> HashSet<Id> {
    assert!(egraph.clean);
    let mut memo = HashMap::<Id, HashSet<Id>>::default();
    let sketch_nodes = s.as_ref();
    let sketch_root = Id::from(sketch_nodes.len() - 1);
    satisfies_sketch_rec(sketch_nodes, sketch_root, egraph, &mut memo)
}

fn satisfies_sketch_rec<L: Language, A: Analysis<L>>(
    s_nodes: &[SketchNode<L>],
    s_index: Id,
    egraph: &EGraph<L, A>,
    memo: &mut HashMap<Id, HashSet<Id>>
) -> HashSet<Id> {
    match memo.get(&s_index) {
        Some(value) => return value.clone(),
        None => ()
    };

    let result = match &s_nodes[usize::from(s_index)] {
        SketchNode::Any => {
            egraph.classes().map(|c| c.id).collect()
        }
        SketchNode::Node(node) => {
            let children_matches = node.children().iter().map(|sid| {
                satisfies_sketch_rec(s_nodes, *sid, egraph, memo)
            }).collect::<Vec<_>>();

            if let Some(potential_ids) = egraph.classes_matching_op(&node) {
                potential_ids.iter().cloned().filter(|&id| {
                    let eclass = &egraph[id];

                    egg::for_each_matching_node(eclass, &node, |matched| {
                        let children_match = children_matches.iter().zip(matched.children())
                            .all(|(matches, id)| matches.contains(id));
                        if children_match { Err(()) } else { Ok(()) }
                    }).is_err()
                }).collect()
            } else {
                HashSet::default()
            }
        }
        SketchNode::Contains(sid) => {
            let contained_matched = satisfies_sketch_rec(s_nodes, *sid, egraph, memo);

            let mut data = egraph.classes().map(|eclass| {
                (eclass.id, contained_matched.contains(&eclass.id))
            }).collect::<HashMap<_, bool>>();

            one_shot_analysis(egraph, SatisfiesContainsAnalysis, &mut data);

            data.iter().flat_map(|(&id, &is_match)| {
                if is_match { Some(id) } else { None }
            }).collect()
        }
        SketchNode::Or(sids) => {
            let matches = sids.iter().map(|sid|
                satisfies_sketch_rec(s_nodes, *sid, egraph, memo));
            matches.reduce(|a, b| a.union(&b).cloned().collect())
                .expect("empty or sketch")
        }
    };

    memo.insert(s_index, result.clone());
    result
}

pub struct SatisfiesContainsAnalysis;
impl<L: Language, A: Analysis<L>> SemiLatticeAnalysis<L, A> for SatisfiesContainsAnalysis {
    type Data = bool;

    fn make<'a>(_egraph: &EGraph<L, A>, enode: &L,
                analysis_of: &'a impl Fn(Id) -> &'a Self::Data) -> Self::Data
            where Self::Data: 'a
    {
        enode.any(|c| *analysis_of(c))
    }

    fn merge(a: &mut Self::Data, b: Self::Data) -> DidMerge {
        let r = *a || b;
        let dm = DidMerge(r != *a, r != b);
        *a = r;
        dm  
    }
}

#[cfg(test)]
mod tests {
    use crate::*;
    use super::*;

    #[test]
    fn simple_extract() {
        let sketch = "(contains (f ?))"
            .parse::<Sketch<SymbolLang>>().unwrap();

        let mut egraph = EGraph::<SymbolLang, ()>::default();
        let a = egraph.add_expr(&"(g (f (v x)))"
            .parse::<RecExpr<SymbolLang>>().unwrap());
        let b = egraph.add_expr(&"(h (g (f (u x))))"
            .parse::<RecExpr<SymbolLang>>().unwrap());
        let c = egraph.add_expr(&"(h (g x))"
            .parse::<RecExpr<SymbolLang>>().unwrap());
        
        egraph.rebuild();

        let sat = satisfies_sketch(&sketch, &egraph);
        assert_eq!(sat.len(), 5);
        assert!(sat.contains(&a));
        assert!(sat.contains(&b));
        assert!(!sat.contains(&c));
    }
}