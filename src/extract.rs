use crate::*;
use sketch::SketchNode;
use analysis::{SemiLatticeAnalysis, one_shot_analysis};

pub fn eclass_satisfies_sketch<L: Language, A: Analysis<L>>(s: &Sketch<L>, egraph: &EGraph<L, A>, id: Id) -> bool {
    satisfies_sketch(&s, egraph).contains(&id)
}

pub fn satisfies_sketch<L: Language, A: Analysis<L>>(s: &Sketch<L>, egraph: &EGraph<L, A>) -> HashSet<Id> {
    assert!(egraph.clean);
    let memo = HashMap::<Sketch<L>, HashSet<Id>>::default();
    let sketch_nodes = s.as_ref();
    let sketch_root = Id::from(sketch_nodes.len() - 1);
    satisfies_sketch_rec(sketch_nodes, sketch_root, egraph, &mut memo)
}

fn satisfies_sketch_rec<L: Language, A: Analysis<L>>(
    s_nodes: &[SketchNode<L>],
    s_index: Id,
    egraph: &EGraph<L, A>,
    memo: &mut HashMap<Sketch<L>, HashSet<Id>>
) -> HashSet<Id> {
    match s_nodes[usize::from(s_index)] {
        SketchNode::Any => {
            egraph.classes().map(|c| c.id).collect()
        }
        SketchNode::Node(node) => {
            let children_matches = node.children().iter().map(|sid| {
                satisfies_sketch_rec(s_nodes, *sid, egraph, memo)
            }).collect::<Vec<_>>();

            // TODO: classes_by_op for efficiency
            egraph.classes().filter(|eclass| {
                // let eclass = egraph[id];
                let mut is_match = false;

                // TODO: foreach matching node
                for_each_matching_node(eclass, node, |matched| {
                    let children_match = children_matches.iter().zip(matched.children())
                        .all(|(matches, id)| matches.contains(id));
                    if children_match {
                        is_match = true;
                    }
                });

                is_match
            }).map(|c| c.id).collect()
        }
        SketchNode::Contains(sid) => {
            let contained_matched = satisfies_sketch_rec(s_nodes, sid, egraph, memo);

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
    }
}

pub struct SatisfiesContainsAnalysis;
impl<L: Language, A: Analysis<L>> SemiLatticeAnalysis<L, A> for SatisfiesContainsAnalysis {
    type Data = bool;

    fn make<'a>(egraph: &EGraph<L, A>, enode: &L,
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
