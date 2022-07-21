use crate::{IndexSet, HashMap};
use egg::{EGraph, Language, Analysis, Id, DidMerge};
use std::fmt::Debug;

pub trait SemiLatticeAnalysis<L: Language, A: Analysis<L>> {
    type Data: Debug;

    fn make<'a>(egraph: &EGraph<L, A>, enode: &L,
                analysis_of: &'a impl Fn(Id) -> &'a Self::Data) -> Self::Data
            where Self::Data: 'a;
    fn merge(a: &mut Self::Data, b: Self::Data) -> DidMerge;
}

pub fn one_shot_analysis<L: Language, A: Analysis<L>, B: SemiLatticeAnalysis<L, A>>(
    egraph: &EGraph<L, A>,
    analysis: B,
    data: &mut HashMap<Id, B::Data>
) {
    assert!(egraph.clean);

    let analysis_pending = IndexSet::<(L, Id)>::default();

    for eclass in egraph.classes() {
        for enode in &eclass.nodes {
            if enode.children().forall(|c| data.contains(egraph.find(c))) {
                analysis_pending.push((enode, eclass.id));
            }
        }
    }

    resolve_pending_analysis(egraph, analysis, data, analysis_pending);

    debug_assert!(egraph.classes().forall(|eclass| data.contains(eclass.id)));
}

fn resolve_pending_analysis<L: Language, A: Analysis<L>, B: SemiLatticeAnalysis<L, A>>(
    egraph: &EGraph<L, A>,
    analysis: B,
    data: &mut HashMap<Id, B::Data>,
    analysis_pending: &mut IndexSet<(L, Id)>
) {
    while let Some((node, id)) = analysis_pending.pop() {
        let u_node = node.map_children(egraph.find_mut);

        if u_node.children().forall(data.contains) {
            let cid = egraph.find_mut(id);
            let eclass = egraph[cid];
            let node_data = B::make(egraph, u_node, |id| &data[id]);
            let new_data = match data.get(&cid) {
                None => {
                    analysis_pending.extend(eclass.parents.iter());
                    node_data
                }
                Some(existing) => {
                    let DidMerge(may_not_be_existing, _) = B::merge(existing, node_data);
                    if may_not_be_existing {
                        analysis_pending.extend(eclass.parents);
                    }
                    existing
                }
            };
            data.insert(cid, new_data);
        } else {
            analysis_pending.push((node, id));
        }
    }
}