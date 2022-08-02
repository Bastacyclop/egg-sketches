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

    let mut analysis_pending = IndexSet::<(L, Id)>::default();

    for eclass in egraph.classes() {
        for enode in &eclass.nodes {
            if enode.all(|c| data.contains_key(&egraph.find(c))) {
                analysis_pending.insert((enode.clone(), eclass.id));
            }
        }
    }

    resolve_pending_analysis(egraph, analysis, data, &mut analysis_pending);

    debug_assert!(egraph.classes().all(|eclass| data.contains_key(&eclass.id)));
}

fn resolve_pending_analysis<L: Language, A: Analysis<L>, B: SemiLatticeAnalysis<L, A>>(
    egraph: &EGraph<L, A>,
    _analysis: B,
    data: &mut HashMap<Id, B::Data>,
    analysis_pending: &mut IndexSet<(L, Id)>
) {
    while let Some((node, id)) = analysis_pending.pop() {
        let u_node = node.clone().map_children(|id| egraph.find(id)); // find_mut?

        if u_node.all(|id| data.contains_key(&id)) {
            let cid = egraph.find(id); // find_mut?
            let eclass = &egraph[cid];
            let node_data = B::make(egraph, &u_node, &|id| &data[&id]);
            let new_data = match data.remove(&cid) {
                None => {
                    analysis_pending.extend(eclass.parents().map(|(n, id)| (n.clone(), id)));
                    node_data
                }
                Some(mut existing) => {
                    let DidMerge(may_not_be_existing, _) = B::merge(&mut existing, node_data);
                    if may_not_be_existing {
                        analysis_pending.extend(eclass.parents().map(|(n, id)| (n.clone(), id)));
                    }
                    existing
                }
            };
            data.insert(cid, new_data);
        } else {
            analysis_pending.insert((node, id));
        }
    }
}