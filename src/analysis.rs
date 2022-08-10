use crate::*;
use std::fmt::Debug;

pub trait SemiLatticeAnalysis<L: Language, A: Analysis<L>> {
    type Data: Debug + 'static;

    fn make<'b>(&mut self, egraph: &EGraph<L, A>, enode: &L,
                analysis_of: &'b impl Fn(Id) -> &'b Self::Data) -> Self::Data
            where Self::Data: 'b;
    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge;
}

pub fn one_shot_analysis<L: Language, A: Analysis<L>, B: SemiLatticeAnalysis<L, A>>(
    egraph: &EGraph<L, A>,
    mut analysis: B,
    data: &mut HashMap<Id, B::Data>
) {
    assert!(egraph.clean);

    let mut analysis_pending = HashSetQueuePop::<(L, Id)>::new();
    // works with queue but IndexSet is stack
    // IndexSet::<(L, Id)>::default();

    for eclass in egraph.classes() {
        for enode in &eclass.nodes {
            if enode.all(|c| data.contains_key(&egraph.find(c))) {
                analysis_pending.insert((enode.clone(), eclass.id));
            }
        }
    }

    resolve_pending_analysis(egraph, &mut analysis, data, &mut analysis_pending);

    debug_assert!(egraph.classes().all(|eclass| data.contains_key(&eclass.id)));
}

fn resolve_pending_analysis<L: Language, A: Analysis<L>, B: SemiLatticeAnalysis<L, A>>(
    egraph: &EGraph<L, A>,
    analysis: &mut B,
    data: &mut HashMap<Id, B::Data>,
    analysis_pending: &mut HashSetQueuePop<(L, Id)>
) {
    while let Some((node, id)) = analysis_pending.pop() {
        let u_node = node.clone().map_children(|id| egraph.find(id)); // find_mut?

        if u_node.all(|id| data.contains_key(&id)) {
            let cid = egraph.find(id); // find_mut?
            let eclass = &egraph[cid];
            let node_data = analysis.make(egraph, &u_node, &|id| &data[&id]);
            let new_data = match data.remove(&cid) {
                None => {
                    analysis_pending.extend(eclass.parents().map(|(n, id)| (n.clone(), id)));
                    node_data
                }
                Some(mut existing) => {
                    let DidMerge(may_not_be_existing, _) = analysis.merge(&mut existing, node_data);
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

pub struct HashSetQueuePop<T> {
  map: HashSet<T>,
  queue: std::collections::VecDeque<T>,
}

impl<T: Eq + std::hash::Hash + Clone> HashSetQueuePop<T> {
    pub fn new() -> Self {
        HashSetQueuePop { map: HashSet::default(), queue: std::collections::VecDeque::new() }
    }

    pub fn insert(&mut self, t: T) {
        if self.map.insert(t.clone()) {
            self.queue.push_back(t);
        }
    }

    pub fn extend<I>(&mut self, iter: I) where I: IntoIterator<Item = T> {
        for t in iter.into_iter() {
            self.insert(t);
        }
    }

    pub fn pop(&mut self) -> Option<T> {
        let res = self.queue.pop_front();
        res.as_ref().map(|t| self.map.remove(t));
        res
    }
}

impl<L: Language, A: Analysis<L>> SemiLatticeAnalysis<L, A> for AstSize {
    type Data = usize;

    fn make<'a>(&mut self, _egraph: &EGraph<L, A>, enode: &L,
                analysis_of: &'a impl Fn(Id) -> &'a Self::Data) -> Self::Data
            where Self::Data: 'a
    {
        enode.fold(1usize, |size, id| size + analysis_of(id))
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        if *a < b {
            DidMerge(false, true)
        } else if *a == b {
            DidMerge(false, false)
        } else {
            *a = b;
            DidMerge(true, false)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::*;
    use super::*;

    #[test]
    fn simple_analysis() {
        let mut egraph = EGraph::<SymbolLang, ()>::default();
        let a = egraph.add(SymbolLang::leaf("a"));
        let z = egraph.add(SymbolLang::leaf("0"));
        let apz = egraph.add(SymbolLang::new("+", vec![a, z]));
        
        egraph.union(a, apz);
        egraph.rebuild();

        let mut data = HashMap::default();
        one_shot_analysis(&egraph, AstSize, &mut data);

        assert_eq!(data[&egraph.find(apz)], 1);
    }
}