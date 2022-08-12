use crate::*;
use analysis::{one_shot_analysis, SemiLatticeAnalysis};
use hashcons::ExprHashCons;
use sketch::SketchNode;
use std::cmp::Ordering;

/// Is the `id` e-class of `egraph` representing at least one program satisfying `s`?
pub fn eclass_satisfies_sketch<L: Language, A: Analysis<L>>(
    s: &Sketch<L>,
    egraph: &EGraph<L, A>,
    id: Id,
) -> bool {
    satisfies_sketch(s, egraph).contains(&id)
}

/// Returns the set of e-classes of `egraph` that represent at least one program satisfying `s`.
pub fn satisfies_sketch<L: Language, A: Analysis<L>>(
    s: &Sketch<L>,
    egraph: &EGraph<L, A>,
) -> HashSet<Id> {
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
    memo: &mut HashMap<Id, HashSet<Id>>,
) -> HashSet<Id> {
    match memo.get(&s_index) {
        Some(value) => return value.clone(),
        None => (),
    };

    let result = match &s_nodes[usize::from(s_index)] {
        SketchNode::Any => egraph.classes().map(|c| c.id).collect(),
        SketchNode::Node(node) => {
            let children_matches = node
                .children()
                .iter()
                .map(|sid| satisfies_sketch_rec(s_nodes, *sid, egraph, memo))
                .collect::<Vec<_>>();

            if let Some(potential_ids) = egraph.classes_matching_op(node) {
                potential_ids
                    .iter()
                    .cloned()
                    .filter(|&id| {
                        let eclass = &egraph[id];

                        let mnode = &node.clone().map_children(|_| Id::from(0));
                        egg::for_each_matching_node(eclass, mnode, |matched| {
                            let children_match = children_matches
                                .iter()
                                .zip(matched.children())
                                .all(|(matches, id)| matches.contains(id));
                            if children_match {
                                Err(())
                            } else {
                                Ok(())
                            }
                        })
                        .is_err()
                    })
                    .collect()
            } else {
                HashSet::default()
            }
        }
        SketchNode::Contains(sid) => {
            let contained_matched = satisfies_sketch_rec(s_nodes, *sid, egraph, memo);

            let mut data = egraph
                .classes()
                .map(|eclass| (eclass.id, contained_matched.contains(&eclass.id)))
                .collect::<HashMap<_, bool>>();

            one_shot_analysis(egraph, SatisfiesContainsAnalysis, &mut data);

            data.iter()
                .flat_map(|(&id, &is_match)| if is_match { Some(id) } else { None })
                .collect()
        }
        SketchNode::Or(sids) => {
            let matches = sids
                .iter()
                .map(|sid| satisfies_sketch_rec(s_nodes, *sid, egraph, memo));
            matches
                .reduce(|a, b| a.union(&b).cloned().collect())
                .expect("empty or sketch")
        }
    };

    memo.insert(s_index, result.clone());
    result
}

pub struct SatisfiesContainsAnalysis;
impl<L: Language, A: Analysis<L>> SemiLatticeAnalysis<L, A> for SatisfiesContainsAnalysis {
    type Data = bool;

    fn make<'a>(
        &mut self,
        _egraph: &EGraph<L, A>,
        enode: &L,
        analysis_of: &'a impl Fn(Id) -> &'a Self::Data,
    ) -> Self::Data
    where
        Self::Data: 'a,
    {
        enode.any(|c| *analysis_of(c))
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        let r = *a || b;
        let dm = DidMerge(r != *a, r != b);
        *a = r;
        dm
    }
}

/// Returns the best program satisfying `s` according to `cost_f` that is represented in the `id` e-class of `egraph`, if it exists.
pub fn eclass_extract_sketch<L, A, CF>(
    s: &Sketch<L>,
    cost_f: CF,
    egraph: &EGraph<L, A>,
    id: Id,
) -> Option<(CF::Cost, RecExpr<L>)>
where
    L: Language,
    A: Analysis<L>,
    CF: CostFunction<L>,
    CF::Cost: 'static + Ord,
{
    let (exprs, eclass_to_best) = extract_sketch(s, cost_f, egraph);
    eclass_to_best
        .get(&id)
        .map(|(best_cost, best_id)| (best_cost.clone(), exprs.extract(*best_id)))
}

fn extract_sketch<L, A, CF>(
    s: &Sketch<L>,
    mut cost_f: CF,
    egraph: &EGraph<L, A>,
) -> (ExprHashCons<L>, HashMap<Id, (CF::Cost, Id)>)
where
    L: Language,
    A: Analysis<L>,
    CF: CostFunction<L>,
    CF::Cost: 'static + Ord,
{
    assert!(egraph.clean);
    let mut memo = HashMap::<Id, HashMap<Id, (CF::Cost, Id)>>::default();
    let sketch_nodes = s.as_ref();
    let sketch_root = Id::from(sketch_nodes.len() - 1);
    let mut exprs = ExprHashCons::new();

    let mut extracted = HashMap::default();
    let analysis = ExtractAnalysis {
        exprs: &mut exprs,
        cost_f: &mut cost_f,
    };
    one_shot_analysis(&egraph, analysis, &mut extracted);

    let res = extract_sketch_rec(
        sketch_nodes,
        sketch_root,
        &mut cost_f,
        egraph,
        &mut exprs,
        &extracted,
        &mut memo,
    );
    (exprs, res)
}

fn extract_sketch_rec<L, A, CF>(
    s_nodes: &[SketchNode<L>],
    s_index: Id,
    cost_f: &mut CF,
    egraph: &EGraph<L, A>,
    exprs: &mut ExprHashCons<L>,
    extracted: &HashMap<Id, (CF::Cost, Id)>,
    memo: &mut HashMap<Id, HashMap<Id, (CF::Cost, Id)>>,
) -> HashMap<Id, (CF::Cost, Id)>
where
    L: Language,
    A: Analysis<L>,
    CF: CostFunction<L>,
    CF::Cost: 'static + Ord,
{
    match memo.get(&s_index) {
        Some(value) => return value.clone(),
        None => (),
    };

    let result = match &s_nodes[usize::from(s_index)] {
        SketchNode::Any => extracted.clone(),
        SketchNode::Node(node) => {
            let children_matches = node
                .children()
                .iter()
                .map(|sid| {
                    extract_sketch_rec(s_nodes, *sid, cost_f, egraph, exprs, extracted, memo)
                })
                .collect::<Vec<_>>();

            if let Some(potential_ids) = egraph.classes_matching_op(node) {
                potential_ids
                    .iter()
                    .cloned()
                    .flat_map(|id| {
                        let eclass = &egraph[id];
                        let mut candidates = Vec::new();

                        let mnode = &node.clone().map_children(|_| Id::from(0));
                        let _ = egg::for_each_matching_node(eclass, mnode, |matched| {
                            let mut matches = Vec::new();
                            for (cm, id) in children_matches.iter().zip(matched.children()) {
                                if let Some(m) = cm.get(id) {
                                    matches.push(m);
                                } else {
                                    break;
                                }
                            }

                            if matches.len() == matched.len() {
                                let to_match: HashMap<_, _> =
                                    matched.children().iter().zip(matches.iter()).collect();
                                candidates.push((
                                    cost_f.cost(matched, |c| to_match[&c].0.clone()),
                                    exprs.add(matched.clone().map_children(|c| to_match[&c].1)),
                                ));
                            }

                            Ok(())
                        });

                        candidates
                            .into_iter()
                            .min_by(|x, y| x.0.cmp(&y.0))
                            .map(|best| (id, best))
                    })
                    .collect()
            } else {
                HashMap::default()
            }
        }
        SketchNode::Contains(sid) => {
            let contained_matches =
                extract_sketch_rec(s_nodes, *sid, cost_f, egraph, exprs, extracted, memo);

            let mut data = egraph
                .classes()
                .map(|eclass| (eclass.id, contained_matches.get(&eclass.id).cloned()))
                .collect::<HashMap<_, _>>();

            let analysis = ExtractContainsAnalysis {
                exprs,
                cost_f,
                extracted,
            };

            one_shot_analysis(egraph, analysis, &mut data);

            data.into_iter()
                .flat_map(|(id, maybe_best)| maybe_best.map(|b| (id, b)))
                .collect()
        }
        SketchNode::Or(sids) => {
            let matches = sids
                .iter()
                .map(|sid| {
                    extract_sketch_rec(s_nodes, *sid, cost_f, egraph, exprs, extracted, memo)
                })
                .collect::<Vec<_>>();
            let mut matching_ids = HashSet::default();
            for m in &matches {
                matching_ids.extend(m.keys());
            }

            matching_ids
                .iter()
                .flat_map(|id| {
                    let mut candidates = Vec::new();
                    for ms in &matches {
                        candidates.extend(ms.get(id));
                    }
                    candidates
                        .into_iter()
                        .min_by(|x, y| x.0.cmp(&y.0))
                        .map(|best| (*id, best.clone()))
                })
                .collect()
        }
    };

    memo.insert(s_index, result.clone());
    result
}

pub struct ExtractContainsAnalysis<'a, L, CF>
where
    L: Language,
    CF: CostFunction<L>,
{
    exprs: &'a mut ExprHashCons<L>,
    cost_f: &'a mut CF,
    extracted: &'a HashMap<Id, (CF::Cost, Id)>,
}

impl<'a, L, A, CF> SemiLatticeAnalysis<L, A> for ExtractContainsAnalysis<'a, L, CF>
where
    L: Language,
    A: Analysis<L>,
    CF: CostFunction<L>,
    CF::Cost: 'static + Ord,
{
    type Data = Option<(CF::Cost, Id)>;

    fn make<'b>(
        &mut self,
        egraph: &EGraph<L, A>,
        enode: &L,
        analysis_of: &'b impl Fn(Id) -> &'b Self::Data,
    ) -> Self::Data
    where
        Self::Data: 'b,
    {
        let children_matching: Vec<_> = enode
            .children()
            .iter()
            .flat_map(|&c| {
                let data = (*analysis_of)(c);
                data.as_ref().map(|x| (c, x.clone()))
            })
            .collect();
        let children_any: Vec<_> = enode
            .children()
            .iter()
            .map(|&c| (c, self.extracted[&egraph.find(c)].clone()))
            .collect();

        let mut candidates = Vec::new();

        for (matching_child, matching) in &children_matching {
            let mut to_selected = HashMap::default();

            for (child, any) in &children_any {
                let selected = if child == matching_child {
                    matching
                } else {
                    any
                };
                to_selected.insert(child, selected);
            }

            candidates.push((
                self.cost_f.cost(enode, |c| to_selected[&c].0.clone()),
                self.exprs
                    .add(enode.clone().map_children(|c| to_selected[&c].1)),
            ));
        }

        candidates.into_iter().min_by(|x, y| x.0.cmp(&y.0))
        //.map(|best| (id, best))
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        let ord = match (&a, &b) {
            (None, None) => Ordering::Equal,
            (Some(_), None) => Ordering::Less,
            (None, Some(_)) => Ordering::Greater,
            (&Some((ref ca, _)), &Some((ref cb, _))) => ca.cmp(cb),
        };
        match ord {
            Ordering::Equal => DidMerge(false, false),
            Ordering::Less => DidMerge(false, true),
            Ordering::Greater => {
                *a = b;
                DidMerge(true, false)
            }
        }
    }
}

pub struct ExtractAnalysis<'a, L, CF> {
    exprs: &'a mut ExprHashCons<L>,
    cost_f: &'a mut CF,
}

impl<'a, L, A, CF> SemiLatticeAnalysis<L, A> for ExtractAnalysis<'a, L, CF>
where
    L: Language,
    A: Analysis<L>,
    CF: CostFunction<L>,
    CF::Cost: 'static,
{
    type Data = (CF::Cost, Id);

    fn make<'b>(
        &mut self,
        _egraph: &EGraph<L, A>,
        enode: &L,
        analysis_of: &'b impl Fn(Id) -> &'b Self::Data,
    ) -> Self::Data
    where
        Self::Data: 'b,
    {
        let expr_node = enode.clone().map_children(|c| (*analysis_of)(c).1);
        let expr = self.exprs.add(expr_node);
        (
            self.cost_f.cost(enode, |c| (*analysis_of)(c).0.clone()),
            expr,
        )
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        if a.0 < b.0 {
            DidMerge(false, true)
        } else if a.0 == b.0 {
            DidMerge(false, false)
        } else {
            *a = b;
            DidMerge(true, false)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;

    #[test]
    fn simple_extract() {
        let sketch = "(contains (f ?))".parse::<Sketch<SymbolLang>>().unwrap();

        let a_expr = "(g (f (v x)))".parse::<RecExpr<SymbolLang>>().unwrap();
        let b_expr = "(h (g (f (u x))))".parse::<RecExpr<SymbolLang>>().unwrap();
        let c_expr = "(h (g x))".parse::<RecExpr<SymbolLang>>().unwrap();

        let mut egraph = EGraph::<SymbolLang, ()>::default();
        let a = egraph.add_expr(&a_expr);
        let b = egraph.add_expr(&b_expr);
        let c = egraph.add_expr(&c_expr);

        egraph.rebuild();

        let sat1 = satisfies_sketch(&sketch, &egraph);
        assert_eq!(sat1.len(), 5);
        assert!(sat1.contains(&a));
        assert!(sat1.contains(&b));
        assert!(!sat1.contains(&c));

        egraph.union(a, b);
        egraph.rebuild();

        let sat2 = satisfies_sketch(&sketch, &egraph);
        assert_eq!(sat2.len(), 4);
        assert!(sat2.contains(&a));
        assert!(sat2.contains(&egraph.find(b)));
        assert!(!sat2.contains(&c));

        let (best_cost, best_expr) = eclass_extract_sketch(&sketch, AstSize, &egraph, a).unwrap();
        assert_eq!(best_cost, 4);
        assert_eq!(best_expr, a_expr);
    }
}
