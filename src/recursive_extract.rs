use crate::*;
use hashcons::ExprHashCons;
use sketch::SketchNode;
use extract::ExtractAnalysis;

pub fn eclass_extract_sketch<L, A, CF>(
  s: &Sketch<L>,
  mut cost_f: CF,
  egraph: &EGraph<L, A>,
  id: Id,
) -> Option<(CF::Cost, RecExpr<L>)>
where
  L: Language,
  A: Analysis<L>,
  CF: CostFunction<L>,
  CF::Cost: 'static + Ord,
{
  assert!(egraph.clean);
  let mut memo = HashMap::<(Id, Id), Option<(CF::Cost, Id)>>::default();
  let sketch_nodes = s.as_ref();
  let sketch_root = Id::from(sketch_nodes.len() - 1);
  let mut exprs = ExprHashCons::new();

  let mut extracted = HashMap::default();
  let analysis = ExtractAnalysis {
      exprs: &mut exprs,
      cost_f: &mut cost_f,
  };
  analysis::one_shot_analysis(&egraph, analysis, &mut extracted);

  let best_option = extract_rec(
    id,
    sketch_nodes,
    sketch_root,
    &mut cost_f,
    egraph,
    &mut exprs,
    &extracted,
    &mut memo,
  );

  best_option.map(|(best_cost, best_id)| (best_cost, exprs.extract(best_id)))
}

fn extract_rec<L, A, CF>(
  id: Id,
  s_nodes: &[SketchNode<L>],
  s_index: Id,
  cost_f: &mut CF,
  egraph: &EGraph<L, A>,
  exprs: &mut ExprHashCons<L>,
  extracted: &HashMap<Id, (CF::Cost, Id)>,
  memo: &mut HashMap<(Id, Id), Option<(CF::Cost, Id)>>,
) -> Option<(CF::Cost, Id)>
where
  L: Language,
  A: Analysis<L>,
  CF: CostFunction<L>,
  CF::Cost: 'static + Ord,
{    
  match memo.get(&(id, s_index)) {
    Some(value) => return value.clone(),
    None => (),
  };
  
  let result = match &s_nodes[usize::from(s_index)] {
    SketchNode::Any => extracted.get(&id).cloned(),
    SketchNode::Node(node) => {
      let eclass = &egraph[id];
      let mut candidates = Vec::new();

      let mnode = &node.clone().map_children(|_| Id::from(0));
      let _ = egg::for_each_matching_node(eclass, mnode, |matched| {
        let mut matches = Vec::new();
        for (sid, id) in node.children().iter().zip(matched.children()) {
          if let Some(m) = extract_rec(*id, s_nodes, *sid, cost_f, egraph, exprs, extracted, memo) {
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

      candidates.into_iter().min_by(|x, y| x.0.cmp(&y.0))
    }
    SketchNode::Contains(sid) => {
      memo.insert((id, s_index), None); // avoid cycles

      let eclass = &egraph[id];
      let mut candidates = Vec::new();

      for enode in &eclass.nodes {
        let children_matching: Vec<_> = enode
          .children()
          .iter()
          .flat_map(|&c| {
            let data_rec = extract_rec(c, s_nodes, s_index, cost_f, egraph, exprs, extracted, memo);
            let data_base = extract_rec(c, s_nodes, *sid, cost_f, egraph, exprs, extracted, memo);
            [data_rec, data_base].into_iter().flatten().map(move |x| (c, x))
          })
          .collect();
        let children_any: Vec<_> = enode
          .children()
          .iter()
          .map(|&c| (c, extracted[&egraph.find(c)].clone()))
          .collect();

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
            cost_f.cost(enode, |c| to_selected[&c].0.clone()),
            exprs.add(enode.clone().map_children(|c| to_selected[&c].1)),
          ));
        }
      }

      candidates.into_iter().min_by(|x, y| x.0.cmp(&y.0))
    }
    SketchNode::Or(sids) => {
      sids
        .iter()
        .flat_map(|sid| {
            extract_rec(id, s_nodes, *sid, cost_f, egraph, exprs, extracted, memo)
        })
        .min_by(|x, y| x.0.cmp(&y.0))
    }
  };

  memo.insert((id, s_index), result.clone());
  result
}