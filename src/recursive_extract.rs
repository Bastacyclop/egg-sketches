use crate::*;
use hashcons::ExprHashCons;
use sketch::SketchNode;
use extract::ExtractAnalysis;

/// Returns the best program satisfying `s` according to `cost_f` that is represented in the `id` e-class of `egraph`, if it exists.
pub fn eclass_extract_sketch<L, A, CF>(
  sketch: &Sketch<L>,
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
  let sketch_root = Id::from(sketch.as_ref().len() - 1);
  let mut exprs = ExprHashCons::new();

  let mut extracted = HashMap::default();
  let analysis = ExtractAnalysis {
      exprs: &mut exprs,
      cost_f: &mut cost_f,
  };
  analysis::one_shot_analysis(&egraph, analysis, &mut extracted);

  let best_option = extract_rec(
    id,
    sketch,
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
  egraph_id: Id,
  sketch: &Sketch<L>,
  sketch_id: Id,
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
  assert_eq!(egraph.find(egraph_id), egraph_id);
  match memo.get(&(egraph_id, sketch_id)) {
    Some(value) => return value.clone(),
    None => (),
  };

  let result = match &sketch[sketch_id] {
    SketchNode::Any =>
      extracted.get(&egraph_id).cloned(),
    SketchNode::Node(sketch_node) => {
      let eclass = &egraph[egraph_id];

      // TODO: factorize code in extract_common
      let mut candidates = Vec::new();
      let mnode = &sketch_node.clone().map_children(|_| Id::from(0));
      let _ = eclass.for_each_matching_node::<()>(mnode, |matched| {
        let mut matches = Vec::new();
        for (sid, id) in sketch_node.children().iter().zip(matched.children()) {
          if let Some(m) = extract_rec(*id, sketch, *sid, cost_f, egraph, exprs, extracted, memo) {
            matches.push(m);
          } else {
            break;
          }
        }

        assert!(matched.all(|c| c == egraph.find(c)));
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
    SketchNode::Contains(inner_sketch_id) => {
      // Avoid cycles.
      // If we have visited the contains once, we do not need to
      // visit it again as the cost in our setup only goes up.
      memo.insert((egraph_id, sketch_id), None);

      let eclass = &egraph[egraph_id];
      let mut candidates = Vec::new();
      // Base case: when this eclass satisfies inner sketch
      candidates.extend(extract_rec(egraph_id, sketch, *inner_sketch_id, cost_f, egraph, exprs, extracted, memo));

      // Recursive case: when children satisfy sketch
      for enode in &eclass.nodes {
        extract_common::push_extract_contains_candidates(&mut candidates,
          exprs, cost_f, extracted, egraph, enode, |c, exprs, cost_f, extracted, egraph| {
            extract_rec(c, sketch, sketch_id, cost_f, egraph, exprs, extracted, memo)
          }
        )
      }

      candidates.into_iter().min_by(|x, y| x.0.cmp(&y.0))
    }
    SketchNode::OnlyContains(inner_sketch_id) => {
      // FIXME: duplicate code
      // Avoid cycles.
      // If we have visited the contains once, we do not need to
      // visit it again as the cost in our setup only goes up.
      memo.insert((egraph_id, sketch_id), None);

      let eclass = &egraph[egraph_id];
      let mut candidates = Vec::new();
      // Base case: when this eclass satisfies inner sketch
      candidates.extend(extract_rec(egraph_id, sketch, *inner_sketch_id, cost_f, egraph, exprs, extracted, memo));

      // Recursive case: when children satisfy sketch
      for enode in &eclass.nodes {
        candidates.extend(extract_common::extract_only_contains_candidate(
          exprs, cost_f, egraph, enode, |c, exprs, cost_f, egraph| {
            extract_rec(c, sketch, sketch_id, cost_f, egraph, exprs, extracted, memo)
          }
        ))
      }

      candidates.into_iter().min_by(|x, y| x.0.cmp(&y.0))
    }
    SketchNode::Or(inner_sketch_ids) => {
      inner_sketch_ids
        .iter()
        .flat_map(|sid| {
            extract_rec(egraph_id, sketch, *sid, cost_f, egraph, exprs, extracted, memo)
        })
        .min_by(|x, y| x.0.cmp(&y.0))
    }
  };

  /* DEBUG
  if let SketchNode::Contains(_) = &sketch[sketch_id] {
    if let Some((cost, _)) = &result {
      println!("result for {:?}, {:?}: {:?}", sketch_id, egraph_id, cost);
    }
  } */

  memo.insert((egraph_id, sketch_id), result.clone());
  result
}