use crate::*;
use hashcons::ExprHashCons;

pub(crate) fn push_extract_contains_candidates<L, A, CF>(
  candidates: &mut Vec<(CF::Cost, Id)>,
  exprs: &mut ExprHashCons<L>,
  cost_f: &mut CF,
  extracted: &HashMap<Id, (CF::Cost, Id)>,
  egraph: &EGraph<L, A>,
  enode: &L,
  mut analysis_of: impl FnMut(Id, &mut ExprHashCons<L>, &mut CF, &HashMap<Id, (CF::Cost, Id)>, &EGraph<L, A>) -> Option<(CF::Cost, Id)>,
)
where
    L: Language,
    A: Analysis<L>,
    CF: CostFunction<L>,
    CF::Cost: 'static + Ord,
{
  // TODO: could probably simplify and optimize this code

  // Children that satisfy the sketch
  let children_matching: Vec<_> = { enode
      .children()
      .iter()
      .map(|&c| {
          let data = analysis_of(c, exprs, cost_f, extracted, egraph);
          (c, data)
      })
      .collect()
  };

  // Children that satisfy '?'
  let children_any: Vec<_> = enode
      .children()
      .iter()
      .map(|&c| (c, extracted[&egraph.find(c)].clone()))
      .collect();

  let mut index_based_enode = enode.clone();
  for (index, id) in index_based_enode.children_mut().iter_mut().enumerate() {
      *id = Id::from(index);
  }

  // If one child satisfies sketch, it's enough.
  // Take '?' options for the other children.
  // Accumulate all combination.
  for (matching_index, (matching_id, matching_data)) in children_matching.iter().enumerate() {
      if let Some(matching_data) = matching_data {
          let mut to_selected = HashMap::default();

          for (index, (id, any_data)) in children_any.iter().enumerate() {
              let selected = if index == matching_index {
                  matching_data
              } else {
                  any_data
              };
              to_selected.insert(Id::from(index), selected);
          }

          candidates.push((
              cost_f.cost(&index_based_enode, |c| to_selected[&c].0.clone()),
              exprs
                  .add(index_based_enode.clone().map_children(|c| to_selected[&c].1)),
          ));
      }
  }
}

pub(crate) fn extract_only_contains_candidate<L, A, CF>(
  exprs: &mut ExprHashCons<L>,
  cost_f: &mut CF,
  egraph: &EGraph<L, A>,
  enode: &L,
  mut analysis_of: impl FnMut(Id, &mut ExprHashCons<L>, &mut CF, &EGraph<L, A>) -> Option<(CF::Cost, Id)>,
) -> Option<(CF::Cost, Id)>
where
    L: Language,
    A: Analysis<L>,
    CF: CostFunction<L>,
    CF::Cost: 'static + Ord,
{
  if enode.children().is_empty() { return None }

  // Children that satisfy the sketch
  let children_matching: HashMap<_, _> = { enode
      .children()
      .iter()
      .map(|&c| {
          let data = analysis_of(c, exprs, cost_f, egraph);
          (c, data)
      })
      .collect()
  };

  let all_contains = children_matching.iter().all(|(c, data)| {
    data.is_some()
  });
  if !all_contains { return None };

  Some((
      cost_f.cost(enode, |c| children_matching[&c].as_ref().unwrap().0.clone()),
      exprs
          .add(enode.clone().map_children(|c| children_matching[&c].as_ref().unwrap().1)),
  ))
}