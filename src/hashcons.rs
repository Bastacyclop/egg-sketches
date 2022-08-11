use crate::*;

/// hash consed storage for expressions,
/// cheap replacement for garbage collected expressions
pub(crate) struct ExprHashCons<L> {
    rec_expr: RecExpr<L>,
    memo: HashMap<L, Id>,
}

impl<L: Language> ExprHashCons<L> {
    pub(crate) fn new() -> Self {
        ExprHashCons {
            rec_expr: RecExpr::default(),
            memo: HashMap::default(),
        }
    }

    pub(crate) fn add(&mut self, node: L) -> Id {
        if let Some(id) = self.memo.get(&node) {
            *id
        } else {
            self.rec_expr.add(node)
        }
    }

    pub(crate) fn extract(&self, id: Id) -> RecExpr<L> {
        let all = self.rec_expr.as_ref();

        let mut used = HashSet::default();
        used.insert(id);
        for (i, node) in all.iter().enumerate().rev() {
            if used.contains(&Id::from(i)) {
                node.for_each(|c| {
                    used.insert(c);
                });
            }
        }

        let mut fresh = RecExpr::default();
        let mut map = HashMap::<Id, Id>::default();
        for (i, node) in all.iter().enumerate() {
            if used.contains(&Id::from(i)) {
                let fresh_node = node.clone().map_children(|c| map[&c]);
                let fresh_id = fresh.add(fresh_node);
                map.insert(Id::from(i), fresh_id);
            }
        }

        fresh
    }
}
