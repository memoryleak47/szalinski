// === minqueue ===

use egg::{Id, EGraph, Language, Extractor, FromOp, RecExpr, Rewrite, Subst, ENodeOrVar, PatternAst, CostFunction, Analysis};

use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, BTreeMap};

pub struct MinPrioQueue<U, T>(BinaryHeap<WithOrdRev<U, T>>);

impl<U: Ord, T: Eq> MinPrioQueue<U, T> {
    pub fn new() -> Self {
        MinPrioQueue(BinaryHeap::default())
    }

    pub fn push(&mut self, u: U, t: T) {
        self.0.push(WithOrdRev(u, t));
    }

    pub fn pop(&mut self) -> Option<(U, T)> {
        self.0.pop().map(|WithOrdRev(u, t)| (u, t))
    }
}

// Takes the `Ord` from U, but reverses it.
#[derive(PartialEq, Eq, Debug)]
struct WithOrdRev<U, T>(pub U, pub T);

impl<U: Ord, T: Eq> PartialOrd for WithOrdRev<U, T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // It's the other way around, because we want a min-heap!
        other.0.partial_cmp(&self.0)
    }
}
impl<U: Ord, T: Eq> Ord for WithOrdRev<U, T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(&other).unwrap()
    }
}

// === ctxt cost ===

type L = crate::cad::Cad;
type N = crate::cad::MetaAnalysis;
type C = egg::AstSize; // crate::cad::CostFn;
fn mk_C() -> C { egg::AstSize }

pub fn compute_ctxt_costs(root: Id, eg: &EGraph<L, N>, ex: &Extractor<C, L, N>) -> HashMap<Id, usize> {
    let mut ctxt_cost = HashMap::new();

    let mut queue: MinPrioQueue<usize, Id> = MinPrioQueue::new();

    // initial
    queue.push(0, root);

    while let Some((cst, i)) = queue.pop() {
        if ctxt_cost.contains_key(&i) { continue }
        ctxt_cost.insert(i, cst);
        for e in &eg[i].nodes {
            let e_cost = mk_C().cost(e, |k| ex.find_best_cost(k));
            for &c in e.children() {
                // optimization: don't push junk to the queue.
                // NOTE: if we remembered what's the best thing we already pushed to the queue for some class,
                // we could do more efficient pruning.
                if ctxt_cost.contains_key(&c) { continue }

                let c_cost = ex.find_best_cost(c);
                let ncst = e_cost + cst - c_cost;
                queue.push(ncst, c);
            }
        }
    }

    ctxt_cost
}

// === pat detour ===

use std::fmt::Display;
use std::time::{Instant, Duration};

pub fn eqsat_pat_detour(st: RecExpr<L>, rws: &[Rewrite<L, N>], time_limit: usize) -> RecExpr<L> {
    println!("Initial: {st}");
    let mut eg = EGraph::default();
    let i = eg.add_expr(&st);

    let start = Instant::now();

    eg.rebuild();
    loop {
        pat_detour_eqsat_step(i, rws, &mut eg);
        if start.elapsed() > Duration::from_secs(time_limit as _) { break }
    }

    let ex = Extractor::new(&eg, mk_C());
    let t = ex.find_best(i).1;
    println!("Detour Extracted: {}", t);
    println!("Total Size: {}", eg.total_size());
    t
}

pub fn pat_detour_eqsat_step(root: Id, rws: &[Rewrite<L, N>], eg: &mut EGraph<L, N>) {
    let ex = Extractor::new(&eg, mk_C());
    let ctxt_cost = compute_ctxt_costs(root, eg, &ex);

    let mut matches: BTreeMap</*detour cost*/ usize, Vec<(/*rw id*/ usize, Id, Subst, /*ctxt_cost*/ usize, /*pat_cost*/ usize)>> = BTreeMap::default();
    for (rw_i, rw) in rws.iter().enumerate() {
        let lhs_pat = rw.searcher.get_pattern_ast().unwrap();

        for m in rw.searcher.search(eg) {
            let lhs = m.eclass;
            for subst in m.substs {
                let pat_cost = pat_cost(lhs_pat, &subst, &ex);
                // We don't subtract the root cost here, it's a constant offset, so why would we.
                let cx_cost = *ctxt_cost.get(&lhs).unwrap_or(&10000000000); // TODO are there disconnected parts?
                let detour_cost = cx_cost + pat_cost;
                if !matches.contains_key(&detour_cost) {
                    matches.insert(detour_cost, Vec::new());
                }
                matches.get_mut(&detour_cost).unwrap().push((rw_i, lhs, subst, cx_cost, pat_cost));
            }
        }
    }

    let root_cost = ex.find_best_cost(root);

    let og_data = eg_data(eg);
    let mut dirty = false;

    for (full_cost, new_apps) in matches {
        for (rw_i, lhs, subst, cx_cost, pat_cost) in &new_apps {
            let rw = &rws[*rw_i];
            rw.applier.apply_one(eg, *lhs, subst, None, rw.name);
            if eg_data(eg) != og_data { dirty = true; }
        }
        if dirty { break }
    }

    eg.rebuild();
}

type EGData = (usize, usize);
fn eg_data(eg: &EGraph<L, N>) -> EGData {
    (eg.number_of_classes(), eg.total_size())
}

fn pat_cost(pat: &PatternAst<L>, subst: &Subst, ex: &Extractor<C, L, N>) -> usize {
    let mut vec: Vec<usize> = Vec::new();
    for i in 0..pat.as_ref().len() {
        let cost = match &pat[i.into()] {
            ENodeOrVar::ENode(n) => mk_C().cost(n, |i| vec[usize::from(i)]),
            ENodeOrVar::Var(v) => ex.find_best_cost(subst[*v]),
        };
        vec.push(cost);
    }
    vec.last().copied().unwrap()
}

// === misc ===

pub fn lookup_pat(pat: &PatternAst<L>, eg: &EGraph<L, N>, subst: &Subst) -> Option<Id> {
    let mut vec = Vec::new();
    for i in 0..pat.as_ref().len() {
        match &pat[i.into()] {
            ENodeOrVar::ENode(n) => {
                let mut n = n.clone().map_children(|k| vec[usize::from(k)]);
                let k = eg.lookup(&mut n)?;
                vec.push(k);
            },
            ENodeOrVar::Var(v) => vec.push(subst[*v]),
        }
    }
    vec.last().copied()
}
