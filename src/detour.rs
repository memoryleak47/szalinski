// === minqueue ===

use noisy_float::types::{R64, r64};
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
type C = crate::cad::CostFn;
fn mk_C() -> C { crate::cad::CostFn }
type Cost = R64;

pub fn compute_ctxt_costs(root: Id, eg: &EGraph<L, N>, ex: &Extractor<C, L, N>) -> HashMap<Id, Cost> {
    let mut ctxt_cost = HashMap::new();

    let mut queue: MinPrioQueue<Cost, Id> = MinPrioQueue::new();

    // initial
    queue.push(r64(0.0), root);

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
                let ncst = r64(e_cost) + cst - r64(c_cost);
                queue.push(ncst, c);
            }
        }
    }

    ctxt_cost
}

// === pat detour ===

use std::fmt::Display;
use std::time::{Instant, Duration};

pub fn eqsat_pat_detour(st: RecExpr<L>, rws: &[Rewrite<L, N>], time_limit_secs: f64) -> RecExpr<L> {
    println!("Initial: {st}");
    let mut eg = EGraph::default();
    let i = eg.add_expr(&st);

    let start = Instant::now();

    eg.rebuild();
    let mut it_counter = 0;
    loop {
        pat_detour_eqsat_step(i, rws, &mut eg);
        it_counter += 1;
        if start.elapsed() > Duration::from_secs_f64(time_limit_secs) { break }
    }

    let ex = Extractor::new(&eg, mk_C());
    let t = ex.find_best(i).1;

    println!("Detour report");
    println!("=============");
    println!("Stop reason: timeout 10s");
    println!("Iterations: {it_counter}");
    println!("Egraph size: {} nodes, {} classes, {} memo", eg.total_number_of_nodes(), eg.number_of_classes(), eg.total_size());
    println!("Detour Extracted: {}", t);

    t
}

pub fn pat_detour_eqsat_step(root: Id, rws: &[Rewrite<L, N>], eg: &mut EGraph<L, N>) {
    let ex = Extractor::new(&eg, mk_C());
    let ctxt_cost = compute_ctxt_costs(root, eg, &ex);

    let mut matches: BTreeMap</*detour cost*/ Cost, Vec<(/*rw id*/ usize, Id, Subst, /*ctxt_cost*/ Cost, /*pat_cost*/ Cost)>> = BTreeMap::default();
    for (rw_i, rw) in rws.iter().enumerate() {
        let lhs_pat = rw.searcher.get_pattern_ast().unwrap();

        for m in rw.searcher.search(eg) {
            let lhs = m.eclass;
            for subst in m.substs {
                let pat_cost = pat_cost(lhs_pat, &subst, &ex);
                // We don't subtract the root cost here, it's a constant offset, so why would we.
                let cx_cost = *ctxt_cost.get(&lhs).unwrap_or(&r64(100000000000000.0)); // TODO so there are disconnected parts?
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
    let mut found_cost = None;

    const OFFSET: f64 = 10.0;

    for (full_cost, new_apps) in matches {
        if let Some(found) = found_cost { if full_cost > found + r64(OFFSET) { break } }
        for (rw_i, lhs, subst, cx_cost, pat_cost) in &new_apps {
            let rw = &rws[*rw_i];
            rw.applier.apply_one(eg, *lhs, subst, None, rw.name);
            if eg_data(eg) != og_data { found_cost = Some(full_cost); }
        }
    }

    eg.rebuild();
}

type EGData = (usize, usize);
fn eg_data(eg: &EGraph<L, N>) -> EGData {
    (eg.number_of_classes(), eg.total_size())
}

fn pat_cost(pat: &PatternAst<L>, subst: &Subst, ex: &Extractor<C, L, N>) -> R64 {
    let mut vec: Vec<f64> = Vec::new();
    for i in 0..pat.as_ref().len() {
        let cost = match &pat[i.into()] {
            ENodeOrVar::ENode(n) => mk_C().cost(n, |i| vec[usize::from(i)]),
            ENodeOrVar::Var(v) => ex.find_best_cost(subst[*v]),
        };
        vec.push(cost);
    }
    r64(vec.last().copied().unwrap())
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
