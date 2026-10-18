//! Bounded Cantor enumeration — the generic half of the spec's
//! `oracle` binding machinery.
//!
//! The domain legs of `oracle._binding_envs` (leaf binding banks,
//! shape-valid attr domains, `JOINT_SHAPES`) stay domain data; what
//! this module ports is the *fair enumeration skeleton* underneath:
//!
//! * [`combos_at_sum`] / [`diag_product`] — `oracle._combos_at_sum` /
//!   `oracle._diag_product`: `product(*lists)` in Cantor index-sum
//!   order. A cap truncates a *corner* of the product space, not a
//!   whole dimension — the ordering is the contract.
//! * [`LazySeq`] — `oracle._LazySeq`: indexed pull over an iterator,
//!   materializing on demand only.
//! * [`diag_groups`] — `oracle._diag_groups`: the ragged
//!   `(viewed × attr)` product interleaved by `v + a`.
//! * [`binding_envs`] — `oracle._binding_envs`: the outer
//!   `(base, free-combo)` diagonal with lazy base pull and the
//!   [`MAX_BINDING_ENVS`] work bound.
//! * [`escalate_limit`] — `oracle.escalate_limit`: the selective
//!   guarded-cap policy.

/// Hard cap on the binding environments [`binding_envs`] enumerates
/// per sweep — `oracle._MAX_BINDING_ENVS` verbatim.
///
/// Consumers bound the *sites* they keep, but a veto (a `derive`
/// declining) or an uninstantiable pair consumes an env without
/// producing a site — the env count is the work bound a
/// veto-everything guard needs. The largest legitimate sweep the spec
/// measured is ~180k envs, so the cap preserves it with headroom
/// while bounding a pathological sweep to a fixed corner of the
/// Cantor order.
pub const MAX_BINDING_ENVS: usize = 250_000;

/// Cap on synthesized instances per candidate — `oracle._MAX_INSTANCES`,
/// the default sweep window.
pub const MAX_INSTANCES: usize = 360;

/// Cap on the viewed-binding rows a domain enumeration may open —
/// `oracle._MAX_VIEWED_BINDINGS`.
pub const MAX_VIEWED_BINDINGS: usize = 512;

/// Second-phase cap for a *starved* guarded-region sweep —
/// `oracle._GUARDED_CAP`. See [`escalate_limit`].
pub const GUARDED_CAP: usize = 2000;

/// Return the effective enumeration cap after one guarded sweep —
/// `oracle.escalate_limit`.
///
/// The selective cap policy: the default window stays the common
/// case. A sweep escalates to [`GUARDED_CAP`] only when it is
/// *starved* — the rule carries a guard (`guarded`) and the window
/// accepted no site at all (`accepted == 0`), i.e. it reached only
/// declines and guard errors. The escalation never fires for an
/// unguarded rule nor for a window that already accepted a site; the
/// returned cap is never below `limit`.
pub fn escalate_limit(limit: usize, guarded: bool, accepted: usize) -> usize {
    if guarded && accepted == 0 {
        return limit.max(GUARDED_CAP);
    }
    limit
}

// ---------------------------------------------------------------------------
//  Diagonal product — oracle._combos_at_sum / oracle._diag_product
// ---------------------------------------------------------------------------

/// Yield `product(*lists)` tuples whose index-sum is `total` —
/// `oracle._combos_at_sum`.
///
/// The recursive generator is boxed so the nesting is lazy; the
/// yielded order matches the spec exactly (first coordinate
/// outermost, index `i > total` short-circuits the head scan).
pub fn combos_at_sum<T: Clone>(
    lists: &[Vec<T>],
    total: usize,
) -> Box<dyn Iterator<Item = Vec<T>> + '_> {
    if lists.is_empty() {
        return Box::new((total == 0).then(Vec::new).into_iter());
    }
    let (head, rest) = lists.split_first().unwrap();
    Box::new(
        head.iter()
            .enumerate()
            .take_while(move |(i, _)| *i <= total)
            .flat_map(move |(i, v)| {
                let v = v.clone();
                combos_at_sum(rest, total - i).map(move |mut tail| {
                    let mut out = Vec::with_capacity(tail.len() + 1);
                    out.push(v.clone());
                    out.append(&mut tail);
                    out
                })
            }),
    )
}

/// Owned-list variant of [`combos_at_sum`] — the recursion shares
/// `lists` through `Rc` so the boxed iterator can be `'static`.
fn combos_at_sum_rc<T: Clone + 'static>(
    lists: std::rc::Rc<Vec<Vec<T>>>,
    start: usize,
    total: usize,
) -> Box<dyn Iterator<Item = Vec<T>>> {
    if start >= lists.len() {
        return Box::new((total == 0).then(Vec::new).into_iter());
    }
    let head = lists[start].clone();
    Box::new(
        head.into_iter()
            .enumerate()
            .take_while(move |(i, _)| *i <= total)
            .flat_map(move |(i, v)| {
                let lists = lists.clone();
                combos_at_sum_rc(lists, start + 1, total - i).map(move |mut tail| {
                    tail.insert(0, v.clone());
                    tail
                })
            }),
    )
}

/// Yield `product(*lists)` in Cantor (index-sum) order —
/// `oracle._diag_product`.
///
/// `itertools.product` advances the last coordinate fastest, so a
/// capped enumeration barely moves the early coordinates. Diagonal
/// order covers the low-index corner of every coordinate first: a cap
/// truncates a *corner* of the product space, not a whole dimension.
/// An empty list empties the product — the spec's early `return`.
pub fn diag_product<T: Clone + 'static>(lists: Vec<Vec<T>>) -> Box<dyn Iterator<Item = Vec<T>>> {
    if lists.iter().any(Vec::is_empty) {
        return Box::new(std::iter::empty());
    }
    let lists = std::rc::Rc::new(lists);
    let max_total: usize = lists.iter().map(|l| l.len() - 1).sum();
    Box::new((0..=max_total).flat_map(move |total| combos_at_sum_rc(lists.clone(), 0, total)))
}

// ---------------------------------------------------------------------------
//  LazySeq + diag_groups — the ragged diagonal
// ---------------------------------------------------------------------------

/// Indexed pull over an iterator — `oracle._LazySeq`.
///
/// `get(i)` returns the i-th yielded item or `None` once exhausted.
/// The diag interleaves probe element `a` of every group before any
/// group's `a+1`, so the enumeration only ever materializes the
/// prefix a cap reaches — the eager `list` form paid the whole
/// product before the first env yielded.
pub struct LazySeq<T> {
    it: Box<dyn Iterator<Item = T>>,
    items: Vec<T>,
    done: bool,
}

impl<T: 'static> LazySeq<T> {
    /// Wrap an iterator.
    pub fn new(it: impl Iterator<Item = T> + 'static) -> LazySeq<T> {
        LazySeq {
            it: Box::new(it),
            items: Vec::new(),
            done: false,
        }
    }

    /// Wrap an already-materialized sequence — the spec's
    /// "plain list" group case.
    ///
    /// `done` still reads `false` until a [`get`](LazySeq::get)
    /// probes past the end — the spec's semantics: `done` marks
    /// "source exhausted by probe", not "buffer empty".
    pub fn from_vec(items: Vec<T>) -> LazySeq<T> {
        LazySeq {
            it: Box::new(std::iter::empty()),
            items,
            done: false,
        }
    }

    /// Return the i-th item, or `None` past the end — `get(i)`.
    ///
    /// A probe past the end marks the sequence done (the spec's
    /// `StopIteration` → `done = True`).
    pub fn get(&mut self, i: usize) -> Option<&T> {
        while self.items.len() <= i && !self.done {
            match self.it.next() {
                Some(v) => self.items.push(v),
                None => self.done = true,
            }
        }
        self.items.get(i)
    }

    /// Whether the source is exhausted — `done`.
    pub fn done(&self) -> bool {
        self.done
    }
}

/// Yield `groups[v][a]` in increasing `v + a` (Cantor) order —
/// `oracle._diag_groups`.
///
/// `groups[v]` is one base's list of combination items; lengths
/// differ, so the diagonal — not a nested product — keeps the
/// low-index corner of *every* group ahead of any group's deep tail.
/// A probe past a group's end marks it done; the yielded order is the
/// spec's exactly.
pub fn diag_groups<T: Clone + 'static>(groups: Vec<LazySeq<T>>) -> DiagGroups<T> {
    DiagGroups {
        lazies: groups,
        total: 0,
        v: 0,
        started: false,
    }
}

/// The iterator [`diag_groups`] returns.
pub struct DiagGroups<T> {
    lazies: Vec<LazySeq<T>>,
    total: usize,
    /// Down-counter for the current round's `v` scan — the spec's
    /// `range(min(total, n-1), -1, -1)`.
    v: usize,
    started: bool,
}

impl<T: Clone + 'static> Iterator for DiagGroups<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        let n = self.lazies.len();
        if n == 0 {
            return None;
        }
        loop {
            if !self.started {
                self.started = true;
                self.v = self.total.min(n - 1) + 1; // exclusive bound
            }
            while self.v > 0 {
                let v = self.v - 1;
                self.v -= 1;
                let a = self.total - v;
                if let Some(item) = self.lazies[v].get(a) {
                    return Some(item.clone());
                }
            }
            // Round exhausted — `while not all(g.done for g in lazies)`.
            if self.lazies.iter().all(|g| g.done()) {
                return None;
            }
            self.total += 1;
            self.v = self.total.min(n - 1) + 1;
        }
    }
}

// ---------------------------------------------------------------------------
//  binding_envs — the outer (base, free-combo) diagonal
// ---------------------------------------------------------------------------

/// One entry in the [`binding_envs`] interleave: a base plus its
/// combo stream — the spec's `[base, free-combo generator, alive]`.
struct Entry<B, I: Iterator> {
    base: B,
    combos: I,
    alive: bool,
}

/// The iterator [`binding_envs`] returns.
pub struct BindingEnvs<B, C, S, I>
where
    S: Iterator<Item = (B, I)>,
    I: Iterator<Item = C>,
{
    src: std::iter::Fuse<S>,
    src_done: bool,
    entries: Vec<Entry<B, I>>,
    total: usize,
    live: usize,
    envs: usize,
    cap: usize,
    /// Down-counter for the current round's `i` scan — the spec's
    /// `range(min(total, len(entries)-1), -1, -1)`.
    i: usize,
    round_started: bool,
    _c: std::marker::PhantomData<C>,
}

/// [`binding_envs_capped`] at the spec's [`MAX_BINDING_ENVS`].
pub fn binding_envs<B, C, S, I>(src: S) -> BindingEnvs<B, C, S, I>
where
    S: Iterator<Item = (B, I)>,
    I: Iterator<Item = C>,
{
    binding_envs_capped(src, MAX_BINDING_ENVS)
}

/// Yield `(base, free-combo)` pairs in Cantor order —
/// `oracle._binding_envs`.
///
/// `src` yields the enumeration's *bases*: each is a `(base, combos)`
/// pair — the domain's `(viewed × attr)` merged binding plus the
/// free-dimension combo stream it opens. Round `total` pulls every
/// due base lazily (`entries[total]` — a capped sweep never
/// materializes bases it cannot yield), then each live entry `i`
/// contributes its `(total - i)`-th combo, scanned in descending `i`.
/// The merge is the caller's — the spec folds `base` and `free` into
/// one dict; here the pair stays typed.
///
/// The enumeration stops after `cap` yielded pairs even when space
/// remains — consumers bound the sites they keep, but a veto consumes
/// an env without producing one, so the env count is the work bound.
pub fn binding_envs_capped<B, C, S, I>(src: S, cap: usize) -> BindingEnvs<B, C, S, I>
where
    S: Iterator<Item = (B, I)>,
    I: Iterator<Item = C>,
{
    BindingEnvs {
        src: src.fuse(),
        src_done: false,
        entries: Vec::new(),
        total: 0,
        live: 0,
        envs: 0,
        cap,
        i: 0,
        round_started: false,
        _c: std::marker::PhantomData,
    }
}

impl<B: Clone, C, S, I> Iterator for BindingEnvs<B, C, S, I>
where
    S: Iterator<Item = (B, I)>,
    I: Iterator<Item = C>,
{
    type Item = (B, C);

    fn next(&mut self) -> Option<(B, C)> {
        if self.envs >= self.cap {
            return None;
        }
        loop {
            if !self.round_started {
                // `_pull_bases`: pull every base due at this round —
                // entries with index <= `total`. A base whose combo
                // stream is empty still lands (alive until its first
                // pull), matching the spec's appended-entry counting.
                while !self.src_done && self.entries.len() <= self.total {
                    match self.src.next() {
                        Some((base, combos)) => {
                            self.entries.push(Entry {
                                base,
                                combos,
                                alive: true,
                            });
                            self.live += 1;
                        }
                        None => {
                            self.src_done = true;
                            break;
                        }
                    }
                }
                self.i = self.total.min(self.entries.len().saturating_sub(1)) + 1;
                self.round_started = true;
            }
            while self.i > 0 {
                let idx = self.i - 1;
                self.i -= 1;
                let entry = &mut self.entries[idx];
                if !entry.alive {
                    continue;
                }
                match entry.combos.next() {
                    None => {
                        entry.alive = false;
                        self.live -= 1;
                    }
                    Some(c) => {
                        self.envs += 1;
                        return Some((entry.base.clone(), c));
                    }
                }
            }
            // Round exhausted — the spec's `while live or not src.done`.
            if self.live == 0 && self.src_done {
                return None;
            }
            self.total += 1;
            self.round_started = false;
        }
    }
}
