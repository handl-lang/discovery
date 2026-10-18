//! Term-level pattern machinery — the pure-compute half of the
//! spec's `egraph.terms` / `meta` helpers.
//!
//! Ports, by contract:
//!
//! * `_term_match` — structural match of a pattern against a plain
//!   term: [`Term::Var`] binds subterms (repeated metavars must bind
//!   structurally equal terms), [`TermAttr::Meta`] binds attr values,
//!   concrete attr values compare with `match_eq` (the spec's
//!   match-time numeric leniency).
//! * `_term_instantiate` ([`instantiate_lenient`]) — unbound *term*
//!   metavariables are a veto (`None`, the spec's `KeyError`), unbound
//!   *attr* metavariables fall back to their literal name (the spec's
//!   `subst.get("$attr:"+v, v)` wart — kept: callers may observe it).
//! * `meta.instantiate_pattern` ([`instantiate_strict`]) — any unbound
//!   metavariable vetoes.
//! * `meta._reexpress_binding` / `meta._compose_guards` /
//!   `meta._rhs_derive_placeholders` — the guard-transport core the
//!   rulecache and the object store replay.
//! * The oracle's generic pattern introspection — [`leaf_metavars`],
//!   [`metavar_parents`], [`free_mvs`] — with the domain's "viewish"
//!   alphabet injected as data.

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use handl_egraph::{AttrValue, BoundEnv, Check, Derive, Derived, Rewrite, Term, TermAttr};

/// The namespaced-derive prefixes a composite carries —
/// `meta._DRV_PREFIX` verbatim: `"@1:"` for parent 1's outputs,
/// `"@2:"` for parent 2's.
pub const DRV_PREFIX: [&str; 2] = ["@1:", "@2:"];

/// A re-expression spec: the maps `pat1`/`pat2` of the spec's
/// `guard_pats` — each parent's metavariables expressed as *patterns
/// over the derived rule's* metavariables.
///
/// `terms` maps a parent term metavariable to a pattern term;
/// `attrs` maps a parent attribute metavariable to either a concrete
/// value (`TermAttr::Lit`) or a reference to a derived-rule attr
/// metavariable (`TermAttr::Meta` — resolved through the fired
/// binding at guard time). The typed `Meta`/`Lit` split is a named
/// improvement over the spec's wire form, where a plain string attr
/// is ambiguously both.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ReExpr {
    /// Parent term metavariable -> pattern over derived metavars.
    pub terms: BTreeMap<Rc<str>, Term>,
    /// Parent attr metavariable -> literal value or meta reference.
    pub attrs: BTreeMap<Rc<str>, TermAttr>,
}

/// A minted composite: the rewrite plus the provenance a store
/// round-trips.
///
/// The spec attaches `.parents` / `.guard_pats` to the `Rewrite`
/// object dynamically (a name wart); Rust carries them explicitly.
/// `parents` is `None` until a guard transport resolves — matching
/// the spec, where the attribute is only set on the transported
/// rebuild path.
pub struct Mint {
    /// The live rewrite.
    pub rule: Rewrite,
    /// The parent rule names the composite was minted from (empty
    /// for axioms / non-composites).
    pub parents: Vec<Rc<str>>,
    /// The `(pat1, pat2)` re-expression spec the composite hooks were
    /// built from — `Some` on every spec-transported mint.
    pub guard_pats: Option<(ReExpr, ReExpr)>,
}

impl Mint {
    /// Wrap a bare rewrite — an axiom or a spec-less object.
    pub fn bare(rule: Rewrite) -> Mint {
        Mint {
            rule,
            parents: Vec::new(),
            guard_pats: None,
        }
    }
}

impl std::ops::Deref for Mint {
    type Target = Rewrite;
    fn deref(&self) -> &Rewrite {
        &self.rule
    }
}

impl std::fmt::Debug for Mint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Mint")
            .field("rule", &self.rule)
            .field("parents", &self.parents)
            .field("guarded", &self.guard_pats.is_some())
            .finish()
    }
}

// ---------------------------------------------------------------------------
//  Pattern introspection (the oracle's generic half)
// ---------------------------------------------------------------------------

/// Ordered unique metavariable names at leaf positions —
/// `oracle._leaf_metavars`.
///
/// DFS pre-order over the pattern; first occurrence wins.
pub fn leaf_metavars(pat: &Term) -> Vec<Rc<str>> {
    fn walk(t: &Term, out: &mut Vec<Rc<str>>) {
        match t {
            Term::Var(name) => {
                if !out.contains(name) {
                    out.push(name.clone());
                }
            }
            Term::Leaf(_) => {}
            Term::Op(op) => {
                for a in op.args.iter() {
                    walk(a, out);
                }
            }
        }
    }
    let mut out = Vec::new();
    walk(pat, &mut out);
    out
}

/// Map each leaf metavariable to the op names of its immediate parent
/// nodes — `oracle._parents` over one pattern.
pub fn metavar_parents(pats: &[&Term]) -> BTreeMap<Rc<str>, BTreeSet<Rc<str>>> {
    fn walk(t: &Term, out: &mut BTreeMap<Rc<str>, BTreeSet<Rc<str>>>) {
        if let Term::Op(op) = t {
            for a in op.args.iter() {
                if let Term::Var(name) = a {
                    out.entry(name.clone()).or_default().insert(op.op.clone());
                }
                walk(a, out);
            }
        }
    }
    let mut out: BTreeMap<Rc<str>, BTreeSet<Rc<str>>> = BTreeMap::new();
    for pat in pats {
        walk(pat, &mut out);
    }
    // The spec seeds every leaf metavar with an empty parent set.
    for pat in pats {
        for m in leaf_metavars(pat) {
            out.entry(m).or_default();
        }
    }
    out
}

/// The metavariables with no "viewish" parent, minus the covered set —
/// `oracle._free_mvs` with the domain's viewish alphabet injected.
///
/// `viewish` is the domain's view-op set (the spec's `_VIEWISH`); a
/// metavariable is *free* when none of its parent ops is viewish.
/// Sorted output, matching `sorted(...)` upstream.
pub fn free_mvs(
    parents: &BTreeMap<Rc<str>, BTreeSet<Rc<str>>>,
    covered: &BTreeSet<Rc<str>>,
    viewish: &BTreeSet<Rc<str>>,
) -> Vec<Rc<str>> {
    parents
        .iter()
        .filter(|(m, ops)| !covered.contains(*m) && ops.is_disjoint(viewish))
        .map(|(m, _)| m.clone())
        .collect()
}

/// Every node carrying an attr metavariable — `oracle._view_nodes`.
///
/// Dedup is structural (the spec dedups by `id()`; equal subtrees in
/// this crate share no identity, so the structural read is the honest
/// one — a repeated identical subtree contributes once).
pub fn meta_attr_nodes(pats: &[&Term]) -> Vec<Term> {
    let mut out: Vec<Term> = Vec::new();
    let mut seen: BTreeSet<Term> = BTreeSet::new();
    let mut stack: Vec<&Term> = pats.to_vec();
    while let Some(t) = stack.pop() {
        if seen.contains(t) {
            continue;
        }
        seen.insert(t.clone());
        if let Term::Op(op) = t {
            if op.attrs.iter().any(|(_, v)| matches!(v, TermAttr::Meta(_))) {
                out.push(t.clone());
            }
            stack.extend(op.args.iter());
        }
    }
    out
}

/// All metavariables in a pattern — `meta.pattern_metavars`.
///
/// Returns `(term metavars, attr metavars)` — the typed split the
/// spec encodes under the `"$attr:"` key prefix.
pub fn pattern_metavars(pat: &Term) -> (BTreeSet<Rc<str>>, BTreeSet<Rc<str>>) {
    let mut terms = BTreeSet::new();
    let mut attrs = BTreeSet::new();
    fn walk(t: &Term, terms: &mut BTreeSet<Rc<str>>, attrs: &mut BTreeSet<Rc<str>>) {
        match t {
            Term::Var(n) => {
                terms.insert(n.clone());
            }
            Term::Leaf(_) => {}
            Term::Op(op) => {
                for a in op.args.iter() {
                    walk(a, terms, attrs);
                }
                for (_, v) in op.attrs.iter() {
                    if let TermAttr::Meta(n) = v {
                        attrs.insert(n.clone());
                    }
                }
            }
        }
    }
    walk(pat, &mut terms, &mut attrs);
    (terms, attrs)
}

// ---------------------------------------------------------------------------
//  Term-level match / instantiate
// ---------------------------------------------------------------------------

/// Structural match of a pattern against a plain term —
/// `egraph.terms._term_match`.
///
/// `subst.terms` maps metavariables to *subterms* (the term-level
/// convention — the e-graph maps them to e-class ids instead).
/// Repeated metavariables must bind structurally equal subterms;
/// `TermAttr::Meta` binds into `subst.attrs`; literal attrs compare
/// with `AttrValue::match_eq` (numeric leniency, the spec's `!=`).
///
/// Returns `false` on mismatch; `subst` may be partially extended on
/// failure — the spec's contract, kept (callers pass a fresh env).
pub fn match_pattern(pat: &Term, term: &Term, subst: &mut BoundEnv) -> bool {
    match (pat, term) {
        (Term::Var(name), _) => match subst.terms.get(name) {
            None => {
                subst.terms.insert(name.clone(), term.clone());
                true
            }
            Some(prev) => prev == term,
        },
        (Term::Leaf(k), Term::Leaf(tk)) => k == tk,
        (Term::Leaf(_), _) => false,
        (
            Term::Op(handl_egraph::Op { op, args, attrs }),
            Term::Op(handl_egraph::Op {
                op: top,
                args: targs,
                attrs: tattrs,
            }),
        ) => {
            if op != top || args.len() != targs.len() || attrs.len() != tattrs.len() {
                return false;
            }
            // The spec gates on key-set equality; sorted unique keys
            // make the zip below exact under the length check.
            for ((k, pv), (tk, tv)) in attrs.iter().zip(tattrs.iter()) {
                if k != tk {
                    return false;
                }
                match pv {
                    TermAttr::Meta(name) => {
                        let TermAttr::Lit(nv) = tv else {
                            return false;
                        };
                        match subst.attrs.get(name) {
                            None => {
                                subst.attrs.insert(name.clone(), nv.clone());
                            }
                            Some(prev) => {
                                if prev != nv {
                                    return false;
                                }
                            }
                        }
                    }
                    TermAttr::Lit(pv) => {
                        let TermAttr::Lit(nv) = tv else {
                            return false;
                        };
                        if !nv.match_eq(pv) {
                            return false;
                        }
                    }
                }
            }
            args.iter()
                .zip(targs.iter())
                .all(|(pa, ta)| match_pattern(pa, ta, subst))
        }
        (Term::Op(_), _) => false,
    }
}

/// Instantiate a pattern — `meta.instantiate_pattern` (strict).
///
/// Any unbound metavariable (term or attr) is a veto: `None`, the
/// spec's `KeyError`.
pub fn instantiate_strict(pat: &Term, subst: &BoundEnv) -> Option<Term> {
    match pat {
        Term::Var(name) => subst.terms.get(name).cloned(),
        Term::Leaf(_) => Some(pat.clone()),
        Term::Op(op) => {
            let mut args = Vec::with_capacity(op.args.len());
            for a in op.args.iter() {
                args.push(instantiate_strict(a, subst)?);
            }
            let mut attrs = Vec::with_capacity(op.attrs.len());
            for (k, v) in op.attrs.iter() {
                let nv = match v {
                    TermAttr::Lit(v) => TermAttr::Lit(v.clone()),
                    TermAttr::Meta(name) => TermAttr::Lit(subst.attrs.get(name)?.clone()),
                };
                attrs.push((k.clone(), nv));
            }
            Some(Term::Op(handl_egraph::Op {
                op: op.op.clone(),
                args: args.into(),
                attrs: attrs.into(),
            }))
        }
    }
}

/// Instantiate a pattern — `egraph.terms._term_instantiate`
/// (lenient).
///
/// Unbound *term* metavariables veto (`None`); unbound *attr*
/// metavariables fall back to their literal name as a string attr —
/// the spec's `subst.get("$attr:"+v, v)` wart, kept verbatim so a
/// caller sees the same instantiated term the spec would mint.
pub fn instantiate_lenient(pat: &Term, subst: &BoundEnv) -> Option<Term> {
    match pat {
        Term::Var(name) => subst.terms.get(name).cloned(),
        Term::Leaf(_) => Some(pat.clone()),
        Term::Op(op) => {
            let mut args = Vec::with_capacity(op.args.len());
            for a in op.args.iter() {
                args.push(instantiate_lenient(a, subst)?);
            }
            let mut attrs = Vec::with_capacity(op.attrs.len());
            for (k, v) in op.attrs.iter() {
                let nv = match v {
                    TermAttr::Lit(v) => v.clone(),
                    TermAttr::Meta(name) => subst
                        .attrs
                        .get(name)
                        .cloned()
                        .unwrap_or_else(|| AttrValue::from(name.as_ref())),
                };
                attrs.push((k.clone(), TermAttr::Lit(nv)));
            }
            Some(Term::Op(handl_egraph::Op {
                op: op.op.clone(),
                args: args.into(),
                attrs: attrs.into(),
            }))
        }
    }
}

/// The namespaced derive placeholders in a derived RHS —
/// `meta._rhs_derive_placeholders`.
///
/// `"@1:"`/`"@2:"`-prefixed metavariables (term or attr position) the
/// composite `derive` must refill. The spec returns a set; callers
/// here only need membership, but the set is the honest return.
pub fn rhs_derive_placeholders(rhs: &Term) -> BTreeSet<Rc<str>> {
    let mut out = BTreeSet::new();
    fn walk(t: &Term, out: &mut BTreeSet<Rc<str>>) {
        match t {
            Term::Var(name) => {
                if DRV_PREFIX.iter().any(|p| name.starts_with(p)) {
                    out.insert(name.clone());
                }
            }
            Term::Leaf(_) => {}
            Term::Op(op) => {
                for (_, v) in op.attrs.iter() {
                    if let TermAttr::Meta(name) = v
                        && DRV_PREFIX.iter().any(|p| name.starts_with(p))
                    {
                        out.insert(name.clone());
                    }
                }
                for a in op.args.iter() {
                    walk(a, out);
                }
            }
        }
    }
    walk(rhs, &mut out);
    out
}

// ---------------------------------------------------------------------------
//  Guard transport — meta._reexpress_binding / meta._compose_guards
// ---------------------------------------------------------------------------

/// Instantiate a re-expression spec against a fired binding —
/// `meta._reexpress_binding`.
///
/// Term metavars instantiate as patterns (strict); an attr `Meta`
/// entry resolves through *subst* — a missing key is an
/// un-reexpressible reference and rejects the composition (`None`).
pub fn reexpress_binding(pats: &ReExpr, subst: &BoundEnv) -> Option<BoundEnv> {
    let mut out = BoundEnv::default();
    for (k, pat) in pats.terms.iter() {
        out.terms.insert(k.clone(), instantiate_strict(pat, subst)?);
    }
    for (k, pv) in pats.attrs.iter() {
        let v = match pv {
            TermAttr::Meta(name) => subst.attrs.get(name)?.clone(),
            TermAttr::Lit(v) => v.clone(),
        };
        out.attrs.insert(k.clone(), v);
    }
    Some(out)
}

/// The `(check, derive)` pair a parent hook tuple produced —
/// `None`/`None` when neither parent is guarded.
type Composed = (Option<Box<Check>>, Option<Box<Derive>>);

/// Namespaced extras from one parent's `derive` applied to the
/// re-expression channel.
///
/// `Attr`/`Term` outputs join the effective binding under the
/// `"@i:"` namespace; `Class` outputs cannot appear in a term-level
/// `BoundEnv` — they are kept in a side map, where a pat2 reference
/// reads as un-reexpressible (the spec would inject the raw eid as
/// a term — a wart this port refuses, conservatively: the composite
/// vetoes instead of minting a nonsense binding).
struct Eff {
    env: BoundEnv,
    classes: BTreeSet<Rc<str>>,
}

fn apply_extras(eff: &mut Eff, ns: &str, extras: &[Derived]) {
    for d in extras {
        match d {
            Derived::Attr(k, v) => {
                eff.env
                    .attrs
                    .insert(Rc::from(format!("{ns}{k}").as_str()), v.clone());
            }
            Derived::Term(k, t) => {
                eff.env
                    .terms
                    .insert(Rc::from(format!("{ns}{k}").as_str()), t.clone());
            }
            Derived::Class(k, _) => {
                eff.classes.insert(Rc::from(format!("{ns}{k}").as_str()));
            }
        }
    }
}

/// `reexpress_binding` over an [`Eff`] — a term pattern referencing
/// a class-bound name vetoes (un-reexpressible).
fn reexpress_eff(pats: &ReExpr, eff: &Eff) -> Option<BoundEnv> {
    for pat in pats.terms.values() {
        let (tvars, _) = pattern_metavars(pat);
        if tvars.iter().any(|v| eff.classes.contains(v)) {
            return None;
        }
    }
    reexpress_binding(pats, &eff.env)
}

fn call_check(r: &Rewrite, env: &BoundEnv) -> bool {
    match &r.check {
        None => true,
        // The spec wraps hook calls in try/except — a raising guard
        // vetoes. A panicking hook is the same signal in Rust.
        Some(c) => {
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| c(env))).unwrap_or(false)
        }
    }
}

fn call_derive(r: &Rewrite, env: &BoundEnv) -> Option<Vec<Derived>> {
    match &r.derive {
        None => Some(Vec::new()),
        Some(d) => {
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| d(env))).unwrap_or(None)
        }
    }
}

/// The spec's `_eval` closure: evaluate both parents' guards on the
/// derived binding. Returns the parents' bindings plus their derive
/// outputs, or `None` on any veto.
///
/// `pat2` is instantiated over the *derived* rule's metavars plus
/// `r1`'s namespaced derive outputs — never `b1`'s namespace (the
/// spec's `eff1 = dict(bound)` comment: merging `b1` would clobber a
/// derived metavar sharing an r1 name).
fn compose_eval(
    r1: &Mint,
    r2: &Mint,
    pat1: &ReExpr,
    pat2: &ReExpr,
    bound: &BoundEnv,
) -> Option<(BoundEnv, Vec<Derived>, BoundEnv, Vec<Derived>)> {
    let b1 = reexpress_binding(pat1, bound)?;
    if !call_check(r1, &b1) {
        return None;
    }
    let mut eff1 = Eff {
        env: bound.clone(),
        classes: BTreeSet::new(),
    };
    let e1 = call_derive(r1, &b1)?;
    apply_extras(&mut eff1, DRV_PREFIX[0], &e1);
    let b2 = reexpress_eff(pat2, &eff1)?;
    if !call_check(r2, &b2) {
        return None;
    }
    let e2 = call_derive(r2, &b2)?;
    Some((b1, e1, b2, e2))
}

/// Build the derived rule's `(check, derive)` from the parents' —
/// `meta._compose_guards`.
///
/// The composite check on a fired binding `bound` is
/// `r1.check(b1) && r2.check(b2)` where `b_i` is the parent's
/// re-expressed binding; derive hooks re-run (they can veto) and
/// their outputs fill the `"@i:"` placeholders the derived RHS
/// carries. Returns `(None, None)` when neither parent is guarded.
pub fn compose_guards(r1: Rc<Mint>, r2: Rc<Mint>, pat1: ReExpr, pat2: ReExpr) -> Composed {
    if r1.check.is_none() && r1.derive.is_none() && r2.check.is_none() && r2.derive.is_none() {
        return (None, None);
    }
    struct Ctx {
        r1: Rc<Mint>,
        r2: Rc<Mint>,
        pat1: ReExpr,
        pat2: ReExpr,
    }
    let ctx = Rc::new(Ctx { r1, r2, pat1, pat2 });
    let c1 = ctx.clone();
    let check: Box<Check> = Box::new(move |bound: &BoundEnv| {
        compose_eval(&c1.r1, &c1.r2, &c1.pat1, &c1.pat2, bound).is_some()
    });
    let derive: Box<Derive> = Box::new(move |bound: &BoundEnv| {
        let (_, e1, _, e2) = compose_eval(&ctx.r1, &ctx.r2, &ctx.pat1, &ctx.pat2, bound)?;
        let mut out: Vec<Derived> = Vec::new();
        for (e, ns) in [(e1, DRV_PREFIX[0]), (e2, DRV_PREFIX[1])] {
            for d in e {
                out.push(match d {
                    Derived::Attr(k, v) => Derived::Attr(Rc::from(format!("{ns}{k}").as_str()), v),
                    Derived::Term(k, t) => Derived::Term(Rc::from(format!("{ns}{k}").as_str()), t),
                    Derived::Class(k, c) => {
                        Derived::Class(Rc::from(format!("{ns}{k}").as_str()), c)
                    }
                });
            }
        }
        Some(out)
    });
    (Some(check), Some(derive))
}
