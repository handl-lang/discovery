//! The evidence leg — premise-anchored derivability, guarded-region
//! sweeps, and the stored-object seam of the spec's `evidence.py`.
//!
//! Pure compute only: the *store* is a trait ([`ObjectStore`]), the
//! bare-record rebuild is a trait ([`ObjectCodec`]), and the numeric
//! oracle is an injected `eval` closure — the torch truth legs stay
//! in the domain. What is ported:
//!
//! * [`premise_rules`] — `evidence._premise_rules`: a stored object's
//!   transitive premise closure, resolved exactly the way
//!   `admit_object` resolves transport parents — a stored row rebuilt
//!   at full declared strength (`missing_hooks` minus `transported`
//!   empty), walked transitively, cycle-safe. Any shortfall empties
//!   the whole closure: a partial premise set is not the derivation
//!   the object was minted under.
//! * [`premise_steps_verify`] / [`premise_credit`] —
//!   `evidence._premise_steps_verify` / `_premise_credit`: the
//!   anti-gaming bar — every non-axiom step an anchored derivation
//!   *invoked* must site-verify `equal` under the injected oracle, or
//!   the anchored credit is revoked.
//! * [`site_outcome`] / [`guarded_evals`] / [`synth_sites`] /
//!   [`guarded_truth`] — `evidence._site_outcome` / `_guarded_evals` /
//!   `_synth_sites` / `_guarded_truth`: the guarded-region sweep
//!   (every accepted evaluable binding must be equal, and at least
//!   one must exist) with the selective-cap escalation.
//! * [`rebuild_stored`] / [`admit`] — `evidence._rebuild_stored` /
//!   `admit_object`: the stored-record → live-rule path with guard
//!   transport.

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use handl_egraph::{BoundEnv, Derived, Rewrite, Term};

use crate::enumerate::{MAX_INSTANCES, escalate_limit};
use crate::terms::{
    Mint, ReExpr, compose_guards, instantiate_lenient, match_pattern, rhs_derive_placeholders,
};

// ---------------------------------------------------------------------------
//  Object records — the declared-object store's row shape
// ---------------------------------------------------------------------------

/// A stored guard-transport spec — the record's `"guard"` field.
///
/// `parents` names the premise rules; `pat1`/`pat2` are the
/// re-expression maps the composite hooks rebuild from (already
/// decoded — the codec lives in [`crate::codec`]).
#[derive(Clone, Debug)]
pub struct GuardSpec {
    /// The premise rule names (the derivation's parents).
    pub parents: Vec<Rc<str>>,
    /// Parent 1's re-expression map.
    pub pat1: ReExpr,
    /// Parent 2's re-expression map.
    pub pat2: ReExpr,
}

/// A parsed declared-object record — the `lemmas` row's `law_json`.
///
/// The generic fields are decoded; domain fields (`cond`, `dspec`,
/// `cert`, provenance, …) ride `data` — [`ObjectCodec::bare_rule`]
/// and the domain's own readers interpret them. `transported` is the
/// admit-time annotation ([`admit`] fills it), never a stored field —
/// the spec's `record["transported"]` convention.
#[derive(Clone, Debug)]
pub struct ObjectRecord {
    /// The declared name.
    pub name: Rc<str>,
    /// The declaration's provenance kind (`"law"`, `"abstraction"`,
    /// `"bridge"`, …) — `record["kind"]`, `"law"` by default.
    pub kind: Rc<str>,
    /// Pattern pair.
    pub lhs: Term,
    /// See `lhs`.
    pub rhs: Term,
    /// Law/lemma name (metadata).
    pub law: String,
    /// Hooks the record *could not* carry — `missing_hooks`.
    pub missing_hooks: Vec<String>,
    /// The guard-transport spec, when the record is a minted
    /// composite.
    pub guard: Option<GuardSpec>,
    /// Admit-time annotation: the hooks guard transport restored.
    pub transported: Vec<String>,
    /// The full parsed record — domain extension point.
    pub data: serde_json::Value,
}

impl ObjectRecord {
    /// Hooks still missing after transport — `missing_hooks` minus
    /// `transported`, the full-data gate's test.
    pub fn unresolved_hooks(&self) -> Vec<String> {
        self.missing_hooks
            .iter()
            .filter(|h| !self.transported.contains(h))
            .cloned()
            .collect()
    }
}

/// The declared-object store — the spec's sqlite `lemmas` table as a
/// trait.
///
/// Two lookups because the spec has two keys: `admit` resolves by
/// content key (`alpha_key`); premise resolution and transport
/// parents resolve by *name*.
pub trait ObjectStore {
    /// The stored record for an object *name* (a `lemmas.name` row).
    fn record_by_name(&self, name: &str) -> Option<ObjectRecord>;
    /// The stored record for a content key (a `lemmas.alpha_key`
    /// row). Defaults to `None` — stores that only serve names.
    fn record_by_key(&self, _key: &str) -> Option<ObjectRecord> {
        None
    }
}

/// Rebuilds the *bare* rule a record declares —
/// `laws.serialize.object_from_data`.
///
/// "Bare" means pattern + declarative fields, no transported hooks:
/// the domain hydrates whatever `data` carries (`cond`, `dspec`,
/// tags, error bounds). A record claiming a kind the codec does not
/// know is a failure to surface (`Err`), never a silent admit.
pub trait ObjectCodec {
    /// Rebuild the bare rule from a parsed record.
    fn bare_rule(&self, rec: &ObjectRecord) -> Result<Rewrite, String>;
}

/// The codec for records whose patterns are already decoded —
/// `bare_rule` builds the `Rewrite` from the record's generic fields
/// (`name`/`lhs`/`rhs`/`law`) and injects no domain hooks. Records
/// needing `cond`/`dspec` hydration use a domain codec instead.
pub struct GenericCodec;

impl ObjectCodec for GenericCodec {
    fn bare_rule(&self, rec: &ObjectRecord) -> Result<Rewrite, String> {
        let mut rule = Rewrite::new(rec.name.clone(), rec.lhs.clone(), rec.rhs.clone());
        rule.law = rec.law.clone();
        Ok(rule)
    }
}

// ---------------------------------------------------------------------------
//  Admit — evidence._rebuild_stored / admit_object
// ---------------------------------------------------------------------------

/// Rebuild one parsed record, transporting the guard spec if stored —
/// `evidence._rebuild_stored`.
///
/// Returns `(mint, transported)` — *transported* names the
/// `check`/`derive` hooks the guard spec restored (empty when the
/// record carries no spec or the spec could not resolve). A spec
/// resolves only when *both* named parents are stored rows that
/// themselves admit at full declared strength — a parent that
/// rebuilt weaker than it declared is not the object the composite
/// was minted against. *seen* bounds the transitive walk against a
/// cyclic record. On any shortfall the bare rebuild is returned —
/// the same honest partial admit a spec-less record gets.
pub fn rebuild_stored(
    store: &dyn ObjectStore,
    codec: &dyn ObjectCodec,
    rec: &ObjectRecord,
    seen: &BTreeSet<Rc<str>>,
) -> Result<(Rc<Mint>, Vec<String>), String> {
    let rule = codec.bare_rule(rec)?;
    let bare = |rule: Rewrite| Ok((Rc::new(Mint::bare(rule)), Vec::new()));
    let Some(guard) = &rec.guard else {
        return bare(rule);
    };
    if guard.parents.len() != 2 || guard.parents.iter().any(|p| seen.contains(p)) {
        return bare(rule);
    }
    let mut resolved: Vec<Rc<Mint>> = Vec::with_capacity(2);
    let mut next_seen = seen.clone();
    for p in &guard.parents {
        next_seen.insert(p.clone());
    }
    for name in &guard.parents {
        let Some(pdata) = store.record_by_name(name) else {
            return bare(rule);
        };
        let (prule, ptrans) = rebuild_stored(store, codec, &pdata, &next_seen)?;
        // A parent that rebuilt weaker than it declared is not the
        // object the composite was minted against.
        let weak: Vec<String> = pdata
            .missing_hooks
            .iter()
            .filter(|h| !ptrans.contains(h))
            .cloned()
            .collect();
        if !weak.is_empty() {
            return bare(rule);
        }
        resolved.push(prule);
    }
    let (check, drv) = compose_guards(
        resolved[0].clone(),
        resolved[1].clone(),
        guard.pat1.clone(),
        guard.pat2.clone(),
    );
    if check.is_none() && drv.is_none() {
        return bare(rule);
    }
    // Same policy as offer/_dec_rule: the composite derive attaches
    // only where the RHS carries the "@i:" placeholders it refills.
    let derive = drv.filter(|_| !rhs_derive_placeholders(&rule.rhs).is_empty());
    let mut out = rule;
    out.check = check;
    out.derive = derive;
    let mut mint = Mint::bare(out);
    mint.parents = guard.parents.clone();
    mint.guard_pats = Some((guard.pat1.clone(), guard.pat2.clone()));
    let transported: Vec<String> = [
        ("check", mint.check.is_some()),
        ("derive", mint.derive.is_some()),
    ]
    .into_iter()
    .filter(|(_, present)| *present)
    .map(|(h, _)| h.to_string())
    .collect();
    Ok((Rc::new(mint), transported))
}

/// Rebuild a stored object as a live rule — `evidence.admit_object`.
///
/// Returns `(mint, record)` — the reconstructed mint plus the parsed
/// record with `transported` annotated — so the caller can read
/// `record.kind`, `record.missing_hooks`, and `record.transported`
/// before trusting the rule to fire identically to its source. A
/// `missing_hooks` record still rebuilds — pattern plus whatever the
/// codec hydrated — unless a `guard` spec transports its hooks.
pub fn admit(
    store: &dyn ObjectStore,
    codec: &dyn ObjectCodec,
    key: &str,
) -> Result<Option<(Rc<Mint>, ObjectRecord)>, String> {
    let Some(mut rec) = store.record_by_key(key) else {
        return Ok(None);
    };
    let mut seen = BTreeSet::new();
    seen.insert(rec.name.clone());
    let (mint, transported) = rebuild_stored(store, codec, &rec, &seen)?;
    rec.transported = transported;
    Ok(Some((mint, rec)))
}

// ---------------------------------------------------------------------------
//  The premise machinery — derivability anchored on stored premises
// ---------------------------------------------------------------------------

/// Resolve *record*'s transitive premise closure through the store —
/// `evidence._premise_rules`.
///
/// `record.guard.parents` names the rules the object was synthesized
/// from — the premises of the derivation it was minted under. Each
/// member resolves exactly the way [`admit`] resolves transport
/// parents: a stored row rebuilt by [`rebuild_stored`] at full
/// declared strength, with its own `guard.parents` walked
/// transitively. A name already among *base* resolves to the axiom
/// itself — the trusted object, no store row needed.
///
/// `Ok(extras)` is the closure's non-axiom members (the ones the
/// measure leg must add to `base` for the anchored leg),
/// parents-first and de-duplicated by name. A member that resolves
/// short of the bar — no row, a weaker-than-declared admit, a cycle
/// back into the closure — empties the whole closure: `Err(detail)`
/// names the shortfall, and a partial premise set is never returned.
pub fn premise_rules(
    store: &dyn ObjectStore,
    codec: &dyn ObjectCodec,
    record: &ObjectRecord,
    base: &[Rc<Mint>],
) -> Result<Vec<Rc<Mint>>, String> {
    let base_by_name: BTreeMap<Rc<str>, Rc<Mint>> =
        base.iter().map(|m| (m.name.clone(), m.clone())).collect();
    /// The walk's shared context — the store, codec, axiom set, and
    /// the accumulating output.
    struct Walk<'a> {
        store: &'a dyn ObjectStore,
        codec: &'a dyn ObjectCodec,
        base_by_name: BTreeMap<Rc<str>, Rc<Mint>>,
        seen: BTreeSet<Rc<str>>,
        out: Vec<Rc<Mint>>,
        failure: Vec<String>,
    }

    impl Walk<'_> {
        fn go(&mut self, rec: &ObjectRecord, ancestors: &BTreeSet<Rc<str>>) {
            let parents: &[Rc<str>] = match &rec.guard {
                Some(g) => &g.parents,
                None => &[],
            };
            for pname in parents {
                if self.seen.contains(pname) || !self.failure.is_empty() {
                    continue;
                }
                self.seen.insert(pname.clone());
                let Some(pdata) = self.store.record_by_name(pname) else {
                    match self.base_by_name.get(pname) {
                        Some(axiom) => self.out.push(axiom.clone()),
                        None => self
                            .failure
                            .push(format!("premise '{pname}' is not a stored row")),
                    }
                    continue;
                };
                // `rebuild_stored`'s `seen` is the ancestor chain for
                // its cycle guard — the flat `seen` dedup set would
                // make a premise shared by two siblings read as a
                // cycle.
                let mut anc = ancestors.clone();
                anc.insert(pname.clone());
                match rebuild_stored(self.store, self.codec, &pdata, &anc) {
                    Err(e) => self.failure.push(e),
                    Ok((prule, ptrans)) => {
                        let weak: Vec<String> = pdata
                            .missing_hooks
                            .iter()
                            .filter(|h| !ptrans.contains(h))
                            .cloned()
                            .collect();
                        if !weak.is_empty() {
                            self.failure.push(format!(
                                "premise '{pname}' admits weaker than declared ({})",
                                weak.join(", ")
                            ));
                            continue;
                        }
                        self.go(&pdata, &anc);
                        self.out.push(prule);
                    }
                }
            }
        }
    }

    let mut seen: BTreeSet<Rc<str>> = BTreeSet::new();
    seen.insert(record.name.clone());
    // The spec calls `walk(record, frozenset(seen))` — the ancestor
    // chain is a *copy* of the dedup set at entry.
    let ancestors = seen.clone();
    let mut w = Walk {
        store,
        codec,
        base_by_name,
        seen,
        out: Vec::new(),
        failure: Vec::new(),
    };
    w.go(record, &ancestors);
    if !w.failure.is_empty() {
        return Err(w.failure.join("; "));
    }
    Ok(w.out
        .into_iter()
        .filter(|r| !w.base_by_name.contains_key(&r.name))
        .collect())
}

// ---------------------------------------------------------------------------
//  Certificates — the level-2 provenance record the steps audit reads
// ---------------------------------------------------------------------------

/// One replayable derivation step — the cert's per-step record.
///
/// `rule` names the applied rule; `lhs`/`rhs` are the *recorded
/// instance* — the exact terms the step rewrote between.
/// `egraph_dependent` marks a step that needs the graph context (not
/// standalone-replayable data) — the strict verifier refuses them,
/// and the premise audit skips them (they are not premise *uses*).
#[derive(Clone, Debug)]
pub struct CertStep {
    /// The applied rule's name.
    pub rule: Rc<str>,
    /// The recorded step instance — before and after.
    pub lhs: Term,
    /// See `lhs`.
    pub rhs: Term,
    /// Whether the step needs e-graph context to replay.
    pub egraph_dependent: bool,
}

/// A replayable certificate view — the spec's `Certificate` read
/// surface.
///
/// Implemented by domain cert types (the cert codec lives in the
/// domain — `lemma_cert`/`proof.py` stayed in Python); the premise
/// audit only reads `replayable` + `steps`.
pub trait CertView {
    /// Whether every step is standalone-replayable (no
    /// e-graph-dependent residue).
    fn replayable(&self) -> bool;
    /// The recorded steps, in replay order.
    fn steps(&self) -> &[CertStep];
}

// ---------------------------------------------------------------------------
//  Site outcomes and the guarded region
// ---------------------------------------------------------------------------

/// The tri-state evaluation outcome for one bound site —
/// `oracle.eval_instance`'s outcome strings, plus the guard's own
/// `declined`/`guard-err` tags from `evidence._site_outcome`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SiteOutcome {
    /// Both sides evaluated and agree.
    Equal,
    /// Both sides evaluated and differ.
    Unequal,
    /// The instantiated LHS failed to evaluate.
    LhsErr,
    /// The instantiated RHS failed to evaluate — the
    /// ill-typed-mint signal.
    RhsErr,
    /// Both sides failed.
    BothErr,
    /// The binding env itself was unusable (e.g. non-int dims).
    EnvErr,
    /// The guard (check or derive veto) declined this binding.
    Declined,
    /// The guard raised — a non-total predicate.
    GuardErr,
}

impl SiteOutcome {
    /// The spec's outcome spelling.
    pub fn as_str(&self) -> &'static str {
        match self {
            SiteOutcome::Equal => "equal",
            SiteOutcome::Unequal => "unequal",
            SiteOutcome::LhsErr => "lhs-err",
            SiteOutcome::RhsErr => "rhs-err",
            SiteOutcome::BothErr => "both-err",
            SiteOutcome::EnvErr => "env-err",
            SiteOutcome::Declined => "declined",
            SiteOutcome::GuardErr => "guard-err",
        }
    }
}

/// The injected numeric oracle — `oracle.eval_instance` at term
/// level: evaluate the concrete `(lhs, rhs)` pair, return the
/// tri-state outcome. (The spec also returns a note; the sweep only
/// reads the outcome.)
pub type SiteEval = dyn Fn(&Term, &Term) -> SiteOutcome;

/// Evaluate one bound site under *rule*'s guard — `evidence._site_outcome`.
///
/// The guard is the rule's own `check` — the same predicate an
/// e-graph firing consults. A `derive` veto counts as `Declined` (a
/// firing aborts the same way); an uninstantiable RHS counts as
/// `RhsErr`. Otherwise the instantiated pair goes to the injected
/// oracle.
pub fn site_outcome(
    rule: &Rewrite,
    subst: &BoundEnv,
    lhs_i: &Term,
    eval: &SiteEval,
) -> SiteOutcome {
    // The spec's try/except: a raising guard is `guard-err`, a false
    // guard is `declined` — a panic is the same signal in Rust.
    let check_res = match &rule.check {
        None => Ok(true),
        Some(c) => std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| c(subst))),
    };
    let mut ok = match check_res {
        Err(_) => return SiteOutcome::GuardErr,
        Ok(v) => v,
    };
    let mut inst = subst.clone();
    if ok && let Some(d) = &rule.derive {
        let extra =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| d(subst))).unwrap_or(None);
        match extra {
            None => ok = false,
            Some(extras) => {
                for e in extras {
                    match e {
                        Derived::Attr(k, v) => {
                            inst.attrs.insert(k, v);
                        }
                        Derived::Term(k, t) => {
                            inst.terms.insert(k, t);
                        }
                        Derived::Class(k, _) => {
                            // A class-bound extra cannot join a
                            // term-level env — the spec would
                            // inject the raw eid; here it makes
                            // the binding un-reexpressible.
                            inst.terms.remove(&k);
                        }
                    }
                }
            }
        }
    }
    if !ok {
        return SiteOutcome::Declined;
    }
    let Some(rhs_i) = instantiate_lenient(&rule.rhs, &inst) else {
        return SiteOutcome::RhsErr;
    };
    eval(lhs_i, &rhs_i)
}

/// Outcome counts over the bindings an object's guard accepts —
/// `evidence.GuardedRegion`.
#[derive(Clone, Debug, Default)]
pub struct GuardedRegion {
    /// Guard-accepted bindings (check passed, derive did not veto).
    pub accepted: usize,
    /// Guard-declined bindings.
    pub declined: usize,
    /// Bindings the guard raised on (non-total guard — inadmissible).
    pub guard_err: usize,
    /// Accepted + evaluated equal.
    pub equal: usize,
    /// Accepted + evaluated unequal.
    pub unequal: usize,
    /// Accepted but the instantiated RHS cannot denote.
    pub rhs_err: usize,
    /// Accepted + any other error outcome.
    pub other_err: usize,
    /// First equal site's lhs (rendered `Debug`).
    pub witness: String,
    /// First unequal site's lhs.
    pub counterexample: String,
    /// The enumeration cost — sites the sweep evaluated.
    pub envs: usize,
}

/// Evaluate `lhs == rhs` on every guarded site in *sites* —
/// `evidence._guarded_evals`.
///
/// *sites* yields `(env, lhs_term)` pairs — the binding environment
/// plus the instantiated LHS — from real matches or the synthesized
/// domain. The rule's own guard decides which region the equality
/// must hold on.
pub fn guarded_evals(
    rule: &Rewrite,
    sites: impl Iterator<Item = (BoundEnv, Term)>,
    eval: &SiteEval,
) -> GuardedRegion {
    let mut r = GuardedRegion::default();
    for (subst, lhs_i) in sites {
        r.envs += 1;
        match site_outcome(rule, &subst, &lhs_i, eval) {
            SiteOutcome::Declined => r.declined += 1,
            SiteOutcome::GuardErr => r.guard_err += 1,
            out => {
                r.accepted += 1;
                match out {
                    SiteOutcome::Equal => {
                        r.equal += 1;
                        if r.witness.is_empty() {
                            r.witness = format!("{lhs_i:?}");
                        }
                    }
                    SiteOutcome::Unequal => {
                        r.unequal += 1;
                        if r.counterexample.is_empty() {
                            r.counterexample = format!("{lhs_i:?}");
                        }
                    }
                    SiteOutcome::RhsErr => r.rhs_err += 1,
                    _ => r.other_err += 1,
                }
            }
        }
    }
    r
}

/// Whether a guarded region holds no *measured* counterexample —
/// `evidence._region_clean`.
///
/// A measured counterexample is a guard-accepted binding the sweep
/// *evaluated* and found contradictory: `unequal`, `rhs_err`, or
/// `guard_err`. These outrank any derivation.
pub fn region_clean(region: &GuardedRegion) -> bool {
    !(region.unequal > 0 || region.rhs_err > 0 || region.guard_err > 0)
}

/// Whether a guarded region supports the declared equality —
/// `evidence._region_ok`.
///
/// Contradiction-free, and — where `need_equal` — exhibiting at
/// least one equal instance (a guard that accepts nothing provable
/// is vacuous, not verified).
pub fn region_ok(region: &GuardedRegion, need_equal: bool) -> bool {
    region_clean(region) && (!need_equal || region.equal >= 1)
}

/// Yield `(env, lhs_term)` over a domain's synthesized domain —
/// `evidence._synth_sites`.
///
/// `envs` is the domain's binding-env stream (the crate's
/// [`crate::enumerate::binding_envs`] composes the fair ordering;
/// the leaf banks and attr domains are the domain's data).
/// Instantiated `(lhs, rhs)` pairs are deduped so each evaluable
/// site is counted once; the sweep stops at `limit` *deduped* sites.
pub fn synth_sites(
    lhs_pat: &Term,
    rhs_pat: &Term,
    envs: impl Iterator<Item = BoundEnv>,
    limit: usize,
) -> impl Iterator<Item = (BoundEnv, Term)> {
    let mut seen: BTreeSet<(Term, Term)> = BTreeSet::new();
    envs.filter_map(move |env| {
        let pair = (
            instantiate_lenient(lhs_pat, &env),
            instantiate_lenient(rhs_pat, &env),
        );
        match pair {
            (Some(l), Some(r)) if !seen.contains(&(l.clone(), r.clone())) => {
                seen.insert((l.clone(), r));
                Some((env, l))
            }
            _ => None,
        }
    })
    // `len(seen) >= limit` stops the sweep — after the limit-th
    // deduped site is yielded.
    .take(limit)
}

/// Sweep the guard-accepted region of *rule*'s domain —
/// `evidence._guarded_truth`.
///
/// Returns `(synth_region, real_region)`: the synthesized domain
/// filtered by the rule's own guard, and every real corpus match
/// filtered the same way. `real_terms` is the injected corpus;
/// `synth` is a factory producing the domain's site stream at a given
/// limit (the selective-cap escalation re-pulls it once at the wider
/// cap); `eval` is the injected numeric oracle.
pub fn guarded_truth(
    rule: &Rewrite,
    real_terms: &[Term],
    mut synth: impl FnMut(usize) -> Box<dyn Iterator<Item = (BoundEnv, Term)>>,
    eval: &SiteEval,
    limit: usize,
) -> (GuardedRegion, GuardedRegion) {
    let real = guarded_evals(rule, real_sites(rule, real_terms), eval);
    let mut synth_region = guarded_evals(rule, synth(limit), eval);
    let eff = escalate_limit(limit, true, synth_region.accepted);
    if eff > limit {
        let mut wider = guarded_evals(rule, synth(eff), eval);
        // The spec unions the two windows' counts — `envs` sums, the
        // outcome counts replace (the wider window supersedes).
        wider.envs += synth_region.envs;
        synth_region = wider;
    }
    (synth_region, real)
}

/// Every real corpus match of the rule's LHS as `(env, term)` sites —
/// the real half of `evidence._guarded_truth`'s site stream.
///
/// Subterms are deduped *structurally* (the spec dedups by identity —
/// equal subtrees share no `id()` here, so the structural read is the
/// honest one; a repeated identical subtree contributes once).
pub fn real_sites<'a>(
    rule: &'a Rewrite,
    real_terms: &'a [Term],
) -> impl Iterator<Item = (BoundEnv, Term)> + 'a {
    let mut seen: BTreeSet<Term> = BTreeSet::new();
    real_terms
        .iter()
        .flat_map(move |t| {
            let mut subs = Vec::new();
            iter_subterms(t, &mut subs);
            subs.into_iter()
        })
        .filter_map(move |sub| {
            if seen.contains(&sub) {
                return None;
            }
            let mut subst = BoundEnv::default();
            if match_pattern(&rule.lhs, &sub, &mut subst) {
                seen.insert(sub.clone());
                Some((subst, sub))
            } else {
                None
            }
        })
}

/// DFS pre-order subterm enumeration (`_iter_subterms` analogue).
fn iter_subterms(t: &Term, out: &mut Vec<Term>) {
    out.push(t.clone());
    if let Term::Op(op) = t {
        for a in op.args.iter() {
            iter_subterms(a, out);
        }
    }
}

// ---------------------------------------------------------------------------
//  Premise site verification — the anti-gaming bar
// ---------------------------------------------------------------------------

/// Site-verify the non-axiom steps an anchored derivation used —
/// `evidence._premise_steps_verify`.
///
/// Premise-anchored `derivable` is honest only if the premises the
/// derivation *invokes* are true — a false stored rule in the
/// closure would let a false composite fake derivability. The
/// anti-circularity bar, per step naming a rule outside
/// *base_names*: the recorded step instance must numerically
/// evaluate `Equal` under the injected oracle.
///
/// `Ok(used)` names the non-axiom rules site-verified (`[]` = axioms
/// only). `Err(detail)` refuses the anchored credit — a premise
/// false at its applied site, an unverifiable step, or a
/// non-replayable witness; conservative, never guessed.
pub fn premise_steps_verify(
    cert: Option<&dyn CertView>,
    base_names: &BTreeSet<Rc<str>>,
    eval: &SiteEval,
) -> Result<Vec<Rc<str>>, String> {
    let Some(cert) = cert else {
        return Err("no certificate to audit".to_string());
    };
    if !cert.replayable() {
        return Err("witness is not standalone-replayable".to_string());
    }
    let mut used: Vec<Rc<str>> = Vec::new();
    for step in cert.steps() {
        if step.egraph_dependent || base_names.contains(&step.rule) {
            continue;
        }
        let outcome = eval(&step.lhs, &step.rhs);
        if outcome != SiteOutcome::Equal {
            return Err(format!(
                "premise step '{}' measured {} at its applied site",
                step.rule,
                outcome.as_str()
            ));
        }
        used.push(step.rule.clone());
    }
    Ok(used)
}

// ---------------------------------------------------------------------------
//  The measured-evidence record the gates read
// ---------------------------------------------------------------------------

/// One reach-probe row — the closure gate's per-case record.
#[derive(Clone, Debug, Default)]
pub struct ReachRow {
    /// With-rule cert replay outcome (`"pass"`, …).
    pub add_cert: String,
    /// Baseline (without-rule) cert replay outcome.
    pub base_cert: String,
    /// Enode count of the baseline saturation (`0` = not measured).
    pub base_enodes: usize,
    /// Enode count of the with-rule saturation.
    pub add_enodes: usize,
    /// Enodes the object's own applications minted (`None` = unaudited).
    pub cand_enodes: Option<usize>,
    /// Whether the object's mint hit the e-node cap.
    pub cand_capped: bool,
}

/// The pipeline's measured `Evidence` row — the fields the gauntlet's
/// gates read. The domain's measure leg fills it; the gates read it.
#[derive(Default)]
pub struct Evidence {
    /// Numeric oracle: `Some(true)` measured equal, `Some(false)`
    /// measured unequal, `None` unproven.
    pub num_true: Option<bool>,
    /// The derivability oracle's verdict.
    pub derivable: bool,
    /// Whether `derivable` was credited premise-anchored (set by
    /// [`premise_credit`]).
    pub premise_anchored: bool,
    /// The raw view-oracle verdict (reported, not gated on).
    pub view_verdict: String,
    /// The view verdict's note.
    pub view_note: String,
    /// Novelty relation (`"new"`, `"duplicate"`, …).
    pub relation: String,
    /// Real corpus matches.
    pub matches: usize,
    /// Census sites.
    pub census_sites: usize,
    /// Probe firings.
    pub fires: usize,
    /// Well-typed firings.
    pub fires_typed: usize,
    /// Ill-typed firings (the mint-a-bad-RHS signal).
    pub fires_ill_typed: usize,
    /// Cases where extraction strictly improved (the pay).
    pub paid: usize,
    /// Lowered-module verification failures.
    pub verify_fail: usize,
    /// `add_cert` failures over the probe corpus — ambient included.
    pub cert_fail: usize,
    /// Reach-probe rows (the closure audit).
    pub reach: Vec<ReachRow>,
    /// Ill-typed reach rows.
    pub reach_ill: usize,
    /// Whether bounded closure held.
    pub closure_safe: bool,
    /// The worst marginal enode growth ratio.
    pub closure_ratio: f64,
    /// The derivation certificate the derivability leg reported.
    pub derivation_cert: Option<Box<dyn CertView>>,
}

/// Credit or revoke a premise-anchored derivation on *evd* —
/// `evidence._premise_credit`.
///
/// Called only when a premise closure was supplied to the measure
/// leg. Site-verifies the reported certificate's non-axiom steps; a
/// derivation that invoked an unverified premise loses the credit —
/// the base-only verdict stands. Returns the stage-detail fragment.
pub fn premise_credit(
    evd: &mut Evidence,
    base_names: &BTreeSet<Rc<str>>,
    eval: &SiteEval,
) -> String {
    if !evd.derivable {
        return "premise-anchored: no derivation".to_string();
    }
    match premise_steps_verify(evd.derivation_cert.as_deref(), base_names, eval) {
        Err(detail) => {
            evd.premise_anchored = false;
            evd.derivable = false;
            detail
        }
        Ok(used) => {
            evd.premise_anchored = !used.is_empty();
            let mut names: Vec<Rc<str>> = used;
            names.sort();
            names.dedup();
            format!(
                "premise-anchored: {}",
                if names.is_empty() {
                    "axioms only".to_string()
                } else {
                    names
                        .iter()
                        .map(|n| n.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                }
            )
        }
    }
}

/// The default sweep window — `oracle._MAX_INSTANCES`, re-exported
/// for gate code.
pub const DEFAULT_SYNTH_LIMIT: usize = MAX_INSTANCES;
