//! The admission gauntlet — `evidence.run_gauntlet`'s stage pipeline
//! as a trait-driven structure.
//!
//! A stored object earns `usable` only by clearing the same gates a
//! shipped law cleared, in the spec's order:
//!
//! 1. **reconstruct** — the record admits into a live rule;
//! 2. **full-data** — `missing_hooks` minus `transported` is empty;
//! 3. **measure** — the domain's measurement pipeline (numeric
//!    oracle, *premise-anchored* derivability, the raw view verdict);
//! 4. **truth** — unguarded: the measured verdict; guarded: the
//!    guarded-region sweep — every accepted evaluable binding equal,
//!    at least one existing;
//! 5. **novelty** — the object is not a library spelling;
//! 6. **typed-pay** — fires, all well-typed, pays, lowerings agree;
//! 7. **closure** — bounded closure, no object-attributable cert
//!    break;
//! 8. **cert** — a recorded derivation replays strict.
//!
//! The *shape* is ported; the *legs* are injected through
//! [`GauntletLegs`] — the store, the record codec, the base axiom
//! set, the measurement pipeline, the guarded-region sweep, the site
//! oracle, the cert replay, and the auto-cond retry are all domain
//! machinery this skeleton drives but never implements.

use std::collections::BTreeSet;
use std::rc::Rc;

use serde_json::Value;

use crate::evidence::{
    Evidence, GuardedRegion, ObjectCodec, ObjectRecord, ObjectStore, ReachRow, SiteEval, admit,
    premise_credit, premise_rules, region_clean,
};
use crate::terms::Mint;

// ---------------------------------------------------------------------------
//  Stage reports
// ---------------------------------------------------------------------------

/// One gate's verdict — `evidence.GauntletStage`.
#[derive(Clone, Debug)]
pub struct GauntletStage {
    /// The stage name.
    pub name: String,
    /// Whether the gate passed.
    pub passed: bool,
    /// The evidence line (why it passed or refused).
    pub detail: String,
}

impl GauntletStage {
    fn new(name: &str, passed: bool, detail: impl Into<String>) -> GauntletStage {
        GauntletStage {
            name: name.to_string(),
            passed,
            detail: detail.into(),
        }
    }
}

/// The adversarial admission verdict for one stored object —
/// `evidence.Gauntlet`.
///
/// `stages` is the ordered gate list — the object's honest record of
/// where it stood. `usable` is `true` only when every stage passed:
/// the store never reports a synthesized object as usable on the
/// strength of reconstruction alone.
#[derive(Default)]
pub struct Gauntlet {
    /// The object's content key.
    pub alpha_key: String,
    /// The admitted name (stage 1).
    pub name: String,
    /// The record's declared kind (stage 1).
    pub kind: String,
    /// `true` only when every recorded stage passed.
    pub usable: bool,
    /// The ordered gate list.
    pub stages: Vec<GauntletStage>,
    /// The live mint (stage 1).
    pub rule: Option<Rc<Mint>>,
    /// The parsed object record (stage 1).
    pub record: Option<ObjectRecord>,
    /// The measured evidence row (stage 3).
    pub evidence: Option<Evidence>,
    /// The guarded-region sweep, synthesized domain (stage 4).
    pub synth_region: Option<GuardedRegion>,
    /// The guarded-region sweep, real corpus (stage 4).
    pub real_region: Option<GuardedRegion>,
    /// The auto-cond attempt report (`auto_cond` armed runs).
    pub auto_cond: Option<Value>,
}

impl Gauntlet {
    /// The first failing stage, or the cleared verdict —
    /// `Gauntlet.reason`.
    pub fn reason(&self) -> String {
        for s in &self.stages {
            if !s.passed {
                return format!("{}: {}", s.name, s.detail);
            }
        }
        if self.stages.is_empty() {
            "no stages ran".to_string()
        } else {
            "cleared".to_string()
        }
    }

    /// Append one stage verdict; return whether it passed —
    /// `evidence._gate`.
    fn gate(&mut self, name: &str, ok: bool, detail: impl Into<String>) -> bool {
        self.stages.push(GauntletStage::new(name, ok, detail));
        ok
    }

    /// Seal the report: `usable` iff every recorded stage passed —
    /// `evidence._finish`.
    fn finish(mut self) -> Gauntlet {
        self.usable = !self.stages.is_empty() && self.stages.iter().all(|s| s.passed);
        self
    }
}

/// Gauntlet run options — `run_gauntlet`'s keyword surface.
#[derive(Clone, Debug, Default)]
pub struct GauntletOptions {
    /// The guarded-region sweep's first-phase window (the oracle's
    /// default when `None`).
    pub synth_limit: Option<usize>,
    /// Arm the conditional→guarded retry.
    pub auto_cond: bool,
    /// Bound the conjunction the auto-cond search may mint.
    pub auto_cond_clauses: usize,
}

/// The auto-cond retry's outcome — the search detail plus whether it
/// minted a guard (the legs rewrite the record themselves before
/// returning `found: true`).
pub struct AutoCondOutcome {
    /// Whether the search minted a guard and rewrote the record.
    pub found: bool,
    /// The prepended stage's detail line.
    pub detail: String,
    /// The `rep.auto_cond` report — clauses, measured counts, the
    /// first refusal's reason (the spec's dict shape).
    pub report: Value,
}

/// The domain legs the gauntlet drives — the injected machinery.
///
/// Stage mapping: `store`+`codec` serve stages 1-2 ([`admit`]) and
/// the premise closure inside stage 3; `base_rules` is the axiom set
/// the derivability leg anchors on; `measure` is stage 3;
/// `guarded_truth` is stage 4's guarded arm; `site_eval` is the
/// numeric oracle the premise audit uses; `stored_certificate` is
/// stage 8; `auto_cond` is the retry hook.
pub trait GauntletLegs {
    /// The declared-object store.
    fn store(&self) -> &dyn ObjectStore;
    /// The record codec (`bare_rule` hydration).
    fn codec(&self) -> &dyn ObjectCodec;
    /// The axiom set the derivability oracle and premise closure use.
    fn base_rules(&self) -> &[Rc<Mint>];
    /// Stage 3 — run the measurement pipeline on the rebuilt rule.
    ///
    /// `premise_extras` is the record's resolved transitive premise
    /// closure (empty when the closure refused or the record has no
    /// premises) — the anchored derivability leg evaluates
    /// `base_rules ∪ premise_extras`; everything else stays scoped to
    /// `base_rules`.
    fn measure(
        &mut self,
        rule: &handl_egraph::Rewrite,
        record: &ObjectRecord,
        premise_extras: &[Rc<Mint>],
    ) -> Result<Evidence, String>;
    /// Stage 4, guarded arm — `(synth_region, real_region)` sweeps of
    /// the guard-accepted region at *limit*.
    fn guarded_truth(
        &mut self,
        rule: &handl_egraph::Rewrite,
        limit: usize,
    ) -> (GuardedRegion, GuardedRegion);
    /// The numeric oracle — tri-state `lhs == rhs` at a concrete site.
    fn site_eval(&self) -> &SiteEval;
    /// Stage 8 — strict certificate replay.
    ///
    /// `Ok(None)` claims no derivation (the honest `cert: null`);
    /// `Ok(Some(n))` is a strict `n`-step replay; `Err` is a replay
    /// failure — a corrupt or drifted record is a failure to
    /// surface, not a flag to read.
    fn stored_certificate(&self, record: &ObjectRecord) -> Result<Option<usize>, String>;
    /// The conditional→guarded retry search — `auto_cond_object`.
    ///
    /// Called on a `truth` refusal or a `full-data` refusal on a
    /// missing `check` alone. The legs search the declarative guard
    /// vocabulary for the smallest conjunction covering the measured
    /// domain; on a hit they rewrite the record (same alpha key, now
    /// carrying the `cond`) and return `found: true`. Default: never
    /// fires — the honest "not implemented" for legs without a
    /// cond vocabulary.
    fn auto_cond(&mut self, _rep: &Gauntlet, _clauses: usize) -> AutoCondOutcome {
        AutoCondOutcome {
            found: false,
            detail: "no auto-cond vocabulary".to_string(),
            report: serde_json::json!({"found": false}),
        }
    }
}

// ---------------------------------------------------------------------------
//  The gates
// ---------------------------------------------------------------------------

/// Stages 1-2 — `evidence._reconstruct_gate`.
///
/// The record must rebuild, and rebuild *fully*: an unknown kind or a
/// missing row is a reconstruction failure; a record that dropped
/// hooks admits a weaker rule than it declares — the full-data gate
/// refuses to call that usable.
fn reconstruct_gate(
    legs: &dyn GauntletLegs,
    rep: &mut Gauntlet,
) -> Option<(Rc<Mint>, ObjectRecord)> {
    match admit(legs.store(), legs.codec(), &rep.alpha_key) {
        Err(e) => {
            rep.gate("reconstruct", false, e);
            None
        }
        Ok(None) => {
            rep.gate("reconstruct", false, "no object under this key");
            None
        }
        Ok(Some((rule, record))) => {
            rep.name = rule.name.to_string();
            rep.kind = record.kind.to_string();
            rep.rule = Some(rule.clone());
            rep.record = Some(record.clone());
            rep.gate("reconstruct", true, format!("{} rebuilds", record.kind));
            let missing = record.unresolved_hooks();
            let transported = &record.transported;
            let detail = if missing.is_empty() {
                format!(
                    "the record carries every hook{}",
                    if transported.is_empty() {
                        String::new()
                    } else {
                        format!(" ({} via guard transport)", transported.join(", "))
                    }
                )
            } else {
                format!("dropped hooks: {}", missing.join(", "))
            };
            if rep.gate("full-data", missing.is_empty(), detail) {
                Some((rule, record))
            } else {
                None
            }
        }
    }
}

/// Render the measured truth evidence — `evidence._truth_detail`.
fn truth_detail(evd: &Evidence) -> String {
    let anchored = if evd.premise_anchored {
        "(premise-anchored)"
    } else {
        ""
    };
    let mut parts = vec![
        format!(
            "numeric={}",
            match evd.num_true {
                Some(true) => "True",
                Some(false) => "False",
                None => "None",
            }
        ),
        format!("derivable={}{anchored}", evd.derivable),
    ];
    if !evd.view_verdict.is_empty() {
        parts.push(format!("view={} ({})", evd.view_verdict, evd.view_note));
    }
    parts.join(" ")
}

/// Render the guarded-region sweeps — `evidence._region_detail`.
fn region_detail(synth: &GuardedRegion, real: &GuardedRegion) -> String {
    let mut out: Vec<String> = Vec::new();
    for (label, r) in [("synth", synth), ("real", real)] {
        out.push(format!(
            "{label}: {}eq/{}ne/{}rerr ({} accepted, {} declined{}{})",
            r.equal,
            r.unequal,
            r.rhs_err,
            r.accepted,
            r.declined,
            if r.guard_err > 0 {
                format!(", {} guard-err", r.guard_err)
            } else {
                String::new()
            },
            if r.envs > 0 {
                format!(", {} envs", r.envs)
            } else {
                String::new()
            },
        ));
    }
    out.join(" | ")
}

/// Stage 4 — `evidence._truth_gate`.
///
/// The declared equality must hold where the rule fires. A measured
/// counterexample outranks a derivation: `derivable` may only waive
/// the *starvation* requirement (that the sweep exhibit at least one
/// equal site), never a measured counterexample. An unguarded object
/// reads the same rule off the numeric oracle.
fn truth_gate(legs: &mut dyn GauntletLegs, rep: &mut Gauntlet, limit: usize) -> bool {
    let evd = rep.evidence.as_mut().expect("truth gate needs evidence");
    let rule = rep.rule.clone().expect("truth gate needs a rule");
    if rule.check.is_none() {
        // Unguarded — a domain `cond` surfaces as a `check` hook, so
        // the spec's `rule.cond is None and rule.check is None` reads
        // as `check.is_none()` here.
        let ok = evd.num_true != Some(false) && (evd.derivable || evd.num_true == Some(true));
        let detail = truth_detail(evd);
        return rep.gate("truth", ok, detail);
    }
    let (synth, real) = legs.guarded_truth(&rule.rule, limit);
    let clean = region_clean(&synth) && region_clean(&real);
    let ok = clean && (evd.derivable || synth.equal >= 1);
    let mut detail = format!(
        "{} | guarded: {}",
        truth_detail(evd),
        region_detail(&synth, &real)
    );
    if !clean && evd.derivable {
        detail += " | derivation overridden by a measured counterexample";
    }
    rep.synth_region = Some(synth);
    rep.real_region = Some(real);
    rep.gate("truth", ok, detail)
}

/// Stages 3-4 — `evidence._measure_gate`.
///
/// `pipeline.measure` on the rebuilt rule, then truth. Derivability
/// is *premise-anchored*: a stored composite's `derivable` leg
/// evaluates against `base_rules` plus the record's transitive
/// premise closure — the proof it was minted under. The anchor is
/// credited only when the anchored certificate site-verifies every
/// non-axiom step.
fn measure_gate(
    legs: &mut dyn GauntletLegs,
    rep: &mut Gauntlet,
    record: &ObjectRecord,
    limit: usize,
) -> bool {
    let base_names: BTreeSet<Rc<str>> = legs.base_rules().iter().map(|m| m.name.clone()).collect();
    let (extras, premise_note) =
        match premise_rules(legs.store(), legs.codec(), record, legs.base_rules()) {
            Ok(e) => (e, String::new()),
            Err(d) => (Vec::new(), d),
        };
    let rule = rep.rule.clone().expect("measure gate needs a rule");
    let mut evd = match legs.measure(&rule.rule, record, &extras) {
        Err(e) => {
            rep.gate("measure", false, e);
            return false;
        }
        Ok(evd) => evd,
    };
    // `_premise_detail`: refusal note first, then the credit line.
    let mut premise_detail = String::new();
    if !premise_note.is_empty() {
        premise_detail = format!(" | premise closure refused: {premise_note}");
    }
    if !extras.is_empty() {
        premise_detail += &format!(
            " | {}",
            premise_credit(&mut evd, &base_names, legs.site_eval())
        );
    }
    let detail = format!(
        "matches={} census={}{premise_detail}",
        evd.matches, evd.census_sites
    );
    rep.evidence = Some(evd);
    rep.gate("measure", true, detail);
    truth_gate(legs, rep, limit)
}

/// Stage 6 — `evidence._typed_pay_gate`: fires, all well-typed,
/// pays, lowered modules agree.
fn typed_pay_gate(rep: &mut Gauntlet) -> bool {
    let evd = rep.evidence.as_ref().expect("typed-pay needs evidence");
    rep.gate(
        "typed-pay",
        evd.fires > 0 && evd.fires_ill_typed == 0 && evd.paid > 0 && evd.verify_fail == 0,
        format!(
            "fires={} typed={} ill={} paid={} verify_fail={}",
            evd.fires, evd.fires_typed, evd.fires_ill_typed, evd.paid, evd.verify_fail
        ),
    )
}

/// Stage 7 — `evidence._closure_gate`: bounded closure and no
/// object-attributable cert break.
///
/// `evd.cert_fail` counts every `add_cert` failure over the probe
/// corpus — including ambient cases whose *base* replay already
/// fails. The gate is narrower: failures *attributable* to the
/// object — a case whose baseline certificate replayed but whose
/// with-rule one did not. Ambient failures are reported, not charged.
fn closure_gate(rep: &mut Gauntlet) -> bool {
    let evd = rep.evidence.as_ref().expect("closure needs evidence");
    let cert_att = evd
        .reach
        .iter()
        .filter(|r| r.add_cert != "pass" && r.base_cert == "pass")
        .count();
    // The footprint audit for the worst-growth row.
    let worst: Option<&ReachRow> = evd
        .reach
        .iter()
        .filter(|r| r.base_enodes > 0)
        .max_by_key(|r| r.add_enodes.saturating_sub(r.base_enodes));
    let mut audit = String::new();
    if let Some(w) = worst
        && let Some(cand) = w.cand_enodes
    {
        audit = format!(
            " minted={cand} excess={}{}",
            w.add_enodes
                .saturating_sub(w.base_enodes)
                .saturating_sub(cand),
            if w.cand_capped { " capped" } else { "" }
        );
    }
    rep.gate(
        "closure",
        cert_att == 0 && evd.reach_ill == 0 && evd.closure_safe,
        format!(
            "enode={:.2}x{audit} cert_fail={cert_att} (ambient={}) reach_ill={}",
            evd.closure_ratio,
            evd.cert_fail.saturating_sub(cert_att),
            evd.reach_ill,
        ),
    )
}

/// Stage 8 — `evidence._cert_gate`: a record carrying a derivation
/// replays it strictly.
fn cert_gate(legs: &dyn GauntletLegs, rep: &mut Gauntlet, record: &ObjectRecord) -> bool {
    match legs.stored_certificate(record) {
        Err(e) => rep.gate("cert", false, format!("strict replay failed: {e}")),
        Ok(None) => rep.gate("cert", true, "no derivation recorded"),
        Ok(Some(n)) => rep.gate("cert", true, format!("{n}-step cert replays strict")),
    }
}

/// Stages 5-8 — `evidence._admit_tail`: novelty → typed-pay →
/// closure → cert replay.
fn admit_tail(legs: &dyn GauntletLegs, mut rep: Gauntlet, record: &ObjectRecord) -> Gauntlet {
    // novelty: a stored object duplicating a library spelling is not
    // a new inhabitant.
    let relation = rep
        .evidence
        .as_ref()
        .map(|e| e.relation.clone())
        .unwrap_or_default();
    if !rep.gate("novelty", relation == "new", format!("relation={relation}")) {
        return rep.finish();
    }
    if !typed_pay_gate(&mut rep) || !closure_gate(&mut rep) {
        return rep.finish();
    }
    cert_gate(legs, &mut rep, record);
    rep.finish()
}

/// Whether the auto-cond retry applies to this refusal —
/// `evidence._auto_cond_armed`.
///
/// `truth`: the candidate measured conditional — the minted guard is
/// the missing piece. `full-data`: exactly the `check` hook is
/// missing — the reconstructed rule is already the bare pattern, and
/// the found `cond` is what the record was missing. Anything else is
/// not an auto-cond question.
fn auto_cond_armed(rep: &Gauntlet, stage: &str) -> bool {
    if rep.rule.is_none() {
        return false;
    }
    if stage == "truth" {
        return rep.stages.last().is_some_and(|s| s.name == "truth");
    }
    rep.record
        .as_ref()
        .is_some_and(|r| r.missing_hooks == ["check"])
}

/// Attempt the conditional→guarded rewrite after a refusal —
/// `evidence._auto_cond_retry`.
///
/// On a hit the legs rewrote the record (same alpha key, now carrying
/// the found `cond`) and the gauntlet re-runs on the rewritten record
/// (`auto_cond: false` — one retry, not a chase). The returned report
/// is the *second* run's, with an `auto-cond` stage prepended; the
/// refusal case keeps the original report, annotated in
/// `rep.auto_cond`.
fn auto_cond_retry(
    legs: &mut dyn GauntletLegs,
    mut rep: Gauntlet,
    opts: &GauntletOptions,
) -> Gauntlet {
    let res = legs.auto_cond(&rep, opts.auto_cond_clauses);
    let mut report = res.report;
    if let Some(obj) = report.as_object_mut() {
        obj.insert("first_reason".to_string(), Value::from(rep.reason()));
    }
    rep.auto_cond = Some(report.clone());
    if !res.found {
        return rep.finish();
    }
    let retry = GauntletOptions {
        auto_cond: false,
        ..opts.clone()
    };
    let mut rep2 = run_gauntlet(legs, &rep.alpha_key, &retry);
    rep2.auto_cond = rep.auto_cond;
    rep2.stages.insert(
        0,
        GauntletStage {
            name: "auto-cond".to_string(),
            passed: true,
            detail: res.detail,
        },
    );
    rep2
}

/// Run the admission gauntlet on a stored declared object —
/// `evidence.run_gauntlet`.
///
/// A failing gate stops the run — later stages are not reached, not
/// skipped. `usable` is `true` only when every stage passed — the
/// honest contract: the store refuses to call a synthesized object
/// usable on reconstruction alone.
pub fn run_gauntlet(
    legs: &mut dyn GauntletLegs,
    alpha_key: &str,
    opts: &GauntletOptions,
) -> Gauntlet {
    let mut rep = Gauntlet {
        alpha_key: alpha_key.to_string(),
        ..Gauntlet::default()
    };
    let Some((_rule, record)) = reconstruct_gate(legs, &mut rep) else {
        if opts.auto_cond && auto_cond_armed(&rep, "full-data") {
            return auto_cond_retry(legs, rep, opts);
        }
        return rep.finish();
    };
    let limit = opts
        .synth_limit
        .unwrap_or(crate::evidence::DEFAULT_SYNTH_LIMIT);
    if !measure_gate(legs, &mut rep, &record, limit) {
        if opts.auto_cond && auto_cond_armed(&rep, "truth") {
            return auto_cond_retry(legs, rep, opts);
        }
        return rep.finish();
    }
    admit_tail(legs, rep, &record)
}
