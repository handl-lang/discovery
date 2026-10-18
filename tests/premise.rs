//! Premise machinery — transitive closure correctness and the
//! site-verification anti-gaming bar, mirroring the Python contract.

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use handl_discovery::{
    CertStep, CertView, Evidence, GenericCodec, GuardSpec, Mint, ObjectRecord, ObjectStore,
    SiteOutcome, Term, premise_credit, premise_rules, premise_steps_verify,
};
use handl_egraph::Rewrite;

/// In-memory declared-object store — rows keyed by name and key.
struct MapStore {
    by_name: BTreeMap<String, ObjectRecord>,
    by_key: BTreeMap<String, ObjectRecord>,
}

impl MapStore {
    fn new() -> MapStore {
        MapStore {
            by_name: BTreeMap::new(),
            by_key: BTreeMap::new(),
        }
    }
    fn put(&mut self, key: &str, rec: ObjectRecord) {
        self.by_name.insert(rec.name.to_string(), rec.clone());
        self.by_key.insert(key.to_string(), rec);
    }
}

impl ObjectStore for MapStore {
    fn record_by_name(&self, name: &str) -> Option<ObjectRecord> {
        self.by_name.get(name).cloned()
    }
    fn record_by_key(&self, key: &str) -> Option<ObjectRecord> {
        self.by_key.get(key).cloned()
    }
}

fn rec(name: &str, parents: &[&str], missing: &[&str]) -> ObjectRecord {
    ObjectRecord {
        name: Rc::from(name),
        kind: Rc::from("law"),
        lhs: Term::opl("f", vec![Term::var("x")]),
        rhs: Term::var("x"),
        law: name.to_string(),
        missing_hooks: missing.iter().map(|s| s.to_string()).collect(),
        guard: parents.first().map(|_| GuardSpec {
            parents: parents.iter().map(|p| Rc::from(*p)).collect(),
            pat1: Default::default(),
            pat2: Default::default(),
        }),
        transported: Vec::new(),
        data: serde_json::Value::Null,
    }
}

fn axiom(name: &str) -> Rc<Mint> {
    Rc::new(Mint::bare(Rewrite::new(
        name,
        Term::var("x"),
        Term::var("x"),
    )))
}

/// The closure resolves stored premises transitively, parents-first,
/// while axiom names resolve to the base rules and drop from extras.
#[test]
fn premise_closure_transitive() {
    let mut store = MapStore::new();
    // p's own premise is q; c's premises are p and the axiom "ax".
    store.put("k1", rec("p", &[], &[]));
    store.put("k2", rec("q", &[], &[]));
    // q is a premise of p: give p a guard naming q (len-1 parents
    // resolve in the premise walk; transport needs exactly 2, so p
    // itself rebuilds bare — honest: p's parents are *derivation*
    // premises, not a guard-transport pair).
    store.put("k1", rec("p", &["q"], &[]));
    store.put("kc", rec("c", &["p", "ax"], &[]));
    let base = vec![axiom("ax")];
    let crec = store.record_by_name("c").unwrap();
    let extras = premise_rules(&store, &GenericCodec, &crec, &base).unwrap();
    // q resolves inside p's walk, parents-first; ax resolves from base
    // and is filtered from extras.
    let names: Vec<String> = extras.iter().map(|m| m.name.to_string()).collect();
    assert_eq!(names, vec!["q", "p"]);
}

/// A premise with no stored row and no axiom entry empties the whole
/// closure — the total-refusal contract.
#[test]
fn premise_missing_row_refuses() {
    let mut store = MapStore::new();
    store.put("kc", rec("c", &["ghost"], &[]));
    let crec = store.record_by_name("c").unwrap();
    let err = premise_rules(&store, &GenericCodec, &crec, &[]).unwrap_err();
    assert!(err.contains("premise 'ghost' is not a stored row"), "{err}");
}

/// A premise that admits *weaker than declared* (missing hooks minus
/// transported non-empty) refuses the whole closure — the composite
/// was minted against the full parent.
#[test]
fn premise_weaker_than_declared_refuses() {
    let mut store = MapStore::new();
    // p declares a missing "check" hook but carries no guard spec to
    // transport it — it admits weaker than declared.
    store.put("k1", rec("p", &[], &["check"]));
    store.put("kc", rec("c", &["p", "ax"], &[]));
    let base = vec![axiom("ax")];
    let crec = store.record_by_name("c").unwrap();
    let err = premise_rules(&store, &GenericCodec, &crec, &base).unwrap_err();
    assert!(
        err.contains("premise 'p' admits weaker than declared (check)"),
        "{err}"
    );
}

/// A cyclic premise reference is skipped, not a failure — `seen`
/// bounds the transitive walk (a premise already in the closure or
/// the object itself contributes nothing twice).
#[test]
fn premise_cycle_is_safe() {
    let mut store = MapStore::new();
    store.put("k1", rec("a", &["b"], &[]));
    store.put("k2", rec("b", &["a"], &[]));
    let arec = store.record_by_name("a").unwrap();
    let extras = premise_rules(&store, &GenericCodec, &arec, &[]).unwrap();
    let names: Vec<String> = extras.iter().map(|m| m.name.to_string()).collect();
    // a -> b -> a(seen, skipped): closure = {b}.
    assert_eq!(names, vec!["b"]);
}

// ---------------------------------------------------------------------------
//  Site verification — the anti-gaming bar
// ---------------------------------------------------------------------------

struct Cert {
    replayable: bool,
    steps: Vec<CertStep>,
}

impl CertView for Cert {
    fn replayable(&self) -> bool {
        self.replayable
    }
    fn steps(&self) -> &[CertStep] {
        &self.steps
    }
}

fn step(rule: &str, l: &str, r: &str, dep: bool) -> CertStep {
    CertStep {
        rule: Rc::from(rule),
        lhs: Term::leaf(l),
        rhs: Term::leaf(r),
        egraph_dependent: dep,
    }
}

/// The test oracle: `equal` iff the two leaves share a key —
/// stand-in for the domain's fp64 eval.
fn eq_eval() -> impl Fn(&Term, &Term) -> SiteOutcome {
    |l: &Term, r: &Term| {
        if l == r {
            SiteOutcome::Equal
        } else {
            SiteOutcome::Unequal
        }
    }
}

/// A premise step naming a non-axiom rule must site-verify equal;
/// axiom and e-graph-dependent steps are skipped.
#[test]
fn steps_verify_anti_gaming() {
    let base: BTreeSet<Rc<str>> = ["ax"].into_iter().map(Rc::from).collect();
    let eval = eq_eval();
    // good: axiom step skipped, premise step equal.
    let cert = Cert {
        replayable: true,
        steps: vec![
            step("ax", "x", "x", false),
            step("p", "u", "u", false),
            step("env_step", "a", "b", true), // e-graph-dependent: skipped
        ],
    };
    let used = premise_steps_verify(Some(&cert), &base, &eval).unwrap();
    assert_eq!(used, vec![Rc::from("p")]);

    // anti-gaming: a premise step false *at its applied site* refuses.
    let bad = Cert {
        replayable: true,
        steps: vec![step("p", "u", "v", false)],
    };
    let err = premise_steps_verify(Some(&bad), &base, &eval).unwrap_err();
    assert!(
        err.contains("premise step 'p' measured unequal at its applied site"),
        "{err}"
    );
}

/// Non-replayable witnesses and absent certs refuse — conservative,
/// never guessed.
#[test]
fn steps_verify_refusals() {
    let base: BTreeSet<Rc<str>> = BTreeSet::new();
    let eval = eq_eval();
    assert_eq!(
        premise_steps_verify(None, &base, &eval).unwrap_err(),
        "no certificate to audit"
    );
    let bad = Cert {
        replayable: false,
        steps: vec![],
    };
    assert_eq!(
        premise_steps_verify(Some(&bad), &base, &eval).unwrap_err(),
        "witness is not standalone-replayable"
    );
    // axioms-only anchored derivation: empty `used` is a pass.
    let cert = Cert {
        replayable: true,
        steps: vec![step("ax", "x", "x", false)],
    };
    let base2: BTreeSet<Rc<str>> = ["ax"].into_iter().map(Rc::from).collect();
    assert_eq!(
        premise_steps_verify(Some(&cert), &base2, &eval).unwrap(),
        Vec::<Rc<str>>::new()
    );
}

/// `premise_credit` — a derivation invoking an unverified premise
/// loses the credit; a verified one is marked anchored.
#[test]
fn premise_credit_revocation() {
    let base: BTreeSet<Rc<str>> = ["ax"].into_iter().map(Rc::from).collect();
    let eval = eq_eval();

    // no derivation at all — honest fragment, nothing to credit.
    let mut evd = Evidence::default();
    assert_eq!(
        premise_credit(&mut evd, &base, &eval),
        "premise-anchored: no derivation"
    );

    // verified anchored derivation: credited and flagged.
    let mut evd = Evidence {
        derivable: true,
        derivation_cert: Some(Box::new(Cert {
            replayable: true,
            steps: vec![step("p", "u", "u", false)],
        })),
        ..Evidence::default()
    };
    let detail = premise_credit(&mut evd, &base, &eval);
    assert_eq!(detail, "premise-anchored: p");
    assert!(evd.derivable && evd.premise_anchored);

    // unverified premise: credit revoked, derivable falls back to the
    // base-only verdict.
    let mut evd = Evidence {
        derivable: true,
        derivation_cert: Some(Box::new(Cert {
            replayable: true,
            steps: vec![step("p", "u", "v", false)],
        })),
        ..Evidence::default()
    };
    let detail = premise_credit(&mut evd, &base, &eval);
    assert!(detail.contains("measured unequal"), "{detail}");
    assert!(!evd.derivable && !evd.premise_anchored);
}
