//! The gauntlet skeleton — stage order, stop-on-failure, auto-cond
//! plumbing, driven by a fake `GauntletLegs`.

use std::collections::BTreeMap;
use std::rc::Rc;

use handl_discovery::{
    AutoCondOutcome, BoundEnv, Evidence, GauntletLegs, GauntletOptions, GenericCodec,
    GuardedRegion, Mint, ObjectCodec, ObjectRecord, ObjectStore, ReachRow, SiteOutcome, Term,
    run_gauntlet,
};
use handl_egraph::Rewrite;

struct MapStore {
    by_name: BTreeMap<String, ObjectRecord>,
    by_key: BTreeMap<String, ObjectRecord>,
}

impl ObjectStore for MapStore {
    fn record_by_name(&self, name: &str) -> Option<ObjectRecord> {
        self.by_name.get(name).cloned()
    }
    fn record_by_key(&self, key: &str) -> Option<ObjectRecord> {
        self.by_key.get(key).cloned()
    }
}

/// A codec that attaches a trivial `check` — exercises the guarded
/// arm of the truth gate without a transport chain.
struct CheckedCodec;

impl ObjectCodec for CheckedCodec {
    fn bare_rule(&self, rec: &ObjectRecord) -> Result<Rewrite, String> {
        let mut r = Rewrite::new(rec.name.clone(), rec.lhs.clone(), rec.rhs.clone());
        r.check = Some(Box::new(|_: &BoundEnv| true));
        Ok(r)
    }
}

fn rec(name: &str, missing: &[&str]) -> ObjectRecord {
    ObjectRecord {
        name: Rc::from(name),
        kind: Rc::from("law"),
        lhs: Term::opl("f", vec![Term::var("x")]),
        rhs: Term::var("x"),
        law: name.to_string(),
        missing_hooks: missing.iter().map(|s| s.to_string()).collect(),
        guard: None,
        transported: Vec::new(),
        data: serde_json::Value::Null,
    }
}

/// Canned evidence: shippable unless fields say otherwise.
fn good_evidence() -> Evidence {
    Evidence {
        num_true: Some(true),
        derivable: false,
        relation: "new".to_string(),
        matches: 2,
        census_sites: 2,
        fires: 1,
        fires_typed: 1,
        paid: 1,
        closure_safe: true,
        closure_ratio: 1.0,
        ..Evidence::default()
    }
}

type EvidenceFn = Box<dyn FnMut(&[Rc<Mint>]) -> Evidence>;

struct TestLegs {
    store: MapStore,
    codec_checked: bool,
    base: Vec<Rc<Mint>>,
    /// Fresh evidence per measure call.
    evidence: EvidenceFn,
    truth: (GuardedRegion, GuardedRegion),
    cert: Result<Option<usize>, String>,
    auto_cond_found: bool,
}

impl TestLegs {
    fn new(store: MapStore) -> TestLegs {
        TestLegs {
            store,
            codec_checked: false,
            base: Vec::new(),
            evidence: Box::new(|_| good_evidence()),
            truth: (GuardedRegion::default(), GuardedRegion::default()),
            cert: Ok(None),
            auto_cond_found: false,
        }
    }
}

impl GauntletLegs for TestLegs {
    fn store(&self) -> &dyn ObjectStore {
        &self.store
    }
    fn codec(&self) -> &dyn ObjectCodec {
        if self.codec_checked {
            &CheckedCodec
        } else {
            &GenericCodec
        }
    }
    fn base_rules(&self) -> &[Rc<Mint>] {
        &self.base
    }
    fn measure(
        &mut self,
        _rule: &Rewrite,
        _record: &ObjectRecord,
        premise_extras: &[Rc<Mint>],
    ) -> Result<Evidence, String> {
        Ok((self.evidence)(premise_extras))
    }
    fn guarded_truth(&mut self, _rule: &Rewrite, _limit: usize) -> (GuardedRegion, GuardedRegion) {
        self.truth.clone()
    }
    fn site_eval(&self) -> &handl_discovery::SiteEval {
        static F: fn(&Term, &Term) -> SiteOutcome = |l, r| {
            if l == r {
                SiteOutcome::Equal
            } else {
                SiteOutcome::Unequal
            }
        };
        &F
    }
    fn stored_certificate(&self, _record: &ObjectRecord) -> Result<Option<usize>, String> {
        self.cert.clone()
    }
    fn auto_cond(&mut self, _rep: &handl_discovery::Gauntlet, _clauses: usize) -> AutoCondOutcome {
        if !self.auto_cond_found {
            return AutoCondOutcome {
                found: false,
                detail: "no guard found".to_string(),
                report: serde_json::json!({"found": false}),
            };
        }
        // The retry rewrites the record — clear the missing check.
        for rec in self.store.by_key.values_mut() {
            rec.missing_hooks.clear();
        }
        AutoCondOutcome {
            found: true,
            detail: "minted cond".to_string(),
            report: serde_json::json!({"found": true, "clauses": ["c0"]}),
        }
    }
}

fn store_with(key: &str, rec: ObjectRecord) -> MapStore {
    let mut s = MapStore {
        by_name: BTreeMap::new(),
        by_key: BTreeMap::new(),
    };
    s.by_name.insert(rec.name.to_string(), rec.clone());
    s.by_key.insert(key.to_string(), rec);
    s
}

fn stage_names(rep: &handl_discovery::Gauntlet) -> Vec<String> {
    rep.stages.iter().map(|s| s.name.clone()).collect()
}

/// The golden path: every stage ran in the spec's order, `usable`.
#[test]
fn gauntlet_full_pass() {
    let store = store_with("k1", rec("obj", &[]));
    let mut legs = TestLegs::new(store);
    legs.cert = Ok(Some(3));
    let rep = run_gauntlet(&mut legs, "k1", &GauntletOptions::default());
    assert!(rep.usable, "reason: {}", rep.reason());
    assert_eq!(
        stage_names(&rep),
        vec![
            "reconstruct",
            "full-data",
            "measure",
            "truth",
            "novelty",
            "typed-pay",
            "closure",
            "cert"
        ]
    );
    assert!(rep.stages.iter().all(|s| s.passed));
    assert_eq!(rep.stages[7].detail, "3-step cert replays strict");
}

/// A measured counterexample outranks derivability — the truth gate
/// blocks even when `derivable` is true.
#[test]
fn gauntlet_truth_blocks_on_counterexample() {
    let store = store_with("k1", rec("obj", &[]));
    let mut legs = TestLegs::new(store);
    legs.evidence = Box::new(|_| Evidence {
        num_true: Some(false),
        derivable: true, // derivation cannot waive a measured site
        ..good_evidence()
    });
    let rep = run_gauntlet(&mut legs, "k1", &GauntletOptions::default());
    assert!(!rep.usable);
    assert_eq!(
        stage_names(&rep),
        vec!["reconstruct", "full-data", "measure", "truth"]
    );
    assert!(rep.reason().starts_with("truth:"));
}

/// The guarded arm: `check`-carrying rules take the region sweep;
/// a clean region with at least one equal site passes.
#[test]
fn gauntlet_guarded_truth() {
    let store = store_with("k1", rec("obj", &[]));
    let mut legs = TestLegs::new(store);
    legs.codec_checked = true;
    legs.truth = (
        GuardedRegion {
            accepted: 4,
            equal: 2,
            declined: 1,
            envs: 5,
            ..GuardedRegion::default()
        },
        GuardedRegion::default(),
    );
    let rep = run_gauntlet(&mut legs, "k1", &GauntletOptions::default());
    assert!(rep.usable, "reason: {}", rep.reason());
    assert!(rep.synth_region.is_some());

    // A measured unequal inside the region blocks despite the sweep.
    let store = store_with("k2", rec("obj2", &[]));
    let mut legs = TestLegs::new(store);
    legs.codec_checked = true;
    legs.truth = (
        GuardedRegion {
            accepted: 4,
            equal: 2,
            unequal: 1,
            ..GuardedRegion::default()
        },
        GuardedRegion::default(),
    );
    legs.evidence = Box::new(|_| Evidence {
        derivable: true,
        ..good_evidence()
    });
    let rep = run_gauntlet(&mut legs, "k2", &GauntletOptions::default());
    assert!(!rep.usable);
    assert!(rep.reason().starts_with("truth:"));
}

/// Novelty refuses a library spelling; the tail stages never run.
#[test]
fn gauntlet_novelty() {
    let store = store_with("k1", rec("obj", &[]));
    let mut legs = TestLegs::new(store);
    legs.evidence = Box::new(|_| Evidence {
        relation: "subsumed".to_string(),
        ..good_evidence()
    });
    let rep = run_gauntlet(&mut legs, "k1", &GauntletOptions::default());
    assert!(!rep.usable);
    assert_eq!(stage_names(&rep).last().unwrap(), "novelty");
}

/// Typed-pay and closure refuse their respective measured failures.
#[test]
fn gauntlet_typed_pay_and_closure() {
    // ill-typed fire refuses typed-pay.
    let store = store_with("k1", rec("obj", &[]));
    let mut legs = TestLegs::new(store);
    legs.evidence = Box::new(|_| Evidence {
        fires_ill_typed: 1,
        ..good_evidence()
    });
    let rep = run_gauntlet(&mut legs, "k1", &GauntletOptions::default());
    assert!(rep.reason().starts_with("typed-pay:"));

    // object-attributable cert failure refuses closure — ambient
    // failures (base also failed) are reported, not charged.
    let store = store_with("k2", rec("obj2", &[]));
    let mut legs = TestLegs::new(store);
    legs.evidence = Box::new(|_| Evidence {
        cert_fail: 2,
        reach: vec![
            ReachRow {
                add_cert: "fail".to_string(),
                base_cert: "pass".to_string(), // attributable
                base_enodes: 10,
                add_enodes: 14,
                cand_enodes: Some(3),
                cand_capped: false,
            },
            ReachRow {
                add_cert: "fail".to_string(),
                base_cert: "fail".to_string(), // ambient
                base_enodes: 0,
                add_enodes: 0,
                cand_enodes: None,
                cand_capped: false,
            },
        ],
        ..good_evidence()
    });
    let rep = run_gauntlet(&mut legs, "k2", &GauntletOptions::default());
    assert!(rep.reason().starts_with("closure:"), "{}", rep.reason());
    let closure = rep.stages.iter().find(|s| s.name == "closure").unwrap();
    assert!(
        closure.detail.contains("cert_fail=1 (ambient=1)"),
        "{}",
        closure.detail
    );
    assert!(
        closure.detail.contains("minted=3 excess=1"),
        "{}",
        closure.detail
    );
}

/// A missing row is a reconstruct refusal — never a silent admit.
#[test]
fn gauntlet_missing_row() {
    let legs_store = MapStore {
        by_name: BTreeMap::new(),
        by_key: BTreeMap::new(),
    };
    let mut legs = TestLegs::new(legs_store);
    let rep = run_gauntlet(&mut legs, "ghost", &GauntletOptions::default());
    assert!(!rep.usable);
    assert_eq!(rep.stages[0].name, "reconstruct");
    assert_eq!(rep.stages[0].detail, "no object under this key");
}

/// full-data: a record that dropped hooks (unresolved after
/// transport) refuses before measure.
#[test]
fn gauntlet_full_data_refusal() {
    let store = store_with("k1", rec("obj", &["check", "derive"]));
    let mut legs = TestLegs::new(store);
    let rep = run_gauntlet(&mut legs, "k1", &GauntletOptions::default());
    assert!(!rep.usable);
    assert_eq!(stage_names(&rep), vec!["reconstruct", "full-data"]);
    assert_eq!(rep.stages[1].detail, "dropped hooks: check, derive");
}

/// Auto-cond armed on a `full-data` refusal of exactly `check`:
/// the retry rewrites the record and the second run clears every
/// stage, with the `auto-cond` stage prepended.
#[test]
fn gauntlet_auto_cond_retry() {
    let store = store_with("k1", rec("obj", &["check"]));
    let mut legs = TestLegs::new(store);
    legs.auto_cond_found = true;
    let opts = GauntletOptions {
        auto_cond: true,
        auto_cond_clauses: 3,
        ..GauntletOptions::default()
    };
    let rep = run_gauntlet(&mut legs, "k1", &opts);
    assert!(rep.usable, "reason: {}", rep.reason());
    assert_eq!(rep.stages[0].name, "auto-cond");
    assert!(rep.stages[0].passed);
    assert_eq!(rep.auto_cond.as_ref().unwrap()["found"], true);

    // Refusal case: no guard found — the original report stands,
    // annotated with the attempt.
    let store = store_with("k2", rec("obj2", &["check"]));
    let mut legs = TestLegs::new(store);
    legs.auto_cond_found = false;
    let rep = run_gauntlet(&mut legs, "k2", &opts);
    assert!(!rep.usable);
    assert_eq!(rep.auto_cond.as_ref().unwrap()["found"], false);
    assert!(
        rep.auto_cond.as_ref().unwrap()["first_reason"]
            .as_str()
            .unwrap()
            .starts_with("full-data:")
    );
}
