//! Rulecache round-trip — payload-internal parent resolution and
//! guard transport, mirroring `test_rulecache`/`test_rulecache_codec`.

use std::rc::Rc;

use handl_discovery::{
    BoundEnv, Mint, ReExpr, RuleCache, SynthParams, Term, cache_key, enc_rule, seed_fingerprint,
    uniform_hook_sig,
};
use handl_egraph::{AttrValue, Derived, Rewrite, attr_meta};

fn tmpdir(tag: &str) -> std::path::PathBuf {
    let d = std::env::temp_dir().join(format!(
        "handl-discovery-test-{}-{}",
        tag,
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&d);
    d
}

/// A parent with a check hook (term "a" must be leaf "good") and a
/// parent with a derive hook (attr "out" = 5).
fn parents() -> (Rc<Mint>, Rc<Mint>) {
    let p1 = Rc::new(Mint::bare(
        Rewrite::new("p1", Term::var("a"), Term::var("a"))
            .with_check(|env| env.terms.get("a") == Some(&Term::leaf("good"))),
    ));
    let p2 = Rc::new(Mint::bare(
        Rewrite::new("p2", Term::var("b"), Term::var("b"))
            .with_derive(|_| Some(vec![Derived::Attr(Rc::from("out"), AttrValue::Int(5))])),
    ));
    (p1, p2)
}

/// The composite minted over p1/p2: re-expressed through u/v, with an
/// "@2:out" attr placeholder the transported derive refills.
fn composite() -> Mint {
    let mut pat1 = ReExpr::default();
    pat1.terms.insert(Rc::from("a"), Term::var("u"));
    let mut pat2 = ReExpr::default();
    pat2.terms.insert(Rc::from("b"), Term::var("v"));
    let mut m = Mint::bare(Rewrite::new(
        "syn_c",
        Term::opl("f", vec![Term::var("u"), Term::var("v")]),
        Term::op("g", vec![Term::var("u")], vec![attr_meta("k", "@2:out")]),
    ));
    m.parents = vec![Rc::from("p1"), Rc::from("p2")];
    m.guard_pats = Some((pat1, pat2));
    // The minted rule carries its hooks (compose at mint time).
    let (check, derive) = handl_discovery::compose_guards(
        parents().0,
        parents().1,
        m.guard_pats.clone().unwrap().0,
        m.guard_pats.clone().unwrap().1,
    );
    m.rule.check = check;
    m.rule.derive = derive;
    m
}

/// The golden path: store a guarded composite, load it with the
/// parents by name — the transported check/derive behave exactly
/// like the minted ones.
#[test]
fn rulecache_roundtrip_guard_transport() {
    let dir = tmpdir("roundtrip");
    let cache = RuleCache::new(&dir);
    let (p1, p2) = parents();
    let c = Rc::new(composite());
    cache.store("k1", std::slice::from_ref(&c)).unwrap();

    let loaded = cache.load("k1", &[p1, p2]).expect("clean load");
    assert_eq!(loaded.len(), 1);
    let r = &loaded[0];
    assert_eq!(r.name.as_ref(), "syn_c");
    assert_eq!(r.parents, vec![Rc::from("p1"), Rc::from("p2")]);
    assert!(r.guard_pats.is_some());
    // The transported check re-runs both parents.
    let check = r.check.as_ref().expect("check transported");
    let good = BoundEnv {
        terms: [
            (Rc::from("u"), Term::leaf("good")),
            (Rc::from("v"), Term::leaf("x")),
        ]
        .into_iter()
        .collect(),
        attrs: Default::default(),
    };
    let bad = BoundEnv {
        terms: [
            (Rc::from("u"), Term::leaf("bad")),
            (Rc::from("v"), Term::leaf("x")),
        ]
        .into_iter()
        .collect(),
        attrs: Default::default(),
    };
    assert!(check(&good));
    assert!(!check(&bad));
    // The derive attaches — the RHS carries "@2:out".
    let derive = r.derive.as_ref().expect("derive transported");
    let extras = derive(&good).unwrap();
    assert!(extras.iter().any(|d| matches!(
        d,
        Derived::Attr(k, v) if k.as_ref() == "@2:out" && *v == AttrValue::Int(5)
    )));
}

/// Payload-internal resolution: a stored composite's parent is an
/// earlier record *of the same payload* — no caller rule needed.
#[test]
fn rulecache_payload_internal_parents() {
    let dir = tmpdir("payload");
    let cache = RuleCache::new(&dir);
    let (_p1, _p2) = parents();
    // c1 is a guarded composite over external parents; c2's guard
    // names c1 (stored earlier in the same payload) plus an external.
    let c1 = Rc::new(composite());
    // c2 over (c1, p1): c1's metavars are (u, v) — its check consumes
    // both sides of its own spec, so pat1 must re-express both.
    let mut pat1 = ReExpr::default();
    pat1.terms.insert(Rc::from("u"), Term::var("w"));
    pat1.terms.insert(Rc::from("v"), Term::var("z"));
    let mut c2 = Mint::bare(Rewrite::new("syn_c2", Term::var("w"), Term::var("w")));
    c2.parents = vec![Rc::from("syn_c"), Rc::from("p1")];
    let mut pat2 = ReExpr::default();
    pat2.terms.insert(Rc::from("a"), Term::var("w"));
    c2.guard_pats = Some((pat1.clone(), pat2));
    let (chk, drv) = handl_discovery::compose_guards(
        c1.clone(),
        parents().0,
        pat1,
        c2.guard_pats.clone().unwrap().1,
    );
    c2.rule.check = chk;
    c2.rule.derive = drv;
    let c2 = Rc::new(c2);

    cache.store("k2", &[c1, c2]).unwrap();
    // p1/p2 resolve from the caller ruleset; syn_c resolves
    // internally — c1 decodes first and joins the resolver.
    let loaded = cache
        .load("k2", &[parents().0, parents().1])
        .expect("payload-internal resolution");
    assert_eq!(loaded.len(), 2);
    let r2 = &loaded[1];
    let check = r2.check.as_ref().expect("check transported");
    // c2's pat1 maps c1's (u,v) <- (w,z): c1.check fires when
    // w == "good"; c2's pat2 maps p1's "a" <- "w" — same metavar.
    let good = BoundEnv {
        terms: [
            (Rc::from("w"), Term::leaf("good")),
            (Rc::from("z"), Term::leaf("any")),
        ]
        .into_iter()
        .collect(),
        attrs: Default::default(),
    };
    let bad = BoundEnv {
        terms: [
            (Rc::from("w"), Term::leaf("bad")),
            (Rc::from("z"), Term::leaf("any")),
        ]
        .into_iter()
        .collect(),
        attrs: Default::default(),
    };
    assert!(check(&good));
    assert!(!check(&bad));
}

/// Clean miss, never partial: a record naming a parent that resolves
/// nowhere fails the *whole* load.
#[test]
fn rulecache_missing_parent_clean_miss() {
    let dir = tmpdir("miss");
    let cache = RuleCache::new(&dir);
    let c = Rc::new(composite());
    cache.store("k3", &[c]).unwrap();
    // Only one parent supplied — the load must not partially apply.
    assert!(cache.load("k3", &[parents().0]).is_none());
    // Wrong key, version mismatch (hand-corrupted file).
    let path = cache.path("k3");
    let mut payload: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
    payload["version"] = serde_json::json!(99);
    std::fs::write(&path, serde_json::to_string(&payload).unwrap()).unwrap();
    assert!(cache.load("k3", &[parents().0, parents().1]).is_none());
    // Missing file entirely.
    assert!(cache.load("nope", &[]).is_none());
}

/// The honest refusal: hooks without a `guard_pats` spec cannot
/// store — silently dropping a side condition is the worse failure.
#[test]
fn rulecache_refuses_unspecced_hooks() {
    let hooked =
        Mint::bare(Rewrite::new("hand", Term::var("x"), Term::var("x")).with_check(|_| true));
    let err = enc_rule(&hooked).unwrap_err();
    assert!(err.contains("guard_pats"), "{err}");

    let dir = tmpdir("refuse");
    let cache = RuleCache::new(&dir);
    assert!(cache.store("k", &[Rc::new(hooked)]).is_err());
    // Bare (unguarded) rules still store and load.
    let bare = Rc::new(Mint::bare(Rewrite::new(
        "bare",
        Term::var("x"),
        Term::var("x"),
    )));
    cache.store("k", &[bare]).unwrap();
    let loaded = cache.load("k", &[]).unwrap();
    assert_eq!(loaded[0].name.as_ref(), "bare");
    assert!(loaded[0].check.is_none());
}

/// The derive attaches only when the RHS carries "@i:" placeholders —
/// a guarded composite over derive-parents whose RHS has none loads
/// check-only.
#[test]
fn rulecache_derive_attachment_policy() {
    let mut pat1 = ReExpr::default();
    pat1.terms.insert(Rc::from("a"), Term::var("u"));
    let mut pat2 = ReExpr::default();
    pat2.terms.insert(Rc::from("b"), Term::var("v"));
    let mut m = Mint::bare(Rewrite::new(
        "syn_noph",
        Term::var("u"),
        Term::var("u"), // no "@i:" placeholders
    ));
    m.parents = vec![Rc::from("p1"), Rc::from("p2")];
    m.guard_pats = Some((pat1.clone(), pat2.clone()));
    let (chk, drv) = handl_discovery::compose_guards(parents().0, parents().1, pat1, pat2);
    m.rule.check = chk;
    m.rule.derive = drv;

    let dir = tmpdir("noph");
    let cache = RuleCache::new(&dir);
    cache.store("k4", &[Rc::new(m)]).unwrap();
    let loaded = cache.load("k4", &[parents().0, parents().1]).unwrap();
    assert!(loaded[0].check.is_some());
    assert!(loaded[0].derive.is_none());
}

/// Fingerprints + cache key are deterministic and distinguish
/// distinct problem instances.
#[test]
fn fingerprints_distinguish() {
    let rules = vec![Rc::new(Mint::bare(Rewrite::new(
        "ax",
        Term::var("x"),
        Term::var("x"),
    )))];
    let params = SynthParams::default();
    let k1 = cache_key(&rules, &[], &params, &|r| uniform_hook_sig(r, "v1"));
    let k1b = cache_key(&rules, &[], &params, &|r| uniform_hook_sig(r, "v1"));
    assert_eq!(k1, k1b);
    // different seeds -> different key.
    let seeds = vec![Term::leaf("s")];
    let k2 = cache_key(&rules, &seeds, &params, &|r| uniform_hook_sig(r, "v1"));
    assert_ne!(k1, k2);
    // different params -> different key.
    let p2 = SynthParams {
        rounds: 3,
        ..SynthParams::default()
    };
    let k3 = cache_key(&rules, &[], &p2, &|r| uniform_hook_sig(r, "v1"));
    assert_ne!(k1, k3);
    // different hook signature -> different key (the _hook_sig seam)
    // — needs a hooked rule: a hookless rule's sig is "" under any tag.
    let hooked = vec![Rc::new(Mint::bare(
        Rewrite::new("h", Term::var("x"), Term::var("x")).with_check(|_| true),
    ))];
    let k4 = cache_key(&hooked, &[], &params, &|r| uniform_hook_sig(r, "v2"));
    let k4b = cache_key(&hooked, &[], &params, &|r| uniform_hook_sig(r, "v1"));
    assert_ne!(k4, k4b);
    // seed fingerprint is order-sensitive (the spec's contract).
    let a = Term::leaf("a");
    let b = Term::leaf("b");
    assert_ne!(
        seed_fingerprint(&[a.clone(), b.clone()]),
        seed_fingerprint(&[b, a])
    );
}
