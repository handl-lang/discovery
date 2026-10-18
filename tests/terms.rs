//! Term-level pattern machinery — match/instantiate/re-express and
//! guard transport, on small fixtures.

use std::rc::Rc;

use handl_discovery::{
    BoundEnv, Mint, ReExpr, TermAttr, compose_guards, free_mvs, instantiate_lenient,
    instantiate_strict, leaf_metavars, match_pattern, metavar_parents, reexpress_binding,
    rhs_derive_placeholders,
};
use handl_egraph::{AttrValue, Derived, Rewrite, Term, attr, attr_meta};

fn env(terms: &[(&str, Term)], attrs: &[(&str, AttrValue)]) -> BoundEnv {
    BoundEnv {
        terms: terms
            .iter()
            .map(|(k, v)| (Rc::from(*k), v.clone()))
            .collect(),
        attrs: attrs
            .iter()
            .map(|(k, v)| (Rc::from(*k), v.clone()))
            .collect(),
    }
}

/// Repeated metavariables must bind structurally equal subterms —
/// `_term_match`'s contract.
#[test]
fn match_repeated_metavar() {
    let pat = Term::opl("add", vec![Term::var("a"), Term::var("a")]);
    let good = Term::opl("add", vec![Term::leaf("x"), Term::leaf("x")]);
    let bad = Term::opl("add", vec![Term::leaf("x"), Term::leaf("y")]);
    let mut e = BoundEnv::default();
    assert!(match_pattern(&pat, &good, &mut e));
    assert_eq!(e.terms["a"], Term::leaf("x"));
    assert!(!match_pattern(&pat, &bad, &mut BoundEnv::default()));
}

/// Attr metavariables bind values; literals compare with `match_eq`
/// (the spec's numeric leniency — `1` pattern matches `1.0` term).
#[test]
fn match_attr_meta_and_leniency() {
    let pat = Term::op("clamp", vec![Term::var("x")], vec![attr_meta("min", "m")]);
    let term = Term::op(
        "clamp",
        vec![Term::leaf("t")],
        vec![attr("min", AttrValue::Float(1.5))],
    );
    let mut e = BoundEnv::default();
    assert!(match_pattern(&pat, &term, &mut e));
    assert_eq!(e.attrs["m"], AttrValue::Float(1.5));

    // Numeric leniency: Int(1) pattern vs Float(1.0) term matches.
    let pat_lit = Term::op("clamp", vec![Term::var("x")], vec![attr("min", 1i64)]);
    let term_int_float = Term::op(
        "clamp",
        vec![Term::leaf("t")],
        vec![attr("min", AttrValue::Float(1.0))],
    );
    assert!(match_pattern(
        &pat_lit,
        &term_int_float,
        &mut BoundEnv::default()
    ));
    // But 1 vs 1.5 does not — leniency is numeric equality, not truncation.
    assert!(!match_pattern(&pat_lit, &term, &mut BoundEnv::default()));
    // Key-set mismatch refuses.
    let term_other = Term::op(
        "clamp",
        vec![Term::leaf("t")],
        vec![attr("max", AttrValue::Float(1.5))],
    );
    assert!(!match_pattern(&pat, &term_other, &mut BoundEnv::default()));
}

/// strict vs lenient instantiation — the spec's `KeyError` (strict)
/// vs literal-name fallback (lenient) on unbound attr metavars.
#[test]
fn instantiate_strict_vs_lenient() {
    let pat = Term::op("f", vec![Term::var("x")], vec![attr_meta("k", "m")]);
    let e = env(&[("x", Term::leaf("v"))], &[]);
    // strict: unbound attr metavars veto.
    assert!(instantiate_strict(&pat, &e).is_none());
    // lenient: the attr metavar falls back to its literal name.
    let got = instantiate_lenient(&pat, &e).unwrap();
    let Term::Op(op) = &got else { panic!() };
    assert_eq!(op.attrs[0].1, TermAttr::Lit(AttrValue::Str(Rc::from("m"))));
    // unbound *term* metavars veto in both.
    assert!(instantiate_lenient(&Term::var("y"), &e).is_none());
}

/// `leaf_metavars` / `metavar_parents` / `free_mvs` — the generic
/// introspection the enumeration's domain wiring uses.
#[test]
fn pattern_introspection() {
    let lhs = Term::opl(
        "reshape",
        vec![Term::opl("mul", vec![Term::var("u"), Term::var("v")])],
    );
    let rhs = Term::var("u");
    assert_eq!(leaf_metavars(&lhs), vec![Rc::from("u"), Rc::from("v")]);
    let parents = metavar_parents(&[&lhs, &rhs]);
    // u's only *op* parent is "mul" (the rhs bare metavar has none).
    assert_eq!(parents["u"], ["mul"].into_iter().map(Rc::from).collect());
    assert_eq!(parents["v"], ["mul"].into_iter().map(Rc::from).collect());
    // free = no viewish parent: "mul" viewish covers both metavars.
    let viewish = ["reshape"].into_iter().map(Rc::from).collect();
    let free = free_mvs(&parents, &Default::default(), &viewish);
    assert_eq!(free, vec![Rc::from("u"), Rc::from("v")]);
    let viewish = ["mul"].into_iter().map(Rc::from).collect();
    assert!(free_mvs(&parents, &Default::default(), &viewish).is_empty());
    // covered removes v.
    let covered = ["v"].into_iter().map(Rc::from).collect();
    let viewish = ["reshape"].into_iter().map(Rc::from).collect();
    assert_eq!(free_mvs(&parents, &covered, &viewish), vec![Rc::from("u")]);
}

/// `reexpress_binding` — parent metavars as patterns over the
/// derived env; attr `Meta` refs resolve through the fired binding,
/// a missing ref vetoes.
#[test]
fn reexpress_binding_resolution() {
    let mut pats = ReExpr::default();
    pats.terms.insert(
        Rc::from("a"),
        Term::opl("mul", vec![Term::var("u"), Term::leaf("2")]),
    );
    pats.attrs
        .insert(Rc::from("dim"), TermAttr::Meta(Rc::from("d")));
    pats.attrs
        .insert(Rc::from("fixed"), TermAttr::Lit(AttrValue::Int(7)));
    let e = env(&[("u", Term::leaf("x"))], &[("d", AttrValue::Int(1))]);
    let got = reexpress_binding(&pats, &e).unwrap();
    assert_eq!(
        got.terms["a"],
        Term::opl("mul", vec![Term::leaf("x"), Term::leaf("2")])
    );
    assert_eq!(got.attrs["dim"], AttrValue::Int(1));
    assert_eq!(got.attrs["fixed"], AttrValue::Int(7));
    // missing attr ref vetoes the whole composition.
    let e2 = env(&[("u", Term::leaf("x"))], &[]);
    assert!(reexpress_binding(&pats, &e2).is_none());
    // missing term metavar vetoes too.
    let e3 = env(&[], &[("d", AttrValue::Int(1))]);
    assert!(reexpress_binding(&pats, &e3).is_none());
}

/// `compose_guards` — the composite check re-runs each parent's guard
/// on its own re-expressed binding.
#[test]
fn compose_guards_semantics() {
    // p1: requires term "a" == leaf "good".
    let p1 = Rc::new(Mint::bare(
        Rewrite::new("p1", Term::var("a"), Term::var("a"))
            .with_check(|env| env.terms.get("a") == Some(&Term::leaf("good"))),
    ));
    // p2: requires term "b" == leaf "also"; derives attr "out"=5.
    let p2 = Rc::new(Mint::bare(
        Rewrite::new("p2", Term::var("b"), Term::var("b"))
            .with_check(|env| env.terms.get("b") == Some(&Term::leaf("also")))
            .with_derive(|_env| Some(vec![Derived::Attr(Rc::from("out"), AttrValue::Int(5))])),
    ));
    let mut pat1 = ReExpr::default();
    pat1.terms.insert(Rc::from("a"), Term::var("u"));
    let mut pat2 = ReExpr::default();
    pat2.terms.insert(Rc::from("b"), Term::var("v"));
    let (check, derive) = compose_guards(p1, p2, pat1, pat2);
    let check = check.expect("guarded parents compose");
    let derive = derive.expect("guarded parents compose");

    // both parents accept.
    let good = env(&[("u", Term::leaf("good")), ("v", Term::leaf("also"))], &[]);
    assert!(check(&good));
    // p1 vetoes.
    let bad1 = env(&[("u", Term::leaf("bad")), ("v", Term::leaf("also"))], &[]);
    assert!(!check(&bad1));
    // p2 vetoes.
    let bad2 = env(&[("u", Term::leaf("good")), ("v", Term::leaf("bad"))], &[]);
    assert!(!check(&bad2));
    // derive namespaces parent-2's output under "@2:".
    let extras = derive(&good).unwrap();
    assert_eq!(extras.len(), 1);
    match &extras[0] {
        Derived::Attr(k, v) => {
            assert_eq!(k.as_ref(), "@2:out");
            assert_eq!(*v, AttrValue::Int(5));
        }
        _ => panic!("expected attr extra"),
    }
}

/// Parent derive outputs travel namespaced under "@1:"/"@2:" —
/// term and attr channels alike.
#[test]
fn compose_guards_derive_namespace() {
    let p1 = Rc::new(Mint::bare(
        Rewrite::new("p1", Term::var("a"), Term::var("a"))
            .with_derive(|_| Some(vec![Derived::Attr(Rc::from("e"), AttrValue::Int(1))])),
    ));
    let p2 = Rc::new(Mint::bare(
        Rewrite::new("p2", Term::var("b"), Term::var("b"))
            .with_derive(|_| Some(vec![Derived::Term(Rc::from("t"), Term::leaf("z"))])),
    ));
    let (check, derive) = compose_guards(p1, p2, ReExpr::default(), ReExpr::default());
    assert!(check.unwrap()(&BoundEnv::default()));
    let extras = derive.unwrap()(&BoundEnv::default()).unwrap();
    let mut names: Vec<Rc<str>> = extras
        .iter()
        .map(|d| match d {
            Derived::Attr(k, _) | Derived::Term(k, _) | Derived::Class(k, _) => k.clone(),
        })
        .collect();
    names.sort();
    assert_eq!(names, vec![Rc::from("@1:e"), Rc::from("@2:t")]);
}

/// Unguarded parents produce no hooks — `_compose_guards`' early out.
#[test]
fn compose_guards_unguarded() {
    let p1 = Rc::new(Mint::bare(Rewrite::new(
        "p1",
        Term::var("a"),
        Term::var("a"),
    )));
    let p2 = Rc::new(Mint::bare(Rewrite::new(
        "p2",
        Term::var("b"),
        Term::var("b"),
    )));
    let (c, d) = compose_guards(p1, p2, ReExpr::default(), ReExpr::default());
    assert!(c.is_none() && d.is_none());
}

/// `rhs_derive_placeholders` finds "@i:" metavars in both positions.
#[test]
fn rhs_placeholders() {
    let rhs = Term::op(
        "g",
        vec![Term::var("@1:sd"), Term::var("x")],
        vec![attr_meta("out", "@2:d")],
    );
    let got = rhs_derive_placeholders(&rhs);
    assert_eq!(got, ["@1:sd", "@2:d"].into_iter().map(Rc::from).collect());
    assert!(rhs_derive_placeholders(&Term::var("x")).is_empty());
}
