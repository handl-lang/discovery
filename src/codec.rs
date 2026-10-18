//! The JSON wire codec — `ir.term_to_data` / `rulecache._enc_binding`
//! ported for the generic `Term`/`ReExpr` shapes.
//!
//! The scheme mirrors the spec's canonical form where it applies:
//!
//! * `{"mvar": name}` — a pattern metavariable (`Term::Var`).
//! * `{"leaf": key}` — a concrete leaf (`Term::Leaf`). The spec's
//!   typed leaf kinds (`Const`/`Var`/`Param`) ride the *key* in this
//!   substrate — the bridge's self-describing-leaf convention.
//! * `{"op": name, "args": [...], "attrs": {k: v}}` — an `Op` node.
//!   Attr entries are the value's `AttrValue` JSON form for
//!   `TermAttr::Lit`, and `{"amvar": name}` for `TermAttr::Meta` —
//!   the typed port of the spec's bare-string ambiguity (a Python
//!   string attr is both "literal string" and "metavar reference";
//!   here the two are distinct, strictly more honest).
//!
//! Binding maps (`ReExpr` / fired substitutions) encode as the spec's
//! `[key, {"t": term} | {"a": attr}]` pair lists.

use std::rc::Rc;

use handl_egraph::{AttrValue, BoundEnv, Term, TermAttr};
use serde_json::{Map, Value, json};

use crate::terms::ReExpr;

/// Codec failure — the spec's `ValueError`/`TypeError` read as data.
#[derive(Debug, Clone)]
pub struct CodecError(pub String);

impl std::fmt::Display for CodecError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for CodecError {}

fn bad<T>(what: &str, v: &Value) -> Result<T, CodecError> {
    Err(CodecError(format!("bad {what} encoding: {v}")))
}

// ---------------------------------------------------------------------------
//  Attr values
// ---------------------------------------------------------------------------

/// Encode an attribute value — `ir.attr_to_data`.
///
/// `AttrValue`'s JSON form is already the spec's scalar/composite
/// domain (null/bool/int/float/str/array/object). `Float` payloads
/// that are non-finite encode as JSON `null` — a named divergence
/// from Python, where `float("nan")` serializes as `NaN` text; the
/// cache treats the wire form as opaque either way.
pub fn attr_to_data(v: &AttrValue) -> Value {
    v.to_json()
}

/// Decode an attribute value — `ir.attr_from_data`.
pub fn attr_from_data(v: &Value) -> Result<AttrValue, CodecError> {
    Ok(AttrValue::from(v))
}

/// `AttrValue` ↔ kernel `TaggedValue` — the eval-boundary bridge for
/// domains whose bindings ride kernel values.
pub fn attr_from_tagged(v: &handl_value::TaggedValue) -> AttrValue {
    AttrValue::from_tagged(v)
}

// ---------------------------------------------------------------------------
//  Terms
// ---------------------------------------------------------------------------

/// Encode a (sub)term — `ir.term_to_data`.
pub fn term_to_data(t: &Term) -> Value {
    match t {
        Term::Var(name) => json!({"mvar": name.as_ref()}),
        Term::Leaf(key) => json!({"leaf": key.as_ref()}),
        Term::Op(op) => {
            let attrs: Map<String, Value> = op
                .attrs
                .iter()
                .map(|(k, v)| {
                    let d = match v {
                        TermAttr::Lit(v) => attr_to_data(v),
                        TermAttr::Meta(name) => json!({"amvar": name.as_ref()}),
                    };
                    (k.to_string(), d)
                })
                .collect();
            json!({
                "op": op.op.as_ref(),
                "args": op.args.iter().map(term_to_data).collect::<Vec<_>>(),
                "attrs": Value::Object(attrs),
            })
        }
    }
}

/// Decode a (sub)term — `ir.term_from_data`.
pub fn term_from_data(d: &Value) -> Result<Term, CodecError> {
    let obj = d
        .as_object()
        .ok_or_else(|| CodecError(format!("bad term encoding: {d}")))?;
    if let Some(m) = obj.get("mvar") {
        return m
            .as_str()
            .map(Term::var)
            .ok_or_else(|| CodecError(format!("bad term encoding: {d}")));
    }
    if let Some(k) = obj.get("leaf") {
        return k
            .as_str()
            .map(Term::leaf)
            .ok_or_else(|| CodecError(format!("bad term encoding: {d}")));
    }
    if let Some(op) = obj.get("op") {
        let op = op
            .as_str()
            .ok_or_else(|| CodecError(format!("bad term encoding: {d}")))?;
        let args = obj
            .get("args")
            .and_then(Value::as_array)
            .ok_or_else(|| CodecError(format!("bad term encoding: {d}")))?
            .iter()
            .map(term_from_data)
            .collect::<Result<Vec<_>, _>>()?;
        let attrs = obj
            .get("attrs")
            .and_then(Value::as_object)
            .ok_or_else(|| CodecError(format!("bad term encoding: {d}")))?;
        let mut attr_list = Vec::with_capacity(attrs.len());
        for (k, v) in attrs {
            let tv = if let Some(m) = v.get("amvar") {
                TermAttr::Meta(Rc::from(
                    m.as_str()
                        .ok_or_else(|| CodecError(format!("bad attr encoding: {v}")))?,
                ))
            } else {
                TermAttr::Lit(attr_from_data(v)?)
            };
            attr_list.push((Rc::from(k.as_str()), tv));
        }
        return Ok(Term::op(op, args, attr_list));
    }
    bad("term", d)
}

// ---------------------------------------------------------------------------
//  Binding / re-expression maps — rulecache._enc_binding / _dec_binding
// ---------------------------------------------------------------------------

/// Encode a re-expression/substitution map — `rulecache._enc_binding`.
///
/// `[[key, {"t": term}], [key, {"a": attr}]]` — term metavars under
/// `"t"`, attr metavars under `"a"` (the spec's `"$attr:"` namespace,
/// carried typed here: the map keys are plain names, the `TermAttr`
/// distinguishes literal values from meta references).
pub fn enc_reexpr(m: &ReExpr) -> Value {
    let mut out = Vec::with_capacity(m.terms.len() + m.attrs.len());
    for (k, v) in m.terms.iter() {
        out.push(json!([k.as_ref(), {"t": term_to_data(v)}]));
    }
    for (k, v) in m.attrs.iter() {
        let d = match v {
            TermAttr::Lit(v) => attr_to_data(v),
            TermAttr::Meta(name) => json!({"amvar": name.as_ref()}),
        };
        out.push(json!([k.as_ref(), {"a": d}]));
    }
    Value::Array(out)
}

/// Decode a re-expression map — `rulecache._dec_binding`.
pub fn dec_reexpr(pairs: &Value) -> Result<ReExpr, CodecError> {
    let mut out = ReExpr::default();
    let list = pairs
        .as_array()
        .ok_or_else(|| CodecError(format!("bad binding encoding: {pairs}")))?;
    for e in list {
        let pair = e
            .as_array()
            .filter(|p| p.len() == 2)
            .ok_or_else(|| CodecError(format!("bad binding encoding: {e}")))?;
        let k = pair[0]
            .as_str()
            .ok_or_else(|| CodecError(format!("bad binding encoding: {e}")))?;
        let enc = &pair[1];
        if let Some(t) = enc.get("t") {
            out.terms.insert(Rc::from(k), term_from_data(t)?);
        } else if let Some(a) = enc.get("a") {
            let tv = if let Some(m) = a.get("amvar") {
                TermAttr::Meta(Rc::from(
                    m.as_str()
                        .ok_or_else(|| CodecError(format!("bad attr encoding: {a}")))?,
                ))
            } else {
                TermAttr::Lit(attr_from_data(a)?)
            };
            out.attrs.insert(Rc::from(k), tv);
        } else {
            return bad("binding", e);
        }
    }
    Ok(out)
}

/// A fired binding environment's wire form — the same pair list with
/// concrete values only (a `BoundEnv` carries no `Meta` positions).
pub fn enc_env(env: &BoundEnv) -> Value {
    let mut out = Vec::with_capacity(env.terms.len() + env.attrs.len());
    for (k, v) in env.terms.iter() {
        out.push(json!([k.as_ref(), {"t": term_to_data(v)}]));
    }
    for (k, v) in env.attrs.iter() {
        out.push(json!([k.as_ref(), {"a": attr_to_data(v)}]));
    }
    Value::Array(out)
}
