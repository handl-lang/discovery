//! Persistent cache for synthesized rewrite rules —
//! `catopt_core.rulecache`.
//!
//! The synthesis engine's output is pure data: Op-tree lhs/rhs
//! patterns plus *hooks*. Hooks are not serialized — each guarded
//! rule stores its *re-expression spec*: the parent pair names and
//! the two substitution maps `(pat1, pat2)` that map each parent's
//! metavariables to patterns over the derived rule's metavars. At
//! load time the composite hooks are rebuilt by re-running
//! [`compose_guards`] against the parent rules resolved by name — the
//! composition machinery is cheap; it is the search/validation that
//! was expensive.
//!
//! Round-trip contract (the spec verbatim):
//!
//! * **Payload-internal parent resolution.** Records decode in
//!   stored order and each decoded rule joins the resolver, so a
//!   fixpoint mint's `syn_*` parents — earlier records of the same
//!   payload — resolve inside the payload and a multi-round output
//!   round-trips self-contained. A caller rule and a stored record
//!   sharing a name resolve to the stored one.
//! * **Guard transport.** A guarded record's `pat1`/`pat2` re-run
//!   `compose_guards` over the resolved parents; the composite
//!   `derive` attaches only when the RHS carries `"@i:"` placeholders
//!   (the spec's offer/load policy).
//! * **Clean miss, never partial.** A missing parent, a version/key
//!   mismatch, or a corrupt file returns `None` — never a
//!   partially-loaded set.
//! * **Honest refusal to store.** A rule carrying hooks without a
//!   `guard_pats` spec is not synthesizer output — `store`/`enc_rule`
//!   refuse rather than silently dropping its side conditions.

use std::collections::BTreeMap;
use std::io;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use handl_egraph::{Rewrite, Term};
use serde_json::{Value, json};
use sha2::Digest;

use crate::codec::{dec_reexpr, enc_reexpr, term_from_data, term_to_data};
use crate::terms::{Mint, ReExpr, compose_guards, rhs_derive_placeholders};

/// Bump when the on-disk format or reconstruction semantics change —
/// `rulecache.CACHE_VERSION`.
pub const CACHE_VERSION: u64 = 1;

// ---------------------------------------------------------------------------
//  Rule records
// ---------------------------------------------------------------------------

/// The stored form of one rule — `_enc_rule`'s record.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct RuleRecord {
    /// Rule name (the resolver key).
    pub name: String,
    /// Law/lemma name (metadata).
    #[serde(default)]
    pub law: String,
    /// Parent rule names (composite provenance).
    #[serde(default)]
    pub parents: Vec<String>,
    /// `term_to_data` lhs/rhs patterns.
    pub lhs: Value,
    /// See `lhs`.
    pub rhs: Value,
    /// The guard re-expression spec — `{"pat1": …, "pat2": …}`.
    #[serde(default)]
    pub guard: Option<GuardRecord>,
}

/// The stored guard spec — `pat1`/`pat2` in `enc_reexpr` wire form.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct GuardRecord {
    /// Parent 1's re-expression map.
    pub pat1: Value,
    /// Parent 2's re-expression map.
    pub pat2: Value,
}

/// Serialize a mint — `_enc_rule`.
///
/// `Err` when the rule carries hooks without a `guard_pats`
/// re-expression spec — the spec's `TypeError`: only rules emitted by
/// the synthesizer are cacheable.
pub fn enc_rule(mint: &Mint) -> Result<RuleRecord, String> {
    let guarded = mint.check.is_some() || mint.derive.is_some();
    if guarded && mint.guard_pats.is_none() {
        return Err(format!(
            "rule {:?} has check/derive hooks but no guard_pats re-expression \
             spec — only rules emitted by the synthesizer are cacheable",
            mint.name
        ));
    }
    let guard = match (guarded, &mint.guard_pats) {
        (true, Some((pat1, pat2))) => Some(GuardRecord {
            pat1: enc_reexpr(pat1),
            pat2: enc_reexpr(pat2),
        }),
        _ => None,
    };
    Ok(RuleRecord {
        name: mint.name.to_string(),
        law: mint.law.clone(),
        parents: mint.parents.iter().map(|p| p.to_string()).collect(),
        lhs: term_to_data(&mint.lhs),
        rhs: term_to_data(&mint.rhs),
        guard,
    })
}

/// Rebuild a rule — `_dec_rule`.
///
/// Guarded rules re-run [`compose_guards`] on the stored
/// re-expression maps; the parents must resolve (by name) in
/// *by_name*, or the error propagates and the whole load is a miss.
/// The composite `derive` attaches only where the RHS carries the
/// `"@i:"` placeholders it refills — the spec's offer/load policy.
pub fn dec_rule(
    rec: &RuleRecord,
    by_name: &BTreeMap<Rc<str>, Rc<Mint>>,
) -> Result<Rc<Mint>, String> {
    let lhs = term_from_data(&rec.lhs).map_err(|e| e.0)?;
    let rhs = term_from_data(&rec.rhs).map_err(|e| e.0)?;
    let mut check = None;
    let mut derive = None;
    let mut pats: Option<(ReExpr, ReExpr)> = None;
    if let Some(guard) = &rec.guard {
        if rec.parents.len() != 2 {
            return Err(format!(
                "rule {:?} guard spec wants a parent pair, found {}",
                rec.name,
                rec.parents.len()
            ));
        }
        let r1 = by_name
            .get(rec.parents[0].as_str())
            .ok_or_else(|| format!("missing parent {:?}", rec.parents[0]))?;
        let r2 = by_name
            .get(rec.parents[1].as_str())
            .ok_or_else(|| format!("missing parent {:?}", rec.parents[1]))?;
        let p1 = dec_reexpr(&guard.pat1).map_err(|e| e.0)?;
        let p2 = dec_reexpr(&guard.pat2).map_err(|e| e.0)?;
        let (chk, drv) = compose_guards(r1.clone(), r2.clone(), p1.clone(), p2.clone());
        check = chk;
        // Same policy as synthesize_rules.offer: the composite derive
        // is only attached when the RHS actually carries "@i:"
        // placeholders.
        derive = drv.filter(|_| !rhs_derive_placeholders(&rhs).is_empty());
        pats = Some((p1, p2));
    }
    let mut rule = Rewrite::new(Rc::from(rec.name.as_str()), lhs, rhs);
    rule.law = rec.law.clone();
    rule.check = check;
    rule.derive = derive;
    let mut mint = Mint::bare(rule);
    mint.parents = rec.parents.iter().map(|p| Rc::from(p.as_str())).collect();
    mint.guard_pats = pats;
    Ok(Rc::new(mint))
}

// ---------------------------------------------------------------------------
//  Fingerprints / cache key
// ---------------------------------------------------------------------------

/// sha256 over nul-separated parts — `rulecache._sha`.
pub fn sha256_hex<'a>(parts: impl Iterator<Item = &'a str>) -> String {
    let mut h = sha2::Sha256::new();
    for p in parts {
        h.update(p.as_bytes());
        h.update(b"\0");
    }
    format!("{:x}", h.finalize())
}

/// Stability signatures for a rule's hooks — the `_hook_sig` seam.
///
/// Rust `dyn Fn` hooks are opaque (no `inspect.getsource`); the domain
/// supplies a tag — its rule-bank version, or a content hash of the
/// spec the hooks were compiled from. An unstable signature only ever
/// causes a cache *miss*, never a wrong hit — conservative by design.
#[derive(Clone, Debug, Default)]
pub struct HookSigs {
    /// Signature covering `rule.check` (`""` when absent).
    pub check: String,
    /// Signature covering `rule.derive` (`""` when absent).
    pub derive: String,
    /// Declarative-guard data (the spec's `cond`/`dspec` slots) —
    /// hashed *as data* because one folded closure signature cannot
    /// see a data edit. Domains without declarative guards leave
    /// `Value::Null`.
    pub guard_data: Value,
}

/// `HookSigs` for a rule whose hooks all share one tag.
///
/// `check`/`derive` get `tag` when present, `""` otherwise — the
/// spec's `fn is None -> ""` leg.
pub fn uniform_hook_sig(rule: &Rewrite, tag: &str) -> HookSigs {
    HookSigs {
        check: if rule.check.is_some() {
            tag.to_string()
        } else {
            String::new()
        },
        derive: if rule.derive.is_some() {
            tag.to_string()
        } else {
            String::new()
        },
        guard_data: Value::Null,
    }
}

/// Hash of the parent ruleset — `rulecache.ruleset_fingerprint`.
///
/// Covers every rule's name, serialized lhs/rhs patterns, and hook
/// signatures — sorted so rule order doesn't matter.
pub fn ruleset_fingerprint(rules: &[Rc<Mint>], sig: &dyn Fn(&Rewrite) -> HookSigs) -> String {
    let mut entries: Vec<String> = rules
        .iter()
        .map(|r| {
            let s = sig(r);
            serde_json::to_string(&json!({
                "name": r.name.as_ref(),
                "lhs": term_to_data(&r.lhs),
                "rhs": term_to_data(&r.rhs),
                "check": s.check,
                "derive": s.derive,
                // The spec's separate "cond"/"dspec" data slots fold
                // into one declarative-guard slot here — same honesty:
                // a folded closure signature can't see a data edit.
                "guard": s.guard_data,
            }))
            .unwrap_or_default()
        })
        .collect();
    entries.sort();
    sha256_hex(entries.iter().map(String::as_str))
}

/// Hash of the serialized seed terms, in order —
/// `rulecache.seed_fingerprint`.
///
/// Seed order affects which derivations are explored and rule naming.
pub fn seed_fingerprint(seed_terms: &[Term]) -> String {
    sha256_hex(
        seed_terms
            .iter()
            .map(|s| {
                // serde_json maps are BTreeMaps — sort_keys=True semantics.
                serde_json::to_string(&term_to_data(s)).unwrap_or_default()
            })
            .collect::<Vec<String>>()
            .iter()
            .map(String::as_str),
    )
}

/// The synthesis problem's parameters — `cache_key`'s `params`.
#[derive(Clone, Debug)]
pub struct SynthParams {
    /// Search fuel.
    pub fuel: u64,
    /// Numeric spot-check during validation.
    pub numeric_check: bool,
    /// Require the critical pair to overlap.
    pub require_overlap: bool,
    /// Emit rules subsumed by an existing one.
    pub emit_subsumed: bool,
    /// Fixpoint rounds (changes the mint — keys).
    pub rounds: u64,
    /// Emission cap per round (changes the mint — keys).
    pub max_emitted: Option<u64>,
    /// The `on_round` observer's signature proxy — `""` for none; a
    /// vetoing observer truncates the fixpoint and must not share the
    /// unobserved entry.
    pub observer: String,
}

impl Default for SynthParams {
    fn default() -> SynthParams {
        SynthParams {
            fuel: 512,
            numeric_check: true,
            require_overlap: true,
            emit_subsumed: false,
            rounds: 1,
            max_emitted: None,
            observer: String::new(),
        }
    }
}

/// The cache key for one synthesis problem instance —
/// `rulecache.cache_key`.
///
/// Combines the ruleset fingerprint, seed fingerprint, synthesis
/// params, and format version.
pub fn cache_key(
    rules: &[Rc<Mint>],
    seed_terms: &[Term],
    params: &SynthParams,
    sig: &dyn Fn(&Rewrite) -> HookSigs,
) -> String {
    let payload = json!({
        "version": CACHE_VERSION,
        "ruleset": ruleset_fingerprint(rules, sig),
        "seeds": seed_fingerprint(seed_terms),
        "params": {
            "fuel": params.fuel,
            "numeric_check": params.numeric_check,
            "require_overlap": params.require_overlap,
            "emit_subsumed": params.emit_subsumed,
            "rounds": params.rounds,
            "max_emitted": params.max_emitted,
            "observer": params.observer,
        },
    });
    sha256_hex(
        [serde_json::to_string(&payload).unwrap_or_default()]
            .iter()
            .map(String::as_str),
    )
}

// ---------------------------------------------------------------------------
//  RuleCache + convenience wrapper
// ---------------------------------------------------------------------------

/// Filesystem cache of synthesized rule sets, one JSON file per key —
/// `rulecache.RuleCache`.
pub struct RuleCache {
    /// The cache directory.
    pub dir: PathBuf,
}

impl RuleCache {
    /// A cache rooted at *dir* (created on first store).
    pub fn new(dir: impl Into<PathBuf>) -> RuleCache {
        RuleCache { dir: dir.into() }
    }

    /// The cache file path for *key* — `rules-{key}.json`.
    pub fn path(&self, key: &str) -> PathBuf {
        self.dir.join(format!("rules-{key}.json"))
    }

    /// Persist *mints* under *key* — `RuleCache.store`.
    ///
    /// `Err` if a rule carries hooks without a `guard_pats` spec
    /// (not synthesizer output), rather than silently dropping its
    /// side conditions. Writes are tmp-then-rename like the spec's.
    pub fn store(&self, key: &str, mints: &[Rc<Mint>]) -> io::Result<PathBuf> {
        std::fs::create_dir_all(&self.dir)?;
        let records: Vec<RuleRecord> = mints
            .iter()
            .map(|m| enc_rule(m))
            .collect::<Result<_, _>>()
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidInput, e))?;
        let payload = json!({
            "version": CACHE_VERSION,
            "key": key,
            "rules": records,
        });
        let tmp = self.dir.join(format!(".rules-{key}.tmp"));
        std::fs::write(&tmp, serde_json::to_string(&payload)?)?;
        let path = self.path(key);
        std::fs::rename(&tmp, &path)?;
        Ok(path)
    }

    /// Load the rule set stored under *key*, or `None` on a miss —
    /// `RuleCache.load`.
    ///
    /// *parents* is the caller ruleset: guarded rules rebuild their
    /// composite check/derive from the parents' hooks, resolved by
    /// name. Records decode in stored order and each decoded rule
    /// joins the resolver — payload-internal parent resolution. A
    /// missing parent, a version/key mismatch, or a corrupt file is a
    /// clean miss — never a partially-loaded set.
    pub fn load(&self, key: &str, parents: &[Rc<Mint>]) -> Option<Vec<Rc<Mint>>> {
        let path: &Path = &self.path(key);
        let text = std::fs::read_to_string(path).ok()?;
        let payload: Value = serde_json::from_str(&text).ok()?;
        if payload.get("version").and_then(Value::as_u64) != Some(CACHE_VERSION)
            || payload.get("key").and_then(Value::as_str) != Some(key)
        {
            return None;
        }
        let mut by_name: BTreeMap<Rc<str>, Rc<Mint>> = parents
            .iter()
            .map(|m| (m.name.clone(), m.clone()))
            .collect();
        let mut out = Vec::new();
        for rec in payload.get("rules")?.as_array()? {
            let rec: RuleRecord = serde_json::from_value(rec.clone()).ok()?;
            let rule = dec_rule(&rec, &by_name).ok()?;
            by_name.insert(rule.name.clone(), rule.clone());
            out.push(rule);
        }
        Some(out)
    }
}

/// `meta.synthesize_rules` with persistence —
/// `rulecache.synthesize_rules_cached`.
///
/// On a repeat call with the same ruleset, seeds, and parameters the
/// derived rules load from the cache (composite guards rebuilt from
/// the parent hooks) instead of re-deriving. *synthesize* is the
/// domain engine, injected: the search machinery is out of this
/// crate's scope — the cache contract is what is ported.
pub fn synthesize_rules_cached(
    cache: &RuleCache,
    rules: &[Rc<Mint>],
    seed_terms: &[Term],
    params: &SynthParams,
    sig: &dyn Fn(&Rewrite) -> HookSigs,
    synthesize: impl FnOnce(&[Rc<Mint>], &[Term], &SynthParams) -> Vec<Rc<Mint>>,
) -> io::Result<Vec<Rc<Mint>>> {
    let key = cache_key(rules, seed_terms, params, sig);
    if let Some(hit) = cache.load(&key, rules) {
        return Ok(hit);
    }
    let derived = synthesize(rules, seed_terms, params);
    cache.store(&key, &derived)?;
    Ok(derived)
}
