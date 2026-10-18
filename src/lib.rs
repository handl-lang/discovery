//! # handl-discovery
//!
//! The pure-compute legs of catopt's discovery/gauntlet machinery —
//! the named Rust port of the domain-free half of
//! `catopt_discovery` (`oracle`, `evidence`) and `catopt_core.rulecache`
//! — composed over [`handl_egraph`]'s saturation substrate.
//!
//! The port is **by contract, not by translation**: enumeration
//! order, cap semantics, premise-closure totality, the
//! stored-composite round-trip, and the gauntlet's gate order mirror
//! the Python spec; the domain legs (numeric oracles, leaf binding
//! banks, `JOINT_SHAPES`-style shape tables, `dag_cost` alphabets,
//! measurement pipelines) are injected via traits and data, never
//! baked in. Divergences are named on each item.
//!
//! ## What ships
//!
//! * [`enumerate`] — bounded Cantor enumeration:
//!   [`enumerate::binding_envs`]'s `(base, free-combo)` diagonal with
//!   lazy base pull and [`enumerate::MAX_BINDING_ENVS`],
//!   [`enumerate::diag_product`] / [`enumerate::diag_groups`],
//!   [`enumerate::LazySeq`], [`enumerate::escalate_limit`].
//! * [`terms`] — term-level pattern machinery: [`terms::match_pattern`],
//!   [`terms::instantiate_strict`] / [`terms::instantiate_lenient`],
//!   [`terms::reexpress_binding`], [`terms::compose_guards`]
//!   (guard transport), [`terms::rhs_derive_placeholders`], and
//!   [`terms::Mint`] (a rewrite plus its provenance record).
//! * [`codec`] — the JSON wire forms (`term_to_data`, binding maps).
//! * [`rulecache`] — the stored-composite round-trip:
//!   [`rulecache::RuleCache`] filesystem cache with payload-internal
//!   parent resolution and guard transport, plus the fingerprint /
//!   `cache_key` machinery.
//! * [`evidence`] — premise-anchored derivability
//!   ([`evidence::premise_rules`] transitive closure +
//!   [`evidence::premise_steps_verify`] site verification), the
//!   guarded-region sweep ([`evidence::guarded_evals`],
//!   [`evidence::guarded_truth`]), and the stored-object seam
//!   ([`evidence::rebuild_stored`], [`evidence::admit`]).
//! * [`gauntlet`] — [`gauntlet::run_gauntlet`]'s stage pipeline
//!   (reconstruct → full-data → measure → truth → novelty →
//!   typed-pay → closure → cert) driven by a [`gauntlet::GauntletLegs`]
//!   trait the domain implements.

pub mod codec;
pub mod enumerate;
pub mod evidence;
pub mod gauntlet;
pub mod rulecache;
pub mod terms;

// The substrate surface the legs work over — re-exported so a domain
// kit names `Term`/`BoundEnv`/`Rewrite`/`Derived` through one crate.
pub use handl_egraph::{
    AttrValue, BoundEnv, Derived, EGraph, Rewrite, Term, TermAttr, attr, attr_meta,
};

pub use codec::{
    CodecError, attr_from_data, attr_from_tagged, attr_to_data, dec_reexpr, enc_env, enc_reexpr,
    term_from_data, term_to_data,
};
pub use enumerate::{
    BindingEnvs, DiagGroups, GUARDED_CAP, LazySeq, MAX_BINDING_ENVS, MAX_INSTANCES,
    MAX_VIEWED_BINDINGS, binding_envs, binding_envs_capped, combos_at_sum, diag_groups,
    diag_product, escalate_limit,
};
pub use evidence::{
    CertStep, CertView, Evidence, GenericCodec, GuardSpec, GuardedRegion, ObjectCodec,
    ObjectRecord, ObjectStore, ReachRow, SiteEval, SiteOutcome, admit, guarded_evals,
    guarded_truth, premise_credit, premise_rules, premise_steps_verify, real_sites, rebuild_stored,
    region_clean, region_ok, site_outcome, synth_sites,
};
pub use gauntlet::{
    AutoCondOutcome, Gauntlet, GauntletLegs, GauntletOptions, GauntletStage, run_gauntlet,
};
pub use rulecache::{
    CACHE_VERSION, GuardRecord, HookSigs, RuleCache, RuleRecord, SynthParams, cache_key, dec_rule,
    enc_rule, ruleset_fingerprint, seed_fingerprint, sha256_hex, synthesize_rules_cached,
    uniform_hook_sig,
};
pub use terms::{
    DRV_PREFIX, Mint, ReExpr, compose_guards, free_mvs, instantiate_lenient, instantiate_strict,
    leaf_metavars, match_pattern, meta_attr_nodes, metavar_parents, pattern_metavars,
    reexpress_binding, rhs_derive_placeholders,
};
