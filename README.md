# discovery

`handl-discovery` — the pure-compute legs of catopt's
discovery/gauntlet machinery. The named Rust port of the domain-free
half of `catopt_discovery` (`oracle`, `evidence`) and
`catopt_core.rulecache`, composed over
[`handl-egraph`](https://github.com/handl-lang/egraph)'s saturation
substrate. The port is **by contract, not by translation** — the
Python is the spec; this crate is the composable machinery any
domain kit drives.

Sibling-repo deps are git dependencies (`branch = "main"`); the
`[patch]` tables (regenerate with `scripts/dev-link.sh`) resolve them
from sibling checkouts for local development — or
`source ~/.cache/devin/handl_deps.env` for the git-insteadOf map.

## What ships

- **`enumerate`** — the fair enumeration skeleton under
  `oracle._binding_envs`: `combos_at_sum` / `diag_product` (Cantor
  index-sum order — a cap truncates a *corner* of the product space,
  not a dimension), `LazySeq`, `diag_groups`, `binding_envs` (the
  `(base, free-combo)` diagonal with lazy base pull), and the spec's
  caps: `MAX_BINDING_ENVS = 250_000`, `MAX_INSTANCES = 360`,
  `MAX_VIEWED_BINDINGS = 512`, `GUARDED_CAP = 2000`, plus the
  `escalate_limit` selective-cap policy.
- **`terms`** — term-level pattern machinery: `match_pattern`
  (`_term_match`), `instantiate_strict`/`instantiate_lenient`
  (`instantiate_pattern`/`_term_instantiate`), `reexpress_binding`,
  `compose_guards` (`meta._compose_guards` — guard transport),
  `rhs_derive_placeholders`, pattern introspection
  (`leaf_metavars`/`metavar_parents`/`free_mvs` with the viewish
  alphabet injected), and `Mint` — a `Rewrite` plus its
  `.parents`/`.guard_pats` provenance (the spec's dynamically-set
  attrs, made explicit).
- **`codec`** — the JSON wire forms: `term_to_data`/`term_from_data`,
  `enc_reexpr`/`dec_reexpr` (the `[key, {"t"|"a": …}]` binding
  pairs), `attr_to_data`/`attr_from_data`, and the
  `AttrValue`↔`TaggedValue` bridge.
- **`rulecache`** — the stored-composite round-trip: `RuleCache`
  filesystem cache (`store`/`load`/`path`), `enc_rule`/`dec_rule`
  with **payload-internal parent resolution** (records decode in
  stored order and join the resolver — a fixpoint mint's `syn_*`
  parents resolve inside the payload) and **guard transport**
  (hooks never serialize; `compose_guards` re-runs over named
  parents), plus `cache_key`/`ruleset_fingerprint`/
  `seed_fingerprint`/`SynthParams`/`synthesize_rules_cached`.
- **`evidence`** — premise-anchored derivability and the guarded
  sweep: `premise_rules` (transitive premise closure — a member that
  resolves short of full strength empties the whole closure),
  `premise_steps_verify`/`premise_credit` (the anti-gaming bar:
  every non-axiom step the derivation *invoked* must site-verify
  `equal`), `site_outcome`/`guarded_evals`/`synth_sites`/
  `guarded_truth`/`real_sites` (the guarded-region sweep with
  selective-cap escalation), `region_clean`/`region_ok`, the
  `ObjectRecord`/`ObjectStore`/`ObjectCodec` seam, and
  `rebuild_stored`/`admit` (stored record → live rule with guard
  transport). `Evidence`/`ReachRow`/`CertView`/`CertStep` are the
  measured-record shapes the gates read.
- **`gauntlet`** — `run_gauntlet`'s stage pipeline as a
  trait-driven skeleton: reconstruct → full-data → measure → truth →
  novelty → typed-pay → closure → cert, stop-on-failure, with the
  `auto_cond` conditional→guarded retry plumbed through
  `GauntletLegs::auto_cond`.

## The boundary — pure compute vs. pluggable backend legs

The crate ships **machinery, not domain**. The Python legs that stay
in the domain (torch truth legs, `TorchSource`-bound fixtures, the
`dag_cost` fold-policy alphabets, `dspec_synth` backend eval,
`JOINT_SHAPES`/`FOLD_OPS`-style data tables) arrive here as *traits
and data*:

| Python leg | Injected as |
|---|---|
| `eval_instance` fp64 numeric oracle | `SiteEval` closure (`&Term,&Term -> SiteOutcome`) |
| `oracle` leaf banks / attr domains / `JOINT_SHAPES` | the `(base, combos)` stream `binding_envs` consumes |
| `laws.serialize.object_from_data` | `ObjectCodec::bare_rule` |
| sqlite `lemmas` store | `ObjectStore` (`record_by_name`/`record_by_key`) |
| `pipeline.measure` (corpus, census, sink, cost_fn) | `GauntletLegs::measure` |
| `shape_proposal.real_matches` + sweep sites | `GauntletLegs::guarded_truth` (`real_sites`/`synth_sites` helpers provided) |
| `lemma_cert.materialize` / strict replay | `GauntletLegs::stored_certificate` |
| `object_synthesis.auto_cond_object` | `GauntletLegs::auto_cond` |
| `meta.synthesize_rules` (the search engine) | the `synthesize` closure of `synthesize_rules_cached` |
| `inspect.getsource` hook signatures | `HookSigs` — a domain tag (rule-bank version) |

A domain wires its data like this:

```rust
use handl_discovery::{binding_envs, diag_product, run_gauntlet, GauntletLegs, GauntletOptions};

// A domain's synthesized binding domain: leaf banks + attr domains
// as data, composed through the crate's Cantor machinery.
let bases = domain_viewed_bindings().map(|base| {
    let combos = diag_product(domain_free_lists(&base));
    (base, combos)
});
for (base, combo) in binding_envs(bases) {
    // each (base, combo) pair is one binding env — merge into the
    // domain's env type and evaluate.
}

// The gauntlet: implement GauntletLegs over the domain's store,
// corpus, and backend legs — the skeleton drives the gates.
let report = run_gauntlet(&mut my_domain_legs, alpha_key, &GauntletOptions::default());
assert!(report.stages.iter().all(|s| s.passed) == report.usable);
```

The Python arm in `graphopt` becomes a **thin shell**: it keeps
the torch corpus, the `TermCase` probe fixtures, the backend eval,
and the law bank — and calls this crate for enumeration, premise
closure, the rulecache round-trip, and the gate order.

## Spec divergences (named, deliberate)

- **Typed namespaces.** The spec's `"$attr:"`-mangled dict keys are
  `BoundEnv.terms`/`BoundEnv.attrs` split maps; a re-expression spec's
  attr entries are `TermAttr::Lit`/`Meta` — strictly more honest than
  Python's str-is-both ambiguity.
- **`Derived::Class` is un-reexpressible.** A parent `derive`
  emitting a class-id extra cannot join a term-level `BoundEnv`; a
  pat2 reference to it vetoes the composition where the spec would
  inject the raw eid as a term. Conservative — never a wrong admit.
- **Structural dedup.** `real_sites`/`synth_sites` dedup by term
  equality where the spec dedups by `id()` — identical semantics for
  the evaluable-site count.
- **Panic = exception.** Hooks wrapped in `catch_unwind`: a panicking
  guard is the spec's `guard-err`/veto, not a crash.
- **Hook signatures are injected.** No `inspect.getsource` — domains
  supply `HookSigs` tags; an unstable tag only ever *misses*, never
  wrong-hits.
- **`Mint` carries provenance.** `.parents`/`.guard_pats` are fields,
  not dynamically-set attrs — no `SYNTH_PARENTS` registry side-effect.

## Verification

```sh
cargo test        # enumeration determinism + cap, premise closure +
                  # site-verify anti-gaming, rulecache round-trip,
                  # gauntlet stage pipeline — 40 tests
cargo fmt --check
cargo clippy --all-targets
```

Recursive walks carry `RUST_MIN_STACK=32MiB` for test threads
(`.cargo/config.toml`), matching the org convention.

## Documentation

Published site (Diátaxis): <https://handl-lang.github.io/docs/discovery/>

- [Reference](https://handl-lang.github.io/docs/discovery/reference/) — public API surface
- [How-to](https://handl-lang.github.io/docs/discovery/how-to/) — task recipes
- [Explanation](https://handl-lang.github.io/docs/discovery/explanation/) — design and rationale

Decision records live on the `project` branch under `project/adrs/`.
