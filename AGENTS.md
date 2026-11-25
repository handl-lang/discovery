# discovery

`handl-discovery` — the pure-compute legs of catopt's
discovery/gauntlet machinery. The named Rust port of the domain-free
half of `catopt_discovery` (`oracle`, `evidence`) and
`catopt_core.rulecache`, composed over `handl-egraph`'s saturation
substrate. The port is **by contract, not by translation** — the Python
is the spec; this crate is the composable machinery any domain kit
drives.

## Layout

| path | role |
| --- | --- |
| `src/enumerate.rs` | fair enumeration skeleton (`combos_at_sum`, `diag_product`, `LazySeq`, `binding_envs`, caps) |
| `src/terms.rs` | term-level pattern machinery (`match_pattern`, `instantiate_*`, `reexpress_binding`, `compose_guards`) |
| `src/{evidence,gauntlet,rulecache,codec}.rs` | evidence model, gauntlet stage pipeline, rule cache, wire codec |
| `tests/` | enumeration determinism/caps, premise closure, rulecache round-trip, gauntlet tests |
| `scripts/dev-link.sh` | regenerates `[patch]` tables for sibling checkouts |
| `xtask/` | vendored gate crate (`fmt`, `clippy`, `test`, `doc`, `gate`) |
| `workflows/gate.yaml` | per-push gate — `handl-gates` rust campaign via bupha |

## Contract

- Spec caps: `MAX_BINDING_ENVS = 250_000`, `MAX_INSTANCES = 360`,
  `MAX_VIEWED_BINDINGS = 512`, `GUARDED_CAP = 2000`, plus the
  `escalate_limit` selective-cap policy.
- `Mint` carries provenance (`.parents`/`.guard_pats` are fields, not
  registry side-effects); `HookSigs` tags only ever *miss*, never
  wrong-hit.
- Sibling deps are git deps (`branch = "main"`); `[patch]` tables
  resolve them locally — `scripts/dev-link.sh` or
  `source ~/.cache/devin/handl_deps.env`.
- Recursive walks carry `RUST_MIN_STACK=32MiB` for test threads
  (`.cargo/config.toml`), matching the org convention.

## Verification

```bash
cargo test        # ~40 tests: enumeration, premise closure, rulecache, gauntlet
cargo fmt --check && cargo clippy --all-targets
# or: cargo xtask gate
```

<!-- myco:agent-awareness -->

## Agent awareness

- Session start / any work discussion: run `myco status --prompt`
  before proposing next steps — know the board first.
- User describes new work → offer to capture it (`myco todo add`,
  `issue new`, `proposal new`). Don't wait to be asked.
- Picking up a task: `myco resume <ID>` is the briefing.
- Wrapping up: `myco handoff <ID>` anything resumable; keep statuses
  honest (claimed → in-progress → blocked/done).

<!-- /myco:agent-awareness -->
