# discovery

The pure-compute legs of catopt's discovery/gauntlet machinery.

## What it is

`handl-discovery` is the domain-free half of `catopt_discovery` (`oracle`,
`evidence`) and `catopt_core.rulecache`, composed over `handl-egraph`'s saturation
substrate. The port is **by contract, not by translation**: the Python is the
spec, this is the composable Rust version.

## Modules
- `oracle` — site proposals, admission and scoring
- `evidence` — attribute/tagged-value bridges and guard composition
- `rulecache` — cache keys and memoised candidate enumeration


## Start here

- **Reference** — [public API](/discovery/reference/)
- **How-to** — [task recipes](/discovery/how-to/)
- **Explanation** — [design and rationale](/discovery/explanation/)

No tutorials: this repo is a building block used from Rust. End-to-end
walkthroughs live with the product that composes it — see the
[Handl platform](/handl/).
