# Explanation

## Why this crate exists

Discovery (proposing rewrite sites) is where research throughput comes from,
and it must be reproducible: the same seeds must yield the same candidates. The
pure-compute half is therefore split from the domain half (`catopt`) and ported by
contract, so the search semantics stay identical to the spec while the substrate
stays reusable.

## Where it sits

This crate belongs to the `engine-*` family. Plugins, kits and hosts reach it
through the kit's operation slot, so the engine can be swapped without touching a
language definition.

See the [reference](/discovery/reference/) for the API and the
[how-to guides](/discovery/how-to/) for tasks.
