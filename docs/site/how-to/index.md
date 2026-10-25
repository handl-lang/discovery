# How-to guides

Task recipes. Each assumes sibling checkouts of this repo and of the platform
repos it patches.

## Bound a discovery search

Use `binding_envs_capped` and a `Stop`-style budget so an open-ended enumeration cannot hang a run; the cap is part of the result, not a silent truncation.

## Reuse the rule cache

Key entries with `cache_key` so identical rule sets across runs hit the same slots — the key is stable by construction, which is what makes cross-run reuse sound.
