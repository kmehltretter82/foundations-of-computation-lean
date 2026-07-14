# Compiler growth campaigns

Every active Compiler construction campaign must pin its original Git base and
record the one frontier it is intended to close.  Small intermediate commits do
not reset that base.

A campaign manifest is a JSON file with these required fields:

```json
{
  "name": "sorry-N",
  "base_commit": "full Git commit hash",
  "frontier": "Fully.Qualified.Lean.Declaration",
  "paths": ["FoC/Computability/Compiler/Owned/Subtree"],
  "focused_checks": ["lake env lean FoC/Path/To/Frontier.lean"],
  "required_axiom_clean": ["Fully.Qualified.Consumer"],
  "allow_net_growth": 1500
}
```

Run the cumulative check from `formal/`:

```sh
scripts/check-compiler-growth.py \
  --baseline scripts/compiler-growth-baseline.json \
  --unreachable-allowlist scripts/compiler-unreachable-allowlist.json \
  --campaign compiler-campaigns/sorry-N.json
```

The initial finite-machine allowance is normally 1,500 lines.  A reviewed
campaign may rise as high as 5,000 lines once its exact in-scope leaf is
axiom-clean, its current consumer compiles, and the manifest records an
`architecture_review` reason plus the full Git commit against which that review
was made.  The allowance is a ceiling, not a target.  The sum of ordinary
outstanding loans may not exceed 10,000 lines. The reviewed global Compiler
growth allowance is likewise 10,000 lines above the pinned baseline.

Pre-policy work that already exceeds the circuit breakers must not reset its
starting commit.  Record it honestly with:

```json
{
  "historical_debt": true,
  "historical_debt_reason": "Why this pre-existing debt is being frozen"
}
```

Such a manifest grandfathers only the measured ceiling in
`allow_net_growth`; it does not authorize further growth.  Ratchet that ceiling
down after each deletion pass.

The checker also requires campaign paths to remain under
`FoC/Computability/Compiler`, a full 40-digit starting commit, nonempty focused
checks, and named declarations that must become axiom-clean.

At closure, delete obsolete routes, record the final net change, and either
repay the loan through cleanup or explicitly review the permanent baseline
increase before removing the campaign manifest.

Baseline writes require an explicit review reason and record the Git commit
against which the measurements were taken:

```sh
scripts/check-compiler-growth.py \
  --write-baseline scripts/compiler-growth-baseline.json \
  --approve-baseline-update "Post-cleanup Compiler freeze"
```

The proof-hygiene workflow also exports the reachable Compiler declaration
environment and rejects new exact duplicate theorem-type groups relative to
`scripts/compiler-duplicate-types-baseline.json`. Generated CSV and smell
reports remain review artifacts under `.lake/`; they are not committed.
