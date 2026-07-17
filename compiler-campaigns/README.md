# Compiler growth campaigns

## Retired completed campaigns (permanent growth)

The governance restoration on 2026-07-17 rechecked the five manifests that
were present immediately before the control files were deleted. The Section
5.2 Boolean-output-acceptor campaign subsequently closed its finite frontier.
Every allowance below is ratcheted to its exact measured net:

| Manifest | Net growth from pinned base | Allowance |
|---|---:|---:|
| `sorry-1.json` | +20,113 | +20,113 frozen |
| `sorry-2.json` | +33 | +33 frozen |
| `sorry-3.json` | +14,561 | +14,561 frozen |
| `sorry-4.json` | +54,487 | +54,487 frozen |
| `sorry-5.json` | +18,391 | +18,391 frozen |
| `chapter05-section02-bool-output-acceptor.json` | +446 | +446 frozen |

Their focused-check lists were reconciled with the current tree; entries for
facades deleted as unreachable in `5bf45c02` were removed.

The separate permanent-growth review anticipated by the restoration was
performed later on 2026-07-17, per the Section 5.3 improvement-plan budget
decision (`LEAN_CHAPTER5_SECTION3_IMPROVEMENT_PLAN.md`, Section 6a) approved
by the project owner. All six manifests are now marked `historical_debt`:
their 108,031 lines of growth are accepted as permanent Compiler content and
no longer count toward the 120,000-line aggregate outstanding-loan allowance.
The ratcheted exact ceilings remain in force as regression guards, so the
closed routes still may not grow, and the manifests stay in place so the
pinned bases keep being checked. This review does not reset the 347,066-line
baseline; the independent global raw-growth ceiling is adjusted separately in
`scripts/compiler-growth-baseline.json` with its own review provenance.

All 23 unique focused commands belonging to the five restored manifests passed
during the 2026-07-17 restoration audit. The three focused checks for the
Boolean-output campaign also pass. The required frontier and consumer
declarations were rechecked with `#print axioms`; they depend only on `propext`,
`Classical.choice`, and `Quot.sound` (with some requiring a subset), and not on
the sorry axiom.

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
  "allow_net_growth": 10000
}
```

Run the cumulative check from `formal/`:

```sh
scripts/check-compiler-growth.py \
  --baseline scripts/compiler-growth-baseline.json \
  --unreachable-allowlist scripts/compiler-unreachable-allowlist.json \
  --campaign compiler-campaigns/sorry-N.json
```

The ordinary finite-machine allowance is 10,000 lines per sorry campaign. The
manifest must request its cumulative allowance explicitly; 10,000 is a ceiling,
not a target or an automatic baseline increase. The sum of ordinary outstanding
loans may not exceed 120,000 lines. Independently, raw Compiler growth may not
exceed 150,000 lines above the pinned baseline. Per-campaign allowances, the
aggregate loan cap, and the global raw-growth allowance are separate,
non-additive circuit breakers. Existing manifests keep their recorded lower
allowances unless they are deliberately reviewed.

A specifically reviewed campaign may exceed the ordinary 10,000-line per-sorry
ceiling only through a narrow, explicit review recorded in that campaign
manifest:

```json
{
  "allow_net_growth": 13000,
  "reviewed_growth_exception": {
    "reason": "Why this specific campaign needs the larger reviewed ceiling",
    "recorded_against": "full 40-digit ancestor commit hash"
  }
}
```

The checker requires a nonempty reason and a recorded commit that exists and is
an ancestor of the current HEAD. A reviewed growth exception conflicts with
`historical_debt`: a campaign must use one policy mechanism or the other. The
exception changes only that campaign's exact allowance. It does not reset the
pinned campaign base, update or reset the global baseline, or waive the
aggregate outstanding-loan cap or independent global raw-growth cap. The full
exception allowance still counts toward both outstanding-loan and global-growth
logic.

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

The proof-hygiene workflow also exports the Compiler facade declaration
environment and rejects new exact duplicate theorem-type groups relative to
`scripts/compiler-duplicate-types-baseline.json`. Generated CSV and smell
reports remain review artifacts under `.lake/`; they are not committed.
