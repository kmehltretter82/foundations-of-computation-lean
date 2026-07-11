# Compiler deletion ledger

This ledger records reusable ideas removed during the Compiler size campaign.
Deletion means “not worth maintaining in the current import and proof graph,”
not “the idea can never be useful.” Git retains the exact source.

Inspect an old file without restoring it:

```sh
git show <deleting-commit>^:<old-path>
```

When an old idea becomes relevant, recover the smallest algorithm or lemma
needed against the current canonical contract. Do not restore an entire route
or adapter stack without a current consumer, a dependency audit, and a net-LOC
comparison.

## Retired surfaces

### Legacy RawBoundary route families

- Deleting commit: `bb4f8907` (`Retire legacy RawBoundary routes`)
- Net reduction: 15,099 lines.
- Old paths: `FST/CountWindow/RawBoundary/Contracts*` and the retired
  `RawBoundary/Impl` blank-sentinel/counting/prepend/restore modules.
- Potentially reusable ideas: counted raw boundaries, marker-aware suffix
  pulling, blank-sentinel finalization, fixed-branch loops, and left-prepending
  encoded chunks.
- Why retired: the final CountWindow consumer uses the smaller uniform core;
  the old families formed parallel implementation and conversion stacks.
- Current route: `FST/CountWindow/RawBoundary/Impl/UniformCore.lean`, exposed by
  the thin `FST/CountWindow/RawBoundary.lean` facade.
- Reconsider only if: a checked consumer needs sentinel behavior that the
  uniform core cannot express. First extract the one missing invariant or
  loop; do not restore the old contract lattice wholesale.

### Orphaned fixed blank movers and materializer scratch draft

- Deleting commit: `a79351e6` (`Remove orphaned compiler modules`)
- Reduction: 401 lines.
- Old paths:
  - `Core/CommonGround/FiniteTransducers/FixedBlankMoves.lean`;
  - `Core/StructuredConstructionTargets/FuelSimulatorInputMaterializerScratch.lean`.
- Potentially reusable ideas: inductively composed fixed-distance blank moves;
  an option-cell expansion target calculation for a three-tape input embedding.
- Why retired: neither module had an importer. The scratch target had already
  been promoted into the production materializer/option-cell expander stack.
- Reconsider only if: two current machines need the same fixed-distance mover,
  or a production target equality is missing. Prefer the current primitive and
  production definitions before recovering the draft.

### Unused append-emitter variants

- Deleting commit: `98cda139` (`Remove unused append emitter variants`)
- Net reduction: 3,257 lines.
- Old paths: `OptionAppend`, `MapAppend`, `EraseAppend`,
  `AlternatingOptionAppend`, `TwoStateOptionAppend`, and
  `OptionSpecializations` under `Core/CommonGround/FiniteTransducers/`.
- Potentially reusable ideas: mapped option emission, erase-on-scan emission,
  alternating control, and a two-state specialization.
- Why retired: none had a real consumer; each repeated transition checks and
  run proofs already represented by the generated/stateful append machinery.
- Current route: `StatefulOptionAppend.lean`,
  `StatefulOptionAppendGenerated.lean`, and `AppendWord.lean`.
- Reconsider only if: a real consumer cannot be expressed as a thin
  specialization of the stateful/generated core. A promoted specialization
  must satisfy the shared-API break-even gate.

### Legacy exact selected-head routes

- Deleting commit: `fa859936` (`Retire legacy exact selected-head routes`)
- Net reduction: 1,373 lines.
- Old surface: exact-only declarations formerly in
  `Structured/HeadRoutes/ExactCleanup.lean`, `Projectors.lean`, and
  `Pipeline.lean`.
- Potentially reusable idea: upgrading selected-head cleanup and projection to
  an exact stored-tape endpoint.
- Why retired: no consumer used the over-strong exact lattice; the live route
  uses honest tape equivalence.
- Current route: the equivalence/representative contracts remaining in the
  same HeadRoutes modules.
- Reconsider only if: a checked consumer genuinely observes exact stored
  windows. Prove that one boundary directly; do not reintroduce symmetric
  exact/equivalence adapter forests.

### Unused ProjTail route and case-contract island

- Deleting commit: `83cbe6a2` (`Remove unused ProjTail contract routes`)
- Reduction: 6,953 lines and 565 declarations.
- Old paths: `ProjTail/Footprint/Contracts.lean`,
  `PrefixEraser/Contracts.lean`, the retired `ScratchBridge/Routes` and
  `ScratchBridge/Mat` route/contract modules, and
  `SelectedFootprintCompactionBridgeOutput.lean`.
- Potentially reusable ideas: nil/cons and padding-symbol case splits,
  selected-decoder/head threading, branch-specific materializer endpoints, and
  normalized-output views of footprint compaction.
- Why retired: the whole island referenced itself but had no importer,
  semantic consumer, or book-facing reference.
- Current route: canonical live ProjTail constructions imported by
  `ClosedCfg/ProjTail.lean`; derive a case theorem at the caller when needed.
- Reconsider only if: an actual endpoint cannot consume the canonical contract
  without one of these distinctions. Recover only that distinction and attach
  it to the live construction.

## Required entry for future deletions

Every deletion tranche should add:

1. deleting commit and net lines;
2. old path group and reusable algorithmic ideas;
3. evidence that it lacked a current consumer;
4. current replacement or canonical contract;
5. a concrete condition for reconsideration.

This ledger is a discovery aid, not a compatibility promise. The source at an
old commit may depend on retired APIs and should be treated as a design sketch
until it compiles against the current tree.
