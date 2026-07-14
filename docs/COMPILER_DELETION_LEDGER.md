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

### Exact padded fuel-pair simulator seam

- Deleting commit: `bc7bced1` (`Retire the exact #12 simulator seam`).
- Reduction: 32 lines in the deletion checkpoint.
- Old surface: `CandidateSimulatorPaddedSpec`,
  `CandidateSimulatorPaddedConstruction`, and
  `candidateSimulatorPaddedConstruction_of_fixedDescription`.
- Potentially reusable idea: an exact retargeted simulator endpoint on the
  canonical padded output representative.
- Why retired: repaired #18 supplies the honest
  `FixedDescriptionBoundedSimulatorEquivConstruction`; it cannot imply exact
  identity of the physically padded blank window.  The exact candidate seam
  had no external declaration consumer.
- Current route: `CandidateSimulatorEquivSpec` and
  `candidateSimulatorRetargetedBlock_runsToContinuation` carry the actual halt
  tape and prove it equivalent to the padded reference.  The contract repair
  is in `009807d6`.
- Reconsider only if: a checked caller genuinely observes the exact physical
  padding.  Add normalization at that caller and prove its necessity; do not
  restore the exact adapter family merely for halt retargeting.

### Represented #18 selector diagnostic island

- Deleting commit: `49a37fad` (`Retire the represented #18 selector island`).
- Reduction: 259 Compiler lines.
- Old paths:
  `Structured/Lowering/LogicalEquivRuns.lean` and
  `ClosedCfg/TerminalCore/RunConfigEmitterCore/SelectorSpliceRepresentedRuns.lean`.
- Potentially reusable idea: structured execution preserves equal control
  states and pointwise `Tape.Equiv` logical-tape representatives.
- Why retired: the selector application was only a diagnostic theorem and had
  no importer.  It could not bridge the actual guarded physical encodings,
  because represented blank workspace becomes nonblank guarded code.
- Current route: `FieldDecomposition/RepRepair.lean` marks the surplus
  represented boundary and physically repairs it to the canonical classified
  source up to outer `Tape.Equiv` before the selector splice begins.
- Reconsider only if: a current structured consumer needs the generic
  logical-execution congruence lemma.  Recover that lemma alone; do not restore
  the obsolete represented-selector route.

### Unused #18 exact field-tape island

- Deleting commit: `7ec5adeb` (`Remove the unused #18 field-tape island`).
- Reduction: 167 Compiler lines.
- Old path: `ClosedCfg/TerminalCore/FieldTapes.lean`.
- Old surface: named exact FST source/target cell layouts and their
  normalized-output expansion lemmas.
- Why retired: the live terminal construction carries the simulator result in
  `HaltsFromTapeEquiv` currency and serializes the exact normalized word
  directly.  No declaration imported or referenced the exact field-tape
  wrapper after the equivalence route was connected.
- Current route: `RunConfigEmitterCore/GuardedEgress` emits the exact semantic
  fields, and `RunConfigEmitterEquiv.lean` carries their tape-equivalence
  result through the terminal adapter.
- Reconsider only if: a current consumer needs one of these exact FST cell
  decompositions.  Recover that lemma at the consumer, not the whole island.

### FuelSimulator fixed scratch representatives and endpoint adapters

- Deleting commit: this change (`Carry actual FuelSimulator representatives`).
- Net reduction: 136 Compiler lines in the contract-repair checkpoint.
- Old surface: `fuelSimulatorStructuredLoweredTape`; the fixed-representative
  `FuelSimulatorStructuredCanonicalEndpointEquiv*` component aliases and their
  materializer/projector adapters.
- Potentially reusable idea: an endpoint that restores logical tape 0 to the
  pristine public input and logical tape 1 to exactly `Tape.blank` before
  lowering.
- Why retired: the sole real consumer immediately projects logical tape 2 and
  observes neither working tape. Moreover, logical blank padding becomes
  nonblank guarded code, so the outer physical `Tape.Equiv` contract does not
  itself discharge exact logical scratch cleanup.
- Current route: `FuelSimulatorStructuredEquivLoweredCoreComponents` carries
  the actual tape-0, tape-1, and lowered representative families. Logical tape
  2 must still contain the exact `SimulatorLayout.initial` encoding, and the
  existing shared projector accepts the carried representatives directly.
- Reconsider only if: a checked consumer genuinely observes a restored input
  or exactly blank scratch tape. Add that cleanup to the specific construction;
  do not restore the fixed-representative component/adapter lattice wholesale.

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
- Current route: the direct marker-preserving tape-2 projector under
  `Structured/HeadRoutes/Tape2Projector/`; the later cleanup entry records the
  deletion of the remaining representative adapter lattice.
- Reconsider only if: a checked consumer genuinely observes exact stored
  windows. Prove that one boundary directly; do not reintroduce symmetric
  exact/equivalence adapter forests.

### False lossy selected-head cleanup and projector adapter lattice

- Deleting commit: this change (`Close sorry #17 projector`).
- Campaign change from pinned base `402d1269`: +3,579/-2,096, net +1,483
  Compiler lines after the checked projector implementation and deletion pass.
- Old paths: `Structured/HeadRoutes/Projectors.lean`, `Pipeline.lean`, and
  `RepresentativeProjectors.lean`; the padded representative split/adapters
  formerly in `ExactCleanup.lean` and `RepresentativeCleanup.lean`; and the
  cleanup-derived shared-projector route formerly in
  `Structured/HeadRoutes/Endpoints.lean`.
- Old surface: padded representative forward/handoff splits, equivalence and
  head-cleanup adapters, `StructuredSelectedHeadDecoderRouteConstruction`,
  segment decoder/normalizer projections, and standalone projector aliases.
- Potentially reusable ideas: nil/cons padding decomposition and reconstruction
  of an exact padded logical-tape representative after a finite scanner.
- Why retired: the selected-segment scanner has already erased the raw
  two-cell head marker. Two concrete logical tapes therefore have literally
  equal post-scanner sources but different head cells and non-equivalent
  targets. Determinism refutes both the equivalence cleanup and exact padded
  forward split. Exhaustive declaration-reference search found no external
  consumer of the cleanup-derived existence lattice.
- Current route: `Structured/HeadRoutes/ContractGuardrails.lean` preserves the
  counterexamples and proves source-class functionality. The checked
  `HeadRoutes/Tape2Projector/` stack erases the structured prefix, parses the
  retained endpoint mode/head marker, streams logical cells, and finalizes the
  requested head position. `EndpointFrontier.lean` exposes the full canonical
  guarded three-tape source and tape 2 up to `Tape.Equiv`. The concrete
  count-window caller in `ScratchBridge/Threaded.lean` now preserves its wider
  segment-normalizer contract instead of coercing it through the narrower
  shared endpoint family.
- Reconsider only if: a checked source still contains a detectable head marker
  and first proves target functionality on source-equivalence classes. Recover
  only a useful scan or reconstruction lemma; never restore the refuted
  post-scanner construction or its adapter lattice.

### False raw-head ingress and unconsumed three-tape normalizer

- Deleting commit: this change (`Retire false raw-head route`).
- Net Compiler change: +141/-1,312, net -1,171 lines.
- Old paths: `Structured/HeadRoutes/Endpoints.lean` and
  `RawHeadNormalizer.lean`; the raw-head source/target families, ingress
  adapters, and normalizer contracts formerly at the end of
  `Structured/HeadRoutes/Base.lean`.
- Potentially reusable idea: the checked three-tape table copied the logical
  cells around a retained raw head marker to tape 2 and rewound to the decoded
  head. Recover that local scan from Git history only if a live route already
  has a collision-safe ingress.
- Why retired: sources differing only by one outer represented blank are tape
  equivalent, but the requested guarded structured targets have different
  normalized outputs. Determinism therefore refutes the #16 target-family
  construction. Exhaustive declaration-reference search found that the
  derived ingress wrappers and the otherwise checked normalizer had no
  external consumer; compatibility barrels supplied only transitive imports.
- Current route: `Structured/HeadRoutes/ContractGuardrails.lean` preserves the
  historical source and target shapes and the kernel-checked impossibility
  theorem. Actual structured endpoints import the independent marker-
  preserving `HeadRoutes/Tape2Projector/EndpointFrontier.lean` directly.
- Reconsider only if: a current consumer exposes a detectable physical
  boundary and first proves its target functional on source-equivalence
  classes. Design the narrowest contract at that consumer; do not restore the
  arbitrary-prefix target family or its adapter wrappers.

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

### False selected-footprint ingress and exact-padding bridge lattice

- Deleting commit: this change (`Retire false selected-footprint bridge
  lattice`).
- Net reduction: 5,003 Compiler lines within the sorry #15 campaign.
- Old paths:
  - `ClosedCfg/ProjTail/SelectedFootprintCompaction/BridgeCore.lean` and
    `ThreeTapeBridge.lean`;
  - the internal `SelectedFootprintCompactionEndpoint.lean`,
    `SelectedFootprintCompactionPaddingSplit.lean`, and
    `SelectedFootprintCompactionPaddingOutput.lean` facades;
  - the compatibility-only `SelectedFootprintCompaction/Base.lean` barrel;
  - the payload-wide ingress construction leaf formerly in
    `Structured/Lowering/PairEncodedOptionCellCompactor/Base.lean`.
- Potentially reusable ideas: exact source/rewind endpoint views, explicit
  bit/separator/padding splits, nil/cons case decomposition, and composition
  of an ingress materializer, lowered three-tape compactor, separator focus,
  and tape-2 projector.
- Why retired: the route's contracts are inconsistent under `Tape.Equiv`.
  Payloads `[]` and `[none]` collide behind the concrete six-blank prefix but
  demand different guarded targets. Likewise, `([], [some true])` and
  `([], [none, some true])` collide at the arbitrary compactor source but
  demand different exact rewind head layouts. Exhaustive reference search
  found no consumer for the endpoint/padding facades outside this false
  lattice.
- Current route: `SelectedFootprintCompaction/ContractGuardrails.lean` records
  both counterexamples and proves target functionality for the narrower live
  `(useAccept, DovetailLayout)` family. The marker-preserving pair-parity
  eraser now retains a `[true, false]` sentinel immediately before the decoder
  footprint, and `LiveIngress/MarkerCompactor.lean` consumes that detectable
  boundary directly. `EndpointFrontier.lean` is closed by the resulting live
  construction, and the structured-prefix densifier composes the two machines.
  The seven externally used facts remain in the shape, output, and guardrail
  modules that own them.
- Algorithms kept: the completed lowered pair-encoded compactor and its
  projectable separator focus remain in
  `Structured/Lowering/PairEncodedOptionCellCompactor/Lowered.lean` and
  `ProjectableFocus.lean`; the structured tape-2 projector and adjacent
  pair-parity prefix scan also remain. A normalized-output weakening of the
  retired endpoint is sound in principle because it does not observe exact
  blank padding or head position, but its spec and adapters were also removed
  because no current declaration consumed them.
- Reconsider only if: a checked source family supplies an injective physical
  frame, such as a nonblank sentinel or explicit length/alignment field, and
  first proves target functionality on `Tape.Equiv` classes. Recover only the
  needed endpoint theorem or adapter from Git; do not restore the arbitrary
  payload/padding lattice wholesale.

The preliminary `LiveIngress/EndMarker.lean` phase was also deleted at closure.
It marked only the right boundary and therefore could not make the blank-led
left footprint boundary observable. Its replacement is the upstream
marker-preserving eraser; #17 remains the separate endpoint-only tape-2
projector and is not widened to cover this interior-separator target.

### Unreachable padded-output and run-loop branches

- Deleting commit: `deebb902` (`Remove unreachable compiler surfaces`)
- Net reduction within the audited unreachable tranche: 4,917 lines.
- Old paths: `ClosedCfg/RunLoop/SourceShape.lean`, the padded projection
  `ForwardOutput`/`Output`/`OutputHybrid` and quoter-output chain,
  `Simulator/PaddedEmitter/RunLoop.lean`, `BoundedLayoutRunner/Emitter.lean`,
  `StructuredInputMaterializerFrontier.lean`, `SingletonRefreshRuns.lean`, and
  `Structured/ProjectionContracts.lean`.
- Potentially reusable ideas: output-only padded projection, a simulator
  run-loop source-shape wrapper, singleton-refresh execution lemmas, and
  indexed structured projection contracts.
- Why retired: the dependency-closed branches had no tracked importer; the old
  padded-emitter run-loop was the documented circular/decoy route for sorry
  #18, not an independent implementation.
- Current route: the public padded-emitter equivalence scaffold through
  `RunConfigEmitterEquiv` and guarded egress, focused structured lowering
  modules, and consumer-local honest projection contracts.
- Reconsider only if: a new checked consumer needs one specific output or
  refresh theorem. Re-derive it over the live construction and verify it does
  not recreate the #18 circular dependency.

### Unconsumed shared execution APIs

- Deleting commit: `deebb902` (`Remove unreachable compiler surfaces`)
- Net reduction: 386 lines including their barrel imports.
- Old paths: `Structured/Lowering/TypedStateTableExecution.lean` and
  `Core/CommonGround/FiniteTransducers/StructuredRuns.lean`.
- Potentially reusable ideas: generic typed-table and structured-description
  `Leads` relations with reflexivity, transitivity, and `runConfig` conversion.
- Why retired: exhaustive reference search found no real consumer. Migrating
  the four local relations would retain their machine-specific step adapters
  and was not net-negative.
- Current route: the small local execution relations beside each machine.
- Reconsider only if: two current construction families are ready to migrate
  in the same change and deleted local code covers the shared layer plus all
  adapters.

### BoolRawInput contract/endpoint adapter island

- Deleting commit: `deebb902` (`Remove unreachable compiler surfaces`)
- Net reduction: 1,500 lines and 115 declarations.
- Old paths: `FST/BoolRawInput/Contracts.lean` and `EndpointRoute.lean`.
- Potentially reusable ideas: materializer route conversions and endpoint
  adapters for raw Boolean-word input decoding.
- Why retired: both namespaces were facade-only and had no source, book, or
  semantic consumer.
- Current route: the live BoolRawInput `Endpoint`, `EndpointContracts`, and
  `Output` modules used by ProjTail.
- Reconsider only if: a caller needs a statement not derivable directly from
  those three live modules; add only the caller-facing theorem.

### Facade-only materializer and CountWindow route bundles

- Deleting commit: `5f557820` (`Remove unused materializer contract bundles`)
- Net reduction: 1,670 lines.
- Old paths: `FiniteTransducers/StructuredInputMaterializerContracts.lean` and
  `FST/CountWindow/Contracts.lean`.
- Potentially reusable ideas: exact/output/equivalence materializer route
  records, endpoint/scan views of CountWindow, construction-chain bundles, and
  exact-live-tail impossibility packaging.
- Why retired: both modules were imported only by the broad finite-transducer
  facade; every declaration reference was internal to its own module. The live
  materializer, CountWindow construction, and downstream raw-source bridge use
  the canonical specs directly.
- Current route: `StructuredInputMaterializer.lean`, its focused endpoint
  modules, and `FST/CountWindow.lean`.
- Reconsider only if: a real caller needs multiple fields of one route record.
  Prefer a direct theorem over recreating symmetric route/bundle conversions.

### Superseded Dispatcher reader layout

- Deleting commit: `123eb193` (`Remove obsolete dispatcher reader scaffolds`)
- Reduction: 292 lines and 37 declarations.
- Old surface: the single-copy tape-0/1/2 reader offsets and limits, partial
  read scratch banks, retargeted reader starts, blank-bounce jump descriptions,
  separation bounds, run wrappers, and target-order convenience lemmas formerly
  in `Structured/Lowering/Dispatcher.lean`.
- Why retired: no qualified, open-namespace, or reopened-namespace consumer
  existed. DispatcherAssembly and StaticMachine use the retained compact
  `ready`/`afterRead` state and target API instead.
- Current route: the compact definitions in `Dispatcher.lean` and the checked
  implementation under `DispatcherAssembly/`.
- Reconsider only if: a new physical dispatcher deliberately chooses the old
  contiguous scratch-bank layout. Compare it first against the compact live
  layout and its 3.28-second `SelectedRuns.lean` benchmark.

### Unused controller invocation and scalar search-driver route bundles

- Deleting commit: `59985a4d` (`Shrink finite scaffold contract facades`).
- Net reduction: 1,371 lines.
- Old surface: route structures, construction bundles, finite-leaf wrappers,
  and public `_route` aliases formerly in
  `ControllerInvocationContracts.lean` and
  `ControllerSearchDriverContracts.lean`.
- Potentially reusable ideas: framed/protected invocation projections, scalar
  fuel-search adapters, finite stage-loop sequencing records, and aggregate
  finite-route witnesses.
- Why retired: exhaustive declaration-reference search found no consumer
  outside the two files. The finite-leaf aliases merely repackaged canonical
  scaffold theorems and were the only sorry-dependent declarations in the
  modules.
- Current route: `ControllerInvocationContracts.lean` remains a thin #6/#7
  acceptance boundary over the canonical invocation contracts; the search
  module retains only the honest Boolean-indexed #12 family consumer.
- Reconsider only if: a checked consumer needs several fields that are not
  already available from the canonical construction or indexed family. Add
  only that consumer-facing record; do not restore the scalar/bundle lattice.

### Superseded #18 input-decomposition and metadata-reparse routes

- Deleting commit: `11514cfd` (`Close metadata prefix run obligation`).
- Net reduction within the checkpoint: zero; 473 lines of exact lag/run proof
  replaced 473 lines of obsolete parser, contract, and pipeline code.
- Old surface: `InputDecompositionPipeline.lean`, the reusable raw Boolean
  decoder detour in `FieldDecomposition.lean`, the generic unclassified loop
  target/specification, and MetadataPrefix's second input/stage/state reparse.
- Potentially reusable ideas: a standalone Boolean-field decoder ingress and a
  generic unclassified three-tape loop target.
- Why retired: the exact D-specific classified boundary is the real #18
  consumer. The old decoder required incompatible padding adapters, and the
  metadata prefix reparsed fields that the following configuration phase must
  parse again.
- Current route: the four-cell-lag metadata copier returns tape 0 directly to
  the complete layout header; the next phase owns the single forward prefix
  and configuration scan. `RunConfigEmitterCore.lean` imports the live input
  materializer directly.
- Reconsider only if: a second checked consumer genuinely needs the old
  unclassified target or standalone decoder boundary. Recover a focused
  theorem over that consumer's exact tape shape, not the retired pipeline.

### FuelOutput-local typed-run and delayed-emitter duplicates

- Deleting commit: `2300dad7` (`Close the FuelSimulator structured core`).
- Net reduction in the three FuelOutput files: 85 lines; their 127 deleted
  lines were replaced by 42 target-specific adapter lines.
- Old surface: local delayed-emitter action matches, full emission-tape update
  and flush proofs, a private `Leads` reflexive/transitive/run extraction
  implementation, and duplicated explicit tape-window action lemmas.
- Potentially reusable ideas: all behavior is retained, not discarded, in
  `Structured/Lowering/DelayedLeftEmitter.lean` and
  `Structured/Lowering/TypedStateRuns.lean`.
- Why retired: FuelSimulator became the second current construction family for
  both abstractions. Keeping the FuelOutput copies would make later fixes and
  proof compression diverge across two live finite-machine stacks.
- Current route: FuelOutput keeps its stable target-facing aliases while both
  FuelOutput and FuelSimulator use the shared delayed-emission and typed-run
  algebra.
- Reconsider only if: a checked consumer needs a genuinely target-specific
  invariant absent from the shared theorem. Add that invariant as a thin local
  theorem; do not restore the duplicate action or reachability implementations.

### Superseded #18 terminal route and endpoint-shape lattice

- Deleting commit: `8a01ac7b` (`Close the configuration materializer`).
- Reduction: 2,159 Compiler lines; the same checkpoint added the concrete
  `ConfigTapeAndHit` execution proof, for a net increase of 134 lines.
- Old surface: the exact/output/equivalence route bundles in
  `ClosedCfg/TerminalCore/Routes.lean`, the aggregate endpoint-shape record,
  and the unconsumed tape-shape/normalized-output adapters in
  `ClosedCfg/TerminalCore/Core.lean`.
- Potentially reusable ideas: right-end-left route composition, normalized
  terminal endpoint views, and aggregate scratch/target shape packaging.
- Why retired: declaration-level reference searches found no consumer outside
  the retired route module. The live padded-emitter and controller consumers
  compile through `RunConfigEmitter` and the retained right-scratch surfaces.
- Current route: the concrete `ConfigTapeAndHit` typed-table run carries the
  actual represented logical tapes, proves their component equivalence, and
  lowers their exact guarded representation. At this checkpoint `Routes.lean`
  remained temporarily; it was later retired in `ed1bc3a6` after
  equivalence-consumer migration.
- Reconsider only if: a checked consumer needs one specific endpoint adapter.
  Recover that theorem from `8a01ac7b^`, state it in the consumer's honest
  exact/equivalence currency, and do not restore the aggregate route lattice.

### Retired #18 exact post-scan, scratch, and FST facade

- Deleting commit: `ed1bc3a6` (`Retire the exact #18 facade`).
- Net reduction: 820 Compiler lines (`+6/-826`).
- Old paths: `ClosedCfg/TerminalCore.lean`,
  `TerminalCore/Adapters.lean`, `Contracts.lean`, `Routes.lean`, the broad
  `RunConfigEmitterCore.lean` aggregator,
  `RunConfigEmitterTheory/Output.lean`, and
  `Simulator/PaddedEmitter/Terminal.lean`.
- Old surface: the exact post-right-end-left-to-scratch construction (the last
  direct #18 `sorry`), its exact terminal-source and right-shifted-source
  descendants, the scratch/right-scratch/FST adapter chain, and the exact
  padded-emitter terminal wrapper.  Unconsumed right-end-left cell and
  normalized-output diagnostics were removed from `RunConfigEmitter.lean` at
  the same checkpoint.
- Potentially reusable idea: exact finite scans from the restored layout word
  through a right-end-left handoff, plus conversions among scratch-padded and
  FST endpoint presentations.
- Why retired: exact conversion to one canonical scratch tape is stronger than
  every current consumer needs and conflicts with the represented-window
  contract repaired earlier in #18.  After the public migration in `206a31b2`,
  declaration and import searches found no consumer of the exact facade;
  `RunConfigEmitterEquiv.lean`, the public padded emitter, and the #12/#14
  consumers compiled with warnings as errors through the equivalence route.
- Current route: `RunConfigEmitter.lean` retains only the checked
  right-end-left scan and
  `fixedDescriptionBoundedSimulatorPaddedEmitterBodyEquivConstruction_of_fullPipeline_configRunner`.
  `runConfigEmitterFullPipelineConstruction_configRunner` and
  `fixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreEquivConstruction_configRunner`
  feed the stable
  `fixedDescriptionBoundedSimulatorEquivConstruction_scaffold_configRunner`
  theorem directly. Commit `d59ece33` removed the redundant premise-free
  construction alias so that this scaffold is the sole public acceptance
  surface with that type. The
  represented-boundary impossibility facts in
  `FieldDecomposition/RepBoundary.lean` remain as guardrails.
- Reconsider only if: a checked caller demonstrably observes the exact
  physical padding or exact FST endpoint, and first proves both context-length
  feasibility and target functionality on its source family.  Recover the
  smallest required scan or shape lemma from `ed1bc3a6^`; do not restore the
  exact construction lattice, compatibility aggregators, or terminal wrapper.

### Superseded #18 standalone selector execution lattice

- Deleting commit: `0e5733b9` (`Splice the selector into the dispatcher`).
- Net reduction at the checkpoint: 43 Compiler lines; 365 deleted standalone
  selector-run lines were replaced by the 317-line combined table and its
  import wiring.
- Old surface: the exact standalone `SelectorIngress` execution lattice whose
  `.done` states were terminal/stuck endpoints, plus its duplicated Boolean,
  natural-number, scan, restoration, and layout composition proofs.
- Potentially reusable idea: exact restoration of the selector field and
  scratch-marker window after parsing the classified-state selector.
- Why retired: the only current consumer must continue immediately from the
  selected `.done tag` state into the matching dispatcher branch. Treating
  that boundary as a standalone halt forced a second execution lattice and an
  adapter at the real consumer boundary.
- Current route: `SelectorSplice` preserves all existing dispatcher/closeout
  state identifiers, assigns the selector a disjoint state range, and redirects
  each selector completion row directly to `.base (.dispatch tag)`. Its exact
  fixed-start execution and lowered tape-equivalence proof are maintained as
  one integrated route.
- Reconsider only if: a checked consumer genuinely needs the selector to halt
  after restoring its source tape. Recover only the restoration contract; do
  not duplicate the combined selector-to-dispatcher execution proof.

### Refuted #18 all-equivalent-input exact-output pipeline

- Deleting commit: `d7c72a5b` (`Repair the guarded egress contract`).
- Replacement size: 72 lines deleted and 110 added across the contract,
  semantic egress, finite-realization boundary, and campaign manifest. The
  added lines include the generic kernel-checked impossibility theorem.
- Old surface: `EquivInputExactOutputSpec` canonical/target-functionality
  adapters and the first-equivalent/second-exact sequential composition
  lattice.
- Potentially reusable idea: exact target functionality for canonical source
  indices remains useful as a semantic collision audit, but it cannot justify
  a machine contract quantified over every padding-equivalent physical input.
- Why retired: any source has equivalent representatives with arbitrarily
  large far-edge blank context. Tape context length cannot decrease during a
  machine run, so no fixed exact target is reachable from all of them.
- Current route: the guarded egress uses `EquivInputEquivOutputSpec`. It fixes
  the exact normalized output and head-relative layout while retaining
  harmless represented padding, and composes with an upstream equivalence run.
- Reconsider only if: a caller supplies a bounded, explicitly indexed padding
  family whose context length is proved no larger than its exact target. Do
  not restore the unrestricted equivalent-input/exact-output quantifier.

### Superseded #18 nested structured tape serializer prototype

- Deleting commit: `20eaa3c4` (`Quote guarded egress pairs`).
- Reduction: 413 Compiler lines removed. The replacement adds the checked
  physical-source adapter and pair rewriter while keeping the frozen #18
  historical-debt ceiling unchanged.
- Old surface: `GuardedEgress/ExactTapeSerializer.lean`, especially the
  three-logical-tape left-length emitter over a tape 0 that already contained
  the raw logical-tape representation.
- Potentially reusable idea: scan the pair-coded left window to the preserved
  head marker and emit one unary tick per stored left cell.
- Why retired: the real post-dispatch source is itself the guarded physical
  lowering of the three logical tapes. Running the old structured component
  there would decode physical tape 0 as a logical tape and therefore require a
  second, nested encoding that no current producer supplies.
- Current route: `GuardedEgress/RawPairQuoter.lean` starts directly on the real
  outer separator, reuses the checked CountWindow raw-boundary emitter, and
  retains the `11` marker as a distinct quoted pair for later exact tape-field
  assembly.
- Reconsider only if: a checked producer genuinely supplies the nested source
  shape expected by the old component. Recover only its left-length table and
  exact run proof; do not restore the unused wrapper module.

### Superseded #18 original-source navigation and scan lattice

- Deleting commit: `3719336d` (`Decode guarded egress pairs`).
- Reduction: 380 lines removed from `GuardedEgress/FiniteRealization.lean`;
  the same checkpoint added the shared padded-decoder API, exact guarded
  pair semantics, and the 201-line physical decoder seam, for net growth of
  149 lines.
- Old surface: separate tape-0 entry/scan, tape-1 separator seek, tape-2
  seek/scan, raw-payload shape, and identity-handoff adapters over the original
  guarded source.
- Potentially reusable idea: non-mutating navigation to one selected guarded
  segment before any source transformation.
- Why retired: the live egress starts with a destructive tape-0 chunk expansion.
  The old tape-1/tape-2 endpoints therefore cannot compose after the current
  first phase, and no declaration outside `FiniteRealization.lean` referenced
  them. Keeping a second pre-transformation route would obscure which physical
  representative owns the final metadata assembly.
- Current route: `RawPairQuoter.lean` carries the untouched tape-1/tape-2 suffix
  through the tape-0 rewrite, and `RawPairDecoder.lean` reaches the shared
  padded decoder endpoint without crossing that suffix.
- Reconsider only if: a checked consumer must parse tape 2 before mutating tape
  0 and also provides an explicit storage/return path for the parsed fields.
  Recover only the required selected-segment seek, not the full scan/identity
  lattice.

### Superseded #18 finite-realization wrapper

- Deleting commit: `023d63dc` (`Split the guarded head marker`).
- Final alias cleanup: `b00c26a6` (`Remove the stale #18 realization wrapper`)
  deleted the last definitionally duplicate `FiniteRealizationConstruction`
  alias, its identity conversion theorem, and the unreferenced production
  witness after exhaustive declaration-reference checks found no consumer.
- Reduction: the 152-line `GuardedEgress/FiniteRealization.lean` wrapper and a
  14-line unused pair-fold theorem were removed. The same checkpoint added the
  160-line exact marker scanner and direct suffix ownership, for zero net
  Compiler growth.
- Old surface: a second semantic `Spec`/`Construction`, canonical-source
  wrappers, round-trip adapters to `GuardedEgress.Spec`, and a leaf alias whose
  construction proposition was definitionally the parent construction.
- Potentially reusable idea: reducing an all-equivalent-input/equivalent-output
  contract to canonical-source runs by standard run-equivalence transport.
- Why retired: no external declaration referenced the wrapper lattice. The
  actual repaired contract already lives in `GuardedEgress.lean`, while the
  physical implementation now proceeds through `RawPairQuoter`,
  `RawPairDecoder`, and `RawPairMarker`.
- Current route: `RawPairQuoter.suffixCells` owns the exact carried tape-1/tape-2
  suffix, and `RawPairMarker.markerScanDescription_haltsFromTape` proves the
  first post-rewrite semantic split.
- Reconsider only if: final composition needs a canonical-source adapter not
  already supplied by `PipelineContracts`. Restore one theorem directly over
  `GuardedEgress.Spec`; do not recreate the duplicate local contract lattice.

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
