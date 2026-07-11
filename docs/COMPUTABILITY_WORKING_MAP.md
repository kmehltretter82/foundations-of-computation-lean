# Computability Working Map

This is a short navigation aid for Lean work in `FoC/Computability/`.  It is
not an API inventory.  Prefer source docstrings, `rg`, and Lean search/hover
for exact theorem statements.

## Search First

Run from `formal/`.

```sh
rg -n "def NAME|theorem NAME|structure NAME|abbrev NAME" FoC/Computability
rg -n "HaltsFromTapeEquiv|ClosedFromTapeEquiv|SubroutineReady" FoC/Computability/Compiler
rg -n "seqSubroutine|canonicalPrimitiveSeq|runConfig_eq_halt" FoC/Computability/Compiler
rg -n "structured3InputMaterializer|encodedGuardedStructured3Tapes" FoC/Computability/Compiler
rg -n "transition_deterministic_of_all|runConfig_add|Computes|Step" FoC/Computability/Compiler
```

When a file is large, first inspect imports, namespace, and module docstring:

```sh
sed -n '1,80p' FoC/Computability/Compiler/Path/File.lean
rg -n "^/-!|^def |^structure |^theorem |^abbrev " FoC/Computability/Compiler/Path/File.lean
```

## Core Execution Semantics

- `FoC/Computability/Tape.lean`, `TapeLemmas.lean`: tape shape, movement,
  equivalence, normalized output.
- `FoC/Computability/TuringMachine.lean`: deterministic TM semantics.
- `FoC/Computability/Compiler/DescriptionExecution.lean`: `MachineDescription`,
  `HaltsFromTape`, `HaltsFromTapeEquiv`, `ClosedFromTapeEquiv`,
  `runConfig_eq_halt_of_haltsFromTape`, context-length facts.
- `FoC/Computability/Compiler/SeqSubroutineSemantics.lean`: exact sequencing
  semantics and inversion, especially
  `seqSubroutine_haltsFromTape_closed_exists_mid`.
- `FoC/Computability/Compiler/Core/CommonGround/SeqComposition.lean`:
  higher-level sequencing lemmas used by compiler components.

Useful pattern: for arbitrary halts of a composed machine, invert the sequence
first, recover the intermediate tape, then use closedness/determinism facts for
the phase machines.

## Machine Tables And Debugging

- `FoC/Computability/Compiler/Core/TransitionTableChecks.lean`: table
  well-formedness and deterministic transition helpers such as
  `transition_deterministic_of_all`.
- `FoC/Computability/MachineBuilder.lean` and
  `FoC/Computability/MachineBuilder/StateTables.lean`: low-level table
  constructors.
- `FoC/Computability/MachineDescriptionDebug.lean`: opt-in trace/debug views
  for exact tapes/configurations.
- `FoC/Computability/Compiler/Core/CommonGround/FiniteTransducers/MachineDescriptionDebugExamples.lean`:
  examples of the debug tooling.

For hard finite leaves, write a scratch `.lean` file under `formal/`, state the
candidate machine and exact run theorem, and keep failed proof shapes there
until the working pieces can be moved into the real module.

## Finite Transducers

General reusable finite one-tape transducers live under:

`FoC/Computability/Compiler/Core/CommonGround/FiniteTransducers/`

Common starting points:

- `Basic.lean`: finite transducer base definitions.
- `AppendWord.lean`, `MapAppend.lean`, `OptionAppend.lean`,
  `StatefulOptionAppend.lean`, `StatefulOptionAppendGenerated.lean`: append and
  map-style stream machines.
- `FixedSkips.lean`, `RightEdgeRewind.lean`: small movement and positioning
  machines.
- `Compaction.lean`, `LeftShiftCompactor.lean`, `SentinelGapCompactor.lean`,
  `GapPayloadLocalCompactor.lean`: gap/window compaction families.
- `Structured.lean`, `StructuredPrimitives.lean`, `StructuredTableChecks.lean`:
  logical-tape structured transducer layer.
- `StructuredInputMaterializer*.lean`: source/output materialization contracts,
  output/frontier lemmas, and endpoint-oriented variants.
- `StructuredLowering.lean`, `StructuredStayLowering.lean`: compatibility
  bridges for structured lowering from the older CommonGround location.

For new stream-like machines, look for an existing append/map/stateful
transducer before hand-writing a new transition table.

## Structured Lowering

Current structured lowerer implementation lives under:

`FoC/Computability/Compiler/Structured/`

Key modules:

- `Lowering.lean`: wrapper import for the structured lowerer.
- `Lowering/ThreeTapeHelpers.lean`: row/action constructors and three-tape
  run composition helpers.
- `Lowering/TailedThreeTapeDebug.lean`: debug views for tailed three-tape
  designs.
- `Lowering/Composition.lean`: endpoint sequencing and closed/equivalence
  composition lemmas.
- `HeadRoutes/*.lean`: selected-head decoder, normalizer, and tape-2 projector
  specs and representative/equivalence routes.

Use the wrapper modules first, then jump to the submodule that contains the
specific row, run, or endpoint lemma.

## Canonical Layouts And Recognizers

- `FoC/Computability/Compiler/Core/EncRewriters/CanonicalLayouts/Basic.lean`:
  generic canonical input/handoff tapes and `ClosedRecognizerSpec`.
- `CanonicalLayouts/Dovetail*.lean`, `Configuration.lean`, `Controller.lean`,
  `Simulator.lean`: family-specific canonical layout recognizers/adapters.
- `FoC/Computability/Compiler/Core/EncRewriters/BoundedLayoutRunner/`: bounded
  layout parser/runner contracts.
- `FoC/Computability/Compiler/Core/EncRewriters/ClosedCfgRunner/`: closed
  configuration runner, merge/projection padded routes, and assembly.

For a closed recognizer route, first prove decoder round-trip/inversion lemmas,
then prove the finite recognizer table satisfies `ClosedRecognizerSpec`.

## Endpoint Construction Targets

Target-facing structured compiler obligations live under:

`FoC/Computability/Compiler/Core/StructuredConstructionTargets/`

Key files:

- `Base.lean`: shared endpoint wrappers, exact/equivalence indexed closedness,
  structured input materializer adapters, and sequencing glue.
- `FuelSimulatorInputMaterializer.lean`: FuelSimulator public-input
  materializer route.
- `FuelSimulator.lean`: FuelSimulator structured endpoint component and lowered
  core placeholder.
- `FuelOutput.lean`, `BoundedFuelPairEnumerator.lean`,
  `StageAttemptFramed.lean`: neighboring endpoint routes with similar patterns.

When proving endpoint closedness, prefer reusable indexed closedness lemmas in
`Base.lean` before adding target-local wrappers.

## Closed Configuration Compiler Areas

- `FoC/Computability/Compiler/ClosedCfg/TerminalCore*.lean`: terminal core
  source shapes, route contracts, adapters, and run-config emitter.
- `ClosedCfg/PostTrans/*.lean`: post-transition cleanup and parsed nested
  layout routes.
- `ClosedCfg/QuoteAssembly/*.lean`: quote assembly and marking loops.
- `ClosedCfg/QuoteRest/*.lean`: quote-rest emitter/joiner routes, structured
  lift, live-tail handling.
- `ClosedCfg/ProjTail*.lean`: selected projection padded tail cleanup,
  prefix erasers, scratch bridge, footprint compaction, and output routes.

These modules are split to keep files small.  Wrapper files are route maps;
implementation usually lives in the corresponding subdirectory.

## Universal And Ranges

- `FoC/Computability/Compiler/UniversalAndRanges/HeaderParser.lean`: direct
  finite `TuringMachine` header scanner route.
- `UniversalAndRanges/FiniteSource.lean`: finite source transition parsing.
- `UniversalAndRanges/FiniteSource/DecodedBoundedSimulator/NormRun*.lean`:
  normalized bounded simulator runner.
- `UniversalAndRanges/FiniteSource/Normalizer/Soundness/TransBlock*.lean`:
  transition-block soundness.
- `UniversalAndRanges/FiniteSource/StageSearchController/GenCall*.lean`:
  generated call search algebra/code/product/exact-fuel pieces.

Keep header scanning and transition parsing separate: `FiniteSource.lean`
tracks `decodeTransitions count tokens`; it is not the header scanner.

## Active Obligation Search

Do not keep live hole lists in this map.  For current obligations, search the
source or export declaration data:

```sh
rg -n "sorry" FoC/Computability/Compiler/Core/StructuredConstructionTargets
lake env lean --run scripts/export-declarations.lean \
  FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelSimulatorInputMaterializer \
  FoC.Computability.StructuredConstructionTargets \
  > .lake/structured-target-decls.csv
scripts/summarize-declaration-smells.py --kind theorem \
  .lake/structured-target-decls.csv
```

Keep active proof-order notes in the working plan for that task, not in this
navigational overview.
