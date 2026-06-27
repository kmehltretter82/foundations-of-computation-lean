import FoC.Computability.Tape
import FoC.Computability.TuringMachine
import FoC.Computability.Computable
import FoC.Computability.Recognizable
import FoC.Computability.Transform
import FoC.Computability.Enumerable
import FoC.Computability.Program
import FoC.Computability.Grammar
import FoC.Computability.Undecidable
import FoC.Computability.Coding
import FoC.Computability.Encoding
import FoC.Computability.DiagonalPairMachine
import FoC.Computability.MachineBuilder
import FoC.Computability.Compiler
import FoC.Computability.Compiler.Core.CommonGround
import FoC.Computability.FiniteProgram

set_option doc.verso true

/-!
# Computability API Cross Reference

This page is a map for the reusable Chapter 5 API. It does not introduce new
theory; it records where the public vocabulary, construction internals, exact
tape contracts, and deferred finite-machine surfaces live.

## Public Semantic API

The semantic entry point is the aggregate module {lit}`FoC.Computability`.

* {module}`FoC.Computability.Tape` and
  {module}`FoC.Computability.TuringMachine` define the operational model:
  tapes, configurations, single steps, multi-step computations, halting,
  accepted languages, exact tape results, and normalized output.
* {module}`FoC.Computability.Computable`,
  {module}`FoC.Computability.Recognizable`, and
  {module}`FoC.Computability.Enumerable` define the language-level and
  function-level predicates used by the book statements.
* {module}`FoC.Computability.Program` is the staged semantic layer. It is useful
  for finite-stage dovetailing and bounded search proofs before a concrete
  Turing-machine description is supplied.
* {module}`FoC.Computability.Grammar` connects unrestricted grammar derivations
  with staged recognizers.
* {module}`FoC.Computability.Undecidable`,
  {module}`FoC.Computability.Coding`, and
  {module}`FoC.Computability.DiagonalPairMachine` provide the diagonal,
  reduction, pair-coding, and concrete diagonal-pair machine witnesses used by
  Section 5.3.

These modules are the public API most book-facing pages should cite. They
avoid depending on the transition-table construction details unless a theorem
explicitly needs a concrete machine witness.

## Encoding and Builder API

The finite construction layer starts with concrete syntax for machine
descriptions and code words.

* {module}`FoC.Computability.Encoding` defines machine-description syntax,
  finite transition descriptions, code symbols, decoders, and interpreter
  relations.
* {module}`FoC.Computability.MachineBuilder` re-exports transition-table
  helpers, state-table checks, simulator layouts, dovetail layouts, controller
  layouts, tape-code primitives, and prefix parsers.
* {module}`FoC.Computability.Compiler.DescriptionExecution` connects a
  well-formed {name (full := FoC.Computability.MachineDescription)}`MachineDescription`
  with executable one-tape behavior.
* {module}`FoC.Computability.Compiler.Core.Language`,
  {module}`FoC.Computability.Compiler.Core.BoundedTrace`, and
  {module}`FoC.Computability.Compiler.Core.DovetailCode` hold the reusable
  language-level codes and semantic bounded-runner facts.
* {module}`FoC.Computability.Compiler.Core.EncodingLemmas` contains shared
  append reassociation and decoder-backed cancellation helpers, including
  {name (full := FoC.Computability.encodeBoolWordAppend_inj)}`encodeBoolWordAppend_inj`,
  {name (full := FoC.Computability.encodeConfigurationAppend_inj)}`encodeConfigurationAppend_inj`,
  and
  {name (full := FoC.Computability.encodeDescriptionAppend_inj)}`encodeDescriptionAppend_inj`.
* {module}`FoC.Computability.Compiler.Core.CommonGround` is the compatibility
  facade for recurring compiler construction helpers. New construction files
  should prefer its narrow submodules for sequential composition, exact
  identity helpers, layouts, scanner inversions, code-word emitters,
  controller-layout facts, controller-invocation contracts, and Boolean-word
  quoters.
* {module}`FoC.Computability.FiniteProgram` packages finite executable program
  descriptions whose concrete machine descriptions are explicitly supplied.

This layer is construction-facing but still stable API. It is the right place
to look for encoding injectivity, decoder, and finite interpreter facts before
opening the scanner or controller proof internals.

## Compiler Contract Ladder

The compiler contracts deliberately separate normalized output, exact output,
subroutine readiness, handoff shape, and closed handoff inversion.

* {name (full := FoC.Computability.TapeCodePrimitiveCompiledByDescription)}`TapeCodePrimitiveCompiledByDescription`
  is the exact-output contract for a tape-code primitive.
* {name (full := FoC.Computability.TapeCodePrimitiveOutputRealizedByDescription)}`TapeCodePrimitiveOutputRealizedByDescription`
  proves the forward output direction only.
* {name (full := FoC.Computability.TapeCodePrimitiveOutputCompiledByDescription)}`TapeCodePrimitiveOutputCompiledByDescription`
  proves the normalized-output iff without fixing the final tape window.
* {name (full := FoC.Computability.TapeCodePrimitiveOutputCompiledSubroutineByDescription)}`TapeCodePrimitiveOutputCompiledSubroutineByDescription`
  adds halt-transition freedom for sequencing.
* {name (full := FoC.Computability.TapeCodePrimitiveHandoffCompiledSubroutineByDescription)}`TapeCodePrimitiveHandoffCompiledSubroutineByDescription`
  adds an existential handoff tape for successful primitive transforms.
* {name (full := FoC.Computability.TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription)}`TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription`
  is the strongest contract: every halting tape on canonical input must come
  from a successful transform and must satisfy the normalized-output and
  handoff equations.
* {name (full := FoC.Computability.EncodedRewriters.RightShiftedOutputCompiledSubroutineByDescription)}`EncodedRewriters.RightShiftedOutputCompiledSubroutineByDescription`
  is the exact-tape form used by encoded rewriters that halt one cell to the
  right of the emitted canonical word. The adapter
  {name (full := FoC.Computability.EncodedRewriters.closedHandoffCompiled_of_rightShiftedOutputCompiled)}`EncodedRewriters.closedHandoffCompiled_of_rightShiftedOutputCompiled`
  turns that exact tape shape into the closed handoff contract when outputs
  are known to be nonempty.

For proof work, use the short accessors
{name (full := FoC.Computability.EncodedRewriters.rightShifted_haltsWithTape_inv)}`EncodedRewriters.rightShifted_haltsWithTape_inv`
and
{name (full := FoC.Computability.closedHandoffCompiled_haltsWithTape_inv)}`closedHandoffCompiled_haltsWithTape_inv`
when moving from a halting tape back to the primitive transform and exact tape
equations.

When a proof only has
{name (full := FoC.Computability.Tape.Equiv)}`Tape.Equiv` or
normalized-output theorem, it does
not automatically satisfy a handoff or closed-handoff goal. Those goals require
the final head position and exact tape window.

## Common Proof Ground

{module}`FoC.Computability.Compiler.Core.CommonGround` is not a replacement for
this cross-reference page. This page explains the API map; CommonGround is a
compatibility wrapper. New construction proofs should import the narrow
submodule whose helper family they use.

The CommonGround submodules and namespaces group the helpers that have already
appeared in multiple completed proofs.

* {module}`FoC.Computability.Compiler.Core.CommonGround.Layouts`
  provides {lit}`CommonGround.LayoutTapes`,
  {lit}`CommonGround.FieldInversions`, {lit}`CommonGround.DovetailLayouts`,
  and {lit}`CommonGround.SimulatorLayouts`.
* {module}`FoC.Computability.Compiler.Core.CommonGround.Scanners`
  provides {lit}`CommonGround.ScannerInversions`.
* {module}`FoC.Computability.Compiler.Core.CommonGround.CodeWordEmitters`
  provides {lit}`CommonGround.CodeWordEmitters`.
* {module}`FoC.Computability.Compiler.Core.CommonGround.Controller`
  provides {lit}`CommonGround.ControllerLayouts` and
  {lit}`CommonGround.ControllerInvocation`.
* {module}`FoC.Computability.Compiler.Core.CommonGround.Identity`
  provides {lit}`CommonGround.Identity`.
* {module}`FoC.Computability.Compiler.Core.CommonGround.BoolWordQuoters`
  provides {lit}`CommonGround.BoolWordQuoters`.
* {module}`FoC.Computability.Compiler.Core.CommonGround.SeqComposition`
  provides {lit}`CommonGround.SeqComposition`.

The main namespace families have the following intended uses.

* {lit}`CommonGround.FieldInversions`
  collects complete decoder inversions for canonical fields.
* {lit}`CommonGround.ScannerInversions`
  collects scanner machines and closed scanner inversions used by parser
  proofs.
* {lit}`CommonGround.CodeWordEmitters`
  contains exact and right-shifted code-word emitter adapters.
* {lit}`CommonGround.ControllerLayouts`
  collects controller-layout encoding and primitive-transform facts.
* {lit}`CommonGround.ControllerInvocation`
  names the witnessed stage-attempt invocation contracts used by
  {module}`FoC.Computability.Compiler.Core.FiniteScaffolds`.
* {lit}`CommonGround.Identity`
  contains the reusable exact-identity ready and run facts.
* {lit}`CommonGround.BoolWordQuoters`
  exposes initializer-derived quoters.

When a proof starts by rebuilding one of those facts locally, prefer extending
the relevant narrow CommonGround submodule or its earlier source lemma and then
using the shared name.

## Canonical Layouts and Closed Parsers

The encoded dovetail pipeline uses canonical code-word layouts before it builds
controller machines.

* {module}`FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts`
  collects the layout encoders, field scanners, configuration encoders,
  controller layout encoders, and simulator layout facts.
* {module}`FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner`
  is a wrapper around the closed scanner implementation. Its submodules divide
  primitive field closedness, bool-word closed inversions, shape facts, and
  composition facts.
* {module}`FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.BoolWordClosed`
  is part of the parser API, not dead code. It contains the code-origin closed
  inversions needed before the full dovetail-layout parser can recover a
  complete canonical layout.
* {module}`FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.Parser`
  recognizes complete encoded dovetail layouts and bridges them to the bounded
  layout runner.
* {module}`FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner`
  contains the closed primitive and assembly layer for one bounded layout step.
  Selected projection is assembled through the finite-description
  padded/equivalence route under
  {module}`FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.FiniteDescriptions`;
  exact and right-shifted selected-projection wrappers are adapter-level
  compatibility surfaces, not the active phase-construction path.

These files are proof-internal compared with the semantic API, but they are
not temporary. They are the finite-parser and exact-tape machinery needed for
the compiler closeouts.

## Dovetail Compiler Pipeline

The concrete paired-recognizer construction is split into reusable stages.

* {module}`FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer`
  builds the initial encoded dovetail layout from a stage-input code word.
* {module}`FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner`
  advances a canonical dovetail layout by the encoded stage bound.
* {module}`FoC.Computability.Compiler.Core.EncodedRewriters.TotalOutputEmitter`
  extracts the raw Boolean output from completed dovetail hits.
* {module}`FoC.Computability.Compiler.Core.ControllerStageInputProjection`
  projects the next stage-input code word from the controller layout.
* {module}`FoC.Computability.Compiler.Core.FiniteScaffolds` and
  {module}`FoC.Computability.Compiler.Core.SearchDrivers` connect those
  subroutines to finite-stage loops and search-driver machines.
* {module}`FoC.Computability.Compiler.UniversalAndRanges` collects the
  universal-runner and range-program surfaces used by the Chapter 5 closeouts.

The public theorem statements should generally depend on the contracts exported
by these wrappers, not on local transition-state names inside the construction
files.

## Module Audit Snapshot

Use this snapshot as the first lookup table when returning to the remaining
finite-construction proofs.

* Stable book-facing surface:
  {module}`FoC.Computability.Tape`,
  {module}`FoC.Computability.TuringMachine`,
  {module}`FoC.Computability.Computable`,
  {module}`FoC.Computability.Recognizable`,
  {module}`FoC.Computability.Enumerable`,
  {module}`FoC.Computability.Program`,
  {module}`FoC.Computability.Grammar`,
  {module}`FoC.Computability.Undecidable`,
  {module}`FoC.Computability.Coding`, and
  {module}`FoC.Computability.FiniteProgram`. These modules should remain
  readable without knowing the finite transition-table construction details.
* Stable compiler-facing surface:
  {module}`FoC.Computability.Encoding`,
  {module}`FoC.Computability.MachineBuilder`,
  {module}`FoC.Computability.Compiler`,
  {module}`FoC.Computability.Compiler.Core.ConstructionTargets`,
  {module}`FoC.Computability.Compiler.Core.Closeout`,
  {module}`FoC.Computability.Compiler.Core.TapeCodePrimitives`,
  {module}`FoC.Computability.Compiler.Core.EncodingLemmas`,
  {module}`FoC.Computability.Compiler.Core.CommonGround`,
  {module}`FoC.Computability.Compiler.Core.CommonGround.Layouts`,
  {module}`FoC.Computability.Compiler.Core.CommonGround.Scanners`,
  {module}`FoC.Computability.Compiler.Core.CommonGround.CodeWordEmitters`,
  {module}`FoC.Computability.Compiler.Core.CommonGround.Controller`, and
  {module}`FoC.Computability.Compiler.Core.EncodedRewriters.RightShifted`.
  These are the files to check first for reusable records, wrappers, aliases,
  append-cancellation facts, and exact-tape handoff contracts.
* Canonical parser proof internals:
  {module}`FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.PrimitiveClosed`,
  {module}`FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.BoolWordClosed`,
  {module}`FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.ShapeClosed`,
  and
  {module}`FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.Composition`.
  These should be opened when a goal needs code-origin, closedness, suffix, or
  scanner-composition inversions. They are proof infrastructure, not a public
  semantic dependency.
* Bounded-layout runner proof internals:
  {module}`FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.Parser`,
  {module}`FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.Parser.Closed`,
  {module}`FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner`,
  {module}`FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed`,
  and
  {module}`FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction`.
  These are the files to inspect for the checked-layout parser inversion and
  the selected projection/merge exact-tape constructions.
* Controller and finite-loop construction internals:
  {module}`FoC.Computability.Compiler.Core.ControllerInputInitializer`,
  {module}`FoC.Computability.Compiler.Core.ControllerResultContinue`,
  {module}`FoC.Computability.Compiler.Core.FiniteScaffolds`, and
  {module}`FoC.Computability.Compiler.Core.SearchDrivers`. These connect
  explicit subroutine descriptions into finite-stage controller loops.
* Universal finite-source construction internals:
  {module}`FoC.Computability.Compiler.UniversalAndRanges.HeaderParser`,
  {module}`FoC.Computability.Compiler.UniversalAndRanges.FiniteSource`,
  {module}`FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.TransitionListParser`,
  and
  {module}`FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController`.
  These are separate from the paired-recognizer dovetail controller and should
  be solved through description decoding, transition-list parsing, and bounded
  simulator facts.

At this cleanup checkpoint, the project is expected to build with only the
intentional {lit}`sorry` warnings. If that changes, update this page together
with the construction target or helper theorem that changed the proof surface.

## Proof Navigation Rules

Before opening a remaining proof hole, classify the goal by contract strength.

* A semantic theorem about acceptance, output, recognizability, or staged
  programs belongs at the public semantic layer and should avoid exact
  transition names.
* A normalized-output theorem can use
  {name (full := FoC.Computability.Tape.output)}`Tape.output` and
  {name (full := FoC.Computability.Tape.Equiv)}`Tape.Equiv`, but it is not
  enough for a right-shifted or closed-handoff construction.
* A right-shifted goal must end with an exact
  {name (full := FoC.Computability.MachineDescription.HaltsWithTape)}`MachineDescription.HaltsWithTape`
  equation whose head is one cell to the right of the canonical output word.
  Use the short right-shifted accessors before expanding the record.
* A closed-handoff goal must prove the inverse direction from every halting
  tape on canonical input back to the primitive transform. Use
  {name (full := FoC.Computability.closedHandoffCompiled_haltsWithTape_inv)}`closedHandoffCompiled_haltsWithTape_inv`
  and related accessors rather than reproving the record projections locally.
* A parser or scanner inversion that compares encoded prefixes should first
  try the decoder-backed cancellation helpers in
  {module}`FoC.Computability.Compiler.Core.EncodingLemmas` and the scanner
  exports in
  {module}`FoC.Computability.Compiler.Core.CommonGround.Scanners`. If the goal
  is still about a canonical layout field, then move into the
  DovetailLayoutScanner closed modules.
* A theorem whose name ends in {lit}`_scaffold` is deliberately a construction
  target. It should be discharged by supplying finite descriptions and
  sequencing data, not by weakening the statement to a semantic equivalence.

## Durable Proof Lessons

The cross-reference file has been useful as a guardrail, especially for
remembering which proof holes are real construction leaves and which facts are
only adapters. Keep these lessons in mind before splitting another {lit}`sorry`
into smaller targets.

* A split is only useful when the second theorem genuinely consumes the
  witness produced by the first theorem. Do not introduce an
  {lit}`OutputSubroutineConstruction` target followed by a theorem that claims
  to turn any output-compiled machine into a right-shifted or closed-handoff
  machine unless that closure proof preserves and uses the supplied machine.
  That pattern was over-strong for the fixed-description bounded simulator
  code, the selected projection and merge primitives, and the bounded-layout
  runner closed-handoff wrapper.
* The right-shifted contract is stronger than normalized output and stronger
  than {name (full := FoC.Computability.Tape.Equiv)}`Tape.Equiv`.
  {name (full := FoC.Computability.EncodedRewriters.RightShiftedOutputCompiledSubroutineByDescription)}`EncodedRewriters.RightShiftedOutputCompiledSubroutineByDescription`
  requires the exact final tape
  {lit}`Tape.move Direction.right (Tape.input (encodeCodeWordAsInput out))`.
  A proof that identifies only the emitted word or a tape-equivalence class is
  not an adapter to this contract.
* The selected projection and selected merge primitives are asymmetric.
  {lit}`SelectedMergeSpec` has an exact-output theorem usable for
  {lit}`selectedMergeRightShifted_of_spec`; {lit}`SelectedProjectionSpec`
  currently exposes only equivalence-style output information. Do not add a
  projection analogue unless the projection spec is strengthened to exact
  final-tape output.
* In the selected-primitive assembly, closed handoff is derived from
  right-shifted output. Using a selected closed-handoff scaffold to prove a
  selected right-shifted leaf would be circular.
* The live bounded config-runner assembly consumes selected projection through
  {name (full := FoC.Computability.EncodedRewriters.BoundedLayoutRunner.SelectedProjectionPhaseFromOutputTape)}`SelectedProjectionPhaseFromOutputTape`
  and the {lit}`AcceptProjectionSpec_of_selected` /
  {lit}`RejectProjectionSpec_of_selected` adapters. Do not route the phase
  assembly back through selected closed-handoff projection scaffolds just to
  repair the right-shifted head position.
* {lit}`controllerResultContinueConstruction_scaffold` is the missing
  code-word subroutine construction itself, not merely an adapter around an
  already compiled subroutine.
* {lit}`controllerInputInitializerConstruction_scaffold` is a raw-Bool-input
  emitter for {lit}`PairedRecognizerDovetailControllerInitialCode w`. It is
  separate from the stage-input-to-initial-layout primitive built by
  {module}`FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer`.
* The stage-search-controller holes are genuine unbounded-search/compiler
  leaves: budget-checker sequencing and budget-search sequencing for the
  code-prefix finite-source path. The Boolean dovetail-controller
  {module}`FoC.Computability.Compiler.Core.SearchDrivers` machinery is related
  background, not a direct replacement for those code-prefix machines.
* The remaining decoded-bounded-simulator code-machine construction should not
  be proved through the aggregate
  {module}`FoC.Computability.Compiler.UniversalAndRanges.FiniteSource` route.
  That route imports the leaf construction path and would turn the proof into
  a cycle.
* For the checked dovetail-layout parser, keep the dependency direction from
  smaller scanner inversions to the body inversion. In particular,
  {lit}`checkedDovetailLayoutScannerDescription_haltsWithTape_body_fields_inv`
  must not use
  {lit}`checkedDovetailLayoutScannerDescription_haltsWithTape_decodeComplete_inv`,
  because the decode-complete theorem is downstream of the body inversion.
* The current parser inversions recover bool-word and natural-number suffix
  boundaries, but the remaining hard lower lemma is still a
  configuration-suffix/final-flag shape inversion: a successful body run must
  expose two encoded configurations followed by two encoded Boolean flags.
  The helper
  {lit}`natSuffixScannerDescription_runConfig_stageNat_handoff` records part
  of that handoff shape for nonempty stage suffixes; it is not the full body
  inversion by itself.
* Do not use a parent aggregate module to prove one of its imported leaf
  modules. When a construction target lives below an aggregate, solve it using
  the lower-level parser, simulator, and sequencing modules already available
  to that leaf.

## Remaining Sorry Work Map

The remaining proof holes are best approached by contract family, not by file
order.

* Universal finite-source leaves:
  {name (full := FoC.Computability.codePrefixDecodedBoundedSimulatorCodeMachineConstruction_core)}`codePrefixDecodedBoundedSimulatorCodeMachineConstruction_core`
  and
  {name (full := FoC.Computability.codePrefixStageSearchControllerProgramCompilerConstruction_core)}`codePrefixStageSearchControllerProgramCompilerConstruction_core`
  live under {module}`FoC.Computability.Compiler.UniversalAndRanges.FiniteSource`.
  They require real finite machines for decoding a staged machine description
  and for unbounded stage search. They should use the header parser,
  transition-list parser, branch sequencing, and bounded simulator semantics
  nearby rather than the encoded dovetail-controller internals.
* Controller finite-loop leaves:
  {name (full := FoC.Computability.controllerInputInitializerConstruction_scaffold)}`controllerInputInitializerConstruction_scaffold`,
  {name (full := FoC.Computability.controllerResultContinueConstruction_scaffold)}`controllerResultContinueConstruction_scaffold`,
  {name (full := FoC.Computability.pairedRecognizerDovetailStageAttemptInvocationConstructionData_scaffold)}`pairedRecognizerDovetailStageAttemptInvocationConstructionData_scaffold`,
  and
  {name (full := FoC.Computability.pairedRecognizerDovetailFiniteStageLoopSequencingConstructionData_scaffold)}`pairedRecognizerDovetailFiniteStageLoopSequencingConstructionData_scaffold`
  are sequencing/construction obligations for the controller loop. They should
  bottom out in explicit initializer, invoker, continue, and finite-loop
  transition descriptions, not in semantic staged-program shortcuts.
* Bounded-layout parser leaf:
  {name (full := FoC.Computability.EncodedRewriters.BoundedLayoutRunner.checkedDovetailLayoutScannerDescription_haltsWithTape_body_inv)}`EncodedRewriters.BoundedLayoutRunner.checkedDovetailLayoutScannerDescription_haltsWithTape_body_inv`
  is the consolidated closed-parser inversion. It should use the bool-word,
  nat, configuration-suffix, and final-flag closed scanner facts from
  {module}`FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner`
  plus the decoder-backed cancellation helpers from
  {module}`FoC.Computability.Compiler.Core.EncodingLemmas`, and should produce
  the exact checked handoff equation, not merely a decoded layout.
* Selected-projection padded/equivalence leaves:
  {name (full := FoC.Computability.EncodedRewriters.BoundedLayoutRunner.selectedProjectionInputQuoterExactShapeConstruction_scaffold)}`EncodedRewriters.BoundedLayoutRunner.selectedProjectionInputQuoterExactShapeConstruction_scaffold`
  and
  {name (full := FoC.Computability.EncodedRewriters.BoundedLayoutRunner.selectedProjectionPaddedTailCleanupConstruction_scaffold)}`EncodedRewriters.BoundedLayoutRunner.selectedProjectionPaddedTailCleanupConstruction_scaffold`
  are the live selected-projection finite-machine obligations. They feed
  {name (full := FoC.Computability.EncodedRewriters.BoundedLayoutRunner.selectedProjectionFiniteDescriptionConstruction_scaffold)}`EncodedRewriters.BoundedLayoutRunner.selectedProjectionFiniteDescriptionConstruction_scaffold`
  through the checked-equivalence padded emitter route, which is the active
  proof path used by bounded-runner phase assembly.
  {name (full := FoC.Computability.EncodedRewriters.BoundedLayoutRunner.selectedProjectionPrimitiveExactConstruction_scaffold)}`EncodedRewriters.BoundedLayoutRunner.selectedProjectionPrimitiveExactConstruction_scaffold`
  and
  {name (full := FoC.Computability.EncodedRewriters.BoundedLayoutRunner.selectedProjectionPrimitiveRightShiftedConstruction_core)}`EncodedRewriters.BoundedLayoutRunner.selectedProjectionPrimitiveRightShiftedConstruction_core`
  are legacy adapter-level compatibility targets for public exact or
  right-shifted primitive packaging. They may remain only when needed for that
  adapter surface, and they should not be used on the route to the known
  context-length shrink obstruction.
* Config-runner selected-merge equivalence leaf:
  {name (full := FoC.Computability.EncodedRewriters.BoundedLayoutRunner.selectedMergeEquivPaddedEmitterConstruction_scaffold)}`EncodedRewriters.BoundedLayoutRunner.selectedMergeEquivPaddedEmitterConstruction_scaffold`
  is the selected-merge finite-machine obligation. The former exact
  right-shifted merge target has a context-length shrink obstruction; see
  {lit}`LEAN_COUNTEREXAMPLE_OVERVIEW.md` for the archived proof names.  The
  merge phase must instead emit the selected output plus blank padding so the
  exact tape is equivalent to the parsed dovetail-layout tape while preserving
  simulator-layout scratch structure.
  The live selected-merge equivalence construction uses the forward-only
  identity parser adapter
  {name (full := FoC.Computability.EncodedRewriters.BoundedLayoutRunner.selectedMergeForwardParserConstruction_scaffold)}`EncodedRewriters.BoundedLayoutRunner.selectedMergeForwardParserConstruction_scaffold`.
  The stronger selected-merge input validator uses
  {name (full := FoC.Computability.EncodedRewriters.BoundedLayoutRunner.selectedMergeInputValidatorConstruction_of_parser_checker)}`EncodedRewriters.BoundedLayoutRunner.selectedMergeInputValidatorConstruction_of_parser_checker`;
  the exact/right-shifted input-validator primitive path is stronger adapter
  glue, not the phase parser dependency.
* Fixed-description simulator phase leaf:
  the old exact canonical phase has a context-length shrink obstruction; see
  {lit}`LEAN_COUNTEREXAMPLE_OVERVIEW.md` for the archived proof names.
  The bounded-layout config runner now uses the padded/equivalence simulator
  boundary instead of that exact phase.  The full right-shifted
  {name (full := FoC.Computability.FixedDescriptionBoundedSimulatorCode)}`FixedDescriptionBoundedSimulatorCode`
  package is no longer a live bounded-runner dependency; parser/primitive
  packaging remains available through adapter theorems rather than public
  scaffolds.
* Bounded-layout closed handoff wrapper:
  {name (full := FoC.Computability.encodedDovetailLayoutBoundedRunnerClosedHandoffRewriterConstruction_scaffold)}`encodedDovetailLayoutBoundedRunnerClosedHandoffRewriterConstruction_scaffold`
  cannot be closed from an output-compiled runner alone. It needs either the
  parser and config-runner exact-tape leaves, or a stronger bounded-layout
  runner theorem that already exposes closed handoff behavior.

## Construction Boundaries

The remaining construction targets are named explicitly in
{module}`FoC.Computability.Compiler.Core.ConstructionTargets` and packaged by
{module}`FoC.Computability.Compiler.Core.Closeout`.

The useful audit categories are:

* public API: semantic definitions, encodings, compiler contracts, and closeout
  records cited by book-facing pages;
* construction internals: concrete transition-table descriptions and
  right-shifted or closed-handoff builders;
* proof internals: scanner closedness, parser inversions, phase-specific run
  lemmas, and code-origin shape facts;
* deferred surfaces: named construction predicates whose theorem statements are
  intentionally stronger than the semantic facts currently available.

This distinction is important for later cleanup. A wrapper theorem or short
alias belongs in the public API only when it hides proof-internal names without
weakening the contract. A missing exact-tape construction should remain a
construction target rather than being replaced by a normalized-output or
{name (full := FoC.Computability.Tape.Equiv)}`Tape.Equiv` theorem.
-/
