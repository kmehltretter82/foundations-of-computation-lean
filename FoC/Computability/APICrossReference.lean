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

When a proof only has
{name (full := FoC.Computability.Tape.Equiv)}`Tape.Equiv` or
normalized-output theorem, it does
not automatically satisfy a handoff or closed-handoff goal. Those goals require
the final head position and exact tape window.

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
  and should produce the exact checked handoff equation, not merely a decoded
  layout.
* Config-runner exact-tape leaves:
  {name (full := FoC.Computability.EncodedRewriters.BoundedLayoutRunner.selectedProjectionPrimitiveRightShiftedConstruction_core)}`EncodedRewriters.BoundedLayoutRunner.selectedProjectionPrimitiveRightShiftedConstruction_core`
  and
  {name (full := FoC.Computability.EncodedRewriters.BoundedLayoutRunner.selectedMergePrimitiveRightShiftedConstruction_core)}`EncodedRewriters.BoundedLayoutRunner.selectedMergePrimitiveRightShiftedConstruction_core`
  must produce
  {name (full := FoC.Computability.EncodedRewriters.RightShiftedOutputCompiledSubroutineByDescription)}`EncodedRewriters.RightShiftedOutputCompiledSubroutineByDescription`.
  A theorem that only proves
  {name (full := FoC.Computability.Tape.Equiv)}`Tape.Equiv` for the selected
  projection or merge output is too weak.
* Fixed-description simulator exact-tape leaf:
  {name (full := FoC.Computability.fixedDescriptionBoundedSimulatorCodeRightShiftedConstruction_scaffold)}`fixedDescriptionBoundedSimulatorCodeRightShiftedConstruction_scaffold`
  is the reusable right-shifted compiler target for
  {name (full := FoC.Computability.FixedDescriptionBoundedSimulatorCode)}`FixedDescriptionBoundedSimulatorCode`.
  Proving it would unblock downstream config-runner phase construction.
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
