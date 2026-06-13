import FoC.Book.Chapter05.Section02.Dovetailing

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter05
namespace Section02

/-!
# Section 5.2 machine compiler boundaries
-/

open Languages
open Computability
open Grammars

universe u v

/-!
**Code-output boundary.**  Exact tape output is intentionally separated from
normalized code output here.  The identity primitive satisfies both contracts,
while erasure is impossible for the exact tape-window contract but is realized
by a concrete finite normalized-output machine.

**Finite-source finish criteria.**  The remaining compiler work is deliberately
tracked through named finite construction targets.  The goal is not to prove a
compiler theorem for arbitrary staged programs or arbitrary
{name}`MachineDescription.TapeCodePrimitive`s in one step; it is to close the
finite parser, emitter, sequencer, branch, and stage-controller descriptions
that the book-facing theorems already route through.

For the fixed one-step primitive, the new bridge says that it is enough to
build a finite stepper on canonical encoded configurations.  Parser
canonicalization lemmas then promote that theorem to the full
{name}`TapeCodePrimitiveOutputRealizedByDescription` interface, covering any
code word whose configuration decoder succeeds completely.

The two formulations are now proved equivalent.  This concentrates the
construction interface into one finite transducer problem: build the concrete
Boolean transition table that parses a canonical configuration, performs one
fixed description-table lookup, and emits the re-encoded successor
configuration.

The concrete transducer pieces are retained as a small compiler core. A finite
table appends one fixed encoded code symbol to the normalized Boolean output,
while the code-primitive layer provides fixed unary comparisons and one-step
tape write/move actions with canonical encode/decode theorems. A concrete
Boolean-output table erases its input and emits either {lit}`true` or
{lit}`false`, giving the eventual dovetail driver finite halt branches. The
identity, erase, and one-symbol append tables are now recorded with the
stronger normalized-output compiled-subroutine contract, and the Boolean-output
table has an iff theorem ruling out non-singleton spurious outputs. The
same tables are also packaged as halt-transition-free subroutines, so later
control-flow tables can call them without adding outgoing transitions from
their halting states. The subroutine layer also provides a description-level
sequencer: a subroutine-ready table can be viewed as a fragment, composed with
another such table, and reasoned about using the existing first-arrival
fragment semantics. A finite cell-branch table is now separated out as the
basic one-step controller primitive: it reads the current tape cell, preserves
it while moving, and jumps to the blank, false, or true target state with
proved well-formedness and halt-free packaging. The controller raw-output
branch also has a code primitive that maps encoded singleton Boolean results
to encoded raw outputs and rejects the empty no-hit result. Composing that
branch after the total-attempt code recovers the older partial stage-attempt
code contract, which is the executable no-hit/singleton split the controller
loop has to implement. The no-hit branch now has its own controller-layout
code primitive that rewrites an encoded controller layout to the next stage,
while the hit branch has a matching emit primitive for the raw Boolean output.
Their canonical-input theorems prove the exact disjunction: a no-hit stage
enables only the continue branch, while a hit stage enables only the matching
encoded Boolean emit branch.
For the paired-recognizer dovetailer, the layout runner
now has a halt-free output-realizer contract and the search-driver interface
has a subroutine-ready variant, isolating the exact contract needed by the
future finite transition table that loops around a compiled layout subroutine.
The controller boundary is now split further into canonical machine-code
operations: build the initial dovetail layout from the input word and stage
limit, run the paired layout subroutine, and inspect the resulting hit flags
as a Boolean output code. These operations are also packaged as a single-stage
attempt primitive whose canonical-input theorem returns exactly the encoded
bounded-dovetail result for that stage. The direct-controller interface uses
a total variant of this primitive: no hit is encoded as the empty Boolean word,
while accepting and rejecting hits are encoded as singleton Boolean words.
That total result now has its own controller layout and branch view: decoding
the total attempt output and taking the singleton raw-output branch is proved
equivalent to the bounded dovetail result for the current stage. The
controller path also records the stronger normalized-output compiler contract
needed for sound branching on a subroutine's observed output: the old
output-realizer contract is one-way, so it cannot rule out spurious halting
outputs from an arbitrary subroutine. Under the stronger contract, a
controller-search driver again yields the paired-recognizer dovetail compiler,
and the controller-search driver is itself closed by a staged program that
tries the total-attempt subroutine at each stage and branches only on singleton
raw outputs. The lower-level work left, if one wants to avoid the
description-backed Boolean compiler principle for this driver, is the
handwritten transition table that iterates the controller state, calls the
total-attempt subroutine, and hands off singleton results to the raw Boolean
output branches.
Exact compilation of every code primitive is proved
impossible because erasure cannot produce an exact empty tape window from
nonempty input. The viable boundary is therefore a normalized-output tape-code
compiler: if that one generic compiler principle is supplied, the fixed
stepper, bounded simulator, and dovetail-layout machine-description obligations
all follow.
-/

theorem concrete_fixed_description_bounded_simulator_table_compiler_of_code_compiler
    (hcompile :
      ConcreteFixedDescriptionBoundedSimulatorCodeCompilerConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction :=
  Computability.fixedDescriptionBoundedSimulatorTableCompiler_of_codeCompiler
    hcompile

theorem concrete_fixed_description_bounded_simulator_table_compiler_of_code_output_realizer
    (hcompile :
      ConcreteFixedDescriptionBoundedSimulatorCodeOutputRealizerConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction :=
  Computability.fixedDescriptionBoundedSimulatorTableCompiler_of_codeOutputRealizer
    hcompile

def concrete_machine_description_primitive_compiler_core :
    MachineDescriptionPrimitiveCompilerCore :=
  Computability.machineDescriptionPrimitiveCompilerCore

def concrete_machine_description_primitive_subroutine_core :
    MachineDescriptionPrimitiveSubroutineCore :=
  Computability.machineDescriptionPrimitiveSubroutineCore

theorem concrete_description_first_reaches_halt_of_runConfig_eq
    {D : MachineDescription}
    (hD : D.HaltTransitionFree)
    {n : Nat} {c : MachineDescription.Configuration} {T : Tape Bool}
    (hrun : D.runConfig n c = { state := D.halt, tape := T }) :
    exists m : Nat,
      m ≤ n ∧
        D.runConfig m c = { state := D.halt, tape := T } ∧
        forall k : Nat,
          k < m -> (D.runConfig k c).state ≠ D.halt :=
  MachineDescription.firstReaches_halt_of_runConfig_eq hD hrun

theorem concrete_seq_subroutine_ready
    {A B : MachineDescription} {handoffMove : Direction}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady) :
    (MachineDescription.seqSubroutine A B handoffMove).SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady hA hB

theorem concrete_seq_subroutine_reaches_of_runConfig_eq
    {A B : MachineDescription} {handoffMove : Direction}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {nA : Nat} {Tin Tmid Tout : Tape Bool}
    (hArun :
      A.runConfig nA { state := A.start, tape := Tin } =
        { state := A.halt, tape := Tmid })
    (hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start,
              tape := Tape.move handoffMove Tmid } =
          { state := B.halt, tape := Tout }) :
    exists n : Nat,
      (MachineDescription.seqSubroutine A B handoffMove).runConfig n
          { state :=
              (MachineDescription.seqSubroutine A B handoffMove).start,
            tape := Tin } =
        { state := (MachineDescription.seqSubroutine A B handoffMove).halt,
          tape := Tout } :=
  MachineDescription.seqSubroutine_reaches_of_runConfig_eq
    hA hB hArun hBReach

theorem concrete_bool_output_description_wellFormed (b : Bool) :
    (ConcreteBoolOutputDescription b).WellFormed :=
  MachineDescription.boolOutputDescription_wellFormed b

theorem concrete_bool_output_description_haltTransitionFree (b : Bool) :
    (ConcreteBoolOutputDescription b).HaltTransitionFree :=
  MachineDescription.boolOutputDescription_haltTransitionFree b

theorem concrete_bool_output_description_haltsWithOutput
    (b : Bool) (w : Word Bool) :
    (ConcreteBoolOutputDescription b).HaltsWithOutput w [b] :=
  MachineDescription.boolOutputDescription_haltsWithOutput b w

theorem concrete_bool_output_description_haltsWithOutput_iff
    (b : Bool) (w out : Word Bool) :
    (ConcreteBoolOutputDescription b).HaltsWithOutput w out <-> out = [b] :=
  MachineDescription.boolOutputDescription_haltsWithOutput_iff b w out

theorem concrete_tape_code_exact_compiler_construction_impossible :
    ¬ ConcreteTapeCodeExactCompilerConstruction :=
  Computability.not_machineDescriptionTapeCodeExactCompilerConstruction

def concrete_machine_description_compiler_closeout_of_tape_code_output_compiler
    (hcompile : ConcreteTapeCodeOutputCompilerConstruction) :
    MachineDescriptionCompilerCloseout :=
  Computability.machineDescriptionCompilerCloseout_of_tapeCodeOutputCompiler
    hcompile

theorem concrete_fixed_description_step_code_configuration_realizer_construction_of_tape_code_output_compiler
    (hcompile : ConcreteTapeCodeOutputCompilerConstruction) :
    ConcreteFixedDescriptionStepCodeConfigurationRealizerConstruction :=
  Computability.fixedDescriptionStepCodeConfigurationRealizerConstruction_of_tapeCodeOutputCompiler
    hcompile

theorem concrete_fixed_description_bounded_simulator_table_compiler_of_tape_code_output_compiler
    (hcompile : ConcreteTapeCodeOutputCompilerConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction :=
  Computability.fixedDescriptionBoundedSimulatorTableCompiler_of_tapeCodeOutputCompiler
    hcompile

theorem concrete_paired_recognizer_dovetail_layout_code_output_realizer_of_tape_code_output_compiler
    (hcompile : ConcreteTapeCodeOutputCompilerConstruction) :
    ConcretePairedRecognizerDovetailLayoutCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailLayoutCodeOutputRealizer_of_tapeCodeOutputCompiler
    hcompile

theorem concrete_paired_recognizer_dovetail_initial_layout_code_output_realizer_of_tape_code_output_compiler
    (hcompile : ConcreteTapeCodeOutputCompilerConstruction) :
    ConcretePairedRecognizerDovetailInitialLayoutCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailInitialLayoutCodeOutputRealizer_of_tapeCodeOutputCompiler
    hcompile

theorem concrete_paired_recognizer_dovetail_output_code_output_realizer_of_tape_code_output_compiler
    (hcompile : ConcreteTapeCodeOutputCompilerConstruction) :
    ConcretePairedRecognizerDovetailOutputCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailOutputCodeOutputRealizer_of_tapeCodeOutputCompiler
    hcompile

theorem concrete_paired_recognizer_dovetail_stage_attempt_code_output_realizer_of_tape_code_output_compiler
    (hcompile : ConcreteTapeCodeOutputCompilerConstruction) :
    ConcretePairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailStageAttemptCodeOutputRealizer_of_tapeCodeOutputCompiler
    hcompile

theorem concrete_paired_recognizer_dovetail_total_stage_attempt_code_output_realizer_of_tape_code_output_compiler
    (hcompile : ConcreteTapeCodeOutputCompilerConstruction) :
    ConcretePairedRecognizerDovetailTotalStageAttemptCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailTotalStageAttemptCodeOutputRealizer_of_tapeCodeOutputCompiler
    hcompile

theorem concrete_paired_recognizer_dovetail_total_then_raw_output_code_output_realizer_of_tape_code_output_compiler
    (hcompile : ConcreteTapeCodeOutputCompilerConstruction) :
    ConcretePairedRecognizerDovetailTotalThenRawOutputCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailTotalThenRawOutputCodeOutputRealizer_of_tapeCodeOutputCompiler
    hcompile

theorem concrete_paired_recognizer_dovetail_controller_continue_code_output_realizer_of_tape_code_output_compiler
    (hcompile : ConcreteTapeCodeOutputCompilerConstruction) :
    ConcretePairedRecognizerDovetailControllerContinueCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailControllerContinueCodeOutputRealizer_of_tapeCodeOutputCompiler
    hcompile

theorem concrete_paired_recognizer_dovetail_controller_emit_code_output_realizer_of_tape_code_output_compiler
    (hcompile : ConcreteTapeCodeOutputCompilerConstruction) :
    ConcretePairedRecognizerDovetailControllerEmitCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailControllerEmitCodeOutputRealizer_of_tapeCodeOutputCompiler
    hcompile

theorem concrete_paired_recognizer_dovetail_total_stage_attempt_code_output_realizer_of_subroutine_realizer
    (hcompile :
      ConcretePairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction) :
    ConcretePairedRecognizerDovetailTotalStageAttemptCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailTotalStageAttemptCodeOutputRealizer_of_subroutineRealizer
    hcompile

theorem concrete_paired_recognizer_dovetail_stage_attempt_code_output_realizer_of_total_then_raw_output_code_output_realizer
    (hcompile :
      ConcretePairedRecognizerDovetailTotalThenRawOutputCodeOutputRealizerConstruction) :
    ConcretePairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailStageAttemptCodeOutputRealizer_of_totalThenRawOutputCodeOutputRealizerConstruction
    hcompile

theorem concrete_paired_recognizer_dovetail_total_stage_attempt_code_controller_result_realizes
    (accept reject : MachineDescription) :
    ConcretePairedRecognizerDovetailTotalStageAttemptControllerResultRealizes
      accept reject
      (PairedRecognizerDovetailTotalStageAttemptCode accept reject) :=
  Computability.pairedRecognizerDovetailTotalStageAttemptCode_controllerResultRealizes
    accept reject

theorem concrete_paired_recognizer_dovetail_controller_raw_output_code_realizes :
    ConcretePairedRecognizerDovetailControllerRawOutputCodeRealizes
      ConcretePairedRecognizerDovetailControllerRawOutputCode :=
  Computability.pairedRecognizerDovetailControllerRawOutputCode_realizes

theorem concrete_paired_recognizer_dovetail_controller_raw_output_code_eq_some_encodeBoolWord_singleton_iff
    {tokens : Word MachineCodeSymbol} {b : Bool} :
    ConcretePairedRecognizerDovetailControllerRawOutputCode.transform
        tokens =
        some (MachineDescription.encodeBoolWord [b]) <->
      MachineDescription.DovetailControllerLayout.decodeAttemptResultCode
        tokens = some [b] :=
  Computability.pairedRecognizerDovetailControllerRawOutputCode_eq_some_encodeBoolWord_singleton_iff

theorem concrete_paired_recognizer_dovetail_controller_continue_code_realizes
    (accept reject : MachineDescription) :
    ConcretePairedRecognizerDovetailControllerContinueCodeRealizes
      accept reject
      (ConcretePairedRecognizerDovetailControllerContinueCode
        accept reject) :=
  Computability.pairedRecognizerDovetailControllerContinueCode_realizes
    accept reject

theorem concrete_paired_recognizer_dovetail_controller_emit_code_realizes
    (accept reject : MachineDescription) :
    ConcretePairedRecognizerDovetailControllerEmitCodeRealizes
      accept reject
      (ConcretePairedRecognizerDovetailControllerEmitCode
        accept reject) :=
  Computability.pairedRecognizerDovetailControllerEmitCode_realizes
    accept reject

theorem concrete_paired_recognizer_dovetail_controller_continue_code_encode_eq_some_iff
    {accept reject : MachineDescription}
    {C : MachineDescription.DovetailControllerLayout}
    {out : Word MachineCodeSymbol} :
    (ConcretePairedRecognizerDovetailControllerContinueCode
      accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some out <->
      MachineDescription.boundedDovetailOutput
          accept reject C.input C.stage = none ∧
        out =
          MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.nextStage C) :=
  Computability.pairedRecognizerDovetailControllerContinueCode_encode_eq_some_iff

theorem concrete_paired_recognizer_dovetail_controller_emit_code_encode_eq_some_iff
    {accept reject : MachineDescription}
    {C : MachineDescription.DovetailControllerLayout}
    {outCode : Word MachineCodeSymbol} :
    (ConcretePairedRecognizerDovetailControllerEmitCode
      accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some outCode <->
      exists out : Word Bool,
        MachineDescription.boundedDovetailOutput
          accept reject C.input C.stage = some out ∧
          outCode = MachineDescription.encodeBoolWord out :=
  Computability.pairedRecognizerDovetailControllerEmitCode_encode_eq_some_iff

theorem concrete_paired_recognizer_dovetail_controller_emit_code_encode_eq_encode_bool_word_iff
    {accept reject : MachineDescription}
    {C : MachineDescription.DovetailControllerLayout}
    {out : Word Bool} :
    (ConcretePairedRecognizerDovetailControllerEmitCode
      accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some (MachineDescription.encodeBoolWord out) <->
      MachineDescription.boundedDovetailOutput
        accept reject C.input C.stage = some out :=
  Computability.pairedRecognizerDovetailControllerEmitCode_encode_eq_encodeBoolWord_iff

theorem concrete_paired_recognizer_dovetail_controller_continue_emit_code_exclusive
    {accept reject : MachineDescription}
    {C : MachineDescription.DovetailControllerLayout}
    {next out : Word MachineCodeSymbol}
    (hcontinue :
      (ConcretePairedRecognizerDovetailControllerContinueCode
        accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
          some next)
    (hemit :
      (ConcretePairedRecognizerDovetailControllerEmitCode
        accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
          some out) :
    False :=
  Computability.pairedRecognizerDovetailControllerContinueEmitCode_exclusive
    hcontinue hemit

theorem concrete_paired_recognizer_dovetail_controller_continue_emit_code_branch
    (accept reject : MachineDescription)
    (C : MachineDescription.DovetailControllerLayout) :
    ((ConcretePairedRecognizerDovetailControllerContinueCode
        accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some
          (MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.nextStage C)) ∧
      (ConcretePairedRecognizerDovetailControllerEmitCode
        accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) = none) ∨
      ((ConcretePairedRecognizerDovetailControllerContinueCode
          accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) = none ∧
        exists out : Word Bool,
          MachineDescription.boundedDovetailOutput
            accept reject C.input C.stage = some out ∧
            (ConcretePairedRecognizerDovetailControllerEmitCode
              accept reject).transform
              (MachineDescription.DovetailControllerLayout.encode C) =
                some (MachineDescription.encodeBoolWord out)) :=
  Computability.pairedRecognizerDovetailControllerContinueEmitCode_branch
    accept reject C

theorem concrete_paired_recognizer_dovetail_total_then_raw_output_code_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailStageAttemptCodeRealizes
      accept reject
      (ConcretePairedRecognizerDovetailTotalThenRawOutputCode
        accept reject) :=
  Computability.pairedRecognizerDovetailTotalThenRawOutputCode_realizes
    accept reject

theorem concrete_paired_recognizer_dovetail_total_then_raw_output_code_eq_stage_attempt_code
    (accept reject : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    (ConcretePairedRecognizerDovetailTotalThenRawOutputCode
      accept reject).transform tokens =
      (PairedRecognizerDovetailStageAttemptCode
        accept reject).transform tokens :=
  Computability.pairedRecognizerDovetailTotalThenRawOutputCode_eq_stageAttemptCode
    accept reject tokens

theorem concrete_cell_branch_description_subroutine_ready
    {stateCount source halt blankTarget falseTarget trueTarget : Nat}
    {move : Direction}
    (hpos : 0 < stateCount)
    (hsource : source < stateCount)
    (hhalt : halt < stateCount)
    (hblank : blankTarget < stateCount)
    (hfalse : falseTarget < stateCount)
    (htrue : trueTarget < stateCount)
    (hsourceNe : source ≠ halt) :
    (MachineDescription.cellBranchDescription stateCount source halt
      blankTarget falseTarget trueTarget move).SubroutineReady :=
  MachineDescription.cellBranchDescription_subroutineReady
    hpos hsource hhalt hblank hfalse htrue hsourceNe

theorem concrete_cell_branch_description_run_config_one_start
    (stateCount source halt blankTarget falseTarget trueTarget : Nat)
    (move : Direction) (T : Tape Bool) :
    (MachineDescription.cellBranchDescription stateCount source halt
      blankTarget falseTarget trueTarget move).runConfig 1
        { state := source, tape := T } =
      { state :=
          MachineDescription.cellBranchTarget (Tape.read T)
            blankTarget falseTarget trueTarget,
        tape := Tape.move move T } :=
  MachineDescription.cellBranchDescription_runConfig_one_start
    stateCount source halt blankTarget falseTarget trueTarget move T

theorem concrete_cell_branch_description_run_config_one_output_nil
    (stateCount source halt blankTarget falseTarget trueTarget : Nat)
    (move : Direction) :
    (MachineDescription.cellBranchDescription stateCount source halt
      blankTarget falseTarget trueTarget move).runConfig 1
        { state := source, tape := Tape.output ([] : Word Bool) } =
      { state := blankTarget,
        tape := Tape.move move (Tape.output ([] : Word Bool)) } :=
  MachineDescription.DovetailControllerLayout.cellBranchDescription_runConfig_one_output_nil
    stateCount source halt blankTarget falseTarget trueTarget move

theorem concrete_cell_branch_description_run_config_one_output_of_raw_output_eq_some
    (stateCount source halt blankTarget falseTarget trueTarget : Nat)
    (move : Direction) {result : Word Bool} {b : Bool}
    (hraw :
      PairedRecognizerDovetailControllerRawOutput result = some [b]) :
    (MachineDescription.cellBranchDescription stateCount source halt
      blankTarget falseTarget trueTarget move).runConfig 1
        { state := source, tape := Tape.output result } =
      { state := if b then trueTarget else falseTarget,
        tape := Tape.move move (Tape.output result) } :=
  MachineDescription.DovetailControllerLayout.cellBranchDescription_runConfig_one_output_of_rawOutput_eq_some
    stateCount source halt blankTarget falseTarget trueTarget move hraw

theorem concrete_fixed_description_step_code_output_realizer_of_configuration_realizer
    {D stepper : MachineDescription}
    (hstepper :
      FixedDescriptionStepCodeConfigurationRealizes D stepper) :
    TapeCodePrimitiveOutputRealizedByDescription
      (FixedDescriptionStepCode D) stepper :=
  Computability.fixedDescriptionStepCodeOutputRealizer_of_configurationRealizer
    hstepper

theorem concrete_fixed_description_step_code_output_realizer_construction_of_configuration_realizer_construction
    (hcompile :
      ConcreteFixedDescriptionStepCodeConfigurationRealizerConstruction) :
    ConcreteFixedDescriptionStepCodeOutputRealizerConstruction :=
  Computability.fixedDescriptionStepCodeOutputRealizerConstruction_of_configurationRealizerConstruction
    hcompile

theorem concrete_fixed_description_step_code_configuration_realizer_construction_of_output_realizer_construction
    (hcompile :
      ConcreteFixedDescriptionStepCodeOutputRealizerConstruction) :
    ConcreteFixedDescriptionStepCodeConfigurationRealizerConstruction :=
  Computability.fixedDescriptionStepCodeConfigurationRealizerConstruction_of_outputRealizerConstruction
    hcompile

theorem concrete_fixed_description_step_code_configuration_realizer_construction_iff_output_realizer_construction :
    ConcreteFixedDescriptionStepCodeConfigurationRealizerConstruction <->
      ConcreteFixedDescriptionStepCodeOutputRealizerConstruction :=
  Computability.fixedDescriptionStepCodeConfigurationRealizerConstruction_iff_outputRealizerConstruction

theorem concrete_fixed_description_step_code_configuration_realizes_transitionless
    {D : MachineDescription}
    (hD : D.transitions = []) :
    FixedDescriptionStepCodeConfigurationRealizes
      D MachineDescription.ExactIdentityDescription :=
  Computability.fixedDescriptionStepCodeConfigurationRealizes_transitionless
    hD

theorem concrete_fixed_description_step_code_configuration_realizes_exact_identity :
    FixedDescriptionStepCodeConfigurationRealizes
      MachineDescription.ExactIdentityDescription
      MachineDescription.ExactIdentityDescription :=
  Computability.fixedDescriptionStepCodeConfigurationRealizes_exactIdentityDescription

theorem concrete_tape_code_identity_compiled_by_description :
    TapeCodePrimitiveCompiledByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription :=
  Computability.tapeCodePrimitiveCompiledByDescription_identity

theorem concrete_tape_code_identity_output_realized_by_description :
    TapeCodePrimitiveOutputRealizedByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription :=
  Computability.tapeCodePrimitiveOutputRealizedByDescription_identity

theorem concrete_tape_code_erase_output_realized_by_description :
    TapeCodePrimitiveOutputRealizedByDescription
      MachineDescription.TapeCodePrimitive.erase
      MachineDescription.EraseRightDescription :=
  Computability.tapeCodePrimitiveOutputRealizedByDescription_erase

theorem concrete_tape_code_erase_not_exact_compiled_by_description :
    ¬ exists D : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        MachineDescription.TapeCodePrimitive.erase D :=
  Computability.not_tapeCodePrimitiveCompiledByDescription_erase

theorem concrete_tape_code_append_singleton_output_realized_by_description
    (symbol : MachineCodeSymbol) :
    TapeCodePrimitiveOutputRealizedByDescription
      (MachineDescription.TapeCodePrimitive.append [symbol])
      (MachineDescription.AppendCodeSymbolRightDescription symbol) :=
  Computability.tapeCodePrimitiveOutputRealizedByDescription_append_singleton
    symbol

theorem concrete_tape_code_compare_nat_eq_on_encoded_nat
    (target n : Nat) (suffix : Word MachineCodeSymbol) :
    (MachineDescription.TapeCodePrimitive.compareNatEq target).transform
        (MachineDescription.encodeNatAppend n suffix) =
      some (MachineDescription.encodeBoolAppend (n == target) suffix) :=
  MachineDescription.TapeCodePrimitive.compareNatEq_transform_encodeNatAppend
    target n suffix

theorem concrete_tape_code_compare_nat_lt_on_encoded_nat
    (bound n : Nat) (suffix : Word MachineCodeSymbol) :
    (MachineDescription.TapeCodePrimitive.compareNatLt bound).transform
        (MachineDescription.encodeNatAppend n suffix) =
      some
        (MachineDescription.encodeBoolAppend (decide (n < bound)) suffix) :=
  MachineDescription.TapeCodePrimitive.compareNatLt_transform_encodeNatAppend
    bound n suffix

theorem concrete_tape_code_write_move_on_encoded_tape
    (cell : Option Bool) (dir : Direction) (T : Tape Bool) :
    (MachineDescription.TapeCodePrimitive.writeMove cell dir).transform
        (MachineDescription.encodeTape T) =
      some
        (MachineDescription.encodeTape
          (Tape.move dir (Tape.write cell T))) :=
  MachineDescription.TapeCodePrimitive.writeMove_transform_encodeTape
    cell dir T

theorem concrete_tape_code_transition_action_on_lookup
    {D : MachineDescription} {c : MachineDescription.Configuration}
    {t : TransitionDescription}
    (hlookup :
      D.lookupTransition c.state (Tape.read c.tape) = some t) :
    (MachineDescription.TapeCodePrimitive.transitionTapeAction t).transform
        (MachineDescription.encodeTape c.tape) =
      some
        (MachineDescription.encodeTape (D.runConfig 1 c).tape) :=
  MachineDescription.TapeCodePrimitive.transitionTapeAction_transform_encodeTape_of_lookupTransition
    hlookup

theorem concrete_fixed_description_step_code_realizes
    (D : MachineDescription) :
    FixedDescriptionStepCodeRealizes D (FixedDescriptionStepCode D) :=
  Computability.fixedDescriptionStepCode_realizes D

theorem concrete_paired_recognizer_dovetail_layout_code_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailLayoutCodeRealizes
      accept reject
      (PairedRecognizerDovetailLayoutCode accept reject) :=
  Computability.pairedRecognizerDovetailLayoutCode_realizes accept reject

theorem concrete_paired_recognizer_dovetail_layout_initial_output
    (accept reject : MachineDescription)
    (w : Word Bool) (limit : Nat) :
    MachineDescription.DovetailLayout.outputFromHits
        (MachineDescription.DovetailLayout.run accept reject limit
          (MachineDescription.DovetailLayout.initial
            accept reject w limit)) =
      MachineDescription.boundedDovetailOutput accept reject w limit :=
  Computability.pairedRecognizerDovetailLayout_initial_output
    accept reject w limit


end Section02
end Chapter05
end Book
end FoC
