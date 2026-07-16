import FoC.Computability.Compiler.Core.BoundedTrace
import FoC.Computability.Compiler.Core.Closeout
import FoC.Computability.Compiler.Core.ConstructionTargets
import FoC.Computability.Compiler.Core.SearchDrivers

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter05
namespace Section02

/-!
# Section 5.2: Machine Compiler
-/

open Languages
open Computability

universe u v

/-!
## Code-Output Boundary

Exact tape output is intentionally separated from
normalized code output here.  The identity primitive satisfies both contracts,
while erasure is impossible for the exact tape-window contract but is realized
by a concrete finite normalized-output machine.

## Finite-Source Compiler Architecture

The finite compiler is organized around canonical Boolean encodings and
normalized output. Its primitive layer provides identity, erasure, fixed-symbol
append, singleton Boolean emission, unary comparison, and one-step tape actions.
These tables also have halt-transition-free subroutine packages, sequencing
lemmas, and cell-sensitive branch tables.

The fixed-description route parses an encoded configuration, performs one
lookup in a fixed description table, and emits the encoded successor.
Canonicalization lemmas lift the exact canonical-input construction to the
decoded-code contract
{name}`TapeCodePrimitiveOutputRealizedByDescription`. Iterating that stepper
supplies the bounded fixed-description simulator boundary used by the chapter.

The paired-recognizer route composes four finite layers: dovetail-layout
initialization, the bounded layout runner, a total single-stage attempt, and the
stage-loop controller. A no-hit attempt produces the empty Boolean word; an
accepting or rejecting hit produces the corresponding singleton word. The
controller preserves the encoded input and registers between stages, advances
the bound after no hit, and hands singleton results to the raw Boolean output
branches. The runner-search bridge packages this controller as the unbounded
paired-recognizer dovetailer.

Exact compilation of every code primitive is impossible because erasure cannot
produce an exact empty tape window from nonempty input. Normalized output is
therefore the common compiler currency. Generic principles that compile
arbitrary semantic staged programs remain explicit in theorem signatures;
concrete finite descriptions use the construction layers above directly.
-/

/-!
## Primitive Compiler Foundations

These bridges expose the bounded simulator, compiled subroutine, and basic
Boolean-output facts supplied by the reusable compiler core.
-/

theorem concrete_fixed_description_bounded_simulator_table_compiler_of_code_compiler
    (hcompile :
      FixedDescriptionBoundedSimulatorCodeCompilerConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction :=
  Computability.fixedDescriptionBoundedSimulatorTableCompiler_of_codeCompiler
    hcompile

theorem concrete_fixed_description_bounded_simulator_table_compiler_of_code_output_realizer
    (hcompile :
      FixedDescriptionBoundedSimulatorCodeOutputRealizerConstruction) :
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
    (MachineDescription.BoolOutputDescription b).WellFormed :=
  MachineDescription.boolOutputDescription_wellFormed b

theorem concrete_bool_output_description_haltTransitionFree (b : Bool) :
    (MachineDescription.BoolOutputDescription b).HaltTransitionFree :=
  MachineDescription.boolOutputDescription_haltTransitionFree b

theorem concrete_bool_output_description_haltsWithOutput
    (b : Bool) (w : Word Bool) :
    (MachineDescription.BoolOutputDescription b).HaltsWithOutput w [b] :=
  MachineDescription.boolOutputDescription_haltsWithOutput b w

theorem concrete_bool_output_description_haltsWithOutput_iff
    (b : Bool) (w out : Word Bool) :
    (MachineDescription.BoolOutputDescription b).HaltsWithOutput w out <-> out = [b] :=
  MachineDescription.boolOutputDescription_haltsWithOutput_iff b w out

theorem concrete_tape_code_exact_compiler_construction_impossible :
    ¬ MachineDescriptionTapeCodeExactCompilerConstruction :=
  Computability.not_machineDescriptionTapeCodeExactCompilerConstruction

def concrete_machine_description_compiler_closeout_of_tape_code_output_compiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    MachineDescriptionCompilerCloseout :=
  Computability.machineDescriptionCompilerCloseout_of_tapeCodeOutputCompiler
    hcompile

namespace ConcreteFixedDescriptionStepCode

namespace ConfigurationRealizerConstruction

theorem of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    FixedDescriptionStepCodeConfigurationRealizerConstruction :=
  Computability.fixedDescriptionStepCodeConfigurationRealizerConstruction_of_tapeCodeOutputCompiler
    hcompile

end ConfigurationRealizerConstruction

end ConcreteFixedDescriptionStepCode

theorem concrete_fixed_description_bounded_simulator_table_compiler_of_tape_code_output_compiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction :=
  Computability.fixedDescriptionBoundedSimulatorTableCompiler_of_tapeCodeOutputCompiler
    hcompile

/-!
## Dovetail Layout Realizers

Layout, initial-layout, result, and stage-attempt primitives share the same
normalized-output compiler boundary.
-/

theorem concrete_paired_recognizer_dovetail_layout_code_output_realizer_of_tape_code_output_compiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailLayoutCodeOutputRealizer_of_tapeCodeOutputCompiler
    hcompile

theorem concrete_paired_recognizer_dovetail_initial_layout_code_output_realizer_of_tape_code_output_compiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailInitialLayoutCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailInitialLayoutCodeOutputRealizer_of_tapeCodeOutputCompiler
    hcompile

theorem concrete_paired_recognizer_dovetail_output_code_output_realizer_of_tape_code_output_compiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailOutputCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailOutputCodeOutputRealizer_of_tapeCodeOutputCompiler
    hcompile

theorem concrete_paired_recognizer_dovetail_stage_attempt_code_output_realizer_of_tape_code_output_compiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailStageAttemptCodeOutputRealizer_of_tapeCodeOutputCompiler
    hcompile

namespace ConcretePairedRecognizerDovetail

namespace TotalStageAttemptCodeOutputRealizer

theorem of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailTotalStageAttemptCodeOutputRealizer_of_tapeCodeOutputCompiler
    hcompile

end TotalStageAttemptCodeOutputRealizer

namespace TotalThenRawOutputCodeOutputRealizer

theorem of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailTotalThenRawOutputCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailTotalThenRawOutputCodeOutputRealizer_of_tapeCodeOutputCompiler
    hcompile

end TotalThenRawOutputCodeOutputRealizer

namespace ControllerContinueCodeOutputRealizer

theorem of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailControllerContinueCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailControllerContinueCodeOutputRealizer_of_tapeCodeOutputCompiler
    hcompile

end ControllerContinueCodeOutputRealizer

namespace ControllerEmitCodeOutputRealizer

theorem of_tapeCodeOutputCompiler
    (hcompile : MachineDescriptionTapeCodeOutputCompilerConstruction) :
    PairedRecognizerDovetailControllerEmitCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailControllerEmitCodeOutputRealizer_of_tapeCodeOutputCompiler
    hcompile

end ControllerEmitCodeOutputRealizer

end ConcretePairedRecognizerDovetail

theorem concrete_paired_recognizer_dovetail_total_stage_attempt_code_output_realizer_of_subroutine_realizer
    (hcompile :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction) :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputRealizerConstruction :=
  Computability.pairedRecognizerDovetailTotalStageAttemptCodeOutputRealizer_of_subroutineRealizer
    hcompile

namespace ConcretePairedRecognizerDovetail

namespace StageAttemptCodeOutputRealizer

theorem of_totalThenRawOutput
    (hcompile :
      PairedRecognizerDovetailTotalThenRawOutputCodeOutputRealizerConstruction) :
    PairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction :=
  Computability.PairedRecognizerDovetail.StageAttemptCodeOutputRealizer.of_totalThenRawOutputConstruction
    hcompile

theorem of_totalStageAttemptOutput
    (hcompile :
      PairedRecognizerDovetailTotalStageAttemptCodeOutputRealizerConstruction) :
    PairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction :=
  Computability.Search.stageOutputConstructionOfTotal
    hcompile

end StageAttemptCodeOutputRealizer

end ConcretePairedRecognizerDovetail

/-!
## Controller Result Branches

The controller decodes a total stage result, distinguishes no-hit from
singleton Boolean hits, and routes each case through a finite code primitive.
-/

theorem concrete_paired_recognizer_dovetail_total_stage_attempt_code_controller_result_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailTotalStageAttemptControllerResultRealizes
      accept reject
      (PairedRecognizerDovetailTotalStageAttemptCode accept reject) :=
  Computability.pairedRecognizerDovetailTotalStageAttemptCode_controllerResultRealizes
    accept reject

theorem concrete_paired_recognizer_dovetail_total_stage_attempt_controller_raw_output_iff_of_output_compiled
    {accept reject attempt : MachineDescription}
    (hattempt :
      TapeCodePrimitiveOutputCompiledByDescription
        (PairedRecognizerDovetailTotalStageAttemptCode accept reject)
        attempt)
    (w : Word Bool) (limit : Nat) (b : Bool) :
    (exists result : Word Bool,
      attempt.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput
          (PairedRecognizerDovetailStageInputCode w limit))
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.encodeBoolWord result)) ∧
      PairedRecognizerDovetailControllerRawOutput result = some [b]) <->
    MachineDescription.boundedDovetailOutput accept reject w limit =
      some [b] :=
  Computability.pairedRecognizerDovetailTotalStageAttemptControllerRawOutput_iff_of_outputCompiled
    hattempt w limit b

theorem concrete_paired_recognizer_dovetail_controller_raw_output_code_realizes :
    PairedRecognizerDovetailControllerRawOutputCodeRealizes
      PairedRecognizerDovetailControllerRawOutputCode :=
  Computability.pairedRecognizerDovetailControllerRawOutputCode_realizes

theorem concrete_paired_recognizer_dovetail_controller_raw_output_code_eq_some_encodeBoolWord_singleton_iff
    {tokens : Word MachineCodeSymbol} {b : Bool} :
    PairedRecognizerDovetailControllerRawOutputCode.transform
        tokens =
        some (MachineDescription.encodeBoolWord [b]) <->
      MachineDescription.DovetailControllerLayout.decodeAttemptResultCode
        tokens = some [b] :=
  Computability.pairedRecognizerDovetailControllerRawOutputCode_eq_some_encodeBoolWord_singleton_iff

theorem concrete_paired_recognizer_dovetail_controller_raw_output_code_eq_some_self
    {code out : Word MachineCodeSymbol}
    (h :
      PairedRecognizerDovetailControllerRawOutputCode.transform
        code = some out) :
    out = code :=
  Computability.pairedRecognizerDovetailControllerRawOutputCode_eq_some_self h

theorem concrete_paired_recognizer_dovetail_controller_raw_output_code_output_realized_by_exact_identity :
    TapeCodePrimitiveOutputRealizedByDescription
      PairedRecognizerDovetailControllerRawOutputCode
      MachineDescription.ExactIdentityDescription :=
  Computability.pairedRecognizerDovetailControllerRawOutputCodeOutputRealizedByDescription

theorem concrete_paired_recognizer_dovetail_controller_continue_code_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailControllerContinueCodeRealizes
      accept reject
      (PairedRecognizerDovetailControllerContinueCode
        accept reject) :=
  Computability.pairedRecognizerDovetailControllerContinueCode_realizes
    accept reject

theorem concrete_paired_recognizer_dovetail_controller_emit_code_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailControllerEmitCodeRealizes
      accept reject
      (PairedRecognizerDovetailControllerEmitCode
        accept reject) :=
  Computability.pairedRecognizerDovetailControllerEmitCode_realizes
    accept reject

theorem concrete_paired_recognizer_dovetail_controller_continue_code_encode_eq_some_iff
    {accept reject : MachineDescription}
    {C : MachineDescription.DovetailControllerLayout}
    {out : Word MachineCodeSymbol} :
    (PairedRecognizerDovetailControllerContinueCode
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
    (PairedRecognizerDovetailControllerEmitCode
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
    (PairedRecognizerDovetailControllerEmitCode
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
      (PairedRecognizerDovetailControllerContinueCode
        accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
          some next)
    (hemit :
      (PairedRecognizerDovetailControllerEmitCode
        accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
          some out) :
    False :=
  Computability.pairedRecognizerDovetailControllerContinueEmitCode_exclusive
    hcontinue hemit

theorem concrete_paired_recognizer_dovetail_controller_continue_emit_code_branch
    (accept reject : MachineDescription)
    (C : MachineDescription.DovetailControllerLayout) :
    ((PairedRecognizerDovetailControllerContinueCode
        accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) =
        some
          (MachineDescription.DovetailControllerLayout.encode
            (MachineDescription.DovetailControllerLayout.nextStage C)) ∧
      (PairedRecognizerDovetailControllerEmitCode
        accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) = none) ∨
      ((PairedRecognizerDovetailControllerContinueCode
          accept reject).transform
        (MachineDescription.DovetailControllerLayout.encode C) = none ∧
        exists out : Word Bool,
          MachineDescription.boundedDovetailOutput
            accept reject C.input C.stage = some out ∧
            (PairedRecognizerDovetailControllerEmitCode
              accept reject).transform
              (MachineDescription.DovetailControllerLayout.encode C) =
                some (MachineDescription.encodeBoolWord out)) :=
  Computability.pairedRecognizerDovetailControllerContinueEmitCode_branch
    accept reject C

theorem concrete_paired_recognizer_dovetail_total_then_raw_output_code_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailStageAttemptCodeRealizes
      accept reject
      (PairedRecognizerDovetailTotalThenRawOutputCode
        accept reject) :=
  Computability.pairedRecognizerDovetailTotalThenRawOutputCode_realizes
    accept reject

theorem concrete_paired_recognizer_dovetail_total_then_raw_output_code_eq_stage_attempt_code
    (accept reject : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    (PairedRecognizerDovetailTotalThenRawOutputCode
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

/-!
## Fixed-Step Realizers

Canonical configuration realizers and normalized-output realizers are
equivalent interfaces for one fixed description step.
-/

theorem concrete_fixed_description_step_code_output_realizer_of_configuration_realizer
    {D stepper : MachineDescription}
    (hstepper :
      FixedDescriptionStepCodeConfigurationRealizes D stepper) :
    TapeCodePrimitiveOutputRealizedByDescription
      (FixedDescriptionStepCode D) stepper :=
  Computability.fixedDescriptionStepCodeOutputRealizer_of_configurationRealizer
    hstepper

namespace ConcreteFixedDescriptionStepCode

namespace OutputRealizerConstruction

theorem of_configurationRealizerConstruction
    (hcompile :
      FixedDescriptionStepCodeConfigurationRealizerConstruction) :
    FixedDescriptionStepCodeOutputRealizerConstruction :=
  Computability.fixedDescriptionStepCodeOutputRealizerConstruction_of_configurationRealizerConstruction
    hcompile

end OutputRealizerConstruction

namespace ConfigurationRealizerConstruction

theorem of_outputRealizerConstruction
    (hcompile :
      FixedDescriptionStepCodeOutputRealizerConstruction) :
    FixedDescriptionStepCodeConfigurationRealizerConstruction :=
  Computability.fixedDescriptionStepCodeConfigurationRealizerConstruction_of_outputRealizerConstruction
    hcompile

theorem iff_outputRealizerConstruction :
    FixedDescriptionStepCodeConfigurationRealizerConstruction <->
      FixedDescriptionStepCodeOutputRealizerConstruction :=
  Computability.fixedDescriptionStepCodeConfigurationRealizerConstruction_iff_outputRealizerConstruction

end ConfigurationRealizerConstruction

end ConcreteFixedDescriptionStepCode

/-!
## Concrete Primitive Closeouts

The final results instantiate the identity, erasure, append, comparison, and
transition-action primitives with checked finite descriptions.
-/

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
