import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.TerminalCore.Rewind
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedParser.Return

set_option doc.verso true

/-!
# Padded simulator terminal construction contracts

This module contains the terminal construction-family contracts and the adapter
lemmas that compose the terminal source, field-FST target, FST target,
right-scratch, and final body layers.  The pure terminal tape-shape facts stay in
{module}`FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.TerminalCore.Core`.
The terminal rewind finite-machine construction stays in
{module}`FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Simulator.PaddedEmitter.TerminalCore.Rewind`.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

def FixedDescriptionBoundedSimulatorPaddedEmitterBodySpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterBodyConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterBodySpec_configRunner D body

def FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceSpec_configRunner
    (D afterRight : MachineDescription) : Prop :=
  afterRight.SubroutineReady ∧
    forall L : SimulatorLayout,
      afterRight.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists afterRight : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceSpec_configRunner
        D afterRight

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTape
        (CommonGround.FiniteTransducers.FSTSourceTape
          (SimulatorLayout.asBoolInput L) 1)
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L))

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetSpec_configRunner
        D body

def FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceSpec_configRunner
    (D rightBody : MachineDescription) : Prop :=
  rightBody.SubroutineReady ∧
    forall L : SimulatorLayout,
      rightBody.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L)
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L))

def FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists rightBody : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceSpec_configRunner
        D rightBody

def FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L)
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterFieldOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L))

def FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceSpec_configRunner
        D body

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTape
        (CommonGround.FiniteTransducers.FSTSourceTape
          (SimulatorLayout.asBoolInput L) 1)
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L))

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetSpec_configRunner
        D body

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalSourceSpec_configRunner
    (D body : MachineDescription) : Prop :=
  body.SubroutineReady ∧
    forall L : SimulatorLayout,
      body.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
          L)
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L))

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalSourceConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists body : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalSourceSpec_configRunner
        D body

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalRightShiftedSourceSpec_configRunner
    (D rightBody : MachineDescription) : Prop :=
  rightBody.SubroutineReady ∧
    forall L : SimulatorLayout,
      rightBody.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L)
        (CommonGround.FiniteTransducers.FSTTargetTape
          (FixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_configRunner
            D L)
          (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L))

def FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalRightShiftedSourceConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists rightBody : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalRightShiftedSourceSpec_configRunner
        D rightBody

def FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceSpec_configRunner
    (D rightBody : MachineDescription) : Prop :=
  rightBody.SubroutineReady ∧
    forall L : SimulatorLayout,
      rightBody.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists rightBody : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceSpec_configRunner
        D rightBody

def FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreSpec_configRunner
    (D post : MachineDescription) : Prop :=
  post.SubroutineReady ∧
    forall explicitLeftBlank : Bool,
    forall L : SimulatorLayout,
      post.HaltsFromTape
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalTape_configRunner
          explicitLeftBlank L)
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
          D L)

def FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists post : MachineDescription,
      FixedDescriptionBoundedSimulatorPaddedScratchEmitterTerminalCoreSpec_configRunner
        D post

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_move_left_move_right_configRunner
    (L : SimulatorLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
            L)) =
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
        L := by
  have hlen : 1 <= (SimulatorLayout.asBoolInput L).length := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput]
  cases hbits : SimulatorLayout.asBoolInput L with
  | nil =>
      simp [hbits] at hlen
  | cons first rest =>
      cases rest with
      | nil =>
          cases first <;>
            simp [
              fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
              DovetailInitialLayoutInitializer.tapeAtCells,
              Tape.move, Tape.moveLeft, Tape.moveRight, hbits]
      | cons second tail =>
          cases first <;> cases second <;>
            simp [
              fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
              DovetailInitialLayoutInitializer.tapeAtCells,
              Tape.move, Tape.moveLeft, Tape.moveRight, hbits]

theorem fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_haltsFrom_terminalSource_configRunner
    (L : SimulatorLayout) :
    FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.HaltsFromTape
      (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
        L)
      (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
        L) := by
  have hlen : 2 <= (SimulatorLayout.asBoolInput L).length := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput]
  cases hbits : SimulatorLayout.asBoolInput L with
  | nil =>
      simp [hbits] at hlen
  | cons first rest =>
      cases rest with
      | nil =>
          simp [hbits] at hlen
      | cons second tail =>
          refine ⟨3, ?_⟩
          constructor
          · cases tail <;> cases first <;> cases second <;>
              simp [
                fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
                FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
                DovetailInitialLayoutInitializer.tapeAtCells,
                runConfig, stepConfig, lookupTransition, Matches,
                DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
                transition, Tape.read, Tape.write, Tape.move,
                Tape.moveLeft, Tape.moveRight, hbits]
          · cases tail <;> cases first <;> cases second <;>
              simp [
                fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner,
                fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
                FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner,
                DovetailInitialLayoutInitializer.tapeAtCells,
                runConfig, stepConfig, lookupTransition, Matches,
                DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
                transition, Tape.read, Tape.write, Tape.move,
                Tape.moveLeft, Tape.moveRight, hbits]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_move_left_move_right_configRunner
    (L : SimulatorLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
            L)) =
      fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
        L := by
  have hlen : 2 <= (SimulatorLayout.asBoolInput L).length := by
    rw [fixedDescriptionBoundedSimulatorLayout_asBoolInput_eq_header_payloadBits_configRunner]
    simp [fixedDescriptionBoundedSimulatorHeaderPrefixBits_configRunner,
      encodeCodeSymbolAsInput]
  cases hbits : SimulatorLayout.asBoolInput L with
  | nil =>
      simp [hbits] at hlen
  | cons first rest =>
      cases rest with
      | nil =>
          simp [hbits] at hlen
      | cons second tail =>
          cases tail <;> cases first <;> cases second <;>
            simp [
              fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner,
              fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner,
              DovetailInitialLayoutInitializer.tapeAtCells,
              Tape.move, Tape.moveLeft, Tape.moveRight, hbits]

theorem fixedDescriptionBoundedSimulatorPaddedEmitterBodyConstruction_of_afterTerminalRightShiftedSource_configRunner
    (hafterRight :
      FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterBodyConstruction_configRunner := by
  intro D
  rcases hafterRight D with ⟨afterRight, hafterRightD⟩
  refine
    ⟨SeqViaCanonical
      FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner
      afterRight, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner
        hafterRightD.left
  · intro L
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner
        hafterRightD.left
        (fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_haltsFrom_terminalSource_configRunner
          L)
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_move_left_move_right_configRunner
          L)
        (hafterRightD.right L)

def fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchCloseout_configRunner
    (rightBody : MachineDescription) : MachineDescription :=
  seqSubroutine rightBody ExactIdentityDescription Direction.left

theorem fixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceConstruction_of_rightScratch_configRunner
    (hright :
      FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterAfterTerminalRightShiftedSourceConstruction_configRunner := by
  intro D
  rcases hright D with ⟨rightBody, hrightD⟩
  refine
    ⟨fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchCloseout_configRunner
      rightBody, ?_⟩
  constructor
  · exact
      seqSubroutine_subroutineReady
        hrightD.left
        CommonGround.Identity.exactIdentityDescription_subroutineReady
  · intro L
    have hidentity :
        exists nB : Nat,
          ExactIdentityDescription.runConfig nB
              { state := ExactIdentityDescription.start,
                tape :=
                  Tape.move Direction.left
                    (FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
                      D L) } =
            { state := ExactIdentityDescription.halt,
              tape :=
                FixedDescriptionBoundedSimulatorPaddedEmitterScratchTape_configRunner
                  D L } := by
      simpa [
        fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_move_left_configRunner
          D L] using
        CommonGround.Identity.exactIdentityDescription_run_from_start
          (Tape.move Direction.left
            (FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_configRunner
              D L))
    simpa [fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchCloseout_configRunner] using
      seqSubroutine_haltsFromTape_of_haltsFromTape
        hrightD.left
        CommonGround.Identity.exactIdentityDescription_subroutineReady
        (hrightD.right L)
        hidentity

theorem fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceConstruction_of_FSTTarget_configRunner
    (hfst :
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalRightShiftedSourceConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterRightScratchFromTerminalRightShiftedSourceConstruction_configRunner := by
  intro D
  rcases hfst D with ⟨rightBody, hrightBody⟩
  refine ⟨rightBody, hrightBody.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterRightScratchTape_eq_FSTTargetTape_configRunner
      D L] using
    hrightBody.right L

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalRightShiftedSourceConstruction_of_source_configRunner
    (hsource :
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalSourceConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalRightShiftedSourceConstruction_configRunner := by
  intro D
  rcases hsource D with ⟨body, hbody⟩
  refine ⟨seqSubroutine ExactIdentityDescription body Direction.left, ?_⟩
  constructor
  · exact
      seqSubroutine_subroutineReady
        CommonGround.Identity.exactIdentityDescription_subroutineReady
        hbody.left
  · intro L
    have hidentityRun :=
      CommonGround.Identity.exactIdentityDescription_run_from_start
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
          L)
    have hidentity :
        ExactIdentityDescription.HaltsFromTape
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
            L)
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
            L) := by
      rcases hidentityRun with ⟨n, hn⟩
      exact ⟨n, by
        constructor
        · exact congrArg Configuration.state hn
        · exact congrArg Configuration.tape hn⟩
    have hleft :
        Tape.move Direction.left
            (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
              L) =
          fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
            L := by
      rw [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner]
      exact
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_move_left_move_right_configRunner
          L
    exact
      seqSubroutine_haltsFromTape_of_haltsFromTape
        CommonGround.Identity.exactIdentityDescription_subroutineReady
        hbody.left
        hidentity
        (by
          rw [hleft]
          exact runConfig_eq_halt_of_haltsFromTape (hbody.right L))

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalSourceConstruction_of_FSTSource_configRunner
    (hfst :
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTTargetFromTerminalSourceConstruction_configRunner := by
  intro D
  rcases hfst D with ⟨body, hbody⟩
  refine ⟨body, hbody.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_eq_FSTSourceTape_configRunner
      L] using
    hbody.right L

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetConstruction_of_fields_configRunner
    (hfields :
      FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFSTTargetConstruction_configRunner := by
  intro D
  rcases hfields D with ⟨body, hbody⟩
  refine ⟨body, hbody.left, ?_⟩
  intro L
  simpa [
    fixedDescriptionBoundedSimulatorPaddedEmitterOutputBits_eq_fieldOutputBits_configRunner
      D L] using
    hbody.right L

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetConstruction_of_rightShiftedFields_configRunner
    (hright :
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFSTSourceToFieldFSTTargetConstruction_configRunner := by
  intro D
  rcases hright D with ⟨rightBody, hrightBody⟩
  refine
    ⟨SeqViaCanonical
      FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner
      rightBody, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner
        hrightBody.left
  · intro L
    have hreturn :
        FixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_configRunner.HaltsFromTape
          (CommonGround.FiniteTransducers.FSTSourceTape
            (SimulatorLayout.asBoolInput L) 1)
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
            L) := by
      simpa [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_eq_FSTSourceTape_configRunner
          L] using
        fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_haltsFrom_terminalSource_configRunner
          L
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        fixedDescriptionBoundedSimulatorReturnToRightShiftedInputDescription_subroutineReady_configRunner
        hrightBody.left
        hreturn
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_move_left_move_right_configRunner
          L)
        (hrightBody.right L)

theorem fixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceConstruction_of_sourceFields_configRunner
    (hsource :
      FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalSourceConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorPaddedEmitterFieldFSTTargetFromTerminalRightShiftedSourceConstruction_configRunner := by
  intro D
  rcases hsource D with ⟨body, hbody⟩
  refine
    ⟨SeqViaCanonical
      CommonGround.FiniteTransducers.leftMoveOnceDescription
      body, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        CommonGround.FiniteTransducers.leftMoveOnceDescription_subroutineReady
        hbody.left
  · intro L
    have hleft :
        CommonGround.FiniteTransducers.leftMoveOnceDescription.HaltsFromTape
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
            L)
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_configRunner
            L) := by
      simpa [
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner,
        fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_move_left_move_right_configRunner
          L] using
        CommonGround.FiniteTransducers.leftMoveOnceDescription_haltsFromTape
          (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalRightShiftedSourceTape_configRunner
            L)
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        CommonGround.FiniteTransducers.leftMoveOnceDescription_subroutineReady
        hbody.left
        hleft
        (fixedDescriptionBoundedSimulatorPaddedEmitterTerminalSourceTape_move_left_move_right_configRunner
          L)
        (hbody.right L)

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
