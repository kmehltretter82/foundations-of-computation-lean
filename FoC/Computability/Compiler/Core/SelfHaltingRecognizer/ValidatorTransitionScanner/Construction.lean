import FoC.Computability.Compiler.Core.CommonGround.SameHeadComposition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.HeaderBoundsPhysical
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.CountedRowsPhysical
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.HeaderBoundsInversion
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorTransitionScanner.CountedRowsInversion

set_option doc.verso true

/-!
# Exact-code validator: transition-scanner construction

The fixed-header bound pass and counted-row pass share one exact physical head
position.  The common same-head sequential wrapper cancels the mandatory
subroutine handoff move, yielding one halt-stable Boolean description for the
complete leaf-3 success path.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer

open Languages
open MachineDescription

namespace ValidatorTransitionScannerConstruction

private theorem haltsFromTape_output_unique_of_haltFree
    {D : MachineDescription}
    (hhaltFree : D.HaltTransitionFree)
    {input first second : Tape Bool}
    (hfirst : D.HaltsFromTape input first)
    (hsecond : D.HaltsFromTape input second) :
    first = second := by
  rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape hfirst with
    ⟨firstSteps, hfirstRun⟩
  rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape hsecond with
    ⟨secondSteps, hsecondRun⟩
  by_cases hle : firstSteps ≤ secondSteps
  · have hsteps :
        secondSteps = firstSteps + (secondSteps - firstSteps) := by
      lia
    have hfirstLater :
        D.runConfig secondSteps { state := D.start, tape := input } =
          { state := D.halt, tape := first } := by
      rw [hsteps, MachineDescription.runConfig_add, hfirstRun]
      exact MachineDescription.runConfig_halt
        hhaltFree first (secondSteps - firstSteps)
    exact congrArg MachineDescription.Configuration.tape
      (hfirstLater.symm.trans hsecondRun)
  · have hle' : secondSteps ≤ firstSteps := Nat.le_of_not_ge hle
    have hsteps :
        firstSteps = secondSteps + (firstSteps - secondSteps) := by
      lia
    have hsecondLater :
        D.runConfig firstSteps { state := D.start, tape := input } =
          { state := D.halt, tape := second } := by
      rw [hsteps, MachineDescription.runConfig_add, hsecondRun]
      exact MachineDescription.runConfig_halt
        hhaltFree second (firstSteps - secondSteps)
    exact (congrArg MachineDescription.Configuration.tape
      (hsecondLater.symm.trans hfirstRun)).symm

private theorem leftRightSeqDescription_haltsFromTape_inv
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {input output : Tape Bool}
    (hseq :
      MachineDescription.HaltsFromTape
        (CommonGround.SameHeadComposition.leftRightSeqDescription A B)
        input output) :
    exists middle : Tape Bool,
      A.HaltsFromTape input middle ∧
        B.HaltsFromTape
          (Tape.move Direction.right (Tape.move Direction.left middle))
          output := by
  let identity := ExactIdentityDescription
  have hidentity : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  have hseq' :
      MachineDescription.HaltsFromTape
        (seqSubroutine
          (seqSubroutine A identity Direction.left) B Direction.right)
        input output := by
    simpa [CommonGround.SameHeadComposition.leftRightSeqDescription,
      identity] using hseq
  rcases seqSubroutine_haltsFromTape_closed_exists_mid
      (seqSubroutine_subroutineReady hA hidentity) hB hseq' with
    ⟨identityOutput, hAIdentity, hBhalt⟩
  rcases seqSubroutine_haltsFromTape_closed_exists_mid
      hA hidentity hAIdentity with
    ⟨middle, hAhalt, hIdentityHalt⟩
  have hIdentityCanonical :=
    CommonGround.Identity.exactIdentityDescription_haltsFromTape
      (Tape.move Direction.left middle)
  have hidentityOutput :
      identityOutput = Tape.move Direction.left middle :=
    haltsFromTape_output_unique_of_haltFree
      hidentity.2 hIdentityHalt hIdentityCanonical
  subst identityOutput
  exact ⟨middle, hAhalt, hBhalt⟩

/-- Complete finite description for the transition scan and all state bounds. -/
def Description : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    ValidatorHeaderBounds.Description ValidatorCountedRows.Description

/-- The composed transition scanner is well formed and halt-stable. -/
theorem description_subroutineReady : Description.SubroutineReady := by
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
      ValidatorHeaderBounds.description_subroutineReady
      ValidatorCountedRows.description_subroutineReady

private theorem scannerStartTape_move_right_left
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (validatorTransitionScannerStartTape
            stateCount start halt transitionCount tokens)) =
      validatorTransitionScannerStartTape
        stateCount start halt transitionCount tokens := by
  unfold validatorTransitionScannerStartTape
  unfold validatorHeaderFieldsHandoffTape
  exact
    CommonGround.FiniteTransducers.tapeAtCells_move_right_move_left_append_singleton
      (((encodeCodeWordAsInput
        (validatorHeaderFieldsPrefix
          stateCount start halt transitionCount)).reverse).map some)
      none
      (List.append ((encodeCodeWordAsInput tokens).map some) [none])

/-- Exact forward run on one counted encoded transition prefix. -/
theorem haltsFromTape_encoded
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription)
    (suffix : Word MachineCodeSymbol)
    (hpositive : 0 < stateCount)
    (hstart : start < stateCount)
    (hhalt : halt < stateCount)
    (hcount : transitionCount = rows.length)
    (hrows : forall row : TransitionDescription,
      row ∈ rows -> row.source < stateCount ∧ row.target < stateCount) :
    Description.HaltsFromTape
      (validatorTransitionScannerStartTape
        stateCount start halt transitionCount
        (encodeTransitionsAppend rows suffix))
      (validatorTransitionScannerHandoffTape
        stateCount start halt transitionCount rows suffix) := by
  apply
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
      ValidatorHeaderBounds.description_subroutineReady
      ValidatorCountedRows.description_subroutineReady
  · exact ValidatorHeaderBounds.haltsFromTape_headerBoundsHandoff
      stateCount start halt transitionCount
      (encodeTransitionsAppend rows suffix)
      hpositive hstart hhalt
  · exact scannerStartTape_move_right_left
      stateCount start halt transitionCount
      (encodeTransitionsAppend rows suffix)
  · exact ValidatorCountedRows.haltsFromTape_transitionScannerRows
      stateCount start halt transitionCount rows suffix hcount hrows

/-- Every semantically accepted counted prefix has an exact finite-machine run. -/
theorem haltsFromTape_of_accepts
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol)
    (haccept : ValidatorTransitionScanAccepts
      stateCount start halt transitionCount tokens) :
    exists rows : List TransitionDescription,
    exists suffix : Word MachineCodeSymbol,
      decodeTransitions transitionCount tokens = some (rows, suffix) ∧
        Description.HaltsFromTape
          (validatorTransitionScannerStartTape
            stateCount start halt transitionCount tokens)
          (validatorTransitionScannerHandoffTape
            stateCount start halt transitionCount rows suffix) := by
  rcases
      (validatorTransitionScanAccepts_iff_exists_encoded
        stateCount start halt transitionCount tokens).mp haccept with
    ⟨rows, suffix, hcount, htokens, hbounds⟩
  rcases
      (validatorStateBoundsBool_eq_true_iff
        stateCount start halt rows).mp hbounds with
    ⟨hpositive, hstart, hhalt, hrows⟩
  subst tokens
  refine ⟨rows, suffix, ?_, ?_⟩
  · rw [hcount]
    exact decodeTransitions_encodeTransitions_append rows suffix
  · exact haltsFromTape_encoded
      stateCount start halt transitionCount rows suffix
      hpositive hstart hhalt hcount hrows

/-- Any halt of the concrete transition scanner certifies its complete
semantic acceptance predicate. -/
theorem accepts_of_haltsFromTape
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol)
    {output : Tape Bool}
    (hhalts : Description.HaltsFromTape
      (validatorTransitionScannerStartTape
        stateCount start halt transitionCount tokens)
      output) :
    ValidatorTransitionScanAccepts
      stateCount start halt transitionCount tokens := by
  rcases leftRightSeqDescription_haltsFromTape_inv
      ValidatorHeaderBounds.description_subroutineReady
      ValidatorCountedRows.description_subroutineReady hhalts with
    ⟨middle, hheader, hcounted⟩
  have hheaderBool :=
    ValidatorHeaderBounds.validatorHeaderBoundsBool_eq_true_of_haltsFromTape
      stateCount start halt transitionCount tokens hheader
  have hheaderBounds :=
    (validatorHeaderBoundsBool_eq_true_iff stateCount start halt).mp
      hheaderBool
  have hheaderCanonical :=
    ValidatorHeaderBounds.haltsFromTape_headerBoundsHandoff
      stateCount start halt transitionCount tokens
      hheaderBounds.1 hheaderBounds.2.1 hheaderBounds.2.2
  have hmiddle :
      middle = validatorTransitionScannerStartTape
        stateCount start halt transitionCount tokens := by
    change middle = validatorHeaderBoundsHandoffTape
      stateCount start halt transitionCount tokens
    exact haltsFromTape_output_unique_of_haltFree
      ValidatorHeaderBounds.description_subroutineReady.2
      hheader hheaderCanonical
  subst middle
  rw [scannerStartTape_move_right_left] at hcounted
  rcases ValidatorCountedRows.exists_bounded_rows_of_haltsFromTape
      stateCount start halt transitionCount tokens hcounted with
    ⟨rows, suffix, hdecode, hrows⟩
  refine ⟨rows, suffix, hdecode, ?_⟩
  apply (validatorStateBoundsBool_eq_true_iff
    stateCount start halt rows).2
  exact
    ⟨hheaderBounds.1, hheaderBounds.2.1, hheaderBounds.2.2,
      fun row hrow => by
        simpa [TransitionDescription.WellFormed] using hrows row hrow⟩

/-- The concrete transition scanner halts on exactly its semantic language. -/
theorem exists_haltsFromTape_iff_accepts
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) :
    (exists output : Tape Bool,
      Description.HaltsFromTape
        (validatorTransitionScannerStartTape
          stateCount start halt transitionCount tokens)
        output) <->
      ValidatorTransitionScanAccepts
        stateCount start halt transitionCount tokens := by
  constructor
  · rintro ⟨output, hhalts⟩
    exact accepts_of_haltsFromTape
      stateCount start halt transitionCount tokens hhalts
  · intro haccept
    rcases haltsFromTape_of_accepts
        stateCount start halt transitionCount tokens haccept with
      ⟨rows, suffix, _hdecode, hhalts⟩
    exact ⟨validatorTransitionScannerHandoffTape
      stateCount start halt transitionCount rows suffix, hhalts⟩

end ValidatorTransitionScannerConstruction

end SelfHaltingRecognizer
end Computability
end FoC
