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

/-- The transition-scanner source has a nonempty left context, so the
same-head composition handoff cancels exactly. -/
theorem scannerStartTape_move_right_left
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
  rcases CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_inv
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
    exact MachineDescription.haltsFromTape_functional_of_haltTransitionFree
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

/-- Every canonical transition-scanner source either reaches its exact decoded
handoff or a contiguous concrete missing row in one of its two physical
subphases. -/
theorem haltsOrContiguousStuckFromTape
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) :
    (exists output : Tape Bool,
      Description.HaltsFromTape
        (validatorTransitionScannerStartTape
          stateCount start halt transitionCount tokens) output) ∨
    (exists stuck : Tape Bool,
      Description.StuckFromTape
          (validatorTransitionScannerStartTape
            stateCount start halt transitionCount tokens) stuck ∧
        ContiguousTape stuck) := by
  rcases ValidatorHeaderBounds.haltsOrContiguousStuckFromTape
      stateCount start halt transitionCount tokens with hheader | hheader
  · rcases hheader with ⟨_headerOutput, hheaderHalts⟩
    have hboundsBool :=
      ValidatorHeaderBounds.validatorHeaderBoundsBool_eq_true_of_haltsFromTape
        stateCount start halt transitionCount tokens hheaderHalts
    have hbounds := (validatorHeaderBoundsBool_eq_true_iff
      stateCount start halt).1 hboundsBool
    have hheaderExact : ValidatorHeaderBounds.Description.HaltsFromTape
        (validatorTransitionScannerStartTape
          stateCount start halt transitionCount tokens)
        (validatorTransitionScannerStartTape
          stateCount start halt transitionCount tokens) := by
      simpa [validatorHeaderBoundsHandoffTape] using
        ValidatorHeaderBounds.haltsFromTape_headerBoundsHandoff
          stateCount start halt transitionCount tokens
          hbounds.1 hbounds.2.1 hbounds.2.2
    rcases ValidatorCountedRows.haltsOrContiguousStuckFromTape
        stateCount start halt transitionCount tokens with hrows | hrows
    · rcases hrows with ⟨output, hrowsHalts⟩
      exact Or.inl ⟨output,
        CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
          ValidatorHeaderBounds.description_subroutineReady
          ValidatorCountedRows.description_subroutineReady
          hheaderExact
          (scannerStartTape_move_right_left
            stateCount start halt transitionCount tokens)
          hrowsHalts⟩
    · rcases hrows with ⟨stuck, hrowsStuck, hcontiguous⟩
      exact Or.inr ⟨stuck,
        CommonGround.SameHeadComposition.leftRightSeqDescription_stuckFromTape_of_right
          ValidatorHeaderBounds.description_subroutineReady
          ValidatorCountedRows.description_subroutineReady
          hheaderExact
          (scannerStartTape_move_right_left
            stateCount start halt transitionCount tokens)
          hrowsStuck,
        hcontiguous⟩
  · rcases hheader with ⟨stuck, hheaderStuck, hcontiguous⟩
    exact Or.inr ⟨stuck,
      CommonGround.SameHeadComposition.leftRightSeqDescription_stuckFromTape_of_left
        ValidatorHeaderBounds.description_subroutineReady
        ValidatorCountedRows.description_subroutineReady
        (by simpa [validatorHeaderBoundsHandoffTape] using hheaderStuck),
      hcontiguous⟩

/-- Every canonical transition-scanner source either reaches its exact decoded
handoff or a concrete missing row in one of its two physical subphases. -/
theorem haltsOrStuckFromTape
    (stateCount start halt transitionCount : Nat)
    (tokens : Word MachineCodeSymbol) :
    (exists output : Tape Bool,
      Description.HaltsFromTape
        (validatorTransitionScannerStartTape
          stateCount start halt transitionCount tokens) output) ∨
    (exists stuck : Tape Bool,
      Description.StuckFromTape
        (validatorTransitionScannerStartTape
          stateCount start halt transitionCount tokens) stuck) := by
  rcases haltsOrContiguousStuckFromTape
      stateCount start halt transitionCount tokens with hhalts | hstuck
  · exact Or.inl hhalts
  · rcases hstuck with ⟨stuck, hstuck, _hcontiguous⟩
    exact Or.inr ⟨stuck, hstuck⟩

end ValidatorTransitionScannerConstruction

end SelfHaltingRecognizer
end Computability
end FoC
