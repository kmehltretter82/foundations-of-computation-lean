import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.DiagonalSchedule
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.FusedLayoutEmission
import FoC.Computability.Compiler.Structured.Lowering.TypedStateRuns

set_option doc.verso true

/-!
# Shared rollover tape operations

Pure tape operations shared by the source- and checker-fuel rollover machines.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace BoundedFuelPairSearch
namespace RolloverTape

def back8Transform (T : Tape Bool) : Tape Bool :=
  let T := keepL.apply T
  let T := keepL.apply T
  let T := keepL.apply T
  let T := keepL.apply T
  let T := keepL.apply T
  let T := keepL.apply T
  let T := keepL.apply T
  keepL.apply T

def prefixBits (w : Word Bool) : Word Bool :=
  List.append (stageNatBits w.length) (cellsBits w)

theorem candidateCode_eq_fields
    (w : Word Bool) (limit candidateFuel : Nat) :
    CandidateCode w limit candidateFuel =
      List.append (encodeNat w.length)
        (List.append (encodeCellsAppend (w.map some) [])
          (List.append (encodeNat limit) (encodeNat candidateFuel))) := by
  unfold CandidateCode
  unfold PairedRecognizerDovetailControllerStageAttemptFuelInputCode
  unfold DovetailLayout.stageInputCodeAppend
  unfold encodeBoolWordAppend
  unfold encodeCellListAppend
  unfold encodeNatAppend
  simp only [List.length_map]
  have hcand :
      List.append (encodeNat candidateFuel) [] = encodeNat candidateFuel :=
    List.append_nil _
  rw [hcand]
  apply congrArg (List.append (encodeNat w.length))
  exact encodeCellsAppend_append (w.map some) []
    (List.append (encodeNat limit) (encodeNat candidateFuel))

theorem candidateInputBits_eq_fields
    (w : Word Bool) (limit candidateFuel : Nat) :
    CandidateInputBits w limit candidateFuel =
      List.append (prefixBits w)
        (List.append (stageNatBits limit) (stageNatBits candidateFuel)) := by
  have h :
      CandidateInputBits w limit candidateFuel =
        List.append (stageNatBits w.length)
          (List.append (cellsBits w)
            (List.append (stageNatBits limit)
              (stageNatBits candidateFuel))) := by
    unfold CandidateInputBits
    rw [candidateCode_eq_fields]
    rw [encodeCodeWordAsInput_append]
    rw [encodeCodeWordAsInput_append]
    rw [encodeCodeWordAsInput_append]
    rfl
  simpa [prefixBits, List.append_assoc] using h

def suffixCursorTape (pre : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append (pre.reverse.map some) [none])
    (List.append
      ((List.append (stageNatBits 0) (stageNatBits 0)).map some)
      [none])

theorem back8Transform_atEnd (pre : Word Bool) :
    back8Transform
        (tapeAtCells
          (List.append
            ((List.append pre
              (List.append (stageNatBits 0) (stageNatBits 0))).reverse.map some)
            [none])
          [none]) =
      suffixCursorTape pre := by
  simp [back8Transform, suffixCursorTape, List.map_reverse,
    List.reverse_append, tapeAtCells, keepL, TapeAction.apply,
    HeadMove.apply, Tape.move, Tape.moveLeft]

def rightWriteBits : Word Bool -> Tape Bool -> Tape Bool
  | [], T => T
  | bit :: rest, T =>
      rightWriteBits rest ((writeBitR bit).apply T)

def fuelDoneTransform (T : Tape Bool) : Tape Bool :=
  let T := (writeBitR false).apply T
  let T := (writeBitR false).apply T
  let T := (writeBitR true).apply T
  let T := (writeBitL true).apply T
  let T := keepL.apply T
  let T := keepL.apply T
  keepL.apply T

def outputDoneTransform (T : Tape Bool) : Tape Bool :=
  let T := (writeBitR false).apply T
  let T := (writeBitR false).apply T
  let T := (writeBitR true).apply T
  let T := (writeBitR true).apply T
  keepL.apply T

def leftScanTape (bits : List Bool)
    (right : List (Option Bool)) : Tape Bool :=
  match bits with
  | [] => tapeAtCells [] (none :: right)
  | bit :: rest =>
      tapeAtCells (List.append (rest.map some) [none])
        (some bit :: right)

theorem rightWriteBits_append
    (first second : Word Bool) (T : Tape Bool) :
    rightWriteBits (List.append first second) T =
      rightWriteBits second (rightWriteBits first T) := by
  induction first generalizing T with
  | nil => rfl
  | cons bit rest ih =>
      change
        rightWriteBits (List.append rest second)
            ((writeBitR bit).apply T) =
          rightWriteBits second
            (rightWriteBits rest ((writeBitR bit).apply T))
      exact ih _

theorem rightWriteBits_blank
    (bits : Word Bool) (left : List (Option Bool)) :
    rightWriteBits bits (tapeAtCells left [none]) =
      tapeAtCells
        (List.append (bits.reverse.map some) left) [none] := by
  induction bits generalizing left with
  | nil => rfl
  | cons bit rest ih =>
      simpa [rightWriteBits, List.map_reverse, List.append_assoc,
        tapeAtCells, writeBitR, writeR, TapeAction.apply,
        HeadMove.apply, Tape.write, Tape.move, Tape.moveRight] using
        ih (some bit :: left)

theorem rightWriteBits_overwrite_of_length_le
    (bits old : Word Bool) (left : List (Option Bool))
    (hlen : old.length ≤ bits.length) :
    rightWriteBits bits
        (tapeAtCells left
          (List.append (old.map some) [none])) =
      tapeAtCells
        (List.append (bits.reverse.map some) left) [none] := by
  induction bits generalizing old left with
  | nil =>
      cases old with
      | nil => rfl
      | cons bit rest => simp at hlen
  | cons bit rest ih =>
      cases old with
      | nil => exact rightWriteBits_blank (bit :: rest) left
      | cons oldBit oldRest =>
          have hrest : oldRest.length ≤ rest.length := by
            simpa using hlen
          have h := ih oldRest (some bit :: left) hrest
          have hstep :
              (writeBitR bit).apply
                  (tapeAtCells left
                    (List.append ((oldBit :: oldRest).map some) [none])) =
                tapeAtCells (some bit :: left)
                  (List.append (oldRest.map some) [none]) := by
            cases oldRest <;> rfl
          have hleft :
              List.append ((bit :: rest).reverse.map some) left =
                List.append (rest.reverse.map some) (some bit :: left) := by
            simp [List.map_reverse, List.append_assoc]
          rw [rightWriteBits, hstep]
          change
            rightWriteBits rest
                (tapeAtCells (some bit :: left)
                  (List.append (oldRest.map some) [none])) =
              tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left) [none]
          rw [hleft]
          exact h

theorem outputDoneTransform_fields
    (pre bits : Word Bool)
    (hlen :
      (List.append (stageNatBits 0) (stageNatBits 0)).length ≤
        (List.append bits (stageNatBits 0)).length) :
    outputDoneTransform (rightWriteBits bits (suffixCursorTape pre)) =
      leftScanTape
        ((List.append pre
          (List.append bits (stageNatBits 0))).reverse)
        [none] := by
  change
    keepL.apply
        (rightWriteBits (stageNatBits 0)
          (rightWriteBits bits (suffixCursorTape pre))) = _
  rw [← rightWriteBits_append]
  unfold suffixCursorTape
  rw [rightWriteBits_overwrite_of_length_le _ _ _ hlen]
  simp [leftScanTape, List.map_reverse, List.map_append,
    List.append_assoc, keepL, TapeAction.apply, HeadMove.apply,
    Tape.move, Tape.moveLeft, tapeAtCells]

def scanBlankTape (padding fuel : Nat)
    (left : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate (stageNatBits fuel).length none)
      (List.append (List.replicate padding none) left))
    [none]

def rolloverZeroTape (padding fuel : Nat)
    (left : List (Option Bool)) : Tape Bool :=
  fuelDoneTransform (scanBlankTape padding fuel left)

theorem fuelDoneTransform_equiv
    {T U : Tape Bool} (h : Tape.Equiv T U) :
    Tape.Equiv (fuelDoneTransform T) (fuelDoneTransform U) := by
  have h1 :=
    StructuredConstructionTargets.FusedLayoutEmission.tapeAction_apply_equiv
      (writeBitR false) h
  have h2 :=
    StructuredConstructionTargets.FusedLayoutEmission.tapeAction_apply_equiv
      (writeBitR false) h1
  have h3 :=
    StructuredConstructionTargets.FusedLayoutEmission.tapeAction_apply_equiv
      (writeBitR true) h2
  have h4 :=
    StructuredConstructionTargets.FusedLayoutEmission.tapeAction_apply_equiv
      (writeBitL true) h3
  have h5 :=
    StructuredConstructionTargets.FusedLayoutEmission.tapeAction_apply_equiv
      keepL h4
  have h6 :=
    StructuredConstructionTargets.FusedLayoutEmission.tapeAction_apply_equiv
      keepL h5
  have h7 :=
    StructuredConstructionTargets.FusedLayoutEmission.tapeAction_apply_equiv
      keepL h6
  simpa [fuelDoneTransform] using h7

theorem fuelDoneTransform_blank_eq_cursorZero :
    fuelDoneTransform Tape.blank =
      StructuredConstructionTargets.RawLayoutPreparation.cursorFuelSourceTape
        0 := by
  rfl

theorem scanBlankTape_replicate_equiv_blank
    (padding fuel count : Nat) :
    Tape.Equiv
      (scanBlankTape padding fuel (List.replicate count none))
      Tape.blank := by
  refine ⟨?_, rfl, rfl⟩
  change
    Tape.dropTrailingNone
        (List.append
          (List.replicate (stageNatBits fuel).length none)
          (List.append (List.replicate padding none)
            (List.replicate count none))) =
      Tape.dropTrailingNone []
  have htail := list_replicate_add_append
    (none : Option Bool) padding count []
  simp only [List.append_nil] at htail
  have hinner := congrArg
    (List.append
      (List.replicate (stageNatBits fuel).length (none : Option Bool)))
    htail.symm
  have hall := list_replicate_add_append
    (none : Option Bool) (stageNatBits fuel).length
    (padding + count) []
  simp only [List.append_nil] at hall
  have hrep := hinner.trans hall.symm
  have hdrop := congrArg Tape.dropTrailingNone hrep
  exact hdrop.trans
    (FoC.Computability.dropTrailingNone_replicate_none _)

theorem rolloverZeroTape_replicate_equiv_cursorZero
    (padding fuel count : Nat) :
    Tape.Equiv
      (rolloverZeroTape padding fuel (List.replicate count none))
      (StructuredConstructionTargets.RawLayoutPreparation.cursorFuelSourceTape
        0) := by
  have hblank := scanBlankTape_replicate_equiv_blank padding fuel count
  have h := fuelDoneTransform_equiv hblank
  rw [fuelDoneTransform_blank_eq_cursorZero] at h
  exact h

end RolloverTape
end BoundedFuelPairSearch

end Computability
end FoC
