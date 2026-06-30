import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.PostPaddingConstruction

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

open CanonicalLayouts.DovetailLayoutScanner

def selectedProjectionPaddedTailCleanupRejectPrefixEraseDescription :
    MachineDescription :=
  seqSubroutine postPaddingOutputPrefixStageScannerDescription
    leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription
    Direction.right

theorem selectedProjectionPaddedTailCleanupRejectPrefixEraseDescription_subroutineReady :
    selectedProjectionPaddedTailCleanupRejectPrefixEraseDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    postPaddingOutputPrefixStageScannerDescription_subroutineReady
    leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription_subroutineReady

def selectedProjectionPaddedTailCleanupRejectGapHitToRightEndDescription :
    MachineDescription :=
  SeqViaCanonical
    (SeqViaCanonical rightMoveAcrossFourBlanksDescription
      rightEdgeScanDescription)
    rightMoveOnceDescription

theorem selectedProjectionPaddedTailCleanupRejectGapHitToRightEndDescription_subroutineReady :
    selectedProjectionPaddedTailCleanupRejectGapHitToRightEndDescription.SubroutineReady :=
  SeqViaCanonical_subroutineReady
    (SeqViaCanonical_subroutineReady
      rightMoveAcrossFourBlanksDescription_subroutineReady
      rightEdgeScanDescription_subroutineReady)
    rightMoveOnceDescription_subroutineReady

theorem rightEdgeScanSourceTapeFromLeft_move_left_move_right_cons
    (left padding : List (Option Bool)) (current : Bool)
    (rest : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rightEdgeScanSourceTapeFromLeft left (current :: rest)
            padding)) =
      rightEdgeScanSourceTapeFromLeft left (current :: rest) padding := by
  cases current <;> cases rest <;> cases padding <;>
    simp [rightEdgeScanSourceTapeFromLeft, tapeAtCells, Tape.move,
      Tape.moveLeft, Tape.moveRight]

theorem rightEdgeScanTargetTapeFromLeft_move_left_move_right_cons
    (left padding : List (Option Bool)) (current : Bool)
    (rest : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rightEdgeScanTargetTapeFromLeft left (current :: rest)
            padding)) =
      rightEdgeScanTargetTapeFromLeft left (current :: rest) padding := by
  cases hbits : (current :: rest).reverse with
  | nil =>
      simp at hbits
  | cons bit revRest =>
      cases padding <;>
        simp [rightEdgeScanTargetTapeFromLeft, tapeAtCells, Tape.move,
          Tape.moveLeft, Tape.moveRight, hbits]

theorem rightMoveOnceDescription_haltsFrom_rightEdgeScanTargetWithRight
    (left padding : List (Option Bool)) (current : Bool)
    (rest : Word Bool) :
    rightMoveOnceDescription.HaltsFromTape
      (rightEdgeScanTargetTapeFromLeft left (current :: rest) padding)
      (rightEndCompactionSourceTapeWithRightPadding
        (List.append left.reverse ((current :: rest).map some))
        padding) := by
  have hmove :=
    rightMoveOnceDescription_haltsFromTape
      (rightEdgeScanTargetTapeFromLeft left (current :: rest) padding)
  cases hbits : (current :: rest).reverse with
  | nil =>
      simp at hbits
  | cons bit revRest =>
      have hleft :
          (List.map some rest).reverse ++ some current :: left =
            some bit :: (List.map some revRest ++ left) := by
        have h :=
          congrArg
            (fun xs : Word Bool => List.append (xs.map some) left)
            hbits
        simpa [List.reverse_cons, List.map_append, List.append_assoc]
          using h
      cases padding <;>
        simp [rightEdgeScanTargetTapeFromLeft,
          rightEndCompactionSourceTapeWithRightPadding, tapeAtCells,
          Tape.move, Tape.moveLeft, Tape.moveRight, List.reverse_append,
          List.append_assoc, hbits] at hmove ⊢
      · rw [hleft]
        exact hmove
      · rw [hleft]
        exact hmove

theorem selectedProjectionPaddedTailCleanupRejectGapHitToRightEndDescription_haltsFrom_baseWithRight
    (leftCells : List (Option Bool)) (hitTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    selectedProjectionPaddedTailCleanupRejectGapHitToRightEndDescription.HaltsFromTape
      (rightEndCompactionSourceTapeWithRightPadding
        leftCells
        (List.append (List.replicate 3 (none : Option Bool))
          (List.append ((false :: hitTail).map some)
            (none :: rightPadding))))
      (rightEndCompactionSourceTapeWithRightPadding
        (List.append leftCells
          (List.append (List.replicate 4 (none : Option Bool))
            ((false :: hitTail).map some)))
        rightPadding) := by
  let scanLeft : List (Option Bool) :=
    List.append (List.replicate 4 (none : Option Bool))
      leftCells.reverse
  have hmove4 :
      rightMoveAcrossFourBlanksDescription.HaltsFromTape
        (rightEndCompactionSourceTapeWithRightPadding
          leftCells
          (List.append (List.replicate 3 (none : Option Bool))
            (List.append ((false :: hitTail).map some)
              (none :: rightPadding))))
        (rightEdgeScanSourceTapeFromLeft scanLeft
          (false :: hitTail) rightPadding) := by
    simpa [scanLeft, rightEndCompactionSourceTapeWithRightPadding,
      rightEdgeScanSourceTapeFromLeft, List.replicate_succ,
      List.append_assoc] using
      rightMoveAcrossFourBlanksDescription_haltsFromTape
        leftCells.reverse
        (List.append ((false :: hitTail).map some)
          (none :: rightPadding))
  have hscan :
      rightEdgeScanDescription.HaltsFromTape
        (rightEdgeScanSourceTapeFromLeft scanLeft
          (false :: hitTail) rightPadding)
        (rightEdgeScanTargetTapeFromLeft scanLeft
          (false :: hitTail) rightPadding) :=
    rightEdgeScanDescription_haltsFromTape scanLeft
      (false :: hitTail) rightPadding
  have hfirst :
      (SeqViaCanonical rightMoveAcrossFourBlanksDescription
        rightEdgeScanDescription).HaltsFromTape
        (rightEndCompactionSourceTapeWithRightPadding
          leftCells
          (List.append (List.replicate 3 (none : Option Bool))
            (List.append ((false :: hitTail).map some)
              (none :: rightPadding))))
        (rightEdgeScanTargetTapeFromLeft scanLeft
          (false :: hitTail) rightPadding) :=
    SeqViaCanonical_haltsFromTape_of_haltsFromTape
      rightMoveAcrossFourBlanksDescription_subroutineReady
      rightEdgeScanDescription_subroutineReady
      hmove4
      (rightEdgeScanSourceTapeFromLeft_move_left_move_right_cons
        scanLeft rightPadding false hitTail)
      hscan
  exact
    SeqViaCanonical_haltsFromTape_of_haltsFromTape
      (SeqViaCanonical_subroutineReady
        rightMoveAcrossFourBlanksDescription_subroutineReady
        rightEdgeScanDescription_subroutineReady)
      rightMoveOnceDescription_subroutineReady
      hfirst
      (rightEdgeScanTargetTapeFromLeft_move_left_move_right_cons
        scanLeft rightPadding false hitTail)
      (by
        have hright :=
          rightMoveOnceDescription_haltsFrom_rightEdgeScanTargetWithRight
            scanLeft rightPadding false hitTail
        simpa [scanLeft, List.reverse_append, List.append_assoc] using
          hright)

def selectedProjectionPaddedTailCleanupRejectEraseToRightEndDescription :
    MachineDescription :=
  seqSubroutine
    selectedProjectionPaddedTailCleanupRejectPrefixEraseDescription
    selectedProjectionPaddedTailCleanupRejectGapHitToRightEndDescription
    Direction.right

theorem selectedProjectionPaddedTailCleanupRejectEraseToRightEndDescription_subroutineReady :
    selectedProjectionPaddedTailCleanupRejectEraseToRightEndDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    selectedProjectionPaddedTailCleanupRejectPrefixEraseDescription_subroutineReady
    selectedProjectionPaddedTailCleanupRejectGapHitToRightEndDescription_subroutineReady

theorem selectedProjectionPaddedTailCleanupRejectPrefixEraseDescription_haltsFrom_sourceWithRight
    (L : DovetailLayout) (rightPadding : List (Option Bool)) :
    exists rejectTail : Word Bool,
    exists pref : Word Bool,
    exists leftBit : Bool,
      selectedProjectionPaddedTailCleanupPrefixBits L =
          List.append pref [leftBit] ∧
      configurationFieldBits L.rejectConfig [] =
          false :: rejectTail ∧
      selectedProjectionPaddedTailCleanupRejectPrefixEraseDescription.HaltsFromTape
        (tapeAtCells [none]
          (List.append
            (List.append
              (List.append
                ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
                ((configurationFieldBits L.acceptConfig []).map some))
              ((configurationFieldBits L.rejectConfig []).map some))
            (none :: rightPadding)))
        (rightBlankGapPayloadScanTargetTape
          (some leftBit :: List.append (pref.reverse.map some) [none])
          (configurationFieldBits L.acceptConfig []).length
          false rejectTail rightPadding) := by
  rcases selectedProjectionPaddedTailCleanupPrefix_append_last L with
    ⟨pref, leftBit, hpref⟩
  rcases configurationFieldBits_cons_false L.rejectConfig [] with
    ⟨rejectTail, hreject⟩
  rcases
      configurationFieldBits_cons_false
        L.acceptConfig (configurationFieldBits L.rejectConfig []) with
    ⟨fieldTail, hfieldTail⟩
  have hfieldAppend :
      List.append (configurationFieldBits L.acceptConfig [])
          (configurationFieldBits L.rejectConfig []) =
        false :: fieldTail := by
    rw [
      configurationFieldBits_append_nil
        L.acceptConfig (configurationFieldBits L.rejectConfig [])]
    exact hfieldTail
  have hfieldAppendMap :
      List.append ((configurationFieldBits L.acceptConfig []).map some)
          (List.append ((configurationFieldBits L.rejectConfig []).map some)
            (none :: rightPadding)) =
        some false :: List.append (fieldTail.map some)
          (none :: rightPadding) := by
    calc
      List.append ((configurationFieldBits L.acceptConfig []).map some)
          (List.append ((configurationFieldBits L.rejectConfig []).map some)
            (none :: rightPadding))
          =
        List.append
          (List.append ((configurationFieldBits L.acceptConfig []).map some)
            ((configurationFieldBits L.rejectConfig []).map some))
          (none :: rightPadding) := by
          simp [List.append_assoc]
      _ =
        List.append
          ((List.append (configurationFieldBits L.acceptConfig [])
            (configurationFieldBits L.rejectConfig [])).map some)
          (none :: rightPadding) := by
          simp [List.map_append]
      _ = some false :: List.append (fieldTail.map some)
          (none :: rightPadding) := by
          rw [hfieldAppend]
          simp
  refine ⟨rejectTail, pref, leftBit, hpref, hreject, ?_⟩
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      postPaddingOutputPrefixStageScannerDescription_subroutineReady
      leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription_subroutineReady
      (by
        have hraw :=
          postPaddingOutputPrefixStageScannerDescription_haltsFrom_raw_withRight
            (ParsedLayoutBits L) L.stage [none] fieldTail
            (none :: rightPadding)
        have hsource :
            tapeAtCells [none]
                (List.append
                  (List.append
                    (List.append
                      ((selectedProjectionPaddedTailCleanupPrefixBits L).map
                        some)
                      ((configurationFieldBits L.acceptConfig []).map some))
                    ((configurationFieldBits L.rejectConfig []).map some))
                  (none :: rightPadding)) =
              DovetailInitialLayoutInitializer.tapeAtCells [none]
                (List.append
                  ((encodeCodeSymbolAsInput MachineCodeSymbol.header).map
                    some)
                  (List.append
                    ((encodeCodeWordAsInput
                      (encodeBoolWordAppend (ParsedLayoutBits L) [])).map
                      some)
                    (List.append
                      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                        L.stage).map some)
                        (some false ::
                        List.append (fieldTail.map some)
                          (none :: rightPadding))))) := by
          have htail :=
            congrArg
              (fun tail : List (Option Bool) =>
                DovetailInitialLayoutInitializer.tapeAtCells [none]
                  (List.append
                    ((encodeCodeSymbolAsInput MachineCodeSymbol.header).map
                      some)
                    (List.append
                      ((encodeCodeWordAsInput
                        (encodeBoolWordAppend (ParsedLayoutBits L) [])).map
                        some)
                      (List.append
                        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                          L.stage).map some)
                        tail))))
              hfieldAppendMap
          simpa [DovetailInitialLayoutInitializer.tapeAtCells, tapeAtCells,
            selectedProjectionPaddedTailCleanupPrefixBits,
            SelectedProjectionTailProjector.outputPrefixBits,
            List.map_append, List.append_assoc] using htail
        rw [hsource]
        exact hraw)
      (by
        have hmove :=
          postPaddingOutputPrefixStageScannerTarget_move_right_eq_configSource_withRight
            (ParsedLayoutBits L) L.stage [none] fieldTail
            (none :: rightPadding)
        rw [postPaddingOutputPrefixAfterStageBase_eq_prefixBits_reverse] at hmove
        rw [hmove, ← hfieldTail, hreject, hpref]
        simp [DovetailInitialLayoutInitializer.tapeAtCells, tapeAtCells,
          List.reverse_append]
        rfl)
      (leftBoundaryBitConfigurationFieldEraseAndPayloadScanDescription_haltsFromTape
        leftBit L.acceptConfig
        (List.append (pref.reverse.map some) [none])
        rejectTail rightPadding)

theorem selectedProjectionPaddedTailCleanupRejectEraseToRightEndDescription_haltsFrom_sourceWithRight
    (L : DovetailLayout) (rightPadding : List (Option Bool)) :
    selectedProjectionPaddedTailCleanupRejectEraseToRightEndDescription.HaltsFromTape
      (tapeAtCells [none]
        (List.append
          (List.append
            (List.append
              ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
              ((configurationFieldBits L.acceptConfig []).map some))
            ((configurationFieldBits L.rejectConfig []).map some))
          (List.append (List.replicate 4 (none : Option Bool))
            (List.append
              ((selectedProjectionPaddedTailCleanupSelectedHitBits
                false L).map some)
              (none :: rightPadding)))))
      (rightEndCompactionSourceTapeWithRightPadding
        (selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells L)
        rightPadding) := by
  rcases cellFieldBits_cons_false (some L.rejectHit) [] with
    ⟨hitTail, hhitTail⟩
  have hhit :
      selectedProjectionPaddedTailCleanupSelectedHitBits false L =
        false :: hitTail := by
    simpa [selectedProjectionPaddedTailCleanupSelectedHitBits,
      boolFieldBits] using hhitTail
  have hhitBool :
      boolFieldBits L.rejectHit [] = false :: hitTail := by
    simpa [boolFieldBits] using hhitTail
  let tailPadding : List (Option Bool) :=
    List.append (List.replicate 3 (none : Option Bool))
      (List.append ((false :: hitTail).map some)
        (none :: rightPadding))
  rcases
      selectedProjectionPaddedTailCleanupRejectPrefixEraseDescription_haltsFrom_sourceWithRight
        L tailPadding with
    ⟨rejectTail, pref, leftBit, hpref, hreject, herase⟩
  let baseLeft : List (Option Bool) :=
    some leftBit :: List.append (pref.reverse.map some) [none]
  let erasedLeftCells : List (Option Bool) :=
    List.append baseLeft.reverse
      (List.append
        (List.replicate (configurationFieldBits L.acceptConfig []).length
          (none : Option Bool))
        ((false :: rejectTail).map some))
  have herase' :
      selectedProjectionPaddedTailCleanupRejectPrefixEraseDescription.HaltsFromTape
        (tapeAtCells [none]
          (List.append
            (List.append
              (List.append
                ((selectedProjectionPaddedTailCleanupPrefixBits L).map some)
                ((configurationFieldBits L.acceptConfig []).map some))
              ((configurationFieldBits L.rejectConfig []).map some))
            (List.append (List.replicate 4 (none : Option Bool))
              (List.append
                ((selectedProjectionPaddedTailCleanupSelectedHitBits
                  false L).map some)
                (none :: rightPadding)))))
        (rightBlankGapPayloadScanTargetTape
          baseLeft
          (configurationFieldBits L.acceptConfig []).length
          false rejectTail tailPadding) := by
    simpa [baseLeft, tailPadding, hhit, List.replicate_succ,
      List.append_assoc] using herase
  have hmove :
      Tape.move Direction.right
          (rightBlankGapPayloadScanTargetTape
            baseLeft
            (configurationFieldBits L.acceptConfig []).length
            false rejectTail tailPadding) =
        rightEndCompactionSourceTapeWithRightPadding
          erasedLeftCells tailPadding := by
    simpa [erasedLeftCells] using
      rightBlankGapPayloadScanTargetTape_move_right_eq_rightEndCompactionSourceTapeWithRightPadding
        baseLeft (configurationFieldBits L.acceptConfig []).length
        false rejectTail tailPadding
  have htargetLeft :
      List.append erasedLeftCells
          (List.append (List.replicate 4 (none : Option Bool))
            ((false :: hitTail).map some)) =
        selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells
          L := by
    simp [erasedLeftCells, baseLeft,
      selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells,
      selectedProjectionPaddedTailCleanupUnselectedConfigBits,
      selectedProjectionPaddedTailCleanupSelectedConfigBits,
      selectedProjectionPaddedTailCleanupSelectedHitBits,
      hpref, hreject, hhitBool, List.reverse_append, List.map_append,
      List.append_assoc]
  have htargetLeft_cons :
      erasedLeftCells ++
          none :: none :: none :: none :: some false ::
            hitTail.map some =
        selectedProjectionPaddedTailCleanupDeletedRejectRightEndLeftCells
          L := by
    simpa [List.replicate_succ, List.append_assoc] using htargetLeft
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      selectedProjectionPaddedTailCleanupRejectPrefixEraseDescription_subroutineReady
      selectedProjectionPaddedTailCleanupRejectGapHitToRightEndDescription_subroutineReady
      herase'
      hmove
      (by
        have hgap :=
          selectedProjectionPaddedTailCleanupRejectGapHitToRightEndDescription_haltsFrom_baseWithRight
            erasedLeftCells hitTail rightPadding
        simpa [tailPadding, htargetLeft_cons, List.append_assoc] using hgap)

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
