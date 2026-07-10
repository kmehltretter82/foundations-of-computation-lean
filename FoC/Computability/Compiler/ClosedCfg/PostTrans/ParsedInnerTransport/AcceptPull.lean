import FoC.Computability.Compiler.ClosedCfg.PostTrans.ParsedInnerTransport.AcceptSchedule

set_option doc.verso true

/-!
# Parsed-inner accepting pull schedule

The accepting deletion pass leaves the selected output fields in separated
regions.  This module pulls them across the erased regions back to the
cell-zero sentinel.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace EncRewriters
namespace BoundedLayoutRunner
namespace ParsedInnerTransport

open CanonicalLayouts.DovetailLayoutScanner

theorem acceptAfterHitTape_move_left_firstPullShape
    (p : SelectedMergeEmitterPayload) :
    exists acTail stageTail : Word Bool,
    SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits p =
      false :: acTail ∧
    stageNatBits p.S.stage = false :: stageTail ∧
    Tape.move Direction.left (acceptAfterHitTape p) =
      tapeSeenLeft
        (List.append
          ((List.append
            (SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p).reverse
            (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).reverse).map
              some)
          (none ::
            List.append (List.replicate stageTail.length none)
              (some (!p.L.rejectHit) ::
                List.append ([p.L.rejectHit, true, false].map some)
                  (none ::
                    List.append
                      (List.replicate 3 none)
                      (List.append
                        ((SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).reverse.map
                          some)
                        (none ::
                          List.append
                            (List.replicate acTail.length none)
                            (List.append
                              ((SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).reverse.map
                                some)
                              [none])))))))
        commonRightPadding := by
  rcases
      configurationFieldBits_cons_false p.L.acceptConfig [] with
    ⟨acTail, hac⟩
  rcases stageNatBits_cons_false p.S.stage with ⟨stageTail, hstage⟩
  refine ⟨acTail, stageTail, ?_, ?_, ?_⟩
  · simpa [SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits] using hac
  · exact hstage
  · rw [acceptAfterHitTape, acceptAfterHitLeft,
      SelectedMergePaddedEmitterParsedInnerAcceptConfigFieldBits,
      hac, SelectedMergePaddedEmitterParsedInnerOuterStageFieldBits,
      hstage,
      SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits,
      SelectedMergePaddedEmitterParsedInnerRejectHitFieldBits,
      SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits,
      boolFieldBits_eq_four]
    simp [SelectedMergePaddedEmitterParsedInnerAcceptHitFieldBits,
      SelectedMergePaddedEmitterParsedInnerRejectHitFieldBits,
      SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits,
      boolFieldBits_eq_four, tapeSeenLeft,
      CommonGround.FiniteTransducers.tapeAtCells,
      commonRightPadding, Tape.move, Tape.moveLeft, List.map_append, List.map_reverse,
      List.reverse_append, List.replicate_succ, List.append_assoc]

def acceptAfterFirstPullTape
    (p : SelectedMergeEmitterPayload)
    (acTail stageTail : Word Bool) : Tape Bool :=
  tapeAtCells [none]
    (some (!p.L.rejectHit) ::
      none ::
        List.append
          ((SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).map some)
          (List.append (List.replicate acTail.length none)
            (none ::
              List.append
                ((SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).map some)
                (List.append (List.replicate 3 none)
                  (none ::
                    List.append ([false, true, p.L.rejectHit].map some)
                      (none ::
                        List.append (List.replicate stageTail.length none)
                          (none ::
                            List.append
                              ((List.append
                                (SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p).reverse
                                (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).reverse).reverse.map
                                  some)
                              commonRightPadding)))))))

theorem pullFirstAccept_haltsFrom
    (p : SelectedMergeEmitterPayload)
    (acTail stageTail : Word Bool)
    (hshape :
      Tape.move Direction.left (acceptAfterHitTape p) =
        tapeSeenLeft
          (List.append
            ((List.append
              (SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p).reverse
              (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).reverse).map
                some)
            (none ::
              List.append (List.replicate stageTail.length none)
                (some (!p.L.rejectHit) ::
                  List.append ([p.L.rejectHit, true, false].map some)
                    (none ::
                      List.append (List.replicate 3 none)
                        (List.append
                          ((SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).reverse.map
                            some)
                          (none ::
                            List.append (List.replicate acTail.length none)
                              (List.append
                                ((SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).reverse.map
                                  some)
                                [none])))))))
          commonRightPadding) :
    pullFirstAcceptDescription.HaltsFromTape
      (Tape.move Direction.left (acceptAfterHitTape p))
      (acceptAfterFirstPullTape p acTail stageTail) := by
  have hRC :
      SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p ≠ [] := by
    rcases configurationFieldBits_cons_false p.L.rejectConfig [] with
      ⟨tail, htail⟩
    intro h
    rw [SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits, htail] at h
    simp at h
  have hRCRev :
      (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).reverse ≠ [] := by
    intro h
    apply hRC
    unfold Word
    simpa using congrArg List.reverse h
  have hP :
      SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p ≠ [] := by
    rcases outputPrefixBits_cons p with ⟨tail, htail⟩
    intro h
    rw [htail] at h
    simp at h
  have hPRev :
      (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).reverse ≠ [] := by
    intro h
    apply hP
    unfold Word
    simpa using congrArg List.reverse h
  apply haltsFromTape_of_reaches
  rw [hshape]
  simpa [acceptAfterFirstPullTape, pullFirstAcceptDescription, List.map_reverse,
    List.reverse_append, List.append_assoc] using
    pullFirstAccept_run
      (List.append
        (SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p).reverse
        (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).reverse)
      stageTail.length
      (!p.L.rejectHit) [p.L.rejectHit, true, false]
      3
      (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).reverse hRCRev
      acTail.length
      (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).reverse hPRev
      commonRightPadding

def acceptJ2InputTape
    (p : SelectedMergeEmitterPayload) (acTail : Word Bool)
    (b1 : Bool) (blkT field : Word Bool)
    (R : List (Option Bool)) : Tape Bool :=
  tapeAtCells [none]
    (List.append ((b1 :: blkT).map some)
      (none ::
        List.append
          ((SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).map some)
          (none ::
            List.append (List.replicate acTail.length none)
              (List.append
                ((SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).map some)
                (none ::
                  List.append (List.replicate 3 none)
                    (List.append (field.map some) (none :: R)))))))

def acceptJ2OutputTape
    (p : SelectedMergeEmitterPayload) (acTail : Word Bool)
    (b1 : Bool) (blkT field : Word Bool)
    (x : Bool) (R : List (Option Bool)) : Tape Bool :=
  tapeAtCells [none]
    (some x ::
      List.append ((b1 :: blkT).map some)
        (none ::
          List.append
            ((SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).map some)
            (List.append (List.replicate acTail.length none)
              (none ::
                List.append
                  ((SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).map some)
                  (List.append (List.replicate 3 none)
                    (none ::
                      List.append (field.map some) (none :: none :: R)))))))

theorem acceptJ2_haltsFrom
    (p : SelectedMergeEmitterPayload) (acTail : Word Bool)
    (b1 : Bool) (blkT field : Word Bool)
    (x : Bool) (R : List (Option Bool)) :
    pullOneBitJ2Description.HaltsFromTape
      (acceptJ2InputTape p acTail b1 blkT (List.append field [x]) R)
      (acceptJ2OutputTape p acTail b1 blkT field x R) := by
  rcases outputPrefixBits_cons p with ⟨prefixTail, hprefix⟩
  rcases configurationFieldBits_cons_false p.L.rejectConfig [] with
    ⟨configTail, hconfig⟩
  apply haltsFromTape_of_reaches
  simpa [acceptJ2InputTape, acceptJ2OutputTape,
    hprefix, hconfig,
    SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits,
    pullOneBitJ2Description,
    replicate_none_comm', List.append_assoc] using
    pullOneBitJ2_run
      b1 blkT false prefixTail acTail.length false configTail
      3 field x R

end ParsedInnerTransport
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
