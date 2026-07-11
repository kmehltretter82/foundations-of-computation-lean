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

@[irreducible] def acceptThroughFirstPullDescription : MachineDescription :=
  seqSubroutine acceptDeleteDescription pullFirstAcceptDescription Direction.left

theorem acceptThroughFirstPullDescription_subroutineReady :
    acceptThroughFirstPullDescription.SubroutineReady := by
  unfold acceptThroughFirstPullDescription
  exact seqSubroutine_subroutineReady
    acceptDeleteDescription_subroutineReady
    pullFirstAcceptDescription_subroutineReady

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
    simp [boolFieldBits_eq_four, tapeSeenLeft,
      CommonGround.FiniteTransducers.tapeAtCells,
      commonRightPadding, Tape.move, Tape.moveLeft, List.map_reverse,
      List.replicate_succ]

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

theorem acceptThroughFirstPullDescription_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    exists acTail stageTail : Word Bool,
      acceptThroughFirstPullDescription.HaltsFromTape
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
        (acceptAfterFirstPullTape p acTail stageTail) := by
  unfold acceptThroughFirstPullDescription
  rcases acceptAfterHitTape_move_left_firstPullShape p with
    ⟨acTail, stageTail, _hac, _hstage, hshape⟩
  refine ⟨acTail, stageTail, ?_⟩
  have hfirst := pullFirstAccept_haltsFrom p acTail stageTail hshape
  rw [hshape] at hfirst
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      acceptDeleteDescription_subroutineReady
      pullFirstAcceptDescription_subroutineReady
      (acceptDeleteDescription_haltsFrom p)
      hshape
      hfirst

def acceptJ2InputTape
    (p : SelectedMergeEmitterPayload) (acTail : Word Bool)
    (b1 : Bool) (blkT field : Word Bool)
    (g2 : Nat) (R : List (Option Bool)) : Tape Bool :=
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
                  List.append (List.replicate g2 none)
                    (List.append (field.map some) (none :: R)))))))

def acceptJ2OutputTape
    (p : SelectedMergeEmitterPayload) (acTail : Word Bool)
    (b1 : Bool) (blkT field : Word Bool)
    (g2 : Nat) (x : Bool) (R : List (Option Bool)) : Tape Bool :=
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
                  (List.append (List.replicate g2 none)
                    (none ::
                      List.append (field.map some) (none :: none :: R)))))))

theorem acceptJ2_haltsFrom
    (p : SelectedMergeEmitterPayload) (acTail : Word Bool)
    (b1 : Bool) (blkT field : Word Bool)
    (g2 : Nat) (x : Bool) (R : List (Option Bool)) :
    pullOneBitJ2Description.HaltsFromTape
      (acceptJ2InputTape p acTail b1 blkT (List.append field [x]) g2 R)
      (acceptJ2OutputTape p acTail b1 blkT field g2 x R) := by
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
      g2 field x R

theorem acceptJ2OutputTape_eq_nextInput
    (p : SelectedMergeEmitterPayload) (acTail : Word Bool)
    (b1 : Bool) (blkT field : Word Bool)
    (g2 : Nat) (x y : Bool) (R : List (Option Bool)) :
    acceptJ2OutputTape p acTail b1 blkT (List.append field [x]) g2 y R =
      acceptJ2InputTape p acTail y (b1 :: blkT)
        (List.append field [x]) g2 (none :: R) := by
  simp [acceptJ2InputTape, acceptJ2OutputTape,
    replicate_none_comm', List.append_assoc]

theorem acceptJ2OutputTape_canonicalBridge
    (p : SelectedMergeEmitterPayload) (acTail : Word Bool)
    (b1 : Bool) (blkT field : Word Bool)
    (g2 : Nat) (x y : Bool) (R : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (acceptJ2OutputTape p acTail b1 blkT
            (List.append field [x]) g2 y R)) =
      acceptJ2InputTape p acTail y (b1 :: blkT)
        (List.append field [x]) g2 (none :: R) := by
  rw [show
      Tape.move Direction.left
          (Tape.move Direction.right
            (acceptJ2OutputTape p acTail b1 blkT
              (List.append field [x]) g2 y R)) =
        acceptJ2OutputTape p acTail b1 blkT
          (List.append field [x]) g2 y R by
    simp [acceptJ2OutputTape,
      CommonGround.FiniteTransducers.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]]
  exact acceptJ2OutputTape_eq_nextInput p acTail b1 blkT field g2 x y R

def acceptAfterRejectHitPullRight
    (p : SelectedMergeEmitterPayload) (stageTail : Word Bool) :
    List (Option Bool) :=
  List.append (List.replicate stageTail.length none)
    (none ::
      List.append
        ((List.append
          (SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits p).reverse
          (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).reverse).reverse.map
            some)
        commonRightPadding)

theorem acceptAfterFirstPullTape_eq_j2Input
    (p : SelectedMergeEmitterPayload) (acTail stageTail : Word Bool) :
    acceptAfterFirstPullTape p acTail stageTail =
      acceptJ2InputTape p acTail (!p.L.rejectHit) []
        [false, true, p.L.rejectHit] 3
        (acceptAfterRejectHitPullRight p stageTail) := by
  simp [acceptAfterFirstPullTape, acceptJ2InputTape,
    acceptAfterRejectHitPullRight,
    replicate_none_comm', List.append_assoc]

@[irreducible] def acceptThroughRejectHitPull2Description : MachineDescription :=
  canonicalSeqDescription
    acceptThroughFirstPullDescription pullOneBitJ2Description

theorem acceptThroughRejectHitPull2Description_subroutineReady :
    acceptThroughRejectHitPull2Description.SubroutineReady := by
  unfold acceptThroughRejectHitPull2Description
  exact canonicalSeqDescription_subroutineReady
    acceptThroughFirstPullDescription_subroutineReady
    pullOneBitJ2Description_subroutineReady

theorem acceptThroughRejectHitPull2Description_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    exists acTail stageTail : Word Bool,
      acceptThroughRejectHitPull2Description.HaltsFromTape
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
        (acceptJ2OutputTape p acTail (!p.L.rejectHit) []
          [false, true] 3 p.L.rejectHit
          (acceptAfterRejectHitPullRight p stageTail)) := by
  unfold acceptThroughRejectHitPull2Description
  rcases acceptThroughFirstPullDescription_haltsFrom p with
    ⟨acTail, stageTail, hfirst⟩
  refine ⟨acTail, stageTail, ?_⟩
  have hbridge :
      Tape.move Direction.left
          (Tape.move Direction.right
            (acceptAfterFirstPullTape p acTail stageTail)) =
        acceptJ2InputTape p acTail (!p.L.rejectHit) []
          [false, true, p.L.rejectHit] 3
          (acceptAfterRejectHitPullRight p stageTail) := by
    rw [show
        Tape.move Direction.left
            (Tape.move Direction.right
              (acceptAfterFirstPullTape p acTail stageTail)) =
          acceptAfterFirstPullTape p acTail stageTail by
      simp [acceptAfterFirstPullTape,
        CommonGround.FiniteTransducers.tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]]
    exact acceptAfterFirstPullTape_eq_j2Input p acTail stageTail
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      acceptThroughFirstPullDescription_subroutineReady
      pullOneBitJ2Description_subroutineReady
      hfirst hbridge
      (acceptJ2_haltsFrom p acTail (!p.L.rejectHit) []
        [false, true] 3 p.L.rejectHit
        (acceptAfterRejectHitPullRight p stageTail))

@[irreducible] def acceptThroughRejectHitPull3Description : MachineDescription :=
  canonicalSeqDescription
    acceptThroughRejectHitPull2Description pullOneBitJ2Description

theorem acceptThroughRejectHitPull3Description_subroutineReady :
    acceptThroughRejectHitPull3Description.SubroutineReady := by
  unfold acceptThroughRejectHitPull3Description
  exact canonicalSeqDescription_subroutineReady
    acceptThroughRejectHitPull2Description_subroutineReady
    pullOneBitJ2Description_subroutineReady

theorem acceptThroughRejectHitPull3Description_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    exists acTail stageTail : Word Bool,
      acceptThroughRejectHitPull3Description.HaltsFromTape
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
        (acceptJ2OutputTape p acTail p.L.rejectHit
          [!p.L.rejectHit] [false] 3 true
          (none :: acceptAfterRejectHitPullRight p stageTail)) := by
  unfold acceptThroughRejectHitPull3Description
  rcases acceptThroughRejectHitPull2Description_haltsFrom p with
    ⟨acTail, stageTail, hprev⟩
  refine ⟨acTail, stageTail, ?_⟩
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      acceptThroughRejectHitPull2Description_subroutineReady
      pullOneBitJ2Description_subroutineReady
      hprev
      (acceptJ2OutputTape_canonicalBridge p acTail (!p.L.rejectHit) []
        [false] 3 true p.L.rejectHit
        (acceptAfterRejectHitPullRight p stageTail))
      (acceptJ2_haltsFrom p acTail p.L.rejectHit
        [!p.L.rejectHit] [false] 3 true
        (none :: acceptAfterRejectHitPullRight p stageTail))

@[irreducible] def acceptThroughRejectHitPull4Description : MachineDescription :=
  canonicalSeqDescription
    acceptThroughRejectHitPull3Description pullOneBitJ2Description

theorem acceptThroughRejectHitPull4Description_subroutineReady :
    acceptThroughRejectHitPull4Description.SubroutineReady := by
  unfold acceptThroughRejectHitPull4Description
  exact canonicalSeqDescription_subroutineReady
    acceptThroughRejectHitPull3Description_subroutineReady
    pullOneBitJ2Description_subroutineReady

theorem acceptThroughRejectHitPull4Description_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    exists acTail stageTail : Word Bool,
      acceptThroughRejectHitPull4Description.HaltsFromTape
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
        (acceptJ2OutputTape p acTail true
          [p.L.rejectHit, !p.L.rejectHit] [] 3 false
          (none :: none :: acceptAfterRejectHitPullRight p stageTail)) := by
  unfold acceptThroughRejectHitPull4Description
  rcases acceptThroughRejectHitPull3Description_haltsFrom p with
    ⟨acTail, stageTail, hprev⟩
  refine ⟨acTail, stageTail, ?_⟩
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      acceptThroughRejectHitPull3Description_subroutineReady
      pullOneBitJ2Description_subroutineReady
      hprev
      (acceptJ2OutputTape_canonicalBridge p acTail p.L.rejectHit
        [!p.L.rejectHit] [] 3 false true
        (none :: acceptAfterRejectHitPullRight p stageTail))
      (acceptJ2_haltsFrom p acTail true
        [p.L.rejectHit, !p.L.rejectHit] [] 3 false
        (none :: none :: acceptAfterRejectHitPullRight p stageTail))

theorem acceptAfterRejectHitPull4_eq_firstOuterHitInput
    (p : SelectedMergeEmitterPayload) (acTail stageTail : Word Bool) :
    acceptJ2OutputTape p acTail true
      [p.L.rejectHit, !p.L.rejectHit] [] 3 false
      (none :: none :: acceptAfterRejectHitPullRight p stageTail) =
      acceptJ2InputTape p acTail false
        [true, p.L.rejectHit, !p.L.rejectHit]
        (List.append
          (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
          [false, true, p.S.hit, !p.S.hit])
        (stageTail.length + 8) (List.replicate 5 none) := by
  simp [acceptJ2InputTape, acceptJ2OutputTape,
    acceptAfterRejectHitPullRight,
    SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits,
    boolFieldBits_eq_four, commonRightPadding,
    replicate_none_append_cons', none_cons_replicate_append,
    List.append_assoc, Nat.add_assoc]

end ParsedInnerTransport
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
