import FoC.Computability.Compiler.ClosedCfg.PostTrans.ParsedInnerTransport.AcceptPull

set_option doc.verso true

/-!
# Parsed-inner accepting outer-hit pull

This continuation keeps the growing composed description behind a module
boundary while it moves the outer hit across the erased fields.
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

@[irreducible] def acceptThroughOuterHitPull1Description : MachineDescription :=
  canonicalSeqDescription
    acceptThroughRejectHitPull4Description pullOneBitJ2Description

theorem acceptThroughOuterHitPull1Description_subroutineReady :
    acceptThroughOuterHitPull1Description.SubroutineReady := by
  unfold acceptThroughOuterHitPull1Description
  exact canonicalSeqDescription_subroutineReady
    acceptThroughRejectHitPull4Description_subroutineReady
    pullOneBitJ2Description_subroutineReady

set_option maxHeartbeats 1000000 in
theorem acceptThroughOuterHitPull1Description_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    exists acTail stageTail : Word Bool,
      acceptThroughOuterHitPull1Description.HaltsFromTape
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
        (acceptJ2OutputTape p acTail false
          [true, p.L.rejectHit, !p.L.rejectHit]
          (List.append
            (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
            [false, true, p.S.hit])
          (stageTail.length + 8) (!p.S.hit)
          (List.replicate 5 none)) := by
  unfold acceptThroughOuterHitPull1Description
  rcases acceptThroughRejectHitPull4Description_haltsFrom p with
    ⟨acTail, stageTail, hprev⟩
  refine ⟨acTail, stageTail, ?_⟩
  have hbridge :
      Tape.move Direction.left
          (Tape.move Direction.right
            (acceptJ2OutputTape p acTail true
              [p.L.rejectHit, !p.L.rejectHit] [] 3 false
              (none :: none :: acceptAfterRejectHitPullRight p stageTail))) =
        acceptJ2InputTape p acTail false
          [true, p.L.rejectHit, !p.L.rejectHit]
          (List.append
            (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
            [false, true, p.S.hit, !p.S.hit])
          (stageTail.length + 8) (List.replicate 5 none) := by
    rw [show
        Tape.move Direction.left
            (Tape.move Direction.right
              (acceptJ2OutputTape p acTail true
                [p.L.rejectHit, !p.L.rejectHit] [] 3 false
                (none :: none :: acceptAfterRejectHitPullRight p stageTail))) =
          acceptJ2OutputTape p acTail true
            [p.L.rejectHit, !p.L.rejectHit] [] 3 false
            (none :: none :: acceptAfterRejectHitPullRight p stageTail) by
      simp [acceptJ2OutputTape,
        CommonGround.FiniteTransducers.tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]]
    exact acceptAfterRejectHitPull4_eq_firstOuterHitInput p acTail stageTail
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      acceptThroughRejectHitPull4Description_subroutineReady
      pullOneBitJ2Description_subroutineReady
      hprev hbridge
      (by
        simpa [List.append_assoc] using
          (acceptJ2_haltsFrom p acTail false
            [true, p.L.rejectHit, !p.L.rejectHit]
            (List.append
              (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
              [false, true, p.S.hit])
            (stageTail.length + 8) (!p.S.hit)
            (List.replicate 5 none)))

@[irreducible] def acceptThroughOuterHitPull2Description : MachineDescription :=
  canonicalSeqDescription
    acceptThroughOuterHitPull1Description pullOneBitJ2Description

theorem acceptThroughOuterHitPull2Description_subroutineReady :
    acceptThroughOuterHitPull2Description.SubroutineReady := by
  unfold acceptThroughOuterHitPull2Description
  exact canonicalSeqDescription_subroutineReady
    acceptThroughOuterHitPull1Description_subroutineReady
    pullOneBitJ2Description_subroutineReady

set_option maxHeartbeats 1000000 in
theorem acceptThroughOuterHitPull2Description_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    exists acTail stageTail : Word Bool,
      acceptThroughOuterHitPull2Description.HaltsFromTape
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
        (acceptJ2OutputTape p acTail (!p.S.hit)
          [false, true, p.L.rejectHit, !p.L.rejectHit]
          (List.append
            (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
            [false, true])
          (stageTail.length + 8) p.S.hit
          (none :: List.replicate 5 none)) := by
  unfold acceptThroughOuterHitPull2Description
  rcases acceptThroughOuterHitPull1Description_haltsFrom p with
    ⟨acTail, stageTail, hprev⟩
  refine ⟨acTail, stageTail, ?_⟩
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      acceptThroughOuterHitPull1Description_subroutineReady
      pullOneBitJ2Description_subroutineReady
      hprev
      (by
        simpa [List.append_assoc] using
          (acceptJ2OutputTape_canonicalBridge p acTail false
            [true, p.L.rejectHit, !p.L.rejectHit]
            (List.append
              (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
              [false, true])
            (stageTail.length + 8) p.S.hit (!p.S.hit)
            (List.replicate 5 none)))
      (by
        simpa [List.append_assoc] using
          (acceptJ2_haltsFrom p acTail (!p.S.hit)
            [false, true, p.L.rejectHit, !p.L.rejectHit]
            (List.append
              (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
              [false, true])
            (stageTail.length + 8) p.S.hit
            (none :: List.replicate 5 none)))

@[irreducible] def acceptThroughOuterHitPull3Description : MachineDescription :=
  canonicalSeqDescription
    acceptThroughOuterHitPull2Description pullOneBitJ2Description

theorem acceptThroughOuterHitPull3Description_subroutineReady :
    acceptThroughOuterHitPull3Description.SubroutineReady := by
  unfold acceptThroughOuterHitPull3Description
  exact canonicalSeqDescription_subroutineReady
    acceptThroughOuterHitPull2Description_subroutineReady
    pullOneBitJ2Description_subroutineReady

set_option maxHeartbeats 1000000 in
theorem acceptThroughOuterHitPull3Description_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    exists acTail stageTail : Word Bool,
      acceptThroughOuterHitPull3Description.HaltsFromTape
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
        (acceptJ2OutputTape p acTail p.S.hit
          [!p.S.hit, false, true, p.L.rejectHit, !p.L.rejectHit]
          (List.append
            (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
            [false])
          (stageTail.length + 8) true
          (none :: none :: List.replicate 5 none)) := by
  unfold acceptThroughOuterHitPull3Description
  rcases acceptThroughOuterHitPull2Description_haltsFrom p with
    ⟨acTail, stageTail, hprev⟩
  refine ⟨acTail, stageTail, ?_⟩
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      acceptThroughOuterHitPull2Description_subroutineReady
      pullOneBitJ2Description_subroutineReady
      hprev
      (by
        simpa [List.append_assoc] using
          (acceptJ2OutputTape_canonicalBridge p acTail (!p.S.hit)
            [false, true, p.L.rejectHit, !p.L.rejectHit]
            (List.append
              (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
              [false])
            (stageTail.length + 8) true p.S.hit
            (none :: List.replicate 5 none)))
      (by
        simpa [List.append_assoc] using
          (acceptJ2_haltsFrom p acTail p.S.hit
            [!p.S.hit, false, true, p.L.rejectHit, !p.L.rejectHit]
            (List.append
              (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
              [false])
            (stageTail.length + 8) true
            (none :: none :: List.replicate 5 none)))

@[irreducible] def acceptThroughOuterHitPull4Description : MachineDescription :=
  canonicalSeqDescription
    acceptThroughOuterHitPull3Description pullOneBitJ2Description

theorem acceptThroughOuterHitPull4Description_subroutineReady :
    acceptThroughOuterHitPull4Description.SubroutineReady := by
  unfold acceptThroughOuterHitPull4Description
  exact canonicalSeqDescription_subroutineReady
    acceptThroughOuterHitPull3Description_subroutineReady
    pullOneBitJ2Description_subroutineReady

set_option maxHeartbeats 1000000 in
theorem acceptThroughOuterHitPull4Description_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    exists acTail stageTail : Word Bool,
      acceptThroughOuterHitPull4Description.HaltsFromTape
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
        (acceptJ2OutputTape p acTail true
          [p.S.hit, !p.S.hit, false, true, p.L.rejectHit, !p.L.rejectHit]
          (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
          (stageTail.length + 8) false
          (none :: none :: none :: List.replicate 5 none)) := by
  unfold acceptThroughOuterHitPull4Description
  rcases acceptThroughOuterHitPull3Description_haltsFrom p with
    ⟨acTail, stageTail, hprev⟩
  refine ⟨acTail, stageTail, ?_⟩
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      acceptThroughOuterHitPull3Description_subroutineReady
      pullOneBitJ2Description_subroutineReady
      hprev
      (acceptJ2OutputTape_canonicalBridge p acTail p.S.hit
        [!p.S.hit, false, true, p.L.rejectHit, !p.L.rejectHit]
        (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
        (stageTail.length + 8) false true
        (none :: none :: List.replicate 5 none))
      (acceptJ2_haltsFrom p acTail true
        [p.S.hit, !p.S.hit, false, true, p.L.rejectHit, !p.L.rejectHit]
        (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
        (stageTail.length + 8) false
        (none :: none :: none :: List.replicate 5 none))

def acceptAfterRejectConfigPullTape
    (p : SelectedMergeEmitterPayload) (acTail stageTail : Word Bool) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      ((SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).map some)
      (List.append
        (([false, true, p.S.hit, !p.S.hit, false, true,
          p.L.rejectHit, !p.L.rejectHit] : Word Bool).map some)
        (none ::
          List.append
            ((SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).map some)
            (List.append (List.replicate acTail.length none)
              (none ::
                List.append
                  (List.replicate
                    (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).length none)
                  (none ::
                    List.append (List.replicate (stageTail.length + 8) none)
                      (none ::
                        List.append
                          ((SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).map some)
                          (none :: none :: none :: List.replicate 5 none))))))))

theorem acceptRejectConfigPull_haltsFrom
    (p : SelectedMergeEmitterPayload) (acTail stageTail : Word Bool) :
    pullLoopJ1Description.HaltsFromTape
      (acceptJ2OutputTape p acTail true
        [p.S.hit, !p.S.hit, false, true, p.L.rejectHit, !p.L.rejectHit]
        (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
        (stageTail.length + 8) false
        (none :: none :: none :: List.replicate 5 none))
      (acceptAfterRejectConfigPullTape p acTail stageTail) := by
  rcases configurationFieldBits_eq_reverse_cons_cons p.L.rejectConfig with
    ⟨x, y, rest, hconfig⟩
  rcases outputPrefixBits_cons p with ⟨prefixTail, hprefix⟩
  apply haltsFromTape_of_reaches
  simpa [acceptJ2OutputTape, acceptAfterRejectConfigPullTape,
    hconfig, hprefix,
    replicate_none_comm', List.map_append, List.map_reverse,
    List.reverse_append, List.replicate_succ, List.append_assoc] using
    pullLoopJ1_run false
      [true, p.S.hit, !p.S.hit, false, true, p.L.rejectHit, !p.L.rejectHit]
      (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p)
      (by simpa [hprefix])
      acTail.length x y rest
      (List.append (List.replicate (stageTail.length + 8) none)
        (none ::
          List.append
            ((SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).map some)
            (none :: none :: none :: List.replicate 5 none)))

@[irreducible] def acceptThroughRejectConfigPullDescription : MachineDescription :=
  canonicalSeqDescription
    acceptThroughOuterHitPull4Description pullLoopJ1Description

theorem acceptThroughRejectConfigPullDescription_subroutineReady :
    acceptThroughRejectConfigPullDescription.SubroutineReady := by
  unfold acceptThroughRejectConfigPullDescription
  exact canonicalSeqDescription_subroutineReady
    acceptThroughOuterHitPull4Description_subroutineReady
    pullLoopJ1Description_subroutineReady

set_option maxHeartbeats 1000000 in
theorem acceptThroughRejectConfigPullDescription_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    exists acTail stageTail : Word Bool,
      acceptThroughRejectConfigPullDescription.HaltsFromTape
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
        (acceptAfterRejectConfigPullTape p acTail stageTail) := by
  unfold acceptThroughRejectConfigPullDescription
  rcases acceptThroughOuterHitPull4Description_haltsFrom p with
    ⟨acTail, stageTail, hprev⟩
  refine ⟨acTail, stageTail, ?_⟩
  have hbridge :
      Tape.move Direction.left
          (Tape.move Direction.right
            (acceptJ2OutputTape p acTail true
              [p.S.hit, !p.S.hit, false, true, p.L.rejectHit, !p.L.rejectHit]
              (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
              (stageTail.length + 8) false
              (none :: none :: none :: List.replicate 5 none))) =
        acceptJ2OutputTape p acTail true
          [p.S.hit, !p.S.hit, false, true, p.L.rejectHit, !p.L.rejectHit]
          (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
          (stageTail.length + 8) false
          (none :: none :: none :: List.replicate 5 none) := by
    simp [acceptJ2OutputTape,
      CommonGround.FiniteTransducers.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      acceptThroughOuterHitPull4Description_subroutineReady
      pullLoopJ1Description_subroutineReady
      hprev hbridge
      (acceptRejectConfigPull_haltsFrom p acTail stageTail)

def acceptAfterOuterConfigPullTape
    (p : SelectedMergeEmitterPayload) (acTail stageTail : Word Bool) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      ((SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).map some)
      (List.append
        ((SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).map some)
        (List.append
          (([false, true, p.S.hit, !p.S.hit, false, true,
            p.L.rejectHit, !p.L.rejectHit] : Word Bool).map some)
          (none ::
            List.append
              ((SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).map some)
              (List.append
                (List.replicate
                  (acTail.length +
                    (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).length +
                    stageTail.length + 10) none)
                (none ::
                  List.append
                    (List.replicate
                      (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).length none)
                    (none :: none :: none :: List.replicate 5 none)))))))

theorem acceptOuterConfigPull_haltsFrom
    (p : SelectedMergeEmitterPayload) (acTail stageTail : Word Bool) :
    pullLoopJ1Description.HaltsFromTape
      (acceptAfterRejectConfigPullTape p acTail stageTail)
      (acceptAfterOuterConfigPullTape p acTail stageTail) := by
  rcases configurationFieldBits_false_false_tail p.L.rejectConfig [] with
    ⟨rcTail, hreject⟩
  rcases configurationFieldBits_eq_reverse_cons_cons p.L.outerConfig with
    ⟨x, y, rest, houter⟩
  rcases outputPrefixBits_cons p with ⟨prefixTail, hprefix⟩
  apply haltsFromTape_of_reaches
  simpa [acceptAfterRejectConfigPullTape, acceptAfterOuterConfigPullTape,
    hreject, houter, hprefix,
    replicate_none_append_cons', List.map_append, List.map_reverse,
    List.reverse_append, List.replicate_succ, List.append_assoc,
    Nat.add_assoc] using
    pullLoopJ1_run false
      (List.append rcTail
        [false, true, p.S.hit, !p.S.hit, false, true,
          p.L.rejectHit, !p.L.rejectHit])
      (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p)
      (by simpa [hprefix])
      (acTail.length +
        (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).length +
        stageTail.length + 10)
      x y rest
      (none :: none :: List.replicate 5 none)

@[irreducible] def acceptThroughOuterConfigPullDescription : MachineDescription :=
  canonicalSeqDescription
    acceptThroughRejectConfigPullDescription pullLoopJ1Description

theorem acceptThroughOuterConfigPullDescription_subroutineReady :
    acceptThroughOuterConfigPullDescription.SubroutineReady := by
  unfold acceptThroughOuterConfigPullDescription
  exact canonicalSeqDescription_subroutineReady
    acceptThroughRejectConfigPullDescription_subroutineReady
    pullLoopJ1Description_subroutineReady

set_option maxHeartbeats 1000000 in
theorem acceptThroughOuterConfigPullDescription_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    exists acTail stageTail : Word Bool,
      acceptThroughOuterConfigPullDescription.HaltsFromTape
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
        (acceptAfterOuterConfigPullTape p acTail stageTail) := by
  unfold acceptThroughOuterConfigPullDescription
  rcases acceptThroughRejectConfigPullDescription_haltsFrom p with
    ⟨acTail, stageTail, hprev⟩
  refine ⟨acTail, stageTail, ?_⟩
  have hbridge :
      Tape.move Direction.left
          (Tape.move Direction.right
            (acceptAfterRejectConfigPullTape p acTail stageTail)) =
        acceptAfterRejectConfigPullTape p acTail stageTail := by
    simp [acceptAfterRejectConfigPullTape,
      CommonGround.FiniteTransducers.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      acceptThroughRejectConfigPullDescription_subroutineReady
      pullLoopJ1Description_subroutineReady
      hprev hbridge
      (acceptOuterConfigPull_haltsFrom p acTail stageTail)

def acceptAfterOutputPrefixPullTape
    (p : SelectedMergeEmitterPayload) (acTail stageTail : Word Bool) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      ((SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).map some)
      (List.append
        ((SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).map some)
        (List.append
          ((SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).map some)
          (List.append
            (([false, true, p.S.hit, !p.S.hit, false, true,
              p.L.rejectHit, !p.L.rejectHit] : Word Bool).map some)
            (none ::
              List.append
                (List.replicate
                  (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p).length none)
                (none ::
                  List.append
                    (List.replicate
                      (acTail.length +
                        (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).length +
                        stageTail.length + 9) none)
                    (none ::
                      List.append
                        (List.replicate
                          (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).length
                          none)
                        (none :: none :: none :: List.replicate 5 none))))))))

theorem acceptOutputPrefixPull_haltsFrom
    (p : SelectedMergeEmitterPayload) (acTail stageTail : Word Bool) :
    pullLoopJ0Description.HaltsFromTape
      (acceptAfterOuterConfigPullTape p acTail stageTail)
      (acceptAfterOutputPrefixPullTape p acTail stageTail) := by
  rcases configurationFieldBits_false_false_tail p.L.outerConfig [] with
    ⟨ocTail, houter⟩
  rcases outputPrefixBits_eq_reverse_cons_cons p with
    ⟨x, y, rest, hprefix⟩
  apply haltsFromTape_of_reaches
  simpa [acceptAfterOuterConfigPullTape, acceptAfterOutputPrefixPullTape,
    houter, hprefix,
    none_cons_replicate_append,
    List.map_append, List.map_reverse, List.reverse_append,
    List.replicate_succ, List.append_assoc, Nat.add_assoc] using
    pullLoopJ0_run false
      (List.append ocTail
        (List.append
          (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p)
          [false, true, p.S.hit, !p.S.hit, false, true,
            p.L.rejectHit, !p.L.rejectHit]))
      x y rest
      (List.append
        (List.replicate
          (acTail.length +
            (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).length +
            stageTail.length + 9) none)
        (none ::
          List.append
            (List.replicate
              (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).length none)
            (none :: none :: none :: List.replicate 5 none)))

@[irreducible] def acceptFieldTransportDescription : MachineDescription :=
  canonicalSeqDescription
    acceptThroughOuterConfigPullDescription pullLoopJ0Description

theorem acceptFieldTransportDescription_subroutineReady :
    acceptFieldTransportDescription.SubroutineReady := by
  unfold acceptFieldTransportDescription
  exact canonicalSeqDescription_subroutineReady
    acceptThroughOuterConfigPullDescription_subroutineReady
    pullLoopJ0Description_subroutineReady

set_option maxHeartbeats 1000000 in
theorem acceptFieldTransportDescription_haltsFrom
    (p : SelectedMergeEmitterPayload) :
    exists acTail stageTail : Word Bool,
      acceptFieldTransportDescription.HaltsFromTape
        (SelectedMergePaddedEmitterParsedInnerPostPrefixGapClosedTape p)
        (acceptAfterOutputPrefixPullTape p acTail stageTail) := by
  unfold acceptFieldTransportDescription
  rcases acceptThroughOuterConfigPullDescription_haltsFrom p with
    ⟨acTail, stageTail, hprev⟩
  refine ⟨acTail, stageTail, ?_⟩
  have hbridge :
      Tape.move Direction.left
          (Tape.move Direction.right
            (acceptAfterOuterConfigPullTape p acTail stageTail)) =
        acceptAfterOuterConfigPullTape p acTail stageTail := by
    simp [acceptAfterOuterConfigPullTape,
      CommonGround.FiniteTransducers.tapeAtCells,
      Tape.move, Tape.moveLeft, Tape.moveRight]
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      acceptThroughOuterConfigPullDescription_subroutineReady
      pullLoopJ0Description_subroutineReady
      hprev hbridge
      (acceptOutputPrefixPull_haltsFrom p acTail stageTail)

theorem acceptAfterOutputPrefixPullTape_equiv_decodedHandoff
    (p : SelectedMergeEmitterPayload) (acTail stageTail : Word Bool) :
    Tape.Equiv (acceptAfterOutputPrefixPullTape p acTail stageTail)
      (SelectedMergePaddedEmitterDecodedHandoffTape true p) := by
  rcases outputPrefixBits_cons p with ⟨prefixTail, hprefix⟩
  have hbits :
      SelectedMergePaddedEmitterDecodedHandoffBits true p =
        List.append
          (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p)
          (List.append
            (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
            (List.append
              (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p)
              (List.append
                [false, true, p.S.hit, !p.S.hit]
                [false, true, p.L.rejectHit, !p.L.rejectHit]))) := by
    rw [SelectedMergePaddedEmitterDecodedHandoffBits_eq_postPrefixTargetBits]
    simp [SelectedMergePaddedEmitterParsedInnerPostPrefixTargetBits,
      SelectedMergePaddedEmitterParsedInnerTargetFieldTailExpandedBits,
      SelectedMergePaddedEmitterParsedInnerOuterHitFieldBits,
      SelectedMergePaddedEmitterParsedInnerRejectHitFieldBits,
      boolFieldBits_eq_four]
  rw [SelectedMergePaddedEmitterDecodedHandoffTape_eq_tapeAtCells_bits, hbits]
  simp [Tape.Equiv, acceptAfterOutputPrefixPullTape,
    CommonGround.FiniteTransducers.tapeAtCells,
    DovetailInitialLayoutInitializer.tapeAtCells,
    hprefix, List.map_append, List.append_assoc,
    FoC.Computability.dropTrailingNone_append_replicate_none]

theorem acceptFieldTransportDescription_spec :
    SelectedMergePaddedEmitterParsedInnerPostPrefixFieldTransportSpec true
      acceptFieldTransportDescription := by
  constructor
  · exact acceptFieldTransportDescription_subroutineReady
  · intro p
    rcases acceptFieldTransportDescription_haltsFrom p with
      ⟨acTail, stageTail, hhalt⟩
    exact ⟨acceptAfterOutputPrefixPullTape p acTail stageTail, hhalt,
      acceptAfterOutputPrefixPullTape_equiv_decodedHandoff p acTail stageTail⟩

end ParsedInnerTransport
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
