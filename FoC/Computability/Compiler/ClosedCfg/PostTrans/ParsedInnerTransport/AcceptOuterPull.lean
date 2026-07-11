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
                      (List.append
                        ((SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).map some)
                        (none :: none :: none :: none :: none ::
                          List.replicate 5 none))))))))

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
  rw [show pullLoopJ1Description.start = 0 by rfl,
    show pullLoopJ1Description.halt = 26 by rfl]
  simpa [acceptJ2OutputTape, acceptAfterRejectConfigPullTape,
    SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits,
    hconfig, hprefix,
    replicate_none_comm', List.map_append, List.map_reverse,
    List.reverse_append, List.replicate_succ, List.append_assoc] using
    pullLoopJ1_run false
      [true, p.S.hit, !p.S.hit, false, true, p.L.rejectHit, !p.L.rejectHit]
      (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p)
      (by simp [hprefix])
      acTail.length x y rest
      (List.append (List.replicate (stageTail.length + 8) none)
        (List.append
          ((SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).map some)
          (none :: none :: none :: none :: none ::
            List.replicate 5 none)))

@[irreducible] def acceptThroughRejectConfigPullDescription : MachineDescription :=
  canonicalSeqDescription
    acceptThroughOuterHitPull4Description pullLoopJ1Description

theorem acceptThroughRejectConfigPullDescription_subroutineReady :
    acceptThroughRejectConfigPullDescription.SubroutineReady := by
  unfold acceptThroughRejectConfigPullDescription
  exact canonicalSeqDescription_subroutineReady
    acceptThroughOuterHitPull4Description_subroutineReady
    pullLoopJ1Description_subroutineReady

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
          (none :: none :: none :: List.replicate 5 none) :=
    Tape.move_left_move_right_eq_self_of_right_cons _ rfl
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
                    stageTail.length + 9) none)
                (none ::
                  List.append
                    (List.replicate
                      (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).length none)
                    (none :: none :: none :: none :: none ::
                      List.replicate 5 none)))))))

theorem acceptOuterConfigPull_haltsFrom
    (p : SelectedMergeEmitterPayload) (acTail stageTail : Word Bool) :
    pullLoopJ1Description.HaltsFromTape
      (acceptAfterRejectConfigPullTape p acTail stageTail)
      (acceptAfterOuterConfigPullTape p acTail stageTail) := by
  rcases configurationFieldBits_false_false_tail p.L.rejectConfig [] with
    ⟨rcTail, hreject⟩
  rcases configurationFieldBits_eq_reverse_cons_cons p.S.config with
    ⟨x, y, rest, houter⟩
  rcases outputPrefixBits_cons p with ⟨prefixTail, hprefix⟩
  apply haltsFromTape_of_reaches
  rw [show pullLoopJ1Description.start = 0 by rfl,
    show pullLoopJ1Description.halt = 26 by rfl]
  have hgap (X : List (Option Bool)) :
      List.replicate
          (acTail.length +
            (rcTail.length + (2 + (stageTail.length + 10)))) none ++ X =
        List.replicate acTail.length none ++
          (List.replicate (rcTail.length + 3) none ++
            (List.replicate (stageTail.length + 9) none ++ X)) := by
    have hcount :
        acTail.length + (rcTail.length + (2 + (stageTail.length + 10))) =
          acTail.length + ((rcTail.length + 3) + (stageTail.length + 9)) := by
      lia
    rw [hcount,
      replicate_add_none acTail.length
        ((rcTail.length + 3) + (stageTail.length + 9)),
      replicate_add_none (rcTail.length + 3) (stageTail.length + 9)]
    exact
      (List.append_assoc
        (List.replicate acTail.length none)
        (List.replicate (rcTail.length + 3) none ++
          List.replicate (stageTail.length + 9) none)
        X).trans
        (congrArg
          (List.append (List.replicate acTail.length none))
          (List.append_assoc
            (List.replicate (rcTail.length + 3) none)
            (List.replicate (stageTail.length + 9) none) X))
  simpa (config := { maxSteps := 500000 })
    [acceptAfterRejectConfigPullTape, acceptAfterOuterConfigPullTape,
    SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits,
    SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits,
    hreject, houter, hprefix,
    replicate_none_append_cons', none_cons_replicate_append,
    List.map_append, List.map_reverse,
    List.reverse_append, hgap, List.append_assoc,
    Nat.add_assoc] using
    pullLoopJ1_run false
      (List.append (false :: rcTail)
        [false, true, p.S.hit, !p.S.hit, false, true,
          p.L.rejectHit, !p.L.rejectHit])
      (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p)
      (by simp [hprefix])
      (acTail.length +
        (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).length +
        stageTail.length + 9)
      x y rest
      (none :: none :: none :: none :: List.replicate 5 none)

@[irreducible] def acceptThroughOuterConfigPullDescription : MachineDescription :=
  canonicalSeqDescription
    acceptThroughRejectConfigPullDescription pullLoopJ1Description

theorem acceptThroughOuterConfigPullDescription_subroutineReady :
    acceptThroughOuterConfigPullDescription.SubroutineReady := by
  unfold acceptThroughOuterConfigPullDescription
  exact canonicalSeqDescription_subroutineReady
    acceptThroughRejectConfigPullDescription_subroutineReady
    pullLoopJ1Description_subroutineReady

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
  rcases configurationFieldBits_false_false_tail p.L.rejectConfig [] with
    ⟨rcTail, hreject⟩
  have hbridge :
      Tape.move Direction.left
          (Tape.move Direction.right
            (acceptAfterRejectConfigPullTape p acTail stageTail)) =
        acceptAfterRejectConfigPullTape p acTail stageTail := by
    simp [acceptAfterRejectConfigPullTape,
      SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits, hreject,
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
                        stageTail.length + 8) none)
                    (none ::
                      List.append
                        (List.replicate
                          (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).length
                          none)
                        (none :: none :: none :: none :: none ::
                          List.replicate 5 none))))))))

theorem acceptOutputPrefixPull_haltsFrom
    (p : SelectedMergeEmitterPayload) (acTail stageTail : Word Bool) :
    pullLoopJ0Description.HaltsFromTape
      (acceptAfterOuterConfigPullTape p acTail stageTail)
      (acceptAfterOutputPrefixPullTape p acTail stageTail) := by
  rcases configurationFieldBits_false_false_tail p.S.config [] with
    ⟨ocTail, houter⟩
  rcases outputPrefixBits_eq_reverse_cons_cons p with
    ⟨x, y, rest, hprefix⟩
  apply haltsFromTape_of_reaches
  rw [show pullLoopJ0Description.start = 0 by rfl,
    show pullLoopJ0Description.halt = 14 by rfl]
  simpa (config := { maxSteps := 500000 })
    [acceptAfterOuterConfigPullTape, acceptAfterOutputPrefixPullTape,
    SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits,
    houter, hprefix,
    none_cons_replicate_append,
    List.map_append, List.map_reverse, List.reverse_append,
    List.append_assoc, Nat.add_assoc] using
    pullLoopJ0_run false
      (List.append (false :: ocTail)
        (List.append
          (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p)
          [false, true, p.S.hit, !p.S.hit, false, true,
            p.L.rejectHit, !p.L.rejectHit]))
      x y rest
      (List.append
        (List.replicate
          (acTail.length +
            (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).length +
            stageTail.length + 8) none)
        (none ::
          List.append
            (List.replicate
              (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).length none)
            (none :: none :: none :: none :: none :: List.replicate 5 none)))

@[irreducible] def acceptFieldTransportDescription : MachineDescription :=
  canonicalSeqDescription
    acceptThroughOuterConfigPullDescription pullLoopJ0Description

theorem acceptFieldTransportDescription_subroutineReady :
    acceptFieldTransportDescription.SubroutineReady := by
  unfold acceptFieldTransportDescription
  exact canonicalSeqDescription_subroutineReady
    acceptThroughOuterConfigPullDescription_subroutineReady
    pullLoopJ0Description_subroutineReady

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
  rcases configurationFieldBits_false_false_tail p.S.config [] with
    ⟨ocTail, houter⟩
  have hbridge :
      Tape.move Direction.left
          (Tape.move Direction.right
            (acceptAfterOuterConfigPullTape p acTail stageTail)) =
        acceptAfterOuterConfigPullTape p acTail stageTail := by
    simp [acceptAfterOuterConfigPullTape,
      SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits, houter,
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
  let core : List (Option Bool) :=
    List.append (prefixTail.map some)
      (List.append
        ((SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).map some)
        (List.append
          ((SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).map some)
          [some false, some true, some p.S.hit, some (!p.S.hit),
            some false, some true, some p.L.rejectHit,
            some (!p.L.rejectHit)]))
  let actualPad : List (Option Bool) :=
    none ::
      List.append (List.replicate (prefixTail.length + 1) none)
        (none ::
          List.append
            (List.replicate
              (acTail.length +
                (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p).length +
                stageTail.length + 8) none)
            (none ::
              List.append
                (List.replicate
                  (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p).length none)
                [none, none, none, none, none, none, none, none, none, none]))
  let targetPad : List (Option Bool) :=
    List.replicate (SimulatorLayout.asBoolInput p.S).length none
  have hactualRight :
      (acceptAfterOutputPrefixPullTape p acTail stageTail).right =
        core ++ actualPad := by
    simp [acceptAfterOutputPrefixPullTape, core, actualPad, hprefix,
      CommonGround.FiniteTransducers.tapeAtCells,
      List.append_assoc]
  have htargetRight :
      (DovetailInitialLayoutInitializer.tapeAtCells []
        (List.append
          ((List.append
            (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p)
            (List.append
              (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
              (List.append
                (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p)
                (List.append
                  [false, true, p.S.hit, !p.S.hit]
                  [false, true, p.L.rejectHit, !p.L.rejectHit])))).map some)
          (List.replicate (SimulatorLayout.asBoolInput p.S).length none))).right =
        core ++ targetPad := by
    rw [hprefix]
    simp [core, targetPad, DovetailInitialLayoutInitializer.tapeAtCells,
      List.map_append, List.append_assoc]
  have hactualLeft :
      (acceptAfterOutputPrefixPullTape p acTail stageTail).left = [none] := by
    simp [acceptAfterOutputPrefixPullTape, hprefix,
      CommonGround.FiniteTransducers.tapeAtCells]
  have htargetLeft :
      (DovetailInitialLayoutInitializer.tapeAtCells []
        (List.append
          ((List.append
            (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p)
            (List.append
              (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
              (List.append
                (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p)
                (List.append
                  [false, true, p.S.hit, !p.S.hit]
                  [false, true, p.L.rejectHit, !p.L.rejectHit])))).map some)
          (List.replicate (SimulatorLayout.asBoolInput p.S).length none))).left = [] := by
    simp [DovetailInitialLayoutInitializer.tapeAtCells, hprefix,
      List.map_append]
  have hactualHead :
      (acceptAfterOutputPrefixPullTape p acTail stageTail).head = some false := by
    simp [acceptAfterOutputPrefixPullTape, hprefix,
      CommonGround.FiniteTransducers.tapeAtCells]
  have htargetHead :
      (DovetailInitialLayoutInitializer.tapeAtCells []
        (List.append
          ((List.append
            (SelectedMergePaddedEmitterParsedInnerOutputPrefixBits p)
            (List.append
              (SelectedMergePaddedEmitterParsedInnerOuterConfigFieldBits p)
              (List.append
                (SelectedMergePaddedEmitterParsedInnerRejectConfigFieldBits p)
                (List.append
                  [false, true, p.S.hit, !p.S.hit]
                  [false, true, p.L.rejectHit, !p.L.rejectHit])))).map some)
          (List.replicate (SimulatorLayout.asBoolInput p.S).length none))).head =
        some false := by
    simp [DovetailInitialLayoutInitializer.tapeAtCells, hprefix,
      List.map_append]
  constructor
  · rw [hactualLeft, htargetLeft]
    rfl
  · constructor
    · rw [hactualHead, htargetHead]
    · rw [hactualRight, htargetRight,
        dropTrailingNone_append_of_all_none core actualPad (by
          intro z hz
          simp [actualPad] at hz
          rcases hz with h | h | h
          · exact h
          · exact h.2
          · exact h),
        dropTrailingNone_append_of_all_none core targetPad (by
          intro z hz
          simp [targetPad] at hz
          exact hz.2)]

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
