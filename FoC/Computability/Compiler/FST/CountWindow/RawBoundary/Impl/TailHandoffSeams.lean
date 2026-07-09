import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.TailHandoff
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.BlockMigrationLoop
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.EndpointSupport
import FoC.Computability.Compiler.Core.CommonGround.SeqComposition

set_option doc.verso true

/-!
# Raw-boundary right-edge tail-handoff seams

This module adapts the proved tail-handoff scanner statements to the exact
entry and exit tape forms used by the uniform two-pass emitter chain: the
guarded-header writer exit feeds the blank-run transit scanner, whose
right-handoff bridge lands exactly on the block-migration loop entry
invariant.  It also contains the small tape-equivalence lemma taking the
migration loop's finished tape (all-blank left context) to the single
blank-sentinel left context of the public left-edge endpoint, plus two
generic transport lemmas moving an equivalence-currency halting spec across
equivalent input or output tapes.  No new machines are introduced here; the
composed transit description below is the plain sequential composition of
the two existing proved machines.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

/-!
## Generic equivalence-currency transports

Moving a halting-up-to-trailing-blanks spec across an equivalent input tape
or an equivalent output tape.  These are small corollaries of the input
transport for exact halting specs plus transitivity of tape equivalence.
-/

theorem haltsFromTapeEquiv_across_input_equiv
    {D : MachineDescription} {Tin Tin' Tout : Tape Bool}
    (hin : Tape.Equiv Tin Tin')
    (h : D.HaltsFromTapeEquiv Tin Tout) :
    D.HaltsFromTapeEquiv Tin' Tout := by
  rcases h with ⟨Tactual, hhalt, hequiv⟩
  rcases HaltsFromTapeEquiv_of_input_equiv hin hhalt with
    ⟨Tactual', hhalt', hequiv'⟩
  exact ⟨Tactual', hhalt', Tape.Equiv.trans hequiv' hequiv⟩

theorem haltsFromTapeEquiv_across_output_equiv
    {D : MachineDescription} {Tin Tout Tout' : Tape Bool}
    (h : D.HaltsFromTapeEquiv Tin Tout)
    (hout : Tape.Equiv Tout Tout') :
    D.HaltsFromTapeEquiv Tin Tout' := by
  rcases h with ⟨Tactual, hhalt, hequiv⟩
  exact ⟨Tactual, hhalt, Tape.Equiv.trans hequiv hout⟩

/-!
## List-shape helpers for the seam equalities
-/

theorem cons_replicate_blank_append
    (blankTail : Nat) (rest : List (Option Bool)) :
    (none : Option Bool) ::
        List.append
          (List.replicate (blankTail + 1) (none : Option Bool)) rest =
      List.append
        (List.replicate (blankTail + 2) (none : Option Bool)) rest := by
  rw [show blankTail + 2 = (blankTail + 1) + 1 by lia]
  rfl

theorem dropTrailingNone_replicate_blank_pair (gap : Nat) :
    Tape.dropTrailingNone
        (List.replicate gap (none : Option Bool) ++
          (none :: none :: [])) = [] := by
  induction gap with
  | zero => rfl
  | succ gap ih =>
      simp [List.replicate_succ, Tape.dropTrailingNone, ih]

/-!
## Writer exit as same-head seam midpoint

The guarded-header writer halts on the separator blank with the guarded
encoded block ending its left context.  The left context is never empty, so
the same-head left-then-right jiggle is the identity on that tape; this is
the bridge equality the same-head composition wrapper consumes.
-/

theorem guardedWriterExitTape_move_right_move_left
    (layout : Word Bool) (blankTail : Nat)
    (right : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            (List.append
              ((encodedLayoutBits layout).reverse.map some)
              [some true, none])
            (none ::
              List.append
                (List.replicate (blankTail + 1) (none : Option Bool))
                right))) =
      tapeAtCells
        (List.append
          ((encodedLayoutBits layout).reverse.map some)
          [some true, none])
        (none ::
          List.append
            (List.replicate (blankTail + 1) (none : Option Bool))
            right) :=
  tapeAtCells_move_right_move_left_append_cons
    ((encodedLayoutBits layout).reverse.map some)
    [none]
    (none ::
      List.append
        (List.replicate (blankTail + 1) (none : Option Bool))
        right)
    (some true)

/-!
## Writer exit to tail-handoff entry
-/

theorem guardedWriterExitTape_eq_tailHandoffEntryTape
    (layout : Word Bool) (blankTail : Nat) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    tapeAtCells
        (List.append
          ((encodedLayoutBits layout).reverse.map some)
          [some true, none])
        (none ::
          List.append
            (List.replicate (blankTail + 1) (none : Option Bool))
            (some tailFirst :: tail)) =
      tapeAtCells
        (List.append
          ((encodedLayoutBits layout).reverse.map some)
          [some true, none])
        (List.append
          (List.replicate (blankTail + 2) (none : Option Bool))
          (some tailFirst :: tail)) := by
  rw [cons_replicate_blank_append]

theorem rightBlankRunTailFirstLeftHandoffDescription_haltsFrom_guardedWriterExit
    (layout : Word Bool) (blankTail : Nat) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rightBlankRunTailFirstLeftHandoffDescription.HaltsFromTape
      (tapeAtCells
        (List.append
          ((encodedLayoutBits layout).reverse.map some)
          [some true, none])
        (none ::
          List.append
            (List.replicate (blankTail + 1) (none : Option Bool))
            (some tailFirst :: tail)))
      (tapeAtCells
        (List.append
          (List.replicate (blankTail + 1) (none : Option Bool))
          (List.append
            ((encodedLayoutBits layout).reverse.map some)
            [some true, none]))
        (none :: some tailFirst :: tail)) := by
  rw [guardedWriterExitTape_eq_tailHandoffEntryTape]
  exact
    rightBlankRunTailFirstLeftHandoffDescription_haltsFromTape
      (blankTail + 1)
      (List.append
        ((encodedLayoutBits layout).reverse.map some)
        [some true, none])
      tail tailFirst

/-!
## Tail-handoff exit to block-migration entry
-/

theorem tailHandoffHaltTape_move_right_eq_blockMigrationEntry
    (layout : Word Bool) (blankTail : Nat) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (tapeAtCells
          (List.append
            (List.replicate (blankTail + 1) (none : Option Bool))
            (List.append
              ((encodedLayoutBits layout).reverse.map some)
              [some true, none]))
          (none :: some tailFirst :: tail)) =
      rawBoundaryBlockMigrationTape [] true (encodedLayoutBits layout)
        (blankTail + 2) tailFirst tail := by
  rw [rightBlankRunTailFirstLeftHandoffDescription_handoff_right]
  rw [rawBoundaryBlockMigrationTape]
  rw [cons_replicate_blank_append]

/-!
## Packaged transit: tail handoff then block migration

The sequential composition of the proved blank-run transit scanner and the
proved block-migration loop, from the guarded writer-exit tape to the
migrated block with the head on its left edge.  The composed description
term is spelled inline so that an assembly module using the same inline
composition matches these statements syntactically.
-/

theorem tailHandoffMigrationSeq_subroutineReady :
    (seqSubroutine rightBlankRunTailFirstLeftHandoffDescription
        rawBoundaryBlockMigrationLoopDescription
        Direction.right).SubroutineReady :=
  seqSubroutine_subroutineReady
    rightBlankRunTailFirstLeftHandoffDescription_subroutineReady
    rawBoundaryBlockMigrationLoopDescription_subroutineReady

theorem tailHandoffMigrationSeq_haltsFromEquiv_guardedWriterExit
    (layout : Word Bool) (blankTail : Nat) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (seqSubroutine rightBlankRunTailFirstLeftHandoffDescription
        rawBoundaryBlockMigrationLoopDescription
        Direction.right).HaltsFromTapeEquiv
      (tapeAtCells
        (List.append
          ((encodedLayoutBits layout).reverse.map some)
          [some true, none])
        (none ::
          List.append
            (List.replicate (blankTail + 1) (none : Option Bool))
            (some tailFirst :: tail)))
      (tapeAtCells
        (List.append
          (List.replicate (blankTail + 2) (none : Option Bool))
          (none :: none :: []))
        (List.append
          ((encodedLayoutBits layout).map some)
          (some tailFirst :: tail))) :=
  SeqComposition.seqSubroutine_haltsFromTapeEquiv_of_haltsFromTape_eq
    rightBlankRunTailFirstLeftHandoffDescription_subroutineReady
    rawBoundaryBlockMigrationLoopDescription_subroutineReady
    (rightBlankRunTailFirstLeftHandoffDescription_haltsFrom_guardedWriterExit
      layout blankTail tailFirst tail)
    (tailHandoffHaltTape_move_right_eq_blockMigrationEntry
      layout blankTail tailFirst tail)
    (rawBoundaryBlockMigrationLoopDescription_haltsFrom_blockMigration
      [] true (encodedLayoutBits layout) (blankTail + 2) tailFirst tail)

/-!
## Migration exit to the left-edge endpoint shape

The migrated block leaves only blank cells in its left context, so the
finished tape is equivalent to the same window with the single blank
sentinel left context used by the public left-edge endpoint.
-/

theorem migrationFinishedTape_left_equiv_singleton_blank
    (gap : Nat) (right : List (Option Bool)) :
    Tape.Equiv
      (tapeAtCells
        (List.append (List.replicate gap (none : Option Bool))
          (none :: none :: []))
        right)
      (tapeAtCells [none] right) := by
  cases right <;>
    simp [Tape.Equiv, tapeAtCells, Tape.dropTrailingNone,
      dropTrailingNone_replicate_blank_pair]

theorem migrationFinishedTape_equiv_encodedLeftEdgeForm
    (layout : Word Bool) (gap : Nat) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.Equiv
      (tapeAtCells
        (List.append (List.replicate gap (none : Option Bool))
          (none :: none :: []))
        (List.append
          ((encodedLayoutBits layout).map some)
          (some tailFirst :: tail)))
      (tapeAtCells [none]
        (List.append
          ((encodedLayoutBits layout).map some)
          (some tailFirst :: tail))) :=
  migrationFinishedTape_left_equiv_singleton_blank gap
    (List.append
      ((encodedLayoutBits layout).map some)
      (some tailFirst :: tail))

theorem tailHandoffMigrationSeq_haltsFromEquiv_guardedWriterExit_leftEdge
    (layout : Word Bool) (blankTail : Nat) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (seqSubroutine rightBlankRunTailFirstLeftHandoffDescription
        rawBoundaryBlockMigrationLoopDescription
        Direction.right).HaltsFromTapeEquiv
      (tapeAtCells
        (List.append
          ((encodedLayoutBits layout).reverse.map some)
          [some true, none])
        (none ::
          List.append
            (List.replicate (blankTail + 1) (none : Option Bool))
            (some tailFirst :: tail)))
      (tapeAtCells [none]
        (List.append
          ((encodedLayoutBits layout).map some)
          (some tailFirst :: tail))) :=
  haltsFromTapeEquiv_across_output_equiv
    (tailHandoffMigrationSeq_haltsFromEquiv_guardedWriterExit
      layout blankTail tailFirst tail)
    (migrationFinishedTape_equiv_encodedLeftEdgeForm
      layout (blankTail + 2) tailFirst tail)

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
