import FoC.Computability.ListLemmas
import FoC.Computability.Compiler.Core.CommonGround.SameHeadComposition
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.BlankSentinelFinalizer
import FoC.Computability.Compiler.FST.CountWindow.RawBoundary.Impl.EraseTailHeadBlankSentinel

set_option doc.verso true

/-!
# Raw-boundary erased-footprint return

This module bridges the raw-base eraser endpoint back to the blank sentinel
shape consumed by the encoded-layout finalizer.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

def rawFootprintReturnToBlankSentinelDescription
    (skipped count : Word Bool) : MachineDescription :=
  rightMoveAcrossBlanksDescription
    ((List.append skipped count).length +
      tailHeadImmediateScratchCellCount count)

theorem rawFootprintReturnToBlankSentinelDescription_subroutineReady
    (skipped count : Word Bool) :
    (rawFootprintReturnToBlankSentinelDescription
      skipped count).SubroutineReady := by
  rw [rawFootprintReturnToBlankSentinelDescription]
  exact
    rightMoveAcrossBlanksDescription_subroutineReady
      ((List.append skipped count).length +
        tailHeadImmediateScratchCellCount count)

private theorem rawFootprintReturn_rightCells
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    List.append
        (List.replicate (List.append skipped count).length
          (none : Option Bool))
        (none ::
          List.append
            (List.replicate (count.length + 2) (none : Option Bool))
            (none :: tail)) =
      List.append
        (List.replicate
          ((List.append skipped count).length +
            tailHeadImmediateScratchCellCount count)
          (none : Option Bool))
        (none :: tail) := by
  have hscratch :
      none ::
          List.append
            (List.replicate (count.length + 2) (none : Option Bool))
            (none :: tail) =
        List.append
          (List.replicate (tailHeadImmediateScratchCellCount count)
            (none : Option Bool))
          (none :: tail) := by
    calc
      none ::
          List.append
            (List.replicate (count.length + 2) (none : Option Bool))
            (none :: tail) =
        List.append
          (List.replicate (count.length + 2) (none : Option Bool))
          (none :: none :: tail) := by
          exact
            (FoC.Computability.list_replicate_append_cons_eq_cons_append
              (none : Option Bool) (count.length + 2)
              (none :: tail)).symm
      _ =
        List.append
          (List.replicate (count.length + 2 + 1)
            (none : Option Bool))
          (none :: tail) := by
          exact
            FoC.Computability.list_replicate_append_self
              (none : Option Bool) (count.length + 2)
              (none :: tail)
      _ =
        List.append
          (List.replicate (tailHeadImmediateScratchCellCount count)
            (none : Option Bool))
          (none :: tail) := by
          simp [tailHeadImmediateScratchCellCount, Nat.add_assoc]
  rw [hscratch]
  exact
    (FoC.Computability.list_replicate_add_append
      (none : Option Bool)
      (List.append skipped count).length
      (tailHeadImmediateScratchCellCount count)
      (none :: tail)).symm

private theorem rawFootprintReturn_leftCells
    (skipped count : Word Bool) :
    List.append
        (List.replicate
          ((List.append skipped count).length +
            tailHeadImmediateScratchCellCount count)
          (none : Option Bool))
        [none] =
      List.replicate
        (tailHeadImmediateScratchCellCount count +
          (tailHeadRawBaseLeft skipped count).length)
        (none : Option Bool) := by
  calc
    List.append
        (List.replicate
          ((List.append skipped count).length +
            tailHeadImmediateScratchCellCount count)
          (none : Option Bool))
        [none] =
      List.replicate
        (((List.append skipped count).length +
            tailHeadImmediateScratchCellCount count) + 1)
        (none : Option Bool) := by
        simpa using
          FoC.Computability.list_replicate_append_self
            (none : Option Bool)
            ((List.append skipped count).length +
              tailHeadImmediateScratchCellCount count)
            []
    _ =
      List.replicate
        (tailHeadImmediateScratchCellCount count +
          (tailHeadRawBaseLeft skipped count).length)
        (none : Option Bool) := by
        simp [tailHeadImmediateScratchCellCount, tailHeadRawBaseLeft,
          List.length_append, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm]

theorem rawFootprintReturnToBlankSentinelDescription_haltsFrom_erasedLeftBoundary
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    (rawFootprintReturnToBlankSentinelDescription
      skipped count).HaltsFromTape
      (tailHeadRawBaseErasedLeftBoundaryTape skipped count tail)
      (tailHeadErasedBlankSentinelTape skipped count tail) := by
  rw [rawFootprintReturnToBlankSentinelDescription,
    tailHeadRawBaseErasedLeftBoundaryTape,
    leftBoundaryEraserTargetTape,
    tailHeadErasedBlankSentinelTape]
  rw [rawFootprintReturn_rightCells skipped count tail]
  rw [← rawFootprintReturn_leftCells skipped count]
  exact
    rightMoveAcrossBlanksDescription_haltsFromTape
      ((List.append skipped count).length +
        tailHeadImmediateScratchCellCount count)
      ([none] : List (Option Bool))
      (none : Option Bool)
      tail

theorem tailHeadBlankSentinelRawBaseEdgeTape_moveLeftRight
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tailHeadBlankSentinelRawBaseEdgeTape skipped count tail)) =
      tailHeadBlankSentinelRawBaseEdgeTape skipped count tail := by
  rw [tailHeadBlankSentinelRawBaseEdgeTape, tailHeadRawBaseLeft]
  exact
    tapeAtCells_move_right_move_left_append_singleton
      ((List.append skipped count).reverse.map some)
      none
      (List.append
        (List.replicate (tailHeadImmediateScratchCellCount count)
          (none : Option Bool))
        (none :: tail))

theorem tailHeadRawBaseErasedLeftBoundaryTape_moveLeftRight
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tailHeadRawBaseErasedLeftBoundaryTape skipped count tail)) =
      tailHeadRawBaseErasedLeftBoundaryTape skipped count tail := by
  rw [tailHeadRawBaseErasedLeftBoundaryTape,
    leftBoundaryEraserTargetTape]
  rw [rawFootprintReturn_rightCells skipped count tail]
  let n :=
    (List.append skipped count).length +
      tailHeadImmediateScratchCellCount count
  change
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells [none]
            (List.append (List.replicate n (none : Option Bool))
              (none :: tail)))) =
      tapeAtCells [none]
        (List.append (List.replicate n (none : Option Bool))
          (none :: tail))
  have hright :
      List.append (List.replicate n (none : Option Bool))
          (none :: tail) =
        none :: List.append (List.replicate n (none : Option Bool))
          tail :=
    FoC.Computability.list_replicate_append_cons_eq_cons_append
      (none : Option Bool) n tail
  rw [hright]
  exact
    tapeAtCells_move_right_move_left_cons
      none [] none
      (List.append (List.replicate n (none : Option Bool)) tail)

def tailHeadRawFootprintClearToLeftBoundaryDescription
    (count : Word Bool) : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    (leftMoveAcrossBlanksDescription
      (tailHeadImmediateScratchCellCount count))
    eraseTailHeadRawBaseFromEdgeDescription

theorem tailHeadRawFootprintClearToLeftBoundaryDescription_subroutineReady
    (count : Word Bool) :
    (tailHeadRawFootprintClearToLeftBoundaryDescription
      count).SubroutineReady := by
  rw [tailHeadRawFootprintClearToLeftBoundaryDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
      (leftMoveAcrossBlanksDescription_subroutineReady
        (tailHeadImmediateScratchCellCount count))
      eraseTailHeadRawBaseFromEdgeDescription_subroutineReady

theorem tailHeadRawFootprintClearToLeftBoundaryDescription_haltsFrom_rawLeft
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    (tailHeadRawFootprintClearToLeftBoundaryDescription
      count).HaltsFromTape
      (tailHeadBlankSentinelRawLeftTape skipped count tail)
      (tailHeadRawBaseErasedLeftBoundaryTape skipped count tail) := by
  rw [tailHeadRawFootprintClearToLeftBoundaryDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
      (leftMoveAcrossBlanksDescription_subroutineReady
        (tailHeadImmediateScratchCellCount count))
      eraseTailHeadRawBaseFromEdgeDescription_subroutineReady
      (leftMoveAcrossBlanksDescription_haltsFrom_tailHeadBlankSentinelRawLeftTape
        skipped count tail)
      (tailHeadBlankSentinelRawBaseEdgeTape_moveLeftRight
        skipped count tail)
      (eraseTailHeadRawBaseFromEdgeDescription_haltsFrom_rawBaseEdge
        skipped count tail)

def tailHeadRawFootprintClearToBlankSentinelDescription
    (skipped count : Word Bool) : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    (tailHeadRawFootprintClearToLeftBoundaryDescription count)
    (rawFootprintReturnToBlankSentinelDescription skipped count)

theorem tailHeadRawFootprintClearToBlankSentinelDescription_subroutineReady
    (skipped count : Word Bool) :
    (tailHeadRawFootprintClearToBlankSentinelDescription
      skipped count).SubroutineReady := by
  rw [tailHeadRawFootprintClearToBlankSentinelDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
      (tailHeadRawFootprintClearToLeftBoundaryDescription_subroutineReady
        count)
      (rawFootprintReturnToBlankSentinelDescription_subroutineReady
        skipped count)

theorem tailHeadRawFootprintClearToBlankSentinelDescription_haltsFrom_rawLeft
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    (tailHeadRawFootprintClearToBlankSentinelDescription
      skipped count).HaltsFromTape
      (tailHeadBlankSentinelRawLeftTape skipped count tail)
      (tailHeadErasedBlankSentinelTape skipped count tail) := by
  rw [tailHeadRawFootprintClearToBlankSentinelDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
      (tailHeadRawFootprintClearToLeftBoundaryDescription_subroutineReady
        count)
      (rawFootprintReturnToBlankSentinelDescription_subroutineReady
        skipped count)
      (tailHeadRawFootprintClearToLeftBoundaryDescription_haltsFrom_rawLeft
        skipped count tail)
      (tailHeadRawBaseErasedLeftBoundaryTape_moveLeftRight
        skipped count tail)
      (rawFootprintReturnToBlankSentinelDescription_haltsFrom_erasedLeftBoundary
        skipped count tail)

theorem tailHeadBlankSentinelRawLeftTape_moveLeftRight
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tailHeadBlankSentinelRawLeftTape skipped count tail)) =
      tailHeadBlankSentinelRawLeftTape skipped count tail := by
  rw [tailHeadBlankSentinelRawLeftTape]
  simp [tailHeadImmediateScratchCellCount, List.replicate_succ]
  exact
    tapeAtCells_move_right_move_left_cons
      none
      (List.append
        (List.replicate (count.length + 2) (none : Option Bool))
        (tailHeadRawBaseLeft skipped count))
      none tail

theorem tailHeadErasedBlankSentinelTape_moveLeftRight
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tailHeadErasedBlankSentinelTape skipped count tail)) =
      tailHeadErasedBlankSentinelTape skipped count tail := by
  rw [tailHeadErasedBlankSentinelTape]
  rw [show
      tailHeadImmediateScratchCellCount count +
          (tailHeadRawBaseLeft skipped count).length =
        Nat.succ
          (count.length + 2 +
            (tailHeadRawBaseLeft skipped count).length) by
    simp [tailHeadImmediateScratchCellCount]
    lia]
  simp [List.replicate_succ]
  exact
    tapeAtCells_move_right_move_left_cons
      none
      (List.replicate
        (count.length + 2 + (tailHeadRawBaseLeft skipped count).length)
        (none : Option Bool))
      none tail

def rawBoundarySourceToErasedBlankSentinelDescription
    (skipped count : Word Bool) (tailFirst : Bool) :
    MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    (sourceToTailHeadBlankSentinelDescription tailFirst)
    (tailHeadRawFootprintClearToBlankSentinelDescription skipped count)

theorem rawBoundarySourceToErasedBlankSentinelDescription_subroutineReady
    (skipped count : Word Bool) (tailFirst : Bool) :
    (rawBoundarySourceToErasedBlankSentinelDescription
      skipped count tailFirst).SubroutineReady := by
  rw [rawBoundarySourceToErasedBlankSentinelDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
      (sourceToTailHeadBlankSentinelDescription_subroutineReady tailFirst)
      (tailHeadRawFootprintClearToBlankSentinelDescription_subroutineReady
        skipped count)

theorem rawBoundarySourceToErasedBlankSentinelDescription_haltsFrom_sourceTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (rawBoundarySourceToErasedBlankSentinelDescription
      skipped count tailFirst).HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (tailHeadErasedBlankSentinelTape skipped count tail) := by
  rw [rawBoundarySourceToErasedBlankSentinelDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
      (sourceToTailHeadBlankSentinelDescription_subroutineReady tailFirst)
      (tailHeadRawFootprintClearToBlankSentinelDescription_subroutineReady
        skipped count)
      (sourceToTailHeadBlankSentinelDescription_haltsFrom_sourceTape
        skipped count tailFirst tail)
      (tailHeadBlankSentinelRawLeftTape_moveLeftRight
        skipped count tail)
      (tailHeadRawFootprintClearToBlankSentinelDescription_haltsFrom_rawLeft
        skipped count tail)

def rawBoundaryBlankSentinelRouteDescription
    (skipped count : Word Bool) (tailFirst : Bool) :
    MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    (rawBoundarySourceToErasedBlankSentinelDescription
      skipped count tailFirst)
    (rawBoundaryBlankSentinelFinalizerDescription
      skipped count tailFirst)

theorem rawBoundaryBlankSentinelRouteDescription_subroutineReady
    (skipped count : Word Bool) (tailFirst : Bool) :
    (rawBoundaryBlankSentinelRouteDescription
      skipped count tailFirst).SubroutineReady := by
  rw [rawBoundaryBlankSentinelRouteDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
      (rawBoundarySourceToErasedBlankSentinelDescription_subroutineReady
        skipped count tailFirst)
      (rawBoundaryBlankSentinelFinalizerDescription_subroutineReady
        skipped count tailFirst)

theorem rawBoundaryBlankSentinelRouteDescription_haltsFrom_sourceTape_rightEdgeTapeEquiv
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    (rawBoundaryBlankSentinelRouteDescription
      skipped count tailFirst).HaltsFromTapeEquiv
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) := by
  rw [rawBoundaryBlankSentinelRouteDescription]
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
      (rawBoundarySourceToErasedBlankSentinelDescription_subroutineReady
        skipped count tailFirst)
      (rawBoundaryBlankSentinelFinalizerDescription_subroutineReady
        skipped count tailFirst)
      (rawBoundarySourceToErasedBlankSentinelDescription_haltsFrom_sourceTape
        skipped count tailFirst tail)
      (tailHeadErasedBlankSentinelTape_moveLeftRight
        skipped count tail)
      (rawBoundaryBlankSentinelFinalizerDescription_haltsFrom_erasedTailHeadHandoff_rightEdgeTapeEquiv
        skipped count tailFirst tail)

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
