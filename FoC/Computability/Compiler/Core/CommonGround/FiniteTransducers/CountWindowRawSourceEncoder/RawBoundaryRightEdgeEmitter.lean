import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.CellPass

set_option doc.verso true

/-!
# Count-window raw-boundary right-edge emitter

This module isolates the finite-machine leaf for the count-window raw-source
encoder.  The input head is on the raw boundary blank after the layout bits;
the right side contains the repaired count-window gap and a live nonblank tail
head.  The desired output is the encoded header/bool-word layout, positioned
immediately to the left of that live tail and halted on the right edge of the
encoded word.

The direct controller-initial header emitter is the model for the phase
structure, but cannot be reused unchanged because it writes into right-side
scratch and would overwrite the live tail.  The finite table for this leaf
should duplicate that phase structure with the following live-tail-safe order:

* preserve a recoverable count while scanning the raw bits;
* emit the cell-code suffix before the live tail without crossing unread bits;
* emit the unary length field from the preserved count markers;
* emit the header field;
* halt at the right edge of the emitted encoded word, immediately left of the
  live tail.

The parent count-window raw-source encoder module specializes this local
contract to the public count-window names.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers
namespace CountWindowRawSourceEncoder
namespace RawBoundaryRightEdgeEmitter

def sourceTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  tapeAtCells
    (List.append ((List.append skipped count).reverse.map some) [none])
    (none ::
      none ::
      none ::
      List.append
        (List.replicate count.length (none : Option Bool))
        tail)

def encodedLayoutBits (layout : Word Bool) : Word Bool :=
  encodeCodeWordAsInput
    (MachineCodeSymbol.header :: encodeBoolWordAppend layout [])

def rightEdgeTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    ((encodedLayoutBits (List.append skipped count)).reverse.map some)
    (some tailFirst :: tail)

def preRewindTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) : Tape Bool :=
  Tape.move Direction.left
    (rightEdgeTape skipped count tailFirst tail)

theorem sourceTape_cells
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.cells (sourceTape skipped count tail) =
      none ::
        List.append ((List.append skipped count).map some)
          (none ::
            none ::
            none ::
            List.append
              (List.replicate count.length (none : Option Bool))
              tail) := by
  simp [sourceTape, Tape.cells, tapeAtCells, List.reverse_append,
    List.map_reverse, List.append_assoc]

theorem rightEdgeTape_cells
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells (rightEdgeTape skipped count tailFirst tail) =
      List.append
        ((encodedLayoutBits (List.append skipped count)).map some)
        (some tailFirst :: tail) := by
  rw [rightEdgeTape, encodedLayoutBits]
  change
    Tape.cells
        (tapeAtCells
          ((encodeCodeWordAsInput
            (MachineCodeSymbol.header ::
              encodeBoolWordAppend (List.append skipped count) [])).reverse.map
            some)
          (some tailFirst :: tail)) =
      List.append
        ((encodeCodeWordAsInput
          (MachineCodeSymbol.header ::
            encodeBoolWordAppend (List.append skipped count) [])).map some)
        (some tailFirst :: tail)
  rw [show
      (encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend (List.append skipped count) [])).reverse.map
          some =
        List.append
          ((encodeCodeWordAsInput
            (encodeBoolWordAppend (List.append skipped count) [])).reverse.map
            some)
          [some false, some false, some false, some false] by
    simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      List.map_append, List.append_assoc]]
  simp [Tape.cells, tapeAtCells, encodeCodeWordAsInput,
    encodeCodeSymbolAsInput]

theorem encodedLayoutBits_eq_headerQuoteBits
    (layout : Word Bool) :
    encodedLayoutBits layout =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            layout.length)
          (EncodedRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.preservingCellPassCellBits
            layout)) := by
  exact
    (EncodedRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.preservingCellPassHeaderQuoteBits_eq_encodeBoolWordAppend
      layout).symm

theorem encodedLayoutBits_eq_header_length_cells
    (layout : Word Bool) :
    encodedLayoutBits layout =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            layout.length)
          (EncodedRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.preservingCellPassCellBits
            layout)) :=
  encodedLayoutBits_eq_headerQuoteBits layout

theorem tapeAtCells_moveRight_moveLeft_append_headerBits
    (pref right : List (Option Bool)) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            (List.append pref
              [some false, some false, some false, some false])
            right)) =
      tapeAtCells
        (List.append pref
          [some false, some false, some false, some false])
        right := by
  cases pref <;> cases right <;>
    simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem preRewindTape_moveRight
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.move Direction.right
        (preRewindTape skipped count tailFirst tail) =
      rightEdgeTape skipped count tailFirst tail := by
  rw [preRewindTape, rightEdgeTape, encodedLayoutBits]
  change
    Tape.move Direction.right
        (Tape.move Direction.left
          (tapeAtCells
            ((encodeCodeWordAsInput
              (MachineCodeSymbol.header ::
                encodeBoolWordAppend (List.append skipped count) [])).reverse.map
              some)
            (some tailFirst :: tail))) =
      tapeAtCells
        ((encodeCodeWordAsInput
          (MachineCodeSymbol.header ::
            encodeBoolWordAppend (List.append skipped count) [])).reverse.map
          some)
        (some tailFirst :: tail)
  rw [show
      (encodeCodeWordAsInput
        (MachineCodeSymbol.header ::
          encodeBoolWordAppend (List.append skipped count) [])).reverse.map
          some =
        List.append
          ((encodeCodeWordAsInput
            (encodeBoolWordAppend (List.append skipped count) [])).reverse.map
            some)
          [some false, some false, some false, some false] by
    simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      List.map_append, List.append_assoc]]
  exact
    tapeAtCells_moveRight_moveLeft_append_headerBits
      ((encodeCodeWordAsInput
        (encodeBoolWordAppend (List.append skipped count) [])).reverse.map
        some)
      (some tailFirst :: tail)

theorem rightEdgeTape_rewind_haltsFromTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rightEdgeRewindDescription.HaltsFromTape
      (rightEdgeTape skipped count tailFirst tail)
      (tapeAtCells [none]
        (List.append
          ((encodedLayoutBits (List.append skipped count)).map some)
          (some tailFirst :: tail))) := by
  simpa [rightEdgeTape] using
    rightEdgeRewindDescription_haltsFrom_rightEdge_noDelimiter
      (encodedLayoutBits (List.append skipped count))
      tailFirst tail

theorem rightEdgeTape_rewind_target_cells
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    Tape.cells
        (tapeAtCells [none]
          (List.append
            ((encodedLayoutBits (List.append skipped count)).map some)
            (some tailFirst :: tail))) =
      none ::
        List.append
          ((encodedLayoutBits (List.append skipped count)).map some)
          (some tailFirst :: tail) := by
  rw [encodedLayoutBits]
  change
    Tape.cells
        (tapeAtCells [none]
          (List.append
            ((encodeCodeWordAsInput
              (MachineCodeSymbol.header ::
                encodeBoolWordAppend (List.append skipped count) [])).map
              some)
            (some tailFirst :: tail))) =
      none ::
        List.append
          ((encodeCodeWordAsInput
            (MachineCodeSymbol.header ::
              encodeBoolWordAppend (List.append skipped count) [])).map some)
          (some tailFirst :: tail)
  simp [Tape.cells, tapeAtCells, encodeCodeWordAsInput,
    encodeCodeSymbolAsInput]

def Spec (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    forall (skipped count : Word Bool)
      (tailFirst : Bool) (tail : List (Option Bool)),
      emitter.HaltsFromTape
        (sourceTape skipped count (some tailFirst :: tail))
        (preRewindTape skipped count tailFirst tail)

def Construction : Prop :=
  exists emitter : MachineDescription, Spec emitter

theorem construction_core : Construction := by
  sorry

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
