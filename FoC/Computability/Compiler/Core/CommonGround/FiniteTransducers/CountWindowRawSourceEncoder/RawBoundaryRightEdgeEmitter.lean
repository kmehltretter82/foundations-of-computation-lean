import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas
import FoC.Computability.Compiler.Core.CommonGround.Identity
import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind
import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.Assembly.Prefix
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
open EncodedRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf

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

-- Defaulted source view for the finite leaf: raw layout bits are followed by
-- the erased count-window gap and then the live tail.
theorem sourceTape_defaultedCells
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells (sourceTape skipped count tail)) =
      false ::
        List.append (List.append skipped count)
          (false ::
            false ::
              false ::
                List.append (List.replicate count.length false)
                  (tail.map optionBitDefaultFalse)) := by
  rw [sourceTape_cells]
  simp [List.map_append, List.append_assoc,
    FoC.Computability.EncodedRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse,
    FoC.Computability.EncodedRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse_map_some]

def entryTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape Bool :=
  Tape.move Direction.left (sourceTape skipped count tail)

def entryDescription : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 none none Direction.left 1 ]

theorem entryDescription_wellFormed :
    entryDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := entryDescription.transitions)
      (stateCount := entryDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := entryDescription.transitions)
      (by decide)

theorem entryDescription_haltTransitionFree :
    entryDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := entryDescription.transitions)
    (state := entryDescription.halt)
    (by decide)

theorem entryDescription_subroutineReady :
    entryDescription.SubroutineReady :=
  ⟨entryDescription_wellFormed,
    entryDescription_haltTransitionFree⟩

theorem entryDescription_run_sourceTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    entryDescription.runConfig 1
        { state := entryDescription.start
          tape := sourceTape skipped count tail } =
      { state := entryDescription.halt
        tape := entryTape skipped count tail } := by
  simp [entryDescription, entryTape, sourceTape, tapeAtCells, runConfig,
    stepConfig, lookupTransition, Matches, transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft]

theorem entryDescription_haltsFrom_sourceTape
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    entryDescription.HaltsFromTape
      (sourceTape skipped count tail)
      (entryTape skipped count tail) := by
  refine ⟨1, ?_⟩
  constructor <;>
    rw [entryDescription_run_sourceTape]

theorem entryTape_moveRight
    (skipped count : Word Bool) (tail : List (Option Bool)) :
    Tape.move Direction.right (entryTape skipped count tail) =
      sourceTape skipped count tail := by
  rw [entryTape, sourceTape]
  exact
    tapeAtCells_move_right_move_left_append_singleton
      ((List.append skipped count).reverse.map some)
      (none : Option Bool)
      (none ::
        none ::
        none ::
        List.append
          (List.replicate count.length (none : Option Bool))
          tail)

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

-- Defaulted target view just before the final rewind: the encoded layout is
-- immediately followed by the nonblank live-tail head.
theorem rightEdgeTape_defaultedCells
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells (rightEdgeTape skipped count tailFirst tail)) =
      List.append
        (encodedLayoutBits (List.append skipped count))
        (tailFirst :: tail.map optionBitDefaultFalse) := by
  rw [rightEdgeTape_cells]
  simp [List.map_append,
    FoC.Computability.EncodedRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse,
    FoC.Computability.EncodedRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse_map_some]

private theorem encodedLayoutBits_eq_headerQuoteBits
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

private theorem encodedLayoutBits_eq_header_length_cells
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

def rightToLeftEncodedLayoutBits (layout : Word Bool) : Word Bool :=
  List.append
    (EncodedRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.preservingCellPassCellBits
      layout).reverse
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        layout.length).reverse
      (encodeCodeSymbolAsInput MachineCodeSymbol.header).reverse)

private theorem rightToLeftEncodedLayoutBits_eq_reverse
    (layout : Word Bool) :
    rightToLeftEncodedLayoutBits layout =
      (encodedLayoutBits layout).reverse := by
  rw [encodedLayoutBits_eq_header_length_cells]
  simp [rightToLeftEncodedLayoutBits, List.reverse_append,
    List.append_assoc]

theorem rightEdgeTape_eq_rightToLeftEncodedLayoutBits
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rightEdgeTape skipped count tailFirst tail =
      tapeAtCells
        ((rightToLeftEncodedLayoutBits
          (List.append skipped count)).map some)
        (some tailFirst :: tail) := by
  rw [rightEdgeTape, rightToLeftEncodedLayoutBits_eq_reverse]

theorem preRewindTape_eq_rightToLeftEncodedLayoutBits
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    preRewindTape skipped count tailFirst tail =
      Tape.move Direction.left
        (tapeAtCells
          ((rightToLeftEncodedLayoutBits
            (List.append skipped count)).map some)
          (some tailFirst :: tail)) := by
  rw [preRewindTape, rightEdgeTape_eq_rightToLeftEncodedLayoutBits]

private theorem tapeAtCells_moveRight_moveLeft_append_headerBits
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

-- The public count-window encoder composes the local emitter with this rewind;
-- this defaulted view records the shape after that packaging step.
theorem rightEdgeTape_rewind_target_defaultedCells
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (tapeAtCells [none]
            (List.append
              ((encodedLayoutBits (List.append skipped count)).map some)
              (some tailFirst :: tail)))) =
      false ::
        List.append
          (encodedLayoutBits (List.append skipped count))
          (tailFirst :: tail.map optionBitDefaultFalse) := by
  rw [rightEdgeTape_rewind_target_cells]
  simp [List.map_append,
    FoC.Computability.EncodedRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse,
    FoC.Computability.EncodedRewriters.BoundedLayoutRunner.SelectedProjectionInputQuoterFiniteLeaf.optionBitDefaultFalse_map_some]

def rawBoundaryRightEdgeEmitterCoreDescription :
    MachineDescription :=
  entryDescription

theorem rawBoundaryRightEdgeEmitterCoreDescription_subroutineReady :
    rawBoundaryRightEdgeEmitterCoreDescription.SubroutineReady := by
  rw [rawBoundaryRightEdgeEmitterCoreDescription]
  exact entryDescription_subroutineReady

def rawBoundaryRightEdgeEmitterDescription :
    MachineDescription :=
  seqSubroutine rawBoundaryRightEdgeEmitterCoreDescription
    ExactIdentityDescription Direction.left

theorem rawBoundaryRightEdgeEmitterDescription_subroutineReady :
    rawBoundaryRightEdgeEmitterDescription.SubroutineReady := by
  rw [rawBoundaryRightEdgeEmitterDescription]
  exact
    seqSubroutine_subroutineReady
      rawBoundaryRightEdgeEmitterCoreDescription_subroutineReady
      CommonGround.Identity.exactIdentityDescription_subroutineReady

-- If this core run theorem cannot be proved for the chosen core table, the
-- core machine itself needs to be reconsidered rather than hidden behind the
-- public construction wrapper.
theorem rawBoundaryRightEdgeEmitterCoreDescription_haltsFrom_sourceTape_rightEdge
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundaryRightEdgeEmitterCoreDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (rightEdgeTape skipped count tailFirst tail) := by
  sorry

theorem rawBoundaryRightEdgeEmitterDescription_haltsFrom_sourceTape
    (skipped count : Word Bool) (tailFirst : Bool)
    (tail : List (Option Bool)) :
    rawBoundaryRightEdgeEmitterDescription.HaltsFromTape
      (sourceTape skipped count (some tailFirst :: tail))
      (preRewindTape skipped count tailFirst tail) := by
  rw [rawBoundaryRightEdgeEmitterDescription, preRewindTape]
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      rawBoundaryRightEdgeEmitterCoreDescription_subroutineReady
      CommonGround.Identity.exactIdentityDescription_subroutineReady
      (rawBoundaryRightEdgeEmitterCoreDescription_haltsFrom_sourceTape_rightEdge
        skipped count tailFirst tail)
      rfl
      (CommonGround.Identity.exactIdentityDescription_haltsFromTape
        (Tape.move Direction.left
          (rightEdgeTape skipped count tailFirst tail)))

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
  refine ⟨rawBoundaryRightEdgeEmitterDescription, ?_⟩
  constructor
  · exact rawBoundaryRightEdgeEmitterDescription_subroutineReady
  · intro skipped count tailFirst tail
    exact
      rawBoundaryRightEdgeEmitterDescription_haltsFrom_sourceTape
        skipped count tailFirst tail

end RawBoundaryRightEdgeEmitter
end CountWindowRawSourceEncoder
end FiniteTransducers
end CommonGround

end Computability
end FoC
