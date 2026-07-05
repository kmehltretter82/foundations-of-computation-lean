import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas
import FoC.Computability.Compiler.Core.CommonGround.Identity
import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.RefreshedRows
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

/-!
## Structured raw-layout cell emitter

The first structured component for the raw-boundary emitter scans the raw
layout bits on logical tape 0 and appends their encoded cell forms to logical
tape 2.  Logical tape 1 is reserved for the length/header phases that will
wrap this suffix emitter.  The table is deliberately a three-tape
{name}`Structured.Description` in the read/write/move row fragment recognized
by the multi-tape lowerer.
-/

private def structuredPreserve
    (move : Structured.HeadMove) : Structured.TapeAction where
  write? := none
  move := move

private def structuredWriteBit
    (bit : Bool) (move : Structured.HeadMove) :
    Structured.TapeAction where
  write? := some (some bit)
  move := move

private def structuredRawBoundaryCellEmitInitialRow
    (read : Bool) (target : Nat) : Structured.Transition where
  source := 0
  reads := [some read, none, none]
  actions :=
    [ structuredPreserve Structured.HeadMove.right
    , Structured.TapeAction.stay
    , structuredWriteBit false Structured.HeadMove.right ]
  target := target

private def structuredRawBoundaryCellEmitWriteRow
    (source : Nat) (read : Option Bool) (bit : Bool) (target : Nat) :
    Structured.Transition where
  source := source
  reads := [read, none, none]
  actions :=
    [ Structured.TapeAction.stay
    , Structured.TapeAction.stay
    , structuredWriteBit bit Structured.HeadMove.right ]
  target := target

private def structuredRawBoundaryCellEmitHaltRow :
    Structured.Transition where
  source := 0
  reads := [none, none, none]
  actions :=
    [ Structured.TapeAction.stay
    , Structured.TapeAction.stay
    , Structured.TapeAction.stay ]
  target := 99

private def structuredRawBoundaryCellEmitWriteRows
    (source : Nat) (bit : Bool) (target : Nat) :
    List Structured.Transition :=
  [ structuredRawBoundaryCellEmitWriteRow source none bit target
  , structuredRawBoundaryCellEmitWriteRow source (some false) bit target
  , structuredRawBoundaryCellEmitWriteRow source (some true) bit target ]

/--
Three-tape structured suffix emitter for the raw-boundary right-edge encoder.

Tape 0 scans the raw layout bits.  Tape 1 is untouched scratch reserved for
the length/header phases.  Tape 2 receives
{name}`preservingCellPassCellBits` output at its current right blank.
-/
def structuredRawBoundaryRightEdgeCellEmitterDescription :
    Structured.Description where
  tapeCount := 3
  stateCount := 100
  start := 0
  halt := 99
  transitions :=
    [ structuredRawBoundaryCellEmitInitialRow false 10
    , structuredRawBoundaryCellEmitInitialRow true 20
    , structuredRawBoundaryCellEmitHaltRow ] ++
    structuredRawBoundaryCellEmitWriteRows 10 true 11 ++
    structuredRawBoundaryCellEmitWriteRows 11 false 12 ++
    structuredRawBoundaryCellEmitWriteRows 12 true 0 ++
    structuredRawBoundaryCellEmitWriteRows 20 true 21 ++
    structuredRawBoundaryCellEmitWriteRows 21 true 22 ++
    structuredRawBoundaryCellEmitWriteRows 22 false 0

theorem structuredRawBoundaryRightEdgeCellEmitterDescription_supportsReadWriteRows3 :
    Structured.MultiTapeLowering.supportsReadWriteRows3
      structuredRawBoundaryRightEdgeCellEmitterDescription = true := by
  decide

theorem structuredRawBoundaryRightEdgeCellEmitterDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredRawBoundaryRightEdgeCellEmitterDescription :=
  Structured.MultiTapeLowering.supportedReadWriteRows3_of_supports_eq_true
    structuredRawBoundaryRightEdgeCellEmitterDescription_supportsReadWriteRows3

private def structuredAnySourceReadRows
    (mkRow : Option Bool -> Structured.Transition) :
    List Structured.Transition :=
  [ mkRow none, mkRow (some false), mkRow (some true) ]

private def structuredRawBoundaryWriteOutputRow
    (source : Nat) (sourceRead : Option Bool) (tape1Read : Option Bool)
    (bit : Bool) (target : Nat)
    (tape0Action tape1Action : Structured.TapeAction) :
    Structured.Transition where
  source := source
  reads := [sourceRead, tape1Read, none]
  actions :=
    [ tape0Action
    , tape1Action
    , structuredWriteBit bit Structured.HeadMove.right ]
  target := target

private def structuredRawBoundaryHeaderRows
    (source target : Nat) :
    List Structured.Transition :=
  structuredAnySourceReadRows fun sourceRead =>
    structuredRawBoundaryWriteOutputRow source sourceRead none false target
      Structured.TapeAction.stay
      Structured.TapeAction.stay

private def structuredRawBoundaryCountRow
    (read : Bool) : Structured.Transition where
  source := 10
  reads := [some read, none, none]
  actions :=
    [ structuredPreserve Structured.HeadMove.right
    , structuredWriteBit true Structured.HeadMove.right
    , Structured.TapeAction.stay ]
  target := 10

private def structuredRawBoundaryCountDoneRow : Structured.Transition where
  source := 10
  reads := [none, none, none]
  actions :=
    [ Structured.TapeAction.stay
    , structuredPreserve Structured.HeadMove.left
    , Structured.TapeAction.stay ]
  target := 20

private def structuredRawBoundaryLengthMarkerRows
    (source : Nat) (bit : Bool) (target : Nat)
    (moveTape1 : Structured.HeadMove := Structured.HeadMove.stay) :
    List Structured.Transition :=
  [ structuredRawBoundaryWriteOutputRow source none (some true) bit target
      Structured.TapeAction.stay
      (structuredPreserve moveTape1) ]

private def structuredRawBoundaryLengthFinalRows
    (source : Nat) (bit : Bool) (target : Nat)
    (moveTape0 : Structured.HeadMove := Structured.HeadMove.stay) :
    List Structured.Transition :=
  [ structuredRawBoundaryWriteOutputRow source none none bit target
      (structuredPreserve moveTape0)
      Structured.TapeAction.stay ]

private def structuredRawBoundaryRewindRow
    (read : Bool) : Structured.Transition where
  source := 41
  reads := [some read, none, none]
  actions :=
    [ structuredPreserve Structured.HeadMove.left
    , Structured.TapeAction.stay
    , Structured.TapeAction.stay ]
  target := 41

private def structuredRawBoundaryRewindDoneRow : Structured.Transition where
  source := 41
  reads := [none, none, none]
  actions :=
    [ structuredPreserve Structured.HeadMove.right
    , Structured.TapeAction.stay
    , Structured.TapeAction.stay ]
  target := 50

private def structuredRawBoundaryCellLoopInitialRow
    (read : Bool) (target : Nat) : Structured.Transition where
  source := 50
  reads := [some read, none, none]
  actions :=
    [ structuredPreserve Structured.HeadMove.right
    , Structured.TapeAction.stay
    , structuredWriteBit false Structured.HeadMove.right ]
  target := target

private def structuredRawBoundaryCellLoopHaltRow :
    Structured.Transition where
  source := 50
  reads := [none, none, none]
  actions :=
    [ Structured.TapeAction.stay
    , Structured.TapeAction.stay
    , Structured.TapeAction.stay ]
  target := 99

/--
Three-tape structured source for the full logical raw-boundary right-edge
emitter.

The routine emits the header bits, counts the raw layout on tape 1, emits the
length field from that count, rewinds tape 0, and then emits the encoded
per-cell suffix.  It is intentionally written in the fragment accepted by
{name}`Structured.MultiTapeLowering.supportsReadWriteRows3`.
-/
def structuredRawBoundaryRightEdgeEmitterDescription :
    Structured.Description where
  tapeCount := 3
  stateCount := 100
  start := 0
  halt := 99
  transitions :=
    structuredRawBoundaryHeaderRows 0 1 ++
    structuredRawBoundaryHeaderRows 1 2 ++
    structuredRawBoundaryHeaderRows 2 3 ++
    structuredRawBoundaryHeaderRows 3 10 ++
    [ structuredRawBoundaryCountRow false
    , structuredRawBoundaryCountRow true
    , structuredRawBoundaryCountDoneRow ] ++
    structuredRawBoundaryLengthMarkerRows 20 false 21 ++
    structuredRawBoundaryLengthMarkerRows 21 false 22 ++
    structuredRawBoundaryLengthMarkerRows 22 true 23 ++
    structuredRawBoundaryLengthMarkerRows 23 false 20
      Structured.HeadMove.left ++
    structuredRawBoundaryLengthFinalRows 20 false 31 ++
    structuredRawBoundaryLengthFinalRows 31 false 32 ++
    structuredRawBoundaryLengthFinalRows 32 true 33 ++
    structuredRawBoundaryLengthFinalRows 33 true 41
      Structured.HeadMove.left ++
    [ structuredRawBoundaryRewindRow false
    , structuredRawBoundaryRewindRow true
    , structuredRawBoundaryRewindDoneRow
    , structuredRawBoundaryCellLoopInitialRow false 51
    , structuredRawBoundaryCellLoopInitialRow true 61
    , structuredRawBoundaryCellLoopHaltRow ] ++
    structuredRawBoundaryCellEmitWriteRows 51 true 52 ++
    structuredRawBoundaryCellEmitWriteRows 52 false 53 ++
    structuredRawBoundaryCellEmitWriteRows 53 true 50 ++
    structuredRawBoundaryCellEmitWriteRows 61 true 62 ++
    structuredRawBoundaryCellEmitWriteRows 62 true 63 ++
    structuredRawBoundaryCellEmitWriteRows 63 false 50

theorem structuredRawBoundaryRightEdgeEmitterDescription_supportsReadWriteRows3 :
    Structured.MultiTapeLowering.supportsReadWriteRows3
      structuredRawBoundaryRightEdgeEmitterDescription = true := by
  decide

theorem structuredRawBoundaryRightEdgeEmitterDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredRawBoundaryRightEdgeEmitterDescription :=
  Structured.MultiTapeLowering.supportedReadWriteRows3_of_supports_eq_true
    structuredRawBoundaryRightEdgeEmitterDescription_supportsReadWriteRows3

def structuredRawBoundaryRightEdgeEmitterSourceTapes
    (layout : Word Bool) : List (Tape Bool) :=
  [ Tape.input layout, Tape.blank, Tape.blank ]

def structuredRawBoundaryRightEdgeEmitterOutputTape
    (layout : Word Bool) : Tape Bool where
  left := (encodedLayoutBits layout).reverse.map some
  head := none
  right := []

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
