import FoC.Computability.Compiler.DescriptionExecution
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoundaryEraser
import FoC.Computability.Compiler.ClosedCfg.ProjTail.SelectedFootprintCompactionShape

set_option doc.verso true

/-!
# Guarded structured-prefix eraser shape

This module isolates the reusable endpoint view for deleting the two guarded
structured logical-tape fields that precede the selected logical-tape decoder
footprint.  The concrete handoff module adapts these generic contracts back to
the selected-segment theorem names.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

/-- Encoded two-tape structured prefix consumed by the eraser handoff. -/
def guardedTwoTapeStructuredPrefixCells
    (T0 T1 : Tape Bool) : List (Option Bool) :=
  encodedStructuredTapeCellsPrefix
    [guardLogicalTape T0, guardLogicalTape T1]

/-- Source tape for the generic guarded two-tape prefix eraser. -/
def guardedTwoTapeStructuredPrefixEraserSourceTape
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  selectedSegmentLogicalTapeDecoderTargetTape
    (rightEdgeScanSourceTapeFromLeft [none] bits padding)
    (guardedTwoTapeStructuredPrefixCells T0 T1)

/-- Target tape for the generic guarded two-tape prefix eraser. -/
def guardedTwoTapeStructuredPrefixEraserTargetTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape Bool :=
  selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
    (selectedSegmentLogicalTapeDecoderPayloadCells bits padding)

theorem guardedTwoTapeStructuredPrefixCells_eq
    (T0 T1 : Tape Bool) :
    guardedTwoTapeStructuredPrefixCells T0 T1 =
      encodedStructuredTapeCellsPrefix
        [guardLogicalTape T0, guardLogicalTape T1] := by
  rfl

theorem guardedTwoTapeStructuredPrefixCells_expanded
    (T0 T1 : Tape Bool) :
    guardedTwoTapeStructuredPrefixCells T0 T1 =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape T0))
          (List.append tapeSeparatorCells
            (logicalTapeCode (guardLogicalTape T1)))) := by
  simp [guardedTwoTapeStructuredPrefixCells,
    encodedStructuredTapeCellsPrefix]

theorem logicalCellBits_length_guardedShape
    (cell : Option Bool) :
    (logicalCellBits cell).length = 2 := by
  cases cell with
  | none =>
      rfl
  | some bit =>
      cases bit <;> rfl

theorem logicalCellListBits_length_guardedShape
    (cells : List (Option Bool)) :
    (logicalCellListBits cells).length = 2 * cells.length := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [logicalCellListBits, logicalCellBits_length_guardedShape,
        ih]
      lia

theorem logicalTapeBits_length_guardedShape
    (T : Tape Bool) :
    (logicalTapeBits T).length =
      2 * T.left.length + 2 * T.right.length + 4 := by
  simp [logicalTapeBits, logicalCellListBits_length_guardedShape,
    logicalCellBits_length_guardedShape]
  lia

theorem guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    guardedTwoTapeStructuredPrefixEraserTargetTape bits padding =
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        bits padding := by
  rw [guardedTwoTapeStructuredPrefixEraserTargetTape]
  rw [selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape]
  rw [selectedSegmentLogicalTapeDecoderFootprintSourceTape_eq_fromPayload]

/--
Reusable contract for the finite eraser that deletes the two guarded
structured logical-tape fields before the selected decoder footprint.
-/
def GuardedTwoTapeStructuredPrefixEraserSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)
        (guardedTwoTapeStructuredPrefixEraserTargetTape
          bits padding)

def GuardedTwoTapeStructuredPrefixEraserConstruction : Prop :=
  exists eraser : MachineDescription,
    GuardedTwoTapeStructuredPrefixEraserSpec eraser

def GuardedTwoTapeStructuredPrefixEraserNilPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall T0 T1 : Tape Bool,
      eraser.HaltsFromTapeEquiv
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])
        (guardedTwoTapeStructuredPrefixEraserTargetTape [] [])) ∧
    (forall (T0 T1 : Tape Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding))
        (guardedTwoTapeStructuredPrefixEraserTargetTape
          [] (none :: padding))) ∧
    forall (T0 T1 : Tape Bool) (padBit : Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding))
        (guardedTwoTapeStructuredPrefixEraserTargetTape
          [] (some padBit :: padding))

def GuardedTwoTapeStructuredPrefixEraserConsPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeEquiv
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])
        (guardedTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) [])) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding))
        (guardedTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) (none :: padding))) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding))
        (guardedTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) (some padBit :: padding))

def GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  GuardedTwoTapeStructuredPrefixEraserNilPadSymbolCaseSpec eraser ∧
    GuardedTwoTapeStructuredPrefixEraserConsPadSymbolCaseSpec eraser

def GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction :
    Prop :=
  exists eraser : MachineDescription,
    GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec eraser

theorem guardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec_of_spec
    {eraser : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixEraserSpec eraser) :
    GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec eraser := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro T0 T1
      exact hrun T0 T1 [] []
    · intro T0 T1 padding
      exact hrun T0 T1 [] (none :: padding)
    · intro T0 T1 padBit padding
      exact hrun T0 T1 [] (some padBit :: padding)
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro T0 T1 bit rest
      exact hrun T0 T1 (bit :: rest) []
    · intro T0 T1 bit rest padding
      exact hrun T0 T1 (bit :: rest) (none :: padding)
    · intro T0 T1 bit rest padBit padding
      exact hrun T0 T1 (bit :: rest) (some padBit :: padding)

theorem guardedTwoTapeStructuredPrefixEraserSpec_of_splitPadSymbolCaseSpec
    {eraser : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
        eraser) :
    GuardedTwoTapeStructuredPrefixEraserSpec eraser := by
  rcases h with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  cases bits with
  | nil =>
      cases padding with
      | nil =>
          exact hnilNil T0 T1
      | cons pad padding =>
          cases pad with
          | none =>
              exact hnilNone T0 T1 padding
          | some padBit =>
              exact hnilSome T0 T1 padBit padding
  | cons bit rest =>
      cases padding with
      | nil =>
          exact hconsNil T0 T1 bit rest
      | cons pad padding =>
          cases pad with
          | none =>
              exact hconsNone T0 T1 bit rest padding
          | some padBit =>
              exact hconsSome T0 T1 bit rest padBit padding

theorem guardedTwoTapeStructuredPrefixEraserConstruction_of_splitPadSymbolCases
    (h :
      GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction) :
    GuardedTwoTapeStructuredPrefixEraserConstruction := by
  rcases h with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      guardedTwoTapeStructuredPrefixEraserSpec_of_splitPadSymbolCaseSpec
        hspec⟩

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
