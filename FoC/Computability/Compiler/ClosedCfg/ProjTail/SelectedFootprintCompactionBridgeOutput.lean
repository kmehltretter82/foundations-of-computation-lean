import FoC.Computability.Compiler.ClosedCfg.ProjTail.SelectedFootprintCompaction

set_option doc.verso true

/-!
# Right-end selected-footprint bridge output splits

The exact selected-footprint bridge is already split into nil/cons and
padding-symbol cases.  The output-only bridge was still stated only as one
uniform contract.  This module adds the parallel output branch surface at the
right-end bridge boundary, so callers that only consume normalized output can
depend on the same case structure without requiring exact final cursor
positions.
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

private theorem haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTapeEquiv Tin Tout) :
    D.HaltsFromTapeWithOutput Tin (Tape.normalizedOutput Tout) :=
  MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv h

/-! ## Branch output contracts -/

def SelectedFootprintCompactorBridgeOutputCaseSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    (forall padding : List (Option Bool),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] padding))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape [] padding))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) padding))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape (bit :: rest) padding))

def SelectedFootprintCompactorBridgeOutputCaseConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedFootprintCompactorBridgeOutputCaseSpec compactor

def SelectedFootprintCompactorBridgeOutputBitPaddingCaseSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    compactor.HaltsFromTapeWithOutput
      (rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          [] []))
      (Tape.normalizedOutput
        (rightEdgeRewindSourceTape [] [])) ∧
    (forall (pad : Option Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] (pad :: padding)))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape [] (pad :: padding)))) ∧
    (forall (bit : Bool) (rest : Word Bool),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) []))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape (bit :: rest) []))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (pad : Option Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) (pad :: padding)))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape (bit :: rest)
            (pad :: padding)))

def SelectedFootprintCompactorBridgeOutputBitPaddingCaseConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedFootprintCompactorBridgeOutputBitPaddingCaseSpec compactor

def SelectedFootprintCompactorBridgeOutputNilPadSymbolCaseSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    compactor.HaltsFromTapeWithOutput
      (rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          [] []))
      (Tape.normalizedOutput
        (rightEdgeRewindSourceTape [] [])) ∧
    (forall padding : List (Option Bool),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] (none :: padding)))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape [] (none :: padding)))) ∧
    forall (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] (some padBit :: padding)))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape [] (some padBit :: padding)))

def SelectedFootprintCompactorBridgeOutputConsPadSymbolCaseSpec
    (compactor : MachineDescription) : Prop :=
  compactor.SubroutineReady ∧
    (forall (bit : Bool) (rest : Word Bool),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) []))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape (bit :: rest) []))) ∧
    (forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) (none :: padding)))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape (bit :: rest)
            (none :: padding)))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      compactor.HaltsFromTapeWithOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) (some padBit :: padding)))
        (Tape.normalizedOutput
          (rightEdgeRewindSourceTape (bit :: rest)
            (some padBit :: padding)))

def SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec
    (compactor : MachineDescription) : Prop :=
  SelectedFootprintCompactorBridgeOutputNilPadSymbolCaseSpec
      compactor ∧
    SelectedFootprintCompactorBridgeOutputConsPadSymbolCaseSpec
      compactor

def SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseConstruction :
    Prop :=
  exists compactor : MachineDescription,
    SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec
      compactor

/-! ## Accessors -/

theorem SelectedFootprintCompactorBridgeOutputCaseSpec.subroutineReady
    {compactor : MachineDescription}
    (h : SelectedFootprintCompactorBridgeOutputCaseSpec
      compactor) :
    compactor.SubroutineReady :=
  h.left

theorem SelectedFootprintCompactorBridgeOutputCaseSpec.nil
    {compactor : MachineDescription}
    (h : SelectedFootprintCompactorBridgeOutputCaseSpec
      compactor)
    (padding : List (Option Bool)) :
    compactor.HaltsFromTapeWithOutput
      (rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          [] padding))
      (Tape.normalizedOutput
        (rightEdgeRewindSourceTape [] padding)) :=
  h.right.left padding

theorem SelectedFootprintCompactorBridgeOutputCaseSpec.cons
    {compactor : MachineDescription}
    (h : SelectedFootprintCompactorBridgeOutputCaseSpec
      compactor)
    (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    compactor.HaltsFromTapeWithOutput
      (rightEndCompactionSourceTape
        (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
          (bit :: rest) padding))
      (Tape.normalizedOutput
        (rightEdgeRewindSourceTape (bit :: rest) padding)) :=
  h.right.right bit rest padding

theorem SelectedFootprintCompactorBridgeOutputBitPaddingCaseSpec.subroutineReady
    {compactor : MachineDescription}
    (h :
      SelectedFootprintCompactorBridgeOutputBitPaddingCaseSpec
        compactor) :
    compactor.SubroutineReady :=
  h.left

theorem SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec.nilSpec
    {compactor : MachineDescription}
    (h :
      SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec
        compactor) :
    SelectedFootprintCompactorBridgeOutputNilPadSymbolCaseSpec
      compactor :=
  h.left

theorem SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec.consSpec
    {compactor : MachineDescription}
    (h :
      SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec
        compactor) :
    SelectedFootprintCompactorBridgeOutputConsPadSymbolCaseSpec
      compactor :=
  h.right

/-! ## Output spec splitting -/

theorem selectedFootprintCompactorBridgeOutputCaseSpec_of_outputSpec
    {compactor : MachineDescription}
    (h :
      SelectedFootprintCompactorBridgeOutputSpec compactor) :
    SelectedFootprintCompactorBridgeOutputCaseSpec compactor := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨hready, ?_, ?_⟩
  · intro padding
    exact hrun [] padding
  · intro bit rest padding
    exact hrun (bit :: rest) padding

theorem selectedFootprintCompactorBridgeOutputSpec_of_caseSpec
    {compactor : MachineDescription}
    (h :
      SelectedFootprintCompactorBridgeOutputCaseSpec compactor) :
    SelectedFootprintCompactorBridgeOutputSpec compactor := by
  rcases h with ⟨hready, hnil, hcons⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  cases bits with
  | nil =>
      exact hnil padding
  | cons bit rest =>
      exact hcons bit rest padding

theorem selectedFootprintCompactorBridgeOutputCaseConstruction_of_output
    (h :
      SelectedFootprintCompactorBridgeOutputConstruction) :
    SelectedFootprintCompactorBridgeOutputCaseConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedFootprintCompactorBridgeOutputCaseSpec_of_outputSpec
        hspec⟩

theorem selectedFootprintCompactorBridgeOutputConstruction_of_case
    (h :
      SelectedFootprintCompactorBridgeOutputCaseConstruction) :
    SelectedFootprintCompactorBridgeOutputConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedFootprintCompactorBridgeOutputSpec_of_caseSpec
        hspec⟩

theorem selectedFootprintCompactorBridgeOutputCaseSpec_of_bitPaddingCaseSpec
    {compactor : MachineDescription}
    (h :
      SelectedFootprintCompactorBridgeOutputBitPaddingCaseSpec
        compactor) :
    SelectedFootprintCompactorBridgeOutputCaseSpec compactor := by
  rcases h with
    ⟨hready, hnilNil, hnilCons, hconsNil, hconsCons⟩
  refine ⟨hready, ?_, ?_⟩
  · intro padding
    cases padding with
    | nil =>
        exact hnilNil
    | cons pad padding =>
        exact hnilCons pad padding
  · intro bit rest padding
    cases padding with
    | nil =>
        exact hconsNil bit rest
    | cons pad padding =>
        exact hconsCons bit rest pad padding

theorem selectedFootprintCompactorBridgeOutputBitPaddingCaseSpec_of_splitPadSymbolCaseSpec
    {compactor : MachineDescription}
    (h :
      SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec
        compactor) :
    SelectedFootprintCompactorBridgeOutputBitPaddingCaseSpec
      compactor := by
  rcases h with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  refine ⟨hready, hnilNil, ?_, hconsNil, ?_⟩
  · intro pad padding
    cases pad with
    | none =>
        exact hnilNone padding
    | some padBit =>
        exact hnilSome padBit padding
  · intro bit rest pad padding
    cases pad with
    | none =>
        exact hconsNone bit rest padding
    | some padBit =>
        exact hconsSome bit rest padBit padding

theorem selectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec_of_outputSpec
    {compactor : MachineDescription}
    (h :
      SelectedFootprintCompactorBridgeOutputSpec compactor) :
    SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec
      compactor := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · exact hrun [] []
    · intro padding
      exact hrun [] (none :: padding)
    · intro padBit padding
      exact hrun [] (some padBit :: padding)
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro bit rest
      exact hrun (bit :: rest) []
    · intro bit rest padding
      exact hrun (bit :: rest) (none :: padding)
    · intro bit rest padBit padding
      exact hrun (bit :: rest) (some padBit :: padding)

theorem selectedFootprintCompactorBridgeOutputSpec_of_splitPadSymbolCaseSpec
    {compactor : MachineDescription}
    (h :
      SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec
        compactor) :
    SelectedFootprintCompactorBridgeOutputSpec compactor := by
  have hbit :
      SelectedFootprintCompactorBridgeOutputBitPaddingCaseSpec
        compactor :=
    selectedFootprintCompactorBridgeOutputBitPaddingCaseSpec_of_splitPadSymbolCaseSpec
      h
  exact
    selectedFootprintCompactorBridgeOutputSpec_of_caseSpec
      (selectedFootprintCompactorBridgeOutputCaseSpec_of_bitPaddingCaseSpec
        hbit)

theorem selectedFootprintCompactorBridgeOutputSplitPadSymbolCaseConstruction_of_output
    (h :
      SelectedFootprintCompactorBridgeOutputConstruction) :
    SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec_of_outputSpec
        hspec⟩

theorem selectedFootprintCompactorBridgeOutputConstruction_of_splitPadSymbolCases
    (h :
      SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseConstruction) :
    SelectedFootprintCompactorBridgeOutputConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedFootprintCompactorBridgeOutputSpec_of_splitPadSymbolCaseSpec
        hspec⟩

theorem selectedFootprintCompactorBridgeOutputSpec_iff_splitPadSymbolCaseSpec
    (compactor : MachineDescription) :
    SelectedFootprintCompactorBridgeOutputSpec compactor ↔
      SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec
        compactor := by
  constructor
  · exact
      selectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec_of_outputSpec
  · exact
      selectedFootprintCompactorBridgeOutputSpec_of_splitPadSymbolCaseSpec

theorem selectedFootprintCompactorBridgeOutputConstruction_iff_splitPadSymbolCaseConstruction :
    SelectedFootprintCompactorBridgeOutputConstruction ↔
      SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseConstruction := by
  constructor
  · exact
      selectedFootprintCompactorBridgeOutputSplitPadSymbolCaseConstruction_of_output
  · exact
      selectedFootprintCompactorBridgeOutputConstruction_of_splitPadSymbolCases

/-! ## Exact-to-output branch adapters -/

theorem selectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec_of_rightEndBridgeSplitSpec
    {compactor : MachineDescription}
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitSpec
        compactor) :
    SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec
      compactor := by
  rcases h with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · exact haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
        hnilNil
    · intro padding
      exact haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
        (hnilNone padding)
    · intro padBit padding
      exact haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
        (hnilSome padBit padding)
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro bit rest
      exact haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
        (hconsNil bit rest)
    · intro bit rest padding
      exact haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
        (hconsNone bit rest padding)
    · intro bit rest padBit padding
      exact haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
        (hconsSome bit rest padBit padding)

theorem selectedFootprintCompactorBridgeOutputSplitPadSymbolCaseConstruction_of_rightEndBridgeSplit
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction) :
    SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec_of_rightEndBridgeSplitSpec
        hspec⟩

theorem selectedFootprintCompactorBridgeOutputConstruction_of_rightEndBridgeSplit
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction) :
    SelectedFootprintCompactorBridgeOutputConstruction :=
  selectedFootprintCompactorBridgeOutputConstruction_of_splitPadSymbolCases
    (selectedFootprintCompactorBridgeOutputSplitPadSymbolCaseConstruction_of_rightEndBridgeSplit
      h)

theorem selectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec_of_rightEndBridgeSpec
    {compactor : MachineDescription}
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSpec
        compactor) :
    SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec
      compactor :=
  selectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec_of_outputSpec
    (selectedFootprintCompactorBridgeOutputSpec_of_exact
      (selectedFootprintCompactorBridgeSpec_of_rightEndBridgeSpec h))

theorem selectedFootprintCompactorBridgeOutputSplitPadSymbolCaseConstruction_of_rightEndBridge
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction) :
    SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseConstruction := by
  rcases h with ⟨compactor, hspec⟩
  exact
    ⟨compactor,
      selectedFootprintCompactorBridgeOutputSplitPadSymbolCaseSpec_of_rightEndBridgeSpec
        hspec⟩

theorem selectedFootprintCompactorBridgeOutputConstruction_of_rightEndBridge
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction) :
    SelectedFootprintCompactorBridgeOutputConstruction :=
  selectedFootprintCompactorBridgeOutputConstruction_of_splitPadSymbolCases
    (selectedFootprintCompactorBridgeOutputSplitPadSymbolCaseConstruction_of_rightEndBridge
      h)

theorem selectedFootprintCompactorBridgeOutputSplitPadSymbolCaseConstruction_of_exactBridge
    (h : SelectedFootprintCompactorBridgeConstruction) :
    SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseConstruction :=
  selectedFootprintCompactorBridgeOutputSplitPadSymbolCaseConstruction_of_output
    (selectedFootprintCompactorBridgeOutputConstruction_of_exact h)

/-! ## Construction aliases for pending core leaves -/

theorem selectedFootprintCompactorBridgeOutputConstruction_core_of_rightEndBridgeSplitCore
    (hcore :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction) :
    SelectedFootprintCompactorBridgeOutputConstruction :=
  selectedFootprintCompactorBridgeOutputConstruction_of_rightEndBridgeSplit
    hcore

theorem selectedFootprintCompactorBridgeOutputSplitPadSymbolCaseConstruction_core_of_rightEndBridgeSplitCore
    (hcore :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction) :
    SelectedFootprintCompactorBridgeOutputSplitPadSymbolCaseConstruction :=
  selectedFootprintCompactorBridgeOutputSplitPadSymbolCaseConstruction_of_rightEndBridgeSplit
    hcore

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorOutputConstruction_of_rightEndBridgeSplit
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorOutputConstruction :=
  selectedSegmentLogicalTapeDecoderFootprintCompactorOutputConstruction_of_bridgeOutput
    (selectedFootprintCompactorBridgeOutputConstruction_of_rightEndBridgeSplit
      h)

theorem selectedSegmentLogicalTapeDecoderFootprintCompactorOutputConstruction_of_rightEndBridge
    (h :
      SelectedSegmentLogicalTapeDecoderFootprintCompactorRightEndBridgeConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintCompactorOutputConstruction :=
  selectedSegmentLogicalTapeDecoderFootprintCompactorOutputConstruction_of_bridgeOutput
    (selectedFootprintCompactorBridgeOutputConstruction_of_rightEndBridge
      h)

/-! ## Named normalized-output equations -/

theorem selectedFootprintCompactorBridgeTarget_output_eq_bits_padding
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (rightEdgeRewindSourceTape bits padding) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  exact rightEdgeRewindSourceTape_normalizedOutput bits padding

theorem selectedFootprintCompactorBridgeSource_output_eq_bits_padding
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            bits padding)) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  simpa [
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_eq_rightEndCompactionSourceTape] using
    selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape_normalizedOutput
      bits padding

theorem selectedFootprintCompactorBridgeSourceTarget_output_eq
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            bits padding)) =
      Tape.normalizedOutput
        (rightEdgeRewindSourceTape bits padding) := by
  rw [selectedFootprintCompactorBridgeSource_output_eq_bits_padding,
    selectedFootprintCompactorBridgeTarget_output_eq_bits_padding]

theorem selectedFootprintCompactorBridgeTarget_nil_nil_output :
    Tape.normalizedOutput (rightEdgeRewindSourceTape [] []) = [] := by
  rw [selectedFootprintCompactorBridgeTarget_output_eq_bits_padding]
  rfl

theorem selectedFootprintCompactorBridgeTarget_nil_none_output
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (rightEdgeRewindSourceTape [] (none :: padding)) =
      padding.filterMap (fun cell => cell) := by
  rw [selectedFootprintCompactorBridgeTarget_output_eq_bits_padding]
  rfl

theorem selectedFootprintCompactorBridgeTarget_nil_some_output
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (rightEdgeRewindSourceTape [] (some padBit :: padding)) =
      padBit :: padding.filterMap (fun cell => cell) := by
  rw [selectedFootprintCompactorBridgeTarget_output_eq_bits_padding]
  rfl

theorem selectedFootprintCompactorBridgeTarget_cons_nil_output
    (bit : Bool) (rest : Word Bool) :
    Tape.normalizedOutput
        (rightEdgeRewindSourceTape (bit :: rest) []) =
      bit :: rest := by
  rw [selectedFootprintCompactorBridgeTarget_output_eq_bits_padding]
  simp

theorem selectedFootprintCompactorBridgeTarget_cons_none_output
    (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (rightEdgeRewindSourceTape (bit :: rest)
          (none :: padding)) =
      List.append (bit :: rest)
        (padding.filterMap (fun cell => cell)) := by
  rw [selectedFootprintCompactorBridgeTarget_output_eq_bits_padding]
  rfl

theorem selectedFootprintCompactorBridgeTarget_cons_some_output
    (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (rightEdgeRewindSourceTape (bit :: rest)
          (some padBit :: padding)) =
      List.append (bit :: rest)
        (padBit :: padding.filterMap (fun cell => cell)) := by
  rw [selectedFootprintCompactorBridgeTarget_output_eq_bits_padding]
  rfl

theorem selectedFootprintCompactorBridgeSource_nil_nil_output :
    Tape.normalizedOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] [])) =
      [] := by
  rw [selectedFootprintCompactorBridgeSource_output_eq_bits_padding]
  rfl

theorem selectedFootprintCompactorBridgeSource_nil_none_output
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] (none :: padding))) =
      padding.filterMap (fun cell => cell) := by
  rw [selectedFootprintCompactorBridgeSource_output_eq_bits_padding]
  rfl

theorem selectedFootprintCompactorBridgeSource_nil_some_output
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            [] (some padBit :: padding))) =
      padBit :: padding.filterMap (fun cell => cell) := by
  rw [selectedFootprintCompactorBridgeSource_output_eq_bits_padding]
  rfl

theorem selectedFootprintCompactorBridgeSource_cons_nil_output
    (bit : Bool) (rest : Word Bool) :
    Tape.normalizedOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) [])) =
      bit :: rest := by
  rw [selectedFootprintCompactorBridgeSource_output_eq_bits_padding]
  simp

theorem selectedFootprintCompactorBridgeSource_cons_none_output
    (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) (none :: padding))) =
      List.append (bit :: rest)
        (padding.filterMap (fun cell => cell)) := by
  rw [selectedFootprintCompactorBridgeSource_output_eq_bits_padding]
  rfl

theorem selectedFootprintCompactorBridgeSource_cons_some_output
    (bit : Bool) (rest : Word Bool)
    (padBit : Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (rightEndCompactionSourceTape
          (selectedSegmentLogicalTapeDecoderDensifierFootprintLeftCells
            (bit :: rest) (some padBit :: padding))) =
      List.append (bit :: rest)
        (padBit :: padding.filterMap (fun cell => cell)) := by
  rw [selectedFootprintCompactorBridgeSource_output_eq_bits_padding]
  rfl

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
