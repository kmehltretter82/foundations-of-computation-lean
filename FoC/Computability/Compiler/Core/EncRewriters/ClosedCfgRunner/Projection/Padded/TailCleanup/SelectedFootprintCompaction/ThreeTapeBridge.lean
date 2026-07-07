import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.SelectedFootprintCompaction.BridgeCore

set_option doc.verso true

/-!
# Selected-footprint three-tape bridge layer

This module contains the guarded three-tape endpoint bridge contracts for the selected-footprint compactor route.
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

open CanonicalLayouts.DovetailLayoutScanner

/-!
## Structured three-tape compactor bridge frontier

The delayed decoder/compactor is now implemented as a lowered structured
three-tape component.  The remaining selected-footprint obligation is the
endpoint bridge between the old one-tape selected footprint and the guarded
structured three-tape layout used by the lowerer.
-/

def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInput0
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape Bool :=
  PairEncodedOptionCellCompactor.sourceTape
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells
        bits padding)

def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInput1
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape Bool :=
  PairEncodedOptionCellCompactor.markerTape
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells
        bits padding).length

def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInput2
    (_bits : Word Bool) (_padding : List (Option Bool)) :
    Tape Bool :=
  PairEncodedOptionCellCompactor.outputTape []

def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput0
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape Bool :=
  PairEncodedOptionCellCompactor.sourceTapeAt
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells
        bits padding)
      []

def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput1
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape Bool :=
  PairEncodedOptionCellCompactor.markerTapeAt
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells
        bits padding).length
      0

def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput2
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape Bool :=
  PairEncodedOptionCellCompactor.outputTape
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells
        bits padding)

def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape Bool :=
  encodedGuardedStructured3Tapes
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInput0
      bits padding)
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInput1
      bits padding)
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInput2
      bits padding)

def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape Bool :=
  encodedGuardedStructured3Tapes
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput0
      bits padding)
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput1
      bits padding)
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput2
      bits padding)

def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeFocusedOutputTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape Bool :=
  encodedGuardedStructured3Tapes
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput0
      bits padding)
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput1
      bits padding)
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
      bits padding)

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeCompactor_haltsFromTapeEquiv
    (bits : Word Bool) (padding : List (Option Bool)) :
    PairEncodedOptionCellCompactor.loweredDescription.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputTape
          bits padding)
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
          bits padding) := by
  simpa [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputTape,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInput0,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInput1,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInput2,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput0,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput1,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput2,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_eq_target_append_boundary] using
    PairEncodedOptionCellCompactor.loweredDescription_haltsFromTape_append_singleton
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells
          bits padding)
        none

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEndpointBridgeSpec
    (initializer projector : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    projector.SubroutineReady ∧
      forall (bits : Word Bool) (padding : List (Option Bool)),
        initializer.HaltsFromTapeEquiv
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
            bits padding)
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputTape
            bits padding) ∧
        projector.HaltsFromTapeEquiv
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
            bits padding)
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
            bits padding)

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEndpointBridgeConstruction :
    Prop :=
  exists initializer projector : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEndpointBridgeSpec
      initializer projector

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeIngressBridgeSpec
    (initializer : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    forall (bits : Word Bool) (padding : List (Option Bool)),
      initializer.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          bits padding)
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputTape
          bits padding)

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeIngressBridgeConstruction :
    Prop :=
  exists initializer : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeIngressBridgeSpec
      initializer

def selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputTape
    (payload : List (Option Bool)) : Tape Bool :=
  encodedGuardedStructured3Tapes
    (PairEncodedOptionCellCompactor.sourceTape payload)
    (PairEncodedOptionCellCompactor.markerTape payload.length)
    (PairEncodedOptionCellCompactor.outputTape [])

def SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSpec
    (initializer : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    forall payload : List (Option Bool),
      initializer.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
          payload)
        (selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputTape
          payload)

def SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerConstruction :
    Prop :=
  exists initializer : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSpec
      initializer

def SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerNilSpec
    (initializer : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    initializer.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload [])
      (selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputTape [])

def SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerConsSpec
    (initializer : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    forall (cell : Option Bool) (payload : List (Option Bool)),
      initializer.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintSourceTapeFromPayload
          (cell :: payload))
        (selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputTape
          (cell :: payload))

def SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSplitSpec
    (initializer : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerNilSpec
      initializer ∧
    SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerConsSpec
      initializer

def SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSplitConstruction :
    Prop :=
  exists initializer : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSplitSpec
      initializer

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputMaterializerSpec
    (initializer : MachineDescription) : Prop :=
  initializer.SubroutineReady ∧
    forall (bits : Word Bool) (padding : List (Option Bool)),
      initializer.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          bits padding)
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputTape
          bits padding)

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputMaterializerConstruction :
    Prop :=
  exists initializer : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputMaterializerSpec
      initializer

theorem selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSpec_of_split
    {initializer : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSplitSpec
        initializer) :
    SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSpec
      initializer := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilRun⟩
  rcases hcons with ⟨_hreadyCons, hconsRun⟩
  refine ⟨hready, ?_⟩
  intro payload
  cases payload with
  | nil =>
      exact hnilRun
  | cons cell payload =>
      exact hconsRun cell payload

theorem selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSplitSpec_of_spec
    {initializer : MachineDescription}
    (hspec :
      SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSpec
        initializer) :
    SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSplitSpec
      initializer := by
  rcases hspec with ⟨hready, hrun⟩
  constructor
  · exact ⟨hready, hrun []⟩
  · exact
      ⟨hready, fun cell payload =>
        hrun (cell :: payload)⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSpec_iff_split
    (initializer : MachineDescription) :
    SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSpec
        initializer ↔
      SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSplitSpec
        initializer := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSplitSpec_of_spec
  · exact
      selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSpec_of_split

theorem selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerConstruction_of_split
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSplitConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerConstruction := by
  rcases hsplit with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSpec_of_split
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSplitConstruction_of_construction
    (hmaterializer :
      SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSplitConstruction := by
  rcases hmaterializer with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSplitSpec_of_spec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerConstruction_iff_split :
    SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerConstruction ↔
      SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSplitConstruction := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSplitConstruction_of_construction
  · exact
      selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerConstruction_of_split

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputTape_eq_payloadInputTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputTape
        bits padding =
      selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputTape
        (selectedSegmentLogicalTapeDecoderPayloadCells bits padding) := by
  simp [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputTape,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInput0,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInput1,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInput2,
    selectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputTape,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_eq]

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputMaterializerSpec_of_payload
    {initializer : MachineDescription}
    (hmaterializer :
      SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerSpec
        initializer) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputMaterializerSpec
      initializer := by
  rcases hmaterializer with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  simpa [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape_eq_fromPayload,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputTape_eq_payloadInputTape] using
    hrun (selectedSegmentLogicalTapeDecoderPayloadCells bits padding)

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputMaterializerConstruction_of_payload
    (hmaterializer :
      SelectedSegmentLogicalTapeDecoderFootprintPayloadThreeTapeInputMaterializerConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputMaterializerConstruction := by
  rcases hmaterializer with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputMaterializerSpec_of_payload
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeIngressBridgeSpec_of_inputMaterializerSpec
    {initializer : MachineDescription}
    (hmaterializer :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputMaterializerSpec
        initializer) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeIngressBridgeSpec
      initializer :=
  hmaterializer

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeIngressBridgeConstruction_of_inputMaterializer
    (hmaterializer :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputMaterializerConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeIngressBridgeConstruction := by
  rcases hmaterializer with ⟨initializer, hspec⟩
  exact
    ⟨initializer,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeIngressBridgeSpec_of_inputMaterializerSpec
        hspec⟩

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressBridgeSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    forall (bits : Word Bool) (padding : List (Option Bool)),
      projector.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
          bits padding)
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          bits padding)

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressBridgeConstruction :
    Prop :=
  exists projector : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressBridgeSpec
      projector

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeStructuredEgressSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    forall (bits : Word Bool) (padding : List (Option Bool)),
      projector.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
          bits padding)
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          bits padding)

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeStructuredEgressConstruction :
    Prop :=
  exists projector : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeStructuredEgressSpec
      projector

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusSpec
    (focus : MachineDescription) : Prop :=
  focus.SubroutineReady ∧
    forall (bits : Word Bool) (padding : List (Option Bool)),
      focus.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
          bits padding)
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeFocusedOutputTape
          bits padding)

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusConstruction :
    Prop :=
  exists focus : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusSpec
      focus

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSpec
    (focus : MachineDescription) : Prop :=
  focus.SubroutineReady ∧
    forall (bits : Word Bool) (padding : List (Option Bool)),
      exists source marker target : Tape Bool,
        Tape.Equiv target
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
            bits padding) ∧
        focus.HaltsFromTapeEquiv
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
            bits padding)
          (encodedGuardedStructured3Tapes
            source marker target)

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusConstruction :
    Prop :=
  exists focus : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSpec
      focus

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusNilPadSymbolCaseSpec
    (focus : MachineDescription) : Prop :=
  focus.SubroutineReady ∧
    (exists source marker target : Tape Bool,
      Tape.Equiv target
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          [] []) ∧
      focus.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
          [] [])
        (encodedGuardedStructured3Tapes
          source marker target)) ∧
    (forall padding : List (Option Bool),
      exists source marker target : Tape Bool,
        Tape.Equiv target
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
            [] (none :: padding)) ∧
        focus.HaltsFromTapeEquiv
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
            [] (none :: padding))
          (encodedGuardedStructured3Tapes
            source marker target)) ∧
    forall (padBit : Bool) (padding : List (Option Bool)),
      exists source marker target : Tape Bool,
        Tape.Equiv target
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
            [] (some padBit :: padding)) ∧
      focus.HaltsFromTapeEquiv
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
            [] (some padBit :: padding))
          (encodedGuardedStructured3Tapes
            source marker target)

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusConsPadSymbolCaseSpec
    (focus : MachineDescription) : Prop :=
  focus.SubroutineReady ∧
    (forall (bit : Bool) (rest : Word Bool),
      exists source marker target : Tape Bool,
        Tape.Equiv target
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
            (bit :: rest) []) ∧
        focus.HaltsFromTapeEquiv
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
            (bit :: rest) [])
          (encodedGuardedStructured3Tapes
            source marker target)) ∧
    (forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      exists source marker target : Tape Bool,
        Tape.Equiv target
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
            (bit :: rest) (none :: padding)) ∧
        focus.HaltsFromTapeEquiv
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
            (bit :: rest) (none :: padding))
          (encodedGuardedStructured3Tapes
            source marker target)) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      exists source marker target : Tape Bool,
        Tape.Equiv target
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
            (bit :: rest) (some padBit :: padding)) ∧
        focus.HaltsFromTapeEquiv
          (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
            (bit :: rest) (some padBit :: padding))
          (encodedGuardedStructured3Tapes
            source marker target)

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSplitPadSymbolCaseSpec
    (focus : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusNilPadSymbolCaseSpec
      focus ∧
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusConsPadSymbolCaseSpec
      focus

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSplitPadSymbolCaseConstruction :
    Prop :=
  exists focus : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSplitPadSymbolCaseSpec
      focus

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSplitPadSymbolCaseSpec_of_spec
    {focus : MachineDescription}
    (hfocus :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSpec
        focus) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSplitPadSymbolCaseSpec
      focus := by
  rcases hfocus with ⟨hready, hrun⟩
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

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSpec_of_splitPadSymbolCaseSpec
    {focus : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSplitPadSymbolCaseSpec
        focus) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSpec
      focus := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  cases bits with
  | nil =>
      cases padding with
      | nil =>
          exact hnilNil
      | cons pad padding =>
          cases pad with
          | none =>
              exact hnilNone padding
          | some padBit =>
              exact hnilSome padBit padding
  | cons bit rest =>
      cases padding with
      | nil =>
          exact hconsNil bit rest
      | cons pad padding =>
          cases pad with
          | none =>
              exact hconsNone bit rest padding
          | some padBit =>
              exact hconsSome bit rest padBit padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusConstruction_of_splitPadSymbolCases
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSplitPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusConstruction := by
  rcases hsplit with ⟨focus, hspec⟩
  exact
    ⟨focus,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSpec_of_splitPadSymbolCaseSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSplitPadSymbolCaseConstruction_of_construction
    (hfocus :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSplitPadSymbolCaseConstruction := by
  rcases hfocus with ⟨focus, hspec⟩
  exact
    ⟨focus,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSplitPadSymbolCaseSpec_of_spec
        hspec⟩

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusNilPadSymbolCaseSpec
    (focus : MachineDescription) : Prop :=
  focus.SubroutineReady ∧
    focus.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
        [] [])
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeFocusedOutputTape
        [] []) ∧
    (forall padding : List (Option Bool),
      focus.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
          [] (none :: padding))
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeFocusedOutputTape
          [] (none :: padding))) ∧
    forall (padBit : Bool) (padding : List (Option Bool)),
      focus.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
          [] (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeFocusedOutputTape
          [] (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusConsPadSymbolCaseSpec
    (focus : MachineDescription) : Prop :=
  focus.SubroutineReady ∧
    (forall (bit : Bool) (rest : Word Bool),
      focus.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
          (bit :: rest) [])
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeFocusedOutputTape
          (bit :: rest) [])) ∧
    (forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      focus.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
          (bit :: rest) (none :: padding))
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeFocusedOutputTape
          (bit :: rest) (none :: padding))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      focus.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
          (bit :: rest) (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeFocusedOutputTape
          (bit :: rest) (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusSplitPadSymbolCaseSpec
    (focus : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusNilPadSymbolCaseSpec
      focus ∧
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusConsPadSymbolCaseSpec
      focus

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusSplitPadSymbolCaseConstruction :
    Prop :=
  exists focus : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusSplitPadSymbolCaseSpec
      focus

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusSplitPadSymbolCaseSpec_of_spec
    {focus : MachineDescription}
    (hfocus :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusSpec
        focus) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusSplitPadSymbolCaseSpec
      focus := by
  rcases hfocus with ⟨hready, hrun⟩
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

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusSpec_of_splitPadSymbolCaseSpec
    {focus : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusSplitPadSymbolCaseSpec
        focus) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusSpec
      focus := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  cases bits with
  | nil =>
      cases padding with
      | nil =>
          exact hnilNil
      | cons pad padding =>
          cases pad with
          | none =>
              exact hnilNone padding
          | some padBit =>
              exact hnilSome padBit padding
  | cons bit rest =>
      cases padding with
      | nil =>
          exact hconsNil bit rest
      | cons pad padding =>
          cases pad with
          | none =>
              exact hconsNone bit rest padding
          | some padBit =>
              exact hconsSome bit rest padBit padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusConstruction_of_splitPadSymbolCases
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusSplitPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusConstruction := by
  rcases hsplit with ⟨focus, hspec⟩
  exact
    ⟨focus,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusSpec_of_splitPadSymbolCaseSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape_eq_pairEncodedSplitTargetOutputTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
        bits padding =
      PairEncodedOptionCellCompactor.splitTargetOutputTape bits padding := by
  simp [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput0,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput1,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput2,
    PairEncodedOptionCellCompactor.splitTargetOutputTape,
    PairEncodedOptionCellCompactor.splitTargetOutput0,
    PairEncodedOptionCellCompactor.splitTargetOutput1,
    PairEncodedOptionCellCompactor.splitTargetOutput2,
    PairEncodedOptionCellCompactor.splitSourcePayloadCells,
    PairEncodedOptionCellCompactor.splitTargetPayloadCells,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_eq_target_append_boundary,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_eq,
    selectedSegmentLogicalTapeDecoderFootprintTargetCells]

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeFocusedOutputTape_eq_pairEncodedSplitTargetFocusedOutputTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeFocusedOutputTape
        bits padding =
      PairEncodedOptionCellCompactor.splitTargetFocusedOutputTape
        bits padding := by
  simp [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeFocusedOutputTape,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput0,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput1,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape_eq_rightEdgeRewind,
    rightEdgeRewindSourceTape,
    PairEncodedOptionCellCompactor.splitTargetFocusedOutputTape,
    PairEncodedOptionCellCompactor.splitTargetOutput0,
    PairEncodedOptionCellCompactor.splitTargetOutput1,
    PairEncodedOptionCellCompactor.splitTargetFocusedOutput2,
    PairEncodedOptionCellCompactor.splitSourcePayloadCells,
    PairEncodedOptionCellCompactor.splitTargetPayloadCells,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourcePayloadCells_eq_target_append_boundary,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetPayloadCells_eq,
    selectedSegmentLogicalTapeDecoderFootprintTargetCells]

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusSpec_of_pairEncodedSplitTarget
    {focus : MachineDescription}
    (hfocus :
      PairEncodedOptionCellCompactor.SplitTargetSeparatorFocusSpec
        focus) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusSpec
      focus := by
  rcases hfocus with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  simpa [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape_eq_pairEncodedSplitTargetOutputTape
      bits padding,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeFocusedOutputTape_eq_pairEncodedSplitTargetFocusedOutputTape
      bits padding] using
    hrun bits padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusSplitPadSymbolCaseConstruction_of_pairEncodedSplitTarget
    (hfocus :
      PairEncodedOptionCellCompactor.SplitTargetSeparatorFocusConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusSplitPadSymbolCaseConstruction := by
  rcases hfocus with ⟨focus, hspec⟩
  exact
    ⟨focus,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusSplitPadSymbolCaseSpec_of_spec
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusSpec_of_pairEncodedSplitTarget
          hspec)⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSpec_of_pairEncoded
    {focus : MachineDescription}
    (hfocus :
      PairEncodedOptionCellCompactor.SplitTargetProjectableRightEdgeRewindOutputSpec
        focus) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSpec
      focus := by
  rcases hfocus with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  rcases hrun bits padding with
    ⟨source, marker, target, htargetEquiv, hrunBits⟩
  refine ⟨source, marker, target, ?_, ?_⟩
  · simpa [
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape_eq_rightEdgeRewind
        bits padding] using
      htargetEquiv
  · simpa [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape_eq_pairEncodedSplitTargetOutputTape
      bits padding,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape_eq_rightEdgeRewind
      bits padding] using
    hrunBits

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusConstruction_of_pairEncoded
    (hfocus :
      PairEncodedOptionCellCompactor.SplitTargetProjectableRightEdgeRewindOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusConstruction := by
  rcases hfocus with ⟨focus, hspec⟩
  exact
    ⟨focus,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSpec_of_pairEncoded
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSpec_of_pairEncodedRightEdgeRewindOutput
    {focus : MachineDescription}
    (hfocus :
      PairEncodedOptionCellCompactor.SplitTargetRightEdgeRewindOutputSpec
        focus) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSpec
      focus :=
  selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSpec_of_pairEncoded
    (PairEncodedOptionCellCompactor.splitTargetProjectableRightEdgeRewindOutputSpec_of_rightEdgeRewindOutputSpec
      hfocus)

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusConstruction_of_pairEncodedRightEdgeRewindOutput
    (hfocus :
      PairEncodedOptionCellCompactor.SplitTargetRightEdgeRewindOutputConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusConstruction :=
  selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusConstruction_of_pairEncoded
    (PairEncodedOptionCellCompactor.splitTargetProjectableRightEdgeRewindOutputConstruction_of_rightEdgeRewindOutput
      hfocus)

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusConstruction_of_pairEncodedRightEdgeRewindOutputSplitPadSymbolCases
    (hsplit :
      PairEncodedOptionCellCompactor.SplitTargetRightEdgeRewindOutputSplitPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusConstruction :=
  selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusConstruction_of_pairEncoded
    (PairEncodedOptionCellCompactor.splitTargetProjectableRightEdgeRewindOutputConstruction_of_rightEdgeRewindOutputSplitPadSymbolCases
      hsplit)

def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectedEgressDescription
    (focus projector : MachineDescription) : MachineDescription :=
  canonicalPrimitiveSeqDescription focus projector

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectedEgressDescription_subroutineReady
    {focus projector : MachineDescription}
    (hfocus : focus.SubroutineReady)
    (hprojector : projector.SubroutineReady) :
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectedEgressDescription
      focus projector).SubroutineReady := by
  simpa [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectedEgressDescription] using
    canonicalPrimitiveSeqDescription_subroutineReady hfocus hprojector

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeStructuredEgressSpec_of_separatorFocus_projector
    {focus projector : MachineDescription}
    (hfocus :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusSpec
        focus)
    (hprojector : StructuredTape2ProjectorSpec projector) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeStructuredEgressSpec
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectedEgressDescription
        focus projector) := by
  rcases hfocus with ⟨hfocusReady, hfocusRun⟩
  rcases hprojector with ⟨hprojectorReady, hprojectorRun⟩
  refine
    ⟨selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectedEgressDescription_subroutineReady
        hfocusReady hprojectorReady,
      ?_⟩
  intro bits padding
  exact
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      hfocusReady
      hprojectorReady
      (hfocusRun bits padding)
      (by
        simpa [
          selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeFocusedOutputTape] using
          hprojectorRun
            (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput0
              bits padding)
            (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput1
              bits padding)
            (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
              bits padding))

private theorem haltsFromTapeEquiv_of_target_equiv
    {D : MachineDescription} {Tin Tmid Tout : Tape Bool}
    (h : D.HaltsFromTapeEquiv Tin Tmid)
    (hequiv : Tape.Equiv Tmid Tout) :
    D.HaltsFromTapeEquiv Tin Tout := by
  rcases h with ⟨actual, hhalt, hactual⟩
  exact ⟨actual, hhalt, Tape.Equiv.trans hactual hequiv⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeStructuredEgressSpec_of_projectableSeparatorFocus_projector
    {focus projector : MachineDescription}
    (hfocus :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusSpec
        focus)
    (hprojector : StructuredTape2ProjectorSpec projector) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeStructuredEgressSpec
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectedEgressDescription
        focus projector) := by
  rcases hfocus with ⟨hfocusReady, hfocusRun⟩
  rcases hprojector with ⟨hprojectorReady, hprojectorRun⟩
  refine
    ⟨selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectedEgressDescription_subroutineReady
        hfocusReady hprojectorReady,
      ?_⟩
  intro bits padding
  rcases hfocusRun bits padding with
    ⟨source, marker, target, htargetEquiv, hfocusRunBits⟩
  have hseq :
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectedEgressDescription
          focus projector).HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
          bits padding)
        target :=
    canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
      hfocusReady
      hprojectorReady
      hfocusRunBits
      (hprojectorRun source marker target)
  exact
    haltsFromTapeEquiv_of_target_equiv hseq htargetEquiv

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeStructuredEgressConstruction_of_separatorFocus_projector
    (hfocus :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeSeparatorFocusConstruction)
    (hprojector : StructuredTape2ProjectorConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeStructuredEgressConstruction := by
  rcases hfocus with ⟨focus, hfocusSpec⟩
  rcases hprojector with ⟨projector, hprojectorSpec⟩
  exact
    ⟨selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectedEgressDescription
        focus projector,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeStructuredEgressSpec_of_separatorFocus_projector
        hfocusSpec hprojectorSpec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeStructuredEgressConstruction_of_projectableSeparatorFocus_projector
    (hfocus :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectableSeparatorFocusConstruction)
    (hprojector : StructuredTape2ProjectorConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeStructuredEgressConstruction := by
  rcases hfocus with ⟨focus, hfocusSpec⟩
  rcases hprojector with ⟨projector, hprojectorSpec⟩
  exact
    ⟨selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeProjectedEgressDescription
        focus projector,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeStructuredEgressSpec_of_projectableSeparatorFocus_projector
        hfocusSpec hprojectorSpec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressBridgeSpec_of_structuredEgressSpec
    {projector : MachineDescription}
    (hpositioner :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeStructuredEgressSpec
        projector) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressBridgeSpec
      projector :=
  hpositioner

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressBridgeConstruction_of_structuredEgress
    (hpositioner :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeStructuredEgressConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressBridgeConstruction := by
  rcases hpositioner with ⟨projector, hspec⟩
  exact
    ⟨projector,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressBridgeSpec_of_structuredEgressSpec
        hspec⟩

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressNilPadSymbolCaseSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    projector.HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
        [] [])
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
        [] []) ∧
    (forall padding : List (Option Bool),
      projector.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
          [] (none :: padding))
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          [] (none :: padding))) ∧
    forall (padBit : Bool) (padding : List (Option Bool)),
      projector.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
          [] (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          [] (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressConsPadSymbolCaseSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    (forall (bit : Bool) (rest : Word Bool),
      projector.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
          (bit :: rest) [])
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          (bit :: rest) [])) ∧
    (forall (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      projector.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
          (bit :: rest) (none :: padding))
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          (bit :: rest) (none :: padding))) ∧
    forall (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      projector.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape
          (bit :: rest) (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          (bit :: rest) (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressSplitPadSymbolCaseSpec
    (projector : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressNilPadSymbolCaseSpec
      projector ∧
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressConsPadSymbolCaseSpec
      projector

def SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressSplitPadSymbolCaseConstruction :
    Prop :=
  exists projector : MachineDescription,
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressSplitPadSymbolCaseSpec
      projector

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressSplitPadSymbolCaseSpec_of_structuredEgressSpec
    {projector : MachineDescription}
    (hpositioner :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeStructuredEgressSpec
        projector) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressSplitPadSymbolCaseSpec
      projector := by
  rcases hpositioner with ⟨hready, hrun⟩
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

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressSplitPadSymbolCaseConstruction_of_structuredEgress
    (hpositioner :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeStructuredEgressConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressSplitPadSymbolCaseConstruction := by
  rcases hpositioner with ⟨projector, hspec⟩
  exact
    ⟨projector,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressSplitPadSymbolCaseSpec_of_structuredEgressSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressBridgeSpec_of_splitPadSymbolCaseSpec
    {projector : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressSplitPadSymbolCaseSpec
        projector) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressBridgeSpec
      projector := by
  rcases hsplit with ⟨hnil, hcons⟩
  rcases hnil with
    ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  refine ⟨hready, ?_⟩
  intro bits padding
  cases bits with
  | nil =>
      cases padding with
      | nil =>
          exact hnilNil
      | cons pad padding =>
          cases pad with
          | none =>
              exact hnilNone padding
          | some padBit =>
              exact hnilSome padBit padding
  | cons bit rest =>
      cases padding with
      | nil =>
          exact hconsNil bit rest
      | cons pad padding =>
          cases pad with
          | none =>
              exact hconsNone bit rest padding
          | some padBit =>
              exact hconsSome bit rest padBit padding

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressBridgeConstruction_of_splitPadSymbolCases
    (hsplit :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressSplitPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressBridgeConstruction := by
  rcases hsplit with ⟨projector, hspec⟩
  exact
    ⟨projector,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressBridgeSpec_of_splitPadSymbolCaseSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEndpointBridgeSpec_of_ingress_egress
    {initializer projector : MachineDescription}
    (hingress :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeIngressBridgeSpec
        initializer)
    (hegress :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressBridgeSpec
        projector) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEndpointBridgeSpec
      initializer projector := by
  rcases hingress with ⟨hinitializerReady, hinitializerRun⟩
  rcases hegress with ⟨hprojectorReady, hprojectorRun⟩
  exact
    ⟨hinitializerReady, hprojectorReady,
      fun bits padding =>
        ⟨hinitializerRun bits padding,
          hprojectorRun bits padding⟩⟩

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEndpointBridgeConstruction_of_ingress_egress
    (hingress :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeIngressBridgeConstruction)
    (hegress :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEgressBridgeConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEndpointBridgeConstruction := by
  rcases hingress with ⟨initializer, hingressSpec⟩
  rcases hegress with ⟨projector, hegressSpec⟩
  exact
    ⟨initializer, projector,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEndpointBridgeSpec_of_ingress_egress
        hingressSpec hegressSpec⟩

def selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeBridgedDescription
    (initializer projector : MachineDescription) : MachineDescription :=
  structured3EndpointBridgeDescription
    initializer
    PairEncodedOptionCellCompactor.loweredDescription
    projector

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeBridgedDescription_haltsFromTapeEquiv
    {initializer projector : MachineDescription}
    (hbridge :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEndpointBridgeSpec
        initializer projector)
    (bits : Word Bool) (padding : List (Option Bool)) :
    (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeBridgedDescription
        initializer projector).HaltsFromTapeEquiv
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
        bits padding)
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
        bits padding) := by
  rcases hbridge with ⟨hinitializerReady, hprojectorReady, hbridgeRun⟩
  rcases hbridgeRun bits padding with
    ⟨hinitializerRun, hprojectorRun⟩
  simpa [
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeBridgedDescription,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInputTape,
    selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutputTape] using
    structured3EndpointBridgeDescription_haltsFromTapeEquiv
      (initializer := initializer)
      (lowered :=
        PairEncodedOptionCellCompactor.loweredDescription)
      (projector := projector)
      (Tin :=
        selectedSegmentLogicalTapeDecoderFootprintPaddingSplitSourceTape
          bits padding)
      (T0 :=
        selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInput0
          bits padding)
      (T1 :=
        selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInput1
          bits padding)
      (T2 :=
        selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeInput2
          bits padding)
      (U0 :=
        selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput0
          bits padding)
      (U1 :=
        selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput1
          bits padding)
      (U2 :=
        selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeOutput2
          bits padding)
      (Tout :=
        selectedSegmentLogicalTapeDecoderFootprintPaddingSplitTargetTape
          bits padding)
      hinitializerReady
      PairEncodedOptionCellCompactor.loweredDescription_subroutineReady
      hprojectorReady
      hinitializerRun
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeCompactor_haltsFromTapeEquiv
        bits padding)
      hprojectorRun

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitSpec_of_threeTapeEndpointBridgeSpec
    {initializer projector : MachineDescription}
    (hbridge :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEndpointBridgeSpec
        initializer projector) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitSpec
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeBridgedDescription
        initializer projector) := by
  rcases hbridge with ⟨hinitializerReady, hprojectorReady, hbridgeRun⟩
  let hbridgeSpec :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEndpointBridgeSpec
        initializer projector :=
    ⟨hinitializerReady, hprojectorReady, hbridgeRun⟩
  have hready :
      (selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeBridgedDescription
        initializer projector).SubroutineReady := by
    simpa [
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeBridgedDescription] using
      structured3EndpointBridgeDescription_subroutineReady
        hinitializerReady
        PairEncodedOptionCellCompactor.loweredDescription_subroutineReady
        hprojectorReady
  refine ⟨?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · exact
        selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeBridgedDescription_haltsFromTapeEquiv
          hbridgeSpec [] []
    · intro padding
      exact
        selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeBridgedDescription_haltsFromTapeEquiv
          hbridgeSpec [] (none :: padding)
    · intro padBit padding
      exact
        selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeBridgedDescription_haltsFromTapeEquiv
          hbridgeSpec [] (some padBit :: padding)
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro bit rest
      exact
        selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeBridgedDescription_haltsFromTapeEquiv
          hbridgeSpec (bit :: rest) []
    · intro bit rest padding
      exact
        selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeBridgedDescription_haltsFromTapeEquiv
          hbridgeSpec (bit :: rest) (none :: padding)
    · intro bit rest padBit padding
      exact
        selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeBridgedDescription_haltsFromTapeEquiv
          hbridgeSpec (bit :: rest) (some padBit :: padding)

theorem selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitConstruction_of_threeTapeEndpointBridge
    (hbridge :
      SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeEndpointBridgeConstruction) :
    SelectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitConstruction := by
  rcases hbridge with ⟨initializer, projector, hspec⟩
  exact
    ⟨selectedSegmentLogicalTapeDecoderFootprintPaddingSplitThreeTapeBridgedDescription
        initializer projector,
      selectedSegmentLogicalTapeDecoderFootprintPaddingSplitCompactorSplitSpec_of_threeTapeEndpointBridgeSpec
        hspec⟩

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
