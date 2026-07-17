import FoC.Computability.Compiler.DescriptionExecution
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoundaryEraser
import FoC.Computability.Compiler.ClosedCfg.ProjTail.SelectedFootprintCompaction
import FoC.Computability.Compiler.ClosedCfg.ProjTail.StructuredPrefixEraserShape

set_option doc.verso true

/-!
# Structured prefix eraser handoff

This module contains the selected logical-tape decoder handoff that erases the
two guarded structured logical tapes before the selected footprint compactor
runs.  Count-window-specific instantiations remain in
the threaded count-window bridge module.
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

def selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  selectedSegmentLogicalTapeDecoderTargetTape
    (rightEdgeScanSourceTapeFromLeft [none] bits padding)
    (encodedStructuredTapeCellsPrefix
      [guardLogicalTape T0, guardLogicalTape T1])

def selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
    (bits : Word Bool) (padding : List (Option Bool)) : Tape Bool :=
  selectedSegmentLogicalTapeDecoderTargetTape
    (rightEdgeScanSourceTapeFromLeft [none] bits padding)
    []

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape
    (bits : Word Bool) (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
        bits padding =
      selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
        bits padding := by
  rfl

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_eq_guardedTwoTapeStructuredPrefixEraserSourceTape
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
        T0 T1 bits padding =
      guardedTwoTapeStructuredPrefixEraserSourceTape
        T0 T1 bits padding := by
  rfl

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          bits padding)

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall (T0 T1 : Tape Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] padding)
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] padding)) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) padding)
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) padding)

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall T0 T1 : Tape Bool,
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] [])) ∧
    (forall (T0 T1 : Tape Bool) (pad : Option Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (pad :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] (pad :: padding))) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) [])) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (pad : Option Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (pad :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) (pad :: padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall T0 T1 : Tape Bool,
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] [])) ∧
    (forall (T0 T1 : Tape Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] (none :: padding))) ∧
    (forall (T0 T1 : Tape Bool) (padBit : Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] (some padBit :: padding))) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) [])) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) (none :: padding))) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserNilPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall T0 T1 : Tape Bool,
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] [])) ∧
    (forall (T0 T1 : Tape Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] (none :: padding))) ∧
    forall (T0 T1 : Tape Bool) (padBit : Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          [] (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConsPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) [])) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) (none :: padding))) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape
          (bit :: rest) (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserNilPadSymbolCaseSpec
      eraser ∧
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConsPadSymbolCaseSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffNilPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall T0 T1 : Tape Bool,
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] [])) ∧
    (forall (T0 T1 : Tape Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (none :: padding))) ∧
    forall (T0 T1 : Tape Bool) (padBit : Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          [] (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConsPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) [])) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (none :: padding))) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding))
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          (bit :: rest) (some padBit :: padding))

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec
    (eraser : MachineDescription) : Prop :=
  SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffNilPadSymbolCaseSpec
      eraser ∧
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConsPadSymbolCaseSpec
      eraser

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec
      eraser

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffNilPadSymbolCaseSpec_of_guardedPrefixEraserSpec
    {eraser : MachineDescription}
    (hguard :
      GuardedTwoTapeStructuredPrefixEraserNilPadSymbolCaseSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffNilPadSymbolCaseSpec
      eraser := by
  rcases hguard with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  refine ⟨hready, ?_, ?_, ?_⟩
  · intro T0 T1
    simpa [
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_eq_guardedTwoTapeStructuredPrefixEraserSourceTape,
      guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
      hnilNil T0 T1
  · intro T0 T1 padding
    simpa [
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_eq_guardedTwoTapeStructuredPrefixEraserSourceTape,
      guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
      hnilNone T0 T1 padding
  · intro T0 T1 padBit padding
    simpa [
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_eq_guardedTwoTapeStructuredPrefixEraserSourceTape,
      guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
      hnilSome T0 T1 padBit padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConsPadSymbolCaseSpec_of_guardedPrefixEraserSpec
    {eraser : MachineDescription}
    (hguard :
      GuardedTwoTapeStructuredPrefixEraserConsPadSymbolCaseSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConsPadSymbolCaseSpec
      eraser := by
  rcases hguard with ⟨hready, hconsNil, hconsNone, hconsSome⟩
  refine ⟨hready, ?_, ?_, ?_⟩
  · intro T0 T1 bit rest
    simpa [
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_eq_guardedTwoTapeStructuredPrefixEraserSourceTape,
      guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
      hconsNil T0 T1 bit rest
  · intro T0 T1 bit rest padding
    simpa [
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_eq_guardedTwoTapeStructuredPrefixEraserSourceTape,
      guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
      hconsNone T0 T1 bit rest padding
  · intro T0 T1 bit rest padBit padding
    simpa [
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_eq_guardedTwoTapeStructuredPrefixEraserSourceTape,
      guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
      hconsSome T0 T1 bit rest padBit padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec_of_guardedPrefixEraserSpec
    {eraser : MachineDescription}
    (hguard :
      GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec
      eraser := by
  rcases hguard with ⟨hnil, hcons⟩
  exact
    ⟨selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffNilPadSymbolCaseSpec_of_guardedPrefixEraserSpec
        hnil,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConsPadSymbolCaseSpec_of_guardedPrefixEraserSpec
        hcons⟩

theorem footprintHandoffSplitPadCaseConstruction_ofGuardedEraser
    (hguard :
      GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction := by
  rcases hguard with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec_of_guardedPrefixEraserSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction_of_split
    (hsplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction := by
  rcases hsplit with ⟨eraser, hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  exact
    ⟨eraser, hready, hnilNil, hnilNone, hnilSome,
      hconsNil, hconsNone, hconsSome⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction_of_padSymbolCases
    (hcases :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction := by
  rcases hcases with
    ⟨eraser, hready, hnilNil, hnilNone, hnilSome, hconsNil,
      hconsNone, hconsSome⟩
  refine ⟨eraser, hready, hnilNil, ?_, hconsNil, ?_⟩
  · intro T0 T1 pad padding
    cases pad with
    | none =>
        exact hnilNone T0 T1 padding
    | some padBit =>
        exact hnilSome T0 T1 padBit padding
  · intro T0 T1 bit rest pad padding
    cases pad with
    | none =>
        exact hconsNone T0 T1 bit rest padding
    | some padBit =>
        exact hconsSome T0 T1 bit rest padBit padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction_of_footprintHandoff
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction := by
  rcases hhandoff with ⟨eraser, hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  refine ⟨eraser, ?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro T0 T1
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hnilNil T0 T1
    · intro T0 T1 padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hnilNone T0 T1 padding
    · intro T0 T1 padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hnilSome T0 T1 padBit padding
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro T0 T1 bit rest
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hconsNil T0 T1 bit rest
    · intro T0 T1 bit rest padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hconsNone T0 T1 bit rest padding
    · intro T0 T1 bit rest padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hconsSome T0 T1 bit rest padBit padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction_of_split
    (hsplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction := by
  rcases hsplit with ⟨eraser, hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  refine ⟨eraser, ?_, ?_⟩
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro T0 T1
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hnilNil T0 T1
    · intro T0 T1 padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hnilNone T0 T1 padding
    · intro T0 T1 padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hnilSome T0 T1 padBit padding
  · refine ⟨hready, ?_, ?_, ?_⟩
    · intro T0 T1 bit rest
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hconsNil T0 T1 bit rest
    · intro T0 T1 bit rest padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hconsNone T0 T1 bit rest padding
    · intro T0 T1 bit rest padBit padding
      simpa [
        selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
        hconsSome T0 T1 bit rest padBit padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction_of_cases
    (hcases :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction := by
  rcases hcases with ⟨eraser, hready, hnil, hcons⟩
  refine ⟨eraser, hready, ?_⟩
  intro T0 T1 bits padding
  cases bits with
  | nil =>
      exact hnil T0 T1 padding
  | cons bit rest =>
      exact hcons T0 T1 bit rest padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseConstruction_of_bitPaddingCases
    (hcases :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserBitPaddingCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserCaseConstruction := by
  rcases hcases with
    ⟨eraser, hready, hnilNil, hnilCons, hconsNil,
      hconsCons⟩
  refine ⟨eraser, hready, ?_, ?_⟩
  · intro T0 T1 padding
    cases padding with
    | nil =>
        exact hnilNil T0 T1
    | cons pad padding =>
        exact hnilCons T0 T1 pad padding
  · intro T0 T1 bit rest padding
    cases padding with
    | nil =>
        exact hconsNil T0 T1 bit rest
    | cons pad padding =>
        exact hconsCons T0 T1 bit rest pad padding

/--
Reusable structured-prefix eraser handoff contract.

A single eraser removes the two guarded structured logical tapes that precede
the selected logical-tape decoder footprint, for every selected payload and
padding shape.  The nil/cons and padding-specific contracts above are views of
this one machine contract.
-/
def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeEquiv
        (selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)
        (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
          bits padding)

def SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction :
    Prop :=
  exists eraser : MachineDescription,
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
      eraser

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_guardedPrefixEraserSpec
    {eraser : MachineDescription}
    (hguard :
      GuardedTwoTapeStructuredPrefixEraserSpec eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
      eraser := by
  rcases hguard with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  simpa [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSourceTape_eq_guardedTwoTapeStructuredPrefixEraserSourceTape,
    guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
    hrun T0 T1 bits padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction_of_guardedPrefixEraser
    (hguard :
      GuardedTwoTapeStructuredPrefixEraserConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction := by
  rcases hguard with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_guardedPrefixEraserSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec_of_handoffSpec
    {eraser : MachineDescription}
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec
      eraser := by
  rcases hhandoff with ⟨hready, hrun⟩
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

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction_of_handoff
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction := by
  rcases hhandoff with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec_of_handoffSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction_of_footprintHandoff
    (hhandoff :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction := by
  rcases hhandoff with ⟨eraser, hready, hrun⟩
  refine ⟨eraser, hready, ?_⟩
  intro T0 T1 bits padding
  simpa [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
    hrun T0 T1 bits padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_eraserSpec
    {eraser : MachineDescription}
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
      eraser := by
  rcases heraser with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  simpa [
    selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
    hrun T0 T1 bits padding

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction_of_eraser
    (heraser :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction := by
  rcases heraser with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_eraserSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_iff_eraserSpec
    (eraser : MachineDescription) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
        eraser ↔
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserSpec
        eraser := by
  constructor
  · intro hhandoff
    rcases hhandoff with ⟨hready, hrun⟩
    refine ⟨hready, ?_⟩
    intro T0 T1 bits padding
    simpa [
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
      hrun T0 T1 bits padding
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_eraserSpec

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction_iff_eraserConstruction :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction ↔
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserConstruction_of_footprintHandoff
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction_of_eraser

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_splitPadSymbolCaseSpec
    {eraser : MachineDescription}
    (hsplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec
        eraser) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
      eraser := by
  rcases hsplit with ⟨hnil, hcons⟩
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

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction_of_splitPadSymbolCases
    (hsplit :
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction := by
  rcases hsplit with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_splitPadSymbolCaseSpec
        hspec⟩

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_iff_splitPadSymbolCaseSpec
    (eraser : MachineDescription) :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec
        eraser ↔
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec
        eraser := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseSpec_of_handoffSpec
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSpec_of_splitPadSymbolCaseSpec

theorem selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction_iff_splitPadSymbolCaseConstruction :
    SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction ↔
      SelectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction := by
  constructor
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffSplitPadSymbolCaseConstruction_of_handoff
  · exact
      selectedSegmentLogicalTapeDecoderTwoTapeStructuredPrefixEraserFootprintHandoffConstruction_of_splitPadSymbolCases

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters
end Computability
end FoC
