import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Padded.TailCleanup.StructuredPrefixEraserBoundaryPhases

set_option doc.verso true

/-!
# Output contracts for the guarded two-tape structured-prefix eraser

The exact structured-prefix eraser leaf still needs endpoint-positioning and
blank-prefix compaction work.  This module records the reusable
normalized-output surface that downstream selected-segment code can use while
those exact cursor commitments remain local.

The contracts here are generic over the guarded two-tape source shape from
{lit}`StructuredPrefixEraserShape`.  The selected-specific handoff module adapts
them back to its public names.
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

/-! ## Generic eraser output contracts -/

def GuardedTwoTapeStructuredPrefixEraserOutputSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)
        (Tape.normalizedOutput
          (guardedTwoTapeStructuredPrefixEraserTargetTape
            bits padding))

def GuardedTwoTapeStructuredPrefixEraserOutputConstruction :
    Prop :=
  exists eraser : MachineDescription,
    GuardedTwoTapeStructuredPrefixEraserOutputSpec eraser

def GuardedTwoTapeStructuredPrefixEraserFootprintOutputSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    forall (T0 T1 : Tape Bool) (bits : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding)
        (Tape.normalizedOutput
          (selectedSegmentLogicalTapeDecoderDensifierFootprintSourceTape
            bits padding))

def GuardedTwoTapeStructuredPrefixEraserFootprintOutputConstruction :
    Prop :=
  exists eraser : MachineDescription,
    GuardedTwoTapeStructuredPrefixEraserFootprintOutputSpec eraser

theorem guardedTwoTapeStructuredPrefixEraserOutputSpec_of_exact
    {eraser : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixEraserSpec eraser) :
    GuardedTwoTapeStructuredPrefixEraserOutputSpec eraser := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  exact
    haltsFromTapeWithOutput_of_haltsFromTapeEquiv_target
      (hrun T0 T1 bits padding)

theorem guardedTwoTapeStructuredPrefixEraserOutputConstruction_of_exact
    (h :
      GuardedTwoTapeStructuredPrefixEraserConstruction) :
    GuardedTwoTapeStructuredPrefixEraserOutputConstruction := by
  rcases h with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      guardedTwoTapeStructuredPrefixEraserOutputSpec_of_exact
        hspec⟩

theorem guardedTwoTapeStructuredPrefixEraserFootprintOutputSpec_of_outputSpec
    {eraser : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixEraserOutputSpec eraser) :
    GuardedTwoTapeStructuredPrefixEraserFootprintOutputSpec
      eraser := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  simpa [
    guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
    hrun T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixEraserOutputSpec_of_footprintOutputSpec
    {eraser : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixEraserFootprintOutputSpec
        eraser) :
    GuardedTwoTapeStructuredPrefixEraserOutputSpec eraser := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  simpa [
    guardedTwoTapeStructuredPrefixEraserTargetTape_eq_footprintSourceTape] using
    hrun T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixEraserFootprintOutputConstruction_of_output
    (h :
      GuardedTwoTapeStructuredPrefixEraserOutputConstruction) :
    GuardedTwoTapeStructuredPrefixEraserFootprintOutputConstruction := by
  rcases h with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      guardedTwoTapeStructuredPrefixEraserFootprintOutputSpec_of_outputSpec
        hspec⟩

theorem guardedTwoTapeStructuredPrefixEraserOutputConstruction_of_footprintOutput
    (h :
      GuardedTwoTapeStructuredPrefixEraserFootprintOutputConstruction) :
    GuardedTwoTapeStructuredPrefixEraserOutputConstruction := by
  rcases h with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      guardedTwoTapeStructuredPrefixEraserOutputSpec_of_footprintOutputSpec
        hspec⟩

theorem guardedTwoTapeStructuredPrefixEraserOutputSpec_iff_footprintOutputSpec
    (eraser : MachineDescription) :
    GuardedTwoTapeStructuredPrefixEraserOutputSpec eraser ↔
      GuardedTwoTapeStructuredPrefixEraserFootprintOutputSpec
        eraser := by
  constructor
  · exact
      guardedTwoTapeStructuredPrefixEraserFootprintOutputSpec_of_outputSpec
  · exact
      guardedTwoTapeStructuredPrefixEraserOutputSpec_of_footprintOutputSpec

theorem guardedTwoTapeStructuredPrefixEraserOutputConstruction_iff_footprintOutputConstruction :
    GuardedTwoTapeStructuredPrefixEraserOutputConstruction ↔
      GuardedTwoTapeStructuredPrefixEraserFootprintOutputConstruction := by
  constructor
  · exact
      guardedTwoTapeStructuredPrefixEraserFootprintOutputConstruction_of_output
  · exact
      guardedTwoTapeStructuredPrefixEraserOutputConstruction_of_footprintOutput

/-! ## Branch output views -/

def GuardedTwoTapeStructuredPrefixEraserCaseOutputSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall (T0 T1 : Tape Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] padding)
        (Tape.normalizedOutput
          (guardedTwoTapeStructuredPrefixEraserTargetTape
            [] padding))) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) padding)
        (Tape.normalizedOutput
          (guardedTwoTapeStructuredPrefixEraserTargetTape
            (bit :: rest) padding))

def GuardedTwoTapeStructuredPrefixEraserCaseOutputConstruction :
    Prop :=
  exists eraser : MachineDescription,
    GuardedTwoTapeStructuredPrefixEraserCaseOutputSpec eraser

def GuardedTwoTapeStructuredPrefixEraserBitPaddingCaseOutputSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall T0 T1 : Tape Bool,
      eraser.HaltsFromTapeWithOutput
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])
        (Tape.normalizedOutput
          (guardedTwoTapeStructuredPrefixEraserTargetTape
            [] []))) ∧
    (forall (T0 T1 : Tape Bool) (pad : Option Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (pad :: padding))
        (Tape.normalizedOutput
          (guardedTwoTapeStructuredPrefixEraserTargetTape
            [] (pad :: padding)))) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeWithOutput
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])
        (Tape.normalizedOutput
          (guardedTwoTapeStructuredPrefixEraserTargetTape
            (bit :: rest) []))) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (pad : Option Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (pad :: padding))
        (Tape.normalizedOutput
          (guardedTwoTapeStructuredPrefixEraserTargetTape
            (bit :: rest) (pad :: padding)))

def GuardedTwoTapeStructuredPrefixEraserBitPaddingCaseOutputConstruction :
    Prop :=
  exists eraser : MachineDescription,
    GuardedTwoTapeStructuredPrefixEraserBitPaddingCaseOutputSpec
      eraser

def GuardedTwoTapeStructuredPrefixEraserNilPadSymbolCaseOutputSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall T0 T1 : Tape Bool,
      eraser.HaltsFromTapeWithOutput
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] [])
        (Tape.normalizedOutput
          (guardedTwoTapeStructuredPrefixEraserTargetTape
            [] []))) ∧
    (forall (T0 T1 : Tape Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (none :: padding))
        (Tape.normalizedOutput
          (guardedTwoTapeStructuredPrefixEraserTargetTape
            [] (none :: padding)))) ∧
    forall (T0 T1 : Tape Bool) (padBit : Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 [] (some padBit :: padding))
        (Tape.normalizedOutput
          (guardedTwoTapeStructuredPrefixEraserTargetTape
            [] (some padBit :: padding)))

def GuardedTwoTapeStructuredPrefixEraserConsPadSymbolCaseOutputSpec
    (eraser : MachineDescription) : Prop :=
  eraser.SubroutineReady ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool),
      eraser.HaltsFromTapeWithOutput
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) [])
        (Tape.normalizedOutput
          (guardedTwoTapeStructuredPrefixEraserTargetTape
            (bit :: rest) []))) ∧
    (forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (none :: padding))
        (Tape.normalizedOutput
          (guardedTwoTapeStructuredPrefixEraserTargetTape
            (bit :: rest) (none :: padding)))) ∧
    forall (T0 T1 : Tape Bool) (bit : Bool) (rest : Word Bool)
      (padBit : Bool) (padding : List (Option Bool)),
      eraser.HaltsFromTapeWithOutput
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 (bit :: rest) (some padBit :: padding))
        (Tape.normalizedOutput
          (guardedTwoTapeStructuredPrefixEraserTargetTape
            (bit :: rest) (some padBit :: padding)))

def GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputSpec
    (eraser : MachineDescription) : Prop :=
  GuardedTwoTapeStructuredPrefixEraserNilPadSymbolCaseOutputSpec
      eraser ∧
    GuardedTwoTapeStructuredPrefixEraserConsPadSymbolCaseOutputSpec
      eraser

def GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputConstruction :
    Prop :=
  exists eraser : MachineDescription,
    GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputSpec
      eraser

theorem guardedTwoTapeStructuredPrefixEraserCaseOutputSpec_of_outputSpec
    {eraser : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixEraserOutputSpec eraser) :
    GuardedTwoTapeStructuredPrefixEraserCaseOutputSpec eraser := by
  rcases h with ⟨hready, hrun⟩
  refine ⟨hready, ?_, ?_⟩
  · intro T0 T1 padding
    exact hrun T0 T1 [] padding
  · intro T0 T1 bit rest padding
    exact hrun T0 T1 (bit :: rest) padding

theorem guardedTwoTapeStructuredPrefixEraserOutputSpec_of_caseOutputSpec
    {eraser : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixEraserCaseOutputSpec eraser) :
    GuardedTwoTapeStructuredPrefixEraserOutputSpec eraser := by
  rcases h with ⟨hready, hnil, hcons⟩
  refine ⟨hready, ?_⟩
  intro T0 T1 bits padding
  cases bits with
  | nil =>
      exact hnil T0 T1 padding
  | cons bit rest =>
      exact hcons T0 T1 bit rest padding

theorem guardedTwoTapeStructuredPrefixEraserCaseOutputConstruction_of_output
    (h :
      GuardedTwoTapeStructuredPrefixEraserOutputConstruction) :
    GuardedTwoTapeStructuredPrefixEraserCaseOutputConstruction := by
  rcases h with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      guardedTwoTapeStructuredPrefixEraserCaseOutputSpec_of_outputSpec
        hspec⟩

theorem guardedTwoTapeStructuredPrefixEraserOutputConstruction_of_caseOutput
    (h :
      GuardedTwoTapeStructuredPrefixEraserCaseOutputConstruction) :
    GuardedTwoTapeStructuredPrefixEraserOutputConstruction := by
  rcases h with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      guardedTwoTapeStructuredPrefixEraserOutputSpec_of_caseOutputSpec
        hspec⟩

theorem guardedTwoTapeStructuredPrefixEraserCaseOutputSpec_of_bitPaddingCaseOutputSpec
    {eraser : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixEraserBitPaddingCaseOutputSpec
        eraser) :
    GuardedTwoTapeStructuredPrefixEraserCaseOutputSpec eraser := by
  rcases h with
    ⟨hready, hnilNil, hnilCons, hconsNil, hconsCons⟩
  refine ⟨hready, ?_, ?_⟩
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

theorem guardedTwoTapeStructuredPrefixEraserBitPaddingCaseOutputSpec_of_padSymbolCaseOutputSpec
    {eraser : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputSpec
        eraser) :
    GuardedTwoTapeStructuredPrefixEraserBitPaddingCaseOutputSpec
      eraser := by
  rcases h with ⟨hnil, hcons⟩
  rcases hnil with ⟨hready, hnilNil, hnilNone, hnilSome⟩
  rcases hcons with
    ⟨_hreadyCons, hconsNil, hconsNone, hconsSome⟩
  refine ⟨hready, hnilNil, ?_, hconsNil, ?_⟩
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

theorem guardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputSpec_of_outputSpec
    {eraser : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixEraserOutputSpec eraser) :
    GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputSpec
      eraser := by
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

theorem guardedTwoTapeStructuredPrefixEraserOutputSpec_of_splitPadSymbolCaseOutputSpec
    {eraser : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputSpec
        eraser) :
    GuardedTwoTapeStructuredPrefixEraserOutputSpec eraser := by
  have hbit :
      GuardedTwoTapeStructuredPrefixEraserBitPaddingCaseOutputSpec
        eraser :=
    guardedTwoTapeStructuredPrefixEraserBitPaddingCaseOutputSpec_of_padSymbolCaseOutputSpec
      h
  exact
    guardedTwoTapeStructuredPrefixEraserOutputSpec_of_caseOutputSpec
      (guardedTwoTapeStructuredPrefixEraserCaseOutputSpec_of_bitPaddingCaseOutputSpec
        hbit)

theorem guardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputConstruction_of_output
    (h :
      GuardedTwoTapeStructuredPrefixEraserOutputConstruction) :
    GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputConstruction := by
  rcases h with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      guardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputSpec_of_outputSpec
        hspec⟩

theorem guardedTwoTapeStructuredPrefixEraserOutputConstruction_of_splitPadSymbolCasesOutput
    (h :
      GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputConstruction) :
    GuardedTwoTapeStructuredPrefixEraserOutputConstruction := by
  rcases h with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      guardedTwoTapeStructuredPrefixEraserOutputSpec_of_splitPadSymbolCaseOutputSpec
        hspec⟩

theorem guardedTwoTapeStructuredPrefixEraserOutputSpec_iff_splitPadSymbolCaseOutputSpec
    (eraser : MachineDescription) :
    GuardedTwoTapeStructuredPrefixEraserOutputSpec eraser ↔
      GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputSpec
        eraser := by
  constructor
  · exact
      guardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputSpec_of_outputSpec
  · exact
      guardedTwoTapeStructuredPrefixEraserOutputSpec_of_splitPadSymbolCaseOutputSpec

theorem guardedTwoTapeStructuredPrefixEraserOutputConstruction_iff_splitPadSymbolCaseOutputConstruction :
    GuardedTwoTapeStructuredPrefixEraserOutputConstruction ↔
      GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputConstruction := by
  constructor
  · exact
      guardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputConstruction_of_output
  · exact
      guardedTwoTapeStructuredPrefixEraserOutputConstruction_of_splitPadSymbolCasesOutput

theorem guardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputSpec_of_exact
    {eraser : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseSpec
        eraser) :
    GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputSpec
      eraser := by
  have hspec :
      GuardedTwoTapeStructuredPrefixEraserSpec eraser :=
    guardedTwoTapeStructuredPrefixEraserSpec_of_splitPadSymbolCaseSpec h
  exact
    guardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputSpec_of_outputSpec
      (guardedTwoTapeStructuredPrefixEraserOutputSpec_of_exact hspec)

theorem guardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputConstruction_of_exact
    (h :
      GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseConstruction) :
    GuardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputConstruction := by
  rcases h with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      guardedTwoTapeStructuredPrefixEraserSplitPadSymbolCaseOutputSpec_of_exact
        hspec⟩

/-! ## Boundary-phase output bundles -/

def GuardedTwoTapeStructuredPrefixBoundaryEraserPairOutputSpec
    (eraser : MachineDescription) : Prop :=
  GuardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserOutputSpec
      eraser ∧
    GuardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserOutputSpec
      eraser

def GuardedTwoTapeStructuredPrefixBoundaryEraserPairOutputConstruction :
    Prop :=
  exists eraser : MachineDescription,
    GuardedTwoTapeStructuredPrefixBoundaryEraserPairOutputSpec eraser

theorem guardedTwoTapeStructuredPrefixBoundaryEraserPairOutputSpec_of_exact
    {eraser : MachineDescription}
    (h :
      GuardedTwoTapeStructuredPrefixBoundaryEraserPairSpec eraser) :
    GuardedTwoTapeStructuredPrefixBoundaryEraserPairOutputSpec
      eraser := by
  rcases h with ⟨hsecond, hfirst⟩
  exact
    ⟨guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserOutputSpec_of_exact
        hsecond,
      guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserOutputSpec_of_exact
        hfirst⟩

theorem guardedTwoTapeStructuredPrefixBoundaryEraserPairOutputConstruction_of_exact
    (h :
      GuardedTwoTapeStructuredPrefixBoundaryEraserPairConstruction) :
    GuardedTwoTapeStructuredPrefixBoundaryEraserPairOutputConstruction := by
  rcases h with ⟨eraser, hspec⟩
  exact
    ⟨eraser,
      guardedTwoTapeStructuredPrefixBoundaryEraserPairOutputSpec_of_exact
        hspec⟩

theorem guardedTwoTapeStructuredPrefixBoundaryEraserPairOutputSpec_core :
    GuardedTwoTapeStructuredPrefixBoundaryEraserPairOutputSpec
      leftBoundaryEraserDescription :=
  guardedTwoTapeStructuredPrefixBoundaryEraserPairOutputSpec_of_exact
    guardedTwoTapeStructuredPrefixBoundaryEraserPairSpec_core

theorem guardedTwoTapeStructuredPrefixBoundaryEraserPairOutputConstruction_core :
    GuardedTwoTapeStructuredPrefixBoundaryEraserPairOutputConstruction :=
  ⟨leftBoundaryEraserDescription,
    guardedTwoTapeStructuredPrefixBoundaryEraserPairOutputSpec_core⟩

/--
Output-level components for the full endpoint route exposed by the boundary
phase split.  This deliberately does not compose the machines; it records the
exact contracts that a later sequence proof must consume.
-/
def GuardedTwoTapeStructuredPrefixBoundaryRouteOutputComponentsSpec
    (initialPositioner secondEraser betweenPositioner firstEraser
      erasedPrefixCompactor : MachineDescription) : Prop :=
  GuardedTwoTapeStructuredPrefixInitialPositionerOutputSpec
      initialPositioner ∧
    GuardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserOutputSpec
      secondEraser ∧
    GuardedTwoTapeStructuredPrefixBetweenFieldsPositionerOutputSpec
      betweenPositioner ∧
    GuardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserOutputSpec
      firstEraser ∧
    GuardedTwoTapeStructuredPrefixErasedPrefixCompactorOutputSpec
      erasedPrefixCompactor

def GuardedTwoTapeStructuredPrefixBoundaryRouteOutputComponentsConstruction :
    Prop :=
  exists initialPositioner secondEraser betweenPositioner firstEraser
      erasedPrefixCompactor : MachineDescription,
    GuardedTwoTapeStructuredPrefixBoundaryRouteOutputComponentsSpec
      initialPositioner secondEraser betweenPositioner firstEraser
      erasedPrefixCompactor

theorem guardedTwoTapeStructuredPrefixBoundaryRouteOutputComponentsSpec_of_exact
    {initialPositioner secondEraser betweenPositioner firstEraser
      erasedPrefixCompactor : MachineDescription}
    (hinitial :
      GuardedTwoTapeStructuredPrefixInitialPositionerSpec
        initialPositioner)
    (hsecond :
      GuardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSpec
        secondEraser)
    (hbetween :
      GuardedTwoTapeStructuredPrefixBetweenFieldsPositionerSpec
        betweenPositioner)
    (hfirst :
      GuardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSpec
        firstEraser)
    (hcompactor :
      GuardedTwoTapeStructuredPrefixErasedPrefixCompactorSpec
        erasedPrefixCompactor) :
    GuardedTwoTapeStructuredPrefixBoundaryRouteOutputComponentsSpec
      initialPositioner secondEraser betweenPositioner firstEraser
      erasedPrefixCompactor := by
  exact
    ⟨guardedTwoTapeStructuredPrefixInitialPositionerOutputSpec_of_exact
        hinitial,
      guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserOutputSpec_of_exact
        hsecond,
      guardedTwoTapeStructuredPrefixBetweenFieldsPositionerOutputSpec_of_exact
        hbetween,
      guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserOutputSpec_of_exact
        hfirst,
      guardedTwoTapeStructuredPrefixErasedPrefixCompactorOutputSpec_of_exact
        hcompactor⟩

theorem guardedTwoTapeStructuredPrefixBoundaryRouteOutputComponentsConstruction_of_exact
    (hinitial :
      GuardedTwoTapeStructuredPrefixInitialPositionerConstruction)
    (hsecond :
      GuardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserConstruction)
    (hbetween :
      GuardedTwoTapeStructuredPrefixBetweenFieldsPositionerConstruction)
    (hfirst :
      GuardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserConstruction)
    (hcompactor :
      GuardedTwoTapeStructuredPrefixErasedPrefixCompactorConstruction) :
    GuardedTwoTapeStructuredPrefixBoundaryRouteOutputComponentsConstruction := by
  rcases hinitial with ⟨initialPositioner, hinitialSpec⟩
  rcases hsecond with ⟨secondEraser, hsecondSpec⟩
  rcases hbetween with ⟨betweenPositioner, hbetweenSpec⟩
  rcases hfirst with ⟨firstEraser, hfirstSpec⟩
  rcases hcompactor with ⟨erasedPrefixCompactor, hcompactorSpec⟩
  exact
    ⟨initialPositioner, secondEraser, betweenPositioner,
      firstEraser, erasedPrefixCompactor,
      guardedTwoTapeStructuredPrefixBoundaryRouteOutputComponentsSpec_of_exact
        hinitialSpec hsecondSpec hbetweenSpec hfirstSpec
        hcompactorSpec⟩

theorem guardedTwoTapeStructuredPrefixBoundaryRouteOutputComponentsSpec_secondFirst_core
    {initialPositioner betweenPositioner erasedPrefixCompactor :
      MachineDescription}
    (hinitial :
      GuardedTwoTapeStructuredPrefixInitialPositionerOutputSpec
        initialPositioner)
    (hbetween :
      GuardedTwoTapeStructuredPrefixBetweenFieldsPositionerOutputSpec
        betweenPositioner)
    (hcompactor :
      GuardedTwoTapeStructuredPrefixErasedPrefixCompactorOutputSpec
        erasedPrefixCompactor) :
    GuardedTwoTapeStructuredPrefixBoundaryRouteOutputComponentsSpec
      initialPositioner leftBoundaryEraserDescription
      betweenPositioner leftBoundaryEraserDescription
      erasedPrefixCompactor := by
  exact
    ⟨hinitial,
      guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserOutputSpec_core,
      hbetween,
      guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserOutputSpec_core,
      hcompactor⟩

theorem guardedTwoTapeStructuredPrefixBoundaryRouteOutputComponentsConstruction_secondFirst_core
    (hinitial :
      exists initialPositioner : MachineDescription,
        GuardedTwoTapeStructuredPrefixInitialPositionerOutputSpec
          initialPositioner)
    (hbetween :
      exists betweenPositioner : MachineDescription,
        GuardedTwoTapeStructuredPrefixBetweenFieldsPositionerOutputSpec
          betweenPositioner)
    (hcompactor :
      exists erasedPrefixCompactor : MachineDescription,
        GuardedTwoTapeStructuredPrefixErasedPrefixCompactorOutputSpec
          erasedPrefixCompactor) :
    GuardedTwoTapeStructuredPrefixBoundaryRouteOutputComponentsConstruction := by
  rcases hinitial with ⟨initialPositioner, hinitialSpec⟩
  rcases hbetween with ⟨betweenPositioner, hbetweenSpec⟩
  rcases hcompactor with ⟨erasedPrefixCompactor, hcompactorSpec⟩
  exact
    ⟨initialPositioner, leftBoundaryEraserDescription,
      betweenPositioner, leftBoundaryEraserDescription,
      erasedPrefixCompactor,
      guardedTwoTapeStructuredPrefixBoundaryRouteOutputComponentsSpec_secondFirst_core
        hinitialSpec hbetweenSpec hcompactorSpec⟩

/-! ## Named endpoint output equalities for phase composition -/

theorem guardedTwoTapeStructuredPrefixBoundaryRouteSource_normalizedOutput
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixEraserSourceTape
          T0 T1 bits padding) =
      List.append (logicalTapeBits (guardLogicalTape T0))
        (List.append (logicalTapeBits (guardLogicalTape T1))
          (List.append bits (padding.filterMap (fun cell => cell)))) := by
  rw [
    guardedTwoTapeStructuredPrefixEraserSourceTape_normalizedOutput_eq_guardedBits_append_target,
    guardedTwoTapeStructuredPrefixEraserTargetTape_normalizedOutput]

theorem guardedTwoTapeStructuredPrefixBoundaryRouteTarget_normalizedOutput
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixEraserTargetTape
          bits padding) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  exact
    guardedTwoTapeStructuredPrefixEraserTargetTape_normalizedOutput
      bits padding

theorem guardedTwoTapeStructuredPrefixBoundaryRouteTargetRightEdge_normalizedOutput
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixEraserTargetRightEdgeTape
          bits padding) =
      Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixEraserTargetTape
          bits padding) := by
  rw [← guardedTwoTapeStructuredPrefixEraserTargetTape_eq_rightEdgeTape]

theorem guardedTwoTapeStructuredPrefixBoundaryRouteTargetRightEdge_normalizedOutput_eq
    (bits : Word Bool) (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixEraserTargetRightEdgeTape
          bits padding) =
      List.append bits (padding.filterMap (fun cell => cell)) := by
  rw [guardedTwoTapeStructuredPrefixBoundaryRouteTargetRightEdge_normalizedOutput,
    guardedTwoTapeStructuredPrefixBoundaryRouteTarget_normalizedOutput]

theorem guardedTwoTapeStructuredPrefixBoundaryRouteFirstFieldTarget_to_final_output
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserTargetTape
          T0 T1 bits padding) =
      Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixEraserTargetRightEdgeTape
          bits padding) := by
  exact
    guardedTwoTapeStructuredPrefixErasedPrefixCompactorSourceTarget_normalizedOutput_eq
      T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixBoundaryRouteSecondFieldTarget_to_firstSource_output
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserTargetTape
          T0 T1 bits padding) =
      Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixFirstFieldBoundaryEraserSourceTape
          T0 T1 bits padding) := by
  exact
    guardedTwoTapeStructuredPrefixBetweenFieldsPositionerSourceTarget_normalizedOutput_eq
      T0 T1 bits padding

theorem guardedTwoTapeStructuredPrefixBoundaryRouteInitialTarget_to_secondSource_output
    (T0 T1 : Tape Bool) (bits : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixEraserSourceRightEdgeTape
          T0 T1 bits padding) =
      Tape.normalizedOutput
        (guardedTwoTapeStructuredPrefixSecondFieldBoundaryEraserSourceTape
          T0 T1 bits padding) := by
  exact
    guardedTwoTapeStructuredPrefixInitialPositionerSourceTarget_normalizedOutput_eq
      T0 T1 bits padding

end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
