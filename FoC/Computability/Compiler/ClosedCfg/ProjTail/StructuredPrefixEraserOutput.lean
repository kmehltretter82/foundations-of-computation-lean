import FoC.Computability.Compiler.ClosedCfg.ProjTail.StructuredPrefixEraserBoundaryPhases

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
