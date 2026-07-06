import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredInputMaterializerEndpoint
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredInputMaterializerOutput

set_option doc.verso true

/-!
# Structured input materializer route contracts

This module packages the generic three-logical-tape input materializer route.
The route is intentionally construction-neutral: it exposes the exact
{lit}`HaltsFromTapeEquiv` boundary, the weaker normalized-output boundary, the
named target-family view, and the canonical endpoint shape without introducing
a new finite-machine leaf.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

open Structured.MultiTapeLowering

namespace StructuredInputMaterializerRouteContracts

/-!
## Canonical endpoint route shape
-/

structure TargetEndpointShape
    (source output : Tape Bool) : Prop where
  logicalTapesEq :
    StructuredInputMaterializerEndpoint.logicalTapes source output =
      [source, Tape.blank, output]
  guardedLogicalTapesEq :
    StructuredInputMaterializerEndpoint.guardedLogicalTapes source output =
      [guardLogicalTape source, guardLogicalTape Tape.blank,
        guardLogicalTape output]
  targetTapeEqMaterializer :
    StructuredInputMaterializerEndpoint.targetTape source output =
      structured3InputMaterializerTargetTape source output
  targetTapeEqEncodedGuardedStructured3 :
    StructuredInputMaterializerEndpoint.targetTape source output =
      encodedGuardedStructured3Tapes source Tape.blank output
  targetTapeEqEncodedStructuredTapesGuarded :
    StructuredInputMaterializerEndpoint.targetTape source output =
      encodedStructuredTapes
        (StructuredInputMaterializerEndpoint.guardedLogicalTapes
          source output)
  targetRead :
    Tape.read
        (StructuredInputMaterializerEndpoint.targetTape source output) =
      none
  targetCells :
    Tape.cells
        (StructuredInputMaterializerEndpoint.targetTape source output) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape source))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape Tape.blank))
              (List.append tapeSeparatorCells
                (List.append (logicalTapeCode (guardLogicalTape output))
                  tapeSeparatorCells)))))
  separator0TapeEqTarget :
    StructuredInputMaterializerEndpoint.separator0Tape source output =
      StructuredInputMaterializerEndpoint.targetTape source output
  separator1TapeEqExpanded :
    StructuredInputMaterializerEndpoint.separator1Tape source output =
      tapeAtEncodedSplit
        (List.append tapeSeparatorCells
          (logicalTapeCode (guardLogicalTape source)))
        (List.append tapeSeparatorCells
          (List.append (logicalTapeCode (guardLogicalTape Tape.blank))
            (List.append tapeSeparatorCells
              (List.append (logicalTapeCode (guardLogicalTape output))
                tapeSeparatorCells))))
  separator2TapeEqExpanded :
    StructuredInputMaterializerEndpoint.separator2Tape source output =
      tapeAtEncodedSplit
        (List.append
          (List.append tapeSeparatorCells
            (logicalTapeCode (guardLogicalTape source)))
          (List.append tapeSeparatorCells
            (logicalTapeCode (guardLogicalTape Tape.blank))))
        (List.append tapeSeparatorCells
          (List.append (logicalTapeCode (guardLogicalTape output))
            tapeSeparatorCells))
  guardedSourceEquiv :
    Tape.Equiv
      (StructuredInputMaterializerEndpoint.guardedSourceTape source)
      source
  guardedScratchEquiv :
    Tape.Equiv
      StructuredInputMaterializerEndpoint.guardedScratchTape Tape.blank
  guardedOutputEquiv :
    Tape.Equiv
      (StructuredInputMaterializerEndpoint.guardedOutputTape output)
      output
  guardedSourceHasGuardCells :
    LogicalTapeHasGuardCells
      (StructuredInputMaterializerEndpoint.guardedSourceTape source)
  guardedScratchHasGuardCells :
    LogicalTapeHasGuardCells
      StructuredInputMaterializerEndpoint.guardedScratchTape
  guardedOutputHasGuardCells :
    LogicalTapeHasGuardCells
      (StructuredInputMaterializerEndpoint.guardedOutputTape output)
  guardedLogicalTapesHaveGuardCells :
    LogicalTapesHaveGuardCells
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output)
  guardedLogicalTapesAtHasGuardCells0 :
    LogicalTapeAtHasGuardCells
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output) 0
  guardedLogicalTapesAtHasGuardCells1 :
    LogicalTapeAtHasGuardCells
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output) 1
  guardedLogicalTapesAtHasGuardCells2 :
    LogicalTapeAtHasGuardCells
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output) 2
  atSeparator0 :
    AtTapeSeparator
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output) 0
      (StructuredInputMaterializerEndpoint.targetTape source output)
  atSeparator0ViaSeparatorTape :
    AtTapeSeparator
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output) 0
      (StructuredInputMaterializerEndpoint.separator0Tape source output)
  atSeparator1 :
    AtTapeSeparator
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output) 1
      (StructuredInputMaterializerEndpoint.separator1Tape source output)
  atSeparator2 :
    AtTapeSeparator
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output) 2
      (StructuredInputMaterializerEndpoint.separator2Tape source output)
  atExistingSeparator0 :
    AtExistingTapeSeparator
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output) 0
      (StructuredInputMaterializerEndpoint.targetTape source output)
  atExistingSeparator0ViaSeparatorTape :
    AtExistingTapeSeparator
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output) 0
      (StructuredInputMaterializerEndpoint.separator0Tape source output)
  atExistingSeparator1 :
    AtExistingTapeSeparator
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output) 1
      (StructuredInputMaterializerEndpoint.separator1Tape source output)
  atExistingSeparator2 :
    AtExistingTapeSeparator
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output) 2
      (StructuredInputMaterializerEndpoint.separator2Tape source output)
  atHeadMarker0 :
    AtTapeHeadMarker
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output) 0
      (StructuredInputMaterializerEndpoint.headMarker0Tape source output)
  atHeadMarker1 :
    AtTapeHeadMarker
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output) 1
      (StructuredInputMaterializerEndpoint.headMarker1Tape source output)
  atHeadMarker2 :
    AtTapeHeadMarker
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output) 2
      (StructuredInputMaterializerEndpoint.headMarker2Tape source output)
  atHeadCell0 :
    AtTapeHeadCellCode
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output) 0
      (StructuredInputMaterializerEndpoint.headCell0Tape source output)
  atHeadCell1 :
    AtTapeHeadCellCode
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output) 1
      (StructuredInputMaterializerEndpoint.headCell1Tape source output)
  atHeadCell2 :
    AtTapeHeadCellCode
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output) 2
      (StructuredInputMaterializerEndpoint.headCell2Tape source output)
  atSegmentEnd0 :
    AtTapeSegmentEnd
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output) 0
      (StructuredInputMaterializerEndpoint.segmentEnd0Tape source output)
  atSegmentEnd1 :
    AtTapeSegmentEnd
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output) 1
      (StructuredInputMaterializerEndpoint.segmentEnd1Tape source output)
  atSegmentEnd2 :
    AtTapeSegmentEnd
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output) 2
      (StructuredInputMaterializerEndpoint.segmentEnd2Tape source output)
  targetStructuredEncodedTapesGuarded :
    StructuredEncodedTapes
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output)
      (StructuredInputMaterializerEndpoint.targetTape source output)
  targetStructuredGuardedEncodedTapes :
    StructuredGuardedEncodedTapes
      (StructuredInputMaterializerEndpoint.logicalTapes source output)
      (StructuredInputMaterializerEndpoint.targetTape source output)
  targetStructuredLogicalEquivEncodedTapes :
    StructuredLogicalEquivEncodedTapes
      (StructuredInputMaterializerEndpoint.logicalTapes source output)
      (StructuredInputMaterializerEndpoint.targetTape source output)
  logicalTapesEquivGuardedLogicalTapes :
    LogicalTapeListEquiv
      (StructuredInputMaterializerEndpoint.guardedLogicalTapes
        source output)
      (StructuredInputMaterializerEndpoint.logicalTapes source output)
  targetNormalizedOutputGuardedLogicalBits :
    Tape.normalizedOutput
        (StructuredInputMaterializerEndpoint.targetTape source output) =
      List.append
        (logicalTapeBits
          (StructuredInputMaterializerEndpoint.guardedSourceTape source))
        (List.append
          (logicalTapeBits
            StructuredInputMaterializerEndpoint.guardedScratchTape)
          (logicalTapeBits
            (StructuredInputMaterializerEndpoint.guardedOutputTape output)))
  targetNormalizedOutputGuardedLogicalTapesBits :
    Tape.normalizedOutput
        (StructuredInputMaterializerEndpoint.targetTape source output) =
      List.append
        (logicalTapeBits
          ((StructuredInputMaterializerEndpoint.guardedLogicalTapes
            source output).get
            ⟨0, by simp [
              StructuredInputMaterializerEndpoint.guardedLogicalTapes,
              StructuredInputMaterializerEndpoint.logicalTapes]⟩))
        (List.append
          (logicalTapeBits
            ((StructuredInputMaterializerEndpoint.guardedLogicalTapes
              source output).get
              ⟨1, by simp [
                StructuredInputMaterializerEndpoint.guardedLogicalTapes,
                StructuredInputMaterializerEndpoint.logicalTapes]⟩))
          (logicalTapeBits
            ((StructuredInputMaterializerEndpoint.guardedLogicalTapes
              source output).get
              ⟨2, by simp [
                StructuredInputMaterializerEndpoint.guardedLogicalTapes,
                StructuredInputMaterializerEndpoint.logicalTapes]⟩)))

theorem targetEndpointShape
    (source output : Tape Bool) :
    TargetEndpointShape source output :=
  { logicalTapesEq :=
      StructuredInputMaterializerEndpoint.logicalTapes_eq source output
    guardedLogicalTapesEq :=
      StructuredInputMaterializerEndpoint.guardedLogicalTapes_eq
        source output
    targetTapeEqMaterializer := rfl
    targetTapeEqEncodedGuardedStructured3 :=
      StructuredInputMaterializerEndpoint.targetTape_eq_encodedGuardedStructured3Tapes
        source output
    targetTapeEqEncodedStructuredTapesGuarded :=
      StructuredInputMaterializerEndpoint.targetTape_eq_encodedStructuredTapes_guarded
        source output
    targetRead :=
      StructuredInputMaterializerEndpoint.targetTape_read source output
    targetCells :=
      StructuredInputMaterializerEndpoint.targetTape_cells source output
    separator0TapeEqTarget :=
      StructuredInputMaterializerEndpoint.separator0Tape_eq_targetTape
        source output
    separator1TapeEqExpanded :=
      StructuredInputMaterializerEndpoint.separator1Tape_eq_expanded
        source output
    separator2TapeEqExpanded :=
      StructuredInputMaterializerEndpoint.separator2Tape_eq_expanded
        source output
    guardedSourceEquiv :=
      StructuredInputMaterializerEndpoint.guardedSourceTape_equiv source
    guardedScratchEquiv :=
      StructuredInputMaterializerEndpoint.guardedScratchTape_equiv
    guardedOutputEquiv :=
      StructuredInputMaterializerEndpoint.guardedOutputTape_equiv output
    guardedSourceHasGuardCells :=
      StructuredInputMaterializerEndpoint.guardedSourceTape_hasGuardCells
        source
    guardedScratchHasGuardCells :=
      StructuredInputMaterializerEndpoint.guardedScratchTape_hasGuardCells
    guardedOutputHasGuardCells :=
      StructuredInputMaterializerEndpoint.guardedOutputTape_hasGuardCells
        output
    guardedLogicalTapesHaveGuardCells :=
      StructuredInputMaterializerEndpoint.guardedLogicalTapes_haveGuardCells
        source output
    guardedLogicalTapesAtHasGuardCells0 :=
      StructuredInputMaterializerEndpoint.guardedLogicalTapes_atHasGuardCells0
        source output
    guardedLogicalTapesAtHasGuardCells1 :=
      StructuredInputMaterializerEndpoint.guardedLogicalTapes_atHasGuardCells1
        source output
    guardedLogicalTapesAtHasGuardCells2 :=
      StructuredInputMaterializerEndpoint.guardedLogicalTapes_atHasGuardCells2
        source output
    atSeparator0 :=
      StructuredInputMaterializerEndpoint.atSeparator0 source output
    atSeparator0ViaSeparatorTape :=
      StructuredInputMaterializerEndpoint.atSeparator0_via_separatorTape
        source output
    atSeparator1 :=
      StructuredInputMaterializerEndpoint.atSeparator1 source output
    atSeparator2 :=
      StructuredInputMaterializerEndpoint.atSeparator2 source output
    atExistingSeparator0 :=
      StructuredInputMaterializerEndpoint.atExistingSeparator0
        source output
    atExistingSeparator0ViaSeparatorTape :=
      StructuredInputMaterializerEndpoint.atExistingSeparator0_via_separatorTape
        source output
    atExistingSeparator1 :=
      StructuredInputMaterializerEndpoint.atExistingSeparator1
        source output
    atExistingSeparator2 :=
      StructuredInputMaterializerEndpoint.atExistingSeparator2
        source output
    atHeadMarker0 :=
      StructuredInputMaterializerEndpoint.atHeadMarker0 source output
    atHeadMarker1 :=
      StructuredInputMaterializerEndpoint.atHeadMarker1 source output
    atHeadMarker2 :=
      StructuredInputMaterializerEndpoint.atHeadMarker2 source output
    atHeadCell0 :=
      StructuredInputMaterializerEndpoint.atHeadCell0 source output
    atHeadCell1 :=
      StructuredInputMaterializerEndpoint.atHeadCell1 source output
    atHeadCell2 :=
      StructuredInputMaterializerEndpoint.atHeadCell2 source output
    atSegmentEnd0 :=
      StructuredInputMaterializerEndpoint.atSegmentEnd0 source output
    atSegmentEnd1 :=
      StructuredInputMaterializerEndpoint.atSegmentEnd1 source output
    atSegmentEnd2 :=
      StructuredInputMaterializerEndpoint.atSegmentEnd2 source output
    targetStructuredEncodedTapesGuarded :=
      StructuredInputMaterializerEndpoint.targetTape_structuredEncodedTapes_guarded
        source output
    targetStructuredGuardedEncodedTapes :=
      StructuredInputMaterializerEndpoint.targetTape_structuredGuardedEncodedTapes
        source output
    targetStructuredLogicalEquivEncodedTapes :=
      StructuredInputMaterializerEndpoint.targetTape_structuredLogicalEquivEncodedTapes
        source output
    logicalTapesEquivGuardedLogicalTapes :=
      StructuredInputMaterializerEndpoint.logicalTapes_equiv_guardedLogicalTapes
        source output
    targetNormalizedOutputGuardedLogicalBits :=
      StructuredInputMaterializerEndpoint.targetTape_normalizedOutput_eq_guardedLogicalBits
        source output
    targetNormalizedOutputGuardedLogicalTapesBits :=
      StructuredInputMaterializerEndpoint.targetTape_normalizedOutput_eq_guardedLogicalTapes_bits
        source output }

theorem targetEndpointShape_targetRead
    (source output : Tape Bool) :
    Tape.read
        (StructuredInputMaterializerEndpoint.targetTape source output) =
      none :=
  (targetEndpointShape source output).targetRead

theorem targetEndpointShape_targetCells
    (source output : Tape Bool) :
    Tape.cells
        (StructuredInputMaterializerEndpoint.targetTape source output) =
      List.append tapeSeparatorCells
        (List.append (logicalTapeCode (guardLogicalTape source))
          (List.append tapeSeparatorCells
            (List.append (logicalTapeCode (guardLogicalTape Tape.blank))
              (List.append tapeSeparatorCells
                (List.append (logicalTapeCode (guardLogicalTape output))
                  tapeSeparatorCells))))) :=
  (targetEndpointShape source output).targetCells

theorem targetEndpointShape_structuredLogicalEquiv
    (source output : Tape Bool) :
    StructuredLogicalEquivEncodedTapes
      (StructuredInputMaterializerEndpoint.logicalTapes source output)
      (StructuredInputMaterializerEndpoint.targetTape source output) :=
  (targetEndpointShape source output).targetStructuredLogicalEquivEncodedTapes

theorem targetEndpointShape_normalizedOutput
    (source output : Tape Bool) :
    Tape.normalizedOutput
        (StructuredInputMaterializerEndpoint.targetTape source output) =
      List.append
        (logicalTapeBits
          (StructuredInputMaterializerEndpoint.guardedSourceTape source))
        (List.append
          (logicalTapeBits
            StructuredInputMaterializerEndpoint.guardedScratchTape)
          (logicalTapeBits
            (StructuredInputMaterializerEndpoint.guardedOutputTape output))) :=
  (targetEndpointShape source output).targetNormalizedOutputGuardedLogicalBits

/-!
## Exact materializer routes
-/

structure ExactMaterializerRoute {ι : Type}
    (source output : ι -> Tape Bool)
    (materializer : MachineDescription) : Prop where
  spec :
    Structured3InputMaterializerSpec source output materializer
  subroutineReady :
    materializer.SubroutineReady
  haltsTarget :
    forall input : ι,
      materializer.HaltsFromTapeEquiv
        (source input)
        (structured3InputMaterializerTargetTape
          (source input) (output input))
  outputSpec :
    Structured3InputMaterializerOutputSpec
      source output materializer
  outputHalts :
    forall input : ι,
      materializer.HaltsFromTapeWithOutput
        (source input)
        (Tape.normalizedOutput
          (structured3InputMaterializerTargetTape
            (source input) (output input)))
  endpointShape :
    forall input : ι,
      TargetEndpointShape (source input) (output input)

def ExactMaterializerRouteConstruction {ι : Type}
    (source output : ι -> Tape Bool) : Prop :=
  exists materializer : MachineDescription,
    ExactMaterializerRoute source output materializer

theorem exactMaterializerRoute_of_spec {ι : Type}
    {source output : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputMaterializerSpec source output materializer) :
    ExactMaterializerRoute source output materializer := by
  let houtput :
      Structured3InputMaterializerOutputSpec
        source output materializer :=
    structured3InputMaterializerOutputSpec_of_exact hmaterializer
  exact
    { spec := hmaterializer
      subroutineReady :=
        structured3InputMaterializerSpec_subroutineReady hmaterializer
      haltsTarget := by
        intro input
        exact
          structured3InputMaterializerSpec_haltsFromTapeEquiv
            hmaterializer input
      outputSpec := houtput
      outputHalts := by
        intro input
        exact
          structured3InputMaterializerOutputSpec_haltsFromTapeWithOutput
            houtput input
      endpointShape := by
        intro input
        exact targetEndpointShape (source input) (output input) }

theorem exactMaterializerRouteConstruction_of_materializerConstruction
    {ι : Type} {source output : ι -> Tape Bool}
    (hmaterializer :
      Structured3InputMaterializerConstruction source output) :
    ExactMaterializerRouteConstruction source output := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact ⟨materializer, exactMaterializerRoute_of_spec hspec⟩

theorem materializerConstruction_of_exactMaterializerRouteConstruction
    {ι : Type} {source output : ι -> Tape Bool}
    (hroute : ExactMaterializerRouteConstruction source output) :
    Structured3InputMaterializerConstruction source output := by
  rcases hroute with ⟨materializer, hmaterializer⟩
  exact ⟨materializer, hmaterializer.spec⟩

theorem exactMaterializerRouteConstruction_iff_materializerConstruction
    {ι : Type} {source output : ι -> Tape Bool} :
    ExactMaterializerRouteConstruction source output ↔
      Structured3InputMaterializerConstruction source output := by
  constructor
  · exact materializerConstruction_of_exactMaterializerRouteConstruction
  · exact exactMaterializerRouteConstruction_of_materializerConstruction

theorem exactMaterializerRoute_reindex {ι κ : Type}
    {source output : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hroute :
      ExactMaterializerRoute source output materializer)
    (index : κ -> ι) :
    ExactMaterializerRoute
      (fun input : κ => source (index input))
      (fun input : κ => output (index input))
      materializer :=
  exactMaterializerRoute_of_spec
    (structured3InputMaterializerSpec_reindex hroute.spec index)

theorem exactMaterializerRouteConstruction_reindex
    {ι κ : Type} {source output : ι -> Tape Bool}
    (hroute :
      ExactMaterializerRouteConstruction source output)
    (index : κ -> ι) :
    ExactMaterializerRouteConstruction
      (fun input : κ => source (index input))
      (fun input : κ => output (index input)) := by
  rcases hroute with ⟨materializer, hmaterializer⟩
  exact
    ⟨materializer,
      exactMaterializerRoute_reindex hmaterializer index⟩

theorem exactMaterializerRoute_of_eq {ι : Type}
    {source output source' output' : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hroute :
      ExactMaterializerRoute source output materializer)
    (hsource : forall input : ι, source' input = source input)
    (houtput : forall input : ι, output' input = output input) :
    ExactMaterializerRoute source' output' materializer :=
  exactMaterializerRoute_of_spec
    (structured3InputMaterializerSpec_of_eq
      hroute.spec hsource houtput)

theorem exactMaterializerRouteConstruction_of_eq {ι : Type}
    {source output source' output' : ι -> Tape Bool}
    (hroute :
      ExactMaterializerRouteConstruction source output)
    (hsource : forall input : ι, source' input = source input)
    (houtput : forall input : ι, output' input = output input) :
    ExactMaterializerRouteConstruction source' output' := by
  rcases hroute with ⟨materializer, hmaterializer⟩
  exact
    ⟨materializer,
      exactMaterializerRoute_of_eq hmaterializer hsource houtput⟩

/-!
## Exact named-target-family routes
-/

structure ExactTargetFamilyRoute {ι : Type}
    (source target : ι -> Tape Bool)
    (materializer : MachineDescription) : Prop where
  spec :
    Structured3InputTargetFamilySpec source target materializer
  subroutineReady :
    materializer.SubroutineReady
  haltsTarget :
    forall input : ι,
      materializer.HaltsFromTapeEquiv
        (source input) (target input)
  outputSpec :
    Structured3InputTargetFamilyOutputSpec
      source target materializer
  outputHalts :
    forall input : ι,
      materializer.HaltsFromTapeWithOutput
        (source input) (Tape.normalizedOutput (target input))

def ExactTargetFamilyRouteConstruction {ι : Type}
    (source target : ι -> Tape Bool) : Prop :=
  exists materializer : MachineDescription,
    ExactTargetFamilyRoute source target materializer

theorem exactTargetFamilyRoute_of_spec {ι : Type}
    {source target : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputTargetFamilySpec source target materializer) :
    ExactTargetFamilyRoute source target materializer := by
  let houtput :
      Structured3InputTargetFamilyOutputSpec
        source target materializer :=
    structured3InputTargetFamilyOutputSpec_of_exact hmaterializer
  exact
    { spec := hmaterializer
      subroutineReady :=
        structured3InputTargetFamilySpec_subroutineReady hmaterializer
      haltsTarget := by
        intro input
        exact
          structured3InputTargetFamilySpec_haltsFromTapeEquiv
            hmaterializer input
      outputSpec := houtput
      outputHalts := by
        intro input
        exact
          structured3InputTargetFamilyOutputSpec_haltsFromTapeWithOutput
            houtput input }

theorem exactTargetFamilyRouteConstruction_of_targetFamilyConstruction
    {ι : Type} {source target : ι -> Tape Bool}
    (hmaterializer :
      Structured3InputTargetFamilyConstruction source target) :
    ExactTargetFamilyRouteConstruction source target := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact ⟨materializer, exactTargetFamilyRoute_of_spec hspec⟩

theorem targetFamilyConstruction_of_exactTargetFamilyRouteConstruction
    {ι : Type} {source target : ι -> Tape Bool}
    (hroute : ExactTargetFamilyRouteConstruction source target) :
    Structured3InputTargetFamilyConstruction source target := by
  rcases hroute with ⟨materializer, hmaterializer⟩
  exact ⟨materializer, hmaterializer.spec⟩

theorem exactTargetFamilyRouteConstruction_iff_targetFamilyConstruction
    {ι : Type} {source target : ι -> Tape Bool} :
    ExactTargetFamilyRouteConstruction source target ↔
      Structured3InputTargetFamilyConstruction source target := by
  constructor
  · exact targetFamilyConstruction_of_exactTargetFamilyRouteConstruction
  · exact exactTargetFamilyRouteConstruction_of_targetFamilyConstruction

theorem exactTargetFamilyRoute_of_materializerRoute
    {ι : Type} {source output target : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hroute :
      ExactMaterializerRoute source output materializer)
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input)) :
    ExactTargetFamilyRoute source target materializer :=
  exactTargetFamilyRoute_of_spec
    (structured3InputTargetFamilySpec_of_materializerSpec
      hroute.spec htarget)

theorem exactMaterializerRoute_of_targetFamilyRoute
    {ι : Type} {source output target : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hroute :
      ExactTargetFamilyRoute source target materializer)
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input)) :
    ExactMaterializerRoute source output materializer :=
  exactMaterializerRoute_of_spec
    (structured3InputMaterializerSpec_of_targetFamilySpec
      hroute.spec htarget)

theorem exactTargetFamilyRouteConstruction_of_materializerRouteConstruction
    {ι : Type} {source output target : ι -> Tape Bool}
    (hroute :
      ExactMaterializerRouteConstruction source output)
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input)) :
    ExactTargetFamilyRouteConstruction source target := by
  rcases hroute with ⟨materializer, hmaterializer⟩
  exact
    ⟨materializer,
      exactTargetFamilyRoute_of_materializerRoute
        hmaterializer htarget⟩

theorem exactMaterializerRouteConstruction_of_targetFamilyRouteConstruction
    {ι : Type} {source output target : ι -> Tape Bool}
    (hroute :
      ExactTargetFamilyRouteConstruction source target)
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input)) :
    ExactMaterializerRouteConstruction source output := by
  rcases hroute with ⟨materializer, hmaterializer⟩
  exact
    ⟨materializer,
      exactMaterializerRoute_of_targetFamilyRoute
        hmaterializer htarget⟩

theorem exactMaterializerRouteConstruction_iff_targetFamilyRouteConstruction
    {ι : Type} {source output target : ι -> Tape Bool}
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input)) :
    ExactMaterializerRouteConstruction source output ↔
      ExactTargetFamilyRouteConstruction source target := by
  constructor
  · intro hroute
    exact
      exactTargetFamilyRouteConstruction_of_materializerRouteConstruction
        hroute htarget
  · intro hroute
    exact
      exactMaterializerRouteConstruction_of_targetFamilyRouteConstruction
        hroute htarget

theorem exactTargetFamilyRoute_reindex {ι κ : Type}
    {source target : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hroute :
      ExactTargetFamilyRoute source target materializer)
    (index : κ -> ι) :
    ExactTargetFamilyRoute
      (fun input : κ => source (index input))
      (fun input : κ => target (index input))
      materializer :=
  exactTargetFamilyRoute_of_spec
    (structured3InputTargetFamilySpec_reindex hroute.spec index)

theorem exactTargetFamilyRouteConstruction_reindex
    {ι κ : Type} {source target : ι -> Tape Bool}
    (hroute :
      ExactTargetFamilyRouteConstruction source target)
    (index : κ -> ι) :
    ExactTargetFamilyRouteConstruction
      (fun input : κ => source (index input))
      (fun input : κ => target (index input)) := by
  rcases hroute with ⟨materializer, hmaterializer⟩
  exact
    ⟨materializer,
      exactTargetFamilyRoute_reindex hmaterializer index⟩

theorem exactTargetFamilyRoute_of_eq {ι : Type}
    {source target source' target' : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hroute :
      ExactTargetFamilyRoute source target materializer)
    (hsource : forall input : ι, source' input = source input)
    (htarget : forall input : ι, target' input = target input) :
    ExactTargetFamilyRoute source' target' materializer :=
  exactTargetFamilyRoute_of_spec
    (structured3InputTargetFamilySpec_of_eq
      hroute.spec hsource htarget)

/-!
## Output materializer routes
-/

structure OutputMaterializerRoute {ι : Type}
    (source output : ι -> Tape Bool)
    (materializer : MachineDescription) : Prop where
  spec :
    Structured3InputMaterializerOutputSpec
      source output materializer
  subroutineReady :
    materializer.SubroutineReady
  outputHalts :
    forall input : ι,
      materializer.HaltsFromTapeWithOutput
        (source input)
        (Tape.normalizedOutput
          (structured3InputMaterializerTargetTape
            (source input) (output input)))
  endpointShape :
    forall input : ι,
      TargetEndpointShape (source input) (output input)

def OutputMaterializerRouteConstruction {ι : Type}
    (source output : ι -> Tape Bool) : Prop :=
  exists materializer : MachineDescription,
    OutputMaterializerRoute source output materializer

theorem outputMaterializerRoute_of_spec {ι : Type}
    {source output : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputMaterializerOutputSpec source output materializer) :
    OutputMaterializerRoute source output materializer :=
  { spec := hmaterializer
    subroutineReady :=
      structured3InputMaterializerOutputSpec_subroutineReady
        hmaterializer
    outputHalts := by
      intro input
      exact
        structured3InputMaterializerOutputSpec_haltsFromTapeWithOutput
          hmaterializer input
    endpointShape := by
      intro input
      exact targetEndpointShape (source input) (output input) }

theorem outputMaterializerRoute_of_exactRoute {ι : Type}
    {source output : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hroute :
      ExactMaterializerRoute source output materializer) :
    OutputMaterializerRoute source output materializer :=
  outputMaterializerRoute_of_spec hroute.outputSpec

theorem outputMaterializerRouteConstruction_of_outputConstruction
    {ι : Type} {source output : ι -> Tape Bool}
    (hmaterializer :
      Structured3InputMaterializerOutputConstruction source output) :
    OutputMaterializerRouteConstruction source output := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact ⟨materializer, outputMaterializerRoute_of_spec hspec⟩

theorem outputConstruction_of_outputMaterializerRouteConstruction
    {ι : Type} {source output : ι -> Tape Bool}
    (hroute : OutputMaterializerRouteConstruction source output) :
    Structured3InputMaterializerOutputConstruction source output := by
  rcases hroute with ⟨materializer, hmaterializer⟩
  exact ⟨materializer, hmaterializer.spec⟩

theorem outputMaterializerRouteConstruction_iff_outputConstruction
    {ι : Type} {source output : ι -> Tape Bool} :
    OutputMaterializerRouteConstruction source output ↔
      Structured3InputMaterializerOutputConstruction source output := by
  constructor
  · exact outputConstruction_of_outputMaterializerRouteConstruction
  · exact outputMaterializerRouteConstruction_of_outputConstruction

theorem outputMaterializerRouteConstruction_of_exactRouteConstruction
    {ι : Type} {source output : ι -> Tape Bool}
    (hroute :
      ExactMaterializerRouteConstruction source output) :
    OutputMaterializerRouteConstruction source output := by
  rcases hroute with ⟨materializer, hmaterializer⟩
  exact
    ⟨materializer,
      outputMaterializerRoute_of_exactRoute hmaterializer⟩

theorem outputMaterializerRouteConstruction_of_exactConstruction
    {ι : Type} {source output : ι -> Tape Bool}
    (hmaterializer :
      Structured3InputMaterializerConstruction source output) :
    OutputMaterializerRouteConstruction source output :=
  outputMaterializerRouteConstruction_of_exactRouteConstruction
    (exactMaterializerRouteConstruction_of_materializerConstruction
      hmaterializer)

theorem outputMaterializerRoute_reindex {ι κ : Type}
    {source output : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hroute :
      OutputMaterializerRoute source output materializer)
    (index : κ -> ι) :
    OutputMaterializerRoute
      (fun input : κ => source (index input))
      (fun input : κ => output (index input))
      materializer :=
  outputMaterializerRoute_of_spec
    (structured3InputMaterializerOutputSpec_reindex
      hroute.spec index)

theorem outputMaterializerRouteConstruction_reindex
    {ι κ : Type} {source output : ι -> Tape Bool}
    (hroute :
      OutputMaterializerRouteConstruction source output)
    (index : κ -> ι) :
    OutputMaterializerRouteConstruction
      (fun input : κ => source (index input))
      (fun input : κ => output (index input)) := by
  rcases hroute with ⟨materializer, hmaterializer⟩
  exact
    ⟨materializer,
      outputMaterializerRoute_reindex hmaterializer index⟩

/-!
## Output named-target-family routes
-/

structure OutputTargetFamilyRoute {ι : Type}
    (source target : ι -> Tape Bool)
    (materializer : MachineDescription) : Prop where
  spec :
    Structured3InputTargetFamilyOutputSpec
      source target materializer
  subroutineReady :
    materializer.SubroutineReady
  outputHalts :
    forall input : ι,
      materializer.HaltsFromTapeWithOutput
        (source input) (Tape.normalizedOutput (target input))

def OutputTargetFamilyRouteConstruction {ι : Type}
    (source target : ι -> Tape Bool) : Prop :=
  exists materializer : MachineDescription,
    OutputTargetFamilyRoute source target materializer

theorem outputTargetFamilyRoute_of_spec {ι : Type}
    {source target : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hmaterializer :
      Structured3InputTargetFamilyOutputSpec
        source target materializer) :
    OutputTargetFamilyRoute source target materializer :=
  { spec := hmaterializer
    subroutineReady :=
      structured3InputTargetFamilyOutputSpec_subroutineReady
        hmaterializer
    outputHalts := by
      intro input
      exact
        structured3InputTargetFamilyOutputSpec_haltsFromTapeWithOutput
          hmaterializer input }

theorem outputTargetFamilyRoute_of_exactTargetFamilyRoute
    {ι : Type} {source target : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hroute :
      ExactTargetFamilyRoute source target materializer) :
    OutputTargetFamilyRoute source target materializer :=
  outputTargetFamilyRoute_of_spec hroute.outputSpec

theorem outputTargetFamilyRouteConstruction_of_outputConstruction
    {ι : Type} {source target : ι -> Tape Bool}
    (hmaterializer :
      Structured3InputTargetFamilyOutputConstruction source target) :
    OutputTargetFamilyRouteConstruction source target := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact ⟨materializer, outputTargetFamilyRoute_of_spec hspec⟩

theorem outputConstruction_of_outputTargetFamilyRouteConstruction
    {ι : Type} {source target : ι -> Tape Bool}
    (hroute : OutputTargetFamilyRouteConstruction source target) :
    Structured3InputTargetFamilyOutputConstruction source target := by
  rcases hroute with ⟨materializer, hmaterializer⟩
  exact ⟨materializer, hmaterializer.spec⟩

theorem outputTargetFamilyRouteConstruction_iff_outputConstruction
    {ι : Type} {source target : ι -> Tape Bool} :
    OutputTargetFamilyRouteConstruction source target ↔
      Structured3InputTargetFamilyOutputConstruction source target := by
  constructor
  · exact outputConstruction_of_outputTargetFamilyRouteConstruction
  · exact outputTargetFamilyRouteConstruction_of_outputConstruction

theorem outputTargetFamilyRouteConstruction_of_exactRouteConstruction
    {ι : Type} {source target : ι -> Tape Bool}
    (hroute :
      ExactTargetFamilyRouteConstruction source target) :
    OutputTargetFamilyRouteConstruction source target := by
  rcases hroute with ⟨materializer, hmaterializer⟩
  exact
    ⟨materializer,
      outputTargetFamilyRoute_of_exactTargetFamilyRoute
        hmaterializer⟩

theorem outputTargetFamilyRoute_of_materializerRoute
    {ι : Type} {source output target : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hroute :
      OutputMaterializerRoute source output materializer)
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input)) :
    OutputTargetFamilyRoute source target materializer :=
  outputTargetFamilyRoute_of_spec
    (structured3InputTargetFamilyOutputSpec_of_materializerOutputSpec
      hroute.spec htarget)

theorem outputMaterializerRoute_of_targetFamilyRoute
    {ι : Type} {source output target : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hroute :
      OutputTargetFamilyRoute source target materializer)
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input)) :
    OutputMaterializerRoute source output materializer :=
  outputMaterializerRoute_of_spec
    (structured3InputMaterializerOutputSpec_of_targetFamilyOutputSpec
      hroute.spec htarget)

theorem outputTargetFamilyRouteConstruction_of_materializerRouteConstruction
    {ι : Type} {source output target : ι -> Tape Bool}
    (hroute :
      OutputMaterializerRouteConstruction source output)
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input)) :
    OutputTargetFamilyRouteConstruction source target := by
  rcases hroute with ⟨materializer, hmaterializer⟩
  exact
    ⟨materializer,
      outputTargetFamilyRoute_of_materializerRoute
        hmaterializer htarget⟩

theorem outputMaterializerRouteConstruction_of_targetFamilyRouteConstruction
    {ι : Type} {source output target : ι -> Tape Bool}
    (hroute :
      OutputTargetFamilyRouteConstruction source target)
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input)) :
    OutputMaterializerRouteConstruction source output := by
  rcases hroute with ⟨materializer, hmaterializer⟩
  exact
    ⟨materializer,
      outputMaterializerRoute_of_targetFamilyRoute
        hmaterializer htarget⟩

theorem outputMaterializerRouteConstruction_iff_targetFamilyRouteConstruction
    {ι : Type} {source output target : ι -> Tape Bool}
    (htarget :
      forall input : ι,
        target input =
          structured3InputMaterializerTargetTape
            (source input) (output input)) :
    OutputMaterializerRouteConstruction source output ↔
      OutputTargetFamilyRouteConstruction source target := by
  constructor
  · intro hroute
    exact
      outputTargetFamilyRouteConstruction_of_materializerRouteConstruction
        hroute htarget
  · intro hroute
    exact
      outputMaterializerRouteConstruction_of_targetFamilyRouteConstruction
        hroute htarget

theorem outputTargetFamilyRoute_reindex {ι κ : Type}
    {source target : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hroute :
      OutputTargetFamilyRoute source target materializer)
    (index : κ -> ι) :
    OutputTargetFamilyRoute
      (fun input : κ => source (index input))
      (fun input : κ => target (index input))
      materializer :=
  outputTargetFamilyRoute_of_spec
    (structured3InputTargetFamilyOutputSpec_reindex
      hroute.spec index)

theorem outputTargetFamilyRouteConstruction_reindex
    {ι κ : Type} {source target : ι -> Tape Bool}
    (hroute :
      OutputTargetFamilyRouteConstruction source target)
    (index : κ -> ι) :
    OutputTargetFamilyRouteConstruction
      (fun input : κ => source (index input))
      (fun input : κ => target (index input)) := by
  rcases hroute with ⟨materializer, hmaterializer⟩
  exact
    ⟨materializer,
      outputTargetFamilyRoute_reindex hmaterializer index⟩

/-!
## Public route aliases
-/

theorem exactRouteConstruction_of_materializerConstruction
    {ι : Type} {source output : ι -> Tape Bool}
    (hmaterializer :
      Structured3InputMaterializerConstruction source output) :
    ExactMaterializerRouteConstruction source output :=
  exactMaterializerRouteConstruction_of_materializerConstruction
    hmaterializer

theorem materializerConstruction_of_exactRouteConstruction
    {ι : Type} {source output : ι -> Tape Bool}
    (hroute :
      ExactMaterializerRouteConstruction source output) :
    Structured3InputMaterializerConstruction source output :=
  materializerConstruction_of_exactMaterializerRouteConstruction
    hroute

theorem outputRouteConstruction_of_exactRouteConstruction
    {ι : Type} {source output : ι -> Tape Bool}
    (hroute :
      ExactMaterializerRouteConstruction source output) :
    OutputMaterializerRouteConstruction source output :=
  outputMaterializerRouteConstruction_of_exactRouteConstruction hroute

theorem endpointShape_of_exactRoute
    {ι : Type} {source output : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hroute :
      ExactMaterializerRoute source output materializer)
    (input : ι) :
    TargetEndpointShape (source input) (output input) :=
  hroute.endpointShape input

theorem endpointShape_of_outputRoute
    {ι : Type} {source output : ι -> Tape Bool}
    {materializer : MachineDescription}
    (hroute :
      OutputMaterializerRoute source output materializer)
    (input : ι) :
    TargetEndpointShape (source input) (output input) :=
  hroute.endpointShape input

end StructuredInputMaterializerRouteContracts

end FiniteTransducers
end CommonGround

end Computability
end FoC
