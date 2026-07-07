import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTJoinerConstruction
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTStructuredOutputBridge

set_option doc.verso true

/-!
# Live-tail joiner route contracts

This module packages the assembly-specific live-tail joiner route.  The
structured raw-tail insertion joiner already proves the output-level run facts,
while the ordinary executable construction remains the finite-machine leaf in
{module}`FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTJoinerConstruction`.
The contracts below keep those two views connected at the assembly source-rest
endpoint used by the mixed parser-stack finisher.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer

/-!
## Assembly endpoint shape
-/

theorem structuredLiveTailJoinerAssemblySourceTape_eq_joinerFamily
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblySourceTape p =
      mixedOptionCellQuoteLiveTailJoinerFamilySourceTape
        assemblySourceRestLiveTailEmitterEmittedPrefix
        assemblySourceRestLiveTailEmitterRawTail
        assemblySourceRestLiveTailEmitterQuoteRest
        p := by
  rfl

theorem structuredLiveTailJoinerAssemblyTargetTape_eq_joinerFamily
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblyTargetTape p =
      mixedOptionCellQuoteLiveTailJoinerFamilyTargetTape
        assemblySourceRestLiveTailEmitterEmittedPrefix
        assemblySourceRestLiveTailEmitterRawTail
        assemblySourceRestLiveTailEmitterQuoteRest
        p := by
  rfl

theorem structuredLiveTailJoinerAssemblySourceOutput_eq_joinerFamily
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblySourceOutput p =
      mixedOptionCellQuoteLiveTailJoinerFamilySourceOutput
        assemblySourceRestLiveTailEmitterEmittedPrefix
        assemblySourceRestLiveTailEmitterRawTail
        assemblySourceRestLiveTailEmitterQuoteRest
        p := by
  rfl

theorem structuredLiveTailJoinerAssemblyTargetOutput_eq_joinerFamily
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblyTargetOutput p =
      mixedOptionCellQuoteLiveTailJoinerFamilyTargetOutput
        assemblySourceRestLiveTailEmitterEmittedPrefix
        assemblySourceRestLiveTailEmitterRawTail
        assemblySourceRestLiveTailEmitterQuoteRest
        p := by
  rfl

theorem structuredLiveTailJoinerAssemblySourceOutput_eq_segments
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblySourceOutput p =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (List.append
          (assemblySourceRestLiveTailEmitterRawTail p)
          (assemblySourceRestLiveTailEmitterQuoteRest p)) := by
  rfl

theorem structuredLiveTailJoinerAssemblyTargetOutput_eq_segments
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblyTargetOutput p =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (List.append
          (assemblySourceRestLiveTailEmitterQuoteRest p)
          (assemblySourceRestLiveTailEmitterRawTail p)) := by
  rfl

theorem structuredLiveTailJoinerAssemblyTargetOutput_eq_named
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblyTargetOutput p =
      List.append
        (assemblySourceRestFinishTargetPrefixBits
          p.w p.sourceRestBits p.stage)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            p.stage)
          p.sourceRestBits) := by
  rw [structuredLiveTailJoinerAssemblyTargetOutput_eq_joined,
    assemblySourceRestFinishJoinedOutput_eq_targetTape_namedOutput]

theorem structuredLiveTailJoinerAssemblySourceTape_normalizedOutput_eq_afterRawTailScan
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (structuredLiveTailJoinerAssemblySourceTape p) =
      Tape.normalizedOutput
        (MixedParserStackWholeSourceAfterRawTailScanTape
          p.w p.sourceRestBits p.stage) := by
  rw [structuredLiveTailJoinerAssemblySourceTape_eq_afterRawTailScan]

theorem structuredLiveTailJoinerAssemblyTargetTape_normalizedOutput_eq_targetTape
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (structuredLiveTailJoinerAssemblyTargetTape p) =
      Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape
          p.w p.sourceRestBits p.stage) := by
  rw [structuredLiveTailJoinerAssemblyTargetTape_eq_finishTarget]

structure LiveTailJoinerAssemblyShape
    (p : AssemblySourceRestLiveTailEmitterParam) : Prop where
  initialConfigEq :
    structuredLiveTailJoinerAssemblyInitialConfig p =
      structuredRawTailInsertionJoinerInitialConfig p
  runFuelEq :
    structuredLiveTailJoinerAssemblyRunFuel p =
      Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.runFuel
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p)
  runConfigEq :
    forall D : Structured.Description,
      structuredLiveTailJoinerAssemblyRunConfig D p =
        structuredRawTailInsertionJoinerAssemblyRunConfig D p
  sourceTapeEq :
    structuredLiveTailJoinerAssemblySourceTape p =
      mixedOptionCellQuoteLiveTailSeparatedTape
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p)
  targetTapeEq :
    structuredLiveTailJoinerAssemblyTargetTape p =
      mixedOptionCellQuoteLiveTailJoinedTape
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p)
  sourceTapeEqFamily :
    structuredLiveTailJoinerAssemblySourceTape p =
      mixedOptionCellQuoteLiveTailJoinerFamilySourceTape
        assemblySourceRestLiveTailEmitterEmittedPrefix
        assemblySourceRestLiveTailEmitterRawTail
        assemblySourceRestLiveTailEmitterQuoteRest
        p
  targetTapeEqFamily :
    structuredLiveTailJoinerAssemblyTargetTape p =
      mixedOptionCellQuoteLiveTailJoinerFamilyTargetTape
        assemblySourceRestLiveTailEmitterEmittedPrefix
        assemblySourceRestLiveTailEmitterRawTail
        assemblySourceRestLiveTailEmitterQuoteRest
        p
  sourceOutputEqFamily :
    structuredLiveTailJoinerAssemblySourceOutput p =
      mixedOptionCellQuoteLiveTailJoinerFamilySourceOutput
        assemblySourceRestLiveTailEmitterEmittedPrefix
        assemblySourceRestLiveTailEmitterRawTail
        assemblySourceRestLiveTailEmitterQuoteRest
        p
  targetOutputEqFamily :
    structuredLiveTailJoinerAssemblyTargetOutput p =
      mixedOptionCellQuoteLiveTailJoinerFamilyTargetOutput
        assemblySourceRestLiveTailEmitterEmittedPrefix
        assemblySourceRestLiveTailEmitterRawTail
        assemblySourceRestLiveTailEmitterQuoteRest
        p
  sourceTapeEqAfterRawTailScan :
    structuredLiveTailJoinerAssemblySourceTape p =
      MixedParserStackWholeSourceAfterRawTailScanTape
        p.w p.sourceRestBits p.stage
  targetTapeEqFinishTarget :
    structuredLiveTailJoinerAssemblyTargetTape p =
      assemblySourceRestFinishTargetTape
        p.w p.sourceRestBits p.stage
  sourceTapeNormalizedOutput :
    Tape.normalizedOutput
        (structuredLiveTailJoinerAssemblySourceTape p) =
      structuredLiveTailJoinerAssemblySourceOutput p
  targetTapeNormalizedOutput :
    Tape.normalizedOutput
        (structuredLiveTailJoinerAssemblyTargetTape p) =
      structuredLiveTailJoinerAssemblyTargetOutput p
  sourceOutputEqSeparated :
    structuredLiveTailJoinerAssemblySourceOutput p =
      assemblySourceRestFinishSeparatedOutput
        p.w p.sourceRestBits p.stage
  targetOutputEqJoined :
    structuredLiveTailJoinerAssemblyTargetOutput p =
      assemblySourceRestFinishJoinedOutput
        p.w p.sourceRestBits p.stage
  targetOutputEqFinishTargetOutput :
    structuredLiveTailJoinerAssemblyTargetOutput p =
      Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape
          p.w p.sourceRestBits p.stage)
  targetTapeNormalizedOutputEqFinishTarget :
    Tape.normalizedOutput
        (structuredLiveTailJoinerAssemblyTargetTape p) =
      Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape
          p.w p.sourceRestBits p.stage)
  sourceOutputEqSegments :
    structuredLiveTailJoinerAssemblySourceOutput p =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (List.append
          (assemblySourceRestLiveTailEmitterRawTail p)
          (assemblySourceRestLiveTailEmitterQuoteRest p))
  targetOutputEqSegments :
    structuredLiveTailJoinerAssemblyTargetOutput p =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (List.append
          (assemblySourceRestLiveTailEmitterQuoteRest p)
          (assemblySourceRestLiveTailEmitterRawTail p))
  targetOutputEqNamed :
    structuredLiveTailJoinerAssemblyTargetOutput p =
      List.append
        (assemblySourceRestFinishTargetPrefixBits
          p.w p.sourceRestBits p.stage)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            p.stage)
          p.sourceRestBits)
  sourceTapeNormalizedOutputEqAfterRawTailScan :
    Tape.normalizedOutput
        (structuredLiveTailJoinerAssemblySourceTape p) =
      Tape.normalizedOutput
        (MixedParserStackWholeSourceAfterRawTailScanTape
          p.w p.sourceRestBits p.stage)
  targetTapeNormalizedOutputEqTargetTape :
    Tape.normalizedOutput
        (structuredLiveTailJoinerAssemblyTargetTape p) =
      Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape
          p.w p.sourceRestBits p.stage)
  separatedTapeNormalizedOutput :
    Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailSeparatedTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            p.w p.sourceRestBits p.stage)
          (assemblySourceRestFinishRawTailBits p.sourceRestBits p.stage)
          (preservingCellPassCellBits p.sourceRestBits)) =
      assemblySourceRestFinishSeparatedOutput
        p.w p.sourceRestBits p.stage
  joinedTapeNormalizedOutput :
    Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailJoinedTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            p.w p.sourceRestBits p.stage)
          (assemblySourceRestFinishRawTailBits p.sourceRestBits p.stage)
          (preservingCellPassCellBits p.sourceRestBits)) =
      assemblySourceRestFinishJoinedOutput
        p.w p.sourceRestBits p.stage

theorem liveTailJoinerAssemblyShape
    (p : AssemblySourceRestLiveTailEmitterParam) :
    LiveTailJoinerAssemblyShape p :=
  { initialConfigEq :=
      structuredLiveTailJoinerAssemblyInitialConfig_eq p
    runFuelEq :=
      structuredLiveTailJoinerAssemblyRunFuel_eq p
    runConfigEq :=
      fun D => structuredLiveTailJoinerAssemblyRunConfig_eq D p
    sourceTapeEq :=
      structuredLiveTailJoinerAssemblySourceTape_eq p
    targetTapeEq :=
      structuredLiveTailJoinerAssemblyTargetTape_eq p
    sourceTapeEqFamily :=
      structuredLiveTailJoinerAssemblySourceTape_eq_joinerFamily p
    targetTapeEqFamily :=
      structuredLiveTailJoinerAssemblyTargetTape_eq_joinerFamily p
    sourceOutputEqFamily :=
      structuredLiveTailJoinerAssemblySourceOutput_eq_joinerFamily p
    targetOutputEqFamily :=
      structuredLiveTailJoinerAssemblyTargetOutput_eq_joinerFamily p
    sourceTapeEqAfterRawTailScan :=
      structuredLiveTailJoinerAssemblySourceTape_eq_afterRawTailScan p
    targetTapeEqFinishTarget :=
      structuredLiveTailJoinerAssemblyTargetTape_eq_finishTarget p
    sourceTapeNormalizedOutput :=
      structuredLiveTailJoinerAssemblySourceTape_normalizedOutput p
    targetTapeNormalizedOutput :=
      structuredLiveTailJoinerAssemblyTargetTape_normalizedOutput p
    sourceOutputEqSeparated :=
      structuredLiveTailJoinerAssemblySourceOutput_eq_separated p
    targetOutputEqJoined :=
      structuredLiveTailJoinerAssemblyTargetOutput_eq_joined p
    targetOutputEqFinishTargetOutput :=
      structuredLiveTailJoinerAssemblyTargetOutput_eq_finishTargetOutput p
    targetTapeNormalizedOutputEqFinishTarget :=
      structuredLiveTailJoinerAssemblyTargetTape_normalizedOutput_eq_finishTarget
        p
    sourceOutputEqSegments :=
      structuredLiveTailJoinerAssemblySourceOutput_eq_segments p
    targetOutputEqSegments :=
      structuredLiveTailJoinerAssemblyTargetOutput_eq_segments p
    targetOutputEqNamed :=
      structuredLiveTailJoinerAssemblyTargetOutput_eq_named p
    sourceTapeNormalizedOutputEqAfterRawTailScan :=
      structuredLiveTailJoinerAssemblySourceTape_normalizedOutput_eq_afterRawTailScan
        p
    targetTapeNormalizedOutputEqTargetTape :=
      structuredLiveTailJoinerAssemblyTargetTape_normalizedOutput_eq_targetTape
        p
    separatedTapeNormalizedOutput :=
      mixedOptionCellQuoteLiveTailSeparatedTape_normalizedOutput_assembly
        p.w p.sourceRestBits p.stage
    joinedTapeNormalizedOutput :=
      mixedOptionCellQuoteLiveTailJoinedTape_normalizedOutput_assembly
        p.w p.sourceRestBits p.stage }

/-!
## Exact and output joiner routes
-/

structure ExactLiveTailJoinerRouteSpec
    (finish : MachineDescription) : Prop where
  family :
    MixedOptionCellQuoteLiveTailJoinerAssemblyFamilySpec finish
  assembly :
    MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestSpec finish
  familyOutput :
    MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputSpec finish
  assemblyOutput :
    MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestOutputSpec finish
  structuredOutput :
    StructuredLiveTailJoinerAssemblyOutputSpec
      structuredRawTailInsertionJoinerDescription
  structuredTapeStateOutput :
    StructuredLiveTailJoinerAssemblyTapeStateOutputSpec
      structuredRawTailInsertionJoinerDescription
  ordinaryOutputBridge :
    StructuredLiveTailJoinerOrdinaryOutputBridgeSpec
      structuredRawTailInsertionJoinerDescription finish
  shape :
    forall p : AssemblySourceRestLiveTailEmitterParam,
      LiveTailJoinerAssemblyShape p

def ExactLiveTailJoinerRouteConstruction : Prop :=
  exists finish : MachineDescription,
    ExactLiveTailJoinerRouteSpec finish

theorem exactLiveTailJoinerRouteSpec_of_familySpec
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailJoinerAssemblyFamilySpec finish) :
    ExactLiveTailJoinerRouteSpec finish := by
  have hassembly :
      MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestSpec finish :=
    (MixedOptionCellQuoteLiveTailJoinerAssemblyFamilySpec_iff_assemblySpec
      finish).mp hfinish
  have hfamilyOutput :
      MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputSpec finish :=
    MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputSpec_of_exact
      hfinish
  have hassemblyOutput :
      MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestOutputSpec
        finish :=
    (MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputSpec_iff_assemblyOutputSpec
      finish).mp hfamilyOutput
  have hstructured :
      StructuredLiveTailJoinerAssemblyOutputSpec
        structuredRawTailInsertionJoinerDescription :=
    structuredRawTailInsertionJoinerDescription_structuredAssemblyOutputSpec
  have htapeState :
      StructuredLiveTailJoinerAssemblyTapeStateOutputSpec
        structuredRawTailInsertionJoinerDescription :=
    structuredRawTailInsertionJoinerDescription_structuredAssemblyTapeStateOutputSpec
  have hbridge :
      StructuredLiveTailJoinerOrdinaryOutputBridgeSpec
        structuredRawTailInsertionJoinerDescription finish :=
    StructuredLiveTailJoinerOrdinaryOutputBridgeSpec_of_outputFamily
      hstructured hfamilyOutput
  exact
    { family := hfinish
      assembly := hassembly
      familyOutput := hfamilyOutput
      assemblyOutput := hassemblyOutput
      structuredOutput := hstructured
      structuredTapeStateOutput := htapeState
      ordinaryOutputBridge := hbridge
      shape := liveTailJoinerAssemblyShape }

theorem exactLiveTailJoinerRouteSpec_of_assemblySpec
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestSpec finish) :
    ExactLiveTailJoinerRouteSpec finish :=
  exactLiveTailJoinerRouteSpec_of_familySpec
    ((MixedOptionCellQuoteLiveTailJoinerAssemblyFamilySpec_iff_assemblySpec
      finish).mpr hfinish)

theorem exactLiveTailJoinerRouteConstruction_of_family
    (hfinish :
      MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyConstruction) :
    ExactLiveTailJoinerRouteConstruction := by
  rcases hfinish with ⟨finish, hspec⟩
  exact
    ⟨finish,
      exactLiveTailJoinerRouteSpec_of_familySpec hspec⟩

theorem familyConstruction_of_exactLiveTailJoinerRouteConstruction
    (hroute : ExactLiveTailJoinerRouteConstruction) :
    MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyConstruction := by
  rcases hroute with ⟨finish, hspec⟩
  exact ⟨finish, hspec.family⟩

theorem exactLiveTailJoinerRouteConstruction_iff_familyConstruction :
    ExactLiveTailJoinerRouteConstruction ↔
      MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyConstruction := by
  constructor
  · exact familyConstruction_of_exactLiveTailJoinerRouteConstruction
  · exact exactLiveTailJoinerRouteConstruction_of_family

theorem exactLiveTailJoinerRouteConstruction_of_assembly
    (hfinish :
      MixedOptionCellQuoteLiveTailJoinerConstructionForAssemblySourceRest) :
    ExactLiveTailJoinerRouteConstruction := by
  rcases hfinish with ⟨finish, hspec⟩
  exact
    ⟨finish,
      exactLiveTailJoinerRouteSpec_of_assemblySpec hspec⟩

theorem assemblyConstruction_of_exactLiveTailJoinerRouteConstruction
    (hroute : ExactLiveTailJoinerRouteConstruction) :
    MixedOptionCellQuoteLiveTailJoinerConstructionForAssemblySourceRest := by
  rcases hroute with ⟨finish, hspec⟩
  exact ⟨finish, hspec.assembly⟩

theorem exactLiveTailJoinerRouteConstruction_iff_assemblyConstruction :
    ExactLiveTailJoinerRouteConstruction ↔
      MixedOptionCellQuoteLiveTailJoinerConstructionForAssemblySourceRest := by
  constructor
  · exact assemblyConstruction_of_exactLiveTailJoinerRouteConstruction
  · exact exactLiveTailJoinerRouteConstruction_of_assembly

theorem exactLiveTailJoinerRouteConstruction_core :
    ExactLiveTailJoinerRouteConstruction :=
  exactLiveTailJoinerRouteConstruction_of_family
    mixedOptionCellQuoteLiveTailJoinerAssemblyFamilyConstruction

structure OutputLiveTailJoinerRouteSpec
    (finish : MachineDescription) : Prop where
  familyOutput :
    MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputSpec finish
  assemblyOutput :
    MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestOutputSpec finish
  structuredOutput :
    StructuredLiveTailJoinerAssemblyOutputSpec
      structuredRawTailInsertionJoinerDescription
  structuredTapeStateOutput :
    StructuredLiveTailJoinerAssemblyTapeStateOutputSpec
      structuredRawTailInsertionJoinerDescription
  ordinaryOutputBridge :
    StructuredLiveTailJoinerOrdinaryOutputBridgeSpec
      structuredRawTailInsertionJoinerDescription finish
  shape :
    forall p : AssemblySourceRestLiveTailEmitterParam,
      LiveTailJoinerAssemblyShape p

def OutputLiveTailJoinerRouteConstruction : Prop :=
  exists finish : MachineDescription,
    OutputLiveTailJoinerRouteSpec finish

theorem outputLiveTailJoinerRouteSpec_of_familyOutputSpec
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputSpec finish) :
    OutputLiveTailJoinerRouteSpec finish := by
  have hassemblyOutput :
      MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestOutputSpec
        finish :=
    (MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputSpec_iff_assemblyOutputSpec
      finish).mp hfinish
  have hstructured :
      StructuredLiveTailJoinerAssemblyOutputSpec
        structuredRawTailInsertionJoinerDescription :=
    structuredRawTailInsertionJoinerDescription_structuredAssemblyOutputSpec
  have htapeState :
      StructuredLiveTailJoinerAssemblyTapeStateOutputSpec
        structuredRawTailInsertionJoinerDescription :=
    structuredRawTailInsertionJoinerDescription_structuredAssemblyTapeStateOutputSpec
  have hbridge :
      StructuredLiveTailJoinerOrdinaryOutputBridgeSpec
        structuredRawTailInsertionJoinerDescription finish :=
    StructuredLiveTailJoinerOrdinaryOutputBridgeSpec_of_outputFamily
      hstructured hfinish
  exact
    { familyOutput := hfinish
      assemblyOutput := hassemblyOutput
      structuredOutput := hstructured
      structuredTapeStateOutput := htapeState
      ordinaryOutputBridge := hbridge
      shape := liveTailJoinerAssemblyShape }

theorem outputLiveTailJoinerRouteSpec_of_assemblyOutputSpec
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestOutputSpec
        finish) :
    OutputLiveTailJoinerRouteSpec finish :=
  outputLiveTailJoinerRouteSpec_of_familyOutputSpec
    ((MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputSpec_iff_assemblyOutputSpec
      finish).mpr hfinish)

theorem outputLiveTailJoinerRouteSpec_of_exactRouteSpec
    {finish : MachineDescription}
    (hroute : ExactLiveTailJoinerRouteSpec finish) :
    OutputLiveTailJoinerRouteSpec finish :=
  { familyOutput := hroute.familyOutput
    assemblyOutput := hroute.assemblyOutput
    structuredOutput := hroute.structuredOutput
    structuredTapeStateOutput := hroute.structuredTapeStateOutput
    ordinaryOutputBridge := hroute.ordinaryOutputBridge
    shape := hroute.shape }

theorem outputLiveTailJoinerRouteConstruction_of_familyOutput
    (hfinish :
      MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputConstruction) :
    OutputLiveTailJoinerRouteConstruction := by
  rcases hfinish with ⟨finish, hspec⟩
  exact
    ⟨finish,
      outputLiveTailJoinerRouteSpec_of_familyOutputSpec hspec⟩

theorem familyOutputConstruction_of_outputLiveTailJoinerRouteConstruction
    (hroute : OutputLiveTailJoinerRouteConstruction) :
    MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputConstruction := by
  rcases hroute with ⟨finish, hspec⟩
  exact ⟨finish, hspec.familyOutput⟩

theorem outputLiveTailJoinerRouteConstruction_iff_familyOutputConstruction :
    OutputLiveTailJoinerRouteConstruction ↔
      MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputConstruction := by
  constructor
  · exact familyOutputConstruction_of_outputLiveTailJoinerRouteConstruction
  · exact outputLiveTailJoinerRouteConstruction_of_familyOutput

theorem outputLiveTailJoinerRouteConstruction_of_exactRoute
    (hroute : ExactLiveTailJoinerRouteConstruction) :
    OutputLiveTailJoinerRouteConstruction := by
  rcases hroute with ⟨finish, hspec⟩
  exact
    ⟨finish,
      outputLiveTailJoinerRouteSpec_of_exactRouteSpec hspec⟩

theorem outputLiveTailJoinerRouteConstruction_core :
    OutputLiveTailJoinerRouteConstruction :=
  outputLiveTailJoinerRouteConstruction_of_exactRoute
    exactLiveTailJoinerRouteConstruction_core

/-!
## Structured ordinary-output route
-/

structure StructuredLiveTailJoinerOutputRouteSpec
    (structured : Structured.Description)
    (finish : MachineDescription) : Prop where
  structuredOutput :
    StructuredLiveTailJoinerAssemblyOutputSpec structured
  structuredTapeStateOutput :
    StructuredLiveTailJoinerAssemblyTapeStateOutputSpec structured
  ordinaryOutputBridge :
    StructuredLiveTailJoinerOrdinaryOutputBridgeSpec
      structured finish
  familyOutput :
    StructuredLiveTailJoinerAssemblyFamilyOutputSpec finish
  assemblyOutput :
    MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestOutputSpec
      finish
  shape :
    forall p : AssemblySourceRestLiveTailEmitterParam,
      LiveTailJoinerAssemblyShape p

def StructuredLiveTailJoinerOutputRouteConstruction
    (structured : Structured.Description) : Prop :=
  exists finish : MachineDescription,
    StructuredLiveTailJoinerOutputRouteSpec structured finish

theorem structuredLiveTailJoinerOutputRouteSpec_of_ordinaryBridge
    {structured : Structured.Description}
    {finish : MachineDescription}
    (htapeState :
      StructuredLiveTailJoinerAssemblyTapeStateOutputSpec structured)
    (hbridge :
      StructuredLiveTailJoinerOrdinaryOutputBridgeSpec
        structured finish) :
    StructuredLiveTailJoinerOutputRouteSpec structured finish :=
  { structuredOutput := hbridge.structured
    structuredTapeStateOutput := htapeState
    ordinaryOutputBridge := hbridge
    familyOutput := hbridge.ordinary
    assemblyOutput :=
      (StructuredLiveTailJoinerAssemblyFamilyOutputSpec_iff_assemblyOutputSpec
        finish).mp hbridge.ordinary
    shape := liveTailJoinerAssemblyShape }

theorem structuredLiveTailJoinerOutputRouteSpec_of_outputRoute
    {finish : MachineDescription}
    (hroute : OutputLiveTailJoinerRouteSpec finish) :
    StructuredLiveTailJoinerOutputRouteSpec
      structuredRawTailInsertionJoinerDescription finish :=
  { structuredOutput := hroute.structuredOutput
    structuredTapeStateOutput := hroute.structuredTapeStateOutput
    ordinaryOutputBridge := hroute.ordinaryOutputBridge
    familyOutput := hroute.familyOutput
    assemblyOutput := hroute.assemblyOutput
    shape := hroute.shape }

theorem structuredLiveTailJoinerOutputRouteConstruction_of_outputRoute
    (hroute : OutputLiveTailJoinerRouteConstruction) :
    StructuredLiveTailJoinerOutputRouteConstruction
      structuredRawTailInsertionJoinerDescription := by
  rcases hroute with ⟨finish, hspec⟩
  exact
    ⟨finish,
      structuredLiveTailJoinerOutputRouteSpec_of_outputRoute hspec⟩

theorem structuredLiveTailJoinerOutputRouteConstruction_core :
    StructuredLiveTailJoinerOutputRouteConstruction
      structuredRawTailInsertionJoinerDescription :=
  structuredLiveTailJoinerOutputRouteConstruction_of_outputRoute
    outputLiveTailJoinerRouteConstruction_core

theorem outputLiveTailJoinerRouteConstruction_of_structuredRoute
    (hroute :
      StructuredLiveTailJoinerOutputRouteConstruction
        structuredRawTailInsertionJoinerDescription) :
    OutputLiveTailJoinerRouteConstruction := by
  rcases hroute with ⟨finish, hspec⟩
  exact
    ⟨finish,
      outputLiveTailJoinerRouteSpec_of_assemblyOutputSpec
        hspec.assemblyOutput⟩

theorem assemblyOutputConstruction_of_structuredLiveTailJoinerRoute
    {structured : Structured.Description}
    (hroute :
      StructuredLiveTailJoinerOutputRouteConstruction structured) :
    MixedOptionCellQuoteLiveTailJoinerOutputConstructionForAssemblySourceRest := by
  rcases hroute with ⟨finish, hspec⟩
  exact ⟨finish, hspec.assemblyOutput⟩

/-!
## Parser-stack after-raw-tail-scan route
-/

structure AfterRawTailScanJoinFinisherRouteSpec
    (finish : MachineDescription) : Prop where
  joinerExact :
    MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestSpec finish
  finisherExact :
    MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestSpec
      finish
  joinerOutput :
    MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestOutputSpec
      finish
  finisherOutput :
    MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestOutputSpec
      finish
  outputRoute :
    OutputLiveTailJoinerRouteSpec finish
  shape :
    forall p : AssemblySourceRestLiveTailEmitterParam,
      LiveTailJoinerAssemblyShape p

def AfterRawTailScanJoinFinisherRouteConstruction : Prop :=
  exists finish : MachineDescription,
    AfterRawTailScanJoinFinisherRouteSpec finish

theorem afterRawTailScanJoinFinisherRouteSpec_of_exactRoute
    {finish : MachineDescription}
    (hroute : ExactLiveTailJoinerRouteSpec finish) :
    AfterRawTailScanJoinFinisherRouteSpec finish := by
  have hfinisherExact :
      MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestSpec
        finish := by
    refine ⟨hroute.assembly.left, ?_⟩
    intro w sourceRestBits stage
    rw [
      MixedParserStackWholeSourceAfterRawTailScanTape_eq_mixedOptionCellQuoteLiveTailSeparatedTape]
    rw [MixedParserStackRewriterWholeSourceTargetTape_eq_quoteRestJoinedTape]
    rw [← mixedOptionCellQuoteLiveTailJoinedTape_eq_assemblyQuoteRestJoinedTape]
    exact hroute.assembly.right w sourceRestBits stage
  have hfinisherOutput :
      MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestOutputSpec
        finish := by
    refine ⟨hroute.assemblyOutput.left, ?_⟩
    intro w sourceRestBits stage
    rw [
      MixedParserStackWholeSourceAfterRawTailScanTape_eq_mixedOptionCellQuoteLiveTailSeparatedTape]
    rw [MixedParserStackRewriterWholeSourceTargetTape_eq_quoteRestJoinedTape]
    rw [← mixedOptionCellQuoteLiveTailJoinedTape_eq_assemblyQuoteRestJoinedTape]
    exact hroute.assemblyOutput.right w sourceRestBits stage
  exact
    { joinerExact := hroute.assembly
      finisherExact := hfinisherExact
      joinerOutput := hroute.assemblyOutput
      finisherOutput := hfinisherOutput
      outputRoute := outputLiveTailJoinerRouteSpec_of_exactRouteSpec hroute
      shape := hroute.shape }

theorem afterRawTailScanJoinFinisherRouteConstruction_of_exactRoute
    (hroute : ExactLiveTailJoinerRouteConstruction) :
    AfterRawTailScanJoinFinisherRouteConstruction := by
  rcases hroute with ⟨finish, hspec⟩
  exact
    ⟨finish,
      afterRawTailScanJoinFinisherRouteSpec_of_exactRoute hspec⟩

theorem exactLiveTailJoinerRouteConstruction_of_afterRawTailScanRoute
    (hroute : AfterRawTailScanJoinFinisherRouteConstruction) :
    ExactLiveTailJoinerRouteConstruction := by
  rcases hroute with ⟨finish, hspec⟩
  exact
    ⟨finish,
      exactLiveTailJoinerRouteSpec_of_assemblySpec hspec.joinerExact⟩

theorem afterRawTailScanJoinFinisherRouteConstruction_iff_exactRoute :
    AfterRawTailScanJoinFinisherRouteConstruction ↔
      ExactLiveTailJoinerRouteConstruction := by
  constructor
  · exact exactLiveTailJoinerRouteConstruction_of_afterRawTailScanRoute
  · exact afterRawTailScanJoinFinisherRouteConstruction_of_exactRoute

theorem afterRawTailScanJoinFinisherRouteConstruction_core :
    AfterRawTailScanJoinFinisherRouteConstruction :=
  afterRawTailScanJoinFinisherRouteConstruction_of_exactRoute
    exactLiveTailJoinerRouteConstruction_core

theorem mixedParserStackAfterRawTailScanJoinFinisherConstruction_from_route
    (hroute : AfterRawTailScanJoinFinisherRouteConstruction) :
    MixedParserStackAfterRawTailScanJoinFinisherConstructionForAssemblySourceRest := by
  rcases hroute with ⟨finish, hspec⟩
  exact ⟨finish, hspec.finisherExact⟩

theorem mixedParserStackAfterRawTailScanJoinFinisherOutputConstruction_from_route
    (hroute : AfterRawTailScanJoinFinisherRouteConstruction) :
    MixedParserStackAfterRawTailScanJoinFinisherOutputConstructionForAssemblySourceRest := by
  rcases hroute with ⟨finish, hspec⟩
  exact ⟨finish, hspec.finisherOutput⟩

/-!
## Field projections
-/

theorem liveTailJoinerAssemblyShape_of_exactRoute
    (hroute : ExactLiveTailJoinerRouteConstruction)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    LiveTailJoinerAssemblyShape p := by
  rcases hroute with ⟨_finish, hspec⟩
  exact hspec.shape p

theorem liveTailJoinerAssemblyShape_of_outputRoute
    (hroute : OutputLiveTailJoinerRouteConstruction)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    LiveTailJoinerAssemblyShape p := by
  rcases hroute with ⟨_finish, hspec⟩
  exact hspec.shape p

theorem liveTailJoinerAssemblyShape_of_structuredRoute
    {structured : Structured.Description}
    (hroute : StructuredLiveTailJoinerOutputRouteConstruction structured)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    LiveTailJoinerAssemblyShape p := by
  rcases hroute with ⟨_finish, hspec⟩
  exact hspec.shape p

theorem liveTailJoinerAssemblyShape_of_afterRawTailScanRoute
    (hroute : AfterRawTailScanJoinFinisherRouteConstruction)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    LiveTailJoinerAssemblyShape p := by
  rcases hroute with ⟨_finish, hspec⟩
  exact hspec.shape p

theorem liveTailJoinerAssemblyTargetTape_normalizedOutput_core
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (structuredLiveTailJoinerAssemblyTargetTape p) =
      Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape
          p.w p.sourceRestBits p.stage) :=
  (liveTailJoinerAssemblyShape_of_exactRoute
    exactLiveTailJoinerRouteConstruction_core p)
      |>.targetTapeNormalizedOutputEqTargetTape

theorem liveTailJoinerAssemblyTargetOutput_eq_named_core
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblyTargetOutput p =
      List.append
        (assemblySourceRestFinishTargetPrefixBits
          p.w p.sourceRestBits p.stage)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            p.stage)
          p.sourceRestBits) :=
  (liveTailJoinerAssemblyShape_of_exactRoute
    exactLiveTailJoinerRouteConstruction_core p)
      |>.targetOutputEqNamed

theorem liveTailJoinerAssemblySourceTape_eq_afterRawTailScan_core
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblySourceTape p =
      MixedParserStackWholeSourceAfterRawTailScanTape
        p.w p.sourceRestBits p.stage :=
  (liveTailJoinerAssemblyShape_of_exactRoute
    exactLiveTailJoinerRouteConstruction_core p)
      |>.sourceTapeEqAfterRawTailScan

theorem liveTailJoinerAssemblyTargetOutput_eq_segments_core
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblyTargetOutput p =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (List.append
          (assemblySourceRestLiveTailEmitterQuoteRest p)
          (assemblySourceRestLiveTailEmitterRawTail p)) :=
  (liveTailJoinerAssemblyShape_of_exactRoute
    exactLiveTailJoinerRouteConstruction_core p)
      |>.targetOutputEqSegments

theorem liveTailJoinerAssemblySeparatedTape_normalizedOutput_core
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailSeparatedTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            p.w p.sourceRestBits p.stage)
          (assemblySourceRestFinishRawTailBits p.sourceRestBits p.stage)
          (preservingCellPassCellBits p.sourceRestBits)) =
      assemblySourceRestFinishSeparatedOutput
        p.w p.sourceRestBits p.stage :=
  (liveTailJoinerAssemblyShape_of_exactRoute
    exactLiveTailJoinerRouteConstruction_core p)
      |>.separatedTapeNormalizedOutput

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
