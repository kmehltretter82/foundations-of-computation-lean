import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTEmitterConstruction
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTEndpointContracts

set_option doc.verso true

/-!
# Live-tail emitter route contracts

This module packages the assembly-specific live-tail emitter construction
surface.  The finite-machine leaf remains in
{module}`FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTEmitterConstruction`,
but the exact/output route and structured-endpoint output route now expose the
same assembly source, target, and normalized-output shape.
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

structure LiveTailEmitterAssemblyShape
    (p : AssemblySourceRestLiveTailEmitterParam) : Prop where
  inputBitsEq :
    structuredLiveTailEmitterAssemblyInputBits p =
      assemblySourceRestFinishSourceBits
        p.w p.sourceRestBits p.stage
  outputPrefixEq :
    structuredLiveTailEmitterAssemblyOutputPrefix p =
      assemblySourceRestFinishTargetPrefixBits
        p.w p.sourceRestBits p.stage
  outputPrefixEqEmittedQuoteRest :
    structuredLiveTailEmitterAssemblyOutputPrefix p =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterQuoteRest p)
  outputBitsEqAppendPrefix :
    forall outputBits : Word Bool,
      structuredLiveTailEmitterAssemblyOutputBits p outputBits =
        List.append outputBits
          (structuredLiveTailEmitterAssemblyOutputPrefix p)
  outputBitsEqAppendEmittedQuoteRest :
    forall outputBits : Word Bool,
      structuredLiveTailEmitterAssemblyOutputBits p outputBits =
        List.append outputBits
          (List.append
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterQuoteRest p))
  outputBitsEqOutputEmittedQuoteRest :
    forall outputBits : Word Bool,
      structuredLiveTailEmitterAssemblyOutputBits p outputBits =
        List.append
          (List.append outputBits
            (assemblySourceRestLiveTailEmitterEmittedPrefix p))
          (assemblySourceRestLiveTailEmitterQuoteRest p)
  initialConfigEq :
    forall outputBits : Word Bool,
      structuredLiveTailEmitterAssemblyInitialConfig p outputBits =
        structuredMixedOptionCellQuoteLiveTailCountConfig
          0 []
          (assemblySourceRestFinishSourceBits
            p.w p.sourceRestBits p.stage)
          0 outputBits
  runStepsEq :
    structuredLiveTailEmitterAssemblyRunSteps p =
      structuredMixedOptionCellQuoteLiveTailEmitterFullSourceSteps
        (assemblySourceRestFinishSourceBits
          p.w p.sourceRestBits p.stage)
  finalConfigEq :
    forall outputBits : Word Bool,
      structuredLiveTailEmitterAssemblyFinalConfig p outputBits =
        structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
          499
          (assemblySourceRestFinishSourceBits
            p.w p.sourceRestBits p.stage).reverse
          []
          (assemblySourceRestFinishSourceBits
            p.w p.sourceRestBits p.stage).length
          (List.append outputBits
            (assemblySourceRestFinishTargetPrefixBits
              p.w p.sourceRestBits p.stage))
  finalConfigEqEmittedQuoteRest :
    forall outputBits : Word Bool,
      structuredLiveTailEmitterAssemblyFinalConfig p outputBits =
        structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
          499
          (assemblySourceRestFinishSourceBits
            p.w p.sourceRestBits p.stage).reverse
          []
          (assemblySourceRestFinishSourceBits
            p.w p.sourceRestBits p.stage).length
          (List.append outputBits
            (List.append
              (assemblySourceRestLiveTailEmitterEmittedPrefix p)
              (assemblySourceRestLiveTailEmitterQuoteRest p)))
  sourceTapeEqFamily :
    structuredLiveTailEmitterAssemblySourceTape p =
      mixedOptionCellQuoteLiveTailEmitterFamilySourceTape
        assemblySourceRestLiveTailEmitterLeftRev
        assemblySourceRestLiveTailEmitterQuoteScan
        assemblySourceRestLiveTailEmitterRawTail
        assemblySourceRestLiveTailEmitterQuoteRest
        p
  targetTapeEqFamily :
    structuredLiveTailEmitterAssemblyTargetTape p =
      mixedOptionCellQuoteLiveTailEmitterFamilyTargetTape
        assemblySourceRestLiveTailEmitterRawTail
        assemblySourceRestLiveTailEmitterQuoteRest
        assemblySourceRestLiveTailEmitterEmittedPrefix
        p
  sourceOutputEqFamily :
    structuredLiveTailEmitterAssemblySourceOutput p =
      mixedOptionCellQuoteLiveTailEmitterFamilySourceOutput
        assemblySourceRestLiveTailEmitterLeftRev
        assemblySourceRestLiveTailEmitterQuoteScan
        assemblySourceRestLiveTailEmitterRawTail
        assemblySourceRestLiveTailEmitterQuoteRest
        p
  targetOutputEqFamily :
    structuredLiveTailEmitterAssemblyTargetOutput p =
      mixedOptionCellQuoteLiveTailEmitterFamilyTargetOutput
        assemblySourceRestLiveTailEmitterRawTail
        assemblySourceRestLiveTailEmitterQuoteRest
        assemblySourceRestLiveTailEmitterEmittedPrefix
        p
  sourceTapeNormalizedOutput :
    Tape.normalizedOutput
        (structuredLiveTailEmitterAssemblySourceTape p) =
      structuredLiveTailEmitterAssemblySourceOutput p
  targetTapeNormalizedOutput :
    Tape.normalizedOutput
        (structuredLiveTailEmitterAssemblyTargetTape p) =
      structuredLiveTailEmitterAssemblyTargetOutput p
  targetOutputEqPrefixQuotedSeparated :
    structuredLiveTailEmitterAssemblyTargetOutput p =
      assemblySourceRestFinishPrefixQuotedSeparatedOutput
        p.w p.sourceRestBits p.stage
  targetTapeNormalizedOutputEqPrefixQuotedSeparated :
    Tape.normalizedOutput
        (structuredLiveTailEmitterAssemblyTargetTape p) =
      assemblySourceRestFinishPrefixQuotedSeparatedOutput
        p.w p.sourceRestBits p.stage
  leftRevDefaultBits :
    List.map optionBitDefaultFalse
        (List.reverse (assemblySourceRestLiveTailEmitterLeftRev p)) =
      List.append
        (false ::
          List.map optionBitDefaultFalse
            assemblySourceRestFinishParserMarkerLeftCells)
        [false]
  sourceBitsEqSegments :
    assemblySourceRestLiveTailEmitterSourceBits p =
      List.append
        (List.map optionBitDefaultFalse
          (List.reverse (assemblySourceRestLiveTailEmitterLeftRev p)))
        (List.append
          (assemblySourceRestLiveTailEmitterQuoteScan p)
          (List.append
            (assemblySourceRestLiveTailEmitterRawTail p)
            (false ::
              List.append
                (assemblySourceRestLiveTailEmitterQuoteRest p)
                [false])))
  targetBitsEqEmittedRawQuoteRest :
    assemblySourceRestLiveTailEmitterTargetBits p =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (List.append
          (assemblySourceRestLiveTailEmitterRawTail p)
          (false ::
            List.append
              (assemblySourceRestLiveTailEmitterQuoteRest p)
              [false]))
  targetPrefixBitsEqEmittedQuoteRest :
    assemblySourceRestFinishTargetPrefixBits
        p.w p.sourceRestBits p.stage =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterQuoteRest p)
  sourceBitsDefaultedCells :
    List.map optionBitDefaultFalse
        (Tape.cells
          (mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
            (assemblySourceRestLiveTailEmitterLeftRev p)
            (assemblySourceRestLiveTailEmitterQuoteScan p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p))) =
      assemblySourceRestLiveTailEmitterSourceBits p
  targetBitsDefaultedCells :
    List.map optionBitDefaultFalse
        (Tape.cells
          (mixedOptionCellQuoteLiveTailEmitterTargetTape
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p))) =
      assemblySourceRestLiveTailEmitterTargetBits p

theorem liveTailEmitterAssemblyShape
    (p : AssemblySourceRestLiveTailEmitterParam) :
    LiveTailEmitterAssemblyShape p :=
  { inputBitsEq := structuredLiveTailEmitterAssemblyInputBits_eq p
    outputPrefixEq := structuredLiveTailEmitterAssemblyOutputPrefix_eq p
    outputPrefixEqEmittedQuoteRest :=
      structuredLiveTailEmitterAssemblyOutputPrefix_eq_emitted_quoteRest p
    outputBitsEqAppendPrefix :=
      structuredLiveTailEmitterAssemblyOutputBits_eq_append_prefix p
    outputBitsEqAppendEmittedQuoteRest :=
      structuredLiveTailEmitterAssemblyOutputBits_eq_append_emitted_quoteRest
        p
    outputBitsEqOutputEmittedQuoteRest :=
      structuredLiveTailEmitterAssemblyOutputBits_eq_output_emitted_quoteRest
        p
    initialConfigEq := structuredLiveTailEmitterAssemblyInitialConfig_eq p
    runStepsEq := structuredLiveTailEmitterAssemblyRunSteps_eq p
    finalConfigEq := structuredLiveTailEmitterAssemblyFinalConfig_eq p
    finalConfigEqEmittedQuoteRest :=
      structuredLiveTailEmitterAssemblyFinalConfig_eq_emitted_quoteRest p
    sourceTapeEqFamily :=
      structuredLiveTailEmitterAssemblySourceTape_eq_family p
    targetTapeEqFamily :=
      structuredLiveTailEmitterAssemblyTargetTape_eq_family p
    sourceOutputEqFamily :=
      structuredLiveTailEmitterAssemblySourceOutput_eq_family p
    targetOutputEqFamily :=
      structuredLiveTailEmitterAssemblyTargetOutput_eq_family p
    sourceTapeNormalizedOutput :=
      structuredLiveTailEmitterAssemblySourceTape_normalizedOutput p
    targetTapeNormalizedOutput :=
      structuredLiveTailEmitterAssemblyTargetTape_normalizedOutput p
    targetOutputEqPrefixQuotedSeparated :=
      structuredLiveTailEmitterAssemblyTargetOutput_eq_prefixQuotedSeparated p
    targetTapeNormalizedOutputEqPrefixQuotedSeparated :=
      structuredLiveTailEmitterAssemblyTargetTape_normalizedOutput_eq_prefixQuotedSeparated
        p
    leftRevDefaultBits :=
      assemblySourceRestLiveTailEmitterLeftRev_defaultBits p
    sourceBitsEqSegments :=
      assemblySourceRestLiveTailEmitterSourceBits_eq_segments p
    targetBitsEqEmittedRawQuoteRest :=
      assemblySourceRestLiveTailEmitterTargetBits_eq_emitted_raw_quoteRest p
    targetPrefixBitsEqEmittedQuoteRest :=
      assemblySourceRestLiveTailEmitterTargetPrefixBits_eq_emitted_quoteRest p
    sourceBitsDefaultedCells :=
      assemblySourceRestLiveTailEmitterSourceBits_defaultedCells p
    targetBitsDefaultedCells :=
      assemblySourceRestLiveTailEmitterTargetBits_defaultedCells p }

/-!
## Exact and output emitter routes
-/

structure ExactLiveTailEmitterRouteSpec
    (finish : MachineDescription) : Prop where
  family :
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilySpec finish
  assembly :
    MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestSpec finish
  familyOutput :
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec finish
  assemblyOutput :
    MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestOutputSpec finish
  shape :
    forall p : AssemblySourceRestLiveTailEmitterParam,
      LiveTailEmitterAssemblyShape p

def ExactLiveTailEmitterRouteConstruction : Prop :=
  exists finish : MachineDescription,
    ExactLiveTailEmitterRouteSpec finish

theorem exactLiveTailEmitterRouteSpec_of_familySpec
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailEmitterAssemblyFamilySpec finish) :
    ExactLiveTailEmitterRouteSpec finish := by
  have hassembly :
      MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestSpec finish :=
    (MixedOptionCellQuoteLiveTailEmitterAssemblyFamilySpec_iff_assemblySpec
      finish).mp hfinish
  have hfamilyOutput :
      MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec finish :=
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec_of_exact
      hfinish
  have hassemblyOutput :
      MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestOutputSpec
        finish :=
    (MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec_iff_assemblyOutputSpec
      finish).mp hfamilyOutput
  exact
    { family := hfinish
      assembly := hassembly
      familyOutput := hfamilyOutput
      assemblyOutput := hassemblyOutput
      shape := liveTailEmitterAssemblyShape }

theorem exactLiveTailEmitterRouteSpec_of_assemblySpec
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestSpec finish) :
    ExactLiveTailEmitterRouteSpec finish :=
  exactLiveTailEmitterRouteSpec_of_familySpec
    ((MixedOptionCellQuoteLiveTailEmitterAssemblyFamilySpec_iff_assemblySpec
      finish).mpr hfinish)

theorem exactLiveTailEmitterRouteConstruction_of_family
    (hfinish :
      MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyConstruction) :
    ExactLiveTailEmitterRouteConstruction := by
  rcases hfinish with ⟨finish, hspec⟩
  exact
    ⟨finish,
      exactLiveTailEmitterRouteSpec_of_familySpec hspec⟩

theorem familyConstruction_of_exactLiveTailEmitterRouteConstruction
    (hroute : ExactLiveTailEmitterRouteConstruction) :
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyConstruction := by
  rcases hroute with ⟨finish, hspec⟩
  exact ⟨finish, hspec.family⟩

theorem exactLiveTailEmitterRouteConstruction_iff_familyConstruction :
    ExactLiveTailEmitterRouteConstruction ↔
      MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyConstruction := by
  constructor
  · exact familyConstruction_of_exactLiveTailEmitterRouteConstruction
  · exact exactLiveTailEmitterRouteConstruction_of_family

theorem exactLiveTailEmitterRouteConstruction_of_assembly
    (hfinish :
      MixedOptionCellQuoteLiveTailEmitterConstructionForAssemblySourceRest) :
    ExactLiveTailEmitterRouteConstruction := by
  rcases hfinish with ⟨finish, hspec⟩
  exact
    ⟨finish,
      exactLiveTailEmitterRouteSpec_of_assemblySpec hspec⟩

theorem assemblyConstruction_of_exactLiveTailEmitterRouteConstruction
    (hroute : ExactLiveTailEmitterRouteConstruction) :
    MixedOptionCellQuoteLiveTailEmitterConstructionForAssemblySourceRest := by
  rcases hroute with ⟨finish, hspec⟩
  exact ⟨finish, hspec.assembly⟩

theorem exactLiveTailEmitterRouteConstruction_iff_assemblyConstruction :
    ExactLiveTailEmitterRouteConstruction ↔
      MixedOptionCellQuoteLiveTailEmitterConstructionForAssemblySourceRest := by
  constructor
  · exact assemblyConstruction_of_exactLiveTailEmitterRouteConstruction
  · exact exactLiveTailEmitterRouteConstruction_of_assembly

theorem exactLiveTailEmitterRouteConstruction_core :
    ExactLiveTailEmitterRouteConstruction :=
  exactLiveTailEmitterRouteConstruction_of_family
    mixedOptionCellQuoteLiveTailEmitterAssemblyFamilyConstruction

structure OutputLiveTailEmitterRouteSpec
    (finish : MachineDescription) : Prop where
  familyOutput :
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec finish
  assemblyOutput :
    MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestOutputSpec finish
  shape :
    forall p : AssemblySourceRestLiveTailEmitterParam,
      LiveTailEmitterAssemblyShape p

def OutputLiveTailEmitterRouteConstruction : Prop :=
  exists finish : MachineDescription,
    OutputLiveTailEmitterRouteSpec finish

theorem outputLiveTailEmitterRouteSpec_of_familyOutputSpec
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec finish) :
    OutputLiveTailEmitterRouteSpec finish :=
  { familyOutput := hfinish
    assemblyOutput :=
      (MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec_iff_assemblyOutputSpec
        finish).mp hfinish
    shape := liveTailEmitterAssemblyShape }

theorem outputLiveTailEmitterRouteSpec_of_assemblyOutputSpec
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestOutputSpec
        finish) :
    OutputLiveTailEmitterRouteSpec finish :=
  outputLiveTailEmitterRouteSpec_of_familyOutputSpec
    ((MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec_iff_assemblyOutputSpec
      finish).mpr hfinish)

theorem outputLiveTailEmitterRouteSpec_of_exactRouteSpec
    {finish : MachineDescription}
    (hroute : ExactLiveTailEmitterRouteSpec finish) :
    OutputLiveTailEmitterRouteSpec finish :=
  { familyOutput := hroute.familyOutput
    assemblyOutput := hroute.assemblyOutput
    shape := hroute.shape }

theorem outputLiveTailEmitterRouteConstruction_of_familyOutput
    (hfinish :
      MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputConstruction) :
    OutputLiveTailEmitterRouteConstruction := by
  rcases hfinish with ⟨finish, hspec⟩
  exact
    ⟨finish,
      outputLiveTailEmitterRouteSpec_of_familyOutputSpec hspec⟩

theorem familyOutputConstruction_of_outputLiveTailEmitterRouteConstruction
    (hroute : OutputLiveTailEmitterRouteConstruction) :
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputConstruction := by
  rcases hroute with ⟨finish, hspec⟩
  exact ⟨finish, hspec.familyOutput⟩

theorem outputLiveTailEmitterRouteConstruction_iff_familyOutputConstruction :
    OutputLiveTailEmitterRouteConstruction ↔
      MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputConstruction := by
  constructor
  · exact familyOutputConstruction_of_outputLiveTailEmitterRouteConstruction
  · exact outputLiveTailEmitterRouteConstruction_of_familyOutput

theorem outputLiveTailEmitterRouteConstruction_of_exactRoute
    (hroute : ExactLiveTailEmitterRouteConstruction) :
    OutputLiveTailEmitterRouteConstruction := by
  rcases hroute with ⟨finish, hspec⟩
  exact
    ⟨finish,
      outputLiveTailEmitterRouteSpec_of_exactRouteSpec hspec⟩

theorem outputLiveTailEmitterRouteConstruction_core :
    OutputLiveTailEmitterRouteConstruction :=
  outputLiveTailEmitterRouteConstruction_of_exactRoute
    exactLiveTailEmitterRouteConstruction_core

/-!
## Structured endpoint output route
-/

structure StructuredEndpointLiveTailEmitterOutputRouteSpec
    (initializer projector finish : MachineDescription) : Prop where
  components :
    StructuredLiveTailEmitterEndpointComponentsSpec initializer projector
  bridge :
    StructuredLiveTailEmitterEndpointBridgeSpec finish
  familyOutput :
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec finish
  assemblyOutput :
    MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestOutputSpec finish
  shape :
    forall p : AssemblySourceRestLiveTailEmitterParam,
      LiveTailEmitterAssemblyShape p

def StructuredEndpointLiveTailEmitterOutputRouteConstruction : Prop :=
  exists initializer projector finish : MachineDescription,
    StructuredEndpointLiveTailEmitterOutputRouteSpec
      initializer projector finish

theorem structuredEndpointLiveTailEmitterOutputRouteSpec_of_components
    {initializer projector : MachineDescription}
    (hcomponents :
      StructuredLiveTailEmitterEndpointComponentsSpec initializer projector) :
    StructuredEndpointLiveTailEmitterOutputRouteSpec
      initializer projector
      (structuredLiveTailEmitterEndpointBridgeDescription
        initializer projector) := by
  have hbridge :
      StructuredLiveTailEmitterEndpointBridgeSpec
        (structuredLiveTailEmitterEndpointBridgeDescription
          initializer projector) :=
    structuredLiveTailEmitterEndpointBridgeDescription_spec_of_components
      hcomponents
  have hfamilyOutput :
      MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec
        (structuredLiveTailEmitterEndpointBridgeDescription
          initializer projector) :=
    hbridge.toOutputSpec
  have hassemblyOutput :
      MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestOutputSpec
        (structuredLiveTailEmitterEndpointBridgeDescription
          initializer projector) :=
    (MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec_iff_assemblyOutputSpec
      _).mp hfamilyOutput
  exact
    { components := hcomponents
      bridge := hbridge
      familyOutput := hfamilyOutput
      assemblyOutput := hassemblyOutput
      shape := liveTailEmitterAssemblyShape }

theorem structuredEndpointLiveTailEmitterOutputRouteConstruction_of_components
    (hcomponents :
      StructuredLiveTailEmitterEndpointComponentsConstruction) :
    StructuredEndpointLiveTailEmitterOutputRouteConstruction := by
  rcases hcomponents with ⟨initializer, projector, hspec⟩
  exact
    ⟨initializer, projector,
      structuredLiveTailEmitterEndpointBridgeDescription
        initializer projector,
      structuredEndpointLiveTailEmitterOutputRouteSpec_of_components
        hspec⟩

theorem outputLiveTailEmitterRouteConstruction_of_structuredEndpoint
    (hroute :
      StructuredEndpointLiveTailEmitterOutputRouteConstruction) :
    OutputLiveTailEmitterRouteConstruction := by
  rcases hroute with ⟨_initializer, _projector, finish, hspec⟩
  exact
    ⟨finish,
      { familyOutput := hspec.familyOutput
        assemblyOutput := hspec.assemblyOutput
        shape := hspec.shape }⟩

theorem assemblyOutputConstruction_of_structuredEndpoint
    (hroute :
      StructuredEndpointLiveTailEmitterOutputRouteConstruction) :
    MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest := by
  rcases hroute with ⟨_initializer, _projector, finish, hspec⟩
  exact ⟨finish, hspec.assemblyOutput⟩

/-!
## Field projections
-/

theorem liveTailEmitterAssemblyShape_of_exactRoute
    (hroute : ExactLiveTailEmitterRouteConstruction)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    LiveTailEmitterAssemblyShape p := by
  rcases hroute with ⟨_finish, hspec⟩
  exact hspec.shape p

theorem liveTailEmitterAssemblyShape_of_outputRoute
    (hroute : OutputLiveTailEmitterRouteConstruction)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    LiveTailEmitterAssemblyShape p := by
  rcases hroute with ⟨_finish, hspec⟩
  exact hspec.shape p

theorem liveTailEmitterAssemblyTargetTape_normalizedOutput_core
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (structuredLiveTailEmitterAssemblyTargetTape p) =
      assemblySourceRestFinishPrefixQuotedSeparatedOutput
        p.w p.sourceRestBits p.stage :=
  (liveTailEmitterAssemblyShape_of_exactRoute
    exactLiveTailEmitterRouteConstruction_core p)
      |>.targetTapeNormalizedOutputEqPrefixQuotedSeparated

theorem liveTailEmitterAssemblyOutputPrefix_eq_emitted_quoteRest_core
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailEmitterAssemblyOutputPrefix p =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) :=
  (liveTailEmitterAssemblyShape_of_exactRoute
    exactLiveTailEmitterRouteConstruction_core p)
      |>.outputPrefixEqEmittedQuoteRest

theorem liveTailEmitterAssemblySourceBits_defaultedCells_core
    (p : AssemblySourceRestLiveTailEmitterParam) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
            (assemblySourceRestLiveTailEmitterLeftRev p)
            (assemblySourceRestLiveTailEmitterQuoteScan p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p))) =
      assemblySourceRestLiveTailEmitterSourceBits p :=
  (liveTailEmitterAssemblyShape_of_exactRoute
    exactLiveTailEmitterRouteConstruction_core p)
      |>.sourceBitsDefaultedCells

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
