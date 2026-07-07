import FoC.Computability.Compiler.ClosedCfg.PostTrans.NestedLayoutParser

set_option doc.verso true

/-!
# Nested-layout route contracts

This module exposes the padded merge nested-layout parser as a set of exact and
normalized-output routes.  The finite-machine leaves remain in
{module}`FoC.Computability.Compiler.ClosedCfg.PostTrans.NestedLayoutParser`;
the definitions here make the feasible contextual window route explicit and
keep the impossible isolated restorer route as a guardrail.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

private theorem haltsFromTapeWithOutput_of_haltsFromTape_target
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTape Tin Tout) :
    D.HaltsFromTapeWithOutput Tin (Tape.normalizedOutput Tout) :=
  MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape h

/-!
## Output-level window specs
-/

def SelectedMergePaddedEmitterNestedLayoutWindowMaterializerOutputSpec
    (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      materializer.HaltsFromTapeWithOutput
        (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p)
        (Tape.normalizedOutput
          (SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape p))

def SelectedMergePaddedEmitterNestedLayoutWindowScannerOutputSpec
    (scanner : MachineDescription) : Prop :=
  scanner.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      scanner.HaltsFromTapeWithOutput
        (SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape p)
        (Tape.normalizedOutput
          (SelectedMergePaddedEmitterNestedLayoutContextParsedTape p))

def SelectedMergePaddedEmitterNestedLayoutWindowRestorerOutputSpec
    (restorer : MachineDescription) : Prop :=
  restorer.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      restorer.HaltsFromTapeWithOutput
        (SelectedMergePaddedEmitterNestedLayoutContextParsedTape p)
        (Tape.normalizedOutput
          (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p))

def SelectedMergePaddedEmitterNestedLayoutWindowIsolatedRestorerOutputSpec
    (restorer : MachineDescription) : Prop :=
  restorer.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      restorer.HaltsFromTapeWithOutput
        (SelectedMergePaddedEmitterNestedLayoutRawParsedTape p)
        (Tape.normalizedOutput
          (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p))

def SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedOutputSpec
    (parser : MachineDescription) : Prop :=
  parser.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      parser.HaltsFromTapeWithOutput
        (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p)
        (Tape.normalizedOutput
          (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p))

def SelectedMergePaddedEmitterNestedLayoutWindowMaterializerOutputConstruction :
    Prop :=
  exists materializer : MachineDescription,
    SelectedMergePaddedEmitterNestedLayoutWindowMaterializerOutputSpec
      materializer

def SelectedMergePaddedEmitterNestedLayoutWindowScannerOutputConstruction :
    Prop :=
  exists scanner : MachineDescription,
    SelectedMergePaddedEmitterNestedLayoutWindowScannerOutputSpec scanner

def SelectedMergePaddedEmitterNestedLayoutWindowRestorerOutputConstruction :
    Prop :=
  exists restorer : MachineDescription,
    SelectedMergePaddedEmitterNestedLayoutWindowRestorerOutputSpec restorer

def SelectedMergePaddedEmitterNestedLayoutWindowIsolatedRestorerOutputConstruction :
    Prop :=
  exists restorer : MachineDescription,
    SelectedMergePaddedEmitterNestedLayoutWindowIsolatedRestorerOutputSpec
      restorer

def SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedOutputConstruction :
    Prop :=
  exists parser : MachineDescription,
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedOutputSpec
      parser

theorem SelectedMergePaddedEmitterNestedLayoutWindowMaterializerOutputSpec_of_exact
    {materializer : MachineDescription}
    (hmaterializer :
      SelectedMergePaddedEmitterNestedLayoutWindowMaterializerSpec
        materializer) :
    SelectedMergePaddedEmitterNestedLayoutWindowMaterializerOutputSpec
      materializer := by
  refine ⟨hmaterializer.left, ?_⟩
  intro p
  exact
    haltsFromTapeWithOutput_of_haltsFromTape_target
      (hmaterializer.right p)

theorem SelectedMergePaddedEmitterNestedLayoutWindowScannerOutputSpec_of_exact
    {scanner : MachineDescription}
    (hscanner :
      SelectedMergePaddedEmitterNestedLayoutWindowScannerSpec scanner) :
    SelectedMergePaddedEmitterNestedLayoutWindowScannerOutputSpec
      scanner := by
  refine ⟨hscanner.left, ?_⟩
  intro p
  exact
    haltsFromTapeWithOutput_of_haltsFromTape_target
      (hscanner.right p)

theorem SelectedMergePaddedEmitterNestedLayoutWindowRestorerOutputSpec_of_exact
    {restorer : MachineDescription}
    (hrestorer :
      SelectedMergePaddedEmitterNestedLayoutWindowRestorerSpec restorer) :
    SelectedMergePaddedEmitterNestedLayoutWindowRestorerOutputSpec
      restorer := by
  refine ⟨hrestorer.left, ?_⟩
  intro p
  exact
    haltsFromTapeWithOutput_of_haltsFromTape_target
      (hrestorer.right p)

theorem SelectedMergePaddedEmitterNestedLayoutWindowIsolatedRestorerOutputSpec_of_exact
    {restorer : MachineDescription}
    (hrestorer :
      SelectedMergePaddedEmitterNestedLayoutWindowIsolatedRestorerSpec
        restorer) :
    SelectedMergePaddedEmitterNestedLayoutWindowIsolatedRestorerOutputSpec
      restorer := by
  refine ⟨hrestorer.left, ?_⟩
  intro p
  exact
    haltsFromTapeWithOutput_of_haltsFromTape_target
      (hrestorer.right p)

theorem SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedOutputSpec_of_exact
    {parser : MachineDescription}
    (hparser :
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedSpec
        parser) :
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedOutputSpec
      parser := by
  refine ⟨hparser.left, ?_⟩
  intro p
  exact
    haltsFromTapeWithOutput_of_haltsFromTape_target
      (hparser.right p)

theorem SelectedMergePaddedEmitterNestedLayoutWindowMaterializerOutputConstruction_of_exact
    (hmaterializer :
      SelectedMergePaddedEmitterNestedLayoutWindowMaterializerConstruction) :
    SelectedMergePaddedEmitterNestedLayoutWindowMaterializerOutputConstruction := by
  rcases hmaterializer with ⟨materializer, hspec⟩
  exact
    ⟨materializer,
      SelectedMergePaddedEmitterNestedLayoutWindowMaterializerOutputSpec_of_exact
        hspec⟩

theorem SelectedMergePaddedEmitterNestedLayoutWindowScannerOutputConstruction_of_exact
    (hscanner :
      SelectedMergePaddedEmitterNestedLayoutWindowScannerConstruction) :
    SelectedMergePaddedEmitterNestedLayoutWindowScannerOutputConstruction := by
  rcases hscanner with ⟨scanner, hspec⟩
  exact
    ⟨scanner,
      SelectedMergePaddedEmitterNestedLayoutWindowScannerOutputSpec_of_exact
        hspec⟩

theorem SelectedMergePaddedEmitterNestedLayoutWindowRestorerOutputConstruction_of_exact
    (hrestorer :
      SelectedMergePaddedEmitterNestedLayoutWindowRestorerConstruction) :
    SelectedMergePaddedEmitterNestedLayoutWindowRestorerOutputConstruction := by
  rcases hrestorer with ⟨restorer, hspec⟩
  exact
    ⟨restorer,
      SelectedMergePaddedEmitterNestedLayoutWindowRestorerOutputSpec_of_exact
        hspec⟩

theorem SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedOutputConstruction_of_exact
    (hparser :
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction) :
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedOutputConstruction := by
  rcases hparser with ⟨parser, hspec⟩
  exact
    ⟨parser,
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedOutputSpec_of_exact
        hspec⟩

/-!
## Window tape shape
-/

structure SelectedMergePaddedEmitterNestedLayoutWindowShape
    (p : SelectedMergeEmitterPayload) : Prop where
  afterHitTapeEqSourceFields :
    SelectedMergePaddedEmitterAfterHitPaddedTape p =
      SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p
  sourceFieldsTapeEqSourceLeftBitsRev :
    SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p =
      DovetailInitialLayoutInitializer.tapeAtCells
        (List.append
          ((SelectedMergePaddedEmitterCleanup.sourceLeftBitsRev p).map some)
          [none])
        [none, none]
  sourceFieldsNormalizedOutputEqSourceBits :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p) =
      SelectedMergePaddedEmitterCleanup.sourceBits p
  sourceFieldsNormalizedOutputEqFields :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend
            (encodeCodeWordAsInput
              (MachineCodeSymbol.transition ::
                encodeBoolWordAppend p.L.input
                  (encodeNatAppend p.L.stage
                    (encodeConfigurationAppend p.L.acceptConfig
                      (encodeConfigurationAppend p.L.rejectConfig
                        (encodeBoolAppend p.L.acceptHit
                          (encodeBoolAppend p.L.rejectHit [])))))))
            (encodeNatAppend p.S.stage
              (encodeConfigurationAppend p.S.config
                (encodeBoolAppend p.S.hit []))))
  sourceFieldsCellsEqSourceBits :
    Tape.cells (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p) =
      List.append [none]
        (List.append
          ((SelectedMergePaddedEmitterCleanup.sourceBits p).map some)
          [none, none])
  sourceFieldsCellsEqFields :
    Tape.cells (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p) =
      List.append [none]
        (List.append
          ((encodeCodeWordAsInput
            (MachineCodeSymbol.transition ::
              encodeBoolWordAppend
                (encodeCodeWordAsInput
                  (MachineCodeSymbol.transition ::
                    encodeBoolWordAppend p.L.input
                      (encodeNatAppend p.L.stage
                        (encodeConfigurationAppend p.L.acceptConfig
                          (encodeConfigurationAppend p.L.rejectConfig
                            (encodeBoolAppend p.L.acceptHit
                              (encodeBoolAppend p.L.rejectHit [])))))))
                (encodeNatAppend p.S.stage
                  (encodeConfigurationAppend p.S.config
                    (encodeBoolAppend p.S.hit []))))).map some)
          [none, none])
  nestedLayoutSourceBitsEqDovetail :
    encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend p.L.input
            (encodeNatAppend p.L.stage
              (encodeConfigurationAppend p.L.acceptConfig
                (encodeConfigurationAppend p.L.rejectConfig
                  (encodeBoolAppend p.L.acceptHit
                    (encodeBoolAppend p.L.rejectHit [])))))) =
      CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits
        p.L []
  nestedLayoutSourceBitsEqMarkedBody :
    encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend p.L.input
            (encodeNatAppend p.L.stage
              (encodeConfigurationAppend p.L.acceptConfig
                (encodeConfigurationAppend p.L.rejectConfig
                  (encodeBoolAppend p.L.acceptHit
                    (encodeBoolAppend p.L.rejectHit [])))))) =
      false ::
        CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits
          p.L
  rawSourceCells :
    Tape.cells (SelectedMergePaddedEmitterNestedLayoutRawSourceTape p) =
      (CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits
        p.L []).map some
  rawSourceNormalizedOutput :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterNestedLayoutRawSourceTape p) =
      CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits
        p.L []
  rawSourceNormalizedOutputEqBits :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterNestedLayoutRawSourceTape p) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend p.L.input
            (encodeNatAppend p.L.stage
              (encodeConfigurationAppend p.L.acceptConfig
                (encodeConfigurationAppend p.L.rejectConfig
                  (encodeBoolAppend p.L.acceptHit
                    (encodeBoolAppend p.L.rejectHit []))))))
  rawParsedNormalizedOutput :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterNestedLayoutRawParsedTape p) =
      false ::
        CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits
          p.L
  contextRawSourceCells :
    Tape.cells
        (SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape p) =
      (CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits
        p.L (SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p)).map
        some
  contextRawSourceNormalizedOutput :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape p) =
      CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits
        p.L (SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p)
  contextParsedCells :
    Tape.cells
        (SelectedMergePaddedEmitterNestedLayoutContextParsedTape p) =
      (SelectedMergePaddedEmitterParsedInnerSourceBits p).map some
  contextParsedNormalizedOutput :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterNestedLayoutContextParsedTape p) =
      SelectedMergePaddedEmitterParsedInnerSourceBits p
  rawSourceMoveLeftMoveRight :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedMergePaddedEmitterNestedLayoutRawSourceTape p)) =
      SelectedMergePaddedEmitterNestedLayoutRawSourceTape p
  rawParsedMoveLeftMoveRight :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedMergePaddedEmitterNestedLayoutRawParsedTape p)) =
      SelectedMergePaddedEmitterNestedLayoutRawParsedTape p
  contextRawSourceMoveLeftMoveRight :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape p)) =
      SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape p
  contextParsedMoveLeftMoveRight :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedMergePaddedEmitterNestedLayoutContextParsedTape p)) =
      SelectedMergePaddedEmitterNestedLayoutContextParsedTape p
  checkedScannerRawHalts :
    CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.HaltsFromTape
      (SelectedMergePaddedEmitterNestedLayoutRawSourceTape p)
      (SelectedMergePaddedEmitterNestedLayoutRawParsedTape p)

theorem selectedMergePaddedEmitterNestedLayoutWindowShape
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterNestedLayoutWindowShape p :=
  { afterHitTapeEqSourceFields :=
      SelectedMergePaddedEmitterAfterHitPaddedTape_eq_sourceFieldsTape p
    sourceFieldsTapeEqSourceLeftBitsRev :=
      SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape_eq_sourceLeftBitsRev_tapeAtCells
        p
    sourceFieldsNormalizedOutputEqSourceBits :=
      SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape_normalizedOutput_eq_sourceBits
        p
    sourceFieldsNormalizedOutputEqFields :=
      SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape_normalizedOutput_eq_fields
        p
    sourceFieldsCellsEqSourceBits :=
      SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape_cells_eq_sourceBits
        p
    sourceFieldsCellsEqFields :=
      SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape_cells_eq_fields
        p
    nestedLayoutSourceBitsEqDovetail :=
      SelectedMergePaddedEmitterNestedLayoutSourceBits_eq_dovetailLayoutFieldBits
        p
    nestedLayoutSourceBitsEqMarkedBody :=
      SelectedMergePaddedEmitterNestedLayoutSourceBits_eq_markedBodyBits p
    rawSourceCells :=
      SelectedMergePaddedEmitterNestedLayoutRawSourceTape_cells p
    rawSourceNormalizedOutput :=
      SelectedMergePaddedEmitterNestedLayoutRawSourceTape_normalizedOutput p
    rawSourceNormalizedOutputEqBits :=
      SelectedMergePaddedEmitterNestedLayoutRawSourceTape_normalizedOutput_eq_bits
        p
    rawParsedNormalizedOutput :=
      SelectedMergePaddedEmitterNestedLayoutRawParsedTape_normalizedOutput p
    contextRawSourceCells :=
      SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape_cells p
    contextRawSourceNormalizedOutput :=
      SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape_normalizedOutput
        p
    contextParsedCells :=
      SelectedMergePaddedEmitterNestedLayoutContextParsedTape_cells p
    contextParsedNormalizedOutput :=
      SelectedMergePaddedEmitterNestedLayoutContextParsedTape_normalizedOutput
        p
    rawSourceMoveLeftMoveRight :=
      SelectedMergePaddedEmitterNestedLayoutRawSourceTape_move_left_move_right
        p
    rawParsedMoveLeftMoveRight :=
      SelectedMergePaddedEmitterNestedLayoutRawParsedTape_move_left_move_right
        p
    contextRawSourceMoveLeftMoveRight :=
      SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape_move_left_move_right
        p
    contextParsedMoveLeftMoveRight :=
      SelectedMergePaddedEmitterNestedLayoutContextParsedTape_move_left_move_right
        p
    checkedScannerRawHalts :=
      checkedDovetailLayoutScannerDescription_haltsFrom_mergeNestedLayoutRawSource
        p }

/-!
## Exact and output route bundles
-/

structure SelectedMergePaddedEmitterNestedLayoutWindowExactRouteSpec
    (materializer scanner restorer : MachineDescription) : Prop where
  materializerExact :
    SelectedMergePaddedEmitterNestedLayoutWindowMaterializerSpec
      materializer
  scannerExact :
    SelectedMergePaddedEmitterNestedLayoutWindowScannerSpec scanner
  restorerExact :
    SelectedMergePaddedEmitterNestedLayoutWindowRestorerSpec restorer
  materializerOutput :
    SelectedMergePaddedEmitterNestedLayoutWindowMaterializerOutputSpec
      materializer
  scannerOutput :
    SelectedMergePaddedEmitterNestedLayoutWindowScannerOutputSpec scanner
  restorerOutput :
    SelectedMergePaddedEmitterNestedLayoutWindowRestorerOutputSpec
      restorer
  parserExact :
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedSpec
      (SelectedMergePaddedEmitterNestedLayoutWindowParser
        materializer scanner restorer)
  parserOutput :
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedOutputSpec
      (SelectedMergePaddedEmitterNestedLayoutWindowParser
        materializer scanner restorer)
  shape :
    forall p : SelectedMergeEmitterPayload,
      SelectedMergePaddedEmitterNestedLayoutWindowShape p

def SelectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction :
    Prop :=
  exists materializer scanner restorer : MachineDescription,
    SelectedMergePaddedEmitterNestedLayoutWindowExactRouteSpec
      materializer scanner restorer

structure SelectedMergePaddedEmitterNestedLayoutWindowOutputRouteSpec
    (materializer scanner restorer : MachineDescription) : Prop where
  materializerOutput :
    SelectedMergePaddedEmitterNestedLayoutWindowMaterializerOutputSpec
      materializer
  scannerOutput :
    SelectedMergePaddedEmitterNestedLayoutWindowScannerOutputSpec scanner
  restorerOutput :
    SelectedMergePaddedEmitterNestedLayoutWindowRestorerOutputSpec
      restorer
  parserOutput :
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedOutputSpec
      (SelectedMergePaddedEmitterNestedLayoutWindowParser
        materializer scanner restorer)
  shape :
    forall p : SelectedMergeEmitterPayload,
      SelectedMergePaddedEmitterNestedLayoutWindowShape p

def SelectedMergePaddedEmitterNestedLayoutWindowOutputRouteConstruction :
    Prop :=
  exists materializer scanner restorer : MachineDescription,
    SelectedMergePaddedEmitterNestedLayoutWindowOutputRouteSpec
      materializer scanner restorer

theorem selectedMergePaddedEmitterNestedLayoutWindowExactRouteSpec_of_parts
    {materializer scanner restorer : MachineDescription}
    (hmaterializer :
      SelectedMergePaddedEmitterNestedLayoutWindowMaterializerSpec
        materializer)
    (hscanner :
      SelectedMergePaddedEmitterNestedLayoutWindowScannerSpec scanner)
    (hrestorer :
      SelectedMergePaddedEmitterNestedLayoutWindowRestorerSpec restorer) :
    SelectedMergePaddedEmitterNestedLayoutWindowExactRouteSpec
      materializer scanner restorer := by
  have hparser :
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedSpec
        (SelectedMergePaddedEmitterNestedLayoutWindowParser
          materializer scanner restorer) :=
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedSpec_of_windowMaterializerAndRestorer
      hmaterializer hscanner hrestorer
  exact
    { materializerExact := hmaterializer
      scannerExact := hscanner
      restorerExact := hrestorer
      materializerOutput :=
        SelectedMergePaddedEmitterNestedLayoutWindowMaterializerOutputSpec_of_exact
          hmaterializer
      scannerOutput :=
        SelectedMergePaddedEmitterNestedLayoutWindowScannerOutputSpec_of_exact
          hscanner
      restorerOutput :=
        SelectedMergePaddedEmitterNestedLayoutWindowRestorerOutputSpec_of_exact
          hrestorer
      parserExact := hparser
      parserOutput :=
        SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedOutputSpec_of_exact
          hparser
      shape := selectedMergePaddedEmitterNestedLayoutWindowShape }

theorem selectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction_of_parts
    (hmaterializer :
      SelectedMergePaddedEmitterNestedLayoutWindowMaterializerConstruction)
    (hscanner :
      SelectedMergePaddedEmitterNestedLayoutWindowScannerConstruction)
    (hrestorer :
      SelectedMergePaddedEmitterNestedLayoutWindowRestorerConstruction) :
    SelectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction := by
  rcases hmaterializer with ⟨materializer, hmaterializerSpec⟩
  rcases hscanner with ⟨scanner, hscannerSpec⟩
  rcases hrestorer with ⟨restorer, hrestorerSpec⟩
  exact
    ⟨materializer, scanner, restorer,
      selectedMergePaddedEmitterNestedLayoutWindowExactRouteSpec_of_parts
        hmaterializerSpec hscannerSpec hrestorerSpec⟩

theorem selectedMergePaddedEmitterNestedLayoutWindowMaterializerConstruction_of_exactRoute
    (hroute :
      SelectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction) :
    SelectedMergePaddedEmitterNestedLayoutWindowMaterializerConstruction := by
  rcases hroute with ⟨materializer, _scanner, _restorer, hspec⟩
  exact ⟨materializer, hspec.materializerExact⟩

theorem selectedMergePaddedEmitterNestedLayoutWindowScannerConstruction_of_exactRoute
    (hroute :
      SelectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction) :
    SelectedMergePaddedEmitterNestedLayoutWindowScannerConstruction := by
  rcases hroute with ⟨_materializer, scanner, _restorer, hspec⟩
  exact ⟨scanner, hspec.scannerExact⟩

theorem selectedMergePaddedEmitterNestedLayoutWindowRestorerConstruction_of_exactRoute
    (hroute :
      SelectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction) :
    SelectedMergePaddedEmitterNestedLayoutWindowRestorerConstruction := by
  rcases hroute with ⟨_materializer, _scanner, restorer, hspec⟩
  exact ⟨restorer, hspec.restorerExact⟩

theorem selectedMergePaddedEmitterNestedLayoutWindowMaterializerAndRestorerConstruction_of_exactRoute
    (hroute :
      SelectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction) :
    SelectedMergePaddedEmitterNestedLayoutWindowMaterializerAndRestorerConstruction := by
  rcases hroute with ⟨materializer, scanner, restorer, hspec⟩
  exact
    ⟨materializer, scanner, restorer, hspec.materializerExact,
      hspec.scannerExact, hspec.restorerExact⟩

theorem selectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction_iff_parts :
    SelectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction ↔
      SelectedMergePaddedEmitterNestedLayoutWindowMaterializerConstruction ∧
      SelectedMergePaddedEmitterNestedLayoutWindowScannerConstruction ∧
      SelectedMergePaddedEmitterNestedLayoutWindowRestorerConstruction := by
  constructor
  · intro hroute
    exact
      ⟨selectedMergePaddedEmitterNestedLayoutWindowMaterializerConstruction_of_exactRoute
          hroute,
        selectedMergePaddedEmitterNestedLayoutWindowScannerConstruction_of_exactRoute
          hroute,
        selectedMergePaddedEmitterNestedLayoutWindowRestorerConstruction_of_exactRoute
          hroute⟩
  · intro hparts
    exact
      selectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction_of_parts
        hparts.left hparts.right.left hparts.right.right

theorem selectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction_core :
    SelectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction :=
  selectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction_of_parts
    selectedMergePaddedEmitterNestedLayoutWindowMaterializerConstruction
    selectedMergePaddedEmitterNestedLayoutWindowScannerConstruction
    selectedMergePaddedEmitterNestedLayoutWindowRestorerConstruction

theorem selectedMergePaddedEmitterNestedLayoutWindowOutputRouteSpec_of_exact
    {materializer scanner restorer : MachineDescription}
    (hroute :
      SelectedMergePaddedEmitterNestedLayoutWindowExactRouteSpec
        materializer scanner restorer) :
    SelectedMergePaddedEmitterNestedLayoutWindowOutputRouteSpec
      materializer scanner restorer :=
  { materializerOutput := hroute.materializerOutput
    scannerOutput := hroute.scannerOutput
    restorerOutput := hroute.restorerOutput
    parserOutput := hroute.parserOutput
    shape := hroute.shape }

theorem selectedMergePaddedEmitterNestedLayoutWindowOutputRouteConstruction_of_exact
    (hroute :
      SelectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction) :
    SelectedMergePaddedEmitterNestedLayoutWindowOutputRouteConstruction := by
  rcases hroute with ⟨materializer, scanner, restorer, hspec⟩
  exact
    ⟨materializer, scanner, restorer,
      selectedMergePaddedEmitterNestedLayoutWindowOutputRouteSpec_of_exact
        hspec⟩

theorem selectedMergePaddedEmitterNestedLayoutWindowOutputRouteConstruction_core :
    SelectedMergePaddedEmitterNestedLayoutWindowOutputRouteConstruction :=
  selectedMergePaddedEmitterNestedLayoutWindowOutputRouteConstruction_of_exact
    selectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction_core

theorem selectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction_of_exactRoute
    (hroute :
      SelectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction) :
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction := by
  rcases hroute with ⟨materializer, scanner, restorer, hspec⟩
  exact
    ⟨SelectedMergePaddedEmitterNestedLayoutWindowParser
        materializer scanner restorer,
      hspec.parserExact⟩

theorem selectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedOutputConstruction_of_outputRoute
    (hroute :
      SelectedMergePaddedEmitterNestedLayoutWindowOutputRouteConstruction) :
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedOutputConstruction := by
  rcases hroute with ⟨materializer, scanner, restorer, hspec⟩
  exact
    ⟨SelectedMergePaddedEmitterNestedLayoutWindowParser
        materializer scanner restorer,
      hspec.parserOutput⟩

/-!
## Guardrail route for the isolated restorer
-/

structure SelectedMergePaddedEmitterNestedLayoutIsolatedRestorerGuardrail
    : Prop where
  targetEqOfLayoutEq :
    forall {restorer : MachineDescription},
      SelectedMergePaddedEmitterNestedLayoutWindowIsolatedRestorerSpec
        restorer ->
      forall {p q : SelectedMergeEmitterPayload},
        p.L = q.L ->
        SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p =
          SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape q
  impossible :
    ¬ SelectedMergePaddedEmitterNestedLayoutWindowIsolatedRestorerConstruction

theorem selectedMergePaddedEmitterNestedLayoutIsolatedRestorerGuardrail :
    SelectedMergePaddedEmitterNestedLayoutIsolatedRestorerGuardrail :=
  { targetEqOfLayoutEq :=
      by
        intro restorer hrestorer p q hL
        exact
          selectedMergePaddedEmitterNestedLayoutWindowIsolatedRestorerSpec_target_eq_of_layout_eq
            hrestorer hL
    impossible :=
      selectedMergePaddedEmitterNestedLayoutWindowIsolatedRestorerConstruction_impossible }

/-!
## Field projections
-/

theorem selectedMergePaddedEmitterNestedLayoutWindowShape_of_exactRoute
    (hroute :
      SelectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction)
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterNestedLayoutWindowShape p := by
  rcases hroute with ⟨_materializer, _scanner, _restorer, hspec⟩
  exact hspec.shape p

theorem selectedMergePaddedEmitterNestedLayoutWindowShape_of_outputRoute
    (hroute :
      SelectedMergePaddedEmitterNestedLayoutWindowOutputRouteConstruction)
    (p : SelectedMergeEmitterPayload) :
    SelectedMergePaddedEmitterNestedLayoutWindowShape p := by
  rcases hroute with ⟨_materializer, _scanner, _restorer, hspec⟩
  exact hspec.shape p

theorem selectedMergePaddedEmitterNestedLayoutWindowContextRawSource_normalizedOutput_core
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape p) =
      CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits
        p.L (SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p) :=
  (selectedMergePaddedEmitterNestedLayoutWindowShape_of_exactRoute
    selectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction_core p)
      |>.contextRawSourceNormalizedOutput

theorem selectedMergePaddedEmitterNestedLayoutWindowContextParsed_normalizedOutput_core
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterNestedLayoutContextParsedTape p) =
      SelectedMergePaddedEmitterParsedInnerSourceBits p :=
  (selectedMergePaddedEmitterNestedLayoutWindowShape_of_exactRoute
    selectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction_core p)
      |>.contextParsedNormalizedOutput

theorem selectedMergePaddedEmitterNestedLayoutWindowSourceFields_normalizedOutput_core
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p) =
      SelectedMergePaddedEmitterCleanup.sourceBits p :=
  (selectedMergePaddedEmitterNestedLayoutWindowShape_of_exactRoute
    selectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction_core p)
      |>.sourceFieldsNormalizedOutputEqSourceBits

theorem selectedMergePaddedEmitterNestedLayoutWindowRawSource_cells_core
    (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergePaddedEmitterNestedLayoutRawSourceTape p) =
      (CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits
        p.L []).map some :=
  (selectedMergePaddedEmitterNestedLayoutWindowShape_of_exactRoute
    selectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction_core p)
      |>.rawSourceCells

theorem selectedMergePaddedEmitterNestedLayoutWindowContextParsed_move_left_move_right_core
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedMergePaddedEmitterNestedLayoutContextParsedTape p)) =
      SelectedMergePaddedEmitterNestedLayoutContextParsedTape p :=
  (selectedMergePaddedEmitterNestedLayoutWindowShape_of_exactRoute
    selectedMergePaddedEmitterNestedLayoutWindowExactRouteConstruction_core p)
      |>.contextParsedMoveLeftMoveRight

theorem selectedMergePaddedEmitterNestedLayoutWindowMaterializer_output_core
    (hroute :
      SelectedMergePaddedEmitterNestedLayoutWindowOutputRouteConstruction) :
    SelectedMergePaddedEmitterNestedLayoutWindowMaterializerOutputConstruction := by
  rcases hroute with ⟨materializer, _scanner, _restorer, hspec⟩
  exact ⟨materializer, hspec.materializerOutput⟩

theorem selectedMergePaddedEmitterNestedLayoutWindowScanner_output_core
    (hroute :
      SelectedMergePaddedEmitterNestedLayoutWindowOutputRouteConstruction) :
    SelectedMergePaddedEmitterNestedLayoutWindowScannerOutputConstruction := by
  rcases hroute with ⟨_materializer, scanner, _restorer, hspec⟩
  exact ⟨scanner, hspec.scannerOutput⟩

theorem selectedMergePaddedEmitterNestedLayoutWindowRestorer_output_core
    (hroute :
      SelectedMergePaddedEmitterNestedLayoutWindowOutputRouteConstruction) :
    SelectedMergePaddedEmitterNestedLayoutWindowRestorerOutputConstruction := by
  rcases hroute with ⟨_materializer, _scanner, restorer, hspec⟩
  exact ⟨restorer, hspec.restorerOutput⟩

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
