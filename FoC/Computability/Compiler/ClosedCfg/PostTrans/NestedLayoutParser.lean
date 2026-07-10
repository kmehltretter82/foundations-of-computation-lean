import FoC.Computability.Compiler.ClosedCfg.PostTrans.Specs

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

/-!
# Merge post-transition nested layout parser
-/

def SelectedMergePaddedEmitterNestedLayoutRawSourceTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells []
    ((CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits
      p.L []).map some)

def SelectedMergePaddedEmitterNestedLayoutRawParsedTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  CanonicalLayouts.DovetailLayoutScanner.restoredCheckedHandoffTapeFromTail
    (CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyRestoredBitsRev
      p.L).reverse

def SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells []
    ((CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits
      p.L (SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p)).map some)

def SelectedMergePaddedEmitterNestedLayoutContextParsedTape
    (p : SelectedMergeEmitterPayload) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells []
    ((SelectedMergePaddedEmitterParsedInnerSourceBits p).map some)

-- Expose the raw scanner source as cells and normalized bits.  The materializer
-- leaf should only need to produce this exact dovetail-layout field window.
theorem SelectedMergePaddedEmitterNestedLayoutRawSourceTape_cells
    (p : SelectedMergeEmitterPayload) :
    Tape.cells (SelectedMergePaddedEmitterNestedLayoutRawSourceTape p) =
      (CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits
        p.L []).map some := by
  rw [SelectedMergePaddedEmitterNestedLayoutRawSourceTape,
    CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits_nil_eq_first_body]
  rcases
      CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits_cons_false
        p.L with
    ⟨tail, htail⟩
  rw [htail]
  simp [
    DovetailInitialLayoutInitializer.tapeAtCells, Tape.cells]

theorem SelectedMergePaddedEmitterNestedLayoutRawSourceTape_normalizedOutput
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput (SelectedMergePaddedEmitterNestedLayoutRawSourceTape p) =
      CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits
        p.L [] := by
  rw [Tape.normalizedOutput,
    SelectedMergePaddedEmitterNestedLayoutRawSourceTape_cells]
  simp [Function.comp_def]

theorem SelectedMergePaddedEmitterNestedLayoutRawSourceTape_normalizedOutput_eq_bits
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput (SelectedMergePaddedEmitterNestedLayoutRawSourceTape p) =
      encodeCodeWordAsInput
        (MachineCodeSymbol.transition ::
          encodeBoolWordAppend p.L.input
            (encodeNatAppend p.L.stage
              (encodeConfigurationAppend p.L.acceptConfig
                (encodeConfigurationAppend p.L.rejectConfig
                  (encodeBoolAppend p.L.acceptHit
                    (encodeBoolAppend p.L.rejectHit [])))))) := by
  rw [SelectedMergePaddedEmitterNestedLayoutRawSourceTape_normalizedOutput]
  exact
    (SelectedMergePaddedEmitterNestedLayoutSourceBits_eq_dovetailLayoutFieldBits
      p).symm

-- The checked scanner target depends only on the inner dovetail layout, not on
-- the outer simulator fields carried by the selected merge payload.
theorem SelectedMergePaddedEmitterNestedLayoutRawParsedTape_normalizedOutput
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterNestedLayoutRawParsedTape p) =
      false ::
        CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits
          p.L := by
  rw [SelectedMergePaddedEmitterNestedLayoutRawParsedTape,
    CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyRestoredBitsRev_reverse]
  rcases
      CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits_cons_false
        p.L with
    ⟨tail, htail⟩
  rw [htail]
  simp [
    CanonicalLayouts.DovetailLayoutScanner.restoredCheckedHandoffTapeFromTail,
    Tape.move, Tape.moveRight, Tape.normalizedOutput, Tape.cells,
    Function.comp_def]

theorem SelectedMergePaddedEmitterNestedLayoutRawParsedTape_eq_of_layout_eq
    {p q : SelectedMergeEmitterPayload} (hL : p.L = q.L) :
    SelectedMergePaddedEmitterNestedLayoutRawParsedTape p =
      SelectedMergePaddedEmitterNestedLayoutRawParsedTape q := by
  rw [SelectedMergePaddedEmitterNestedLayoutRawParsedTape,
    SelectedMergePaddedEmitterNestedLayoutRawParsedTape, hL]

-- Contextual scanner windows preserve the outer simulator fields after the
-- nested raw layout, so the downstream restorer has enough information.
theorem SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape_cells
    (p : SelectedMergeEmitterPayload) :
    Tape.cells
        (SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape p) =
      (CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits
        p.L (SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p)).map
        some := by
  rw [SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape]
  simp [DovetailInitialLayoutInitializer.tapeAtCells, Tape.cells,
    CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.transitionPrefixBits,
    encodeCodeSymbolAsInput]

theorem SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape_normalizedOutput
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape p) =
      CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits
        p.L (SelectedMergePaddedEmitterParsedInnerOuterSuffixBits p) := by
  rw [Tape.normalizedOutput,
    SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape_cells]
  simp [Function.comp_def]

theorem SelectedMergePaddedEmitterNestedLayoutContextParsedTape_cells
    (p : SelectedMergeEmitterPayload) :
    Tape.cells
        (SelectedMergePaddedEmitterNestedLayoutContextParsedTape p) =
      (SelectedMergePaddedEmitterParsedInnerSourceBits p).map some := by
  rw [SelectedMergePaddedEmitterNestedLayoutContextParsedTape]
  simp [DovetailInitialLayoutInitializer.tapeAtCells, Tape.cells,
    SelectedMergePaddedEmitterParsedInnerSourceBits,
    encodeCodeSymbolAsInput]

theorem SelectedMergePaddedEmitterNestedLayoutContextParsedTape_normalizedOutput
    (p : SelectedMergeEmitterPayload) :
    Tape.normalizedOutput
        (SelectedMergePaddedEmitterNestedLayoutContextParsedTape p) =
      SelectedMergePaddedEmitterParsedInnerSourceBits p := by
  rw [Tape.normalizedOutput,
    SelectedMergePaddedEmitterNestedLayoutContextParsedTape_cells]
  simp [Function.comp_def]

theorem SelectedMergePaddedEmitterNestedLayoutRawSourceTape_move_left_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedMergePaddedEmitterNestedLayoutRawSourceTape p)) =
      SelectedMergePaddedEmitterNestedLayoutRawSourceTape p := by
  rw [SelectedMergePaddedEmitterNestedLayoutRawSourceTape,
    CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits_nil_eq_first_body]
  rcases
      CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits_cons_false
        p.L with
    ⟨tail, htail⟩
  rw [htail]
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem SelectedMergePaddedEmitterNestedLayoutRawParsedTape_move_left_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedMergePaddedEmitterNestedLayoutRawParsedTape p)) =
      SelectedMergePaddedEmitterNestedLayoutRawParsedTape p := by
  rw [SelectedMergePaddedEmitterNestedLayoutRawParsedTape]
  rw [
    CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyRestoredBitsRev_reverse]
  rcases
      CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits_cons_false
        p.L with
    ⟨tail, htail⟩
  rw [htail]
  cases tail <;>
    simp [
      CanonicalLayouts.DovetailLayoutScanner.restoredCheckedHandoffTapeFromTail,
      Tape.move, Tape.moveLeft, Tape.moveRight]

theorem SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape_move_left_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape p)) =
      SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape p := by
  rw [SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape]
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight,
    CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.transitionPrefixBits,
    encodeCodeSymbolAsInput]

theorem SelectedMergePaddedEmitterNestedLayoutContextParsedTape_move_left_move_right
    (p : SelectedMergeEmitterPayload) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (SelectedMergePaddedEmitterNestedLayoutContextParsedTape p)) =
      SelectedMergePaddedEmitterNestedLayoutContextParsedTape p := by
  rw [SelectedMergePaddedEmitterNestedLayoutContextParsedTape]
  simp [DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight,
    SelectedMergePaddedEmitterParsedInnerSourceBits,
    encodeCodeSymbolAsInput]

theorem checkedDovetailLayoutScannerDescription_haltsFrom_raw_nestedLayout
    (L : DovetailLayout) :
    CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.HaltsFromTape
      (DovetailInitialLayoutInitializer.tapeAtCells []
        ((CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits
          L []).map some))
      (CanonicalLayouts.DovetailLayoutScanner.restoredCheckedHandoffTapeFromTail
        (CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyRestoredBitsRev
          L).reverse) := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.run_checkedDovetailLayoutScanner_raw_to_checkedHandoff
        L with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn] using
      congrArg MachineDescription.Configuration.state hsteps
  · simpa [MachineDescription.HaltsFromTapeIn] using
      congrArg MachineDescription.Configuration.tape hsteps

theorem checkedDovetailLayoutScannerDescription_haltsFrom_mergeNestedLayoutRawSource
    (p : SelectedMergeEmitterPayload) :
    CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.HaltsFromTape
      (SelectedMergePaddedEmitterNestedLayoutRawSourceTape p)
      (SelectedMergePaddedEmitterNestedLayoutRawParsedTape p) := by
  exact checkedDovetailLayoutScannerDescription_haltsFrom_raw_nestedLayout
    p.L

def SelectedMergePaddedEmitterNestedLayoutWindowExactMaterializerSpec
    (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      materializer.HaltsFromTape
        (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p)
        (SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape p)

def SelectedMergePaddedEmitterNestedLayoutWindowMaterializerSpec
    (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      materializer.HaltsFromTapeEquiv
        (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p)
        (SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape p)

def SelectedMergePaddedEmitterNestedLayoutWindowScannerSpec
    (scanner : MachineDescription) : Prop :=
  scanner.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      scanner.HaltsFromTape
        (SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape p)
        (SelectedMergePaddedEmitterNestedLayoutContextParsedTape p)

def SelectedMergePaddedEmitterNestedLayoutWindowRestorerSpec
    (restorer : MachineDescription) : Prop :=
  restorer.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      restorer.HaltsFromTape
        (SelectedMergePaddedEmitterNestedLayoutContextParsedTape p)
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p)

def SelectedMergePaddedEmitterNestedLayoutWindowIsolatedRestorerSpec
    (restorer : MachineDescription) : Prop :=
  restorer.SubroutineReady ∧
    forall p : SelectedMergeEmitterPayload,
      restorer.HaltsFromTape
        (SelectedMergePaddedEmitterNestedLayoutRawParsedTape p)
        (SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p)

-- If a deterministic restorer starts from a tape determined only by `p.L`,
-- then payloads with the same inner layout must have identical restored targets.
theorem selectedMergePaddedEmitterNestedLayoutWindowIsolatedRestorerSpec_target_eq_of_layout_eq
    {restorer : MachineDescription}
    (hrestorer :
      SelectedMergePaddedEmitterNestedLayoutWindowIsolatedRestorerSpec
        restorer)
    {p q : SelectedMergeEmitterPayload} (hL : p.L = q.L) :
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p =
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape q := by
  have hsource :
      SelectedMergePaddedEmitterNestedLayoutRawParsedTape p =
        SelectedMergePaddedEmitterNestedLayoutRawParsedTape q :=
    SelectedMergePaddedEmitterNestedLayoutRawParsedTape_eq_of_layout_eq hL
  have hp := hrestorer.right p
  have hq := hrestorer.right q
  rw [← hsource] at hq
  exact
    haltsFromTape_functional_of_haltTransitionFree
      hrestorer.left.right hp hq

def SelectedMergePaddedEmitterNestedLayoutWindowMaterializerConstruction :
    Prop :=
  exists materializer : MachineDescription,
    SelectedMergePaddedEmitterNestedLayoutWindowMaterializerSpec
      materializer

def SelectedMergePaddedEmitterNestedLayoutWindowScannerConstruction :
    Prop :=
  exists scanner : MachineDescription,
    SelectedMergePaddedEmitterNestedLayoutWindowScannerSpec scanner

def SelectedMergePaddedEmitterNestedLayoutWindowRestorerConstruction :
    Prop :=
  exists restorer : MachineDescription,
    SelectedMergePaddedEmitterNestedLayoutWindowRestorerSpec restorer

def SelectedMergePaddedEmitterNestedLayoutWindowIsolatedRestorerConstruction :
    Prop :=
  exists restorer : MachineDescription,
    SelectedMergePaddedEmitterNestedLayoutWindowIsolatedRestorerSpec
      restorer

def selectedMergePaddedEmitterNestedLayoutMaterializerContextCounterexampleConfig :
    Configuration :=
  { state := 0, tape := Tape.input [] }

def selectedMergePaddedEmitterNestedLayoutMaterializerContextCounterexampleLayout :
    DovetailLayout :=
  { input := []
    stage := 0
    acceptConfig :=
      selectedMergePaddedEmitterNestedLayoutMaterializerContextCounterexampleConfig
    rejectConfig :=
      selectedMergePaddedEmitterNestedLayoutMaterializerContextCounterexampleConfig
    acceptHit := false
    rejectHit := false }

def selectedMergePaddedEmitterNestedLayoutMaterializerContextCounterexampleSimulator :
    SimulatorLayout :=
  { input :=
      encodeCodeWordAsInput
        (DovetailLayout.encode
          selectedMergePaddedEmitterNestedLayoutMaterializerContextCounterexampleLayout)
    stage := 0
    config :=
      selectedMergePaddedEmitterNestedLayoutMaterializerContextCounterexampleConfig
    hit := false }

def selectedMergePaddedEmitterNestedLayoutMaterializerContextCounterexampleParam :
    SelectedMergeEmitterPayload :=
  { S :=
      selectedMergePaddedEmitterNestedLayoutMaterializerContextCounterexampleSimulator
    L :=
      selectedMergePaddedEmitterNestedLayoutMaterializerContextCounterexampleLayout
    input := by
      simp [
        selectedMergePaddedEmitterNestedLayoutMaterializerContextCounterexampleSimulator]
      exact
        decodeCodeWordAsInput_encodeCodeWordAsInput
          (DovetailLayout.encode
            selectedMergePaddedEmitterNestedLayoutMaterializerContextCounterexampleLayout) }

/--
The old exact materializer source has 450 context cells, while its requested
target has only 75.  This is the permanent size regression witness for #24.
-/
theorem selectedMergePaddedEmitterNestedLayoutMaterializerContextCounterexample_contextLengths :
    Tape.contextLength
        (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape
          selectedMergePaddedEmitterNestedLayoutMaterializerContextCounterexampleParam) =
      450 ∧
    Tape.contextLength
        (SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape
          selectedMergePaddedEmitterNestedLayoutMaterializerContextCounterexampleParam) =
      75 := by
  set_option maxRecDepth 4096 in
    decide

/-- The old exact nested-layout materializer family is unreachable. -/
theorem not_selectedMergePaddedEmitterNestedLayoutWindowExactMaterializerConstruction :
    ¬ exists materializer : MachineDescription,
      SelectedMergePaddedEmitterNestedLayoutWindowExactMaterializerSpec
        materializer := by
  intro hconstruction
  rcases hconstruction with ⟨materializer, hmaterializer⟩
  have hrun :=
    hmaterializer.right
      selectedMergePaddedEmitterNestedLayoutMaterializerContextCounterexampleParam
  apply MachineDescription.not_haltsFromTape_of_contextLength_gt ?_ hrun
  set_option maxRecDepth 4096 in
    decide

-- The current restorer contract is inconsistent: two payloads share the same
-- inner layout source but require different outer-stage target tapes.
theorem selectedMergePaddedEmitterNestedLayoutWindowIsolatedRestorerConstruction_impossible :
    ¬ SelectedMergePaddedEmitterNestedLayoutWindowIsolatedRestorerConstruction := by
  intro h
  rcases h with ⟨restorer, hrestorer⟩
  let cfg : Configuration := { state := 0, tape := Tape.input [] }
  let L : DovetailLayout :=
    { input := []
      stage := 0
      acceptConfig := cfg
      rejectConfig := cfg
      acceptHit := false
      rejectHit := false }
  let S0 : SimulatorLayout :=
    { input := encodeCodeWordAsInput (DovetailLayout.encode L)
      stage := 0
      config := cfg
      hit := false }
  let S1 : SimulatorLayout :=
    { input := encodeCodeWordAsInput (DovetailLayout.encode L)
      stage := 1
      config := cfg
      hit := false }
  let p0 : SelectedMergeEmitterPayload :=
    { S := S0
      L := L
      input := by
        simp [S0]
        exact decodeCodeWordAsInput_encodeCodeWordAsInput
          (DovetailLayout.encode L) }
  let p1 : SelectedMergeEmitterPayload :=
    { S := S1
      L := L
      input := by
        simp [S1]
        exact decodeCodeWordAsInput_encodeCodeWordAsInput
          (DovetailLayout.encode L) }
  have htape :
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p0 =
        SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape p1 :=
    selectedMergePaddedEmitterNestedLayoutWindowIsolatedRestorerSpec_target_eq_of_layout_eq
      hrestorer rfl
  have hnorm :=
    congrArg Tape.normalizedOutput htape
  rw [
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape_normalizedOutput_eq_markedBody,
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedTape_normalizedOutput_eq_markedBody] at hnorm
  simp [p0, p1, S0, S1, L, cfg,
    FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits,
    encodeNat, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
    CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits,
    CanonicalLayouts.DovetailLayoutScanner.transitionRemainderBits,
    CanonicalLayouts.DovetailLayoutScanner.boolWordFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellListFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.tapeFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    List.append_assoc] at hnorm
  contradiction

def SelectedMergePaddedEmitterNestedLayoutWindowMaterializerAndRestorerConstruction :
    Prop :=
  exists materializer : MachineDescription,
  exists scanner : MachineDescription,
  exists restorer : MachineDescription,
    SelectedMergePaddedEmitterNestedLayoutWindowMaterializerSpec
      materializer ∧
    SelectedMergePaddedEmitterNestedLayoutWindowScannerSpec scanner ∧
    SelectedMergePaddedEmitterNestedLayoutWindowRestorerSpec restorer

def SelectedMergePaddedEmitterNestedLayoutWindowParser
    (materializer scanner restorer : MachineDescription) : MachineDescription :=
  SeqViaCanonical
    (SeqViaCanonical materializer
      scanner)
    restorer

theorem SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedSpec_of_windowMaterializerAndRestorer
    {materializer scanner restorer : MachineDescription}
    (hmaterializer :
      SelectedMergePaddedEmitterNestedLayoutWindowMaterializerSpec
        materializer)
    (hscanner :
      SelectedMergePaddedEmitterNestedLayoutWindowScannerSpec scanner)
    (hrestorer :
      SelectedMergePaddedEmitterNestedLayoutWindowRestorerSpec restorer) :
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedSpec
      (SelectedMergePaddedEmitterNestedLayoutWindowParser
        materializer scanner restorer) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        (SeqViaCanonical_subroutineReady
          hmaterializer.left
          hscanner.left)
        hrestorer.left
  · intro p
    have hscannerSeq :
        (SeqViaCanonical materializer
          scanner).HaltsFromTapeEquiv
          (SelectedMergePaddedEmitterAfterHitPaddedSourceFieldsTape p)
          (SelectedMergePaddedEmitterNestedLayoutContextParsedTape p) := by
      exact
        SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
          hmaterializer.left
          hscanner.left
          (hmaterializer.right p)
          (by
            rw [SelectedMergePaddedEmitterNestedLayoutContextRawSourceTape_move_left_move_right
              p]
            exact Tape.Equiv.refl _)
          (hscanner.right p).toEquiv
    exact
      SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
        (SeqViaCanonical_subroutineReady
          hmaterializer.left
          hscanner.left)
        hrestorer.left
        hscannerSeq
        (by
          rw [SelectedMergePaddedEmitterNestedLayoutContextParsedTape_move_left_move_right
            p]
          exact Tape.Equiv.refl _)
        (hrestorer.right p).toEquiv

theorem selectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction_of_windowMaterializerAndRestorer
    (h :
      SelectedMergePaddedEmitterNestedLayoutWindowMaterializerAndRestorerConstruction) :
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction := by
  rcases h with
    ⟨materializer, scanner, restorer,
      hmaterializer, hscanner, hrestorer⟩
  exact
    ⟨SelectedMergePaddedEmitterNestedLayoutWindowParser
        materializer scanner restorer,
      SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedSpec_of_windowMaterializerAndRestorer
        hmaterializer hscanner hrestorer⟩

theorem selectedMergePaddedEmitterNestedLayoutWindowMaterializerAndRestorerConstruction_of_parts
    (hmaterializer :
      SelectedMergePaddedEmitterNestedLayoutWindowMaterializerConstruction)
    (hscanner :
      SelectedMergePaddedEmitterNestedLayoutWindowScannerConstruction)
    (hrestorer :
      SelectedMergePaddedEmitterNestedLayoutWindowRestorerConstruction) :
    SelectedMergePaddedEmitterNestedLayoutWindowMaterializerAndRestorerConstruction := by
  rcases hmaterializer with ⟨materializer, hmaterializerSpec⟩
  rcases hscanner with ⟨scanner, hscannerSpec⟩
  rcases hrestorer with ⟨restorer, hrestorerSpec⟩
  exact
    ⟨materializer, scanner, restorer, hmaterializerSpec,
      hscannerSpec, hrestorerSpec⟩

/--
Finite-machine obligation that exposes the nested raw layout field from the
restored outer source fields.
-/
theorem selectedMergePaddedEmitterNestedLayoutWindowMaterializerConstruction :
    SelectedMergePaddedEmitterNestedLayoutWindowMaterializerConstruction := by
  sorry

/--
Finite-machine obligation that scans the contextual nested layout window while
preserving the outer simulator suffix.
-/
theorem selectedMergePaddedEmitterNestedLayoutWindowScannerConstruction :
    SelectedMergePaddedEmitterNestedLayoutWindowScannerConstruction := by
  sorry

/--
Finite-machine obligation that restores the checked scanner result to the
parsed source-fields shape.
-/
theorem selectedMergePaddedEmitterNestedLayoutWindowRestorerConstruction :
    SelectedMergePaddedEmitterNestedLayoutWindowRestorerConstruction := by
  sorry

/--
Checked glue over the nested-layout materializer and restorer leaves.
-/
theorem selectedMergePaddedEmitterNestedLayoutWindowMaterializerAndRestorerConstruction :
    SelectedMergePaddedEmitterNestedLayoutWindowMaterializerAndRestorerConstruction := by
  exact
    selectedMergePaddedEmitterNestedLayoutWindowMaterializerAndRestorerConstruction_of_parts
      selectedMergePaddedEmitterNestedLayoutWindowMaterializerConstruction
      selectedMergePaddedEmitterNestedLayoutWindowScannerConstruction
      selectedMergePaddedEmitterNestedLayoutWindowRestorerConstruction

/--
Common finite-machine leaf that parses the nested layout code word after the
outer source fields have been restored.
-/
theorem selectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction :
    SelectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction := by
  exact
    selectedMergePaddedEmitterAfterHitPaddedNestedLayoutParsedConstruction_of_windowMaterializerAndRestorer
      selectedMergePaddedEmitterNestedLayoutWindowMaterializerAndRestorerConstruction

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
