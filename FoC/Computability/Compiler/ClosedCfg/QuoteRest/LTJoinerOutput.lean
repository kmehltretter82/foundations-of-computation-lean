import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTEmitterOutput
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTJoinerRuns

set_option doc.verso true

/-!
# Live-tail joiner output endpoints

This module records normalized-output views for the live-tail joiner tapes and
the assembly after-raw-tail-scan finisher.  The exact joiner construction still
targets the ordinary tape endpoint; these contracts are the weaker interface
needed when downstream composition only cares about the emitted word.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer

private theorem filterMap_id_comp_some_bool (w : Word Bool) :
    List.filterMap ((fun cell : Option Bool => cell) ∘ some) w = w := by
  simpa [Function.comp] using Tape.filterMap_id_map_some w

def rightBlankGapPayloadScanTargetNormalizedOutput
    (baseLeft : List (Option Bool)) (_gap : Nat)
    (current : Bool) (payloadRest : Word Bool)
    (padding : List (Option Bool)) : Word Bool :=
  List.append
    (List.filterMap (fun cell => cell) baseLeft.reverse)
    (List.append (current :: payloadRest)
      (List.filterMap (fun cell => cell) padding))

theorem rightBlankGapPayloadScanTargetTape_normalizedOutput
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool)
    (padding : List (Option Bool)) :
    Tape.normalizedOutput
        (CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape
          baseLeft gap current payloadRest padding) =
      rightBlankGapPayloadScanTargetNormalizedOutput
        baseLeft gap current payloadRest padding := by
  rw [Tape.normalizedOutput]
  rw [rightBlankGapPayloadScanTargetTape_cells]
  simp [rightBlankGapPayloadScanTargetNormalizedOutput,
    filterMap_id_comp_some_bool]

def mixedOptionCellQuoteLiveTailSeparatedNormalizedOutput
    (emittedPrefix rawTail quoteRest : Word Bool) : Word Bool :=
  List.append emittedPrefix (List.append rawTail quoteRest)

def mixedOptionCellQuoteLiveTailJoinedNormalizedOutput
    (emittedPrefix rawTail quoteRest : Word Bool) : Word Bool :=
  List.append emittedPrefix (List.append quoteRest rawTail)

theorem mixedOptionCellQuoteLiveTailSeparatedTape_normalizedOutput
    (emittedPrefix rawTail quoteRest : Word Bool) :
    Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailSeparatedTape
          emittedPrefix rawTail quoteRest) =
      mixedOptionCellQuoteLiveTailSeparatedNormalizedOutput
        emittedPrefix rawTail quoteRest := by
  cases rawTail with
  | nil =>
      rw [Tape.normalizedOutput]
      simp [mixedOptionCellQuoteLiveTailSeparatedTape, tapeAtCells,
        Tape.cells, mixedOptionCellQuoteLiveTailSeparatedNormalizedOutput,
        filterMap_id_comp_some_bool]
  | cons head rawTailRest =>
      rw [Tape.normalizedOutput]
      rw [mixedOptionCellQuoteLiveTailSeparatedTape_cells_cons]
      simp [mixedOptionCellQuoteLiveTailSeparatedNormalizedOutput,
        filterMap_id_comp_some_bool]

theorem mixedOptionCellQuoteLiveTailJoinedTape_normalizedOutput
    (emittedPrefix rawTail quoteRest : Word Bool) :
    Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailJoinedTape
          emittedPrefix rawTail quoteRest) =
      mixedOptionCellQuoteLiveTailJoinedNormalizedOutput
        emittedPrefix rawTail quoteRest := by
  rw [Tape.normalizedOutput]
  cases rawTail with
  | nil =>
      simp [mixedOptionCellQuoteLiveTailJoinedTape, tapeAtCells,
        Tape.cells, mixedOptionCellQuoteLiveTailJoinedNormalizedOutput,
        List.map_append, List.map_reverse,
        filterMap_id_comp_some_bool]
  | cons head rawTailRest =>
      rw [mixedOptionCellQuoteLiveTailJoinedTape_cells_cons]
      simp [mixedOptionCellQuoteLiveTailJoinedNormalizedOutput,
        filterMap_id_comp_some_bool]

theorem mixedOptionCellQuoteLiveTailSeparatedNormalizedOutput_eq_emitted_raw_quoteRest
    (emittedPrefix rawTail quoteRest : Word Bool) :
    mixedOptionCellQuoteLiveTailSeparatedNormalizedOutput
        emittedPrefix rawTail quoteRest =
      List.append emittedPrefix (List.append rawTail quoteRest) := by
  rfl

theorem mixedOptionCellQuoteLiveTailJoinedNormalizedOutput_eq_emitted_quoteRest_raw
    (emittedPrefix rawTail quoteRest : Word Bool) :
    mixedOptionCellQuoteLiveTailJoinedNormalizedOutput
        emittedPrefix rawTail quoteRest =
      List.append emittedPrefix (List.append quoteRest rawTail) := by
  rfl

def mixedOptionCellQuoteLiveTailJoinerFamilySourceTape
    {ι : Type}
    (emittedPrefix rawTail quoteRest : ι -> Word Bool)
    (p : ι) : Tape Bool :=
  mixedOptionCellQuoteLiveTailSeparatedTape
    (emittedPrefix p) (rawTail p) (quoteRest p)

def mixedOptionCellQuoteLiveTailJoinerFamilyTargetTape
    {ι : Type}
    (emittedPrefix rawTail quoteRest : ι -> Word Bool)
    (p : ι) : Tape Bool :=
  mixedOptionCellQuoteLiveTailJoinedTape
    (emittedPrefix p) (rawTail p) (quoteRest p)

def mixedOptionCellQuoteLiveTailJoinerFamilySourceOutput
    {ι : Type}
    (emittedPrefix rawTail quoteRest : ι -> Word Bool)
    (p : ι) : Word Bool :=
  mixedOptionCellQuoteLiveTailSeparatedNormalizedOutput
    (emittedPrefix p) (rawTail p) (quoteRest p)

def mixedOptionCellQuoteLiveTailJoinerFamilyTargetOutput
    {ι : Type}
    (emittedPrefix rawTail quoteRest : ι -> Word Bool)
    (p : ι) : Word Bool :=
  mixedOptionCellQuoteLiveTailJoinedNormalizedOutput
    (emittedPrefix p) (rawTail p) (quoteRest p)

theorem mixedOptionCellQuoteLiveTailJoinerFamilySourceTape_eq
    {ι : Type}
    (emittedPrefix rawTail quoteRest : ι -> Word Bool)
    (p : ι) :
    mixedOptionCellQuoteLiveTailJoinerFamilySourceTape
        emittedPrefix rawTail quoteRest p =
      mixedOptionCellQuoteLiveTailSeparatedTape
        (emittedPrefix p) (rawTail p) (quoteRest p) := by
  rfl

theorem mixedOptionCellQuoteLiveTailJoinerFamilyTargetTape_eq
    {ι : Type}
    (emittedPrefix rawTail quoteRest : ι -> Word Bool)
    (p : ι) :
    mixedOptionCellQuoteLiveTailJoinerFamilyTargetTape
        emittedPrefix rawTail quoteRest p =
      mixedOptionCellQuoteLiveTailJoinedTape
        (emittedPrefix p) (rawTail p) (quoteRest p) := by
  rfl

theorem mixedOptionCellQuoteLiveTailJoinerFamilySourceTape_normalizedOutput
    {ι : Type}
    (emittedPrefix rawTail quoteRest : ι -> Word Bool)
    (p : ι) :
    Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailJoinerFamilySourceTape
          emittedPrefix rawTail quoteRest p) =
      mixedOptionCellQuoteLiveTailJoinerFamilySourceOutput
        emittedPrefix rawTail quoteRest p := by
  rw [mixedOptionCellQuoteLiveTailJoinerFamilySourceTape,
    mixedOptionCellQuoteLiveTailJoinerFamilySourceOutput]
  exact
    mixedOptionCellQuoteLiveTailSeparatedTape_normalizedOutput
      (emittedPrefix p) (rawTail p) (quoteRest p)

theorem mixedOptionCellQuoteLiveTailJoinerFamilyTargetTape_normalizedOutput
    {ι : Type}
    (emittedPrefix rawTail quoteRest : ι -> Word Bool)
    (p : ι) :
    Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailJoinerFamilyTargetTape
          emittedPrefix rawTail quoteRest p) =
      mixedOptionCellQuoteLiveTailJoinerFamilyTargetOutput
        emittedPrefix rawTail quoteRest p := by
  rw [mixedOptionCellQuoteLiveTailJoinerFamilyTargetTape,
    mixedOptionCellQuoteLiveTailJoinerFamilyTargetOutput]
  exact
    mixedOptionCellQuoteLiveTailJoinedTape_normalizedOutput
      (emittedPrefix p) (rawTail p) (quoteRest p)

theorem MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestOutputSpec_subroutineReady
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestOutputSpec
        finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestOutputSpec_haltsFromTapeWithOutput
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestOutputSpec
        finish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    finish.HaltsFromTapeWithOutput
      (mixedOptionCellQuoteLiveTailSeparatedTape
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits))
      (Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailJoinedTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits))) :=
  hfinish.right w sourceRestBits stage

theorem MixedOptionCellQuoteLiveTailJoinerFamilyOutputSpec_subroutineReady
    {ι : Type}
    {emittedPrefix rawTail quoteRest : ι -> Word Bool}
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailJoinerFamilyOutputSpec
        emittedPrefix rawTail quoteRest finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem MixedOptionCellQuoteLiveTailJoinerFamilyOutputSpec_haltsFromTapeWithOutput
    {ι : Type}
    {emittedPrefix rawTail quoteRest : ι -> Word Bool}
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailJoinerFamilyOutputSpec
        emittedPrefix rawTail quoteRest finish)
    (p : ι) :
    finish.HaltsFromTapeWithOutput
      (mixedOptionCellQuoteLiveTailSeparatedTape
        (emittedPrefix p) (rawTail p) (quoteRest p))
      (Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailJoinedTape
          (emittedPrefix p) (rawTail p) (quoteRest p))) :=
  hfinish.right p

theorem MixedOptionCellQuoteLiveTailJoinerFamilyOutputSpec_haltsFromFamilyTapeWithTargetOutput
    {ι : Type}
    {emittedPrefix rawTail quoteRest : ι -> Word Bool}
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailJoinerFamilyOutputSpec
        emittedPrefix rawTail quoteRest finish)
    (p : ι) :
    finish.HaltsFromTapeWithOutput
      (mixedOptionCellQuoteLiveTailJoinerFamilySourceTape
        emittedPrefix rawTail quoteRest p)
      (mixedOptionCellQuoteLiveTailJoinerFamilyTargetOutput
        emittedPrefix rawTail quoteRest p) := by
  rw [mixedOptionCellQuoteLiveTailJoinerFamilySourceTape]
  rw [← mixedOptionCellQuoteLiveTailJoinerFamilyTargetTape_normalizedOutput]
  exact hfinish.right p

def assemblySourceRestFinishSeparatedOutput
    (w sourceRestBits : Word Bool) (stage : Nat) : Word Bool :=
  List.append
    (assemblySourceRestFinishPrefixQuoteOutputBits w sourceRestBits stage)
    (List.append
      (assemblySourceRestFinishRawTailBits sourceRestBits stage)
      (preservingCellPassCellBits sourceRestBits))

def assemblySourceRestFinishJoinedOutput
    (w sourceRestBits : Word Bool) (stage : Nat) : Word Bool :=
  List.append
    (assemblySourceRestFinishPrefixQuoteOutputBits w sourceRestBits stage)
    (List.append
      (preservingCellPassCellBits sourceRestBits)
      (assemblySourceRestFinishRawTailBits sourceRestBits stage))

theorem assemblySourceRestFinishSeparatedOutput_eq_joinerSource
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishSeparatedOutput w sourceRestBits stage =
      mixedOptionCellQuoteLiveTailSeparatedNormalizedOutput
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits) := by
  rfl

theorem assemblySourceRestFinishJoinedOutput_eq_joinerTarget
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishJoinedOutput w sourceRestBits stage =
      mixedOptionCellQuoteLiveTailJoinedNormalizedOutput
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits) := by
  rfl

theorem mixedOptionCellQuoteLiveTailSeparatedTape_normalizedOutput_assembly
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailSeparatedTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits)) =
      assemblySourceRestFinishSeparatedOutput
        w sourceRestBits stage := by
  rw [mixedOptionCellQuoteLiveTailSeparatedTape_normalizedOutput]
  rfl

theorem mixedOptionCellQuoteLiveTailJoinedTape_normalizedOutput_assembly
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailJoinedTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits)) =
      assemblySourceRestFinishJoinedOutput
        w sourceRestBits stage := by
  rw [mixedOptionCellQuoteLiveTailJoinedTape_normalizedOutput]
  rfl

theorem MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestOutputSpec_haltsFromTapeWithJoinedOutput
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestOutputSpec
        finish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    finish.HaltsFromTapeWithOutput
      (mixedOptionCellQuoteLiveTailSeparatedTape
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage)
        (preservingCellPassCellBits sourceRestBits))
      (assemblySourceRestFinishJoinedOutput w sourceRestBits stage) := by
  rw [← mixedOptionCellQuoteLiveTailJoinedTape_normalizedOutput_assembly]
  exact hfinish.right w sourceRestBits stage

theorem mixedOptionCellQuoteLiveTailSeparatedTape_normalizedOutput_eq_emitterTargetTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailSeparatedTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits)) =
      Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailEmitterTargetTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits)) := by
  rw [mixedOptionCellQuoteLiveTailSeparatedTape_normalizedOutput_assembly]
  rw [mixedOptionCellQuoteLiveTailEmitterTargetTape_normalizedOutput_assembly]
  rfl

theorem MixedParserStackWholeSourceAfterRawTailScanTape_normalizedOutput
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (MixedParserStackWholeSourceAfterRawTailScanTape
          w sourceRestBits stage) =
      assemblySourceRestFinishSeparatedOutput
        w sourceRestBits stage := by
  rw [
    MixedParserStackWholeSourceAfterRawTailScanTape_eq_mixedOptionCellQuoteLiveTailSeparatedTape]
  exact
    mixedOptionCellQuoteLiveTailSeparatedTape_normalizedOutput_assembly
      w sourceRestBits stage

theorem MixedParserStackWholeSourceAfterRawTailScanTape_normalizedOutput_eq_separatedTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (MixedParserStackWholeSourceAfterRawTailScanTape
          w sourceRestBits stage) =
      Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailSeparatedTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits)) := by
  rw [
    MixedParserStackWholeSourceAfterRawTailScanTape_eq_mixedOptionCellQuoteLiveTailSeparatedTape]

theorem MixedParserStackWholeSourceAfterRawTailScanTape_normalizedOutput_eq_prefixQuotedSeparatedTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (MixedParserStackWholeSourceAfterRawTailScanTape
          w sourceRestBits stage) =
      Tape.normalizedOutput
        (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
          w sourceRestBits stage) := by
  rw [MixedParserStackWholeSourceAfterRawTailScanTape_normalizedOutput]
  rw [MixedParserStackWholeSourcePrefixQuotedSeparatedTape_normalizedOutput]
  rfl

theorem MixedParserStackRewriterWholeSourceTargetTape_normalizedOutput_eq_joinedTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (MixedParserStackRewriterWholeSourceTargetTape
          (MixedParserStackRewriterTrueSourceCells
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)) =
      Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailJoinedTape
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits)) := by
  rw [MixedParserStackRewriterWholeSourceTargetTape_eq_quoteRestJoinedTape]
  rw [← mixedOptionCellQuoteLiveTailJoinedTape_eq_assemblyQuoteRestJoinedTape]

theorem MixedParserStackRewriterWholeSourceTargetTape_normalizedOutput
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (MixedParserStackRewriterWholeSourceTargetTape
          (MixedParserStackRewriterTrueSourceCells
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)) =
      assemblySourceRestFinishJoinedOutput
        w sourceRestBits stage := by
  rw [
    MixedParserStackRewriterWholeSourceTargetTape_normalizedOutput_eq_joinedTape,
    mixedOptionCellQuoteLiveTailJoinedTape_normalizedOutput_assembly]

theorem MixedParserStackRewriterWholeSourceTargetTape_normalizedOutput_eq_targetTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.normalizedOutput
        (MixedParserStackRewriterWholeSourceTargetTape
          (MixedParserStackRewriterTrueSourceCells
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage)) =
      Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) := by
  rw [MixedParserStackRewriterWholeSourceTargetTape_eq_quoteRestJoinedTape]
  rw [assemblySourceRestFinishQuoteRestJoinedTape_eq_targetTape]

theorem assemblySourceRestFinishJoinedOutput_eq_targetTape_normalizedOutput
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishJoinedOutput w sourceRestBits stage =
      Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) := by
  rw [← MixedParserStackRewriterWholeSourceTargetTape_normalizedOutput]
  rw [MixedParserStackRewriterWholeSourceTargetTape_normalizedOutput_eq_targetTape]

theorem assemblySourceRestFinishJoinedOutput_eq_targetTape_namedOutput
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishJoinedOutput w sourceRestBits stage =
      List.append
        (assemblySourceRestFinishTargetPrefixBits
          w sourceRestBits stage)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits) := by
  rw [assemblySourceRestFinishJoinedOutput_eq_targetTape_normalizedOutput]
  rw [assemblySourceRestFinishTargetTape_normalizedOutput]

def MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestOutputSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTapeWithOutput
        (MixedParserStackWholeSourceAfterRawTailScanTape
          w sourceRestBits stage)
        (Tape.normalizedOutput
          (MixedParserStackRewriterWholeSourceTargetTape
            (MixedParserStackRewriterTrueSourceCells
              w sourceRestBits stage)
            (assemblySourceRestFinishRawTailBits sourceRestBits stage)))

def MixedParserStackAfterRawTailScanJoinFinisherOutputConstructionForAssemblySourceRest :
    Prop :=
  exists finish : MachineDescription,
    MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestOutputSpec
      finish

theorem MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestOutputSpec_subroutineReady
    {finish : MachineDescription}
    (hfinish :
      MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestOutputSpec
        finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestOutputSpec_haltsFromTapeWithOutput
    {finish : MachineDescription}
    (hfinish :
      MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestOutputSpec
        finish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    finish.HaltsFromTapeWithOutput
      (MixedParserStackWholeSourceAfterRawTailScanTape
        w sourceRestBits stage)
      (Tape.normalizedOutput
        (MixedParserStackRewriterWholeSourceTargetTape
          (MixedParserStackRewriterTrueSourceCells
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage))) :=
  hfinish.right w sourceRestBits stage

theorem MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestOutputSpec_haltsFromTapeWithJoinedOutput
    {finish : MachineDescription}
    (hfinish :
      MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestOutputSpec
        finish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    finish.HaltsFromTapeWithOutput
      (MixedParserStackWholeSourceAfterRawTailScanTape
        w sourceRestBits stage)
      (assemblySourceRestFinishJoinedOutput w sourceRestBits stage) := by
  rw [← MixedParserStackRewriterWholeSourceTargetTape_normalizedOutput]
  exact hfinish.right w sourceRestBits stage

theorem MixedParserStackAfterRawTailScanJoinFinisherOutputConstructionForAssemblySourceRest_of_mixedOptionCellQuoteLiveTailJoinerOutput
    (hjoin :
      MixedOptionCellQuoteLiveTailJoinerOutputConstructionForAssemblySourceRest) :
    MixedParserStackAfterRawTailScanJoinFinisherOutputConstructionForAssemblySourceRest := by
  rcases hjoin with ⟨finish, hfinish⟩
  refine ⟨finish, hfinish.left, ?_⟩
  intro w sourceRestBits stage
  rw [
    MixedParserStackWholeSourceAfterRawTailScanTape_eq_mixedOptionCellQuoteLiveTailSeparatedTape]
  rw [MixedParserStackRewriterWholeSourceTargetTape_eq_quoteRestJoinedTape]
  rw [← mixedOptionCellQuoteLiveTailJoinedTape_eq_assemblyQuoteRestJoinedTape]
  exact hfinish.right w sourceRestBits stage

theorem MixedParserStackAfterRawTailScanJoinFinisherOutputConstructionForAssemblySourceRest_of_mixedOptionCellQuoteLiveTailJoiner
    (hjoin :
      MixedOptionCellQuoteLiveTailJoinerConstructionForAssemblySourceRest) :
    MixedParserStackAfterRawTailScanJoinFinisherOutputConstructionForAssemblySourceRest :=
  MixedParserStackAfterRawTailScanJoinFinisherOutputConstructionForAssemblySourceRest_of_mixedOptionCellQuoteLiveTailJoinerOutput
    (MixedOptionCellQuoteLiveTailJoinerOutputConstructionForAssemblySourceRest_of_exact
      hjoin)

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
