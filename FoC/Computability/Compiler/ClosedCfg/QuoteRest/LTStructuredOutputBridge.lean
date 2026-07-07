import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTEmitterOutput
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTJoinerOutput
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTEmitterStructuredQuote
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTJoinerStructuredRestore

set_option doc.verso true

/-!
# Structured live-tail output bridge

This module packages the structured live-tail emitter and joiner facts around
the assembly parameter family used by the source-rest finisher.  The structured
descriptions already prove the relevant run-level facts; this file gives those
facts stable output-facing names and records the precise ordinary
{lit}`MachineDescription` obligations still needed by the executable construction
leaves.
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

/-! ## Structured emitter assembly views -/

def structuredLiveTailEmitterAssemblyInputBits
    (p : AssemblySourceRestLiveTailEmitterParam) : Word Bool :=
  assemblySourceRestFinishSourceBits p.w p.sourceRestBits p.stage

def structuredLiveTailEmitterAssemblyOutputPrefix
    (p : AssemblySourceRestLiveTailEmitterParam) : Word Bool :=
  assemblySourceRestFinishTargetPrefixBits p.w p.sourceRestBits p.stage

def structuredLiveTailEmitterAssemblyInitialConfig
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) : Structured.Configuration :=
  structuredMixedOptionCellQuoteLiveTailCountConfig
    0 [] (structuredLiveTailEmitterAssemblyInputBits p) 0 outputBits

def structuredLiveTailEmitterAssemblyRunSteps
    (p : AssemblySourceRestLiveTailEmitterParam) : Nat :=
  structuredMixedOptionCellQuoteLiveTailEmitterFullSourceSteps
    (structuredLiveTailEmitterAssemblyInputBits p)

def structuredLiveTailEmitterAssemblyOutputBits
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) : Word Bool :=
  List.append outputBits
    (structuredLiveTailEmitterAssemblyOutputPrefix p)

def structuredLiveTailEmitterAssemblyFinalConfig
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) : Structured.Configuration :=
  structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
    499
    (structuredLiveTailEmitterAssemblyInputBits p).reverse
    []
    (structuredLiveTailEmitterAssemblyInputBits p).length
    (structuredLiveTailEmitterAssemblyOutputBits p outputBits)

def structuredLiveTailEmitterAssemblySourceTape
    (p : AssemblySourceRestLiveTailEmitterParam) : Tape Bool :=
  mixedOptionCellQuoteLiveTailEmitterSplitSourceTape
    (assemblySourceRestLiveTailEmitterLeftRev p)
    (assemblySourceRestLiveTailEmitterQuoteScan p)
    (assemblySourceRestLiveTailEmitterRawTail p)
    (assemblySourceRestLiveTailEmitterQuoteRest p)

def structuredLiveTailEmitterAssemblyTargetTape
    (p : AssemblySourceRestLiveTailEmitterParam) : Tape Bool :=
  mixedOptionCellQuoteLiveTailEmitterTargetTape
    (assemblySourceRestLiveTailEmitterEmittedPrefix p)
    (assemblySourceRestLiveTailEmitterRawTail p)
    (assemblySourceRestLiveTailEmitterQuoteRest p)

def structuredLiveTailEmitterAssemblySourceOutput
    (p : AssemblySourceRestLiveTailEmitterParam) : Word Bool :=
  mixedOptionCellQuoteLiveTailEmitterSplitSourceNormalizedOutput
    (assemblySourceRestLiveTailEmitterLeftRev p)
    (assemblySourceRestLiveTailEmitterQuoteScan p)
    (assemblySourceRestLiveTailEmitterRawTail p)
    (assemblySourceRestLiveTailEmitterQuoteRest p)

def structuredLiveTailEmitterAssemblyTargetOutput
    (p : AssemblySourceRestLiveTailEmitterParam) : Word Bool :=
  mixedOptionCellQuoteLiveTailEmitterTargetNormalizedOutput
    (assemblySourceRestLiveTailEmitterEmittedPrefix p)
    (assemblySourceRestLiveTailEmitterRawTail p)
    (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredLiveTailEmitterAssemblyInputBits_eq
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailEmitterAssemblyInputBits p =
      assemblySourceRestFinishSourceBits
        p.w p.sourceRestBits p.stage := by
  rfl

theorem structuredLiveTailEmitterAssemblyOutputPrefix_eq
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailEmitterAssemblyOutputPrefix p =
      assemblySourceRestFinishTargetPrefixBits
        p.w p.sourceRestBits p.stage := by
  rfl

theorem structuredLiveTailEmitterAssemblyOutputPrefix_eq_emitted_quoteRest
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailEmitterAssemblyOutputPrefix p =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) :=
  assemblySourceRestLiveTailEmitterTargetPrefixBits_eq_emitted_quoteRest p

theorem structuredLiveTailEmitterAssemblyOutputBits_eq_append_prefix
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) :
    structuredLiveTailEmitterAssemblyOutputBits p outputBits =
      List.append outputBits
        (structuredLiveTailEmitterAssemblyOutputPrefix p) := by
  rfl

theorem structuredLiveTailEmitterAssemblyOutputBits_eq_append_emitted_quoteRest
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) :
    structuredLiveTailEmitterAssemblyOutputBits p outputBits =
      List.append outputBits
        (List.append
          (assemblySourceRestLiveTailEmitterEmittedPrefix p)
          (assemblySourceRestLiveTailEmitterQuoteRest p)) := by
  rw [structuredLiveTailEmitterAssemblyOutputBits,
    structuredLiveTailEmitterAssemblyOutputPrefix_eq_emitted_quoteRest]

theorem structuredLiveTailEmitterAssemblyOutputBits_eq_output_emitted_quoteRest
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) :
    structuredLiveTailEmitterAssemblyOutputBits p outputBits =
      List.append
        (List.append outputBits
          (assemblySourceRestLiveTailEmitterEmittedPrefix p))
        (assemblySourceRestLiveTailEmitterQuoteRest p) := by
  rw [structuredLiveTailEmitterAssemblyOutputBits_eq_append_emitted_quoteRest]
  simp [List.append_assoc]

theorem structuredLiveTailEmitterAssemblyInitialConfig_eq
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) :
    structuredLiveTailEmitterAssemblyInitialConfig p outputBits =
      structuredMixedOptionCellQuoteLiveTailCountConfig
        0 []
        (assemblySourceRestFinishSourceBits
          p.w p.sourceRestBits p.stage)
        0 outputBits := by
  rfl

theorem structuredLiveTailEmitterAssemblyRunSteps_eq
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailEmitterAssemblyRunSteps p =
      structuredMixedOptionCellQuoteLiveTailEmitterFullSourceSteps
        (assemblySourceRestFinishSourceBits
          p.w p.sourceRestBits p.stage) := by
  rfl

theorem structuredLiveTailEmitterAssemblyFinalConfig_eq
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) :
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
            p.w p.sourceRestBits p.stage)) := by
  rfl

theorem structuredLiveTailEmitterAssemblyFinalConfig_eq_emitted_quoteRest
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) :
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
            (assemblySourceRestLiveTailEmitterQuoteRest p))) := by
  rw [structuredLiveTailEmitterAssemblyFinalConfig_eq,
    assemblySourceRestLiveTailEmitterTargetPrefixBits_eq_emitted_quoteRest]

theorem structuredLiveTailEmitterAssemblySourceTape_eq_family
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailEmitterAssemblySourceTape p =
      mixedOptionCellQuoteLiveTailEmitterFamilySourceTape
        assemblySourceRestLiveTailEmitterLeftRev
        assemblySourceRestLiveTailEmitterQuoteScan
        assemblySourceRestLiveTailEmitterRawTail
        assemblySourceRestLiveTailEmitterQuoteRest
        p := by
  rfl

theorem structuredLiveTailEmitterAssemblyTargetTape_eq_family
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailEmitterAssemblyTargetTape p =
      mixedOptionCellQuoteLiveTailEmitterFamilyTargetTape
        assemblySourceRestLiveTailEmitterRawTail
        assemblySourceRestLiveTailEmitterQuoteRest
        assemblySourceRestLiveTailEmitterEmittedPrefix
        p := by
  rfl

theorem structuredLiveTailEmitterAssemblySourceOutput_eq_family
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailEmitterAssemblySourceOutput p =
      mixedOptionCellQuoteLiveTailEmitterFamilySourceOutput
        assemblySourceRestLiveTailEmitterLeftRev
        assemblySourceRestLiveTailEmitterQuoteScan
        assemblySourceRestLiveTailEmitterRawTail
        assemblySourceRestLiveTailEmitterQuoteRest
        p := by
  rfl

theorem structuredLiveTailEmitterAssemblyTargetOutput_eq_family
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailEmitterAssemblyTargetOutput p =
      mixedOptionCellQuoteLiveTailEmitterFamilyTargetOutput
        assemblySourceRestLiveTailEmitterRawTail
        assemblySourceRestLiveTailEmitterQuoteRest
        assemblySourceRestLiveTailEmitterEmittedPrefix
        p := by
  rfl

theorem structuredLiveTailEmitterAssemblySourceTape_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (structuredLiveTailEmitterAssemblySourceTape p) =
      structuredLiveTailEmitterAssemblySourceOutput p := by
  rw [structuredLiveTailEmitterAssemblySourceTape,
    structuredLiveTailEmitterAssemblySourceOutput]
  exact
    mixedOptionCellQuoteLiveTailEmitterSplitSourceTape_normalizedOutput
      (assemblySourceRestLiveTailEmitterLeftRev p)
      (assemblySourceRestLiveTailEmitterQuoteScan p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredLiveTailEmitterAssemblyTargetTape_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (structuredLiveTailEmitterAssemblyTargetTape p) =
      structuredLiveTailEmitterAssemblyTargetOutput p := by
  rw [structuredLiveTailEmitterAssemblyTargetTape,
    structuredLiveTailEmitterAssemblyTargetOutput]
  exact
    mixedOptionCellQuoteLiveTailEmitterTargetTape_normalizedOutput
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredLiveTailEmitterAssemblyTargetOutput_eq_prefixQuotedSeparated
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailEmitterAssemblyTargetOutput p =
      assemblySourceRestFinishPrefixQuotedSeparatedOutput
        p.w p.sourceRestBits p.stage := by
  cases p with
  | mk w sourceRestBits stage =>
      rfl

theorem structuredLiveTailEmitterAssemblyTargetTape_normalizedOutput_eq_prefixQuotedSeparated
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (structuredLiveTailEmitterAssemblyTargetTape p) =
      assemblySourceRestFinishPrefixQuotedSeparatedOutput
        p.w p.sourceRestBits p.stage := by
  rw [structuredLiveTailEmitterAssemblyTargetTape_normalizedOutput,
    structuredLiveTailEmitterAssemblyTargetOutput_eq_prefixQuotedSeparated]

def StructuredLiveTailEmitterAssemblyOutputSpec
    (D : Structured.Description) : Prop :=
  StructuredMixedOptionCellQuoteLiveTailEmitterAssemblyTargetPrefixSpec D ∧
    forall (p : AssemblySourceRestLiveTailEmitterParam)
      (outputBits : Word Bool),
      D.runConfig
          (structuredLiveTailEmitterAssemblyRunSteps p)
          (structuredLiveTailEmitterAssemblyInitialConfig p outputBits) =
        structuredLiveTailEmitterAssemblyFinalConfig p outputBits

theorem StructuredLiveTailEmitterAssemblyOutputSpec.targetPrefix
    {D : Structured.Description}
    (hD : StructuredLiveTailEmitterAssemblyOutputSpec D) :
    StructuredMixedOptionCellQuoteLiveTailEmitterAssemblyTargetPrefixSpec D :=
  hD.left

theorem StructuredLiveTailEmitterAssemblyOutputSpec.fullSource
    {D : Structured.Description}
    (hD : StructuredLiveTailEmitterAssemblyOutputSpec D) :
    StructuredMixedOptionCellQuoteLiveTailEmitterFullSourceSpec D :=
  hD.targetPrefix.left

theorem StructuredLiveTailEmitterAssemblyOutputSpec.supported
    {D : Structured.Description}
    (hD : StructuredLiveTailEmitterAssemblyOutputSpec D) :
    Structured.MultiTapeLowering.SupportsReadWriteRows3 D :=
  hD.targetPrefix.supported

theorem StructuredLiveTailEmitterAssemblyOutputSpec.run
    {D : Structured.Description}
    (hD : StructuredLiveTailEmitterAssemblyOutputSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) :
    D.runConfig
        (structuredLiveTailEmitterAssemblyRunSteps p)
        (structuredLiveTailEmitterAssemblyInitialConfig p outputBits) =
      structuredLiveTailEmitterAssemblyFinalConfig p outputBits :=
  hD.right p outputBits

theorem StructuredLiveTailEmitterAssemblyOutputSpec.run_wsource
    {D : Structured.Description}
    (hD : StructuredLiveTailEmitterAssemblyOutputSpec D)
    (w sourceRestBits outputBits : Word Bool) (stage : Nat) :
    D.runConfig
        (structuredMixedOptionCellQuoteLiveTailEmitterFullSourceSteps
          (assemblySourceRestFinishSourceBits w sourceRestBits stage))
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 [] (assemblySourceRestFinishSourceBits w sourceRestBits stage)
          0 outputBits) =
      structuredMixedOptionCellQuoteLiveTailCellPassAfterRewindConfig
        499
        (assemblySourceRestFinishSourceBits w sourceRestBits stage).reverse
        []
        (assemblySourceRestFinishSourceBits w sourceRestBits stage).length
        (List.append outputBits
          (assemblySourceRestFinishTargetPrefixBits
            w sourceRestBits stage)) := by
  simpa [
    structuredLiveTailEmitterAssemblyRunSteps,
    structuredLiveTailEmitterAssemblyInitialConfig,
    structuredLiveTailEmitterAssemblyFinalConfig,
    structuredLiveTailEmitterAssemblyInputBits,
    structuredLiveTailEmitterAssemblyOutputBits,
    structuredLiveTailEmitterAssemblyOutputPrefix]
    using
      hD.run
        { w := w, sourceRestBits := sourceRestBits, stage := stage }
        outputBits

theorem StructuredLiveTailEmitterAssemblyOutputSpec.run_emitted_quoteRest
    {D : Structured.Description}
    (hD : StructuredLiveTailEmitterAssemblyOutputSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam)
    (outputBits : Word Bool) :
    D.runConfig
        (structuredLiveTailEmitterAssemblyRunSteps p)
        (structuredLiveTailEmitterAssemblyInitialConfig p outputBits) =
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
            (assemblySourceRestLiveTailEmitterQuoteRest p))) := by
  rw [hD.run p outputBits]
  rw [structuredLiveTailEmitterAssemblyFinalConfig_eq_emitted_quoteRest]

theorem StructuredLiveTailEmitterAssemblyOutputSpec_of_targetPrefix
    {D : Structured.Description}
    (hD :
      StructuredMixedOptionCellQuoteLiveTailEmitterAssemblyTargetPrefixSpec
        D) :
    StructuredLiveTailEmitterAssemblyOutputSpec D := by
  refine ⟨hD, ?_⟩
  intro p outputBits
  cases p with
  | mk w sourceRestBits stage =>
      simpa [
        structuredLiveTailEmitterAssemblyRunSteps,
        structuredLiveTailEmitterAssemblyInitialConfig,
        structuredLiveTailEmitterAssemblyFinalConfig,
        structuredLiveTailEmitterAssemblyInputBits,
        structuredLiveTailEmitterAssemblyOutputBits,
        structuredLiveTailEmitterAssemblyOutputPrefix]
        using hD.run w sourceRestBits outputBits stage

theorem structuredMixedOptionCellQuoteLiveTailEmitterDescription_structuredAssemblyOutputSpec :
    StructuredLiveTailEmitterAssemblyOutputSpec
      structuredMixedOptionCellQuoteLiveTailEmitterDescription :=
  StructuredLiveTailEmitterAssemblyOutputSpec_of_targetPrefix
    structuredMixedOptionCellQuoteLiveTailEmitterDescription_assemblyTargetPrefixSpec

/-! ## Structured joiner assembly views -/

def structuredLiveTailJoinerAssemblyInitialConfig
    (p : AssemblySourceRestLiveTailEmitterParam) : Structured.Configuration :=
  structuredRawTailInsertionJoinerInitialConfig p

def structuredLiveTailJoinerAssemblyRunFuel
    (p : AssemblySourceRestLiveTailEmitterParam) : Nat :=
  Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.runFuel
    (assemblySourceRestLiveTailEmitterRawTail p)
    (assemblySourceRestLiveTailEmitterQuoteRest p)

def structuredLiveTailJoinerAssemblyRunConfig
    (D : Structured.Description)
    (p : AssemblySourceRestLiveTailEmitterParam) : Structured.Configuration :=
  structuredRawTailInsertionJoinerAssemblyRunConfig D p

def structuredLiveTailJoinerAssemblySourceTape
    (p : AssemblySourceRestLiveTailEmitterParam) : Tape Bool :=
  mixedOptionCellQuoteLiveTailSeparatedTape
    (assemblySourceRestLiveTailEmitterEmittedPrefix p)
    (assemblySourceRestLiveTailEmitterRawTail p)
    (assemblySourceRestLiveTailEmitterQuoteRest p)

def structuredLiveTailJoinerAssemblyTargetTape
    (p : AssemblySourceRestLiveTailEmitterParam) : Tape Bool :=
  mixedOptionCellQuoteLiveTailJoinedTape
    (assemblySourceRestLiveTailEmitterEmittedPrefix p)
    (assemblySourceRestLiveTailEmitterRawTail p)
    (assemblySourceRestLiveTailEmitterQuoteRest p)

def structuredLiveTailJoinerAssemblySourceOutput
    (p : AssemblySourceRestLiveTailEmitterParam) : Word Bool :=
  mixedOptionCellQuoteLiveTailSeparatedNormalizedOutput
    (assemblySourceRestLiveTailEmitterEmittedPrefix p)
    (assemblySourceRestLiveTailEmitterRawTail p)
    (assemblySourceRestLiveTailEmitterQuoteRest p)

def structuredLiveTailJoinerAssemblyTargetOutput
    (p : AssemblySourceRestLiveTailEmitterParam) : Word Bool :=
  mixedOptionCellQuoteLiveTailJoinedNormalizedOutput
    (assemblySourceRestLiveTailEmitterEmittedPrefix p)
    (assemblySourceRestLiveTailEmitterRawTail p)
    (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredLiveTailJoinerAssemblyInitialConfig_eq
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblyInitialConfig p =
      structuredRawTailInsertionJoinerInitialConfig p := by
  rfl

theorem structuredLiveTailJoinerAssemblyRunFuel_eq
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblyRunFuel p =
      Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.runFuel
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) := by
  rfl

theorem structuredLiveTailJoinerAssemblyRunConfig_eq
    (D : Structured.Description)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblyRunConfig D p =
      structuredRawTailInsertionJoinerAssemblyRunConfig D p := by
  rfl

theorem structuredLiveTailJoinerAssemblySourceTape_eq
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblySourceTape p =
      mixedOptionCellQuoteLiveTailSeparatedTape
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) := by
  rfl

theorem structuredLiveTailJoinerAssemblyTargetTape_eq
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblyTargetTape p =
      mixedOptionCellQuoteLiveTailJoinedTape
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) := by
  rfl

theorem structuredLiveTailJoinerAssemblySourceTape_eq_afterRawTailScan
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblySourceTape p =
      MixedParserStackWholeSourceAfterRawTailScanTape
        p.w p.sourceRestBits p.stage :=
  assemblySourceRestLiveTailJoinerSeparatedTape_eq_afterRawTailScanTape p

theorem structuredLiveTailJoinerAssemblyTargetTape_eq_finishTarget
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblyTargetTape p =
      assemblySourceRestFinishTargetTape
        p.w p.sourceRestBits p.stage :=
  assemblySourceRestLiveTailJoinerJoinedTape_eq_targetTape p

theorem structuredLiveTailJoinerAssemblySourceTape_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (structuredLiveTailJoinerAssemblySourceTape p) =
      structuredLiveTailJoinerAssemblySourceOutput p := by
  rw [structuredLiveTailJoinerAssemblySourceTape,
    structuredLiveTailJoinerAssemblySourceOutput]
  exact
    mixedOptionCellQuoteLiveTailSeparatedTape_normalizedOutput
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredLiveTailJoinerAssemblyTargetTape_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (structuredLiveTailJoinerAssemblyTargetTape p) =
      structuredLiveTailJoinerAssemblyTargetOutput p := by
  rw [structuredLiveTailJoinerAssemblyTargetTape,
    structuredLiveTailJoinerAssemblyTargetOutput]
  exact
    mixedOptionCellQuoteLiveTailJoinedTape_normalizedOutput
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredLiveTailJoinerAssemblySourceOutput_eq_separated
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblySourceOutput p =
      assemblySourceRestFinishSeparatedOutput
        p.w p.sourceRestBits p.stage := by
  cases p with
  | mk w sourceRestBits stage =>
      rfl

theorem structuredLiveTailJoinerAssemblyTargetOutput_eq_joined
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblyTargetOutput p =
      assemblySourceRestFinishJoinedOutput
        p.w p.sourceRestBits p.stage := by
  cases p with
  | mk w sourceRestBits stage =>
      rfl

theorem structuredLiveTailJoinerAssemblyTargetOutput_eq_finishTargetOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredLiveTailJoinerAssemblyTargetOutput p =
      Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape
          p.w p.sourceRestBits p.stage) := by
  rw [structuredLiveTailJoinerAssemblyTargetOutput_eq_joined,
    assemblySourceRestFinishJoinedOutput_eq_targetTape_normalizedOutput]

theorem structuredLiveTailJoinerAssemblyTargetTape_normalizedOutput_eq_finishTarget
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (structuredLiveTailJoinerAssemblyTargetTape p) =
      Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape
          p.w p.sourceRestBits p.stage) := by
  rw [structuredLiveTailJoinerAssemblyTargetTape_eq_finishTarget]

def StructuredLiveTailJoinerAssemblyOutputSpec
    (D : Structured.Description) : Prop :=
  StructuredRawTailInsertionJoinerAssemblyRestoreRunOutputSpec D ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (structuredLiveTailJoinerAssemblyRunConfig D p).tapes 0) =
        structuredLiveTailJoinerAssemblyTargetOutput p

theorem StructuredLiveTailJoinerAssemblyOutputSpec.restoreRun
    {D : Structured.Description}
    (hD : StructuredLiveTailJoinerAssemblyOutputSpec D) :
    StructuredRawTailInsertionJoinerAssemblyRestoreRunOutputSpec D :=
  hD.left

theorem StructuredLiveTailJoinerAssemblyOutputSpec.restore
    {D : Structured.Description}
    (hD : StructuredLiveTailJoinerAssemblyOutputSpec D) :
    StructuredRawTailInsertionJoinerAssemblyRestoreSpec D :=
  hD.restoreRun.restore

theorem StructuredLiveTailJoinerAssemblyOutputSpec.full
    {D : Structured.Description}
    (hD : StructuredLiveTailJoinerAssemblyOutputSpec D) :
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.FullSpec D :=
  hD.restore.full

theorem StructuredLiveTailJoinerAssemblyOutputSpec.output
    {D : Structured.Description}
    (hD : StructuredLiveTailJoinerAssemblyOutputSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredLiveTailJoinerAssemblyRunConfig D p).tapes 0) =
      structuredLiveTailJoinerAssemblyTargetOutput p :=
  hD.right p

theorem StructuredLiveTailJoinerAssemblyOutputSpec.output_finishTarget
    {D : Structured.Description}
    (hD : StructuredLiveTailJoinerAssemblyOutputSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredLiveTailJoinerAssemblyRunConfig D p).tapes 0) =
      Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape
          p.w p.sourceRestBits p.stage) := by
  rw [hD.output p,
    structuredLiveTailJoinerAssemblyTargetOutput_eq_finishTargetOutput]

theorem StructuredLiveTailJoinerAssemblyOutputSpec.output_joined
    {D : Structured.Description}
    (hD : StructuredLiveTailJoinerAssemblyOutputSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredLiveTailJoinerAssemblyRunConfig D p).tapes 0) =
      assemblySourceRestFinishJoinedOutput
        p.w p.sourceRestBits p.stage := by
  rw [hD.output p, structuredLiveTailJoinerAssemblyTargetOutput_eq_joined]

theorem StructuredLiveTailJoinerAssemblyOutputSpec_of_restoreRun
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreRunOutputSpec D) :
    StructuredLiveTailJoinerAssemblyOutputSpec D := by
  refine ⟨hD, ?_⟩
  intro p
  calc
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredLiveTailJoinerAssemblyRunConfig D p).tapes 0) =
      Tape.normalizedOutput
        (structuredLiveTailJoinerAssemblyTargetTape p) := by
        simpa [
          structuredLiveTailJoinerAssemblyRunConfig,
          structuredLiveTailJoinerAssemblyTargetTape]
          using hD.output p
    _ = structuredLiveTailJoinerAssemblyTargetOutput p := by
        exact structuredLiveTailJoinerAssemblyTargetTape_normalizedOutput p

theorem structuredRawTailInsertionJoinerDescription_structuredAssemblyOutputSpec :
    StructuredLiveTailJoinerAssemblyOutputSpec
      structuredRawTailInsertionJoinerDescription :=
  StructuredLiveTailJoinerAssemblyOutputSpec_of_restoreRun
    structuredRawTailInsertionJoinerDescription_assemblyRestoreRunOutputSpec

def StructuredLiveTailJoinerAssemblyTapeStateOutputSpec
    (D : Structured.Description) : Prop :=
  StructuredRawTailInsertionJoinerAssemblyRestoreRunTapeStateSpec D ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (structuredLiveTailJoinerAssemblyRunConfig D p).tapes 0) =
        structuredLiveTailJoinerAssemblyTargetOutput p ∧
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (structuredLiveTailJoinerAssemblyRunConfig D p).tapes 1) =
        assemblySourceRestLiveTailEmitterQuoteRest p ∧
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (structuredLiveTailJoinerAssemblyRunConfig D p).tapes 2) =
        []

theorem StructuredLiveTailJoinerAssemblyTapeStateOutputSpec.tapeState
    {D : Structured.Description}
    (hD : StructuredLiveTailJoinerAssemblyTapeStateOutputSpec D) :
    StructuredRawTailInsertionJoinerAssemblyRestoreRunTapeStateSpec D :=
  hD.left

theorem StructuredLiveTailJoinerAssemblyTapeStateOutputSpec.outputSpec
    {D : Structured.Description}
    (hD : StructuredLiveTailJoinerAssemblyTapeStateOutputSpec D) :
    StructuredLiveTailJoinerAssemblyOutputSpec D := by
  refine ⟨hD.tapeState.outputSpec, ?_⟩
  intro p
  exact (hD.right p).left

theorem StructuredLiveTailJoinerAssemblyTapeStateOutputSpec.source
    {D : Structured.Description}
    (hD : StructuredLiveTailJoinerAssemblyTapeStateOutputSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredLiveTailJoinerAssemblyRunConfig D p).tapes 0) =
      structuredLiveTailJoinerAssemblyTargetOutput p :=
  (hD.right p).left

theorem StructuredLiveTailJoinerAssemblyTapeStateOutputSpec.source_finishTarget
    {D : Structured.Description}
    (hD : StructuredLiveTailJoinerAssemblyTapeStateOutputSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredLiveTailJoinerAssemblyRunConfig D p).tapes 0) =
      Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape
          p.w p.sourceRestBits p.stage) :=
  hD.outputSpec.output_finishTarget p

theorem StructuredLiveTailJoinerAssemblyTapeStateOutputSpec.scratch
    {D : Structured.Description}
    (hD : StructuredLiveTailJoinerAssemblyTapeStateOutputSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredLiveTailJoinerAssemblyRunConfig D p).tapes 1) =
      assemblySourceRestLiveTailEmitterQuoteRest p :=
  (hD.right p).right.left

theorem StructuredLiveTailJoinerAssemblyTapeStateOutputSpec.work
    {D : Structured.Description}
    (hD : StructuredLiveTailJoinerAssemblyTapeStateOutputSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredLiveTailJoinerAssemblyRunConfig D p).tapes 2) =
      [] :=
  (hD.right p).right.right

theorem StructuredLiveTailJoinerAssemblyTapeStateOutputSpec_of_tapeState
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreRunTapeStateSpec D) :
    StructuredLiveTailJoinerAssemblyTapeStateOutputSpec D := by
  refine ⟨hD, ?_⟩
  intro p
  exact
    ⟨(StructuredLiveTailJoinerAssemblyOutputSpec_of_restoreRun
        hD.outputSpec).output p,
      by
        simpa [structuredLiveTailJoinerAssemblyRunConfig]
          using hD.scratch p,
      by
        simpa [structuredLiveTailJoinerAssemblyRunConfig]
          using hD.work p⟩

theorem structuredRawTailInsertionJoinerDescription_structuredAssemblyTapeStateOutputSpec :
    StructuredLiveTailJoinerAssemblyTapeStateOutputSpec
      structuredRawTailInsertionJoinerDescription :=
  StructuredLiveTailJoinerAssemblyTapeStateOutputSpec_of_tapeState
    structuredRawTailInsertionJoinerDescription_assemblyRestoreRunTapeStateSpec

/-! ## Combined structured route -/

def StructuredLiveTailAssemblyOutputRouteSpec
    (emitter joiner : Structured.Description) : Prop :=
  StructuredLiveTailEmitterAssemblyOutputSpec emitter ∧
    StructuredLiveTailJoinerAssemblyTapeStateOutputSpec joiner

theorem StructuredLiveTailAssemblyOutputRouteSpec.emitter
    {emitter joiner : Structured.Description}
    (h : StructuredLiveTailAssemblyOutputRouteSpec emitter joiner) :
    StructuredLiveTailEmitterAssemblyOutputSpec emitter :=
  h.left

theorem StructuredLiveTailAssemblyOutputRouteSpec.joinerTapeState
    {emitter joiner : Structured.Description}
    (h : StructuredLiveTailAssemblyOutputRouteSpec emitter joiner) :
    StructuredLiveTailJoinerAssemblyTapeStateOutputSpec joiner :=
  h.right

theorem StructuredLiveTailAssemblyOutputRouteSpec.joiner
    {emitter joiner : Structured.Description}
    (h : StructuredLiveTailAssemblyOutputRouteSpec emitter joiner) :
    StructuredLiveTailJoinerAssemblyOutputSpec joiner :=
  h.joinerTapeState.outputSpec

theorem StructuredLiveTailAssemblyOutputRouteSpec.emitter_supported
    {emitter joiner : Structured.Description}
    (h : StructuredLiveTailAssemblyOutputRouteSpec emitter joiner) :
    Structured.MultiTapeLowering.SupportsReadWriteRows3 emitter :=
  h.emitter.supported

theorem StructuredLiveTailAssemblyOutputRouteSpec.joiner_full
    {emitter joiner : Structured.Description}
    (h : StructuredLiveTailAssemblyOutputRouteSpec emitter joiner) :
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.FullSpec joiner :=
  h.joiner.full

theorem structuredLiveTailAssemblyOutputRouteSpec_descriptions :
    StructuredLiveTailAssemblyOutputRouteSpec
      structuredMixedOptionCellQuoteLiveTailEmitterDescription
      structuredRawTailInsertionJoinerDescription :=
  ⟨structuredMixedOptionCellQuoteLiveTailEmitterDescription_structuredAssemblyOutputSpec,
    structuredRawTailInsertionJoinerDescription_structuredAssemblyTapeStateOutputSpec⟩

/-! ## Ordinary output-family aliases -/

def StructuredLiveTailJoinerAssemblyFamilyOutputSpec
    (finish : MachineDescription) : Prop :=
  MixedOptionCellQuoteLiveTailJoinerFamilyOutputSpec
    assemblySourceRestLiveTailEmitterEmittedPrefix
    assemblySourceRestLiveTailEmitterRawTail
    assemblySourceRestLiveTailEmitterQuoteRest
    finish

def StructuredLiveTailJoinerAssemblyFamilyOutputConstruction :
    Prop :=
  MixedOptionCellQuoteLiveTailJoinerFamilyOutputConstruction
    assemblySourceRestLiveTailEmitterEmittedPrefix
    assemblySourceRestLiveTailEmitterRawTail
    assemblySourceRestLiveTailEmitterQuoteRest

theorem StructuredLiveTailJoinerAssemblyFamilyOutputSpec_subroutineReady
    {finish : MachineDescription}
    (hfinish :
      StructuredLiveTailJoinerAssemblyFamilyOutputSpec finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem StructuredLiveTailJoinerAssemblyFamilyOutputSpec_haltsFromTapeWithOutput
    {finish : MachineDescription}
    (hfinish :
      StructuredLiveTailJoinerAssemblyFamilyOutputSpec finish)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    finish.HaltsFromTapeWithOutput
      (structuredLiveTailJoinerAssemblySourceTape p)
      (Tape.normalizedOutput
        (structuredLiveTailJoinerAssemblyTargetTape p)) := by
  simpa [
    StructuredLiveTailJoinerAssemblyFamilyOutputSpec,
    structuredLiveTailJoinerAssemblySourceTape,
    structuredLiveTailJoinerAssemblyTargetTape]
    using hfinish.right p

theorem StructuredLiveTailJoinerAssemblyFamilyOutputSpec_haltsFromOutput
    {finish : MachineDescription}
    (hfinish :
      StructuredLiveTailJoinerAssemblyFamilyOutputSpec finish)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    finish.HaltsFromTapeWithOutput
      (structuredLiveTailJoinerAssemblySourceTape p)
      (structuredLiveTailJoinerAssemblyTargetOutput p) := by
  rw [← structuredLiveTailJoinerAssemblyTargetTape_normalizedOutput]
  exact
    StructuredLiveTailJoinerAssemblyFamilyOutputSpec_haltsFromTapeWithOutput
      hfinish p

theorem StructuredLiveTailJoinerAssemblyFamilyOutputSpec_iff_assemblyOutputSpec
    (finish : MachineDescription) :
    StructuredLiveTailJoinerAssemblyFamilyOutputSpec finish ↔
      MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestOutputSpec
        finish := by
  constructor
  · intro hfinish
    refine ⟨hfinish.left, ?_⟩
    intro w sourceRestBits stage
    exact hfinish.right
      { w := w, sourceRestBits := sourceRestBits, stage := stage }
  · intro hfinish
    refine ⟨hfinish.left, ?_⟩
    intro p
    cases p with
    | mk w sourceRestBits stage =>
        exact hfinish.right w sourceRestBits stage

theorem StructuredLiveTailJoinerOutputConstructionForAssemblySourceRest_of_outputFamily
    (h : StructuredLiveTailJoinerAssemblyFamilyOutputConstruction) :
    MixedOptionCellQuoteLiveTailJoinerOutputConstructionForAssemblySourceRest := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨finish,
      (StructuredLiveTailJoinerAssemblyFamilyOutputSpec_iff_assemblyOutputSpec
        finish).mp hfinish⟩

theorem StructuredLiveTailJoinerAssemblyFamilyOutputConstruction_of_assemblyOutput
    (h :
      MixedOptionCellQuoteLiveTailJoinerOutputConstructionForAssemblySourceRest) :
    StructuredLiveTailJoinerAssemblyFamilyOutputConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨finish,
      (StructuredLiveTailJoinerAssemblyFamilyOutputSpec_iff_assemblyOutputSpec
        finish).mpr hfinish⟩

theorem StructuredLiveTailJoinerAssemblyFamilyOutputConstruction_of_exact
    (h :
      MixedOptionCellQuoteLiveTailJoinerFamilyConstruction
        assemblySourceRestLiveTailEmitterEmittedPrefix
        assemblySourceRestLiveTailEmitterRawTail
        assemblySourceRestLiveTailEmitterQuoteRest) :
    StructuredLiveTailJoinerAssemblyFamilyOutputConstruction :=
  MixedOptionCellQuoteLiveTailJoinerFamilyOutputConstruction_of_exact h

/-! ## Structured-to-ordinary output bridge contracts -/

def StructuredLiveTailEmitterOrdinaryOutputBridgeSpec
    (structured : Structured.Description)
    (finish : MachineDescription) : Prop :=
  StructuredLiveTailEmitterAssemblyOutputSpec structured ∧
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec finish

def StructuredLiveTailJoinerOrdinaryOutputBridgeSpec
    (structured : Structured.Description)
    (finish : MachineDescription) : Prop :=
  StructuredLiveTailJoinerAssemblyOutputSpec structured ∧
    StructuredLiveTailJoinerAssemblyFamilyOutputSpec finish

def StructuredLiveTailOrdinaryOutputBridgeSpec
    (emitterStructured joinerStructured : Structured.Description)
    (emitterFinish joinerFinish : MachineDescription) : Prop :=
  StructuredLiveTailEmitterOrdinaryOutputBridgeSpec
    emitterStructured emitterFinish ∧
  StructuredLiveTailJoinerOrdinaryOutputBridgeSpec
    joinerStructured joinerFinish

def StructuredLiveTailEmitterOrdinaryOutputBridgeConstruction
    (structured : Structured.Description) : Prop :=
  exists finish : MachineDescription,
    StructuredLiveTailEmitterOrdinaryOutputBridgeSpec structured finish

def StructuredLiveTailJoinerOrdinaryOutputBridgeConstruction
    (structured : Structured.Description) : Prop :=
  exists finish : MachineDescription,
    StructuredLiveTailJoinerOrdinaryOutputBridgeSpec structured finish

def StructuredLiveTailOrdinaryOutputBridgeConstruction
    (emitterStructured joinerStructured : Structured.Description) : Prop :=
  exists emitterFinish joinerFinish : MachineDescription,
    StructuredLiveTailOrdinaryOutputBridgeSpec
      emitterStructured joinerStructured emitterFinish joinerFinish

theorem StructuredLiveTailEmitterOrdinaryOutputBridgeSpec.structured
    {structured : Structured.Description} {finish : MachineDescription}
    (h :
      StructuredLiveTailEmitterOrdinaryOutputBridgeSpec
        structured finish) :
    StructuredLiveTailEmitterAssemblyOutputSpec structured :=
  h.left

theorem StructuredLiveTailEmitterOrdinaryOutputBridgeSpec.ordinary
    {structured : Structured.Description} {finish : MachineDescription}
    (h :
      StructuredLiveTailEmitterOrdinaryOutputBridgeSpec
        structured finish) :
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec finish :=
  h.right

theorem StructuredLiveTailEmitterOrdinaryOutputBridgeSpec.subroutineReady
    {structured : Structured.Description} {finish : MachineDescription}
    (h :
      StructuredLiveTailEmitterOrdinaryOutputBridgeSpec
        structured finish) :
    finish.SubroutineReady :=
  h.ordinary.left

theorem StructuredLiveTailEmitterOrdinaryOutputBridgeSpec.haltsFromTapeWithOutput
    {structured : Structured.Description} {finish : MachineDescription}
    (h :
      StructuredLiveTailEmitterOrdinaryOutputBridgeSpec
        structured finish)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    finish.HaltsFromTapeWithOutput
      (structuredLiveTailEmitterAssemblySourceTape p)
      (Tape.normalizedOutput
        (structuredLiveTailEmitterAssemblyTargetTape p)) := by
  simpa [
    structuredLiveTailEmitterAssemblySourceTape_eq_family,
    structuredLiveTailEmitterAssemblyTargetTape_eq_family,
    structuredLiveTailEmitterAssemblySourceTape,
    structuredLiveTailEmitterAssemblyTargetTape,
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec]
    using h.ordinary.right p

theorem StructuredLiveTailEmitterOrdinaryOutputBridgeSpec.haltsFromTargetOutput
    {structured : Structured.Description} {finish : MachineDescription}
    (h :
      StructuredLiveTailEmitterOrdinaryOutputBridgeSpec
        structured finish)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    finish.HaltsFromTapeWithOutput
      (structuredLiveTailEmitterAssemblySourceTape p)
      (structuredLiveTailEmitterAssemblyTargetOutput p) := by
  rw [← structuredLiveTailEmitterAssemblyTargetTape_normalizedOutput]
  exact h.haltsFromTapeWithOutput p

theorem StructuredLiveTailJoinerOrdinaryOutputBridgeSpec.structured
    {structured : Structured.Description} {finish : MachineDescription}
    (h :
      StructuredLiveTailJoinerOrdinaryOutputBridgeSpec
        structured finish) :
    StructuredLiveTailJoinerAssemblyOutputSpec structured :=
  h.left

theorem StructuredLiveTailJoinerOrdinaryOutputBridgeSpec.ordinary
    {structured : Structured.Description} {finish : MachineDescription}
    (h :
      StructuredLiveTailJoinerOrdinaryOutputBridgeSpec
        structured finish) :
    StructuredLiveTailJoinerAssemblyFamilyOutputSpec finish :=
  h.right

theorem StructuredLiveTailJoinerOrdinaryOutputBridgeSpec.subroutineReady
    {structured : Structured.Description} {finish : MachineDescription}
    (h :
      StructuredLiveTailJoinerOrdinaryOutputBridgeSpec
        structured finish) :
    finish.SubroutineReady :=
  h.ordinary.left

theorem StructuredLiveTailJoinerOrdinaryOutputBridgeSpec.haltsFromTapeWithOutput
    {structured : Structured.Description} {finish : MachineDescription}
    (h :
      StructuredLiveTailJoinerOrdinaryOutputBridgeSpec
        structured finish)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    finish.HaltsFromTapeWithOutput
      (structuredLiveTailJoinerAssemblySourceTape p)
      (Tape.normalizedOutput
        (structuredLiveTailJoinerAssemblyTargetTape p)) :=
  StructuredLiveTailJoinerAssemblyFamilyOutputSpec_haltsFromTapeWithOutput
    h.ordinary p

theorem StructuredLiveTailJoinerOrdinaryOutputBridgeSpec.haltsFromTargetOutput
    {structured : Structured.Description} {finish : MachineDescription}
    (h :
      StructuredLiveTailJoinerOrdinaryOutputBridgeSpec
        structured finish)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    finish.HaltsFromTapeWithOutput
      (structuredLiveTailJoinerAssemblySourceTape p)
      (structuredLiveTailJoinerAssemblyTargetOutput p) :=
  StructuredLiveTailJoinerAssemblyFamilyOutputSpec_haltsFromOutput
    h.ordinary p

theorem StructuredLiveTailOrdinaryOutputBridgeSpec.emitter
    {emitterStructured joinerStructured : Structured.Description}
    {emitterFinish joinerFinish : MachineDescription}
    (h :
      StructuredLiveTailOrdinaryOutputBridgeSpec
        emitterStructured joinerStructured emitterFinish joinerFinish) :
    StructuredLiveTailEmitterOrdinaryOutputBridgeSpec
      emitterStructured emitterFinish :=
  h.left

theorem StructuredLiveTailOrdinaryOutputBridgeSpec.joiner
    {emitterStructured joinerStructured : Structured.Description}
    {emitterFinish joinerFinish : MachineDescription}
    (h :
      StructuredLiveTailOrdinaryOutputBridgeSpec
        emitterStructured joinerStructured emitterFinish joinerFinish) :
    StructuredLiveTailJoinerOrdinaryOutputBridgeSpec
      joinerStructured joinerFinish :=
  h.right

theorem StructuredLiveTailEmitterOrdinaryOutputBridgeSpec_of_outputFamily
    {structured : Structured.Description} {finish : MachineDescription}
    (hstructured :
      StructuredLiveTailEmitterAssemblyOutputSpec structured)
    (hfinish :
      MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec finish) :
    StructuredLiveTailEmitterOrdinaryOutputBridgeSpec structured finish :=
  ⟨hstructured, hfinish⟩

theorem StructuredLiveTailJoinerOrdinaryOutputBridgeSpec_of_outputFamily
    {structured : Structured.Description} {finish : MachineDescription}
    (hstructured :
      StructuredLiveTailJoinerAssemblyOutputSpec structured)
    (hfinish :
      StructuredLiveTailJoinerAssemblyFamilyOutputSpec finish) :
    StructuredLiveTailJoinerOrdinaryOutputBridgeSpec structured finish :=
  ⟨hstructured, hfinish⟩

theorem StructuredLiveTailOrdinaryOutputBridgeSpec_of_parts
    {emitterStructured joinerStructured : Structured.Description}
    {emitterFinish joinerFinish : MachineDescription}
    (hemitter :
      StructuredLiveTailEmitterOrdinaryOutputBridgeSpec
        emitterStructured emitterFinish)
    (hjoiner :
      StructuredLiveTailJoinerOrdinaryOutputBridgeSpec
        joinerStructured joinerFinish) :
    StructuredLiveTailOrdinaryOutputBridgeSpec
      emitterStructured joinerStructured emitterFinish joinerFinish :=
  ⟨hemitter, hjoiner⟩

theorem StructuredLiveTailEmitterOrdinaryOutputBridgeConstruction_of_outputFamily
    {structured : Structured.Description}
    (hstructured :
      StructuredLiveTailEmitterAssemblyOutputSpec structured)
    (hfinish : MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputConstruction) :
    StructuredLiveTailEmitterOrdinaryOutputBridgeConstruction structured := by
  rcases hfinish with ⟨finish, hfinish⟩
  exact
    ⟨finish,
      StructuredLiveTailEmitterOrdinaryOutputBridgeSpec_of_outputFamily
        hstructured hfinish⟩

theorem StructuredLiveTailEmitterOrdinaryOutputBridgeConstruction_of_assemblyOutput
    {structured : Structured.Description}
    (hstructured :
      StructuredLiveTailEmitterAssemblyOutputSpec structured)
    (hfinish :
      MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest) :
    StructuredLiveTailEmitterOrdinaryOutputBridgeConstruction structured :=
  StructuredLiveTailEmitterOrdinaryOutputBridgeConstruction_of_outputFamily
    hstructured
    (MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputConstruction_of_assemblyOutput
      hfinish)

theorem StructuredLiveTailJoinerOrdinaryOutputBridgeConstruction_of_outputFamily
    {structured : Structured.Description}
    (hstructured :
      StructuredLiveTailJoinerAssemblyOutputSpec structured)
    (hfinish : StructuredLiveTailJoinerAssemblyFamilyOutputConstruction) :
    StructuredLiveTailJoinerOrdinaryOutputBridgeConstruction structured := by
  rcases hfinish with ⟨finish, hfinish⟩
  exact
    ⟨finish,
      StructuredLiveTailJoinerOrdinaryOutputBridgeSpec_of_outputFamily
        hstructured hfinish⟩

theorem StructuredLiveTailJoinerOrdinaryOutputBridgeConstruction_of_assemblyOutput
    {structured : Structured.Description}
    (hstructured :
      StructuredLiveTailJoinerAssemblyOutputSpec structured)
    (hfinish :
      MixedOptionCellQuoteLiveTailJoinerOutputConstructionForAssemblySourceRest) :
    StructuredLiveTailJoinerOrdinaryOutputBridgeConstruction structured :=
  StructuredLiveTailJoinerOrdinaryOutputBridgeConstruction_of_outputFamily
    hstructured
    (StructuredLiveTailJoinerAssemblyFamilyOutputConstruction_of_assemblyOutput
      hfinish)

theorem StructuredLiveTailOrdinaryOutputBridgeConstruction_of_parts
    {emitterStructured joinerStructured : Structured.Description}
    (hemitter :
      StructuredLiveTailEmitterOrdinaryOutputBridgeConstruction
        emitterStructured)
    (hjoiner :
      StructuredLiveTailJoinerOrdinaryOutputBridgeConstruction
        joinerStructured) :
    StructuredLiveTailOrdinaryOutputBridgeConstruction
      emitterStructured joinerStructured := by
  rcases hemitter with ⟨emitterFinish, hemitter⟩
  rcases hjoiner with ⟨joinerFinish, hjoiner⟩
  exact ⟨emitterFinish, joinerFinish, hemitter, hjoiner⟩

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
