import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.SourceRestFinishCore.LTJoinerStructured.LiftedOneTape

set_option doc.verso true

/-!
# Structured raw-tail insertion joiner

Raw-tail insertion assembly and tape-shape proofs for the structured live-tail joiner.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

/-!
The raw tail insertion component is the current lowerer-facing body candidate
for the joiner: at the visible-cell level it transforms
{lit}`emittedPrefix ++ rawTail ++ quoteRest` into
{lit}`emittedPrefix ++ quoteRest ++ rawTail`.

Its source contract starts at the prefix/raw-tail boundary and its final tape is
parked past the restored tail, so the bridges below deliberately prove
{name}`Tape.cells` or {name}`Tape.normalizedOutput` facts rather than exact
public joiner configuration equality.
-/
def structuredRawTailInsertionJoinerDescription :
    Structured.Description :=
  Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.description

def structuredRawTailInsertionJoinerInitialConfig
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Configuration :=
  Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.initialConfig
    (assemblySourceRestLiveTailEmitterEmittedPrefix p)
    (assemblySourceRestLiveTailEmitterRawTail p)
    (assemblySourceRestLiveTailEmitterQuoteRest p)

def structuredRawTailInsertionJoinerFinalConfig
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Configuration :=
  Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.finalConfig
    (assemblySourceRestLiveTailEmitterEmittedPrefix p)
    (assemblySourceRestLiveTailEmitterRawTail p)
    (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionSource_cells_eq_separated
    (emittedPrefix rawTail quoteRest : Word Bool) :
    Tape.cells
        (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.sourceTape
          emittedPrefix rawTail quoteRest) =
      Tape.cells
        (mixedOptionCellQuoteLiveTailSeparatedTape
          emittedPrefix rawTail quoteRest) := by
  cases rawTail with
  | nil =>
      simp [
        Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.sourceTape,
        mixedOptionCellQuoteLiveTailSeparatedTape,
        DovetailInitialLayoutInitializer.tapeAtCells,
        CommonGround.FiniteTransducers.tapeAtCells,
        Tape.cells, List.map_reverse]
  | cons head rest =>
      rw [mixedOptionCellQuoteLiveTailSeparatedTape_cells_cons]
      simp [
        Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.sourceTape,
        CommonGround.FiniteTransducers.tapeAtCells,
        Tape.cells, List.map_reverse]

theorem structuredRawTailInsertionSource_normalizedOutput_eq_separated
    (emittedPrefix rawTail quoteRest : Word Bool) :
    Tape.normalizedOutput
        (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.sourceTape
          emittedPrefix rawTail quoteRest) =
      Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailSeparatedTape
          emittedPrefix rawTail quoteRest) := by
  simp [Tape.normalizedOutput,
    structuredRawTailInsertionSource_cells_eq_separated]

theorem structuredRawTailInsertionRestoredSource_normalizedOutput_eq_joined
    (emittedPrefix rawTail quoteRest : Word Bool) :
    Tape.normalizedOutput
        (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoredSourceTape
          emittedPrefix rawTail quoteRest) =
      Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailJoinedTape
          emittedPrefix rawTail quoteRest) := by
  rw [
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoredSourceTape_normalizedOutput]
  cases rawTail with
  | nil =>
      simp [mixedOptionCellQuoteLiveTailJoinedTape,
        DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.normalizedOutput, Tape.cells, List.map_reverse,
        List.append_assoc, Function.comp_def]
  | cons head rest =>
      change
        List.append emittedPrefix
            (List.append quoteRest (head :: rest)) =
          (Tape.cells
            (mixedOptionCellQuoteLiveTailJoinedTape
              emittedPrefix (head :: rest) quoteRest)).filterMap
            (fun cell => cell)
      rw [mixedOptionCellQuoteLiveTailJoinedTape_cells_cons]
      simp [List.filterMap_append, Function.comp_def]

def structuredMixedOptionCellQuoteLiveTailJoinerCompactionLeftCells
    (w sourceRestBits : Word Bool) (stage : Nat)
    (head : Bool) (rawTailRest : Word Bool) :
    List (Option Bool) :=
  List.append
    (((List.append
      (MixedParserStackRewriterLengthHeader
        (assemblySourceRestFinishParserPrefixCells w)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage)
        sourceRestBits)
      (MixedParserStackRewriterPrefixQuote
        (assemblySourceRestFinishParserPrefixCells w)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage))).reverse.map some).reverse)
    ((head :: rawTailRest).map some)

def structuredMixedOptionCellQuoteLiveTailJoinerCompactionRightPadding
    (sourceRestBits : Word Bool) : List (Option Bool) :=
  List.append ((preservingCellPassCellBits sourceRestBits).map some) [none]

def structuredMixedOptionCellQuoteLiveTailJoinerInitialConfig
    (state : Nat) (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Configuration :=
  Structured.MultiTapeLowering.ThreeTape.config state
    (mixedOptionCellQuoteLiveTailSeparatedTape
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p))
    structuredMixedOptionCellQuoteLiveTailJoinerScratchTape
    structuredMixedOptionCellQuoteLiveTailJoinerWorkTape

def structuredMixedOptionCellQuoteLiveTailJoinerFinalConfig
    (state : Nat) (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Configuration :=
  Structured.MultiTapeLowering.ThreeTape.config state
    (mixedOptionCellQuoteLiveTailJoinedTape
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p))
    structuredMixedOptionCellQuoteLiveTailJoinerScratchTape
    structuredMixedOptionCellQuoteLiveTailJoinerWorkTape

theorem structuredJoinerInitialConfig_sourceTape
    (state : Nat) (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Description.tapeAt
        (structuredMixedOptionCellQuoteLiveTailJoinerInitialConfig
          state p).tapes
        0 =
      mixedOptionCellQuoteLiveTailSeparatedTape
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) := by
  rfl

theorem structuredRawTailInsertionJoinerDescription_copyTailSpec :
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.CopyTailSpec
      structuredRawTailInsertionJoinerDescription :=
  Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.description_copyTailSpec

theorem structuredRawTailInsertionJoinerDescription_rewindTailSpec :
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.RewindTailSpec
      structuredRawTailInsertionJoinerDescription :=
  Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.description_rewindTailSpec

theorem structuredRawTailInsertionJoinerDescription_copyRewindTailSpec :
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.CopyRewindTailSpec
      structuredRawTailInsertionJoinerDescription :=
  Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.description_copyRewindTailSpec

theorem structuredRawTailInsertionJoinerDescription_rewindScratchSpec :
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.RewindScratchSpec
      structuredRawTailInsertionJoinerDescription :=
  Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.description_rewindScratchSpec

theorem structuredRawTailInsertionJoinerDescription_copyRewindScratchSpec :
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.CopyRewindScratchSpec
      structuredRawTailInsertionJoinerDescription :=
  Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.description_copyRewindScratchSpec

theorem structuredRawTailInsertionJoinerDescription_writeInsertSpec :
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.WriteInsertSpec
      structuredRawTailInsertionJoinerDescription :=
  Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.description_writeInsertSpec

theorem structuredRawTailInsertionJoinerDescription_copyRewindScratchWriteInsertSpec :
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.CopyRewindScratchWriteInsertSpec
      structuredRawTailInsertionJoinerDescription :=
  Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.description_copyRewindScratchWriteInsertSpec

def StructuredRawTailInsertionJoinerAssemblyCopyTailSpec
    (D : Structured.Description) : Prop :=
  Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.CopyTailSpec D ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      D.runConfig
          ((assemblySourceRestLiveTailEmitterRawTail p).length + 1)
          (structuredRawTailInsertionJoinerInitialConfig p) =
        Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.copyTailHandoffConfig
          (assemblySourceRestLiveTailEmitterEmittedPrefix p)
          (assemblySourceRestLiveTailEmitterRawTail p)
          (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem StructuredRawTailInsertionJoinerAssemblyCopyTailSpec.supported
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyCopyTailSpec D) :
    Structured.MultiTapeLowering.SupportsReadWriteRows3 D :=
  hD.left.supported

theorem StructuredRawTailInsertionJoinerAssemblyCopyTailSpec.run
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyCopyTailSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    D.runConfig
        ((assemblySourceRestLiveTailEmitterRawTail p).length + 1)
        (structuredRawTailInsertionJoinerInitialConfig p) =
      Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.copyTailHandoffConfig
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) :=
  hD.right p

theorem StructuredRawTailInsertionJoinerAssemblyCopyTailSpec_of_copyTailSpec
    {D : Structured.Description}
    (hD : Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.CopyTailSpec
      D) :
    StructuredRawTailInsertionJoinerAssemblyCopyTailSpec D := by
  refine ⟨hD, ?_⟩
  intro p
  simpa [structuredRawTailInsertionJoinerInitialConfig]
    using
      hD.run
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerDescription_assemblyCopyTailSpec :
    StructuredRawTailInsertionJoinerAssemblyCopyTailSpec
      structuredRawTailInsertionJoinerDescription :=
  StructuredRawTailInsertionJoinerAssemblyCopyTailSpec_of_copyTailSpec
    structuredRawTailInsertionJoinerDescription_copyTailSpec

def StructuredRawTailInsertionJoinerAssemblyCopyRewindTailSpec
    (D : Structured.Description) : Prop :=
  StructuredRawTailInsertionJoinerAssemblyCopyTailSpec D ∧
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.CopyRewindTailSpec
      D ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      D.runConfig
          (2 * (assemblySourceRestLiveTailEmitterRawTail p).length + 3)
          (structuredRawTailInsertionJoinerInitialConfig p) =
        Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindTailHandoffConfig
          (assemblySourceRestLiveTailEmitterEmittedPrefix p)
          (assemblySourceRestLiveTailEmitterRawTail p)
          (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem StructuredRawTailInsertionJoinerAssemblyCopyRewindTailSpec.copyTail
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyCopyRewindTailSpec D) :
    StructuredRawTailInsertionJoinerAssemblyCopyTailSpec D :=
  hD.left

theorem StructuredRawTailInsertionJoinerAssemblyCopyRewindTailSpec.copyRewindTail
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyCopyRewindTailSpec D) :
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.CopyRewindTailSpec
      D :=
  hD.right.left

theorem StructuredRawTailInsertionJoinerAssemblyCopyRewindTailSpec.rewindTail
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyCopyRewindTailSpec D) :
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.RewindTailSpec
      D :=
  hD.copyRewindTail.rewindTail

theorem StructuredRawTailInsertionJoinerAssemblyCopyRewindTailSpec.run
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyCopyRewindTailSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    D.runConfig
        (2 * (assemblySourceRestLiveTailEmitterRawTail p).length + 3)
        (structuredRawTailInsertionJoinerInitialConfig p) =
      Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindTailHandoffConfig
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) :=
  hD.right.right p

theorem StructuredRawTailInsertionJoinerAssemblyCopyRewindTailSpec_of_copyRewindTailSpec
    {D : Structured.Description}
    (hD : Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.CopyRewindTailSpec
      D) :
    StructuredRawTailInsertionJoinerAssemblyCopyRewindTailSpec D := by
  refine
    ⟨StructuredRawTailInsertionJoinerAssemblyCopyTailSpec_of_copyTailSpec
        hD.copyTail,
      hD, ?_⟩
  intro p
  simpa [structuredRawTailInsertionJoinerInitialConfig]
    using
      hD.run
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerDescription_assemblyCopyRewindTailSpec :
    StructuredRawTailInsertionJoinerAssemblyCopyRewindTailSpec
      structuredRawTailInsertionJoinerDescription :=
  StructuredRawTailInsertionJoinerAssemblyCopyRewindTailSpec_of_copyRewindTailSpec
    structuredRawTailInsertionJoinerDescription_copyRewindTailSpec

def StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchSpec
    (D : Structured.Description) : Prop :=
  StructuredRawTailInsertionJoinerAssemblyCopyRewindTailSpec D ∧
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.CopyRewindScratchSpec
      D ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      D.runConfig
          (2 * (assemblySourceRestLiveTailEmitterRawTail p).length +
            (assemblySourceRestLiveTailEmitterQuoteRest p).length + 5)
          (structuredRawTailInsertionJoinerInitialConfig p) =
        Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindScratchHandoffConfig
          (assemblySourceRestLiveTailEmitterEmittedPrefix p)
          (assemblySourceRestLiveTailEmitterRawTail p)
          (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchSpec.copyRewindTail
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchSpec D) :
    StructuredRawTailInsertionJoinerAssemblyCopyRewindTailSpec D :=
  hD.left

theorem StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchSpec.copyRewindScratch
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchSpec D) :
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.CopyRewindScratchSpec
      D :=
  hD.right.left

theorem StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchSpec.rewindScratch
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchSpec D) :
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.RewindScratchSpec
      D :=
  hD.copyRewindScratch.rewindScratch

theorem StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchSpec.run
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    D.runConfig
        (2 * (assemblySourceRestLiveTailEmitterRawTail p).length +
          (assemblySourceRestLiveTailEmitterQuoteRest p).length + 5)
        (structuredRawTailInsertionJoinerInitialConfig p) =
      Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindScratchHandoffConfig
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) :=
  hD.right.right p

theorem StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchSpec_of_copyRewindScratchSpec
    {D : Structured.Description}
    (hD : Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.CopyRewindScratchSpec
      D) :
    StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchSpec D := by
  refine
    ⟨StructuredRawTailInsertionJoinerAssemblyCopyRewindTailSpec_of_copyRewindTailSpec
        hD.copyRewindTail,
      hD, ?_⟩
  intro p
  simpa [structuredRawTailInsertionJoinerInitialConfig]
    using
      hD.run
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerDescription_assemblyCopyRewindScratchSpec :
    StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchSpec
      structuredRawTailInsertionJoinerDescription :=
  StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchSpec_of_copyRewindScratchSpec
    structuredRawTailInsertionJoinerDescription_copyRewindScratchSpec

def StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchWriteInsertSpec
    (D : Structured.Description) : Prop :=
  StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchSpec D ∧
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.CopyRewindScratchWriteInsertSpec
      D ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      D.runConfig
          (2 * (assemblySourceRestLiveTailEmitterRawTail p).length +
            2 * (assemblySourceRestLiveTailEmitterQuoteRest p).length + 6)
          (structuredRawTailInsertionJoinerInitialConfig p) =
        Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.writeInsertHandoffConfig
          (assemblySourceRestLiveTailEmitterEmittedPrefix p)
          (assemblySourceRestLiveTailEmitterRawTail p)
          (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchWriteInsertSpec.copyRewindScratch
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchWriteInsertSpec
      D) :
    StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchSpec D :=
  hD.left

theorem StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchWriteInsertSpec.copyRewindScratchWriteInsert
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchWriteInsertSpec
      D) :
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.CopyRewindScratchWriteInsertSpec
      D :=
  hD.right.left

theorem StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchWriteInsertSpec.writeInsert
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchWriteInsertSpec
      D) :
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.WriteInsertSpec
      D :=
  hD.copyRewindScratchWriteInsert.writeInsert

theorem StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchWriteInsertSpec.run
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchWriteInsertSpec
      D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    D.runConfig
        (2 * (assemblySourceRestLiveTailEmitterRawTail p).length +
          2 * (assemblySourceRestLiveTailEmitterQuoteRest p).length + 6)
        (structuredRawTailInsertionJoinerInitialConfig p) =
      Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.writeInsertHandoffConfig
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) :=
  hD.right.right p

theorem StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchWriteInsertSpec_of_copyRewindScratchWriteInsertSpec
    {D : Structured.Description}
    (hD : Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.CopyRewindScratchWriteInsertSpec
      D) :
    StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchWriteInsertSpec
      D := by
  refine
    ⟨StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchSpec_of_copyRewindScratchSpec
        hD.copyRewindScratch,
      hD, ?_⟩
  intro p
  simpa [structuredRawTailInsertionJoinerInitialConfig]
    using
      hD.run
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerDescription_assemblyCopyRewindScratchWriteInsertSpec :
    StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchWriteInsertSpec
      structuredRawTailInsertionJoinerDescription :=
  StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchWriteInsertSpec_of_copyRewindScratchWriteInsertSpec
    structuredRawTailInsertionJoinerDescription_copyRewindScratchWriteInsertSpec

theorem structuredRawTailInsertionJoinerInitialConfig_source_cells_eq_separated
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.cells
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerInitialConfig p).tapes 0) =
      Tape.cells
        (mixedOptionCellQuoteLiveTailSeparatedTape
          (assemblySourceRestLiveTailEmitterEmittedPrefix p)
          (assemblySourceRestLiveTailEmitterRawTail p)
          (assemblySourceRestLiveTailEmitterQuoteRest p)) := by
  simpa [structuredRawTailInsertionJoinerInitialConfig,
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.initialConfig]
    using
      structuredRawTailInsertionSource_cells_eq_separated
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerInitialConfig_source_normalizedOutput_eq_separated
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerInitialConfig p).tapes 0) =
      Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailSeparatedTape
          (assemblySourceRestLiveTailEmitterEmittedPrefix p)
          (assemblySourceRestLiveTailEmitterRawTail p)
          (assemblySourceRestLiveTailEmitterQuoteRest p)) := by
  simp [Tape.normalizedOutput,
    structuredRawTailInsertionJoinerInitialConfig_source_cells_eq_separated]

theorem structuredRawTailInsertionJoinerInitialConfig_source_normalizedOutput_eq_afterRawTailScan
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerInitialConfig p).tapes 0) =
      Tape.normalizedOutput
        (MixedParserStackWholeSourceAfterRawTailScanTape
          p.w p.sourceRestBits p.stage) := by
  rw [
    structuredRawTailInsertionJoinerInitialConfig_source_normalizedOutput_eq_separated,
    assemblySourceRestLiveTailJoinerSeparatedTape_eq_afterRawTailScanTape]

theorem structuredRawTailInsertionJoinerInitialConfig_scratch_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerInitialConfig p).tapes 1) =
      assemblySourceRestLiveTailEmitterQuoteRest p := by
  simpa [structuredRawTailInsertionJoinerInitialConfig,
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.initialConfig]
    using
      Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.initialConfig_scratch_normalizedOutput
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerInitialConfig_work_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerInitialConfig p).tapes 2) =
      [] := by
  simpa [structuredRawTailInsertionJoinerInitialConfig,
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.initialConfig]
    using
      Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.initialConfig_work_normalizedOutput
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerCopyTailHandoff_source_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.copyTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 0) =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) := by
  exact
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.copyTailHandoffConfig_source_normalizedOutput
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerCopyTailHandoff_scratch_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.copyTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 1) =
      assemblySourceRestLiveTailEmitterQuoteRest p := by
  exact
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.copyTailHandoffConfig_scratch_normalizedOutput
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerCopyTailHandoff_work_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.copyTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 2) =
      assemblySourceRestLiveTailEmitterRawTail p := by
  exact
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.copyTailHandoffConfig_work_normalizedOutput
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerRewindTailHandoff_source_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 0) =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) := by
  exact
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindTailHandoffConfig_source_normalizedOutput
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerRewindTailHandoff_scratch_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 1) =
      assemblySourceRestLiveTailEmitterQuoteRest p := by
  exact
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindTailHandoffConfig_scratch_normalizedOutput
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerRewindTailHandoff_work_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 2) =
      assemblySourceRestLiveTailEmitterRawTail p := by
  exact
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindTailHandoffConfig_work_normalizedOutput
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerRewindScratchHandoff_source_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindScratchHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 0) =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) := by
  exact
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindScratchHandoffConfig_source_normalizedOutput
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerRewindScratchHandoff_scratch_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindScratchHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 1) =
      assemblySourceRestLiveTailEmitterQuoteRest p := by
  exact
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindScratchHandoffConfig_scratch_normalizedOutput
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerRewindScratchHandoff_work_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindScratchHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 2) =
      assemblySourceRestLiveTailEmitterRawTail p := by
  exact
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindScratchHandoffConfig_work_normalizedOutput
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerWriteInsertHandoff_source_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.writeInsertHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 0) =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (List.append
          (assemblySourceRestLiveTailEmitterQuoteRest p)
          ((Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.writeInsertHandoffRightCells
              (assemblySourceRestLiveTailEmitterRawTail p)
              (assemblySourceRestLiveTailEmitterQuoteRest p)).filterMap
            (fun cell => cell))) := by
  exact
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.writeInsertHandoffConfig_source_normalizedOutput
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerWriteInsertHandoff_scratch_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.writeInsertHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 1) =
      assemblySourceRestLiveTailEmitterQuoteRest p := by
  exact
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.writeInsertHandoffConfig_scratch_normalizedOutput
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerWriteInsertHandoff_work_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.writeInsertHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 2) =
      assemblySourceRestLiveTailEmitterRawTail p := by
  exact
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.writeInsertHandoffConfig_work_normalizedOutput
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerFinalConfig_source_normalizedOutput_eq_joined
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerFinalConfig p).tapes 0) =
      Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailJoinedTape
          (assemblySourceRestLiveTailEmitterEmittedPrefix p)
          (assemblySourceRestLiveTailEmitterRawTail p)
          (assemblySourceRestLiveTailEmitterQuoteRest p)) := by
  simpa [structuredRawTailInsertionJoinerFinalConfig,
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.finalConfig]
    using
      structuredRawTailInsertionRestoredSource_normalizedOutput_eq_joined
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerFinalConfig_source_normalizedOutput_eq_target
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerFinalConfig p).tapes 0) =
      Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape
          p.w p.sourceRestBits p.stage) := by
  rw [
    structuredRawTailInsertionJoinerFinalConfig_source_normalizedOutput_eq_joined,
    assemblySourceRestLiveTailJoinerJoinedTape_eq_targetTape]

theorem structuredRawTailInsertionJoinerFinalConfig_scratch_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerFinalConfig p).tapes 1) =
      assemblySourceRestLiveTailEmitterQuoteRest p := by
  simpa [structuredRawTailInsertionJoinerFinalConfig,
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.finalConfig]
    using
      Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.finalScratchTape_normalizedOutput
        (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerFinalConfig_work_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerFinalConfig p).tapes 2) =
      [] := by
  simpa [structuredRawTailInsertionJoinerFinalConfig,
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.finalConfig]
    using
      Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.finalConfig_work_normalizedOutput
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p)

def StructuredRawTailInsertionJoinerAssemblyShapeSpec
    (D : Structured.Description) : Prop :=
  StructuredRawTailInsertionJoinerAssemblyCopyTailSpec D ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (structuredRawTailInsertionJoinerInitialConfig p).tapes 0) =
        Tape.normalizedOutput
          (MixedParserStackWholeSourceAfterRawTailScanTape
            p.w p.sourceRestBits p.stage) ∧
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (structuredRawTailInsertionJoinerFinalConfig p).tapes 0) =
        Tape.normalizedOutput
          (assemblySourceRestFinishTargetTape
            p.w p.sourceRestBits p.stage)

theorem StructuredRawTailInsertionJoinerAssemblyShapeSpec.copyTail
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyShapeSpec D) :
    StructuredRawTailInsertionJoinerAssemblyCopyTailSpec D :=
  hD.left

theorem StructuredRawTailInsertionJoinerAssemblyShapeSpec.initial_source
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyShapeSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerInitialConfig p).tapes 0) =
      Tape.normalizedOutput
        (MixedParserStackWholeSourceAfterRawTailScanTape
          p.w p.sourceRestBits p.stage) :=
  (hD.right p).left

theorem StructuredRawTailInsertionJoinerAssemblyShapeSpec.final_source
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyShapeSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerFinalConfig p).tapes 0) =
      Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape
          p.w p.sourceRestBits p.stage) :=
  (hD.right p).right

theorem structuredRawTailInsertionJoinerDescription_assemblyShapeSpec :
    StructuredRawTailInsertionJoinerAssemblyShapeSpec
      structuredRawTailInsertionJoinerDescription := by
  refine
    ⟨structuredRawTailInsertionJoinerDescription_assemblyCopyTailSpec,
      ?_⟩
  intro p
  exact
    ⟨structuredRawTailInsertionJoinerInitialConfig_source_normalizedOutput_eq_afterRawTailScan
        p,
      structuredRawTailInsertionJoinerFinalConfig_source_normalizedOutput_eq_target
        p⟩

def StructuredRawTailInsertionJoinerAssemblyTapeStateSpec
    (D : Structured.Description) : Prop :=
  StructuredRawTailInsertionJoinerAssemblyShapeSpec D ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (structuredRawTailInsertionJoinerInitialConfig p).tapes 1) =
        assemblySourceRestLiveTailEmitterQuoteRest p ∧
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (structuredRawTailInsertionJoinerInitialConfig p).tapes 2) =
        [] ∧
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.copyTailHandoffConfig
              (assemblySourceRestLiveTailEmitterEmittedPrefix p)
              (assemblySourceRestLiveTailEmitterRawTail p)
              (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 0) =
        List.append
          (assemblySourceRestLiveTailEmitterEmittedPrefix p)
          (assemblySourceRestLiveTailEmitterQuoteRest p) ∧
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.copyTailHandoffConfig
              (assemblySourceRestLiveTailEmitterEmittedPrefix p)
              (assemblySourceRestLiveTailEmitterRawTail p)
              (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 1) =
        assemblySourceRestLiveTailEmitterQuoteRest p ∧
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.copyTailHandoffConfig
              (assemblySourceRestLiveTailEmitterEmittedPrefix p)
              (assemblySourceRestLiveTailEmitterRawTail p)
              (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 2) =
        assemblySourceRestLiveTailEmitterRawTail p ∧
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (structuredRawTailInsertionJoinerFinalConfig p).tapes 1) =
        assemblySourceRestLiveTailEmitterQuoteRest p ∧
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (structuredRawTailInsertionJoinerFinalConfig p).tapes 2) =
        []

theorem StructuredRawTailInsertionJoinerAssemblyTapeStateSpec.shape
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyTapeStateSpec D) :
    StructuredRawTailInsertionJoinerAssemblyShapeSpec D :=
  hD.left

theorem StructuredRawTailInsertionJoinerAssemblyTapeStateSpec.initial_scratch
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerInitialConfig p).tapes 1) =
      assemblySourceRestLiveTailEmitterQuoteRest p :=
by
  rcases hD.right p with
    ⟨hinitScratch, hinitWork, hhandoffSource, hhandoffScratch,
      hhandoffWork, hfinalScratch, hfinalWork⟩
  exact hinitScratch

theorem StructuredRawTailInsertionJoinerAssemblyTapeStateSpec.initial_work
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerInitialConfig p).tapes 2) =
      [] :=
by
  rcases hD.right p with
    ⟨hinitScratch, hinitWork, hhandoffSource, hhandoffScratch,
      hhandoffWork, hfinalScratch, hfinalWork⟩
  exact hinitWork

theorem StructuredRawTailInsertionJoinerAssemblyTapeStateSpec.handoff_source
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.copyTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 0) =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) :=
by
  rcases hD.right p with
    ⟨hinitScratch, hinitWork, hhandoffSource, hhandoffScratch,
      hhandoffWork, hfinalScratch, hfinalWork⟩
  exact hhandoffSource

theorem StructuredRawTailInsertionJoinerAssemblyTapeStateSpec.handoff_scratch
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.copyTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 1) =
      assemblySourceRestLiveTailEmitterQuoteRest p :=
by
  rcases hD.right p with
    ⟨hinitScratch, hinitWork, hhandoffSource, hhandoffScratch,
      hhandoffWork, hfinalScratch, hfinalWork⟩
  exact hhandoffScratch

theorem StructuredRawTailInsertionJoinerAssemblyTapeStateSpec.handoff_work
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.copyTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 2) =
      assemblySourceRestLiveTailEmitterRawTail p :=
by
  rcases hD.right p with
    ⟨hinitScratch, hinitWork, hhandoffSource, hhandoffScratch,
      hhandoffWork, hfinalScratch, hfinalWork⟩
  exact hhandoffWork

theorem StructuredRawTailInsertionJoinerAssemblyTapeStateSpec.final_scratch
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerFinalConfig p).tapes 1) =
      assemblySourceRestLiveTailEmitterQuoteRest p :=
by
  rcases hD.right p with
    ⟨hinitScratch, hinitWork, hhandoffSource, hhandoffScratch,
      hhandoffWork, hfinalScratch, hfinalWork⟩
  exact hfinalScratch

theorem StructuredRawTailInsertionJoinerAssemblyTapeStateSpec.final_work
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerFinalConfig p).tapes 2) =
      [] :=
by
  rcases hD.right p with
    ⟨hinitScratch, hinitWork, hhandoffSource, hhandoffScratch,
      hhandoffWork, hfinalScratch, hfinalWork⟩
  exact hfinalWork

theorem structuredRawTailInsertionJoinerDescription_assemblyTapeStateSpec :
    StructuredRawTailInsertionJoinerAssemblyTapeStateSpec
      structuredRawTailInsertionJoinerDescription := by
  refine
    ⟨structuredRawTailInsertionJoinerDescription_assemblyShapeSpec, ?_⟩
  intro p
  exact
    ⟨structuredRawTailInsertionJoinerInitialConfig_scratch_normalizedOutput p,
      structuredRawTailInsertionJoinerInitialConfig_work_normalizedOutput p,
      structuredRawTailInsertionJoinerCopyTailHandoff_source_normalizedOutput p,
      structuredRawTailInsertionJoinerCopyTailHandoff_scratch_normalizedOutput p,
      structuredRawTailInsertionJoinerCopyTailHandoff_work_normalizedOutput p,
      structuredRawTailInsertionJoinerFinalConfig_scratch_normalizedOutput p,
      structuredRawTailInsertionJoinerFinalConfig_work_normalizedOutput p⟩

def StructuredRawTailInsertionJoinerAssemblyRewindTapeStateSpec
    (D : Structured.Description) : Prop :=
  StructuredRawTailInsertionJoinerAssemblyTapeStateSpec D ∧
    StructuredRawTailInsertionJoinerAssemblyCopyRewindTailSpec D ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindTailHandoffConfig
              (assemblySourceRestLiveTailEmitterEmittedPrefix p)
              (assemblySourceRestLiveTailEmitterRawTail p)
              (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 0) =
        List.append
          (assemblySourceRestLiveTailEmitterEmittedPrefix p)
          (assemblySourceRestLiveTailEmitterQuoteRest p) ∧
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindTailHandoffConfig
              (assemblySourceRestLiveTailEmitterEmittedPrefix p)
              (assemblySourceRestLiveTailEmitterRawTail p)
              (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 1) =
        assemblySourceRestLiveTailEmitterQuoteRest p ∧
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindTailHandoffConfig
              (assemblySourceRestLiveTailEmitterEmittedPrefix p)
              (assemblySourceRestLiveTailEmitterRawTail p)
              (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 2) =
        assemblySourceRestLiveTailEmitterRawTail p

theorem StructuredRawTailInsertionJoinerAssemblyRewindTapeStateSpec.tapeState
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRewindTapeStateSpec D) :
    StructuredRawTailInsertionJoinerAssemblyTapeStateSpec D :=
  hD.left

theorem StructuredRawTailInsertionJoinerAssemblyRewindTapeStateSpec.copyRewindTail
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRewindTapeStateSpec D) :
    StructuredRawTailInsertionJoinerAssemblyCopyRewindTailSpec D :=
  hD.right.left

theorem StructuredRawTailInsertionJoinerAssemblyRewindTapeStateSpec.rewind_source
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRewindTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 0) =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) :=
  (hD.right.right p).left

theorem StructuredRawTailInsertionJoinerAssemblyRewindTapeStateSpec.rewind_scratch
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRewindTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 1) =
      assemblySourceRestLiveTailEmitterQuoteRest p :=
  (hD.right.right p).right.left

theorem StructuredRawTailInsertionJoinerAssemblyRewindTapeStateSpec.rewind_work
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRewindTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 2) =
      assemblySourceRestLiveTailEmitterRawTail p :=
  (hD.right.right p).right.right

theorem structuredRawTailInsertionJoinerDescription_assemblyRewindTapeStateSpec :
    StructuredRawTailInsertionJoinerAssemblyRewindTapeStateSpec
      structuredRawTailInsertionJoinerDescription := by
  refine
    ⟨structuredRawTailInsertionJoinerDescription_assemblyTapeStateSpec,
      structuredRawTailInsertionJoinerDescription_assemblyCopyRewindTailSpec,
      ?_⟩
  intro p
  exact
    ⟨structuredRawTailInsertionJoinerRewindTailHandoff_source_normalizedOutput
        p,
      structuredRawTailInsertionJoinerRewindTailHandoff_scratch_normalizedOutput
        p,
      structuredRawTailInsertionJoinerRewindTailHandoff_work_normalizedOutput
        p⟩

def StructuredRawTailInsertionJoinerAssemblyScratchRewindTapeStateSpec
    (D : Structured.Description) : Prop :=
  StructuredRawTailInsertionJoinerAssemblyRewindTapeStateSpec D ∧
    StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchSpec D ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindScratchHandoffConfig
              (assemblySourceRestLiveTailEmitterEmittedPrefix p)
              (assemblySourceRestLiveTailEmitterRawTail p)
              (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 0) =
        List.append
          (assemblySourceRestLiveTailEmitterEmittedPrefix p)
          (assemblySourceRestLiveTailEmitterQuoteRest p) ∧
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindScratchHandoffConfig
              (assemblySourceRestLiveTailEmitterEmittedPrefix p)
              (assemblySourceRestLiveTailEmitterRawTail p)
              (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 1) =
        assemblySourceRestLiveTailEmitterQuoteRest p ∧
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindScratchHandoffConfig
              (assemblySourceRestLiveTailEmitterEmittedPrefix p)
              (assemblySourceRestLiveTailEmitterRawTail p)
              (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 2) =
        assemblySourceRestLiveTailEmitterRawTail p

theorem StructuredRawTailInsertionJoinerAssemblyScratchRewindTapeStateSpec.rewindTapeState
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyScratchRewindTapeStateSpec D) :
    StructuredRawTailInsertionJoinerAssemblyRewindTapeStateSpec D :=
  hD.left

theorem StructuredRawTailInsertionJoinerAssemblyScratchRewindTapeStateSpec.copyRewindScratch
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyScratchRewindTapeStateSpec D) :
    StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchSpec D :=
  hD.right.left

theorem StructuredRawTailInsertionJoinerAssemblyScratchRewindTapeStateSpec.scratchRewind_source
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyScratchRewindTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindScratchHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 0) =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) :=
  (hD.right.right p).left

theorem StructuredRawTailInsertionJoinerAssemblyScratchRewindTapeStateSpec.scratchRewind_scratch
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyScratchRewindTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindScratchHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 1) =
      assemblySourceRestLiveTailEmitterQuoteRest p :=
  (hD.right.right p).right.left

theorem StructuredRawTailInsertionJoinerAssemblyScratchRewindTapeStateSpec.scratchRewind_work
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyScratchRewindTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.rewindScratchHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 2) =
      assemblySourceRestLiveTailEmitterRawTail p :=
  (hD.right.right p).right.right

theorem structuredRawTailInsertionJoinerDescription_assemblyScratchRewindTapeStateSpec :
    StructuredRawTailInsertionJoinerAssemblyScratchRewindTapeStateSpec
      structuredRawTailInsertionJoinerDescription := by
  refine
    ⟨structuredRawTailInsertionJoinerDescription_assemblyRewindTapeStateSpec,
      structuredRawTailInsertionJoinerDescription_assemblyCopyRewindScratchSpec,
      ?_⟩
  intro p
  exact
    ⟨structuredRawTailInsertionJoinerRewindScratchHandoff_source_normalizedOutput
        p,
      structuredRawTailInsertionJoinerRewindScratchHandoff_scratch_normalizedOutput
        p,
      structuredRawTailInsertionJoinerRewindScratchHandoff_work_normalizedOutput
        p⟩

def StructuredRawTailInsertionJoinerAssemblyWriteInsertTapeStateSpec
    (D : Structured.Description) : Prop :=
  StructuredRawTailInsertionJoinerAssemblyScratchRewindTapeStateSpec D ∧
    StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchWriteInsertSpec
      D ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.writeInsertHandoffConfig
              (assemblySourceRestLiveTailEmitterEmittedPrefix p)
              (assemblySourceRestLiveTailEmitterRawTail p)
              (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 0) =
        List.append
          (assemblySourceRestLiveTailEmitterEmittedPrefix p)
          (List.append
            (assemblySourceRestLiveTailEmitterQuoteRest p)
            ((Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.writeInsertHandoffRightCells
                (assemblySourceRestLiveTailEmitterRawTail p)
                (assemblySourceRestLiveTailEmitterQuoteRest p)).filterMap
              (fun cell => cell))) ∧
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.writeInsertHandoffConfig
              (assemblySourceRestLiveTailEmitterEmittedPrefix p)
              (assemblySourceRestLiveTailEmitterRawTail p)
              (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 1) =
        assemblySourceRestLiveTailEmitterQuoteRest p ∧
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.writeInsertHandoffConfig
              (assemblySourceRestLiveTailEmitterEmittedPrefix p)
              (assemblySourceRestLiveTailEmitterRawTail p)
              (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 2) =
        assemblySourceRestLiveTailEmitterRawTail p

theorem StructuredRawTailInsertionJoinerAssemblyWriteInsertTapeStateSpec.scratchRewindTapeState
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyWriteInsertTapeStateSpec D) :
    StructuredRawTailInsertionJoinerAssemblyScratchRewindTapeStateSpec D :=
  hD.left

theorem StructuredRawTailInsertionJoinerAssemblyWriteInsertTapeStateSpec.copyRewindScratchWriteInsert
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyWriteInsertTapeStateSpec D) :
    StructuredRawTailInsertionJoinerAssemblyCopyRewindScratchWriteInsertSpec
      D :=
  hD.right.left

theorem StructuredRawTailInsertionJoinerAssemblyWriteInsertTapeStateSpec.writeInsert_source
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyWriteInsertTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.writeInsertHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 0) =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (List.append
          (assemblySourceRestLiveTailEmitterQuoteRest p)
          ((Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.writeInsertHandoffRightCells
              (assemblySourceRestLiveTailEmitterRawTail p)
              (assemblySourceRestLiveTailEmitterQuoteRest p)).filterMap
            (fun cell => cell))) :=
  (hD.right.right p).left

theorem StructuredRawTailInsertionJoinerAssemblyWriteInsertTapeStateSpec.writeInsert_scratch
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyWriteInsertTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.writeInsertHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 1) =
      assemblySourceRestLiveTailEmitterQuoteRest p :=
  (hD.right.right p).right.left

theorem StructuredRawTailInsertionJoinerAssemblyWriteInsertTapeStateSpec.writeInsert_work
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyWriteInsertTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.writeInsertHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 2) =
      assemblySourceRestLiveTailEmitterRawTail p :=
  (hD.right.right p).right.right

theorem structuredRawTailInsertionJoinerDescription_assemblyWriteInsertTapeStateSpec :
    StructuredRawTailInsertionJoinerAssemblyWriteInsertTapeStateSpec
      structuredRawTailInsertionJoinerDescription := by
  refine
    ⟨structuredRawTailInsertionJoinerDescription_assemblyScratchRewindTapeStateSpec,
      structuredRawTailInsertionJoinerDescription_assemblyCopyRewindScratchWriteInsertSpec,
      ?_⟩
  intro p
  exact
    ⟨structuredRawTailInsertionJoinerWriteInsertHandoff_source_normalizedOutput
        p,
      structuredRawTailInsertionJoinerWriteInsertHandoff_scratch_normalizedOutput
        p,
      structuredRawTailInsertionJoinerWriteInsertHandoff_work_normalizedOutput
        p⟩


end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
