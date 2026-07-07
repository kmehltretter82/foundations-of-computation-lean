import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTJoinerStructured

set_option doc.verso true

/-!
# Structured live-tail joiner restore endpoint

This module keeps the final restore endpoint facts for the structured
raw-tail insertion joiner out of `LTJoinerStructured.lean`, which is already
near the repository's large-file threshold.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

def StructuredRawTailInsertionJoinerAssemblyRestoreSpec
    (D : Structured.Description) : Prop :=
  Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.FullSpec D ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      D.runConfig
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.runFuel
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p))
          (structuredRawTailInsertionJoinerInitialConfig p) =
        Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig
          (assemblySourceRestLiveTailEmitterEmittedPrefix p)
          (assemblySourceRestLiveTailEmitterRawTail p)
          (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem StructuredRawTailInsertionJoinerAssemblyRestoreSpec.full
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreSpec D) :
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.FullSpec D :=
  hD.left

theorem StructuredRawTailInsertionJoinerAssemblyRestoreSpec.restoreTail
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreSpec D) :
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.RestoreTailSpec
      D :=
  hD.full.restoreTail

theorem StructuredRawTailInsertionJoinerAssemblyRestoreSpec.run
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    D.runConfig
        (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.runFuel
          (assemblySourceRestLiveTailEmitterRawTail p)
          (assemblySourceRestLiveTailEmitterQuoteRest p))
        (structuredRawTailInsertionJoinerInitialConfig p) =
      Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) :=
  hD.right p

theorem StructuredRawTailInsertionJoinerAssemblyRestoreSpec_of_fullSpec
    {D : Structured.Description}
    (hD : Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.FullSpec
      D) :
    StructuredRawTailInsertionJoinerAssemblyRestoreSpec D := by
  refine ⟨hD, ?_⟩
  intro p
  simpa [structuredRawTailInsertionJoinerInitialConfig]
    using
      hD.run
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerDescription_assemblyRestoreSpec :
    StructuredRawTailInsertionJoinerAssemblyRestoreSpec
      structuredRawTailInsertionJoinerDescription :=
  StructuredRawTailInsertionJoinerAssemblyRestoreSpec_of_fullSpec
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.description_fullSpec

theorem structuredRawTailInsertionJoinerRestoreHandoff_source_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 0) =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (List.append
          (assemblySourceRestLiveTailEmitterQuoteRest p)
          (assemblySourceRestLiveTailEmitterRawTail p)) := by
  exact
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig_source_normalizedOutput
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerRestoreHandoff_source_normalizedOutput_eq_joined
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 0) =
      Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailJoinedTape
          (assemblySourceRestLiveTailEmitterEmittedPrefix p)
          (assemblySourceRestLiveTailEmitterRawTail p)
          (assemblySourceRestLiveTailEmitterQuoteRest p)) := by
  rw [structuredRawTailInsertionJoinerRestoreHandoff_source_normalizedOutput]
  rw [← structuredRawTailInsertionRestoredSource_normalizedOutput_eq_joined]
  rw [
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoredSourceTape_normalizedOutput]

theorem structuredRawTailInsertionJoinerRestoreHandoff_source_normalizedOutput_eq_target
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 0) =
      Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape
          p.w p.sourceRestBits p.stage) := by
  rw [
    structuredRawTailInsertionJoinerRestoreHandoff_source_normalizedOutput_eq_joined,
    assemblySourceRestLiveTailJoinerJoinedTape_eq_targetTape]

theorem structuredRawTailInsertionJoinerRestoreHandoff_scratch_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 1) =
      assemblySourceRestLiveTailEmitterQuoteRest p := by
  exact
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig_scratch_normalizedOutput
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerRestoreHandoff_work_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 2) =
      [] := by
  exact
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig_work_normalizedOutput
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

def StructuredRawTailInsertionJoinerAssemblyRestoreTapeStateSpec
    (D : Structured.Description) : Prop :=
  StructuredRawTailInsertionJoinerAssemblyRestoreSpec D ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig
              (assemblySourceRestLiveTailEmitterEmittedPrefix p)
              (assemblySourceRestLiveTailEmitterRawTail p)
              (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 0) =
        Tape.normalizedOutput
          (assemblySourceRestFinishTargetTape
            p.w p.sourceRestBits p.stage) ∧
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig
              (assemblySourceRestLiveTailEmitterEmittedPrefix p)
              (assemblySourceRestLiveTailEmitterRawTail p)
              (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 1) =
        assemblySourceRestLiveTailEmitterQuoteRest p ∧
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig
              (assemblySourceRestLiveTailEmitterEmittedPrefix p)
              (assemblySourceRestLiveTailEmitterRawTail p)
              (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 2) =
        []

theorem StructuredRawTailInsertionJoinerAssemblyRestoreTapeStateSpec.restore
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreTapeStateSpec D) :
    StructuredRawTailInsertionJoinerAssemblyRestoreSpec D :=
  hD.left

theorem StructuredRawTailInsertionJoinerAssemblyRestoreTapeStateSpec.source
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 0) =
      Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape
          p.w p.sourceRestBits p.stage) :=
  (hD.right p).left

theorem StructuredRawTailInsertionJoinerAssemblyRestoreTapeStateSpec.scratch
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 1) =
      assemblySourceRestLiveTailEmitterQuoteRest p :=
  (hD.right p).right.left

theorem StructuredRawTailInsertionJoinerAssemblyRestoreTapeStateSpec.work
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p)).tapes 2) =
      [] :=
  (hD.right p).right.right

theorem structuredRawTailInsertionJoinerDescription_assemblyRestoreTapeStateSpec :
    StructuredRawTailInsertionJoinerAssemblyRestoreTapeStateSpec
      structuredRawTailInsertionJoinerDescription := by
  refine
    ⟨structuredRawTailInsertionJoinerDescription_assemblyRestoreSpec,
      ?_⟩
  intro p
  exact
    ⟨structuredRawTailInsertionJoinerRestoreHandoff_source_normalizedOutput_eq_target
        p,
      structuredRawTailInsertionJoinerRestoreHandoff_scratch_normalizedOutput
        p,
      structuredRawTailInsertionJoinerRestoreHandoff_work_normalizedOutput
        p⟩

def structuredRawTailInsertionJoinerAssemblyRunConfig
    (D : Structured.Description)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Configuration :=
  D.runConfig
    (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.runFuel
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p))
    (structuredRawTailInsertionJoinerInitialConfig p)

theorem structuredRawTailInsertionJoinerAssemblyRunConfig_eq_restoreHandoff
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredRawTailInsertionJoinerAssemblyRunConfig D p =
      Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoreTailHandoffConfig
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) := by
  exact hD.run p

theorem StructuredRawTailInsertionJoinerAssemblyRestoreSpec.run_source_normalizedOutput
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerAssemblyRunConfig D p).tapes 0) =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (List.append
          (assemblySourceRestLiveTailEmitterQuoteRest p)
          (assemblySourceRestLiveTailEmitterRawTail p)) := by
  rw [structuredRawTailInsertionJoinerAssemblyRunConfig_eq_restoreHandoff
    hD p]
  exact structuredRawTailInsertionJoinerRestoreHandoff_source_normalizedOutput
    p

theorem StructuredRawTailInsertionJoinerAssemblyRestoreSpec.run_source_normalizedOutput_eq_joined
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerAssemblyRunConfig D p).tapes 0) =
      Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailJoinedTape
          (assemblySourceRestLiveTailEmitterEmittedPrefix p)
          (assemblySourceRestLiveTailEmitterRawTail p)
          (assemblySourceRestLiveTailEmitterQuoteRest p)) := by
  rw [structuredRawTailInsertionJoinerAssemblyRunConfig_eq_restoreHandoff
    hD p]
  exact
    structuredRawTailInsertionJoinerRestoreHandoff_source_normalizedOutput_eq_joined
      p

theorem StructuredRawTailInsertionJoinerAssemblyRestoreSpec.run_source_normalizedOutput_eq_target
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerAssemblyRunConfig D p).tapes 0) =
      Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape
          p.w p.sourceRestBits p.stage) := by
  rw [structuredRawTailInsertionJoinerAssemblyRunConfig_eq_restoreHandoff
    hD p]
  exact
    structuredRawTailInsertionJoinerRestoreHandoff_source_normalizedOutput_eq_target
      p

theorem StructuredRawTailInsertionJoinerAssemblyRestoreSpec.run_scratch_normalizedOutput
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerAssemblyRunConfig D p).tapes 1) =
      assemblySourceRestLiveTailEmitterQuoteRest p := by
  rw [structuredRawTailInsertionJoinerAssemblyRunConfig_eq_restoreHandoff
    hD p]
  exact structuredRawTailInsertionJoinerRestoreHandoff_scratch_normalizedOutput
    p

theorem StructuredRawTailInsertionJoinerAssemblyRestoreSpec.run_work_normalizedOutput
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerAssemblyRunConfig D p).tapes 2) =
      [] := by
  rw [structuredRawTailInsertionJoinerAssemblyRunConfig_eq_restoreHandoff
    hD p]
  exact structuredRawTailInsertionJoinerRestoreHandoff_work_normalizedOutput p

def StructuredRawTailInsertionJoinerAssemblyRestoreRunOutputSpec
    (D : Structured.Description) : Prop :=
  StructuredRawTailInsertionJoinerAssemblyRestoreSpec D ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (structuredRawTailInsertionJoinerAssemblyRunConfig D p).tapes
            0) =
        Tape.normalizedOutput
          (mixedOptionCellQuoteLiveTailJoinedTape
            (assemblySourceRestLiveTailEmitterEmittedPrefix p)
            (assemblySourceRestLiveTailEmitterRawTail p)
            (assemblySourceRestLiveTailEmitterQuoteRest p))

theorem StructuredRawTailInsertionJoinerAssemblyRestoreRunOutputSpec.restore
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreRunOutputSpec D) :
    StructuredRawTailInsertionJoinerAssemblyRestoreSpec D :=
  hD.left

theorem StructuredRawTailInsertionJoinerAssemblyRestoreRunOutputSpec.output
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreRunOutputSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerAssemblyRunConfig D p).tapes 0) =
      Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailJoinedTape
          (assemblySourceRestLiveTailEmitterEmittedPrefix p)
          (assemblySourceRestLiveTailEmitterRawTail p)
          (assemblySourceRestLiveTailEmitterQuoteRest p)) :=
  hD.right p

theorem StructuredRawTailInsertionJoinerAssemblyRestoreRunOutputSpec.target
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreRunOutputSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerAssemblyRunConfig D p).tapes 0) =
      Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape
          p.w p.sourceRestBits p.stage) := by
  rw [hD.output p, assemblySourceRestLiveTailJoinerJoinedTape_eq_targetTape]

theorem StructuredRawTailInsertionJoinerAssemblyRestoreRunOutputSpec.source_words
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreRunOutputSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerAssemblyRunConfig D p).tapes 0) =
      List.append
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (List.append
          (assemblySourceRestLiveTailEmitterQuoteRest p)
          (assemblySourceRestLiveTailEmitterRawTail p)) :=
  hD.restore.run_source_normalizedOutput p

theorem StructuredRawTailInsertionJoinerAssemblyRestoreRunOutputSpec_of_restore
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreSpec D) :
    StructuredRawTailInsertionJoinerAssemblyRestoreRunOutputSpec D := by
  refine ⟨hD, ?_⟩
  intro p
  exact hD.run_source_normalizedOutput_eq_joined p

theorem structuredRawTailInsertionJoinerDescription_assemblyRestoreRunOutputSpec :
    StructuredRawTailInsertionJoinerAssemblyRestoreRunOutputSpec
      structuredRawTailInsertionJoinerDescription :=
  StructuredRawTailInsertionJoinerAssemblyRestoreRunOutputSpec_of_restore
    structuredRawTailInsertionJoinerDescription_assemblyRestoreSpec

def StructuredRawTailInsertionJoinerAssemblyRestoreRunTapeStateSpec
    (D : Structured.Description) : Prop :=
  StructuredRawTailInsertionJoinerAssemblyRestoreSpec D ∧
    forall p : AssemblySourceRestLiveTailEmitterParam,
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (structuredRawTailInsertionJoinerAssemblyRunConfig D p).tapes
            0) =
        Tape.normalizedOutput
          (assemblySourceRestFinishTargetTape
            p.w p.sourceRestBits p.stage) ∧
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (structuredRawTailInsertionJoinerAssemblyRunConfig D p).tapes
            1) =
        assemblySourceRestLiveTailEmitterQuoteRest p ∧
      Tape.normalizedOutput
          (Structured.Description.tapeAt
            (structuredRawTailInsertionJoinerAssemblyRunConfig D p).tapes
            2) =
        []

theorem StructuredRawTailInsertionJoinerAssemblyRestoreRunTapeStateSpec.restore
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreRunTapeStateSpec D) :
    StructuredRawTailInsertionJoinerAssemblyRestoreSpec D :=
  hD.left

theorem StructuredRawTailInsertionJoinerAssemblyRestoreRunTapeStateSpec.outputSpec
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreRunTapeStateSpec D) :
    StructuredRawTailInsertionJoinerAssemblyRestoreRunOutputSpec D := by
  refine ⟨hD.restore, ?_⟩
  intro p
  rw [(hD.right p).left]
  rw [← assemblySourceRestLiveTailJoinerJoinedTape_eq_targetTape]

theorem StructuredRawTailInsertionJoinerAssemblyRestoreRunTapeStateSpec.source
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreRunTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerAssemblyRunConfig D p).tapes 0) =
      Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape
          p.w p.sourceRestBits p.stage) :=
  (hD.right p).left

theorem StructuredRawTailInsertionJoinerAssemblyRestoreRunTapeStateSpec.scratch
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreRunTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerAssemblyRunConfig D p).tapes 1) =
      assemblySourceRestLiveTailEmitterQuoteRest p :=
  (hD.right p).right.left

theorem StructuredRawTailInsertionJoinerAssemblyRestoreRunTapeStateSpec.work
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreRunTapeStateSpec D)
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerAssemblyRunConfig D p).tapes 2) =
      [] :=
  (hD.right p).right.right

theorem StructuredRawTailInsertionJoinerAssemblyRestoreRunTapeStateSpec_of_restore
    {D : Structured.Description}
    (hD : StructuredRawTailInsertionJoinerAssemblyRestoreSpec D) :
    StructuredRawTailInsertionJoinerAssemblyRestoreRunTapeStateSpec D := by
  refine ⟨hD, ?_⟩
  intro p
  exact
    ⟨hD.run_source_normalizedOutput_eq_target p,
      hD.run_scratch_normalizedOutput p,
      hD.run_work_normalizedOutput p⟩

theorem structuredRawTailInsertionJoinerDescription_assemblyRestoreRunTapeStateSpec :
    StructuredRawTailInsertionJoinerAssemblyRestoreRunTapeStateSpec
      structuredRawTailInsertionJoinerDescription :=
  StructuredRawTailInsertionJoinerAssemblyRestoreRunTapeStateSpec_of_restore
    structuredRawTailInsertionJoinerDescription_assemblyRestoreSpec

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
