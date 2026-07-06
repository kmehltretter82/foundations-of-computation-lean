import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.Projection.Quoter.SourceRestFinishCore.LTJoinerStructured

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

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
