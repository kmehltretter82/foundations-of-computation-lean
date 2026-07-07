import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTJoinerOutput

set_option doc.verso true

/-!
# Live-tail joiner assembly construction

This module contains the assembly-specific packaging for the live-tail joiner.
The separated tape does not carry enough structure to support the arbitrary
stage/source joiner route, so this construction remains tied to the assembly
source-rest family whose prefix and raw-tail boundary are known.  The reusable
tape-shape facts and the impossibility guardrail live in
{module}`FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTJoinerRuns`.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

def MixedOptionCellQuoteLiveTailJoinerAssemblyFamilySpec
    (finish : MachineDescription) : Prop :=
  MixedOptionCellQuoteLiveTailJoinerFamilySpec
    assemblySourceRestLiveTailEmitterEmittedPrefix
    assemblySourceRestLiveTailEmitterRawTail
    assemblySourceRestLiveTailEmitterQuoteRest
    finish

def MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyConstruction :
    Prop :=
  MixedOptionCellQuoteLiveTailJoinerFamilyConstruction
    assemblySourceRestLiveTailEmitterEmittedPrefix
    assemblySourceRestLiveTailEmitterRawTail
    assemblySourceRestLiveTailEmitterQuoteRest

def MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputSpec
    (finish : MachineDescription) : Prop :=
  MixedOptionCellQuoteLiveTailJoinerFamilyOutputSpec
    assemblySourceRestLiveTailEmitterEmittedPrefix
    assemblySourceRestLiveTailEmitterRawTail
    assemblySourceRestLiveTailEmitterQuoteRest
    finish

def MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputConstruction :
    Prop :=
  MixedOptionCellQuoteLiveTailJoinerFamilyOutputConstruction
    assemblySourceRestLiveTailEmitterEmittedPrefix
    assemblySourceRestLiveTailEmitterRawTail
    assemblySourceRestLiveTailEmitterQuoteRest

theorem MixedOptionCellQuoteLiveTailJoinerAssemblyFamilySpec_iff_assemblySpec
    (finish : MachineDescription) :
    MixedOptionCellQuoteLiveTailJoinerAssemblyFamilySpec finish ↔
      MixedOptionCellQuoteLiveTailJoinerForAssemblySourceRestSpec finish := by
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

theorem MixedOptionCellQuoteLiveTailJoinerConstructionForAssemblySourceRest_of_family
    (h : MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyConstruction) :
    MixedOptionCellQuoteLiveTailJoinerConstructionForAssemblySourceRest := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨finish,
      (MixedOptionCellQuoteLiveTailJoinerAssemblyFamilySpec_iff_assemblySpec
        finish).mp hfinish⟩

theorem MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyConstruction_of_assembly
    (h : MixedOptionCellQuoteLiveTailJoinerConstructionForAssemblySourceRest) :
    MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨finish,
      (MixedOptionCellQuoteLiveTailJoinerAssemblyFamilySpec_iff_assemblySpec
        finish).mpr hfinish⟩

theorem MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputSpec_iff_assemblyOutputSpec
    (finish : MachineDescription) :
    MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputSpec finish ↔
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

theorem MixedOptionCellQuoteLiveTailJoinerOutputConstructionForAssemblySourceRest_of_outputFamily
    (h : MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputConstruction) :
    MixedOptionCellQuoteLiveTailJoinerOutputConstructionForAssemblySourceRest := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨finish,
      (MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputSpec_iff_assemblyOutputSpec
        finish).mp hfinish⟩

theorem MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputConstruction_of_assemblyOutput
    (h :
      MixedOptionCellQuoteLiveTailJoinerOutputConstructionForAssemblySourceRest) :
    MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨finish,
      (MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputSpec_iff_assemblyOutputSpec
        finish).mpr hfinish⟩

theorem MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputSpec_of_exact
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailJoinerAssemblyFamilySpec finish) :
    MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputSpec finish :=
  MixedOptionCellQuoteLiveTailJoinerFamilyOutputSpec_of_exact hfinish

theorem MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputConstruction_of_exact
    (h : MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyConstruction) :
    MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputConstruction :=
  MixedOptionCellQuoteLiveTailJoinerFamilyOutputConstruction_of_exact h

/--
Guardrail for the live-tail joiner construction.  The arbitrary stage/source
joiner route is inconsistent: the separated tape can erase the boundary between
the emitted prefix and the stage/source tail while the target tape still
depends on that boundary.  The assembly construction must therefore use the
assembly-specific prefix and raw-tail shape.
-/
theorem mixedOptionCellQuoteLiveTailStageSourceJoinerConstruction_impossible :
    ¬ MixedOptionCellQuoteLiveTailStageSourceJoinerConstruction :=
  not_MixedOptionCellQuoteLiveTailStageSourceJoinerConstruction

/--
Logical adapter only.  This theorem is useful when reading old attempts, but
the guardrail above proves that its premise cannot be supplied.
-/
theorem MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyConstruction_of_stageSource
    (h : MixedOptionCellQuoteLiveTailStageSourceJoinerConstruction) :
    MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyConstruction := by
  rcases h with ⟨finish, hfinish⟩
  refine ⟨finish, hfinish.left, ?_⟩
  intro p
  cases p with
  | mk w sourceRestBits stage =>
      exact hfinish.right
        (assemblySourceRestFinishPrefixQuoteOutputBits
          w sourceRestBits stage)
        sourceRestBits stage

theorem mixedOptionCellQuoteLiveTailJoinerAssemblyFamilyConstruction :
    MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyConstruction := by
  -- Remaining obligation: construct the assembly-specific live-tail joiner
  -- without using the refuted arbitrary stage/source joiner route.
  sorry

theorem mixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputConstruction :
    MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputConstruction :=
  MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputConstruction_of_exact
    mixedOptionCellQuoteLiveTailJoinerAssemblyFamilyConstruction

theorem mixedOptionCellQuoteLiveTailJoinerOutputConstruction_for_assemblySourceRest :
    MixedOptionCellQuoteLiveTailJoinerOutputConstructionForAssemblySourceRest :=
  MixedOptionCellQuoteLiveTailJoinerOutputConstructionForAssemblySourceRest_of_outputFamily
    mixedOptionCellQuoteLiveTailJoinerAssemblyFamilyOutputConstruction

/--
Specialized finite-table obligation for joining the reusable quote-rest field
in front of the source-rest live tail.  The arbitrary stage/source version is
too strong: the separated source tape does not carry a delimiter between an
arbitrary emitted prefix and the stage prefix, so this construction stays with
the assembly source-rest family required by the plan.
-/
theorem mixedOptionCellQuoteLiveTailJoinerConstruction :
    MixedOptionCellQuoteLiveTailJoinerConstructionForAssemblySourceRest := by
  exact
    MixedOptionCellQuoteLiveTailJoinerConstructionForAssemblySourceRest_of_family
      mixedOptionCellQuoteLiveTailJoinerAssemblyFamilyConstruction

def MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (MixedParserStackWholeSourceAfterRawTailScanTape
          w sourceRestBits stage)
        (MixedParserStackRewriterWholeSourceTargetTape
          (MixedParserStackRewriterTrueSourceCells
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage))

def MixedParserStackAfterRawTailScanJoinFinisherConstructionForAssemblySourceRest :
    Prop :=
  exists finish : MachineDescription,
    MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestSpec finish

theorem MixedParserStackAfterRawTailScanJoinFinisherConstructionForAssemblySourceRest_of_mixedOptionCellQuoteLiveTailJoiner
    (hjoin :
      MixedOptionCellQuoteLiveTailJoinerConstructionForAssemblySourceRest) :
    MixedParserStackAfterRawTailScanJoinFinisherConstructionForAssemblySourceRest := by
  rcases hjoin with ⟨finish, hfinish⟩
  refine ⟨finish, hfinish.left, ?_⟩
  intro w sourceRestBits stage
  rw [MixedParserStackWholeSourceAfterRawTailScanTape_eq_mixedOptionCellQuoteLiveTailSeparatedTape]
  rw [MixedParserStackRewriterWholeSourceTargetTape_eq_quoteRestJoinedTape]
  rw [← mixedOptionCellQuoteLiveTailJoinedTape_eq_assemblyQuoteRestJoinedTape]
  exact hfinish.right w sourceRestBits stage

/--
Finite-machine obligation for Phase 3 of the mixed parser-stack finisher.  It
joins the already-computed quoted source-rest field onto the emitted prefix and
leaves {lit}`stageBits ++ sourceRestBits` as the live right tail.
-/
theorem mixedParserStackAfterRawTailScanJoinFinisherConstruction_for_assemblySourceRest :
    MixedParserStackAfterRawTailScanJoinFinisherConstructionForAssemblySourceRest :=
  MixedParserStackAfterRawTailScanJoinFinisherConstructionForAssemblySourceRest_of_mixedOptionCellQuoteLiveTailJoiner
    mixedOptionCellQuoteLiveTailJoinerConstruction

theorem mixedParserStackAfterRawTailScanJoinFinisherOutputConstruction_for_assemblySourceRest :
    MixedParserStackAfterRawTailScanJoinFinisherOutputConstructionForAssemblySourceRest :=
  MixedParserStackAfterRawTailScanJoinFinisherOutputConstructionForAssemblySourceRest_of_mixedOptionCellQuoteLiveTailJoinerOutput
    mixedOptionCellQuoteLiveTailJoinerOutputConstruction_for_assemblySourceRest

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
