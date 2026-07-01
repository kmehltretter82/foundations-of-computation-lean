import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.LiveTail

set_option doc.verso true

/-!
# Live-tail joiner assembly construction

This module contains the assembly-specific packaging for the live-tail joiner.
The separated tape does not carry enough structure to support the arbitrary
stage/source joiner route, so this construction remains tied to the assembly
source-rest family whose prefix and raw-tail boundary are known.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
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

theorem
    MixedOptionCellQuoteLiveTailJoinerAssemblyFamilySpec_iff_assemblySpec
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

theorem
    MixedOptionCellQuoteLiveTailJoinerConstructionForAssemblySourceRest_of_family
    (h : MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyConstruction) :
    MixedOptionCellQuoteLiveTailJoinerConstructionForAssemblySourceRest := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨finish,
      (MixedOptionCellQuoteLiveTailJoinerAssemblyFamilySpec_iff_assemblySpec
        finish).mp hfinish⟩

theorem
    MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyConstruction_of_assembly
    (h : MixedOptionCellQuoteLiveTailJoinerConstructionForAssemblySourceRest) :
    MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨finish,
      (MixedOptionCellQuoteLiveTailJoinerAssemblyFamilySpec_iff_assemblySpec
        finish).mpr hfinish⟩

theorem
    MixedOptionCellQuoteLiveTailJoinerAssemblyFamilyConstruction_of_stageSource
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
  sorry

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

