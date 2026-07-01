import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.LiveTail

set_option doc.verso true

/-!
# Live-tail emitter assembly construction

This module contains the assembly-specific packaging for the live-tail emitter.
The raw tape-shape definitions and exact source/target shape lemmas remain in
the live-tail core module.  Keeping this layer separate leaves the core module
as reusable local theory, while this file carries the finite-machine leaf that
must eventually build the emitter family for the assembly source-rest route.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

def MixedOptionCellQuoteLiveTailEmitterAssemblyFamilySpec
    (finish : MachineDescription) : Prop :=
  MixedOptionCellQuoteLiveTailEmitterFamilySpec
    assemblySourceRestLiveTailEmitterLeftRev
    assemblySourceRestLiveTailEmitterQuoteScan
    assemblySourceRestLiveTailEmitterRawTail
    assemblySourceRestLiveTailEmitterQuoteRest
    assemblySourceRestLiveTailEmitterEmittedPrefix
    finish

def MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyConstruction :
    Prop :=
  MixedOptionCellQuoteLiveTailEmitterFamilyConstruction
    assemblySourceRestLiveTailEmitterLeftRev
    assemblySourceRestLiveTailEmitterQuoteScan
    assemblySourceRestLiveTailEmitterRawTail
    assemblySourceRestLiveTailEmitterQuoteRest
    assemblySourceRestLiveTailEmitterEmittedPrefix

theorem
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilySpec_iff_assemblySpec
    (finish : MachineDescription) :
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilySpec finish ↔
      MixedOptionCellQuoteLiveTailEmitterForAssemblySourceRestSpec finish := by
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
    MixedOptionCellQuoteLiveTailEmitterConstructionForAssemblySourceRest_of_family
    (h : MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyConstruction) :
    MixedOptionCellQuoteLiveTailEmitterConstructionForAssemblySourceRest := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨finish,
      (MixedOptionCellQuoteLiveTailEmitterAssemblyFamilySpec_iff_assemblySpec
        finish).mp hfinish⟩

theorem
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyConstruction_of_assembly
    (h : MixedOptionCellQuoteLiveTailEmitterConstructionForAssemblySourceRest) :
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨finish,
      (MixedOptionCellQuoteLiveTailEmitterAssemblyFamilySpec_iff_assemblySpec
        finish).mpr hfinish⟩

theorem mixedOptionCellQuoteLiveTailEmitterAssemblyFamilyConstruction :
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyConstruction := by
  sorry

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC

