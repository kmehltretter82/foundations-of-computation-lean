import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.LiveTail.EmitterRuns

set_option doc.verso true

/-!
# Live-tail emitter assembly construction

This module contains the assembly-specific packaging for the live-tail emitter.
The raw tape-shape definitions and exact source/target shape lemmas remain in
{module}`FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.LiveTail.EmitterRuns`.
Keeping this layer separate leaves the run module as reusable local theory,
while this file carries the finite-machine leaf that must eventually build the
emitter family for the assembly source-rest route.
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

/--
Reusable emitter obligation for the specialized assembly parser-prefix grammar.
It quotes the defaulted mixed option-cell prefix and stage prefix, leaves the
live raw tail to the right, and keeps the already-computed quote-rest separated
for the live-tail joiner.
-/
theorem
    mixedOptionCellQuoteLiveTailEmitterConstruction_for_assemblySourceRest :
    MixedOptionCellQuoteLiveTailEmitterConstructionForAssemblySourceRest := by
  exact
    MixedOptionCellQuoteLiveTailEmitterConstructionForAssemblySourceRest_of_family
      mixedOptionCellQuoteLiveTailEmitterAssemblyFamilyConstruction

def MixedParserStackPrefixQuotedSeparatedFinisherAssemblySourceRestSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (MixedParserStackRewriterDefaultedInternalMarkerTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
          w sourceRestBits stage)

def
    MixedParserStackPrefixQuotedSeparatedFinisherConstructionForAssemblySourceRest :
    Prop :=
  exists finish : MachineDescription,
    MixedParserStackPrefixQuotedSeparatedFinisherAssemblySourceRestSpec finish

theorem
    MixedParserStackPrefixQuotedSeparatedFinisherConstructionForAssemblySourceRest_of_mixedOptionCellQuoteLiveTailEmitter
    (hemitter :
      MixedOptionCellQuoteLiveTailEmitterConstructionForAssemblySourceRest) :
    MixedParserStackPrefixQuotedSeparatedFinisherConstructionForAssemblySourceRest := by
  rcases hemitter with ⟨finish, hfinish⟩
  refine ⟨finish, hfinish.left, ?_⟩
  intro w sourceRestBits stage
  rw [MixedParserStackRewriterDefaultedInternalMarkerTape_eq_mixedOptionCellQuoteLiveTailEmitterSplitSourceTape]
  rw [MixedParserStackWholeSourcePrefixQuotedSeparatedTape_eq_mixedOptionCellQuoteLiveTailEmitterTargetTape]
  exact hfinish.right w sourceRestBits stage

/--
Finite-machine obligation for Phase 1 and Phase 2 of the mixed parser-stack
finisher.  It emits the header and quoted parser-prefix/stage prefix, leaves
the live raw tail on the right, and keeps the reusable source-rest quote behind
the structural blank for the final join phase.
-/
theorem
    mixedParserStackPrefixQuotedSeparatedFinisherConstruction_for_assemblySourceRest :
    MixedParserStackPrefixQuotedSeparatedFinisherConstructionForAssemblySourceRest :=
  MixedParserStackPrefixQuotedSeparatedFinisherConstructionForAssemblySourceRest_of_mixedOptionCellQuoteLiveTailEmitter
    mixedOptionCellQuoteLiveTailEmitterConstruction_for_assemblySourceRest

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
