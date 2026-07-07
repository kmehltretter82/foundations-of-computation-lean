import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTEmitterOutput
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTEmitterStructuredQuote

set_option doc.verso true

/-!
# Live-tail emitter assembly construction

This module contains the assembly-specific packaging for the live-tail emitter.
The raw tape-shape definitions and exact source/target shape lemmas remain in
{module}`FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTEmitterRuns`.
Keeping this layer separate leaves the run module as reusable local theory,
while this file carries the finite-machine leaf that must eventually build the
emitter family for the assembly source-rest route.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
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

theorem MixedOptionCellQuoteLiveTailEmitterAssemblyFamilySpec_iff_assemblySpec
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

theorem MixedOptionCellQuoteLiveTailEmitterConstructionForAssemblySourceRest_of_family
    (h : MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyConstruction) :
    MixedOptionCellQuoteLiveTailEmitterConstructionForAssemblySourceRest := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨finish,
      (MixedOptionCellQuoteLiveTailEmitterAssemblyFamilySpec_iff_assemblySpec
        finish).mp hfinish⟩

theorem MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyConstruction_of_assembly
    (h : MixedOptionCellQuoteLiveTailEmitterConstructionForAssemblySourceRest) :
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨finish,
      (MixedOptionCellQuoteLiveTailEmitterAssemblyFamilySpec_iff_assemblySpec
        finish).mpr hfinish⟩

theorem MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec_of_exact
    {finish : MachineDescription}
    (hfinish :
      MixedOptionCellQuoteLiveTailEmitterAssemblyFamilySpec finish) :
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputSpec finish :=
  MixedOptionCellQuoteLiveTailEmitterFamilyOutputSpec_of_exact hfinish

theorem MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputConstruction_of_exact
    (h : MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyConstruction) :
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputConstruction :=
  MixedOptionCellQuoteLiveTailEmitterFamilyOutputConstruction_of_exact h

/--
Reusable emitter obligation for the specialized assembly parser-prefix grammar.
It quotes the defaulted mixed option-cell prefix and stage prefix, leaves the
live raw tail to the right, and keeps the already-computed quote-rest separated
for the live-tail joiner.
-/
theorem mixedOptionCellQuoteLiveTailEmitterAssemblyFamilyConstruction :
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyConstruction := by
  sorry

theorem mixedOptionCellQuoteLiveTailEmitterConstruction_for_assemblySourceRest :
    MixedOptionCellQuoteLiveTailEmitterConstructionForAssemblySourceRest := by
  exact
    MixedOptionCellQuoteLiveTailEmitterConstructionForAssemblySourceRest_of_family
      mixedOptionCellQuoteLiveTailEmitterAssemblyFamilyConstruction

theorem mixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputConstruction :
    MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputConstruction :=
  MixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputConstruction_of_exact
    mixedOptionCellQuoteLiveTailEmitterAssemblyFamilyConstruction

theorem mixedOptionCellQuoteLiveTailEmitterOutputConstruction_for_assemblySourceRest :
    MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest :=
  MixedOptionCellQuoteLiveTailEmitterOutputConstructionForAssemblySourceRest_of_outputFamily
    mixedOptionCellQuoteLiveTailEmitterAssemblyFamilyOutputConstruction

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

def MixedParserStackPrefixQuotedSeparatedFinisherConstructionForAssemblySourceRest :
    Prop :=
  exists finish : MachineDescription,
    MixedParserStackPrefixQuotedSeparatedFinisherAssemblySourceRestSpec finish

/--
Finite-machine obligation for Phase 1 and Phase 2 of the mixed parser-stack
finisher.  It emits the header and quoted parser-prefix/stage prefix, leaves
the live raw tail on the right, and keeps the reusable source-rest quote behind
the structural blank for the final join phase.
-/
theorem mixedParserStackPrefixQuotedSeparatedFinisherConstruction_for_assemblySourceRest :
    MixedParserStackPrefixQuotedSeparatedFinisherConstructionForAssemblySourceRest := by
  rcases mixedOptionCellQuoteLiveTailEmitterConstruction_for_assemblySourceRest with
    ⟨finish, hfinish⟩
  refine ⟨finish, hfinish.left, ?_⟩
  intro w sourceRestBits stage
  rw [MixedParserStackRewriterDefaultedInternalMarkerTape_eq_mixedOptionCellQuoteLiveTailEmitterSplitSourceTape]
  rw [MixedParserStackWholeSourcePrefixQuotedSeparatedTape_eq_mixedOptionCellQuoteLiveTailEmitterTargetTape]
  exact hfinish.right w sourceRestBits stage

theorem mixedParserStackPrefixQuotedSeparatedFinisherOutputConstruction_for_assemblySourceRest :
    MixedParserStackPrefixQuotedSeparatedFinisherOutputConstructionForAssemblySourceRest :=
  assemblySourceRestOutputConstruction_ofLiveTailEmitterOutput
    mixedOptionCellQuoteLiveTailEmitterOutputConstruction_for_assemblySourceRest

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
