import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.PhaseOutputAdapters
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTEmitterConstruction
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTJoinerConstruction
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTGapOutput

set_option doc.verso true

/-!
# Live-tail source-rest equivalence and output route

This module composes the live-tail source-rest finish phases through tape
equivalence. The prefix and gap endpoints remain exact because they provide
physical handoff positions; the final joiner may retain trailing blank padding.
Normalized output is derived from this equivalence-facing route.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer

def mixedParserStackSourceRestFinishOutputMachine
    (prefixFinish gapFinish joinFinish : MachineDescription) :
    MachineDescription :=
  SeqViaCanonical prefixFinish
    (SeqViaCanonical gapFinish joinFinish)

def MixedParserStackSourceRestFinishAssemblyEquivSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTapeEquiv
        (MixedParserStackRewriterDefaultedInternalMarkerTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (assemblySourceRestFinishTargetTape
          w sourceRestBits stage)

def MixedParserStackSourceRestFinishAssemblyEquivConstruction :
    Prop :=
  exists finish : MachineDescription,
    MixedParserStackSourceRestFinishAssemblyEquivSpec finish

def MixedParserStackSourceRestFinishExactPrefixGapEquivComponentsSpec
    (prefixFinish gapFinish joinFinish : MachineDescription) : Prop :=
  MixedParserStackPrefixQuotedSeparatedFinisherAssemblySourceRestSpec
      prefixFinish ∧
    RightBlankGapPayloadScanAssemblyTapeSpec gapFinish ∧
    MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestEquivSpec
      joinFinish

def MixedParserStackSourceRestFinishExactPrefixGapEquivComponentsConstruction :
    Prop :=
  exists prefixFinish gapFinish joinFinish : MachineDescription,
    MixedParserStackSourceRestFinishExactPrefixGapEquivComponentsSpec
      prefixFinish gapFinish joinFinish

theorem MixedParserStackSourceRestFinishExactPrefixGapEquivComponentsConstruction.toEquivConstruction
    (h :
      MixedParserStackSourceRestFinishExactPrefixGapEquivComponentsConstruction) :
    MixedParserStackSourceRestFinishAssemblyEquivConstruction := by
  rcases h with ⟨prefixFinish, gapFinish, joinFinish, hprefix, hgap, hjoin⟩
  refine
    ⟨mixedParserStackSourceRestFinishOutputMachine
        prefixFinish gapFinish joinFinish, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady hprefix.left
        (SeqViaCanonical_subroutineReady hgap.subroutineReady hjoin.left)
  · intro w sourceRestBits stage
    have hjoinTarget :
        joinFinish.HaltsFromTapeEquiv
          (MixedParserStackWholeSourceAfterRawTailScanTape
            w sourceRestBits stage)
          (assemblySourceRestFinishTargetTape
            w sourceRestBits stage) := by
      simpa [MixedParserStackRewriterWholeSourceTargetTape_eq_quoteRestJoinedTape,
        assemblySourceRestFinishQuoteRestJoinedTape_eq_targetTape] using
        hjoin.right w sourceRestBits stage
    have hinner :
        (SeqViaCanonical gapFinish joinFinish).HaltsFromTapeEquiv
          (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
            w sourceRestBits stage)
          (assemblySourceRestFinishTargetTape
            w sourceRestBits stage) := by
      exact
        SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
          hgap.subroutineReady hjoin.left
          (hgap.haltsFromTape w sourceRestBits stage).toEquiv
          (by
            rw [MixedParserStackWholeSourceAfterRawTailScanTape_move_left_move_right]
            exact Tape.Equiv.refl _)
          hjoinTarget
    exact
      SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
        hprefix.left
        (SeqViaCanonical_subroutineReady hgap.subroutineReady hjoin.left)
        (hprefix.right w sourceRestBits stage).toEquiv
        (by
          rw [MixedParserStackWholeSourcePrefixQuotedSeparatedTape_move_left_move_right]
          exact Tape.Equiv.refl _)
        hinner

def MixedParserStackSourceRestFinishAssemblyOutputSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTapeWithOutput
        (MixedParserStackRewriterDefaultedInternalMarkerTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (assemblySourceRestFinishJoinedOutput
          w sourceRestBits stage)

def MixedParserStackSourceRestFinishAssemblyOutputConstruction :
    Prop :=
  exists finish : MachineDescription,
    MixedParserStackSourceRestFinishAssemblyOutputSpec finish

def MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec
    (prefixFinish gapFinish joinFinish : MachineDescription) : Prop :=
  MixedParserStackPrefixQuotedSeparatedFinisherAssemblySourceRestSpec
    prefixFinish ∧
  RightBlankGapPayloadScanAssemblyTapeSpec gapFinish ∧
  MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestOutputSpec
    joinFinish

def MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsConstruction :
    Prop :=
  exists prefixFinish gapFinish joinFinish : MachineDescription,
    MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec
      prefixFinish gapFinish joinFinish

theorem MixedParserStackSourceRestFinishAssemblyOutputSpec.subroutineReady
    {finish : MachineDescription}
    (hfinish :
      MixedParserStackSourceRestFinishAssemblyOutputSpec finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem MixedParserStackSourceRestFinishAssemblyOutputSpec.haltsFromTapeWithOutput
    {finish : MachineDescription}
    (hfinish :
      MixedParserStackSourceRestFinishAssemblyOutputSpec finish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    finish.HaltsFromTapeWithOutput
      (MixedParserStackRewriterDefaultedInternalMarkerTape
        w sourceRestBits
        (preservingCellPassCellBits sourceRestBits)
        stage)
      (assemblySourceRestFinishJoinedOutput
        w sourceRestBits stage) :=
  hfinish.right w sourceRestBits stage

theorem MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec.prefix
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec
        prefixFinish gapFinish joinFinish) :
    MixedParserStackPrefixQuotedSeparatedFinisherAssemblySourceRestSpec
      prefixFinish :=
  h.left

theorem MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec.gap
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec
        prefixFinish gapFinish joinFinish) :
    RightBlankGapPayloadScanAssemblyTapeSpec gapFinish :=
  h.right.left

theorem MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec.join
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec
        prefixFinish gapFinish joinFinish) :
    MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestOutputSpec
      joinFinish :=
  h.right.right

theorem MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec.prefix_subroutineReady
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec
        prefixFinish gapFinish joinFinish) :
    prefixFinish.SubroutineReady :=
  h.prefix.left

theorem MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec.gap_subroutineReady
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec
        prefixFinish gapFinish joinFinish) :
    gapFinish.SubroutineReady :=
  h.gap.subroutineReady

theorem MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec.join_subroutineReady
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec
        prefixFinish gapFinish joinFinish) :
    joinFinish.SubroutineReady :=
  MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestOutputSpec_subroutineReady
    h.join

theorem MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec.prefix_halts
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec
        prefixFinish gapFinish joinFinish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    prefixFinish.HaltsFromTape
      (MixedParserStackRewriterDefaultedInternalMarkerTape
        w sourceRestBits
        (preservingCellPassCellBits sourceRestBits)
        stage)
      (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
        w sourceRestBits stage) :=
  h.prefix.right w sourceRestBits stage

theorem MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec.gap_halts
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec
        prefixFinish gapFinish joinFinish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    gapFinish.HaltsFromTape
      (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
        w sourceRestBits stage)
      (MixedParserStackWholeSourceAfterRawTailScanTape
        w sourceRestBits stage) :=
  h.gap.haltsFromTape w sourceRestBits stage

theorem MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec.join_output
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec
        prefixFinish gapFinish joinFinish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    joinFinish.HaltsFromTapeWithOutput
      (MixedParserStackWholeSourceAfterRawTailScanTape
        w sourceRestBits stage)
      (assemblySourceRestFinishJoinedOutput
        w sourceRestBits stage) :=
  MixedParserStackAfterRawTailScanJoinFinisherAssemblySourceRestOutputSpec_haltsFromTapeWithJoinedOutput
    h.join w sourceRestBits stage

theorem mixedParserStackSourceRestFinishOutputMachine_subroutineReady
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec
        prefixFinish gapFinish joinFinish) :
    (mixedParserStackSourceRestFinishOutputMachine
      prefixFinish gapFinish joinFinish).SubroutineReady := by
  exact
    SeqViaCanonical_subroutineReady
      h.prefix_subroutineReady
      (SeqViaCanonical_subroutineReady
        h.gap_subroutineReady h.join_subroutineReady)

theorem mixedParserStackSourceRestFinishOutputMachine_haltsFromTapeWithOutput
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec
        prefixFinish gapFinish joinFinish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    (mixedParserStackSourceRestFinishOutputMachine
      prefixFinish gapFinish joinFinish).HaltsFromTapeWithOutput
      (MixedParserStackRewriterDefaultedInternalMarkerTape
        w sourceRestBits
        (preservingCellPassCellBits sourceRestBits)
        stage)
      (assemblySourceRestFinishJoinedOutput
        w sourceRestBits stage) := by
  have hinner :
      (SeqViaCanonical gapFinish joinFinish).HaltsFromTapeWithOutput
        (MixedParserStackWholeSourcePrefixQuotedSeparatedTape
          w sourceRestBits stage)
        (assemblySourceRestFinishJoinedOutput
          w sourceRestBits stage) :=
    SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape_eq
      h.gap_subroutineReady
      h.join_subroutineReady
      (h.gap_halts w sourceRestBits stage)
      (MixedParserStackWholeSourceAfterRawTailScanTape_move_left_move_right
        w sourceRestBits stage)
      (h.join_output w sourceRestBits stage)
  exact
    SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape_eq
      h.prefix_subroutineReady
      (SeqViaCanonical_subroutineReady
        h.gap_subroutineReady h.join_subroutineReady)
      (h.prefix_halts w sourceRestBits stage)
      (MixedParserStackWholeSourcePrefixQuotedSeparatedTape_move_left_move_right
        w sourceRestBits stage)
      hinner

theorem MixedParserStackSourceRestFinishAssemblyOutputSpec_of_components
    {prefixFinish gapFinish joinFinish : MachineDescription}
    (h :
      MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsSpec
        prefixFinish gapFinish joinFinish) :
    MixedParserStackSourceRestFinishAssemblyOutputSpec
      (mixedParserStackSourceRestFinishOutputMachine
        prefixFinish gapFinish joinFinish) := by
  constructor
  · exact mixedParserStackSourceRestFinishOutputMachine_subroutineReady h
  · intro w sourceRestBits stage
    exact
      mixedParserStackSourceRestFinishOutputMachine_haltsFromTapeWithOutput
        h w sourceRestBits stage

theorem MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsConstruction.toOutputConstruction
    (h :
      MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsConstruction) :
    MixedParserStackSourceRestFinishAssemblyOutputConstruction := by
  rcases h with ⟨prefixFinish, gapFinish, joinFinish, hcomponents⟩
  exact
    ⟨mixedParserStackSourceRestFinishOutputMachine
        prefixFinish gapFinish joinFinish,
      MixedParserStackSourceRestFinishAssemblyOutputSpec_of_components
        hcomponents⟩

theorem mixedParserStackSourceRestFinishExactPrefixGapEquivComponents_for_assemblySourceRest :
    MixedParserStackSourceRestFinishExactPrefixGapEquivComponentsConstruction := by
  rcases
      mixedParserStackPrefixQuotedSeparatedFinisherConstruction_for_assemblySourceRest
      with
    ⟨prefixFinish, hprefix⟩
  rcases
      mixedParserStackAfterRawTailScanJoinFinisherEquivConstruction_for_assemblySourceRest
      with
    ⟨joinFinish, hjoin⟩
  exact
    ⟨prefixFinish,
      CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription,
      joinFinish,
      hprefix,
      rightBlankGapPayloadScanDescription_assemblyTapeSpec,
      hjoin⟩

theorem mixedParserStackSourceRestFinishEquivConstruction_for_assemblySourceRest :
    MixedParserStackSourceRestFinishAssemblyEquivConstruction :=
  MixedParserStackSourceRestFinishExactPrefixGapEquivComponentsConstruction.toEquivConstruction
    mixedParserStackSourceRestFinishExactPrefixGapEquivComponents_for_assemblySourceRest

theorem MixedParserStackSourceRestFinishAssemblyOutputSpec_of_equiv
    {finish : MachineDescription}
    (hfinish : MixedParserStackSourceRestFinishAssemblyEquivSpec finish) :
    MixedParserStackSourceRestFinishAssemblyOutputSpec finish := by
  refine ⟨hfinish.left, ?_⟩
  intro w sourceRestBits stage
  simpa [assemblySourceRestFinishJoinedOutput_eq_targetTape_normalizedOutput]
    using
      MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv
        (hfinish.right w sourceRestBits stage)

theorem MixedParserStackSourceRestFinishAssemblyOutputConstruction_of_equiv
    (hfinish : MixedParserStackSourceRestFinishAssemblyEquivConstruction) :
    MixedParserStackSourceRestFinishAssemblyOutputConstruction := by
  rcases hfinish with ⟨finish, hspec⟩
  exact
    ⟨finish,
      MixedParserStackSourceRestFinishAssemblyOutputSpec_of_equiv hspec⟩

theorem mixedParserStackSourceRestFinishExactPrefixGapOutputComponents_for_assemblySourceRest :
    MixedParserStackSourceRestFinishExactPrefixGapOutputComponentsConstruction := by
  rcases
      mixedParserStackPrefixQuotedSeparatedFinisherConstruction_for_assemblySourceRest
      with
    ⟨prefixFinish, hprefix⟩
  rcases
      mixedParserStackAfterRawTailScanJoinFinisherOutputConstruction_for_assemblySourceRest
      with
    ⟨joinFinish, hjoin⟩
  exact
    ⟨prefixFinish,
      CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription,
      joinFinish,
      hprefix,
      rightBlankGapPayloadScanDescription_assemblyTapeSpec,
      hjoin⟩

theorem mixedParserStackSourceRestFinishOutputConstruction_for_assemblySourceRest :
    MixedParserStackSourceRestFinishAssemblyOutputConstruction :=
  MixedParserStackSourceRestFinishAssemblyOutputConstruction_of_equiv
    mixedParserStackSourceRestFinishEquivConstruction_for_assemblySourceRest

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
