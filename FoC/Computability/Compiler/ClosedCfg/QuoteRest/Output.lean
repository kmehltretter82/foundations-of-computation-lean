import FoC.Computability.Compiler.Core.EncRewriters.ClosedCfgRunner.PhaseOutputAdapters
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.Construction
import FoC.Computability.Compiler.ClosedCfg.QuoteRest.DirectJoinedEndpoint

set_option doc.verso true

/-!
# Source-rest finish output route

The direct joined endpoint emits the normalized source-rest word and then
positions the head at the live raw-tail boundary.  This module lifts that exact
inner construction through the scanner wrappers used by the public finish
phase and also exposes normalized-output adapters.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer

/-! ## Public output contracts -/

def assemblySourceRestFinishOutput
    (w sourceRestBits : Word Bool) (stage : Nat) : Word Bool :=
  assemblySourceRestFinishJoinedOutput w sourceRestBits stage

theorem assemblySourceRestFinishOutput_eq_joinedOutput
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishOutput w sourceRestBits stage =
      assemblySourceRestFinishJoinedOutput w sourceRestBits stage := by
  rfl

theorem assemblySourceRestFinishOutput_eq_targetTape_normalizedOutput
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishOutput w sourceRestBits stage =
      Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape w sourceRestBits stage) := by
  rw [assemblySourceRestFinishOutput,
    assemblySourceRestFinishJoinedOutput_eq_targetTape_normalizedOutput]

theorem assemblySourceRestFinishOutput_eq_targetTape_namedOutput
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishOutput w sourceRestBits stage =
      List.append
        (assemblySourceRestFinishTargetPrefixBits
          w sourceRestBits stage)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits) := by
  rw [assemblySourceRestFinishOutput,
    assemblySourceRestFinishJoinedOutput_eq_targetTape_namedOutput]

def AssemblySourceRestFinishEquivSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTapeEquiv
        (assemblySourceRestFinishSourceTape w sourceRestBits stage)
        (assemblySourceRestFinishTargetTape w sourceRestBits stage)

def AssemblySourceRestFinishEquivConstruction : Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestFinishEquivSpec finish

def AssemblySourceRestFinishOutputSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTapeWithOutput
        (assemblySourceRestFinishSourceTape w sourceRestBits stage)
        (assemblySourceRestFinishOutput w sourceRestBits stage)

def AssemblySourceRestFinishOutputConstruction : Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestFinishOutputSpec finish

theorem AssemblySourceRestFinishEquivSpec.subroutineReady
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishEquivSpec finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem AssemblySourceRestFinishEquivSpec.haltsFromTapeEquiv
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishEquivSpec finish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    finish.HaltsFromTapeEquiv
      (assemblySourceRestFinishSourceTape w sourceRestBits stage)
      (assemblySourceRestFinishTargetTape w sourceRestBits stage) :=
  hfinish.right w sourceRestBits stage

def AssemblySourceRestFinishBoundaryOutputSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTapeWithOutput
        (assemblySourceRestFinishBoundaryTape w sourceRestBits stage)
        (assemblySourceRestFinishOutput w sourceRestBits stage)

def AssemblySourceRestFinishBoundaryOutputConstruction : Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestFinishBoundaryOutputSpec finish

def AssemblySourceRestFinishQuoteBoundaryOutputSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTapeWithOutput
        (assemblySourceRestFinishQuoteBoundaryTape w sourceRestBits stage)
        (assemblySourceRestFinishOutput w sourceRestBits stage)

def AssemblySourceRestFinishQuoteBoundaryOutputConstruction : Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestFinishQuoteBoundaryOutputSpec finish

def AssemblySourceRestFinishLeftBoundaryOutputSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTapeWithOutput
        (assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage)
        (assemblySourceRestFinishOutput w sourceRestBits stage)

def AssemblySourceRestFinishLeftBoundaryOutputConstruction : Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestFinishLeftBoundaryOutputSpec finish

def AssemblySourceRestFinishLeftBoundaryCoreOutputConstruction : Prop :=
  AssemblySourceRestFinishLeftBoundaryOutputConstruction

/-! ## Mixed parser-stack output contracts -/

def MixedParserStackFinisherAssemblySourceRestOutputSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTapeWithOutput
        (MixedParserStackRewriterSourceTape
          (assemblySourceRestFinishParserPrefixCells w)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits
          (preservingCellPassCellBits sourceRestBits))
        (assemblySourceRestFinishOutput w sourceRestBits stage)

def MixedParserStackFinisherOutputConstructionForAssemblySourceRest :
    Prop :=
  exists finish : MachineDescription,
    MixedParserStackFinisherAssemblySourceRestOutputSpec finish

def MixedParserStackTrueLeftBoundaryFinisherAssemblySourceRestOutputSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTapeWithOutput
        (MixedParserStackRewriterTrueLeftBoundaryTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (assemblySourceRestFinishOutput w sourceRestBits stage)

def MixedParserStackTrueLeftBoundaryFinisherOutputConstructionForAssemblySourceRest :
    Prop :=
  exists finish : MachineDescription,
    MixedParserStackTrueLeftBoundaryFinisherAssemblySourceRestOutputSpec
      finish

def MixedParserStackDefaultedInternalMarkerFinisherAssemblySourceRestOutputSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTapeWithOutput
        (MixedParserStackRewriterDefaultedInternalMarkerTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (assemblySourceRestFinishOutput w sourceRestBits stage)

def MixedParserStackDefaultedInternalMarkerFinisherOutputConstructionForAssemblySourceRest :
    Prop :=
  exists finish : MachineDescription,
    MixedParserStackDefaultedInternalMarkerFinisherAssemblySourceRestOutputSpec
      finish

/-! ## Spec accessors -/

theorem AssemblySourceRestFinishOutputSpec.subroutineReady
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishOutputSpec finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem AssemblySourceRestFinishOutputSpec.haltsFromTapeWithOutput
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishOutputSpec finish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    finish.HaltsFromTapeWithOutput
      (assemblySourceRestFinishSourceTape w sourceRestBits stage)
      (assemblySourceRestFinishOutput w sourceRestBits stage) :=
  hfinish.right w sourceRestBits stage

theorem AssemblySourceRestFinishOutputSpec.haltsFromTapeWithTargetOutput
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishOutputSpec finish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    finish.HaltsFromTapeWithOutput
      (assemblySourceRestFinishSourceTape w sourceRestBits stage)
      (Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape w sourceRestBits stage)) := by
  rw [← assemblySourceRestFinishOutput_eq_targetTape_normalizedOutput]
  exact hfinish.haltsFromTapeWithOutput w sourceRestBits stage

theorem AssemblySourceRestFinishBoundaryOutputSpec.subroutineReady
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishBoundaryOutputSpec finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem AssemblySourceRestFinishBoundaryOutputSpec.haltsFromTapeWithOutput
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishBoundaryOutputSpec finish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    finish.HaltsFromTapeWithOutput
      (assemblySourceRestFinishBoundaryTape w sourceRestBits stage)
      (assemblySourceRestFinishOutput w sourceRestBits stage) :=
  hfinish.right w sourceRestBits stage

theorem AssemblySourceRestFinishQuoteBoundaryOutputSpec.subroutineReady
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishQuoteBoundaryOutputSpec finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem AssemblySourceRestFinishQuoteBoundaryOutputSpec.haltsFromTapeWithOutput
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishQuoteBoundaryOutputSpec finish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    finish.HaltsFromTapeWithOutput
      (assemblySourceRestFinishQuoteBoundaryTape w sourceRestBits stage)
      (assemblySourceRestFinishOutput w sourceRestBits stage) :=
  hfinish.right w sourceRestBits stage

theorem AssemblySourceRestFinishLeftBoundaryOutputSpec.subroutineReady
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishLeftBoundaryOutputSpec finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem AssemblySourceRestFinishLeftBoundaryOutputSpec.haltsFromTapeWithOutput
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishLeftBoundaryOutputSpec finish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    finish.HaltsFromTapeWithOutput
      (assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage)
      (assemblySourceRestFinishOutput w sourceRestBits stage) :=
  hfinish.right w sourceRestBits stage

theorem MixedParserStackFinisherAssemblySourceRestOutputSpec.subroutineReady
    {finish : MachineDescription}
    (hfinish :
      MixedParserStackFinisherAssemblySourceRestOutputSpec finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem MixedParserStackFinisherAssemblySourceRestOutputSpec.haltsFromTapeWithOutput
    {finish : MachineDescription}
    (hfinish :
      MixedParserStackFinisherAssemblySourceRestOutputSpec finish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    finish.HaltsFromTapeWithOutput
      (MixedParserStackRewriterSourceTape
        (assemblySourceRestFinishParserPrefixCells w)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage)
        sourceRestBits
        (preservingCellPassCellBits sourceRestBits))
      (assemblySourceRestFinishOutput w sourceRestBits stage) :=
  hfinish.right w sourceRestBits stage

theorem MixedParserStackTrueLeftBoundaryFinisherAssemblySourceRestOutputSpec.subroutineReady
    {finish : MachineDescription}
    (hfinish :
      MixedParserStackTrueLeftBoundaryFinisherAssemblySourceRestOutputSpec
        finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem MixedParserStackTrueLeftBoundaryFinisherAssemblySourceRestOutputSpec.haltsFromTapeWithOutput
    {finish : MachineDescription}
    (hfinish :
      MixedParserStackTrueLeftBoundaryFinisherAssemblySourceRestOutputSpec
        finish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    finish.HaltsFromTapeWithOutput
      (MixedParserStackRewriterTrueLeftBoundaryTape
        w sourceRestBits
        (preservingCellPassCellBits sourceRestBits)
        stage)
      (assemblySourceRestFinishOutput w sourceRestBits stage) :=
  hfinish.right w sourceRestBits stage

theorem MixedParserStackDefaultedInternalMarkerFinisherAssemblySourceRestOutputSpec.subroutineReady
    {finish : MachineDescription}
    (hfinish :
      MixedParserStackDefaultedInternalMarkerFinisherAssemblySourceRestOutputSpec
        finish) :
    finish.SubroutineReady :=
  hfinish.left

theorem MixedParserStackDefaultedInternalMarkerFinisherAssemblySourceRestOutputSpec.haltsFromTapeWithOutput
    {finish : MachineDescription}
    (hfinish :
      MixedParserStackDefaultedInternalMarkerFinisherAssemblySourceRestOutputSpec
        finish)
    (w sourceRestBits : Word Bool) (stage : Nat) :
    finish.HaltsFromTapeWithOutput
      (MixedParserStackRewriterDefaultedInternalMarkerTape
        w sourceRestBits
        (preservingCellPassCellBits sourceRestBits)
        stage)
      (assemblySourceRestFinishOutput w sourceRestBits stage) :=
  hfinish.right w sourceRestBits stage

/-! ## Tape-to-output adapters -/

private theorem haltsFromTapeWithOutput_of_haltsFromTape_target
    {D : MachineDescription} {Tin Tout : Tape Bool}
    (h : D.HaltsFromTape Tin Tout) :
    D.HaltsFromTapeWithOutput Tin (Tape.normalizedOutput Tout) :=
  MachineDescription.haltsFromTapeWithOutput_of_haltsFromTape h

theorem AssemblySourceRestFinishEquivSpec.toOutputSpec
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishEquivSpec finish) :
    AssemblySourceRestFinishOutputSpec finish := by
  constructor
  · exact hfinish.left
  · intro w sourceRestBits stage
    rw [assemblySourceRestFinishOutput_eq_targetTape_normalizedOutput]
    exact
      MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv
        (hfinish.right w sourceRestBits stage)

theorem AssemblySourceRestFinishEquivConstruction.toOutputConstruction
    (h : AssemblySourceRestFinishEquivConstruction) :
    AssemblySourceRestFinishOutputConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact ⟨finish, hfinish.toOutputSpec⟩

theorem AssemblySourceRestFinishSpec.toOutputSpec
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishSpec finish) :
    AssemblySourceRestFinishOutputSpec finish := by
  constructor
  · exact hfinish.left
  · intro w sourceRestBits stage
    rw [assemblySourceRestFinishOutput_eq_targetTape_normalizedOutput]
    exact
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hfinish.right w sourceRestBits stage)

theorem AssemblySourceRestFinishConstruction.toOutputConstruction
    (h : AssemblySourceRestFinishConstruction) :
    AssemblySourceRestFinishOutputConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact ⟨finish, hfinish.toOutputSpec⟩

theorem AssemblySourceRestFinishBoundarySpec.toOutputSpec
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishBoundarySpec finish) :
    AssemblySourceRestFinishBoundaryOutputSpec finish := by
  constructor
  · exact hfinish.left
  · intro w sourceRestBits stage
    rw [assemblySourceRestFinishOutput_eq_targetTape_normalizedOutput]
    exact
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hfinish.right w sourceRestBits stage)

theorem AssemblySourceRestFinishBoundaryConstruction.toOutputConstruction
    (h : AssemblySourceRestFinishBoundaryConstruction) :
    AssemblySourceRestFinishBoundaryOutputConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact ⟨finish, hfinish.toOutputSpec⟩

theorem AssemblySourceRestFinishQuoteBoundarySpec.toOutputSpec
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishQuoteBoundarySpec finish) :
    AssemblySourceRestFinishQuoteBoundaryOutputSpec finish := by
  constructor
  · exact hfinish.left
  · intro w sourceRestBits stage
    rw [assemblySourceRestFinishOutput_eq_targetTape_normalizedOutput]
    exact
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hfinish.right w sourceRestBits stage)

theorem AssemblySourceRestFinishQuoteBoundaryConstruction.toOutputConstruction
    (h : AssemblySourceRestFinishQuoteBoundaryConstruction) :
    AssemblySourceRestFinishQuoteBoundaryOutputConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact ⟨finish, hfinish.toOutputSpec⟩

theorem AssemblySourceRestFinishLeftBoundarySpec.toOutputSpec
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishLeftBoundarySpec finish) :
    AssemblySourceRestFinishLeftBoundaryOutputSpec finish := by
  constructor
  · exact hfinish.left
  · intro w sourceRestBits stage
    rw [assemblySourceRestFinishOutput_eq_targetTape_normalizedOutput]
    exact
      haltsFromTapeWithOutput_of_haltsFromTape_target
        (hfinish.right w sourceRestBits stage)

theorem AssemblySourceRestFinishLeftBoundaryConstruction.toOutputConstruction
    (h : AssemblySourceRestFinishLeftBoundaryConstruction) :
    AssemblySourceRestFinishLeftBoundaryOutputConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact ⟨finish, hfinish.toOutputSpec⟩

theorem MixedParserStackSourceRestFinishAssemblyOutputSpec.toDefaultedInternalMarkerSpec
    {finish : MachineDescription}
    (hfinish : MixedParserStackSourceRestFinishAssemblyOutputSpec finish) :
    MixedParserStackDefaultedInternalMarkerFinisherAssemblySourceRestOutputSpec
      finish := by
  constructor
  · exact hfinish.left
  · intro w sourceRestBits stage
    simpa [assemblySourceRestFinishOutput] using
      hfinish.haltsFromTapeWithOutput w sourceRestBits stage

theorem MixedParserStackSourceRestFinishAssemblyOutputConstruction.toDefaultedInternalMarkerConstruction
    (h : MixedParserStackSourceRestFinishAssemblyOutputConstruction) :
    MixedParserStackDefaultedInternalMarkerFinisherOutputConstructionForAssemblySourceRest := by
  rcases h with ⟨finish, hfinish⟩
  exact ⟨finish, hfinish.toDefaultedInternalMarkerSpec⟩

/-! ## Scanner output lifting -/

theorem MixedParserStackTrueLeftBoundaryFinisherOutputConstructionForAssemblySourceRest_of_defaultedInternalMarker
    (h :
      MixedParserStackDefaultedInternalMarkerFinisherOutputConstructionForAssemblySourceRest) :
    MixedParserStackTrueLeftBoundaryFinisherOutputConstructionForAssemblySourceRest := by
  rcases h with ⟨finish, hfinish⟩
  refine
    ⟨SeqViaCanonical
      mixedParserStackDefaultInternalMarkerDescription finish, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        mixedParserStackDefaultInternalMarkerDescription_subroutineReady
        hfinish.subroutineReady
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape_eq
        mixedParserStackDefaultInternalMarkerDescription_subroutineReady
        hfinish.subroutineReady
        (mixedParserStackDefaultInternalMarkerDescription_haltsFrom_trueLeftBoundaryTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (MixedParserStackRewriterDefaultedInternalMarkerTape_move_left_move_right
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (hfinish.haltsFromTapeWithOutput w sourceRestBits stage)

theorem MixedParserStackFinisherOutputConstructionForAssemblySourceRest_of_trueLeftBoundary
    (h :
      MixedParserStackTrueLeftBoundaryFinisherOutputConstructionForAssemblySourceRest) :
    MixedParserStackFinisherOutputConstructionForAssemblySourceRest := by
  rcases h with ⟨finish, hfinish⟩
  refine
    ⟨SeqViaCanonical
      mixedParserStackSeekLeftBoundaryDescription finish, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        mixedParserStackSeekLeftBoundaryDescription_subroutineReady
        hfinish.subroutineReady
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape_eq
        mixedParserStackSeekLeftBoundaryDescription_subroutineReady
        hfinish.subroutineReady
        (mixedParserStackSeekLeftBoundaryDescription_haltsFrom_sourceTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (MixedParserStackRewriterTrueLeftBoundaryTape_move_left_move_right
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (hfinish.haltsFromTapeWithOutput w sourceRestBits stage)

theorem assemblySourceRestFinishLeftBoundaryOutputSpec_of_mixedParserStackFinisher
    {finish : MachineDescription}
    (hfinish :
      MixedParserStackFinisherAssemblySourceRestOutputSpec finish) :
    AssemblySourceRestFinishLeftBoundaryOutputSpec finish := by
  constructor
  · exact hfinish.subroutineReady
  · intro w sourceRestBits stage
    simpa [MixedParserStackRewriterSourceTape_eq_leftBoundary] using
      hfinish.haltsFromTapeWithOutput w sourceRestBits stage

theorem assemblySourceRestFinishLeftBoundaryOutputConstruction_of_mixedParserStackFinisher
    (h :
      MixedParserStackFinisherOutputConstructionForAssemblySourceRest) :
    AssemblySourceRestFinishLeftBoundaryOutputConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨finish,
      assemblySourceRestFinishLeftBoundaryOutputSpec_of_mixedParserStackFinisher
        hfinish⟩

theorem assemblySourceRestFinishLeftBoundaryCoreOutputConstruction_of_mixedParserStackFinisher
    (h :
      MixedParserStackFinisherOutputConstructionForAssemblySourceRest) :
    AssemblySourceRestFinishLeftBoundaryCoreOutputConstruction :=
  assemblySourceRestFinishLeftBoundaryOutputConstruction_of_mixedParserStackFinisher
    h

theorem assemblySourceRestFinishLeftBoundaryTape_move_left_move_right_output
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (assemblySourceRestFinishLeftBoundaryTape
            w sourceRestBits stage)) =
      assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage := by
  rw [assemblySourceRestFinishLeftBoundaryTape]
  exact
    scanLeftToBlankLeftHaltTape_move_left_move_right_none_right
      (List.append (sourceRestBits.reverse.map some)
        (assemblySourceRestBoundaryLeftRev w stage))
      (preservingCellPassCellBits sourceRestBits)
      []

def assemblySourceRestFinishOutputFromLeftBoundary
    (finish : MachineDescription) : MachineDescription :=
  SeqViaCanonical scanLeftToBlankLeftDescription finish

theorem assemblySourceRestFinishQuoteBoundaryOutputSpec_of_leftBoundary
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishLeftBoundaryOutputSpec finish) :
    AssemblySourceRestFinishQuoteBoundaryOutputSpec
      (assemblySourceRestFinishOutputFromLeftBoundary finish) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        scanLeftToBlankLeftDescription_subroutineReady
        hfinish.subroutineReady
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape_eq
        scanLeftToBlankLeftDescription_subroutineReady
        hfinish.subroutineReady
        (scanLeftToBlankLeftDescription_haltsFrom_finishQuoteBoundaryTape
          w sourceRestBits stage)
        (assemblySourceRestFinishLeftBoundaryTape_move_left_move_right_output
          w sourceRestBits stage)
        (hfinish.haltsFromTapeWithOutput w sourceRestBits stage)

theorem assemblySourceRestFinishQuoteBoundaryOutputConstruction_of_leftBoundary
    (h : AssemblySourceRestFinishLeftBoundaryOutputConstruction) :
    AssemblySourceRestFinishQuoteBoundaryOutputConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨assemblySourceRestFinishOutputFromLeftBoundary finish,
      assemblySourceRestFinishQuoteBoundaryOutputSpec_of_leftBoundary
        hfinish⟩

def assemblySourceRestFinishOutputFromQuoteBoundary
    (finish : MachineDescription) : MachineDescription :=
  SeqViaCanonical scanRightToBlankLeftDescription finish

theorem assemblySourceRestFinishOutputSpec_of_quoteBoundary
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishQuoteBoundaryOutputSpec finish) :
    AssemblySourceRestFinishOutputSpec
      (assemblySourceRestFinishOutputFromQuoteBoundary finish) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        scanRightToBlankLeftDescription_subroutineReady
        hfinish.subroutineReady
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape_eq
        scanRightToBlankLeftDescription_subroutineReady
        hfinish.subroutineReady
        (scanRightToBlankLeftDescription_haltsFrom_finishSourceTape
          w sourceRestBits stage)
        (assemblySourceRestFinishQuoteBoundaryTape_move_left_move_right
          w sourceRestBits stage)
        (hfinish.haltsFromTapeWithOutput w sourceRestBits stage)

theorem assemblySourceRestFinishOutputConstruction_of_quoteBoundary
    (h : AssemblySourceRestFinishQuoteBoundaryOutputConstruction) :
    AssemblySourceRestFinishOutputConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨assemblySourceRestFinishOutputFromQuoteBoundary finish,
      assemblySourceRestFinishOutputSpec_of_quoteBoundary hfinish⟩

def assemblySourceRestFinishOutputFromBoundary
    (finish : MachineDescription) : MachineDescription :=
  SeqViaCanonical assemblySourceRestFinishLeftMoveDescription finish

theorem assemblySourceRestFinishOutputSpec_of_boundary
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishBoundaryOutputSpec finish) :
    AssemblySourceRestFinishOutputSpec
      (assemblySourceRestFinishOutputFromBoundary finish) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        assemblySourceRestFinishLeftMoveDescription_subroutineReady
        hfinish.subroutineReady
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTapeWithOutput_of_haltsFromTape_eq
        assemblySourceRestFinishLeftMoveDescription_subroutineReady
        hfinish.subroutineReady
        (assemblySourceRestFinishLeftMoveDescription_haltsFrom_sourceTape
          w sourceRestBits stage)
        (assemblySourceRestFinishBoundaryTape_move_left_move_right
          w sourceRestBits stage)
        (hfinish.haltsFromTapeWithOutput w sourceRestBits stage)

theorem assemblySourceRestFinishOutputConstruction_of_boundary
    (h : AssemblySourceRestFinishBoundaryOutputConstruction) :
    AssemblySourceRestFinishOutputConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨assemblySourceRestFinishOutputFromBoundary finish,
      assemblySourceRestFinishOutputSpec_of_boundary hfinish⟩

def assemblySourceRestFinishEquivFromInnerLiveTail
    (inner : MachineDescription) : MachineDescription :=
  assemblySourceRestFinishOutputFromQuoteBoundary
    (assemblySourceRestFinishOutputFromLeftBoundary
      (SeqViaCanonical mixedParserStackSeekLeftBoundaryDescription
        (SeqViaCanonical
          mixedParserStackDefaultInternalMarkerDescription inner)))

theorem assemblySourceRestFinishEquivConstruction_of_innerLiveTail
    (hinner : MixedParserStackSourceRestFinishAssemblyEquivConstruction) :
    AssemblySourceRestFinishEquivConstruction := by
  rcases hinner with ⟨inner, hinner⟩
  refine ⟨assemblySourceRestFinishEquivFromInnerLiveTail inner, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        scanRightToBlankLeftDescription_subroutineReady
        (SeqViaCanonical_subroutineReady
          scanLeftToBlankLeftDescription_subroutineReady
          (SeqViaCanonical_subroutineReady
            mixedParserStackSeekLeftBoundaryDescription_subroutineReady
            (SeqViaCanonical_subroutineReady
              mixedParserStackDefaultInternalMarkerDescription_subroutineReady
              hinner.left)))
  · intro w sourceRestBits stage
    have hdefault :
        (SeqViaCanonical
          mixedParserStackDefaultInternalMarkerDescription inner).HaltsFromTapeEquiv
          (MixedParserStackRewriterTrueLeftBoundaryTape
            w sourceRestBits
            (preservingCellPassCellBits sourceRestBits)
            stage)
          (assemblySourceRestFinishTargetTape
            w sourceRestBits stage) := by
      exact
        SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
          mixedParserStackDefaultInternalMarkerDescription_subroutineReady
          hinner.left
          (mixedParserStackDefaultInternalMarkerDescription_haltsFrom_trueLeftBoundaryTape
            w sourceRestBits
            (preservingCellPassCellBits sourceRestBits)
            stage).toEquiv
          (by
            rw [MixedParserStackRewriterDefaultedInternalMarkerTape_move_left_move_right]
            exact Tape.Equiv.refl _)
          (hinner.right w sourceRestBits stage)
    have hseek :
        (SeqViaCanonical mixedParserStackSeekLeftBoundaryDescription
          (SeqViaCanonical
            mixedParserStackDefaultInternalMarkerDescription inner)).HaltsFromTapeEquiv
          (MixedParserStackRewriterSourceTape
            (assemblySourceRestFinishParserPrefixCells w)
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage)
            sourceRestBits
            (preservingCellPassCellBits sourceRestBits))
          (assemblySourceRestFinishTargetTape
            w sourceRestBits stage) := by
      exact
        SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
          mixedParserStackSeekLeftBoundaryDescription_subroutineReady
          (SeqViaCanonical_subroutineReady
            mixedParserStackDefaultInternalMarkerDescription_subroutineReady
            hinner.left)
          (mixedParserStackSeekLeftBoundaryDescription_haltsFrom_sourceTape
            w sourceRestBits
            (preservingCellPassCellBits sourceRestBits)
            stage).toEquiv
          (by
            rw [MixedParserStackRewriterTrueLeftBoundaryTape_move_left_move_right]
            exact Tape.Equiv.refl _)
          hdefault
    have hleftBoundary :
        (SeqViaCanonical mixedParserStackSeekLeftBoundaryDescription
          (SeqViaCanonical
            mixedParserStackDefaultInternalMarkerDescription inner)).HaltsFromTapeEquiv
          (assemblySourceRestFinishLeftBoundaryTape
            w sourceRestBits stage)
          (assemblySourceRestFinishTargetTape
            w sourceRestBits stage) := by
      simpa [MixedParserStackRewriterSourceTape_eq_leftBoundary] using hseek
    have hquoteBoundary :
        (assemblySourceRestFinishOutputFromLeftBoundary
          (SeqViaCanonical mixedParserStackSeekLeftBoundaryDescription
            (SeqViaCanonical
              mixedParserStackDefaultInternalMarkerDescription inner))).HaltsFromTapeEquiv
          (assemblySourceRestFinishQuoteBoundaryTape
            w sourceRestBits stage)
          (assemblySourceRestFinishTargetTape
            w sourceRestBits stage) := by
      exact
        SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
          scanLeftToBlankLeftDescription_subroutineReady
          (SeqViaCanonical_subroutineReady
            mixedParserStackSeekLeftBoundaryDescription_subroutineReady
            (SeqViaCanonical_subroutineReady
              mixedParserStackDefaultInternalMarkerDescription_subroutineReady
              hinner.left))
          (scanLeftToBlankLeftDescription_haltsFrom_finishQuoteBoundaryTape
            w sourceRestBits stage).toEquiv
          (by
            rw [assemblySourceRestFinishLeftBoundaryTape_move_left_move_right_output]
            exact Tape.Equiv.refl _)
          hleftBoundary
    exact
      SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
        scanRightToBlankLeftDescription_subroutineReady
        (SeqViaCanonical_subroutineReady
          scanLeftToBlankLeftDescription_subroutineReady
          (SeqViaCanonical_subroutineReady
            mixedParserStackSeekLeftBoundaryDescription_subroutineReady
            (SeqViaCanonical_subroutineReady
              mixedParserStackDefaultInternalMarkerDescription_subroutineReady
              hinner.left)))
        (scanRightToBlankLeftDescription_haltsFrom_finishSourceTape
          w sourceRestBits stage).toEquiv
        (by
          rw [assemblySourceRestFinishQuoteBoundaryTape_move_left_move_right]
          exact Tape.Equiv.refl _)
        hquoteBoundary

/-! ## Public construction route -/

theorem assemblySourceRestFinishEquivConstruction_for_assemblySourceRest :
    AssemblySourceRestFinishEquivConstruction :=
  assemblySourceRestFinishEquivConstruction_of_innerLiveTail
    directJoinedSourceRestFinishAssemblyEquivConstruction

theorem mixedParserStackDefaultedInternalMarkerFinisherOutputConstruction_for_assemblySourceRest :
    MixedParserStackDefaultedInternalMarkerFinisherOutputConstructionForAssemblySourceRest :=
  MixedParserStackSourceRestFinishAssemblyOutputConstruction.toDefaultedInternalMarkerConstruction
    directJoinedSourceRestFinishAssemblyOutputConstruction

theorem mixedParserStackTrueLeftBoundaryFinisherOutputConstruction_for_assemblySourceRest :
    MixedParserStackTrueLeftBoundaryFinisherOutputConstructionForAssemblySourceRest :=
  MixedParserStackTrueLeftBoundaryFinisherOutputConstructionForAssemblySourceRest_of_defaultedInternalMarker
    mixedParserStackDefaultedInternalMarkerFinisherOutputConstruction_for_assemblySourceRest

theorem mixedParserStackFinisherOutputConstruction_for_assemblySourceRest :
    MixedParserStackFinisherOutputConstructionForAssemblySourceRest :=
  MixedParserStackFinisherOutputConstructionForAssemblySourceRest_of_trueLeftBoundary
    mixedParserStackTrueLeftBoundaryFinisherOutputConstruction_for_assemblySourceRest

theorem assemblySourceRestFinishLeftBoundaryOutputConstruction_for_assemblySourceRest :
    AssemblySourceRestFinishLeftBoundaryOutputConstruction :=
  assemblySourceRestFinishLeftBoundaryOutputConstruction_of_mixedParserStackFinisher
    mixedParserStackFinisherOutputConstruction_for_assemblySourceRest

theorem assemblySourceRestFinishQuoteBoundaryOutputConstruction_for_assemblySourceRest :
    AssemblySourceRestFinishQuoteBoundaryOutputConstruction :=
  assemblySourceRestFinishQuoteBoundaryOutputConstruction_of_leftBoundary
    assemblySourceRestFinishLeftBoundaryOutputConstruction_for_assemblySourceRest

theorem assemblySourceRestFinishOutputConstruction_for_assemblySourceRest :
    AssemblySourceRestFinishOutputConstruction :=
  assemblySourceRestFinishEquivConstruction_for_assemblySourceRest.toOutputConstruction

theorem assemblySourceRestFinishOutputConstruction_of_innerLiveTail
    (hinner : MixedParserStackSourceRestFinishAssemblyOutputConstruction) :
    AssemblySourceRestFinishOutputConstruction := by
  exact
    assemblySourceRestFinishOutputConstruction_of_quoteBoundary
      (assemblySourceRestFinishQuoteBoundaryOutputConstruction_of_leftBoundary
        (assemblySourceRestFinishLeftBoundaryOutputConstruction_of_mixedParserStackFinisher
          (MixedParserStackFinisherOutputConstructionForAssemblySourceRest_of_trueLeftBoundary
            (MixedParserStackTrueLeftBoundaryFinisherOutputConstructionForAssemblySourceRest_of_defaultedInternalMarker
              (MixedParserStackSourceRestFinishAssemblyOutputConstruction.toDefaultedInternalMarkerConstruction
                hinner)))))

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
