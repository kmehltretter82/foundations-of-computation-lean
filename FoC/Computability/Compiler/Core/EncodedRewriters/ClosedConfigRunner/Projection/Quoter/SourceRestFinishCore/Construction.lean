import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.Construction.BoundaryCore

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer
open DovetailInitialLayoutInitializer.StageInputMarkedScanner
/-!
**Construction contracts.**  The public finish specification starts at
{name}`assemblySourceRestFinishSourceTape`.  The intermediate contracts expose
the exact scanner handoff points: the post-boundary tape, the quote-boundary
tape, and the left-boundary tape used by the still-local core copier.
-/

def AssemblySourceRestFinishSpec (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (assemblySourceRestFinishSourceTape w sourceRestBits stage)
        (assemblySourceRestFinishTargetTape w sourceRestBits stage)

def AssemblySourceRestFinishConstruction : Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestFinishSpec finish

def AssemblySourceRestFinishBoundarySpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (assemblySourceRestFinishBoundaryTape w sourceRestBits stage)
        (assemblySourceRestFinishTargetTape w sourceRestBits stage)

def AssemblySourceRestFinishBoundaryConstruction : Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestFinishBoundarySpec finish

/-!
**Mixed parser-stack finisher target.**  The low-level boundary mechanics are
provided by
{module}`FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.Construction.BoundaryCore`.
The remaining concrete leaf should prove the mixed parser-stack finisher
construction below; the adapter then turns it into the public left-boundary
core without inspecting the transition table.
-/

def MixedParserStackFinisherAssemblySourceRestSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (MixedParserStackRewriterSourceTape
          (assemblySourceRestFinishParserPrefixCells w)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits
          (preservingCellPassCellBits sourceRestBits))
        (MixedParserStackRewriterTargetTape
          (MixedParserStackRewriterPrefixQuote
            (assemblySourceRestFinishParserPrefixCells w)
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage))
          (MixedParserStackRewriterLengthHeader
            (assemblySourceRestFinishParserPrefixCells w)
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage)
            sourceRestBits)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits
          (preservingCellPassCellBits sourceRestBits))

def MixedParserStackFinisherConstructionForAssemblySourceRest : Prop :=
  exists finish : MachineDescription,
    MixedParserStackFinisherAssemblySourceRestSpec finish

theorem
    assemblySourceRestFinishLeftBoundaryCoreConstruction_of_mixedParserStackFinisher
    (h : MixedParserStackFinisherConstructionForAssemblySourceRest) :
    AssemblySourceRestFinishLeftBoundaryCoreConstruction := by
  rcases h with ⟨finish, hfinish⟩
  refine ⟨finish, hfinish.left, ?_⟩
  intro w sourceRestBits stage
  simpa
    [MixedParserStackRewriterSourceTape_eq_leftBoundary,
      MixedParserStackRewriterTargetTape_eq_targetTape_computed]
    using hfinish.right w sourceRestBits stage

def MixedParserStackTrueLeftBoundaryFinisherAssemblySourceRestSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (MixedParserStackRewriterTrueLeftBoundaryTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (MixedParserStackRewriterTargetTape
          (MixedParserStackRewriterPrefixQuote
            (assemblySourceRestFinishParserPrefixCells w)
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage))
          (MixedParserStackRewriterLengthHeader
            (assemblySourceRestFinishParserPrefixCells w)
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage)
            sourceRestBits)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits
          (preservingCellPassCellBits sourceRestBits))

def MixedParserStackTrueLeftBoundaryFinisherConstructionForAssemblySourceRest :
    Prop :=
  exists finish : MachineDescription,
    MixedParserStackTrueLeftBoundaryFinisherAssemblySourceRestSpec finish

def MixedParserStackDefaultedInternalMarkerFinisherAssemblySourceRestSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (MixedParserStackRewriterDefaultedInternalMarkerTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (MixedParserStackRewriterTargetTape
          (MixedParserStackRewriterPrefixQuote
            (assemblySourceRestFinishParserPrefixCells w)
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage))
          (MixedParserStackRewriterLengthHeader
            (assemblySourceRestFinishParserPrefixCells w)
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage)
            sourceRestBits)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits
          (preservingCellPassCellBits sourceRestBits))

def
    MixedParserStackDefaultedInternalMarkerFinisherConstructionForAssemblySourceRest :
    Prop :=
  exists finish : MachineDescription,
    MixedParserStackDefaultedInternalMarkerFinisherAssemblySourceRestSpec finish

def MixedParserStackWholeSourceFinisherAssemblySourceRestSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (MixedParserStackRewriterDefaultedInternalMarkerTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (MixedParserStackRewriterWholeSourceTargetTape
          (MixedParserStackRewriterTrueSourceCells
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage))

def MixedParserStackWholeSourceFinisherConstructionForAssemblySourceRest :
    Prop :=
  exists finish : MachineDescription,
    MixedParserStackWholeSourceFinisherAssemblySourceRestSpec finish

def MixedParserStackRightBoundaryFinisherAssemblySourceRestSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (MixedParserStackRewriterDefaultedRightBoundaryTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (MixedParserStackRewriterWholeSourceTargetTape
          (MixedParserStackRewriterTrueSourceCells
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage))

def MixedParserStackRightBoundaryFinisherConstructionForAssemblySourceRest :
    Prop :=
  exists finish : MachineDescription,
    MixedParserStackRightBoundaryFinisherAssemblySourceRestSpec finish

def MixedParserStackSourceStartFinisherAssemblySourceRestSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (MixedParserStackRewriterDefaultedSourceStartTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (MixedParserStackRewriterWholeSourceTargetTape
          (MixedParserStackRewriterTrueSourceCells
            w sourceRestBits stage)
          (assemblySourceRestFinishRawTailBits sourceRestBits stage))

def MixedParserStackSourceStartFinisherConstructionForAssemblySourceRest :
    Prop :=
  exists finish : MachineDescription,
    MixedParserStackSourceStartFinisherAssemblySourceRestSpec finish

def AssemblySourceRestReusableQuoteSourceStartFinisherSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (MixedParserStackRewriterDefaultedSourceStartTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (assemblySourceRestFinishRawBoolReusableQuoteTargetTape
          w sourceRestBits stage)

def AssemblySourceRestReusableQuoteSourceStartFinisherConstruction :
    Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestReusableQuoteSourceStartFinisherSpec finish

def AssemblySourceRestReusableQuoteSourceRestBoundaryFinisherSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (MixedParserStackRewriterDefaultedSourceRestBoundaryTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (assemblySourceRestFinishRawBoolReusableQuoteTargetTape
          w sourceRestBits stage)

def AssemblySourceRestReusableQuoteSourceRestBoundaryFinisherConstruction :
    Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestReusableQuoteSourceRestBoundaryFinisherSpec finish

theorem
    MixedParserStackRewriterDefaultedSourceRestBoundaryTape_move_left_move_right
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (MixedParserStackRewriterDefaultedSourceRestBoundaryTape
            w sourceRestBits quoteRestBits stage)) =
      MixedParserStackRewriterDefaultedSourceRestBoundaryTape
        w sourceRestBits quoteRestBits stage := by
  rw [MixedParserStackRewriterDefaultedSourceRestBoundaryTape]
  cases sourceRestBits with
  | nil =>
      cases quoteRestBits <;>
        simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons head tail =>
      cases tail <;>
        simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem
    AssemblySourceRestReusableQuoteSourceStartFinisherConstruction_of_sourceRestBoundary
    (h :
      AssemblySourceRestReusableQuoteSourceRestBoundaryFinisherConstruction) :
    AssemblySourceRestReusableQuoteSourceStartFinisherConstruction := by
  rcases h with ⟨finish, hfinish⟩
  refine ⟨SeqViaCanonical AssemblyPrefixDescription finish, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        assemblyPrefixDescription_subroutineReady
        hfinish.left
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        assemblyPrefixDescription_subroutineReady
        hfinish.left
        (assemblyPrefixDescription_haltsFrom_defaultedSourceStart_to_sourceRestBoundary
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (MixedParserStackRewriterDefaultedSourceRestBoundaryTape_move_left_move_right
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (hfinish.right w sourceRestBits stage)

def AssemblySourceRestRawBoolSourceStartFinisherSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (MixedParserStackRewriterDefaultedSourceStartTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (assemblySourceRestFinishRawBoolSourceStartTargetTape
          w sourceRestBits stage)

def AssemblySourceRestRawBoolSourceStartFinisherConstruction :
    Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestRawBoolSourceStartFinisherSpec finish

theorem AssemblySourceRestRawBoolSourceStartFinisherConstruction_of_reusableQuote
    (h : AssemblySourceRestReusableQuoteSourceStartFinisherConstruction) :
    AssemblySourceRestRawBoolSourceStartFinisherConstruction := by
  rcases h with ⟨finish, hfinish⟩
  refine ⟨finish, hfinish.left, ?_⟩
  intro w sourceRestBits stage
  rw [assemblySourceRestFinishRawBoolSourceStartTargetTape_eq_reusableQuote]
  exact hfinish.right w sourceRestBits stage

theorem MixedParserStackSourceStartFinisherConstructionForAssemblySourceRest_of_rawBool
    (h : AssemblySourceRestRawBoolSourceStartFinisherConstruction) :
    MixedParserStackSourceStartFinisherConstructionForAssemblySourceRest := by
  rcases h with ⟨finish, hfinish⟩
  refine ⟨finish, hfinish.left, ?_⟩
  intro w sourceRestBits stage
  rw [MixedParserStackRewriterWholeSourceTargetTape_eq_rawBoolTargetTape]
  exact hfinish.right w sourceRestBits stage

theorem
    MixedParserStackRightBoundaryFinisherConstructionForAssemblySourceRest_of_sourceStart
    (h :
      MixedParserStackSourceStartFinisherConstructionForAssemblySourceRest) :
    MixedParserStackRightBoundaryFinisherConstructionForAssemblySourceRest := by
  rcases h with ⟨finish, hfinish⟩
  refine
    ⟨SeqViaCanonical
      CommonGround.FiniteTransducers.rightEdgeRewindDescription
      finish, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        CommonGround.FiniteTransducers.rightEdgeRewindDescription_subroutineReady
        hfinish.left
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        CommonGround.FiniteTransducers.rightEdgeRewindDescription_subroutineReady
        hfinish.left
        (rightEdgeRewindDescription_haltsFrom_defaultedRightBoundaryTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (MixedParserStackRewriterDefaultedSourceStartTape_move_left_move_right
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (hfinish.right w sourceRestBits stage)

theorem
    MixedParserStackWholeSourceFinisherConstructionForAssemblySourceRest_of_rightBoundary
    (h :
      MixedParserStackRightBoundaryFinisherConstructionForAssemblySourceRest) :
    MixedParserStackWholeSourceFinisherConstructionForAssemblySourceRest := by
  rcases h with ⟨finish, hfinish⟩
  refine
    ⟨SeqViaCanonical
      mixedParserStackScanRightToStructuralBlankDescription finish, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        mixedParserStackScanRightToStructuralBlankDescription_subroutineReady
        hfinish.left
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        mixedParserStackScanRightToStructuralBlankDescription_subroutineReady
        hfinish.left
        (mixedParserStackScanRightToStructuralBlankDescription_haltsFrom_defaultedInternalMarkerTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (MixedParserStackRewriterDefaultedRightBoundaryTape_move_left_move_right
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (hfinish.right w sourceRestBits stage)

theorem
    MixedParserStackDefaultedInternalMarkerFinisherConstructionForAssemblySourceRest_of_wholeSource
    (h :
      MixedParserStackWholeSourceFinisherConstructionForAssemblySourceRest) :
    MixedParserStackDefaultedInternalMarkerFinisherConstructionForAssemblySourceRest := by
  rcases h with ⟨finish, hfinish⟩
  refine ⟨finish, hfinish.left, ?_⟩
  intro w sourceRestBits stage
  simpa [MixedParserStackRewriterTargetTape_eq_wholeSourceTargetTape]
    using hfinish.right w sourceRestBits stage

theorem
    MixedParserStackTrueLeftBoundaryFinisherConstructionForAssemblySourceRest_of_defaultedInternalMarker
    (h :
      MixedParserStackDefaultedInternalMarkerFinisherConstructionForAssemblySourceRest) :
    MixedParserStackTrueLeftBoundaryFinisherConstructionForAssemblySourceRest := by
  rcases h with ⟨finish, hfinish⟩
  refine
    ⟨SeqViaCanonical
      mixedParserStackDefaultInternalMarkerDescription finish, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        mixedParserStackDefaultInternalMarkerDescription_subroutineReady
        hfinish.left
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        mixedParserStackDefaultInternalMarkerDescription_subroutineReady
        hfinish.left
        (mixedParserStackDefaultInternalMarkerDescription_haltsFrom_trueLeftBoundaryTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (MixedParserStackRewriterDefaultedInternalMarkerTape_move_left_move_right
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (hfinish.right w sourceRestBits stage)

theorem MixedParserStackRewriterTrueLeftBoundaryTape_move_left_move_right
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (MixedParserStackRewriterTrueLeftBoundaryTape
            w sourceRestBits quoteRestBits stage)) =
      MixedParserStackRewriterTrueLeftBoundaryTape
        w sourceRestBits quoteRestBits stage := by
  exact
    Tape.move_left_move_right_eq_self_of_right_cons
      (MixedParserStackRewriterTrueLeftBoundaryTape
        w sourceRestBits quoteRestBits stage)
      (cell := some false)
      (right :=
        some false ::
          some false ::
            some true ::
              some false ::
                none ::
                  List.append
                    ((assemblySourceRestFinishRightPayloadBits
                      w sourceRestBits stage).map some)
                    (none ::
                      List.append (quoteRestBits.map some) [none]))
      (by
        simp [MixedParserStackRewriterTrueLeftBoundaryTape,
          assemblySourceRestFinishParserMarkerLeftCells,
          transitionPrefixLeftTail, tapeAtCells])

theorem
    MixedParserStackFinisherConstructionForAssemblySourceRest_of_trueLeftBoundary
    (h :
      MixedParserStackTrueLeftBoundaryFinisherConstructionForAssemblySourceRest) :
    MixedParserStackFinisherConstructionForAssemblySourceRest := by
  rcases h with ⟨finish, hfinish⟩
  refine
    ⟨SeqViaCanonical
      mixedParserStackSeekLeftBoundaryDescription finish, ?_⟩
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        mixedParserStackSeekLeftBoundaryDescription_subroutineReady
        hfinish.left
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        mixedParserStackSeekLeftBoundaryDescription_subroutineReady
        hfinish.left
        (mixedParserStackSeekLeftBoundaryDescription_haltsFrom_sourceTape
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (MixedParserStackRewriterTrueLeftBoundaryTape_move_left_move_right
          w sourceRestBits
          (preservingCellPassCellBits sourceRestBits)
          stage)
        (hfinish.right w sourceRestBits stage)

def assemblySourceRestFinishLengthHeaderTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells
    ((assemblySourceRestFinishLengthHeaderBits
      w sourceRestBits stage).reverse.map some)
    ((List.append
      (assemblySourceRestFinishQuotedPrefixBits w stage)
      (List.append
        (preservingCellPassCellBits sourceRestBits)
        (assemblySourceRestFinishRawTailBits
          sourceRestBits stage))).map some)

def assemblySourceRestFinishPrefixQuotedTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells
    ((assemblySourceRestFinishPrefixQuoteOutputBits
      w sourceRestBits stage).reverse.map some)
    ((List.append
      (preservingCellPassCellBits sourceRestBits)
      (assemblySourceRestFinishRawTailBits
        sourceRestBits stage)).map some)

def assemblySourceRestFinishQuoteRestJoinedTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells
    ((List.append
      (assemblySourceRestFinishPrefixQuoteOutputBits
        w sourceRestBits stage)
      (preservingCellPassCellBits sourceRestBits)).reverse.map some)
    ((assemblySourceRestFinishRawTailBits
      sourceRestBits stage).map some)

def assemblySourceRestFinishTailCopiedTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  assemblySourceRestFinishQuoteRestJoinedTape w sourceRestBits stage

theorem assemblySourceRestFinishQuoteRestJoinedTape_eq_targetTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishQuoteRestJoinedTape w sourceRestBits stage =
      assemblySourceRestFinishTargetTape w sourceRestBits stage := by
  rw [assemblySourceRestFinishQuoteRestJoinedTape,
    assemblySourceRestFinishTargetTape_eq_tapeAtCells_segments]

theorem assemblySourceRestFinishTailCopiedTape_eq_targetTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTailCopiedTape w sourceRestBits stage =
      assemblySourceRestFinishTargetTape w sourceRestBits stage := by
  rw [assemblySourceRestFinishTailCopiedTape,
    assemblySourceRestFinishQuoteRestJoinedTape_eq_targetTape]

/-!
**Phase composition.**  The remaining lemmas compose the small scanners around
the left-boundary core.  The only finite-machine leaf still hidden behind the
core construction is the copier that consumes the mixed parser-stack layout and
emits the normalized target tape.
-/

theorem preservingCellPassHaltTape_eq_assemblySourceRestFinishSourceTape
    (w : Word Bool) (b : Bool) (rest : Word Bool) (stage : Nat) :
    preservingCellPassHaltTape
        (assemblySourceRestBoundaryLeftRev w stage) (b :: rest) [] =
      assemblySourceRestFinishSourceTape w (b :: rest) stage := by
  simpa [assemblySourceRestFinishSourceTape] using
    preservingCellPassHaltTape_nonempty_empty_output_eq_tapeAtCells
      (assemblySourceRestBoundaryLeftRev w stage) b rest

theorem preservingCellPassDescription_haltsFrom_finishPostBoundaryTape
    (w : Word Bool) (b : Bool) (rest : Word Bool) (stage : Nat) :
    PreservingCellPassDescription.HaltsFromTape
      (assemblySourceRestFinishPostBoundaryTape w (b :: rest) stage)
      (assemblySourceRestFinishSourceTape w (b :: rest) stage) := by
  rw [assemblySourceRestFinishPostBoundaryTape]
  rw [← preservingCellPassHaltTape_eq_assemblySourceRestFinishSourceTape]
  simpa [List.map_cons] using
    preservingCellPassDescription_haltsFrom_nonempty_cells_oneBlank
      (assemblySourceRestBoundaryLeftRev w stage) b rest

theorem scanLeftToBlankLeftDescription_haltsFrom_empty_scanRightToBlankLeftHaltTape
    (leftBase : List (Option Bool)) :
    scanLeftToBlankLeftDescription.HaltsFromTape
      (scanRightToBlankLeftHaltTape (none :: leftBase) [])
      (scanLeftToBlankLeftHaltTape leftBase [] [none]) := by
  refine ⟨1, ?_⟩
  constructor <;>
    simp [scanRightToBlankLeftHaltTape,
      scanLeftToBlankLeftHaltTape, scanLeftToBlankLeftDescription,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, tapeAtCells]

theorem scanLeftToBlankLeftDescription_haltsFrom_finishQuoteBoundaryTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    scanLeftToBlankLeftDescription.HaltsFromTape
      (assemblySourceRestFinishQuoteBoundaryTape w sourceRestBits stage)
      (assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage) := by
  cases hquote : preservingCellPassCellBits sourceRestBits with
  | nil =>
      rw [assemblySourceRestFinishQuoteBoundaryTape,
        assemblySourceRestFinishLeftBoundaryTape, hquote]
      exact
        scanLeftToBlankLeftDescription_haltsFrom_empty_scanRightToBlankLeftHaltTape
          (List.append (sourceRestBits.reverse.map some)
            (assemblySourceRestBoundaryLeftRev w stage))
  | cons quoteHead quoteTail =>
      rcases exists_reverse_append_singleton_of_cons quoteHead quoteTail with
        ⟨scanRev, current, hscan⟩
      rw [assemblySourceRestFinishQuoteBoundaryTape,
        assemblySourceRestFinishLeftBoundaryTape, hquote, hscan]
      exact
        scanLeftToBlankLeftDescription_haltsFrom_scanRightToBlankLeftHaltTape
          (List.append (sourceRestBits.reverse.map some)
            (assemblySourceRestBoundaryLeftRev w stage))
          scanRev current

theorem assemblySourceRestFinishLeftBoundaryTape_move_left_move_right
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

def assemblySourceRestFinishFromLeftBoundary
    (finish : MachineDescription) : MachineDescription :=
  SeqViaCanonical scanLeftToBlankLeftDescription finish

theorem assemblySourceRestFinishQuoteBoundarySpec_of_leftBoundary
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishLeftBoundarySpec finish) :
    AssemblySourceRestFinishQuoteBoundarySpec
      (assemblySourceRestFinishFromLeftBoundary finish) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        scanLeftToBlankLeftDescription_subroutineReady
        hfinish.left
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        scanLeftToBlankLeftDescription_subroutineReady
        hfinish.left
        (scanLeftToBlankLeftDescription_haltsFrom_finishQuoteBoundaryTape
          w sourceRestBits stage)
        (assemblySourceRestFinishLeftBoundaryTape_move_left_move_right
          w sourceRestBits stage)
        (hfinish.right w sourceRestBits stage)

theorem assemblySourceRestFinishQuoteBoundaryConstruction_of_leftBoundary
    (h : AssemblySourceRestFinishLeftBoundaryConstruction) :
    AssemblySourceRestFinishQuoteBoundaryConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨assemblySourceRestFinishFromLeftBoundary finish,
      assemblySourceRestFinishQuoteBoundarySpec_of_leftBoundary hfinish⟩

def assemblySourceRestFinishFromQuoteBoundary
    (finish : MachineDescription) : MachineDescription :=
  SeqViaCanonical scanRightToBlankLeftDescription finish

theorem assemblySourceRestFinishSpec_of_quoteBoundary
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishQuoteBoundarySpec finish) :
    AssemblySourceRestFinishSpec
      (assemblySourceRestFinishFromQuoteBoundary finish) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        scanRightToBlankLeftDescription_subroutineReady
        hfinish.left
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        scanRightToBlankLeftDescription_subroutineReady
        hfinish.left
        (scanRightToBlankLeftDescription_haltsFrom_finishSourceTape
          w sourceRestBits stage)
        (assemblySourceRestFinishQuoteBoundaryTape_move_left_move_right
          w sourceRestBits stage)
        (hfinish.right w sourceRestBits stage)

theorem assemblySourceRestFinishConstruction_of_quoteBoundary
    (h : AssemblySourceRestFinishQuoteBoundaryConstruction) :
    AssemblySourceRestFinishConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨assemblySourceRestFinishFromQuoteBoundary finish,
      assemblySourceRestFinishSpec_of_quoteBoundary hfinish⟩

def assemblySourceRestFinishFromBoundary
    (finish : MachineDescription) : MachineDescription :=
  SeqViaCanonical assemblySourceRestFinishLeftMoveDescription finish

theorem assemblySourceRestFinishSpec_of_boundary
    {finish : MachineDescription}
    (hfinish : AssemblySourceRestFinishBoundarySpec finish) :
    AssemblySourceRestFinishSpec
      (assemblySourceRestFinishFromBoundary finish) := by
  constructor
  · exact
      SeqViaCanonical_subroutineReady
        assemblySourceRestFinishLeftMoveDescription_subroutineReady
        hfinish.left
  · intro w sourceRestBits stage
    exact
      SeqViaCanonical_haltsFromTape_of_haltsFromTape
        assemblySourceRestFinishLeftMoveDescription_subroutineReady
        hfinish.left
        (assemblySourceRestFinishLeftMoveDescription_haltsFrom_sourceTape
          w sourceRestBits stage)
        (assemblySourceRestFinishBoundaryTape_move_left_move_right
          w sourceRestBits stage)
        (hfinish.right w sourceRestBits stage)

theorem assemblySourceRestFinishConstruction_of_boundary
    (h : AssemblySourceRestFinishBoundaryConstruction) :
    AssemblySourceRestFinishConstruction := by
  rcases h with ⟨finish, hfinish⟩
  exact
    ⟨assemblySourceRestFinishFromBoundary finish,
      assemblySourceRestFinishSpec_of_boundary hfinish⟩


end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
