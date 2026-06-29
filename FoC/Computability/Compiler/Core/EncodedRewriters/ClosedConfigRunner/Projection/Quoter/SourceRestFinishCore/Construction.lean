import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.Views

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

def assemblySourceRestFinishLeftMoveDescription : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1 ]

theorem assemblySourceRestFinishLeftMoveDescription_wellFormed :
    assemblySourceRestFinishLeftMoveDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := assemblySourceRestFinishLeftMoveDescription.transitions)
      (stateCount := assemblySourceRestFinishLeftMoveDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := assemblySourceRestFinishLeftMoveDescription.transitions)
      (by decide)

theorem assemblySourceRestFinishLeftMoveDescription_haltTransitionFree :
    assemblySourceRestFinishLeftMoveDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := assemblySourceRestFinishLeftMoveDescription.transitions)
    (state := assemblySourceRestFinishLeftMoveDescription.halt)
    (by decide)

theorem assemblySourceRestFinishLeftMoveDescription_subroutineReady :
    assemblySourceRestFinishLeftMoveDescription.SubroutineReady :=
  ⟨assemblySourceRestFinishLeftMoveDescription_wellFormed,
    assemblySourceRestFinishLeftMoveDescription_haltTransitionFree⟩

theorem assemblySourceRestFinishLeftMoveDescription_haltsFromTape
    (T : Tape Bool) :
    assemblySourceRestFinishLeftMoveDescription.HaltsFromTape T
      (Tape.move Direction.left T) := by
  refine ⟨1, ?_⟩
  constructor <;>
    cases T with
    | mk left head right =>
        cases head with
        | none =>
            simp [assemblySourceRestFinishLeftMoveDescription,
              runConfig, stepConfig, lookupTransition, Matches,
              transition, Tape.read, Tape.write, Tape.move]
        | some b =>
            cases b <;>
              simp [assemblySourceRestFinishLeftMoveDescription,
                runConfig, stepConfig, lookupTransition, Matches,
                transition, Tape.read, Tape.write, Tape.move]

theorem tapeAtCells_move_left_cons_append_singleton
    (left cells : List (Option Bool)) :
    Tape.move Direction.left
        (tapeAtCells (none :: left) (List.append cells [none])) =
      tapeAtCells left (none :: List.append cells [none]) := by
  cases cells <;>
    simp [tapeAtCells, Tape.move, Tape.moveLeft]

theorem tapeAtCells_move_left_move_right_none_cons_append_singleton
    (left cells : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (tapeAtCells left (none :: List.append cells [none]))) =
      tapeAtCells left (none :: List.append cells [none]) := by
  cases cells <;>
    simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem tapeAtCells_move_left_none_cons_cells_of_left_ne_nil
    (left right : List (Option Bool)) (hleft : left ≠ []) :
    Tape.cells (Tape.move Direction.left (tapeAtCells left (none :: right))) =
      List.append left.reverse (none :: right) := by
  cases left with
  | nil =>
      contradiction
  | cons cell rest =>
      simp [tapeAtCells, Tape.cells, Tape.move, Tape.moveLeft]

theorem MixedParserStackRewriterSourceTape_cells_of_left_ne_nil
    (prefixCells : List (Option Bool))
    (stageBits sourceRestBits quoteRestBits : Word Bool)
    (hleft :
      List.append
        (sourceRestBits.reverse.map some)
        (List.append (stageBits.reverse.map some)
          prefixCells.reverse) ≠ []) :
    Tape.cells
        (MixedParserStackRewriterSourceTape
          prefixCells stageBits sourceRestBits quoteRestBits) =
      List.append prefixCells
        (List.append (stageBits.map some)
          (List.append (sourceRestBits.map some)
            (none ::
              List.append (quoteRestBits.map some) [none]))) := by
  rw [MixedParserStackRewriterSourceTape,
    scanLeftToBlankLeftHaltTape]
  rw [tapeAtCells_move_left_none_cons_cells_of_left_ne_nil _ _ hleft]
  simp [List.reverse_append, List.map_reverse, List.append_assoc]

theorem MixedParserStackRewriterSourceTape_cells_stageNat
    (prefixCells : List (Option Bool))
    (sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (MixedParserStackRewriterSourceTape prefixCells
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits quoteRestBits) =
      List.append prefixCells
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)
          (List.append (sourceRestBits.map some)
            (none ::
              List.append (quoteRestBits.map some) [none]))) := by
  rcases SelectedProjectionTailProjector.stageNatBits_cons_cons stage with
    ⟨head, next, right, hstage⟩
  exact
    MixedParserStackRewriterSourceTape_cells_of_left_ne_nil
      prefixCells
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        stage)
      sourceRestBits quoteRestBits
      (by
        cases sourceRestBits with
        | nil =>
            simp [hstage]
        | cons bit rest =>
            simp)

theorem MixedParserStackRewriterSourceTape_cells_marker_split_stageNat
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (MixedParserStackRewriterSourceTape
          (assemblySourceRestFinishParserPrefixCells w)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits quoteRestBits) =
      List.append assemblySourceRestFinishParserMarkerLeftCells
        (none ::
          List.append
            (assemblySourceRestFinishParserMarkerRightCells w)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some)
              (List.append (sourceRestBits.map some)
                (none ::
                  List.append (quoteRestBits.map some) [none])))) := by
  rw [MixedParserStackRewriterSourceTape_cells_stageNat]
  rw [assemblySourceRestFinishParserPrefixCells_eq_marker_split]
  simp [List.append_assoc]

theorem assemblySourceRestFinishSourceTape_move_left
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (assemblySourceRestFinishSourceTape w sourceRestBits stage) =
      assemblySourceRestFinishBoundaryTape w sourceRestBits stage := by
  rw [assemblySourceRestFinishSourceTape,
    assemblySourceRestFinishBoundaryTape]
  exact
    tapeAtCells_move_left_cons_append_singleton
      (List.append (sourceRestBits.reverse.map some)
        (assemblySourceRestBoundaryLeftRev w stage))
      ((preservingCellPassCellBits sourceRestBits).map some)

theorem assemblySourceRestFinishLeftMoveDescription_haltsFrom_sourceTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishLeftMoveDescription.HaltsFromTape
      (assemblySourceRestFinishSourceTape w sourceRestBits stage)
      (assemblySourceRestFinishBoundaryTape w sourceRestBits stage) := by
  simpa [assemblySourceRestFinishSourceTape_move_left] using
    assemblySourceRestFinishLeftMoveDescription_haltsFromTape
      (assemblySourceRestFinishSourceTape w sourceRestBits stage)

theorem assemblySourceRestFinishBoundaryTape_move_left_move_right
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (assemblySourceRestFinishBoundaryTape w sourceRestBits stage)) =
      assemblySourceRestFinishBoundaryTape w sourceRestBits stage := by
  rw [assemblySourceRestFinishBoundaryTape]
  exact
    tapeAtCells_move_left_move_right_none_cons_append_singleton
      (List.append (sourceRestBits.reverse.map some)
        (assemblySourceRestBoundaryLeftRev w stage))
      ((preservingCellPassCellBits sourceRestBits).map some)

/-!
**Scanner handoff reductions.**  The first reductions move from the source tape
to the quote boundary by scanning across the already-quoted source-rest field,
then back to the left boundary.  They are stated as exact
{name}`MachineDescription.HaltsFromTape` facts so the final construction can be
assembled with {name}`SeqViaCanonical`.
-/

def assemblySourceRestFinishQuoteBoundaryTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  scanRightToBlankLeftHaltTape
    (none :: List.append (sourceRestBits.reverse.map some)
      (assemblySourceRestBoundaryLeftRev w stage))
    (preservingCellPassCellBits sourceRestBits)

def AssemblySourceRestFinishQuoteBoundarySpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (assemblySourceRestFinishQuoteBoundaryTape w sourceRestBits stage)
        (assemblySourceRestFinishTargetTape w sourceRestBits stage)

def AssemblySourceRestFinishQuoteBoundaryConstruction : Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestFinishQuoteBoundarySpec finish

theorem scanRightToBlankLeftDescription_haltsFrom_finishSourceTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    scanRightToBlankLeftDescription.HaltsFromTape
      (assemblySourceRestFinishSourceTape w sourceRestBits stage)
      (assemblySourceRestFinishQuoteBoundaryTape w sourceRestBits stage) := by
  rw [assemblySourceRestFinishSourceTape,
    assemblySourceRestFinishQuoteBoundaryTape]
  exact
    scanRightToBlankLeftDescription_haltsFromTape
      (none :: List.append (sourceRestBits.reverse.map some)
        (assemblySourceRestBoundaryLeftRev w stage))
      (preservingCellPassCellBits sourceRestBits)

theorem assemblySourceRestFinishQuoteBoundaryTape_move_left_move_right
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (assemblySourceRestFinishQuoteBoundaryTape
            w sourceRestBits stage)) =
      assemblySourceRestFinishQuoteBoundaryTape w sourceRestBits stage := by
  cases hquote : preservingCellPassCellBits sourceRestBits with
  | nil =>
      rw [assemblySourceRestFinishQuoteBoundaryTape, hquote]
      simp [scanRightToBlankLeftHaltTape, tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons quoteHead quoteTail =>
      rw [assemblySourceRestFinishQuoteBoundaryTape, hquote]
      exact
        scanRightToBlankLeftHaltTape_move_left_move_right_cons
          (none :: List.append (sourceRestBits.reverse.map some)
            (assemblySourceRestBoundaryLeftRev w stage))
          quoteHead quoteTail

def assemblySourceRestFinishLeftBoundaryTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  scanLeftToBlankLeftHaltTape
    (List.append (sourceRestBits.reverse.map some)
      (assemblySourceRestBoundaryLeftRev w stage))
    (preservingCellPassCellBits sourceRestBits)
    [none]

def AssemblySourceRestFinishLeftBoundarySpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage)
        (assemblySourceRestFinishTargetTape w sourceRestBits stage)

def AssemblySourceRestFinishLeftBoundaryConstruction : Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestFinishLeftBoundarySpec finish

def AssemblySourceRestFinishLeftBoundaryCoreSpec
    (finish : MachineDescription) : Prop :=
  finish.SubroutineReady ∧
    forall (w sourceRestBits : Word Bool) (stage : Nat),
      finish.HaltsFromTape
        (assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage)
        (assemblySourceRestFinishTargetTape w sourceRestBits stage)

def AssemblySourceRestFinishLeftBoundaryCoreConstruction : Prop :=
  exists finish : MachineDescription,
    AssemblySourceRestFinishLeftBoundaryCoreSpec finish

theorem assemblySourceRestFinishLeftBoundaryConstruction_of_core
    (h : AssemblySourceRestFinishLeftBoundaryCoreConstruction) :
    AssemblySourceRestFinishLeftBoundaryConstruction := by
  exact h

theorem scanLeftToBlankLeftHaltTape_cons
    (cell : Option Bool) (leftBase : List (Option Bool))
    (bits : Word Bool) (right : List (Option Bool)) :
    scanLeftToBlankLeftHaltTape (cell :: leftBase) bits right =
      { left := leftBase
        head := cell
        right := none :: List.append (bits.map some) right } := by
  simp [scanLeftToBlankLeftHaltTape, tapeAtCells, Tape.move,
    Tape.moveLeft]

theorem scanLeftToBlankLeftHaltTape_right_of_left_ne_nil
    (leftBase : List (Option Bool)) (bits : Word Bool)
    (right : List (Option Bool)) (hleft : leftBase ≠ []) :
    (scanLeftToBlankLeftHaltTape leftBase bits right).right =
      none :: List.append (bits.map some) right := by
  cases leftBase with
  | nil =>
      contradiction
  | cons cell rest =>
      simp [scanLeftToBlankLeftHaltTape_cons]

theorem assemblySourceRestBoundaryLeftRev_ne_nil
    (w : Word Bool) (stage : Nat) :
    assemblySourceRestBoundaryLeftRev w stage ≠ [] := by
  cases w <;>
    simp [assemblySourceRestBoundaryLeftRev]

theorem assemblySourceRestFinishLeftBoundaryTape_cells_eq_fields
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage) =
      List.append
        (List.reverse (assemblySourceRestBoundaryLeftRev w stage))
        (List.append
          (sourceRestBits.map some)
          (none ::
            List.append
              ((preservingCellPassCellBits sourceRestBits).map some)
              [none])) := by
  rw [assemblySourceRestFinishLeftBoundaryTape,
    scanLeftToBlankLeftHaltTape]
  have hleft :
      List.append (sourceRestBits.reverse.map some)
          (assemblySourceRestBoundaryLeftRev w stage) ≠ [] := by
    cases sourceRestBits with
    | nil =>
        simpa using assemblySourceRestBoundaryLeftRev_ne_nil w stage
    | cons bit rest =>
        simp
  rw [tapeAtCells_move_left_none_cons_cells_of_left_ne_nil _ _ hleft]
  simp [List.reverse_append, List.map_reverse, List.append_assoc]

theorem assemblySourceRestFinishLeftBoundaryTape_cells_eq_prefix_sourceRest_quote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage) =
      List.append
        (List.reverse (assemblySourceRestBoundaryLeftRev w stage))
        (List.append
          (sourceRestBits.map some)
          (none ::
            List.append
              ((preservingCellPassCellBits sourceRestBits).map some)
              [none])) :=
  assemblySourceRestFinishLeftBoundaryTape_cells_eq_fields
    w sourceRestBits stage

theorem assemblySourceRestFinishLeftBoundaryTape_cells_eq_marker_split
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage) =
      List.append assemblySourceRestFinishParserMarkerLeftCells
        (none ::
          List.append
            (assemblySourceRestFinishParserMarkerRightCells w)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some)
              (List.append (sourceRestBits.map some)
                (none ::
                  List.append
                    ((preservingCellPassCellBits sourceRestBits).map some)
                    [none])))) := by
  rw [assemblySourceRestFinishLeftBoundaryTape_cells_eq_fields]
  change
    List.append
      (assemblySourceRestFinishParserStackCells w stage)
      (List.append
        (sourceRestBits.map some)
        (none ::
          List.append
            ((preservingCellPassCellBits sourceRestBits).map some)
            [none])) =
      List.append assemblySourceRestFinishParserMarkerLeftCells
        (none ::
          List.append
            (assemblySourceRestFinishParserMarkerRightCells w)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some)
              (List.append (sourceRestBits.map some)
                (none ::
                  List.append
                    ((preservingCellPassCellBits sourceRestBits).map some)
                    [none]))))
  rw [assemblySourceRestFinishParserStackCells_eq_prefixCells_append_stageNat]
  rw [assemblySourceRestFinishParserPrefixCells_eq_marker_split]
  simp [List.append_assoc]

theorem assemblySourceRestFinishLeftBoundaryTape_cells_nil_eq_marker_split
    (sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishLeftBoundaryTape
          ([] : Word Bool) sourceRestBits stage) =
      List.append assemblySourceRestFinishParserMarkerLeftCells
        (none ::
          List.append
            ([true, true].map some)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some)
              (List.append (sourceRestBits.map some)
                (none ::
                  List.append
                    ((preservingCellPassCellBits sourceRestBits).map some)
                    [none])))) := by
  rw [assemblySourceRestFinishLeftBoundaryTape_cells_eq_marker_split]
  rfl

theorem assemblySourceRestFinishLeftBoundaryTape_cells_cons_eq_marker_split
    (b : Bool) (rest sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishLeftBoundaryTape
          (b :: rest) sourceRestBits stage) =
      List.append assemblySourceRestFinishParserMarkerLeftCells
        (none ::
          List.append
            ((true :: false ::
              List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  rest.length)
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
                    b)
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                    rest))).map some)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some)
              (List.append (sourceRestBits.map some)
                (none ::
                  List.append
                    ((preservingCellPassCellBits sourceRestBits).map some)
                    [none])))) := by
  rw [assemblySourceRestFinishLeftBoundaryTape_cells_eq_marker_split]
  rfl

theorem assemblySourceRestFinishLeftBoundaryTape_cells_eq_boundaryTape_cells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage) =
      Tape.cells
        (assemblySourceRestFinishBoundaryTape w sourceRestBits stage) := by
  rw [assemblySourceRestFinishLeftBoundaryTape_cells_eq_fields,
    assemblySourceRestFinishBoundaryTape_cells]

theorem assemblySourceRestFinishLeftBoundaryTape_defaultedCells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishLeftBoundaryTape
            w sourceRestBits stage)) =
      List.append
        (assemblySourceRestFinishSourceBits w sourceRestBits stage)
        (false ::
          List.append (preservingCellPassCellBits sourceRestBits)
            [false]) := by
  rw [assemblySourceRestFinishLeftBoundaryTape_cells_eq_boundaryTape_cells]
  exact assemblySourceRestFinishBoundaryTape_defaultedCells
    w sourceRestBits stage

theorem assemblySourceRestFinishLeftBoundaryTape_defaultedCells_eq_sourceBits_quote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishLeftBoundaryTape
            w sourceRestBits stage)) =
      List.append
        (assemblySourceRestFinishSourceBits w sourceRestBits stage)
        (false ::
          List.append (preservingCellPassCellBits sourceRestBits)
            [false]) :=
  assemblySourceRestFinishLeftBoundaryTape_defaultedCells
    w sourceRestBits stage

theorem assemblySourceRestFinishLeftBoundaryTape_defaultedCells_eq_named_fields
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishLeftBoundaryTape
            w sourceRestBits stage)) =
      List.append
        (assemblySourceRestFinishRawSourceBits w sourceRestBits stage)
        (false ::
          List.append (preservingCellPassCellBits sourceRestBits)
            [false]) := by
  rw [assemblySourceRestFinishLeftBoundaryTape_defaultedCells,
    assemblySourceRestFinishRawSourceBits]

theorem
    assemblySourceRestFinishLeftBoundaryTape_defaultedCells_eq_prefix_sourceRest_quote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishLeftBoundaryTape
            w sourceRestBits stage)) =
      List.append
        (assemblySourceRestFinishSourcePrefixBits w stage)
        (List.append sourceRestBits
          (false ::
            List.append (preservingCellPassCellBits sourceRestBits)
              [false])) := by
  rw [assemblySourceRestFinishLeftBoundaryTape_defaultedCells,
    assemblySourceRestFinishSourceBits_eq_prefix_append_sourceRest]
  simp [List.append_assoc]

theorem assemblySourceRestFinishLeftBoundaryTape_defaultedCells_eq_fields
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishLeftBoundaryTape
            w sourceRestBits stage)) =
      List.append
        (assemblySourceRestFinishSourcePrefixBits w stage)
        (List.append sourceRestBits
          (List.append [false]
            (List.append (preservingCellPassCellBits sourceRestBits)
              [false]))) := by
  rw [
    assemblySourceRestFinishLeftBoundaryTape_defaultedCells_eq_prefix_sourceRest_quote]
  simp

theorem assemblySourceRestFinishLeftBoundaryTape_right
    (w sourceRestBits : Word Bool) (stage : Nat) :
    (assemblySourceRestFinishLeftBoundaryTape w sourceRestBits stage).right =
      none ::
        List.append
          ((preservingCellPassCellBits sourceRestBits).map some)
          [none] := by
  rw [assemblySourceRestFinishLeftBoundaryTape]
  exact
    scanLeftToBlankLeftHaltTape_right_of_left_ne_nil
      (List.append (sourceRestBits.reverse.map some)
        (assemblySourceRestBoundaryLeftRev w stage))
      (preservingCellPassCellBits sourceRestBits)
      [none]
      (by
        cases sourceRestBits with
        | nil =>
            simpa using assemblySourceRestBoundaryLeftRev_ne_nil w stage
        | cons bit rest =>
            simp)

theorem MixedParserStackRewriterSourceTape_eq_leftBoundary_of_split
    (w sourceRestBits : Word Bool) (stage : Nat)
    (prefixCells : List (Option Bool))
    (hsplit :
      assemblySourceRestFinishParserStackCells w stage =
        List.append prefixCells
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)) :
    MixedParserStackRewriterSourceTape prefixCells
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage)
        sourceRestBits
        (preservingCellPassCellBits sourceRestBits) =
      assemblySourceRestFinishLeftBoundaryTape
        w sourceRestBits stage := by
  have hboundary :
      assemblySourceRestBoundaryLeftRev w stage =
        List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).reverse.map some)
          prefixCells.reverse := by
    have hrev := congrArg List.reverse hsplit
    simpa [assemblySourceRestFinishParserStackCells,
      List.reverse_append, List.map_reverse] using hrev
  rw [MixedParserStackRewriterSourceTape,
    assemblySourceRestFinishLeftBoundaryTape, hboundary]

theorem
    exists_MixedParserStackRewriterSourceTape_eq_leftBoundary
    (w sourceRestBits : Word Bool) (stage : Nat) :
    exists prefixCells : List (Option Bool),
      MixedParserStackRewriterSourceTape prefixCells
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits
          (preservingCellPassCellBits sourceRestBits) =
        assemblySourceRestFinishLeftBoundaryTape
          w sourceRestBits stage := by
  rcases
      assemblySourceRestFinishParserStackCells_eq_prefix_append_stageNat
        w stage with
    ⟨prefixCells, hsplit⟩
  exact
    ⟨prefixCells,
      MixedParserStackRewriterSourceTape_eq_leftBoundary_of_split
        w sourceRestBits stage prefixCells hsplit⟩

theorem MixedParserStackRewriterSourceTape_eq_leftBoundary
    (w sourceRestBits : Word Bool) (stage : Nat) :
    MixedParserStackRewriterSourceTape
        (assemblySourceRestFinishParserPrefixCells w)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage)
        sourceRestBits
        (preservingCellPassCellBits sourceRestBits) =
      assemblySourceRestFinishLeftBoundaryTape
        w sourceRestBits stage :=
  MixedParserStackRewriterSourceTape_eq_leftBoundary_of_split
    w sourceRestBits stage
    (assemblySourceRestFinishParserPrefixCells w)
    (assemblySourceRestFinishParserStackCells_eq_prefixCells_append_stageNat
      w stage)

theorem assemblySourceRestFinishTargetTape_eq_tapeAtCells_fields_prefixLength
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetTape w sourceRestBits stage =
      tapeAtCells
        ((List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.header)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              ((assemblySourceRestFinishSourcePrefixBits w stage).length +
                sourceRestBits.length))
            (List.append
              (preservingCellPassCellBits
                (assemblySourceRestFinishSourcePrefixBits w stage))
              (preservingCellPassCellBits sourceRestBits)))).reverse.map some)
        ((List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage)
          sourceRestBits).map some) := by
  rw [assemblySourceRestFinishTargetTape,
    assemblySourceRestFinishTargetPrefixBits_eq_splitQuote_prefixLength]

theorem assemblySourceRestFinishTargetTape_eq_tapeAtCells_named_prefixLength
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetTape w sourceRestBits stage =
      tapeAtCells
        ((assemblySourceRestFinishTargetPrefixBits
          w sourceRestBits stage).reverse.map some)
        ((assemblySourceRestFinishRawTailBits
          sourceRestBits stage).map some) := by
  rw [assemblySourceRestFinishTargetTape,
    assemblySourceRestFinishRawTailBits]

theorem assemblySourceRestFinishTargetTape_eq_tapeAtCells_named_fields_prefixLength
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetTape w sourceRestBits stage =
      tapeAtCells
        ((List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.header)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              ((assemblySourceRestFinishSourcePrefixBits w stage).length +
                sourceRestBits.length))
            (List.append
              (assemblySourceRestFinishQuotedPrefixBits w stage)
              (preservingCellPassCellBits sourceRestBits)))).reverse.map some)
        ((assemblySourceRestFinishRawTailBits
          sourceRestBits stage).map some) := by
  rw [assemblySourceRestFinishTargetTape,
    assemblySourceRestFinishTargetPrefixBits_eq_named_fields_prefixLength,
    assemblySourceRestFinishRawTailBits]

theorem assemblySourceRestFinishTargetTape_eq_tapeAtCells_segments
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishTargetTape w sourceRestBits stage =
      tapeAtCells
        ((List.append
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits)).reverse.map some)
        ((assemblySourceRestFinishRawTailBits
          sourceRestBits stage).map some) := by
  rw [assemblySourceRestFinishTargetTape,
    assemblySourceRestFinishTargetPrefixBits_eq_prefixQuote_append_restQuote,
    assemblySourceRestFinishRawTailBits]

theorem MixedParserStackRewriterTargetTape_eq_targetTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    MixedParserStackRewriterTargetTape
        (assemblySourceRestFinishQuotedPrefixBits w stage)
        (assemblySourceRestFinishLengthHeaderBits
          w sourceRestBits stage)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage)
        sourceRestBits
        (preservingCellPassCellBits sourceRestBits) =
      assemblySourceRestFinishTargetTape w sourceRestBits stage := by
  rw [MixedParserStackRewriterTargetTape,
    assemblySourceRestFinishTargetTape_eq_tapeAtCells_segments,
    assemblySourceRestFinishPrefixQuoteOutputBits,
    assemblySourceRestFinishRawTailBits]
  simp [List.append_assoc]

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

/--
Core finite-machine obligation for the left-boundary source-rest finish phase.
All surrounding results are exact-tape adapters; this leaf is responsible for
rewriting the mixed parser-stack/source-rest layout into
{name}`assemblySourceRestFinishTargetTape`.
-/
theorem assemblySourceRestFinishLeftBoundaryCoreConstruction :
    AssemblySourceRestFinishLeftBoundaryCoreConstruction := by
  sorry

theorem assemblySourceRestFinishLeftBoundaryConstruction :
    AssemblySourceRestFinishLeftBoundaryConstruction :=
  assemblySourceRestFinishLeftBoundaryConstruction_of_core
    assemblySourceRestFinishLeftBoundaryCoreConstruction

theorem assemblySourceRestFinishQuoteBoundaryConstruction :
    AssemblySourceRestFinishQuoteBoundaryConstruction :=
  assemblySourceRestFinishQuoteBoundaryConstruction_of_leftBoundary
    assemblySourceRestFinishLeftBoundaryConstruction

theorem assemblySourceRestFinishConstruction :
    AssemblySourceRestFinishConstruction :=
  assemblySourceRestFinishConstruction_of_quoteBoundary
    assemblySourceRestFinishQuoteBoundaryConstruction


end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
