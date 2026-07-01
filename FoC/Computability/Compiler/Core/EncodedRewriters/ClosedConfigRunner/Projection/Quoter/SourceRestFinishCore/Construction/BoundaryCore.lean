import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.Views
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind

set_option doc.verso true

/-!
# Source-rest finish boundary core

This module contains the low-level tape-shape and scanner facts used by the
source-rest finish construction.  The public construction module imports this
file and keeps the higher-level construction contracts and adapters separate
from the boundary mechanics.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

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

/-!
**Left-boundary seeker for the mixed parser stack.**  This scanner is the
first finite slice needed by the core copier.  Unlike the ordinary left scan,
it treats the parser-stack marker blank as data, recognizes the fixed
transition-prefix cells to its left, and halts on the true blank before the
source segment.
-/

def mixedParserStackSeekLeftBoundaryDescription : MachineDescription where
  stateCount := 20
  start := 0
  halt := 19
  transitions :=
    [ transition 0 (some false) (some false) Direction.left 0
    , transition 0 (some true) (some true) Direction.left 0
    , transition 0 none none Direction.left 10
    , transition 10 (some false) (some false) Direction.left 11
    , transition 11 (some true) (some true) Direction.left 12
    , transition 12 (some false) (some false) Direction.left 13
    , transition 13 (some false) (some false) Direction.left 14
    , transition 14 (some false) (some false) Direction.left 19
    ]

private abbrev MPSLB := mixedParserStackSeekLeftBoundaryDescription

theorem mixedParserStackSeekLeftBoundaryDescription_wellFormed :
    MPSLB.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := MPSLB.transitions)
      (stateCount := MPSLB.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := MPSLB.transitions)
      (by decide)

theorem mixedParserStackSeekLeftBoundaryDescription_haltTransitionFree :
    MPSLB.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := MPSLB.transitions)
    (state := MPSLB.halt)
    (by decide)

theorem mixedParserStackSeekLeftBoundaryDescription_subroutineReady :
    MPSLB.SubroutineReady :=
  ⟨mixedParserStackSeekLeftBoundaryDescription_wellFormed,
    mixedParserStackSeekLeftBoundaryDescription_haltTransitionFree⟩

theorem mixedParserStackSeekLeftBoundaryDescription_run_payloadRev
    (scanRev : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    MPSLB.runConfig (scanRev.length + 1)
        { state := MPSLB.start
          tape :=
            tapeAtCells
              (List.append (scanRev.map some)
                (none ::
                  List.reverse assemblySourceRestFinishParserMarkerLeftCells))
              (some current :: right) } =
      { state := MPSLB.start
        tape :=
          tapeAtCells
            (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
            (none ::
              List.append (scanRev.reverse.map some)
                (some current :: right)) } := by
  induction scanRev generalizing current right with
  | nil =>
      cases current <;>
        simp [MPSLB, mixedParserStackSeekLeftBoundaryDescription,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  | cons prev rest ih =>
      rw [show (prev :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          MPSLB.runConfig 1
              { state := MPSLB.start
                tape :=
                  tapeAtCells
                    (List.append ((prev :: rest).map some)
                      (none ::
                        List.reverse
                          assemblySourceRestFinishParserMarkerLeftCells))
                    (some current :: right) } =
            { state := MPSLB.start
              tape :=
                tapeAtCells
                  (List.append (rest.map some)
                    (none ::
                      List.reverse
                        assemblySourceRestFinishParserMarkerLeftCells))
                  (some prev :: some current :: right) } := by
        cases current <;> cases prev <;>
          simp [MPSLB, mixedParserStackSeekLeftBoundaryDescription,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih prev (some current :: right)

theorem mixedParserStackSeekLeftBoundaryDescription_run_markerLeft
    (right : List (Option Bool)) :
    MPSLB.runConfig 6
        { state := MPSLB.start
          tape :=
            tapeAtCells
              (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
              (none :: right) } =
      { state := MPSLB.halt
        tape :=
          tapeAtCells []
            (none ::
              List.append assemblySourceRestFinishParserMarkerLeftCells
                (none :: right)) } := by
  simp [MPSLB, mixedParserStackSeekLeftBoundaryDescription,
    assemblySourceRestFinishParserMarkerLeftCells,
    transitionPrefixLeftTail, runConfig, stepConfig, lookupTransition,
    Matches, transition, tapeAtCells, Tape.read, Tape.write, Tape.move,
    Tape.moveLeft]

theorem mixedParserStackSeekLeftBoundaryDescription_run_payloadToLeftBoundary
    (scanRev : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    MPSLB.runConfig (scanRev.length + 7)
        { state := MPSLB.start
          tape :=
            tapeAtCells
              (List.append (scanRev.map some)
                (none ::
                  List.reverse assemblySourceRestFinishParserMarkerLeftCells))
              (some current :: right) } =
      { state := MPSLB.halt
        tape :=
          tapeAtCells []
            (none ::
              List.append assemblySourceRestFinishParserMarkerLeftCells
                (none ::
                  List.append (scanRev.reverse.map some)
                    (some current :: right))) } := by
  rw [show scanRev.length + 7 = (scanRev.length + 1) + 6 by omega]
  rw [runConfig_add]
  rw [mixedParserStackSeekLeftBoundaryDescription_run_payloadRev]
  rw [mixedParserStackSeekLeftBoundaryDescription_run_markerLeft]

def assemblySourceRestFinishRightPayloadBits
    (w sourceRestBits : Word Bool) (stage : Nat) : Word Bool :=
  List.append (assemblySourceRestFinishParserMarkerRightBits w)
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        stage)
      sourceRestBits)

def assemblySourceRestFinishRawTailPrefixBits
    (w : Word Bool) : Word Bool :=
  List.append
    (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
    (List.append [false, false]
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
        w))

theorem assemblySourceRestFinishSourceBits_eq_rawTailPrefix_append_rawTail
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishSourceBits w sourceRestBits stage =
      List.append (assemblySourceRestFinishRawTailPrefixBits w)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage) := by
  rw [assemblySourceRestFinishSourceBits,
    assemblySourceRestFinishRawTailPrefixBits,
    assemblySourceRestFinishRawTailBits]
  rw [DovetailInitialLayoutInitializer.stageInputBits_eq_false_false_tail]
  rw [
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTail_eq_prefix_stageNat]
  simp [List.append_assoc]

def MixedParserStackRewriterTrueLeftBoundaryTape
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape Bool :=
  tapeAtCells []
    (none ::
      List.append assemblySourceRestFinishParserMarkerLeftCells
        (none ::
          List.append
            ((assemblySourceRestFinishRightPayloadBits
              w sourceRestBits stage).map some)
            (none :: List.append (quoteRestBits.map some) [none])))

def MixedParserStackRewriterTrueSourceCells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List (Option Bool) :=
  List.append assemblySourceRestFinishParserMarkerLeftCells
    (none ::
      (assemblySourceRestFinishRightPayloadBits
        w sourceRestBits stage).map some)

def MixedParserStackRewriterDefaultedSourceCells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List (Option Bool) :=
  List.append assemblySourceRestFinishParserMarkerLeftCells
    (some false ::
      (assemblySourceRestFinishRightPayloadBits
        w sourceRestBits stage).map some)

theorem assemblySourceRestFinishRightPayloadBits_ne_nil
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishRightPayloadBits
      w sourceRestBits stage ≠ [] := by
  cases w with
  | nil =>
      simp [assemblySourceRestFinishRightPayloadBits,
        assemblySourceRestFinishParserMarkerRightBits]
  | cons b rest =>
      simp [assemblySourceRestFinishRightPayloadBits,
        assemblySourceRestFinishParserMarkerRightBits,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix]

theorem MixedParserStackRewriterTrueSourceCells_eq_flatSourceCells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    MixedParserStackRewriterTrueSourceCells w sourceRestBits stage =
      assemblySourceRestFinishFlatSourceCells
        w sourceRestBits stage := by
  rw [MixedParserStackRewriterTrueSourceCells,
    assemblySourceRestFinishFlatSourceCells,
    assemblySourceRestFinishParserStackCells_eq_prefixCells_append_stageNat,
    assemblySourceRestFinishParserPrefixCells_eq_marker_split,
    assemblySourceRestFinishParserMarkerRightCells_eq_bits,
    assemblySourceRestFinishRightPayloadBits]
  simp [List.map_append, List.append_assoc]

theorem MixedParserStackRewriterTrueSourceCells_defaultBits
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (MixedParserStackRewriterTrueSourceCells
          w sourceRestBits stage) =
      assemblySourceRestFinishSourceBits
        w sourceRestBits stage := by
  rw [MixedParserStackRewriterTrueSourceCells_eq_flatSourceCells]
  exact assemblySourceRestFinishFlatSourceCells_defaultBits
    w sourceRestBits stage

theorem MixedParserStackRewriterTrueSourceCells_length
    (w sourceRestBits : Word Bool) (stage : Nat) :
    (MixedParserStackRewriterTrueSourceCells
        w sourceRestBits stage).length =
      (assemblySourceRestFinishSourceBits
        w sourceRestBits stage).length := by
  rw [← mixedParserStack_defaultBits_length
    (MixedParserStackRewriterTrueSourceCells
      w sourceRestBits stage)]
  rw [MixedParserStackRewriterTrueSourceCells_defaultBits]

theorem MixedParserStackRewriterTrueSourceCells_quotedBits
    (w sourceRestBits : Word Bool) (stage : Nat) :
    mixedParserStackQuotedCellsBits
        (MixedParserStackRewriterTrueSourceCells
          w sourceRestBits stage) =
      List.append
        (assemblySourceRestFinishQuotedPrefixBits w stage)
        (preservingCellPassCellBits sourceRestBits) := by
  rw [mixedParserStackQuotedCellsBits_eq_defaultBits]
  rw [MixedParserStackRewriterTrueSourceCells_defaultBits]
  rw [assemblySourceRestFinishSourceBits_eq_prefix_append_sourceRest]
  rw [preservingCellPassCellBits_append_bool]
  rfl

theorem MixedParserStackRewriterTrueSourceCells_quotedBits_eq_sourceBits
    (w sourceRestBits : Word Bool) (stage : Nat) :
    mixedParserStackQuotedCellsBits
        (MixedParserStackRewriterTrueSourceCells
          w sourceRestBits stage) =
      preservingCellPassCellBits
        (assemblySourceRestFinishSourceBits
          w sourceRestBits stage) := by
  rw [mixedParserStackQuotedCellsBits_eq_defaultBits]
  rw [MixedParserStackRewriterTrueSourceCells_defaultBits]

theorem MixedParserStackRewriterDefaultedSourceCells_defaultBits
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (MixedParserStackRewriterDefaultedSourceCells
          w sourceRestBits stage) =
      assemblySourceRestFinishSourceBits
        w sourceRestBits stage := by
  rw [← MixedParserStackRewriterTrueSourceCells_defaultBits
    w sourceRestBits stage]
  rw [MixedParserStackRewriterDefaultedSourceCells,
    MixedParserStackRewriterTrueSourceCells]
  simp [List.map_append, List.map_map, optionBitDefaultFalse,
    optionBitDefaultFalse_map_some]

theorem MixedParserStackRewriterDefaultedSourceCells_length
    (w sourceRestBits : Word Bool) (stage : Nat) :
    (MixedParserStackRewriterDefaultedSourceCells
        w sourceRestBits stage).length =
      (assemblySourceRestFinishSourceBits
        w sourceRestBits stage).length := by
  rw [← mixedParserStack_defaultBits_length
    (MixedParserStackRewriterDefaultedSourceCells
      w sourceRestBits stage)]
  rw [MixedParserStackRewriterDefaultedSourceCells_defaultBits]

theorem MixedParserStackRewriterDefaultedSourceCells_quotedBits
    (w sourceRestBits : Word Bool) (stage : Nat) :
    mixedParserStackQuotedCellsBits
        (MixedParserStackRewriterDefaultedSourceCells
          w sourceRestBits stage) =
      List.append
        (assemblySourceRestFinishQuotedPrefixBits w stage)
        (preservingCellPassCellBits sourceRestBits) := by
  rw [mixedParserStackQuotedCellsBits_eq_defaultBits]
  rw [MixedParserStackRewriterDefaultedSourceCells_defaultBits]
  rw [assemblySourceRestFinishSourceBits_eq_prefix_append_sourceRest]
  rw [preservingCellPassCellBits_append_bool]
  rfl

theorem MixedParserStackRewriterDefaultedSourceCells_eq_sourceBits_map_some
    (w sourceRestBits : Word Bool) (stage : Nat) :
    MixedParserStackRewriterDefaultedSourceCells
        w sourceRestBits stage =
      (assemblySourceRestFinishSourceBits
        w sourceRestBits stage).map some := by
  rw [assemblySourceRestFinishSourceBits_eq_prefix_append_sourceRest,
    assemblySourceRestFinishSourcePrefixBits]
  rw [DovetailInitialLayoutInitializer.stageInputBits_eq_false_false_tail]
  rw [
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTail_eq_prefix_stageNat]
  cases w with
  | nil =>
      simp [MixedParserStackRewriterDefaultedSourceCells,
        assemblySourceRestFinishRightPayloadBits,
        assemblySourceRestFinishParserMarkerRightBits,
        assemblySourceRestFinishParserMarkerLeftCells,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix,
        transitionPrefixLeftTail, encodeCodeSymbolAsInput,
        List.map_append]
  | cons b rest =>
      simp [MixedParserStackRewriterDefaultedSourceCells,
        assemblySourceRestFinishRightPayloadBits,
        assemblySourceRestFinishParserMarkerRightBits,
        assemblySourceRestFinishParserMarkerLeftCells,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix,
        transitionPrefixLeftTail, encodeCodeSymbolAsInput,
        List.map_append]

theorem MixedParserStackRewriterTrueLeftBoundaryTape_cells
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (MixedParserStackRewriterTrueLeftBoundaryTape
          w sourceRestBits quoteRestBits stage) =
      none ::
        List.append
          (MixedParserStackRewriterTrueSourceCells
            w sourceRestBits stage)
          (none ::
            List.append (quoteRestBits.map some) [none]) := by
  rw [MixedParserStackRewriterTrueLeftBoundaryTape,
    MixedParserStackRewriterTrueSourceCells]
  simp [tapeAtCells, Tape.cells, List.append_assoc]

theorem MixedParserStackRewriterTrueLeftBoundaryTape_defaultedCells
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (MixedParserStackRewriterTrueLeftBoundaryTape
            w sourceRestBits quoteRestBits stage)) =
      false ::
        List.append
          (assemblySourceRestFinishSourceBits
            w sourceRestBits stage)
          (false :: List.append quoteRestBits [false]) := by
  rw [MixedParserStackRewriterTrueLeftBoundaryTape_cells]
  simp [List.map_append,
    MixedParserStackRewriterTrueSourceCells_defaultBits,
    optionBitDefaultFalse, List.map_map,
    optionBitDefaultFalse_map_some]

theorem MixedParserStackRewriterTrueLeftBoundaryTape_defaultedCells_finish
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (MixedParserStackRewriterTrueLeftBoundaryTape
            w sourceRestBits
            (preservingCellPassCellBits sourceRestBits) stage)) =
      false ::
        List.append
          (assemblySourceRestFinishSourceBits
            w sourceRestBits stage)
          (false ::
            List.append (preservingCellPassCellBits sourceRestBits)
              [false]) := by
  rw [MixedParserStackRewriterTrueLeftBoundaryTape_defaultedCells]

def MixedParserStackRewriterDefaultedInternalMarkerTape
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape Bool :=
  tapeAtCells
    (some false ::
      List.append
        (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
        [none])
    (List.append
      ((assemblySourceRestFinishRightPayloadBits
        w sourceRestBits stage).map some)
      (none :: List.append (quoteRestBits.map some) [none]))

def mixedParserStackDefaultInternalMarkerDescription :
    MachineDescription where
  stateCount := 8
  start := 0
  halt := 7
  transitions :=
    [ transition 0 none none Direction.right 1
    , transition 1 (some false) (some false) Direction.right 2
    , transition 2 (some false) (some false) Direction.right 3
    , transition 3 (some false) (some false) Direction.right 4
    , transition 4 (some true) (some true) Direction.right 5
    , transition 5 (some false) (some false) Direction.right 6
    , transition 6 none (some false) Direction.right 7
    ]

private abbrev MPSDIM :=
  mixedParserStackDefaultInternalMarkerDescription

theorem mixedParserStackDefaultInternalMarkerDescription_wellFormed :
    MPSDIM.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := MPSDIM.transitions)
      (stateCount := MPSDIM.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := MPSDIM.transitions)
      (by decide)

theorem mixedParserStackDefaultInternalMarkerDescription_haltTransitionFree :
    MPSDIM.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := MPSDIM.transitions)
    (state := MPSDIM.halt)
    (by decide)

theorem mixedParserStackDefaultInternalMarkerDescription_subroutineReady :
    MPSDIM.SubroutineReady :=
  ⟨mixedParserStackDefaultInternalMarkerDescription_wellFormed,
    mixedParserStackDefaultInternalMarkerDescription_haltTransitionFree⟩

theorem mixedParserStackDefaultInternalMarkerDescription_run
    (right : List (Option Bool)) :
    MPSDIM.runConfig 7
        { state := MPSDIM.start
          tape :=
            tapeAtCells []
              (none ::
                List.append assemblySourceRestFinishParserMarkerLeftCells
                  (none :: right)) } =
      { state := MPSDIM.halt
        tape :=
          tapeAtCells
            (some false ::
              List.append
                (List.reverse
                  assemblySourceRestFinishParserMarkerLeftCells)
                [none])
            right } := by
  cases right <;>
    simp [MPSDIM, mixedParserStackDefaultInternalMarkerDescription,
      assemblySourceRestFinishParserMarkerLeftCells,
      transitionPrefixLeftTail, runConfig, stepConfig,
      lookupTransition, Matches, transition, tapeAtCells,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem
    mixedParserStackDefaultInternalMarkerDescription_haltsFrom_trueLeftBoundaryTape
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    MPSDIM.HaltsFromTape
      (MixedParserStackRewriterTrueLeftBoundaryTape
        w sourceRestBits quoteRestBits stage)
      (MixedParserStackRewriterDefaultedInternalMarkerTape
        w sourceRestBits quoteRestBits stage) := by
  refine ⟨7, ?_⟩
  have hrun :=
    mixedParserStackDefaultInternalMarkerDescription_run
      (List.append
        ((assemblySourceRestFinishRightPayloadBits
          w sourceRestBits stage).map some)
        (none :: List.append (quoteRestBits.map some) [none]))
  constructor
  · simpa [MixedParserStackRewriterTrueLeftBoundaryTape,
      MixedParserStackRewriterDefaultedInternalMarkerTape] using
      congrArg Configuration.state hrun
  · simpa [MixedParserStackRewriterTrueLeftBoundaryTape,
      MixedParserStackRewriterDefaultedInternalMarkerTape,
      List.append_assoc] using
      congrArg Configuration.tape hrun

theorem
    MixedParserStackRewriterDefaultedInternalMarkerTape_move_left_move_right
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (MixedParserStackRewriterDefaultedInternalMarkerTape
            w sourceRestBits quoteRestBits stage)) =
      MixedParserStackRewriterDefaultedInternalMarkerTape
        w sourceRestBits quoteRestBits stage := by
  cases w with
  | nil =>
      simp [MixedParserStackRewriterDefaultedInternalMarkerTape,
        assemblySourceRestFinishRightPayloadBits,
        assemblySourceRestFinishParserMarkerRightBits,
        tapeAtCells, Tape.move, Tape.moveRight, Tape.moveLeft]
  | cons b rest =>
      simp [MixedParserStackRewriterDefaultedInternalMarkerTape,
        assemblySourceRestFinishRightPayloadBits,
        assemblySourceRestFinishParserMarkerRightBits,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix,
        tapeAtCells, Tape.move, Tape.moveRight, Tape.moveLeft]

theorem MixedParserStackRewriterDefaultedInternalMarkerTape_cells
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (MixedParserStackRewriterDefaultedInternalMarkerTape
          w sourceRestBits quoteRestBits stage) =
      none ::
        List.append assemblySourceRestFinishParserMarkerLeftCells
          (some false ::
            List.append
              ((assemblySourceRestFinishRightPayloadBits
                w sourceRestBits stage).map some)
              (none ::
                List.append (quoteRestBits.map some) [none])) := by
  rw [MixedParserStackRewriterDefaultedInternalMarkerTape]
  cases hpayload :
      assemblySourceRestFinishRightPayloadBits
        w sourceRestBits stage with
  | nil =>
      exact
        False.elim
          ((assemblySourceRestFinishRightPayloadBits_ne_nil
              w sourceRestBits stage) hpayload)
  | cons bit rest =>
      simp [tapeAtCells, Tape.cells,
        List.reverse_append, List.append_assoc]

theorem
    MixedParserStackRewriterDefaultedInternalMarkerTape_cells_eq_defaultedSourceCells
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (MixedParserStackRewriterDefaultedInternalMarkerTape
          w sourceRestBits quoteRestBits stage) =
      none ::
        List.append
          (MixedParserStackRewriterDefaultedSourceCells
            w sourceRestBits stage)
          (none ::
            List.append (quoteRestBits.map some) [none]) := by
  rw [MixedParserStackRewriterDefaultedInternalMarkerTape_cells,
    MixedParserStackRewriterDefaultedSourceCells]
  simp [List.append_assoc]

theorem MixedParserStackRewriterDefaultedInternalMarkerTape_defaultedCells
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (MixedParserStackRewriterDefaultedInternalMarkerTape
            w sourceRestBits quoteRestBits stage)) =
      false ::
        List.append
          (assemblySourceRestFinishSourceBits
            w sourceRestBits stage)
          (false :: List.append quoteRestBits [false]) := by
  rw [MixedParserStackRewriterDefaultedInternalMarkerTape_cells]
  have hsource :=
    MixedParserStackRewriterTrueSourceCells_defaultBits
      w sourceRestBits stage
  rw [MixedParserStackRewriterTrueSourceCells] at hsource
  simp [List.map_append, List.map_map,
    optionBitDefaultFalse, optionBitDefaultFalse_map_some] at hsource ⊢
  rw [← hsource]
  simp [List.append_assoc]

def MixedParserStackRewriterWholeSourceTargetTape
    (sourceCells : List (Option Bool)) (tailBits : Word Bool) :
    Tape Bool :=
  tapeAtCells
    ((List.append
      (encodeCodeSymbolAsInput MachineCodeSymbol.header)
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          sourceCells.length)
        (mixedParserStackQuotedCellsBits sourceCells))).reverse.map some)
    (tailBits.map some)

theorem MixedParserStackRewriterWholeSourceTargetTape_eq_sourceBits
    (w sourceRestBits : Word Bool) (stage : Nat) :
    MixedParserStackRewriterWholeSourceTargetTape
        (MixedParserStackRewriterTrueSourceCells
          w sourceRestBits stage)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage) =
      tapeAtCells
        ((List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.header)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (assemblySourceRestFinishSourceBits
                w sourceRestBits stage).length)
            (preservingCellPassCellBits
              (assemblySourceRestFinishSourceBits
                w sourceRestBits stage)))).reverse.map some)
        ((assemblySourceRestFinishRawTailBits
          sourceRestBits stage).map some) := by
  rw [MixedParserStackRewriterWholeSourceTargetTape]
  rw [MixedParserStackRewriterTrueSourceCells_length]
  rw [MixedParserStackRewriterTrueSourceCells_quotedBits_eq_sourceBits]

theorem MixedParserStackRewriterTargetTape_eq_wholeSourceTargetTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    MixedParserStackRewriterTargetTape
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
        (preservingCellPassCellBits sourceRestBits) =
      MixedParserStackRewriterWholeSourceTargetTape
        (MixedParserStackRewriterTrueSourceCells
          w sourceRestBits stage)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage) := by
  rw [MixedParserStackRewriterTargetTape,
    MixedParserStackRewriterWholeSourceTargetTape,
    MixedParserStackRewriterPrefixQuote_eq_assemblyQuotedPrefix,
    MixedParserStackRewriterLengthHeader_eq_assemblyLengthHeader,
    assemblySourceRestFinishLengthHeaderBits,
    assemblySourceRestFinishRawTailBits]
  have hlen :
      (MixedParserStackRewriterTrueSourceCells
          w sourceRestBits stage).length =
        (assemblySourceRestFinishSourcePrefixBits w stage).length +
          sourceRestBits.length := by
    rw [MixedParserStackRewriterTrueSourceCells_length,
      assemblySourceRestFinishSourceBits_length_eq_prefix_add]
  rw [hlen]
  rw [MixedParserStackRewriterTrueSourceCells_quotedBits]
  simp [List.append_assoc]

def MixedParserStackRewriterDefaultedRightBoundaryTape
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape Bool :=
  Tape.move Direction.left
    (tapeAtCells
      (List.append
        ((assemblySourceRestFinishRightPayloadBits
          w sourceRestBits stage).reverse.map some)
        (some false ::
          List.append
            (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
            [none]))
      (none :: List.append (quoteRestBits.map some) [none]))

def MixedParserStackRewriterDefaultedSourceStartTape
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape Bool :=
  tapeAtCells [none]
    (List.append
      ((assemblySourceRestFinishSourceBits
        w sourceRestBits stage).map some)
      (none :: List.append (quoteRestBits.map some) [none]))

def MixedParserStackRewriterDefaultedSourceRestBoundaryTape
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape Bool :=
  tapeAtCells
    (List.append (assemblySourceRestBoundaryLeftRev w stage) [none])
    (List.append (sourceRestBits.map some)
      (none :: List.append (quoteRestBits.map some) [none]))

theorem MixedParserStackRewriterDefaultedSourceRestBoundaryTape_cells
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (MixedParserStackRewriterDefaultedSourceRestBoundaryTape
          w sourceRestBits quoteRestBits stage) =
      none ::
        List.append
          (List.reverse (assemblySourceRestBoundaryLeftRev w stage))
          (List.append (sourceRestBits.map some)
            (none :: List.append (quoteRestBits.map some) [none])) := by
  rw [MixedParserStackRewriterDefaultedSourceRestBoundaryTape]
  cases sourceRestBits <;>
    simp [tapeAtCells, Tape.cells, List.reverse_append]

theorem
    MixedParserStackRewriterDefaultedSourceRestBoundaryTape_defaultedCells
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (MixedParserStackRewriterDefaultedSourceRestBoundaryTape
            w sourceRestBits quoteRestBits stage)) =
      false ::
        List.append
          (assemblySourceRestFinishSourcePrefixBits w stage)
          (List.append sourceRestBits
            (false :: List.append quoteRestBits [false])) := by
  rw [MixedParserStackRewriterDefaultedSourceRestBoundaryTape_cells]
  have hprefix :=
    assemblySourceRestBoundaryLeftRev_defaultBits_eq_sourcePrefix
      w stage
  simp [List.map_append, List.map_map, optionBitDefaultFalse,
    optionBitDefaultFalse_map_some, hprefix]

theorem
    assemblyPrefixDescription_haltsFrom_empty_defaultedSourceStart_to_sourceRestBoundary
    (sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    AssemblyPrefixDescription.HaltsFromTape
      (MixedParserStackRewriterDefaultedSourceStartTape
        ([] : Word Bool) sourceRestBits quoteRestBits stage)
      (MixedParserStackRewriterDefaultedSourceRestBoundaryTape
        ([] : Word Bool) sourceRestBits quoteRestBits stage) := by
  rcases
      assemblyPrefixDescription_run_empty_stageInput_to_sourceRest_boundary_cells_withBase
        [none]
        (List.append (sourceRestBits.map some)
          (none :: List.append (quoteRestBits.map some) [none]))
        stage with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn,
      AssemblyPrefixDescription,
      MixedParserStackRewriterDefaultedSourceStartTape,
      assemblySourceRestFinishSourceBits, List.map_append,
      List.append_assoc, config] using
      congrArg Configuration.state hsteps
  · simpa [MachineDescription.HaltsFromTapeIn,
      MixedParserStackRewriterDefaultedSourceRestBoundaryTape,
      MixedParserStackRewriterDefaultedSourceStartTape,
      assemblySourceRestFinishSourceBits,
      assemblySourceRestBoundaryLeftRev, List.map_append,
      List.append_assoc, config] using
      congrArg Configuration.tape hsteps

theorem
    assemblyPrefixDescription_haltsFrom_defaultedSourceStart_to_sourceRestBoundary
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    AssemblyPrefixDescription.HaltsFromTape
      (MixedParserStackRewriterDefaultedSourceStartTape
        w sourceRestBits quoteRestBits stage)
      (MixedParserStackRewriterDefaultedSourceRestBoundaryTape
        w sourceRestBits quoteRestBits stage) := by
  rcases
      assemblyPrefixDescription_run_stageInput_to_sourceRest_boundary_cells_withBase_core
        [none] w stage
        (List.append (sourceRestBits.map some)
          (none :: List.append (quoteRestBits.map some) [none])) with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsFromTapeIn,
      AssemblyPrefixDescription,
      MixedParserStackRewriterDefaultedSourceStartTape,
      assemblySourceRestFinishSourceBits, List.map_append,
      List.append_assoc, config] using
      congrArg Configuration.state hsteps
  · simpa [MachineDescription.HaltsFromTapeIn,
      MixedParserStackRewriterDefaultedSourceRestBoundaryTape,
      MixedParserStackRewriterDefaultedSourceStartTape,
      assemblySourceRestFinishSourceBits,
      assemblySourceRestBoundaryLeftRev, List.map_append,
      List.append_assoc, config] using
      congrArg Configuration.tape hsteps

theorem
    assemblySkeletonDescription_run_defaultedSourceStart_to_sourceRestBoundary
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    exists steps : Nat,
      AssemblySkeletonDescription.runConfig steps
          { state := AssemblySkeletonDescription.start
            tape :=
              MixedParserStackRewriterDefaultedSourceStartTape
                w sourceRestBits quoteRestBits stage } =
        { state := 210
          tape :=
            MixedParserStackRewriterDefaultedSourceRestBoundaryTape
              w sourceRestBits quoteRestBits stage } := by
  rcases
      assemblySkeletonDescription_run_stageInput_to_sourceRest_boundary_cells_withBase
        [none] w stage
        (List.append (sourceRestBits.map some)
          (none :: List.append (quoteRestBits.map some) [none])) with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [MixedParserStackRewriterDefaultedSourceStartTape,
    MixedParserStackRewriterDefaultedSourceRestBoundaryTape,
    assemblySourceRestFinishSourceBits, List.map_append,
    List.append_assoc, config] using hsteps

def assemblySourceRestFinishRawBoolSourceStartTargetTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells
    ((List.append
      (encodeCodeSymbolAsInput MachineCodeSymbol.header)
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          (assemblySourceRestFinishSourceBits
            w sourceRestBits stage).length)
        (preservingCellPassCellBits
          (assemblySourceRestFinishSourceBits
            w sourceRestBits stage)))).reverse.map some)
    ((assemblySourceRestFinishRawTailBits
      sourceRestBits stage).map some)

def assemblySourceRestFinishRawBoolReusableQuoteTargetTape
    (w sourceRestBits : Word Bool) (stage : Nat) : Tape Bool :=
  tapeAtCells
    ((List.append
      (encodeCodeSymbolAsInput MachineCodeSymbol.header)
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          (assemblySourceRestFinishSourceBits
            w sourceRestBits stage).length)
        (List.append
          (preservingCellPassCellBits
            (assemblySourceRestFinishRawTailPrefixBits w))
          (List.append
            (preservingCellPassCellBits
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage))
            (preservingCellPassCellBits sourceRestBits))))).reverse.map some)
    ((assemblySourceRestFinishRawTailBits
      sourceRestBits stage).map some)

theorem assemblySourceRestFinishRawBoolReusableQuoteTargetTape_cells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (assemblySourceRestFinishRawBoolReusableQuoteTargetTape
          w sourceRestBits stage) =
      List.append
        ((List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.header)
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (assemblySourceRestFinishSourceBits
                w sourceRestBits stage).length)
            (List.append
              (preservingCellPassCellBits
                (assemblySourceRestFinishRawTailPrefixBits w))
              (List.append
                (preservingCellPassCellBits
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    stage))
                (preservingCellPassCellBits sourceRestBits))))).map some)
        ((assemblySourceRestFinishRawTailBits
          sourceRestBits stage).map some) := by
  rcases SelectedProjectionTailProjector.stageNatBits_cons_cons stage with
    ⟨head, next, right, hstage⟩
  rw [assemblySourceRestFinishRawBoolReusableQuoteTargetTape,
    assemblySourceRestFinishRawTailBits, hstage]
  simp [tapeAtCells, Tape.cells, List.map_reverse, List.map_append]

theorem assemblySourceRestFinishRawBoolReusableQuoteTargetTape_defaultedCells
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (assemblySourceRestFinishRawBoolReusableQuoteTargetTape
            w sourceRestBits stage)) =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.header)
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            (assemblySourceRestFinishSourceBits
              w sourceRestBits stage).length)
          (List.append
            (preservingCellPassCellBits
              (assemblySourceRestFinishRawTailPrefixBits w))
            (List.append
              (preservingCellPassCellBits
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  stage))
              (List.append
                (preservingCellPassCellBits sourceRestBits)
                (assemblySourceRestFinishRawTailBits
                  sourceRestBits stage))))) := by
  rw [assemblySourceRestFinishRawBoolReusableQuoteTargetTape_cells]
  simp [List.map_append, List.map_map,
    optionBitDefaultFalse_map_some, List.append_assoc]

theorem assemblySourceRestFinishRawBoolSourceStartTargetTape_eq_reusableQuote
    (w sourceRestBits : Word Bool) (stage : Nat) :
    assemblySourceRestFinishRawBoolSourceStartTargetTape
        w sourceRestBits stage =
      assemblySourceRestFinishRawBoolReusableQuoteTargetTape
        w sourceRestBits stage := by
  rw [assemblySourceRestFinishRawBoolSourceStartTargetTape,
    assemblySourceRestFinishRawBoolReusableQuoteTargetTape]
  have hquote :
      preservingCellPassCellBits
          (assemblySourceRestFinishSourceBits
            w sourceRestBits stage) =
        List.append
          (preservingCellPassCellBits
            (assemblySourceRestFinishRawTailPrefixBits w))
          (List.append
            (preservingCellPassCellBits
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage))
            (preservingCellPassCellBits sourceRestBits)) := by
    rw [assemblySourceRestFinishSourceBits_eq_rawTailPrefix_append_rawTail,
      assemblySourceRestFinishRawTailBits,
      preservingCellPassCellBits_append_bool,
      preservingCellPassCellBits_append_bool]
  rw [hquote]

theorem MixedParserStackRewriterDefaultedSourceStartTape_cells
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (MixedParserStackRewriterDefaultedSourceStartTape
          w sourceRestBits quoteRestBits stage) =
      none ::
        List.append
          ((assemblySourceRestFinishSourceBits
            w sourceRestBits stage).map some)
          (none :: List.append (quoteRestBits.map some) [none]) := by
  rcases assemblySourceRestFinishSourceBits_headerPrefix
      w sourceRestBits stage with
    ⟨rest0, hbits0⟩
  simp [MixedParserStackRewriterDefaultedSourceStartTape,
    tapeAtCells, Tape.cells, hbits0]

theorem MixedParserStackRewriterDefaultedSourceStartTape_defaultedCells
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (MixedParserStackRewriterDefaultedSourceStartTape
            w sourceRestBits quoteRestBits stage)) =
      false ::
        List.append
          (assemblySourceRestFinishSourceBits
            w sourceRestBits stage)
          (false :: List.append quoteRestBits [false]) := by
  rw [MixedParserStackRewriterDefaultedSourceStartTape_cells]
  simp [List.map_append, List.map_map,
    optionBitDefaultFalse, optionBitDefaultFalse_map_some]

theorem MixedParserStackRewriterWholeSourceTargetTape_eq_rawBoolTargetTape
    (w sourceRestBits : Word Bool) (stage : Nat) :
    MixedParserStackRewriterWholeSourceTargetTape
        (MixedParserStackRewriterTrueSourceCells
          w sourceRestBits stage)
        (assemblySourceRestFinishRawTailBits sourceRestBits stage) =
      assemblySourceRestFinishRawBoolSourceStartTargetTape
        w sourceRestBits stage := by
  rw [MixedParserStackRewriterWholeSourceTargetTape_eq_sourceBits,
    assemblySourceRestFinishRawBoolSourceStartTargetTape]

theorem MixedParserStackRewriterDefaultedRightBoundaryTape_eq_movedLeft_sourceBits
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    MixedParserStackRewriterDefaultedRightBoundaryTape
        w sourceRestBits quoteRestBits stage =
      Tape.move Direction.left
        (tapeAtCells
          (List.append
            ((assemblySourceRestFinishSourceBits
              w sourceRestBits stage).reverse.map some)
            [none])
          (none :: List.append (quoteRestBits.map some) [none])) := by
  rw [MixedParserStackRewriterDefaultedRightBoundaryTape]
  have hrev := congrArg List.reverse
    (MixedParserStackRewriterDefaultedSourceCells_eq_sourceBits_map_some
      w sourceRestBits stage)
  have hleft :
      List.append
          ((assemblySourceRestFinishRightPayloadBits
            w sourceRestBits stage).reverse.map some)
          (some false ::
            List.append
              (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
              [none]) =
        List.append
          ((assemblySourceRestFinishSourceBits
            w sourceRestBits stage).reverse.map some)
          [none] := by
    simpa [MixedParserStackRewriterDefaultedSourceCells,
      List.reverse_append, List.map_reverse, List.append_assoc]
      using congrArg (fun cells => List.append cells [none]) hrev
  rw [hleft]

theorem
    rightEdgeRewindDescription_haltsFrom_defaultedRightBoundaryTape
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    CommonGround.FiniteTransducers.rightEdgeRewindDescription.HaltsFromTape
      (MixedParserStackRewriterDefaultedRightBoundaryTape
        w sourceRestBits quoteRestBits stage)
      (MixedParserStackRewriterDefaultedSourceStartTape
        w sourceRestBits quoteRestBits stage) := by
  rcases assemblySourceRestFinishSourceBits_headerPrefix
      w sourceRestBits stage with
    ⟨rest0, hbits0⟩
  rcases exists_reverse_append_singleton_of_cons false
      (false :: false :: true :: rest0) with
    ⟨leftStack, current, hsplit⟩
  have hbits :
      assemblySourceRestFinishSourceBits w sourceRestBits stage =
        List.append leftStack.reverse [current] := by
    rw [hbits0]
    exact hsplit
  have hrew :=
    CommonGround.FiniteTransducers.rightEdgeRewindDescription_haltsFrom_lastBitBoundary
      leftStack current (List.append (quoteRestBits.map some) [none])
  simpa [MixedParserStackRewriterDefaultedRightBoundaryTape_eq_movedLeft_sourceBits,
    MixedParserStackRewriterDefaultedSourceStartTape,
    CommonGround.FiniteTransducers.rightEdgeRewindTargetTape,
    CommonGround.FiniteTransducers.tapeAtCells,
    DovetailInitialLayoutInitializer.tapeAtCells,
    hbits, List.reverse_append, List.map_append, List.map_reverse,
    List.append_assoc, Tape.move, Tape.moveLeft]
    using hrew

theorem MixedParserStackRewriterDefaultedSourceStartTape_move_left_move_right
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (MixedParserStackRewriterDefaultedSourceStartTape
            w sourceRestBits quoteRestBits stage)) =
      MixedParserStackRewriterDefaultedSourceStartTape
        w sourceRestBits quoteRestBits stage := by
  rcases assemblySourceRestFinishSourceBits_headerPrefix
      w sourceRestBits stage with
    ⟨rest0, hbits0⟩
  simp [MixedParserStackRewriterDefaultedSourceStartTape, hbits0,
    tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

def mixedParserStackScanRightToStructuralBlankDescription :
    MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 (some false) (some false) Direction.right 0
    , transition 0 (some true) (some true) Direction.right 0
    , transition 0 none none Direction.left 1
    ]

private abbrev MPSSR :=
  mixedParserStackScanRightToStructuralBlankDescription

theorem mixedParserStackScanRightToStructuralBlankDescription_wellFormed :
    MPSSR.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := MPSSR.transitions)
      (stateCount := MPSSR.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := MPSSR.transitions)
      (by decide)

theorem
    mixedParserStackScanRightToStructuralBlankDescription_haltTransitionFree :
    MPSSR.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := MPSSR.transitions)
    (state := MPSSR.halt)
    (by decide)

theorem
    mixedParserStackScanRightToStructuralBlankDescription_subroutineReady :
    MPSSR.SubroutineReady :=
  ⟨mixedParserStackScanRightToStructuralBlankDescription_wellFormed,
    mixedParserStackScanRightToStructuralBlankDescription_haltTransitionFree⟩

theorem mixedParserStackScanRightToStructuralBlankDescription_run
    (input : Word Bool) (left padding : List (Option Bool)) :
    MPSSR.runConfig (input.length + 1)
        { state := MPSSR.start
          tape :=
            tapeAtCells left
              (List.append (input.map some) (none :: padding)) } =
        { state := MPSSR.halt
          tape :=
            Tape.move Direction.left
              (tapeAtCells
                (List.append (input.reverse.map some) left)
                (none :: padding)) } := by
  induction input generalizing left with
  | nil =>
      cases padding <;>
        simp [MPSSR, mixedParserStackScanRightToStructuralBlankDescription,
          runConfig, stepConfig, lookupTransition, Matches, transition,
          tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveLeft]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          MPSSR.runConfig 1
              { state := MPSSR.start
                tape :=
                  tapeAtCells left
                    (List.append ((bit :: rest).map some)
                      (none :: padding)) } =
            { state := MPSSR.start
              tape :=
                tapeAtCells (some bit :: left)
                  (List.append (rest.map some) (none :: padding)) } := by
        cases bit <;> cases rest <;>
          simp [MPSSR, mixedParserStackScanRightToStructuralBlankDescription,
            runConfig, stepConfig, lookupTransition, Matches, transition,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight]
      rw [hstep]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

theorem
    mixedParserStackScanRightToStructuralBlankDescription_haltsFrom_defaultedInternalMarkerTape
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    MPSSR.HaltsFromTape
      (MixedParserStackRewriterDefaultedInternalMarkerTape
        w sourceRestBits quoteRestBits stage)
      (MixedParserStackRewriterDefaultedRightBoundaryTape
        w sourceRestBits quoteRestBits stage) := by
  refine
    ⟨(assemblySourceRestFinishRightPayloadBits
        w sourceRestBits stage).length + 1, ?_⟩
  have hrun :=
    mixedParserStackScanRightToStructuralBlankDescription_run
      (assemblySourceRestFinishRightPayloadBits
        w sourceRestBits stage)
      (some false ::
        List.append
          (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
          [none])
      (List.append (quoteRestBits.map some) [none])
  constructor
  · simpa [MixedParserStackRewriterDefaultedInternalMarkerTape,
      MixedParserStackRewriterDefaultedRightBoundaryTape]
      using congrArg Configuration.state hrun
  · simpa [MixedParserStackRewriterDefaultedInternalMarkerTape,
      MixedParserStackRewriterDefaultedRightBoundaryTape,
      List.append_assoc]
      using congrArg Configuration.tape hrun

theorem MixedParserStackRewriterDefaultedRightBoundaryTape_move_left_move_right
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (MixedParserStackRewriterDefaultedRightBoundaryTape
            w sourceRestBits quoteRestBits stage)) =
      MixedParserStackRewriterDefaultedRightBoundaryTape
        w sourceRestBits quoteRestBits stage := by
  rw [MixedParserStackRewriterDefaultedRightBoundaryTape]
  cases hpayload :
      assemblySourceRestFinishRightPayloadBits
        w sourceRestBits stage with
  | nil =>
      exact
        False.elim
          ((assemblySourceRestFinishRightPayloadBits_ne_nil
              w sourceRestBits stage) hpayload)
  | cons bit rest =>
      exact
        Tape.move_left_move_right_eq_self_of_right_cons
          (Tape.move Direction.left
            (tapeAtCells
              (List.append
                ((bit :: rest).reverse.map some)
                (some false ::
                  List.append
                    (List.reverse
                      assemblySourceRestFinishParserMarkerLeftCells)
                    [none]))
              (none :: List.append (quoteRestBits.map some) [none])))
          (cell := none)
          (right := List.append (quoteRestBits.map some) [none])
          (by
            have hleft_ne :
                List.append ((bit :: rest).reverse.map some)
                    (some false ::
                      List.append
                        (List.reverse
                          assemblySourceRestFinishParserMarkerLeftCells)
                        [none]) ≠ [] := by
              cases rest <;>
                simp [List.reverse_cons, List.map_append]
            cases hleft :
                List.append ((bit :: rest).reverse.map some)
                  (some false ::
                    List.append
                      (List.reverse
                        assemblySourceRestFinishParserMarkerLeftCells)
                      [none]) with
            | nil =>
                exact False.elim (hleft_ne hleft)
            | cons cell cells =>
                simp [tapeAtCells, Tape.move, Tape.moveLeft])

theorem MixedParserStackRewriterDefaultedRightBoundaryTape_cells
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    Tape.cells
        (MixedParserStackRewriterDefaultedRightBoundaryTape
          w sourceRestBits quoteRestBits stage) =
      none ::
        List.append
          (MixedParserStackRewriterDefaultedSourceCells
            w sourceRestBits stage)
          (none ::
            List.append (quoteRestBits.map some) [none]) := by
  rw [MixedParserStackRewriterDefaultedRightBoundaryTape,
    MixedParserStackRewriterDefaultedSourceCells]
  cases hpayload :
      assemblySourceRestFinishRightPayloadBits
        w sourceRestBits stage with
  | nil =>
      exact
        False.elim
          ((assemblySourceRestFinishRightPayloadBits_ne_nil
              w sourceRestBits stage) hpayload)
  | cons bit rest =>
      have hleft_ne :
          List.append ((bit :: rest).reverse.map some)
              (some false ::
                List.append
                  (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
                  [none]) ≠ [] := by
        cases rest <;>
          simp [List.reverse_cons, List.map_append]
      rw [tapeAtCells_move_left_none_cons_cells_of_left_ne_nil
        (List.append ((bit :: rest).reverse.map some)
          (some false ::
            List.append
              (List.reverse assemblySourceRestFinishParserMarkerLeftCells)
              [none]))
        (List.append (quoteRestBits.map some) [none])
        hleft_ne]
      simp [List.reverse_append, List.map_reverse, List.append_assoc]

theorem MixedParserStackRewriterDefaultedRightBoundaryTape_defaultedCells
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (Tape.cells
          (MixedParserStackRewriterDefaultedRightBoundaryTape
            w sourceRestBits quoteRestBits stage)) =
      false ::
        List.append
          (assemblySourceRestFinishSourceBits
            w sourceRestBits stage)
          (false :: List.append quoteRestBits [false]) := by
  rw [MixedParserStackRewriterDefaultedRightBoundaryTape_cells]
  simp [List.map_append, List.map_map,
    MixedParserStackRewriterDefaultedSourceCells_defaultBits,
    optionBitDefaultFalse, optionBitDefaultFalse_map_some]

theorem MixedParserStackRewriterSourceTape_eq_seekLeftBoundarySource
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat)
    (scanRev : Word Bool) (current : Bool)
    (hpayload :
      assemblySourceRestFinishRightPayloadBits
        w sourceRestBits stage =
          List.append scanRev.reverse [current]) :
    MixedParserStackRewriterSourceTape
        (assemblySourceRestFinishParserPrefixCells w)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage)
        sourceRestBits
        quoteRestBits =
      tapeAtCells
        (List.append (scanRev.map some)
          (none ::
            List.reverse assemblySourceRestFinishParserMarkerLeftCells))
        (some current ::
          none :: List.append (quoteRestBits.map some) [none]) := by
  rw [MixedParserStackRewriterSourceTape,
    scanLeftToBlankLeftHaltTape]
  rw [assemblySourceRestFinishParserPrefixCells_eq_marker_split]
  rw [assemblySourceRestFinishParserMarkerRightCells_eq_bits]
  have hpayloadCells :
      List.append (sourceRestBits.reverse.map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).reverse.map some)
            (List.append
              ((assemblySourceRestFinishParserMarkerRightBits w).reverse.map
                some)
              (none ::
                List.reverse assemblySourceRestFinishParserMarkerLeftCells))) =
        some current ::
          List.append (scanRev.map some)
            (none ::
              List.reverse assemblySourceRestFinishParserMarkerLeftCells) := by
    have hrev :=
      congrArg (fun bits => bits.reverse.map some) hpayload
    simpa [assemblySourceRestFinishRightPayloadBits, List.reverse_append,
      List.append_assoc] using congrArg
        (fun cells =>
          List.append cells
            (none :: List.reverse
              assemblySourceRestFinishParserMarkerLeftCells))
        hrev
  have hpayloadCells' :
      (List.map some sourceRestBits).reverse ++
          ((List.map some
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage)).reverse ++
            ((List.map some
                (assemblySourceRestFinishParserMarkerRightBits w)).reverse ++
              none ::
                assemblySourceRestFinishParserMarkerLeftCells.reverse)) =
        some current ::
          List.append (scanRev.map some)
            (none ::
              List.reverse assemblySourceRestFinishParserMarkerLeftCells) := by
    simpa [List.map_reverse] using hpayloadCells
  simp [List.reverse_append, List.append_assoc, hpayloadCells',
    tapeAtCells, Tape.move, Tape.moveLeft]

theorem MixedParserStackRewriterTrueLeftBoundaryTape_eq_payloadSplit
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat)
    (scanRev : Word Bool) (current : Bool)
    (hpayload :
      assemblySourceRestFinishRightPayloadBits
        w sourceRestBits stage =
          List.append scanRev.reverse [current]) :
    MixedParserStackRewriterTrueLeftBoundaryTape
        w sourceRestBits quoteRestBits stage =
      tapeAtCells []
        (none ::
          List.append assemblySourceRestFinishParserMarkerLeftCells
            (none ::
              List.append (scanRev.reverse.map some)
                (some current ::
                  none :: List.append (quoteRestBits.map some) [none]))) := by
  rw [MixedParserStackRewriterTrueLeftBoundaryTape]
  rw [hpayload]
  simp [List.map_append, List.append_assoc]

theorem mixedParserStackSeekLeftBoundaryDescription_haltsFrom_sourceTape
    (w sourceRestBits quoteRestBits : Word Bool) (stage : Nat) :
    MPSLB.HaltsFromTape
      (MixedParserStackRewriterSourceTape
        (assemblySourceRestFinishParserPrefixCells w)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage)
        sourceRestBits
        quoteRestBits)
      (MixedParserStackRewriterTrueLeftBoundaryTape
        w sourceRestBits quoteRestBits stage) := by
  rcases exists_reverse_append_singleton_of_nonempty
      (assemblySourceRestFinishRightPayloadBits
        w sourceRestBits stage)
      (assemblySourceRestFinishRightPayloadBits_ne_nil
        w sourceRestBits stage) with
    ⟨scanRev, current, hpayload⟩
  refine ⟨scanRev.length + 7, ?_⟩
  have hrun :=
    mixedParserStackSeekLeftBoundaryDescription_run_payloadToLeftBoundary
      scanRev current
      (none :: List.append (quoteRestBits.map some) [none])
  have hsource :=
    MixedParserStackRewriterSourceTape_eq_seekLeftBoundarySource
      w sourceRestBits quoteRestBits stage scanRev current hpayload
  have htarget :=
    MixedParserStackRewriterTrueLeftBoundaryTape_eq_payloadSplit
      w sourceRestBits quoteRestBits stage scanRev current hpayload
  constructor
  · simpa [hsource] using congrArg Configuration.state hrun
  · simpa [hsource, htarget] using congrArg Configuration.tape hrun

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

theorem MixedParserStackRewriterTargetTape_eq_targetTape_computed
    (w sourceRestBits : Word Bool) (stage : Nat) :
    MixedParserStackRewriterTargetTape
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
        (preservingCellPassCellBits sourceRestBits) =
      assemblySourceRestFinishTargetTape w sourceRestBits stage := by
  rw [MixedParserStackRewriterPrefixQuote_eq_assemblyQuotedPrefix,
    MixedParserStackRewriterLengthHeader_eq_assemblyLengthHeader]
  exact MixedParserStackRewriterTargetTape_eq_targetTape
    w sourceRestBits stage

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
