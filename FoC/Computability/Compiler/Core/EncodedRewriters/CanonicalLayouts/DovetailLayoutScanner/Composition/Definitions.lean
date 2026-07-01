import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.BoolWord

set_option doc.verso true

/-!
# Composed dovetail-layout scanner fields

This module assembles the primitive suffix-aware scanner components into tape
and configuration field scanners.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace CanonicalLayouts
namespace DovetailLayoutScanner

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner
open CommonGround.SeqComposition

/-!
## Composed tape and configuration field scanners

Run theorems keep explicit base-left contexts so the recognizer can be chained
field by field.
-/

def TapeSuffixScannerDescription : MachineDescription :=
  seqSubroutine
    CellListSuffixScannerDescription
    (seqSubroutine
      CellSuffixScannerDescription
      CellListSuffixScannerDescription
      Direction.right)
    Direction.right

theorem tapeSuffixScannerDescription_subroutineReady :
    TapeSuffixScannerDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    cellListSuffixScannerDescription_subroutineReady
    (seqSubroutine_subroutineReady
      cellSuffixScannerDescription_subroutineReady
      cellListSuffixScannerDescription_subroutineReady)

def ConfigurationSuffixScannerDescription : MachineDescription :=
  seqSubroutine
    DovetailStagePrefix.NonemptyNatSuffixScannerDescription
    TapeSuffixScannerDescription
    Direction.right

theorem configurationSuffixScannerDescription_subroutineReady :
    ConfigurationSuffixScannerDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
    tapeSuffixScannerDescription_subroutineReady

def FinalHitFlagsScannerDescription : MachineDescription :=
  seqSubroutine
    BoolSuffixScannerDescription
    BoolFinalScannerDescription
    Direction.right

theorem finalHitFlagsScannerDescription_subroutineReady :
    FinalHitFlagsScannerDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    boolSuffixScannerDescription_subroutineReady
    boolFinalScannerDescription_subroutineReady

/-!
## Checked complete-layout bookends

The final Boolean scanner must read the physical blank at the end of the
input.  To recover a left-boundary handoff without changing the encoded word,
the checked complete-layout scanner temporarily turns the first transition bit
into an internal blank marker, validates the rest of the layout, scans back to
that marker, restores the bit, and halts on the second input bit.  The visited
right blank remains in the tape window, which is the checked parser shape.
-/

def MarkFirstTransitionBitDescription : MachineDescription where
  stateCount := 10
  start := 0
  halt := 9
  transitions :=
    [ writeMove 0 (some false) none Direction.right 1
    , keepMove 1 (some false) Direction.left 9
    ]

theorem markFirstTransitionBitDescription_wellFormed :
    MarkFirstTransitionBitDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := MarkFirstTransitionBitDescription.transitions)
      (stateCount := MarkFirstTransitionBitDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := MarkFirstTransitionBitDescription.transitions)
      (by decide)

theorem markFirstTransitionBitDescription_haltTransitionFree :
    MarkFirstTransitionBitDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := MarkFirstTransitionBitDescription.transitions)
    (state := MarkFirstTransitionBitDescription.halt)
    (by decide)

theorem markFirstTransitionBitDescription_subroutineReady :
    MarkFirstTransitionBitDescription.SubroutineReady :=
  ⟨markFirstTransitionBitDescription_wellFormed,
    markFirstTransitionBitDescription_haltTransitionFree⟩

theorem run_markFirstTransitionBit_raw
    (tail : Word Bool) :
    MarkFirstTransitionBitDescription.runConfig 2
        (config 0 []
          (some false :: some false :: tail.map some)) =
      config MarkFirstTransitionBitDescription.halt []
        (none :: some false :: tail.map some) := by
  cases tail <;>
    simp [MarkFirstTransitionBitDescription, config, tapeAtCells,
      keepMove, writeMove, runConfig,
      stepConfig, lookupTransition,
      Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      Tape.moveRight]

def TransitionRemainderPrefixScannerDescription : MachineDescription where
  stateCount := 100
  start := 30
  halt := 99
  transitions :=
    [ keepMove 30 (some false) Direction.right 31
    , keepMove 31 (some false) Direction.right 32
    , keepMove 32 (some true) Direction.right 40
    , keepMove 40 (some false) Direction.left 99
    , keepMove 40 (some true) Direction.left 99
    ]

theorem transitionRemainderPrefixScannerDescription_wellFormed :
    TransitionRemainderPrefixScannerDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := TransitionRemainderPrefixScannerDescription.transitions)
      (stateCount :=
        TransitionRemainderPrefixScannerDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := TransitionRemainderPrefixScannerDescription.transitions)
      (by decide)

theorem transitionRemainderPrefixScannerDescription_haltTransitionFree :
    TransitionRemainderPrefixScannerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := TransitionRemainderPrefixScannerDescription.transitions)
    (state := TransitionRemainderPrefixScannerDescription.halt)
    (by decide)

theorem transitionRemainderPrefixScannerDescription_subroutineReady :
    TransitionRemainderPrefixScannerDescription.SubroutineReady :=
  ⟨transitionRemainderPrefixScannerDescription_wellFormed,
    transitionRemainderPrefixScannerDescription_haltTransitionFree⟩

def transitionRemainderBits : Word Bool :=
  [false, false, true]

def transitionRemainderHandoffConfigWithBase
    (baseLeft : List (Option Bool)) (suffixBits : Word Bool) :
    Configuration :=
  { state := TransitionRemainderPrefixScannerDescription.halt
    tape :=
      Tape.move Direction.left
        (tapeAtCells
          (List.append (transitionRemainderBits.reverse.map some)
            baseLeft)
          (suffixBits.map some)) }

def transitionRemainderHandoffConfigWithBaseAndRight
    (baseLeft : List (Option Bool)) (suffixBits : Word Bool)
    (rightPadding : List (Option Bool)) : Configuration :=
  { state := TransitionRemainderPrefixScannerDescription.halt
    tape :=
      Tape.move Direction.left
        (tapeAtCells
          (List.append (transitionRemainderBits.reverse.map some)
            baseLeft)
          (List.append (suffixBits.map some) rightPadding)) }

theorem run_transitionRemainderPrefix_raw_to_handoff_withBase
    (baseLeft : List (Option Bool)) (b : Bool)
    (suffixTail : Word Bool) :
    exists steps : Nat,
      TransitionRemainderPrefixScannerDescription.runConfig steps
          (config 30 baseLeft
            (some false :: some false :: some true ::
              some b :: suffixTail.map some)) =
        transitionRemainderHandoffConfigWithBase baseLeft
          (b :: suffixTail) := by
  refine ⟨4, ?_⟩
  cases b <;> cases suffixTail <;>
    simp [TransitionRemainderPrefixScannerDescription,
      transitionRemainderHandoffConfigWithBase,
      transitionRemainderBits, config, tapeAtCells, keepMove,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

theorem run_transitionRemainderPrefix_raw_to_handoff_withBaseAndRight
    (baseLeft : List (Option Bool)) (b : Bool)
    (suffixTail : Word Bool) (rightPadding : List (Option Bool)) :
    exists steps : Nat,
      TransitionRemainderPrefixScannerDescription.runConfig steps
          (config 30 baseLeft
            (some false :: some false :: some true ::
              some b :: List.append (suffixTail.map some) rightPadding)) =
        transitionRemainderHandoffConfigWithBaseAndRight baseLeft
          (b :: suffixTail) rightPadding := by
  refine ⟨4, ?_⟩
  cases b <;>
    simp [TransitionRemainderPrefixScannerDescription,
      transitionRemainderHandoffConfigWithBaseAndRight,
      transitionRemainderBits, config, tapeAtCells, keepMove,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

theorem transitionRemainderHandoffConfigWithBase_move_right
    (baseLeft : List (Option Bool)) (b : Bool)
    (suffixTail : Word Bool) :
    Tape.move Direction.right
        (transitionRemainderHandoffConfigWithBase baseLeft
          (b :: suffixTail)).tape =
      tapeAtCells
        (List.append (transitionRemainderBits.reverse.map some)
          baseLeft)
        ((b :: suffixTail).map some) := by
  unfold transitionRemainderHandoffConfigWithBase transitionRemainderBits
  simpa [List.append_assoc] using
    FoC.Computability.EncodedRewriters.CanonicalLayouts.DovetailStagePrefix.tapeAtCells_move_right_move_left_cons
      (some true)
      (some false :: some false :: baseLeft)
      (some b) (suffixTail.map some)

theorem transitionRemainderHandoffConfigWithBaseAndRight_move_right
    (baseLeft : List (Option Bool)) (b : Bool)
    (suffixTail : Word Bool) (rightPadding : List (Option Bool)) :
    Tape.move Direction.right
        (transitionRemainderHandoffConfigWithBaseAndRight baseLeft
          (b :: suffixTail) rightPadding).tape =
      tapeAtCells
        (List.append (transitionRemainderBits.reverse.map some)
          baseLeft)
        (List.append ((b :: suffixTail).map some) rightPadding) := by
  unfold transitionRemainderHandoffConfigWithBaseAndRight transitionRemainderBits
  simpa [List.append_assoc] using
    FoC.Computability.EncodedRewriters.CanonicalLayouts.DovetailStagePrefix.tapeAtCells_move_right_move_left_cons
      (some true)
      (some false :: some false :: baseLeft)
      (some b) (List.append (suffixTail.map some) rightPadding)

def ReturnToFirstMarkerDescription : MachineDescription where
  stateCount := 20
  start := 0
  halt := 19
  transitions :=
    [ keepMove 0 none Direction.left 1
    , keepMove 1 (some false) Direction.left 1
    , keepMove 1 (some true) Direction.left 1
    , writeMove 1 none (some false) Direction.right 19
    ]

theorem returnToFirstMarkerDescription_wellFormed :
    ReturnToFirstMarkerDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := ReturnToFirstMarkerDescription.transitions)
      (stateCount := ReturnToFirstMarkerDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := ReturnToFirstMarkerDescription.transitions)
      (by decide)

theorem returnToFirstMarkerDescription_haltTransitionFree :
    ReturnToFirstMarkerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := ReturnToFirstMarkerDescription.transitions)
    (state := ReturnToFirstMarkerDescription.halt)
    (by decide)

theorem returnToFirstMarkerDescription_subroutineReady :
    ReturnToFirstMarkerDescription.SubroutineReady :=
  ⟨returnToFirstMarkerDescription_wellFormed,
    returnToFirstMarkerDescription_haltTransitionFree⟩

def restoredCheckedHandoffTapeFromTail (tail : Word Bool) : Tape Bool :=
  Tape.move Direction.right
    { left := []
      head := some false
      right := List.append (tail.map some) [none] }

def returnToFirstMarkerScanConfig
    (remainingRev scanned : Word Bool) :
    Configuration :=
  match remainingRev with
  | [] =>
      config 1 [] (none :: List.append (scanned.map some) [none])
  | bit :: rest =>
      config 1 (List.append (rest.map some) [none])
        (some bit :: List.append (scanned.map some) [none])

theorem run_returnToFirstMarker_scan
    (remainingRev scanned : Word Bool) :
    ReturnToFirstMarkerDescription.runConfig
        (remainingRev.length + 1)
        (returnToFirstMarkerScanConfig remainingRev scanned) =
      { state := ReturnToFirstMarkerDescription.halt
        tape :=
          restoredCheckedHandoffTapeFromTail
            (List.append remainingRev.reverse scanned) } := by
  induction remainingRev generalizing scanned with
  | nil =>
      simp [returnToFirstMarkerScanConfig,
        restoredCheckedHandoffTapeFromTail,
        ReturnToFirstMarkerDescription, config, tapeAtCells,
        keepMove, writeMove, runConfig,
        stepConfig,
        lookupTransition, Matches,
        transition, Tape.read, Tape.write, Tape.move,
        Tape.moveRight]
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        omega]
      have hstep :
          ReturnToFirstMarkerDescription.runConfig 1
              (returnToFirstMarkerScanConfig (bit :: rest) scanned) =
            returnToFirstMarkerScanConfig rest (bit :: scanned) := by
        cases bit <;> cases rest <;>
          simp [returnToFirstMarkerScanConfig,
            ReturnToFirstMarkerDescription, config, tapeAtCells,
            keepMove, writeMove, runConfig,
            stepConfig,
            lookupTransition, Matches,
            transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
      rw [runConfig_add]
      rw [hstep]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (bit :: scanned)

theorem run_returnToFirstMarker_from_reversedBits
    (prefixRev : Word Bool) :
    ReturnToFirstMarkerDescription.runConfig
        (prefixRev.length + 2)
        (config 0 (List.append (prefixRev.map some) [none]) [none]) =
      { state := ReturnToFirstMarkerDescription.halt
        tape :=
          restoredCheckedHandoffTapeFromTail prefixRev.reverse } := by
  rw [show prefixRev.length + 2 = 1 + (prefixRev.length + 1) by omega]
  rw [runConfig_add]
  cases prefixRev with
  | nil =>
      simp [ReturnToFirstMarkerDescription, config, tapeAtCells,
        keepMove, writeMove, runConfig,
        stepConfig,
        lookupTransition, Matches,
        transition, Tape.read, Tape.write, Tape.move,
        Tape.moveLeft, Tape.moveRight,
        restoredCheckedHandoffTapeFromTail]
  | cons bit rest =>
      have hstep :
          ReturnToFirstMarkerDescription.runConfig 1
              (config 0
                (List.append ((bit :: rest).map some) [none]) [none]) =
            returnToFirstMarkerScanConfig (bit :: rest) [] := by
        cases bit <;>
          simp [returnToFirstMarkerScanConfig,
            ReturnToFirstMarkerDescription, config, tapeAtCells,
            keepMove, writeMove, runConfig,
            stepConfig,
            lookupTransition, Matches,
            transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [List.append_assoc] using
        run_returnToFirstMarker_scan (bit :: rest) []

def RejectConfigAndFinalFlagsScannerDescription : MachineDescription :=
  seqSubroutine
    ConfigurationSuffixScannerDescription
    FinalHitFlagsScannerDescription
    Direction.right

theorem rejectConfigAndFinalFlagsScannerDescription_subroutineReady :
    RejectConfigAndFinalFlagsScannerDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    configurationSuffixScannerDescription_subroutineReady
    finalHitFlagsScannerDescription_subroutineReady

def ConfigurationsAndFinalFlagsScannerDescription : MachineDescription :=
  seqSubroutine
    ConfigurationSuffixScannerDescription
    RejectConfigAndFinalFlagsScannerDescription
    Direction.right

theorem configurationsAndFinalFlagsScannerDescription_subroutineReady :
    ConfigurationsAndFinalFlagsScannerDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    configurationSuffixScannerDescription_subroutineReady
    rejectConfigAndFinalFlagsScannerDescription_subroutineReady

def StageConfigurationsAndFinalFlagsScannerDescription :
    MachineDescription :=
  seqSubroutine
    DovetailStagePrefix.NonemptyNatSuffixScannerDescription
    ConfigurationsAndFinalFlagsScannerDescription
    Direction.right

theorem stageConfigurationsAndFinalFlagsScannerDescription_subroutineReady :
    StageConfigurationsAndFinalFlagsScannerDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
    configurationsAndFinalFlagsScannerDescription_subroutineReady

def InputStageConfigurationsAndFinalFlagsScannerDescription :
    MachineDescription :=
  seqSubroutine
    BoolWordSuffixScannerDescription
    StageConfigurationsAndFinalFlagsScannerDescription
    Direction.right

theorem inputStageConfigurationsAndFinalFlagsScannerDescription_subroutineReady :
    InputStageConfigurationsAndFinalFlagsScannerDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    boolWordSuffixScannerDescription_subroutineReady
    stageConfigurationsAndFinalFlagsScannerDescription_subroutineReady

def MarkedDovetailLayoutBodyScannerDescription : MachineDescription :=
  seqSubroutine
    TransitionRemainderPrefixScannerDescription
    InputStageConfigurationsAndFinalFlagsScannerDescription
    Direction.right

theorem markedDovetailLayoutBodyScannerDescription_subroutineReady :
    MarkedDovetailLayoutBodyScannerDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    transitionRemainderPrefixScannerDescription_subroutineReady
    inputStageConfigurationsAndFinalFlagsScannerDescription_subroutineReady

def CheckedDovetailLayoutScannerDescription : MachineDescription :=
  seqSubroutine
    MarkFirstTransitionBitDescription
    (seqSubroutine
      MarkedDovetailLayoutBodyScannerDescription
      ReturnToFirstMarkerDescription
      Direction.right)
    Direction.right

theorem checkedDovetailLayoutScannerDescription_subroutineReady :
    CheckedDovetailLayoutScannerDescription.SubroutineReady :=
  seqSubroutine_subroutineReady
    markFirstTransitionBitDescription_subroutineReady
    (seqSubroutine_subroutineReady
      markedDovetailLayoutBodyScannerDescription_subroutineReady
      returnToFirstMarkerDescription_subroutineReady)

def configurationRestoredLeftWithBase
    (cfg : Configuration)
    (baseLeft : List (Option Bool)) : List (Option Bool) :=
  cellListCanonicalRestoredLeftWithBase cfg.tape.right
    (List.append ((cellCodeBits cfg.tape.head).reverse.map some)
      (cellListCanonicalRestoredLeftWithBase cfg.tape.left
        (List.append ((stageNatBits cfg.state).reverse.map some)
          baseLeft)))

def finalHitFlagsRestoredLeftWithBase
    (acceptHit rejectHit : Bool)
    (baseLeft : List (Option Bool)) : List (Option Bool) :=
  List.append ((cellCodeBits (some rejectHit)).reverse.map some)
    (List.append ((cellCodeBits (some acceptHit)).reverse.map some)
      baseLeft)

theorem configurationFieldBits_cons_false
    (cfg : Configuration) (suffixBits : Word Bool) :
    exists tail : Word Bool,
      configurationFieldBits cfg suffixBits = false :: tail := by
  rcases stageNatBits_cons_false cfg.state with ⟨tail, htail⟩
  refine ⟨List.append tail (tapeFieldBits cfg.tape suffixBits), ?_⟩
  simp [configurationFieldBits, htail]

def cellListCanonicalLengthPrefixBitsRev : Nat -> Word Bool
  | 0 => []
  | n + 1 =>
      List.append tickBits.reverse
        (cellListCanonicalLengthPrefixBitsRev n)

theorem cellListCanonicalLengthPrefixBitsRev_map_some
    (n : Nat) :
    (cellListCanonicalLengthPrefixBitsRev n).map some =
      cellListCanonicalLengthPrefixRev n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [cellListCanonicalLengthPrefixBitsRev,
        cellListCanonicalLengthPrefixRev, List.map_append, ih]

def cellListCanonicalRestoredBitsRev
    (cells : List (Option Bool)) : Word Bool :=
  List.append (cellsCodeBits cells).reverse
    (List.append doneBits.reverse
      (cellListCanonicalLengthPrefixBitsRev cells.length))

theorem cellListCanonicalRestoredBitsRev_map_some_withBase
    (cells baseLeft : List (Option Bool)) :
    List.append ((cellListCanonicalRestoredBitsRev cells).map some)
        baseLeft =
      cellListCanonicalRestoredLeftWithBase cells baseLeft := by
  simp [cellListCanonicalRestoredBitsRev,
    cellListCanonicalRestoredLeftWithBase,
    cellListCanonicalFinishStartLeftWithBase,
    cellListCanonicalLengthPrefixBitsRev_map_some,
    List.map_append, List.map_reverse, List.append_assoc]

theorem cellListCanonicalFinishStartLeftWithBase_append_base
    (cells baseLeft extra : List (Option Bool)) :
    cellListCanonicalFinishStartLeftWithBase
        cells (List.append baseLeft extra) =
      List.append
        (cellListCanonicalFinishStartLeftWithBase cells baseLeft)
        extra := by
  unfold cellListCanonicalFinishStartLeftWithBase
  simp [List.append_assoc]

theorem cellListCanonicalRestoredLeftWithBase_append_base
    (cells baseLeft extra : List (Option Bool)) :
    cellListCanonicalRestoredLeftWithBase
        cells (List.append baseLeft extra) =
      List.append
        (cellListCanonicalRestoredLeftWithBase cells baseLeft)
        extra := by
  unfold cellListCanonicalRestoredLeftWithBase
  rw [cellListCanonicalFinishStartLeftWithBase_append_base]
  simp [List.append_assoc]

theorem cellListFieldBits_append_nil
    (cells : List (Option Bool)) (suffixBits : Word Bool) :
    List.append (cellListFieldBits cells []) suffixBits =
      cellListFieldBits cells suffixBits := by
  simp [cellListFieldBits, List.append_assoc]

theorem cellFieldBits_append_nil
    (cell : Option Bool) (suffixBits : Word Bool) :
    List.append (cellFieldBits cell []) suffixBits =
      cellFieldBits cell suffixBits := by
  simp [cellFieldBits]

theorem tapeFieldBits_append_nil
    (T : Tape Bool) (suffixBits : Word Bool) :
    List.append (tapeFieldBits T []) suffixBits =
      tapeFieldBits T suffixBits := by
  simp [tapeFieldBits, cellFieldBits, cellListFieldBits,
    List.append_assoc]

theorem configurationFieldBits_append_nil
    (cfg : Configuration) (suffixBits : Word Bool) :
    List.append (configurationFieldBits cfg []) suffixBits =
      configurationFieldBits cfg suffixBits := by
  simp [configurationFieldBits, tapeFieldBits, cellFieldBits,
    cellListFieldBits, List.append_assoc]

theorem cellListCanonicalLengthPrefixBitsRev_reverse_append_tick
    (n : Nat) :
    List.append (cellListCanonicalLengthPrefixBitsRev n).reverse tickBits =
      List.append tickBits
        (cellListCanonicalLengthPrefixBitsRev n).reverse := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        List.append
            (cellListCanonicalLengthPrefixBitsRev (n + 1)).reverse
            tickBits =
          List.append
            (List.append
              (cellListCanonicalLengthPrefixBitsRev n).reverse tickBits)
            tickBits := by
              simp [cellListCanonicalLengthPrefixBitsRev,
                List.reverse_append, List.append_assoc]
        _ =
          List.append
            (List.append tickBits
              (cellListCanonicalLengthPrefixBitsRev n).reverse)
            tickBits := by
              rw [ih]
        _ =
          List.append tickBits
            (cellListCanonicalLengthPrefixBitsRev (n + 1)).reverse := by
              simp [cellListCanonicalLengthPrefixBitsRev,
                List.reverse_append, List.append_assoc]

theorem cellListCanonicalLengthPrefixBitsRev_reverse_append_done
    (n : Nat) :
    List.append (cellListCanonicalLengthPrefixBitsRev n).reverse doneBits =
      stageNatBits n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        List.append
            (cellListCanonicalLengthPrefixBitsRev (n + 1)).reverse
            doneBits =
          List.append
            (List.append
              (cellListCanonicalLengthPrefixBitsRev n).reverse tickBits)
            doneBits := by
              simp [cellListCanonicalLengthPrefixBitsRev,
                List.reverse_append]
        _ =
          List.append
            (List.append tickBits
              (cellListCanonicalLengthPrefixBitsRev n).reverse)
            doneBits := by
              rw [cellListCanonicalLengthPrefixBitsRev_reverse_append_tick]
        _ =
          List.append tickBits
            (List.append
              (cellListCanonicalLengthPrefixBitsRev n).reverse doneBits) := by
              simp [List.append_assoc]
        _ = List.append tickBits (stageNatBits n) := by
              rw [ih]
        _ = stageNatBits (n + 1) := by
              rw [stageNatBits_succ]
              rfl

theorem cellListCanonicalRestoredBitsRev_reverse
    (cells : List (Option Bool)) :
    (cellListCanonicalRestoredBitsRev cells).reverse =
      cellListFieldBits cells [] := by
  calc
    (cellListCanonicalRestoredBitsRev cells).reverse =
        List.append (cellListCanonicalLengthPrefixBitsRev cells.length).reverse
          (List.append doneBits (cellsCodeBits cells)) := by
          simp [cellListCanonicalRestoredBitsRev, List.reverse_append,
            List.append_assoc]
    _ =
        List.append
          (List.append
            (cellListCanonicalLengthPrefixBitsRev cells.length).reverse
            doneBits)
          (cellsCodeBits cells) := by
          simp [List.append_assoc]
    _ = List.append (stageNatBits cells.length) (cellsCodeBits cells) := by
          rw [cellListCanonicalLengthPrefixBitsRev_reverse_append_done]
    _ = cellListFieldBits cells [] := by
          simp [cellListFieldBits]

def configurationRestoredBitsRev
    (cfg : Configuration) : Word Bool :=
  List.append (cellListCanonicalRestoredBitsRev cfg.tape.right)
    (List.append (cellCodeBits cfg.tape.head).reverse
      (List.append (cellListCanonicalRestoredBitsRev cfg.tape.left)
        (stageNatBits cfg.state).reverse))

theorem configurationRestoredBitsRev_map_some_withBase
    (cfg : Configuration)
    (baseLeft : List (Option Bool)) :
    List.append ((configurationRestoredBitsRev cfg).map some)
        baseLeft =
      configurationRestoredLeftWithBase cfg baseLeft := by
  let baseAfterState :=
    List.append ((stageNatBits cfg.state).reverse.map some) baseLeft
  let baseAfterLeft :=
    cellListCanonicalRestoredLeftWithBase cfg.tape.left baseAfterState
  have hleft :
      List.append
          ((cellListCanonicalRestoredBitsRev cfg.tape.left).map some)
          baseAfterState =
        baseAfterLeft := by
    simpa [baseAfterLeft] using
      cellListCanonicalRestoredBitsRev_map_some_withBase
        cfg.tape.left baseAfterState
  have hright :
      List.append
          ((cellListCanonicalRestoredBitsRev cfg.tape.right).map some)
          (List.append ((cellCodeBits cfg.tape.head).reverse.map some)
            baseAfterLeft) =
        cellListCanonicalRestoredLeftWithBase cfg.tape.right
          (List.append ((cellCodeBits cfg.tape.head).reverse.map some)
            baseAfterLeft) := by
    simpa using
      cellListCanonicalRestoredBitsRev_map_some_withBase
        cfg.tape.right
        (List.append ((cellCodeBits cfg.tape.head).reverse.map some)
          baseAfterLeft)
  calc
    List.append ((configurationRestoredBitsRev cfg).map some) baseLeft =
        List.append
          ((cellListCanonicalRestoredBitsRev cfg.tape.right).map some)
          (List.append
            ((cellCodeBits cfg.tape.head).reverse.map some)
            (List.append
              ((cellListCanonicalRestoredBitsRev cfg.tape.left).map some)
              baseAfterState)) := by
          simp [configurationRestoredBitsRev, baseAfterState,
            List.map_append, List.map_reverse, List.append_assoc]
    _ =
        List.append
          ((cellListCanonicalRestoredBitsRev cfg.tape.right).map some)
          (List.append
            ((cellCodeBits cfg.tape.head).reverse.map some)
            baseAfterLeft) := by
          rw [hleft]
    _ = configurationRestoredLeftWithBase cfg baseLeft := by
          simpa [configurationRestoredLeftWithBase, baseAfterState,
            baseAfterLeft] using hright

theorem configurationRestoredLeftWithBase_append_base
    (cfg : Configuration) (baseLeft extra : List (Option Bool)) :
    configurationRestoredLeftWithBase
        cfg (List.append baseLeft extra) =
      List.append
        (configurationRestoredLeftWithBase cfg baseLeft)
        extra := by
  rw [←
    configurationRestoredBitsRev_map_some_withBase
      cfg (List.append baseLeft extra)]
  rw [← configurationRestoredBitsRev_map_some_withBase cfg baseLeft]
  simp [List.append_assoc]

theorem configurationRestoredBitsRev_reverse
    (cfg : Configuration) :
    (configurationRestoredBitsRev cfg).reverse =
      configurationFieldBits cfg [] := by
  simp [configurationRestoredBitsRev, configurationFieldBits,
    tapeFieldBits, cellFieldBits,
    cellListCanonicalRestoredBitsRev_reverse, cellListFieldBits,
    List.reverse_append, List.append_assoc]

def markedDovetailLayoutBodyRestoredBitsRev
    (L : DovetailLayout) : Word Bool :=
  List.append (cellCodeBits (some L.rejectHit)).reverse
    (List.append (cellCodeBits (some L.acceptHit)).reverse
      (List.append (configurationRestoredBitsRev L.rejectConfig)
        (List.append (configurationRestoredBitsRev L.acceptConfig)
          (List.append (stageNatBits L.stage).reverse
            (List.append
              (cellListCanonicalRestoredBitsRev (L.input.map some))
              transitionRemainderBits.reverse)))))

def markedDovetailLayoutBodyBits
    (L : DovetailLayout) : Word Bool :=
  List.append transitionRemainderBits
    (boolWordFieldBits L.input
      (List.append (stageNatBits L.stage)
        (configurationFieldBits L.acceptConfig
          (configurationFieldBits L.rejectConfig
            (boolFieldBits L.acceptHit
              (boolFieldBits L.rejectHit []))))))

theorem markedDovetailLayoutBodyRestoredBitsRev_reverse
    (L : DovetailLayout) :
    (markedDovetailLayoutBodyRestoredBitsRev L).reverse =
      markedDovetailLayoutBodyBits L := by
  simp [markedDovetailLayoutBodyRestoredBitsRev,
    markedDovetailLayoutBodyBits, boolWordFieldBits, boolFieldBits,
    cellFieldBits, cellListFieldBits,
    cellListCanonicalRestoredBitsRev_reverse,
    configurationRestoredBitsRev_reverse, List.reverse_append,
    List.append_assoc]
  simp [configurationFieldBits, tapeFieldBits, cellFieldBits,
    cellListFieldBits, List.append_assoc]

theorem markedDovetailLayoutBodyRestoredBitsRev_map_some_withMarker
    (L : DovetailLayout) :
    List.append ((markedDovetailLayoutBodyRestoredBitsRev L).map some)
        [none] =
      finalHitFlagsRestoredLeftWithBase L.acceptHit L.rejectHit
        (configurationRestoredLeftWithBase L.rejectConfig
          (configurationRestoredLeftWithBase L.acceptConfig
            (List.append ((stageNatBits L.stage).reverse.map some)
              (cellListCanonicalRestoredLeftWithBase (L.input.map some)
                (List.append (transitionRemainderBits.reverse.map some)
                  [none]))))) := by
  let baseAfterTransition :=
    List.append (transitionRemainderBits.reverse.map some) [none]
  let baseAfterInput :=
    cellListCanonicalRestoredLeftWithBase (L.input.map some)
      baseAfterTransition
  let baseAfterStage :=
    List.append ((stageNatBits L.stage).reverse.map some) baseAfterInput
  let baseAfterAccept :=
    configurationRestoredLeftWithBase L.acceptConfig baseAfterStage
  have hinput :
      List.append
          ((cellListCanonicalRestoredBitsRev (L.input.map some)).map some)
          baseAfterTransition =
        baseAfterInput := by
    simpa [baseAfterInput] using
      cellListCanonicalRestoredBitsRev_map_some_withBase
        (L.input.map some) baseAfterTransition
  have haccept :
      List.append ((configurationRestoredBitsRev L.acceptConfig).map some)
          baseAfterStage =
        baseAfterAccept := by
    simpa [baseAfterAccept] using
      configurationRestoredBitsRev_map_some_withBase
        L.acceptConfig baseAfterStage
  have hreject :
      List.append ((configurationRestoredBitsRev L.rejectConfig).map some)
          baseAfterAccept =
        configurationRestoredLeftWithBase L.rejectConfig baseAfterAccept :=
    configurationRestoredBitsRev_map_some_withBase
      L.rejectConfig baseAfterAccept
  calc
    List.append ((markedDovetailLayoutBodyRestoredBitsRev L).map some)
        [none] =
      finalHitFlagsRestoredLeftWithBase L.acceptHit L.rejectHit
        (List.append
          ((configurationRestoredBitsRev L.rejectConfig).map some)
          (List.append
            ((configurationRestoredBitsRev L.acceptConfig).map some)
            (List.append ((stageNatBits L.stage).reverse.map some)
              (List.append
                ((cellListCanonicalRestoredBitsRev
                  (L.input.map some)).map some)
                baseAfterTransition)))) := by
          simp [markedDovetailLayoutBodyRestoredBitsRev,
            finalHitFlagsRestoredLeftWithBase, baseAfterTransition,
            List.map_append, List.map_reverse, List.append_assoc]
    _ =
      finalHitFlagsRestoredLeftWithBase L.acceptHit L.rejectHit
        (List.append
          ((configurationRestoredBitsRev L.rejectConfig).map some)
          (List.append
            ((configurationRestoredBitsRev L.acceptConfig).map some)
            baseAfterStage)) := by
          rw [hinput]
    _ =
      finalHitFlagsRestoredLeftWithBase L.acceptHit L.rejectHit
        (List.append
          ((configurationRestoredBitsRev L.rejectConfig).map some)
          baseAfterAccept) := by
          rw [haccept]
    _ =
      finalHitFlagsRestoredLeftWithBase L.acceptHit L.rejectHit
        (configurationRestoredLeftWithBase L.rejectConfig
          baseAfterAccept) := by
          rw [hreject]
    _ =
      finalHitFlagsRestoredLeftWithBase L.acceptHit L.rejectHit
        (configurationRestoredLeftWithBase L.rejectConfig
          (configurationRestoredLeftWithBase L.acceptConfig
            (List.append ((stageNatBits L.stage).reverse.map some)
              (cellListCanonicalRestoredLeftWithBase (L.input.map some)
                (List.append (transitionRemainderBits.reverse.map some)
                  [none]))))) := by
          simp [baseAfterTransition, baseAfterInput, baseAfterStage,
            baseAfterAccept]

theorem dovetailLayoutFieldBits_nil_eq_first_body
    (L : DovetailLayout) :
    dovetailLayoutFieldBits L [] =
      false :: markedDovetailLayoutBodyBits L := by
  simp [dovetailLayoutFieldBits, markedDovetailLayoutBodyBits,
    transitionPrefixBits, transitionRemainderBits,
    encodeCodeSymbolAsInput]

theorem markedDovetailLayoutBodyBits_cons_false
    (L : DovetailLayout) :
    exists tail : Word Bool,
      markedDovetailLayoutBodyBits L = false :: tail := by
  refine ⟨List.cons false (List.cons true
    (boolWordFieldBits L.input
      (List.append (stageNatBits L.stage)
        (configurationFieldBits L.acceptConfig
          (configurationFieldBits L.rejectConfig
            (boolFieldBits L.acceptHit
              (boolFieldBits L.rejectHit []))))))), ?_⟩
  simp [markedDovetailLayoutBodyBits, transitionRemainderBits]


end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
