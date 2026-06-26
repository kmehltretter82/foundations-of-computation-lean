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

namespace EncodedRewriters
namespace CanonicalLayouts
namespace DovetailLayoutScanner

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

/-!
## Composed tape and configuration field scanners

Run theorems keep explicit base-left contexts so the recognizer can be chained
field by field.
-/

def TapeSuffixScannerDescription : MachineDescription :=
  MachineDescription.seqSubroutine
    CellListSuffixScannerDescription
    (MachineDescription.seqSubroutine
      CellSuffixScannerDescription
      CellListSuffixScannerDescription
      Direction.right)
    Direction.right

theorem tapeSuffixScannerDescription_subroutineReady :
    TapeSuffixScannerDescription.SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    cellListSuffixScannerDescription_subroutineReady
    (MachineDescription.seqSubroutine_subroutineReady
      cellSuffixScannerDescription_subroutineReady
      cellListSuffixScannerDescription_subroutineReady)

def ConfigurationSuffixScannerDescription : MachineDescription :=
  MachineDescription.seqSubroutine
    DovetailStagePrefix.NonemptyNatSuffixScannerDescription
    TapeSuffixScannerDescription
    Direction.right

theorem configurationSuffixScannerDescription_subroutineReady :
    ConfigurationSuffixScannerDescription.SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
    tapeSuffixScannerDescription_subroutineReady

def FinalHitFlagsScannerDescription : MachineDescription :=
  MachineDescription.seqSubroutine
    BoolSuffixScannerDescription
    BoolFinalScannerDescription
    Direction.right

theorem finalHitFlagsScannerDescription_subroutineReady :
    FinalHitFlagsScannerDescription.SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
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
  refine ⟨by native_decide, by native_decide, by native_decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := MarkFirstTransitionBitDescription.transitions)
      (stateCount := MarkFirstTransitionBitDescription.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := MarkFirstTransitionBitDescription.transitions)
      (by native_decide)

theorem markFirstTransitionBitDescription_haltTransitionFree :
    MarkFirstTransitionBitDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := MarkFirstTransitionBitDescription.transitions)
    (state := MarkFirstTransitionBitDescription.halt)
    (by native_decide)

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
      keepMove, writeMove, MachineDescription.runConfig,
      MachineDescription.stepConfig, MachineDescription.lookupTransition,
      MachineDescription.Matches, MachineDescription.transition,
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
  refine ⟨by native_decide, by native_decide, by native_decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := TransitionRemainderPrefixScannerDescription.transitions)
      (stateCount :=
        TransitionRemainderPrefixScannerDescription.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := TransitionRemainderPrefixScannerDescription.transitions)
      (by native_decide)

theorem transitionRemainderPrefixScannerDescription_haltTransitionFree :
    TransitionRemainderPrefixScannerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := TransitionRemainderPrefixScannerDescription.transitions)
    (state := TransitionRemainderPrefixScannerDescription.halt)
    (by native_decide)

theorem transitionRemainderPrefixScannerDescription_subroutineReady :
    TransitionRemainderPrefixScannerDescription.SubroutineReady :=
  ⟨transitionRemainderPrefixScannerDescription_wellFormed,
    transitionRemainderPrefixScannerDescription_haltTransitionFree⟩

def transitionRemainderBits : Word Bool :=
  [false, false, true]

def transitionRemainderHandoffConfigWithBase
    (baseLeft : List (Option Bool)) (suffixBits : Word Bool) :
    MachineDescription.Configuration :=
  { state := TransitionRemainderPrefixScannerDescription.halt
    tape :=
      Tape.move Direction.left
        (tapeAtCells
          (List.append (transitionRemainderBits.reverse.map some)
            baseLeft)
          (suffixBits.map some)) }

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
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
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
  refine ⟨by native_decide, by native_decide, by native_decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := ReturnToFirstMarkerDescription.transitions)
      (stateCount := ReturnToFirstMarkerDescription.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := ReturnToFirstMarkerDescription.transitions)
      (by native_decide)

theorem returnToFirstMarkerDescription_haltTransitionFree :
    ReturnToFirstMarkerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := ReturnToFirstMarkerDescription.transitions)
    (state := ReturnToFirstMarkerDescription.halt)
    (by native_decide)

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
    MachineDescription.Configuration :=
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
        keepMove, writeMove, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write, Tape.move,
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
            keepMove, writeMove, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
      rw [MachineDescription.runConfig_add]
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
  rw [MachineDescription.runConfig_add]
  cases prefixRev with
  | nil =>
      simp [ReturnToFirstMarkerDescription, config, tapeAtCells,
        keepMove, writeMove, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write, Tape.move,
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
            keepMove, writeMove, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
      rw [hstep]
      simpa [List.append_assoc] using
        run_returnToFirstMarker_scan (bit :: rest) []

def RejectConfigAndFinalFlagsScannerDescription : MachineDescription :=
  MachineDescription.seqSubroutine
    ConfigurationSuffixScannerDescription
    FinalHitFlagsScannerDescription
    Direction.right

theorem rejectConfigAndFinalFlagsScannerDescription_subroutineReady :
    RejectConfigAndFinalFlagsScannerDescription.SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    configurationSuffixScannerDescription_subroutineReady
    finalHitFlagsScannerDescription_subroutineReady

def ConfigurationsAndFinalFlagsScannerDescription : MachineDescription :=
  MachineDescription.seqSubroutine
    ConfigurationSuffixScannerDescription
    RejectConfigAndFinalFlagsScannerDescription
    Direction.right

theorem configurationsAndFinalFlagsScannerDescription_subroutineReady :
    ConfigurationsAndFinalFlagsScannerDescription.SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    configurationSuffixScannerDescription_subroutineReady
    rejectConfigAndFinalFlagsScannerDescription_subroutineReady

def StageConfigurationsAndFinalFlagsScannerDescription :
    MachineDescription :=
  MachineDescription.seqSubroutine
    DovetailStagePrefix.NonemptyNatSuffixScannerDescription
    ConfigurationsAndFinalFlagsScannerDescription
    Direction.right

theorem stageConfigurationsAndFinalFlagsScannerDescription_subroutineReady :
    StageConfigurationsAndFinalFlagsScannerDescription.SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
    configurationsAndFinalFlagsScannerDescription_subroutineReady

def InputStageConfigurationsAndFinalFlagsScannerDescription :
    MachineDescription :=
  MachineDescription.seqSubroutine
    BoolWordSuffixScannerDescription
    StageConfigurationsAndFinalFlagsScannerDescription
    Direction.right

theorem inputStageConfigurationsAndFinalFlagsScannerDescription_subroutineReady :
    InputStageConfigurationsAndFinalFlagsScannerDescription.SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    boolWordSuffixScannerDescription_subroutineReady
    stageConfigurationsAndFinalFlagsScannerDescription_subroutineReady

def MarkedDovetailLayoutBodyScannerDescription : MachineDescription :=
  MachineDescription.seqSubroutine
    TransitionRemainderPrefixScannerDescription
    InputStageConfigurationsAndFinalFlagsScannerDescription
    Direction.right

theorem markedDovetailLayoutBodyScannerDescription_subroutineReady :
    MarkedDovetailLayoutBodyScannerDescription.SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    transitionRemainderPrefixScannerDescription_subroutineReady
    inputStageConfigurationsAndFinalFlagsScannerDescription_subroutineReady

def CheckedDovetailLayoutScannerDescription : MachineDescription :=
  MachineDescription.seqSubroutine
    MarkFirstTransitionBitDescription
    (MachineDescription.seqSubroutine
      MarkedDovetailLayoutBodyScannerDescription
      ReturnToFirstMarkerDescription
      Direction.right)
    Direction.right

theorem checkedDovetailLayoutScannerDescription_subroutineReady :
    CheckedDovetailLayoutScannerDescription.SubroutineReady :=
  MachineDescription.seqSubroutine_subroutineReady
    markFirstTransitionBitDescription_subroutineReady
    (MachineDescription.seqSubroutine_subroutineReady
      markedDovetailLayoutBodyScannerDescription_subroutineReady
      returnToFirstMarkerDescription_subroutineReady)

def configurationRestoredLeftWithBase
    (cfg : MachineDescription.Configuration)
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
    (cfg : MachineDescription.Configuration) (suffixBits : Word Bool) :
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
    (cfg : MachineDescription.Configuration) (suffixBits : Word Bool) :
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
    (cfg : MachineDescription.Configuration) : Word Bool :=
  List.append (cellListCanonicalRestoredBitsRev cfg.tape.right)
    (List.append (cellCodeBits cfg.tape.head).reverse
      (List.append (cellListCanonicalRestoredBitsRev cfg.tape.left)
        (stageNatBits cfg.state).reverse))

theorem configurationRestoredBitsRev_map_some_withBase
    (cfg : MachineDescription.Configuration)
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

theorem configurationRestoredBitsRev_reverse
    (cfg : MachineDescription.Configuration) :
    (configurationRestoredBitsRev cfg).reverse =
      configurationFieldBits cfg [] := by
  simp [configurationRestoredBitsRev, configurationFieldBits,
    tapeFieldBits, cellFieldBits,
    cellListCanonicalRestoredBitsRev_reverse, cellListFieldBits,
    List.reverse_append, List.append_assoc]

def markedDovetailLayoutBodyRestoredBitsRev
    (L : MachineDescription.DovetailLayout) : Word Bool :=
  List.append (cellCodeBits (some L.rejectHit)).reverse
    (List.append (cellCodeBits (some L.acceptHit)).reverse
      (List.append (configurationRestoredBitsRev L.rejectConfig)
        (List.append (configurationRestoredBitsRev L.acceptConfig)
          (List.append (stageNatBits L.stage).reverse
            (List.append
              (cellListCanonicalRestoredBitsRev (L.input.map some))
              transitionRemainderBits.reverse)))))

def markedDovetailLayoutBodyBits
    (L : MachineDescription.DovetailLayout) : Word Bool :=
  List.append transitionRemainderBits
    (boolWordFieldBits L.input
      (List.append (stageNatBits L.stage)
        (configurationFieldBits L.acceptConfig
          (configurationFieldBits L.rejectConfig
            (boolFieldBits L.acceptHit
              (boolFieldBits L.rejectHit []))))))

theorem markedDovetailLayoutBodyRestoredBitsRev_reverse
    (L : MachineDescription.DovetailLayout) :
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
    (L : MachineDescription.DovetailLayout) :
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
    (L : MachineDescription.DovetailLayout) :
    dovetailLayoutFieldBits L [] =
      false :: markedDovetailLayoutBodyBits L := by
  simp [dovetailLayoutFieldBits, markedDovetailLayoutBodyBits,
    transitionPrefixBits, transitionRemainderBits,
    MachineDescription.encodeCodeSymbolAsInput]

theorem markedDovetailLayoutBodyBits_cons_false
    (L : MachineDescription.DovetailLayout) :
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

theorem run_finalHitFlags_raw_to_handoff_withBase
    (acceptHit rejectHit : Bool)
    (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      FinalHitFlagsScannerDescription.runConfig steps
          { state := FinalHitFlagsScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((boolFieldBits acceptHit
                  (boolFieldBits rejectHit [])).map some) } =
        { state := FinalHitFlagsScannerDescription.halt
          tape :=
            (boolFinalHandoffConfigWithBase rejectHit
              (List.append
                ((cellCodeBits (some acceptHit)).reverse.map some)
                baseLeft)).tape } := by
  rcases cellCodeBits_cons_false (some rejectHit) with
    ⟨tail, htail⟩
  rcases run_boolOnlySuffix_raw_to_handoff_withBase
      acceptHit baseLeft false tail with
    ⟨acceptSteps, haccept⟩
  let baseAfterAccept :=
    List.append ((cellCodeBits (some acceptHit)).reverse.map some)
      baseLeft
  let Tmid :=
    boolOnlySuffixHandoffConfigWithBase acceptHit baseLeft
      (false :: tail)
  have hArun :
      BoolSuffixScannerDescription.runConfig acceptSteps
          { state := BoolSuffixScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((boolFieldBits acceptHit
                  (boolFieldBits rejectHit [])).map some) } =
        { state := BoolSuffixScannerDescription.halt
          tape := Tmid.tape } := by
    change
      BoolSuffixScannerDescription.runConfig acceptSteps
          (config 10 baseLeft
            ((boolFieldBits acceptHit
              (boolFieldBits rejectHit [])).map some)) =
        Tmid
    rw [show
        ((boolFieldBits acceptHit
          (boolFieldBits rejectHit [])).map some) =
          List.append ((cellCodeBits (some acceptHit)).map some)
            (some false :: tail.map some) by
      change
        (cellFieldBits (some acceptHit)
          (cellFieldBits (some rejectHit) [])).map some =
          List.append ((cellCodeBits (some acceptHit)).map some)
            (some false :: tail.map some)
      simp [cellFieldBits, htail, List.map_append]]
    simpa [Tmid] using haccept
  have hBReach :
      exists nB : Nat,
        BoolFinalScannerDescription.runConfig nB
            { state := BoolFinalScannerDescription.start
              tape := Tape.move Direction.right Tmid.tape } =
          { state := BoolFinalScannerDescription.halt
            tape :=
              (boolFinalHandoffConfigWithBase rejectHit
                baseAfterAccept).tape } := by
    rcases run_boolFinal_raw_to_handoff_withBase
        rejectHit baseAfterAccept with
      ⟨finalSteps, hfinal⟩
    have hmove :
        Tape.move Direction.right Tmid.tape =
          tapeAtCells baseAfterAccept
            ((cellCodeBits (some rejectHit)).map some) := by
      simpa [Tmid, baseAfterAccept, htail] using
        boolOnlySuffixHandoffConfigWithBase_move_right
          acceptHit baseLeft false tail
    exact
      CommonGround.SeqComposition.runConfig_reaches_from_move_eq
        (B := BoolFinalScannerDescription)
        (handoffMove := Direction.right)
        hmove
        (by simpa [config] using hfinal)
  simpa [FinalHitFlagsScannerDescription, Tmid, baseAfterAccept]
    using
      CommonGround.SeqComposition.seqSubroutine_runConfig_exists
        (A := BoolSuffixScannerDescription)
        (B := BoolFinalScannerDescription)
        (handoffMove := Direction.right)
        boolSuffixScannerDescription_subroutineReady
        boolFinalScannerDescription_subroutineReady
        hArun hBReach

theorem run_cellThenCellList_raw_to_handoff_withBase
    (head : Option Bool) (right baseLeft : List (Option Bool))
    (suffixTail : Word Bool) :
    exists steps : Nat,
      (MachineDescription.seqSubroutine
          CellSuffixScannerDescription
          CellListSuffixScannerDescription
          Direction.right).runConfig steps
          { state :=
              (MachineDescription.seqSubroutine
                CellSuffixScannerDescription
                CellListSuffixScannerDescription
                Direction.right).start
            tape :=
              tapeAtCells baseLeft
                ((cellFieldBits head
                  (cellListFieldBits right
                    (false :: suffixTail))).map some) } =
        { state :=
            (MachineDescription.seqSubroutine
              CellSuffixScannerDescription
              CellListSuffixScannerDescription
              Direction.right).halt
          tape :=
            (cellListCanonicalHandoffConfigWithBase right
              (List.append ((cellCodeBits head).reverse.map some)
                baseLeft)
              (false :: suffixTail)).tape } := by
  rcases cellListFieldBits_cons_false right (false :: suffixTail) with
    ⟨fieldTail, hfieldTail⟩
  rcases run_cellSuffix_raw_to_handoff_withBase
      head baseLeft false fieldTail with
    ⟨headSteps, hhead⟩
  let baseAfterHead :=
    List.append ((cellCodeBits head).reverse.map some) baseLeft
  let Tmid := cellSuffixHandoffConfigWithBase head baseLeft
    (false :: fieldTail)
  have hArun :
      CellSuffixScannerDescription.runConfig headSteps
          { state := CellSuffixScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((cellFieldBits head
                  (cellListFieldBits right
                    (false :: suffixTail))).map some) } =
        { state := CellSuffixScannerDescription.halt
          tape := Tmid.tape } := by
    simpa [Tmid, cellFieldBits, hfieldTail, List.map_append] using
      hhead
  have hBReach :
      exists nB : Nat,
        CellListSuffixScannerDescription.runConfig nB
            { state := CellListSuffixScannerDescription.start
              tape := Tape.move Direction.right Tmid.tape } =
          { state := CellListSuffixScannerDescription.halt
            tape :=
              (cellListCanonicalHandoffConfigWithBase right
                baseAfterHead (false :: suffixTail)).tape } := by
    rcases run_cellList_raw_to_canonical_handoff_withBase
        right baseAfterHead suffixTail with
      ⟨rightSteps, hright⟩
    have hmove :
        Tape.move Direction.right Tmid.tape =
          tapeAtCells baseAfterHead
            ((cellListFieldBits right
              (false :: suffixTail)).map some) := by
      simpa [Tmid, baseAfterHead, hfieldTail] using
        cellSuffixHandoffConfigWithBase_move_right
          head baseLeft false fieldTail
    exact
      CommonGround.SeqComposition.runConfig_reaches_from_move_eq
        (B := CellListSuffixScannerDescription)
        (handoffMove := Direction.right)
        hmove
        (by
          simpa [CellListSuffixScannerDescription, config,
            cellListFieldBits, List.map_append, baseAfterHead] using
            hright)
  simpa [Tmid, baseAfterHead, cellFieldBits, hfieldTail,
    List.map_append] using
      CommonGround.SeqComposition.seqSubroutine_runConfig_exists
        (A := CellSuffixScannerDescription)
        (B := CellListSuffixScannerDescription)
        (handoffMove := Direction.right)
        cellSuffixScannerDescription_subroutineReady
        cellListSuffixScannerDescription_subroutineReady
        hArun hBReach

theorem run_tapeSuffix_raw_to_handoff_withBase
    (T : Tape Bool) (baseLeft : List (Option Bool))
    (suffixTail : Word Bool) :
    exists steps : Nat,
      TapeSuffixScannerDescription.runConfig steps
          { state := TapeSuffixScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((tapeFieldBits T (false :: suffixTail)).map some) } =
        { state := TapeSuffixScannerDescription.halt
          tape :=
            (cellListCanonicalHandoffConfigWithBase T.right
              (List.append ((cellCodeBits T.head).reverse.map some)
                (cellListCanonicalRestoredLeftWithBase T.left baseLeft))
              (false :: suffixTail)).tape } := by
  rcases cellFieldBits_cons_false T.head
      (cellListFieldBits T.right (false :: suffixTail)) with
    ⟨headTail, hheadTail⟩
  rcases run_cellList_raw_to_canonical_handoff_withBase
      T.left baseLeft headTail with
    ⟨leftSteps, hleft⟩
  let baseAfterLeft := cellListCanonicalRestoredLeftWithBase T.left baseLeft
  let Tmid := cellListCanonicalHandoffConfigWithBase T.left baseLeft
    (false :: headTail)
  have hArun :
      CellListSuffixScannerDescription.runConfig leftSteps
          { state := CellListSuffixScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((tapeFieldBits T (false :: suffixTail)).map some) } =
        { state := CellListSuffixScannerDescription.halt
          tape := Tmid.tape } := by
    change
      CellListSuffixScannerDescription.runConfig leftSteps
          (config 100 baseLeft
            ((tapeFieldBits T (false :: suffixTail)).map some)) =
        Tmid
    rw [show
        ((tapeFieldBits T (false :: suffixTail)).map some) =
          List.append ((stageNatBits T.left.length).map some)
            (List.append ((cellsCodeBits T.left).map some)
              (some false :: headTail.map some)) by
      change
        (cellListFieldBits T.left
          (cellFieldBits T.head
            (cellListFieldBits T.right (false :: suffixTail)))).map
            some =
          List.append ((stageNatBits T.left.length).map some)
            (List.append ((cellsCodeBits T.left).map some)
              (some false :: headTail.map some))
      rw [hheadTail]
      simp [cellListFieldBits, List.map_append]]
    simpa [Tmid] using hleft
  have hBReach :
      exists nB : Nat,
        (MachineDescription.seqSubroutine
          CellSuffixScannerDescription
          CellListSuffixScannerDescription
          Direction.right).runConfig nB
            { state :=
                (MachineDescription.seqSubroutine
                  CellSuffixScannerDescription
                  CellListSuffixScannerDescription
                  Direction.right).start
              tape := Tape.move Direction.right Tmid.tape } =
          { state :=
              (MachineDescription.seqSubroutine
                CellSuffixScannerDescription
                CellListSuffixScannerDescription
                Direction.right).halt
            tape :=
              (cellListCanonicalHandoffConfigWithBase T.right
                (List.append ((cellCodeBits T.head).reverse.map some)
                  baseAfterLeft)
                (false :: suffixTail)).tape } := by
    rcases run_cellThenCellList_raw_to_handoff_withBase
        T.head T.right baseAfterLeft suffixTail with
      ⟨innerSteps, hinner⟩
    have hmove :
        Tape.move Direction.right Tmid.tape =
          tapeAtCells baseAfterLeft
            ((cellFieldBits T.head
              (cellListFieldBits T.right
                (false :: suffixTail))).map some) := by
      simpa [Tmid, baseAfterLeft, hheadTail] using
        cellListCanonicalHandoffConfigWithBase_move_right
          T.left baseLeft false headTail
    exact
      CommonGround.SeqComposition.runConfig_reaches_from_move_eq
        (B :=
          MachineDescription.seqSubroutine
            CellSuffixScannerDescription
            CellListSuffixScannerDescription
            Direction.right)
        (handoffMove := Direction.right)
        hmove
        (by simpa [baseAfterLeft] using hinner)
  simpa [TapeSuffixScannerDescription, Tmid, baseAfterLeft,
    tapeFieldBits, hheadTail, List.map_append] using
    CommonGround.SeqComposition.seqSubroutine_runConfig_exists
      (A := CellListSuffixScannerDescription)
      (B :=
        MachineDescription.seqSubroutine
          CellSuffixScannerDescription
          CellListSuffixScannerDescription
          Direction.right)
      (handoffMove := Direction.right)
      cellListSuffixScannerDescription_subroutineReady
      (MachineDescription.seqSubroutine_subroutineReady
        cellSuffixScannerDescription_subroutineReady
        cellListSuffixScannerDescription_subroutineReady)
      hArun hBReach

theorem run_configurationSuffix_raw_to_handoff_withBase
    (cfg : MachineDescription.Configuration)
    (baseLeft : List (Option Bool)) (suffixTail : Word Bool) :
    exists steps : Nat,
      ConfigurationSuffixScannerDescription.runConfig steps
          { state := ConfigurationSuffixScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((configurationFieldBits cfg
                  (false :: suffixTail)).map some) } =
        { state := ConfigurationSuffixScannerDescription.halt
          tape :=
            (cellListCanonicalHandoffConfigWithBase cfg.tape.right
              (List.append ((cellCodeBits cfg.tape.head).reverse.map some)
                (cellListCanonicalRestoredLeftWithBase cfg.tape.left
                  (List.append ((stageNatBits cfg.state).reverse.map some)
                    baseLeft)))
              (false :: suffixTail)).tape } := by
  rcases tapeFieldBits_cons_false cfg.tape (false :: suffixTail) with
    ⟨tapeTail, htapeTail⟩
  rcases
      DovetailStagePrefix.run_nonemptyNatSuffix_raw_to_handoff_withBase
        cfg.state baseLeft false tapeTail with
    ⟨stateSteps, hstate⟩
  let baseAfterState :=
    List.append ((stageNatBits cfg.state).reverse.map some) baseLeft
  let Tmid :=
    DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBase
      cfg.state baseLeft (false :: tapeTail)
  have hArun :
      DovetailStagePrefix.NonemptyNatSuffixScannerDescription.runConfig
          stateSteps
          { state :=
              DovetailStagePrefix.NonemptyNatSuffixScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((configurationFieldBits cfg
                  (false :: suffixTail)).map some) } =
        { state := DovetailStagePrefix.NonemptyNatSuffixScannerDescription.halt
          tape := Tmid.tape } := by
    change
      DovetailStagePrefix.NonemptyNatSuffixScannerDescription.runConfig
          stateSteps
          (config 200 baseLeft
            ((configurationFieldBits cfg
              (false :: suffixTail)).map some)) =
        Tmid
    rw [show
        ((configurationFieldBits cfg
          (false :: suffixTail)).map some) =
          List.append ((stageNatBits cfg.state).map some)
            (some false :: tapeTail.map some) by
      change
        (List.append (stageNatBits cfg.state)
          (tapeFieldBits cfg.tape (false :: suffixTail))).map some =
          List.append ((stageNatBits cfg.state).map some)
            (some false :: tapeTail.map some)
      rw [htapeTail]
      simp [List.map_append]]
    simpa [Tmid] using hstate
  have hBReach :
      exists nB : Nat,
        TapeSuffixScannerDescription.runConfig nB
            { state := TapeSuffixScannerDescription.start
              tape := Tape.move Direction.right Tmid.tape } =
          { state := TapeSuffixScannerDescription.halt
            tape :=
              (cellListCanonicalHandoffConfigWithBase cfg.tape.right
                (List.append
                  ((cellCodeBits cfg.tape.head).reverse.map some)
                  (cellListCanonicalRestoredLeftWithBase cfg.tape.left
                    baseAfterState))
                (false :: suffixTail)).tape } := by
    rcases run_tapeSuffix_raw_to_handoff_withBase
        cfg.tape baseAfterState suffixTail with
      ⟨tapeSteps, htape⟩
    have hmove :
        Tape.move Direction.right Tmid.tape =
          tapeAtCells baseAfterState
            ((tapeFieldBits cfg.tape
              (false :: suffixTail)).map some) := by
      simpa [Tmid, baseAfterState, htapeTail] using
        DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBase_move_right
          cfg.state baseLeft false tapeTail
    exact
      CommonGround.SeqComposition.runConfig_reaches_from_move_eq
        (B := TapeSuffixScannerDescription)
        (handoffMove := Direction.right)
        hmove
        (by simpa [baseAfterState] using htape)
  simpa [ConfigurationSuffixScannerDescription, Tmid, baseAfterState,
    configurationFieldBits, htapeTail, List.map_append] using
      CommonGround.SeqComposition.seqSubroutine_runConfig_exists
        (A := DovetailStagePrefix.NonemptyNatSuffixScannerDescription)
        (B := TapeSuffixScannerDescription)
        (handoffMove := Direction.right)
        DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
        tapeSuffixScannerDescription_subroutineReady
        hArun hBReach

theorem run_rejectConfigAndFinalFlags_raw_to_handoff_withBase
    (rejectConfig : MachineDescription.Configuration)
    (acceptHit rejectHit : Bool)
    (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      RejectConfigAndFinalFlagsScannerDescription.runConfig steps
          { state := RejectConfigAndFinalFlagsScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((configurationFieldBits rejectConfig
                  (boolFieldBits acceptHit
                    (boolFieldBits rejectHit []))).map some) } =
        { state := RejectConfigAndFinalFlagsScannerDescription.halt
          tape :=
            (boolFinalHandoffConfigWithBase rejectHit
              (List.append
                ((cellCodeBits (some acceptHit)).reverse.map some)
                (configurationRestoredLeftWithBase rejectConfig
                  baseLeft))).tape } := by
  rcases cellFieldBits_cons_false (some acceptHit)
      (boolFieldBits rejectHit []) with
    ⟨flagsTail, hflagsTail⟩
  rcases run_configurationSuffix_raw_to_handoff_withBase
      rejectConfig baseLeft flagsTail with
    ⟨configSteps, hconfig⟩
  let TmidTape : Tape Bool :=
    (cellListCanonicalHandoffConfigWithBase rejectConfig.tape.right
      (List.append ((cellCodeBits rejectConfig.tape.head).reverse.map some)
        (cellListCanonicalRestoredLeftWithBase rejectConfig.tape.left
          (List.append ((stageNatBits rejectConfig.state).reverse.map some)
            baseLeft)))
      (false :: flagsTail)).tape
  have hArun :
      ConfigurationSuffixScannerDescription.runConfig configSteps
          { state := ConfigurationSuffixScannerDescription.start
            tape :=
            tapeAtCells baseLeft
                ((configurationFieldBits rejectConfig
                  (boolFieldBits acceptHit
                    (boolFieldBits rejectHit []))).map some) } =
        { state := ConfigurationSuffixScannerDescription.halt
          tape := TmidTape } := by
    rw [show
        ((configurationFieldBits rejectConfig
          (boolFieldBits acceptHit
            (boolFieldBits rejectHit []))).map some) =
          (configurationFieldBits rejectConfig
            (false :: flagsTail)).map some by
      have hflagsBits :
          boolFieldBits acceptHit (boolFieldBits rejectHit []) =
            false :: flagsTail := by
        simpa [boolFieldBits] using hflagsTail
      rw [hflagsBits]]
    simpa [TmidTape] using hconfig
  have hBReach :
      exists nB : Nat,
        FinalHitFlagsScannerDescription.runConfig nB
            { state := FinalHitFlagsScannerDescription.start
              tape := Tape.move Direction.right TmidTape } =
          { state := FinalHitFlagsScannerDescription.halt
            tape :=
              (boolFinalHandoffConfigWithBase rejectHit
                (List.append
                  ((cellCodeBits (some acceptHit)).reverse.map some)
                  (configurationRestoredLeftWithBase rejectConfig
                    baseLeft))).tape } := by
    rcases run_finalHitFlags_raw_to_handoff_withBase
        acceptHit rejectHit
        (configurationRestoredLeftWithBase rejectConfig baseLeft) with
      ⟨flagSteps, hflags⟩
    have hmove :
        Tape.move Direction.right TmidTape =
          tapeAtCells
            (configurationRestoredLeftWithBase rejectConfig baseLeft)
            ((boolFieldBits acceptHit
              (boolFieldBits rejectHit [])).map some) := by
      have hraw :
          Tape.move Direction.right TmidTape =
            tapeAtCells
              (configurationRestoredLeftWithBase rejectConfig baseLeft)
              ((false :: flagsTail).map some) := by
        simpa [TmidTape, configurationRestoredLeftWithBase] using
          cellListCanonicalHandoffConfigWithBase_move_right
            rejectConfig.tape.right
            (List.append
              ((cellCodeBits rejectConfig.tape.head).reverse.map some)
              (cellListCanonicalRestoredLeftWithBase rejectConfig.tape.left
                (List.append
                  ((stageNatBits rejectConfig.state).reverse.map some)
                  baseLeft)))
            false flagsTail
      rw [hraw]
      have hflagsCells :
          (false :: flagsTail).map some =
            (boolFieldBits acceptHit
              (boolFieldBits rejectHit [])).map some := by
        simpa [boolFieldBits] using
          congrArg (fun bits => bits.map some) hflagsTail.symm
      simp [hflagsCells]
    exact
      CommonGround.SeqComposition.runConfig_reaches_from_move_eq
        (B := FinalHitFlagsScannerDescription)
        (handoffMove := Direction.right)
        hmove
        (by simpa using hflags)
  simpa [RejectConfigAndFinalFlagsScannerDescription, TmidTape] using
    CommonGround.SeqComposition.seqSubroutine_runConfig_exists
      (A := ConfigurationSuffixScannerDescription)
      (B := FinalHitFlagsScannerDescription)
      (handoffMove := Direction.right)
      configurationSuffixScannerDescription_subroutineReady
      finalHitFlagsScannerDescription_subroutineReady
      hArun hBReach

theorem run_configurationsAndFinalFlags_raw_to_handoff_withBase
    (acceptConfig rejectConfig : MachineDescription.Configuration)
    (acceptHit rejectHit : Bool)
    (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      ConfigurationsAndFinalFlagsScannerDescription.runConfig steps
          { state := ConfigurationsAndFinalFlagsScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((configurationFieldBits acceptConfig
                  (configurationFieldBits rejectConfig
                    (boolFieldBits acceptHit
                      (boolFieldBits rejectHit [])))).map some) } =
        { state := ConfigurationsAndFinalFlagsScannerDescription.halt
          tape :=
            (boolFinalHandoffConfigWithBase rejectHit
              (List.append
                ((cellCodeBits (some acceptHit)).reverse.map some)
                (configurationRestoredLeftWithBase rejectConfig
                  (configurationRestoredLeftWithBase acceptConfig
                    baseLeft)))).tape } := by
  rcases configurationFieldBits_cons_false rejectConfig
      (boolFieldBits acceptHit (boolFieldBits rejectHit [])) with
    ⟨rejectTail, hrejectTail⟩
  rcases run_configurationSuffix_raw_to_handoff_withBase
      acceptConfig baseLeft rejectTail with
    ⟨acceptSteps, haccept⟩
  let TmidTape : Tape Bool :=
    (cellListCanonicalHandoffConfigWithBase acceptConfig.tape.right
      (List.append ((cellCodeBits acceptConfig.tape.head).reverse.map some)
        (cellListCanonicalRestoredLeftWithBase acceptConfig.tape.left
          (List.append ((stageNatBits acceptConfig.state).reverse.map some)
            baseLeft)))
      (false :: rejectTail)).tape
  have hArun :
      ConfigurationSuffixScannerDescription.runConfig acceptSteps
          { state := ConfigurationSuffixScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((configurationFieldBits acceptConfig
                  (configurationFieldBits rejectConfig
                    (boolFieldBits acceptHit
                      (boolFieldBits rejectHit [])))).map some) } =
        { state := ConfigurationSuffixScannerDescription.halt
          tape := TmidTape } := by
    rw [show
        ((configurationFieldBits acceptConfig
          (configurationFieldBits rejectConfig
            (boolFieldBits acceptHit
              (boolFieldBits rejectHit [])))).map some) =
          (configurationFieldBits acceptConfig
            (false :: rejectTail)).map some by
      rw [hrejectTail]]
    simpa [TmidTape] using haccept
  have hBReach :
      exists nB : Nat,
        RejectConfigAndFinalFlagsScannerDescription.runConfig nB
            { state := RejectConfigAndFinalFlagsScannerDescription.start
              tape := Tape.move Direction.right TmidTape } =
          { state := RejectConfigAndFinalFlagsScannerDescription.halt
            tape :=
              (boolFinalHandoffConfigWithBase rejectHit
                (List.append
                  ((cellCodeBits (some acceptHit)).reverse.map some)
                  (configurationRestoredLeftWithBase rejectConfig
                    (configurationRestoredLeftWithBase acceptConfig
                      baseLeft)))).tape } := by
    rcases run_rejectConfigAndFinalFlags_raw_to_handoff_withBase
        rejectConfig acceptHit rejectHit
        (configurationRestoredLeftWithBase acceptConfig baseLeft) with
      ⟨rejectSteps, hreject⟩
    have hmove :
        Tape.move Direction.right TmidTape =
          tapeAtCells
            (configurationRestoredLeftWithBase acceptConfig baseLeft)
            ((configurationFieldBits rejectConfig
              (boolFieldBits acceptHit
                (boolFieldBits rejectHit []))).map some) := by
      have hraw :
          Tape.move Direction.right TmidTape =
            tapeAtCells
              (configurationRestoredLeftWithBase acceptConfig baseLeft)
              ((false :: rejectTail).map some) := by
        simpa [TmidTape, configurationRestoredLeftWithBase] using
          cellListCanonicalHandoffConfigWithBase_move_right
            acceptConfig.tape.right
            (List.append
              ((cellCodeBits acceptConfig.tape.head).reverse.map some)
              (cellListCanonicalRestoredLeftWithBase acceptConfig.tape.left
                (List.append
                  ((stageNatBits acceptConfig.state).reverse.map some)
                  baseLeft)))
            false rejectTail
      rw [hraw]
      have hrejectCells :
          (false :: rejectTail).map some =
            (configurationFieldBits rejectConfig
              (boolFieldBits acceptHit
                (boolFieldBits rejectHit []))).map some := by
        simpa using
          congrArg (fun bits => bits.map some) hrejectTail.symm
      simp [hrejectCells]
    exact
      CommonGround.SeqComposition.runConfig_reaches_from_move_eq
        (B := RejectConfigAndFinalFlagsScannerDescription)
        (handoffMove := Direction.right)
        hmove
        (by simpa using hreject)
  simpa [ConfigurationsAndFinalFlagsScannerDescription, TmidTape] using
    CommonGround.SeqComposition.seqSubroutine_runConfig_exists
      (A := ConfigurationSuffixScannerDescription)
      (B := RejectConfigAndFinalFlagsScannerDescription)
      (handoffMove := Direction.right)
      configurationSuffixScannerDescription_subroutineReady
      rejectConfigAndFinalFlagsScannerDescription_subroutineReady
      hArun hBReach

theorem run_stageConfigurationsAndFinalFlags_raw_to_handoff_withBase
    (stage : Nat)
    (acceptConfig rejectConfig : MachineDescription.Configuration)
    (acceptHit rejectHit : Bool)
    (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      StageConfigurationsAndFinalFlagsScannerDescription.runConfig steps
          { state := StageConfigurationsAndFinalFlagsScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((List.append (stageNatBits stage)
                  (configurationFieldBits acceptConfig
                    (configurationFieldBits rejectConfig
                      (boolFieldBits acceptHit
                        (boolFieldBits rejectHit []))))).map some) } =
        { state := StageConfigurationsAndFinalFlagsScannerDescription.halt
          tape :=
            (boolFinalHandoffConfigWithBase rejectHit
              (List.append
                ((cellCodeBits (some acceptHit)).reverse.map some)
                (configurationRestoredLeftWithBase rejectConfig
                  (configurationRestoredLeftWithBase acceptConfig
                    (List.append ((stageNatBits stage).reverse.map some)
                      baseLeft))))).tape } := by
  rcases configurationFieldBits_cons_false acceptConfig
      (configurationFieldBits rejectConfig
        (boolFieldBits acceptHit (boolFieldBits rejectHit []))) with
    ⟨acceptTail, hacceptTail⟩
  rcases DovetailStagePrefix.run_nonemptyNatSuffix_raw_to_handoff_withBase
      stage baseLeft false acceptTail with
    ⟨stageSteps, hstage⟩
  let TmidTape : Tape Bool :=
    (DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBase
      stage baseLeft (false :: acceptTail)).tape
  let baseAfterStage : List (Option Bool) :=
    List.append ((stageNatBits stage).reverse.map some) baseLeft
  have hArun :
      DovetailStagePrefix.NonemptyNatSuffixScannerDescription.runConfig
          stageSteps
          { state :=
              DovetailStagePrefix.NonemptyNatSuffixScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((List.append (stageNatBits stage)
                  (configurationFieldBits acceptConfig
                    (configurationFieldBits rejectConfig
                      (boolFieldBits acceptHit
                        (boolFieldBits rejectHit []))))).map some) } =
        { state := DovetailStagePrefix.NonemptyNatSuffixScannerDescription.halt
          tape := TmidTape } := by
    rw [show
        (List.append (stageNatBits stage)
          (configurationFieldBits acceptConfig
            (configurationFieldBits rejectConfig
              (boolFieldBits acceptHit
                (boolFieldBits rejectHit []))))).map some =
          (List.append (stageNatBits stage)
            (false :: acceptTail)).map some by
      rw [hacceptTail]]
    simpa [TmidTape] using hstage
  have hBReach :
      exists nB : Nat,
        ConfigurationsAndFinalFlagsScannerDescription.runConfig nB
            { state := ConfigurationsAndFinalFlagsScannerDescription.start
              tape := Tape.move Direction.right TmidTape } =
          { state := ConfigurationsAndFinalFlagsScannerDescription.halt
            tape :=
              (boolFinalHandoffConfigWithBase rejectHit
                (List.append
                  ((cellCodeBits (some acceptHit)).reverse.map some)
                  (configurationRestoredLeftWithBase rejectConfig
                    (configurationRestoredLeftWithBase acceptConfig
                      baseAfterStage)))).tape } := by
    rcases run_configurationsAndFinalFlags_raw_to_handoff_withBase
        acceptConfig rejectConfig acceptHit rejectHit baseAfterStage with
      ⟨configSteps, hconfigs⟩
    have hmove :
        Tape.move Direction.right TmidTape =
          tapeAtCells baseAfterStage
            ((configurationFieldBits acceptConfig
              (configurationFieldBits rejectConfig
                (boolFieldBits acceptHit
                  (boolFieldBits rejectHit [])))).map some) := by
      have hraw :
          Tape.move Direction.right TmidTape =
            tapeAtCells baseAfterStage
              ((false :: acceptTail).map some) := by
        simpa [TmidTape, baseAfterStage] using
          DovetailStagePrefix.nonemptyNatSuffixHandoffConfigWithBase_move_right
            stage baseLeft false acceptTail
      rw [hraw]
      have hacceptCells :
          (false :: acceptTail).map some =
            (configurationFieldBits acceptConfig
              (configurationFieldBits rejectConfig
                (boolFieldBits acceptHit
                  (boolFieldBits rejectHit [])))).map some := by
        simpa using
          congrArg (fun bits => bits.map some) hacceptTail.symm
      simp [hacceptCells]
    exact
      CommonGround.SeqComposition.runConfig_reaches_from_move_eq
        (B := ConfigurationsAndFinalFlagsScannerDescription)
        (handoffMove := Direction.right)
        hmove
        (by simpa [baseAfterStage] using hconfigs)
  simpa [StageConfigurationsAndFinalFlagsScannerDescription, TmidTape,
    baseAfterStage] using
      CommonGround.SeqComposition.seqSubroutine_runConfig_exists
        (A := DovetailStagePrefix.NonemptyNatSuffixScannerDescription)
        (B := ConfigurationsAndFinalFlagsScannerDescription)
        (handoffMove := Direction.right)
        DovetailStagePrefix.nonemptyNatSuffixScannerDescription_subroutineReady
        configurationsAndFinalFlagsScannerDescription_subroutineReady
        hArun hBReach

theorem run_inputStageConfigurationsAndFinalFlags_raw_to_handoff_withBase
    (input : Word Bool) (stage : Nat)
    (acceptConfig rejectConfig : MachineDescription.Configuration)
    (acceptHit rejectHit : Bool)
    (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      InputStageConfigurationsAndFinalFlagsScannerDescription.runConfig
          steps
          { state :=
              InputStageConfigurationsAndFinalFlagsScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((boolWordFieldBits input
                  (List.append (stageNatBits stage)
                    (configurationFieldBits acceptConfig
                      (configurationFieldBits rejectConfig
                        (boolFieldBits acceptHit
                          (boolFieldBits rejectHit [])))))).map some) } =
        { state :=
            InputStageConfigurationsAndFinalFlagsScannerDescription.halt
          tape :=
            (boolFinalHandoffConfigWithBase rejectHit
              (List.append
                ((cellCodeBits (some acceptHit)).reverse.map some)
                (configurationRestoredLeftWithBase rejectConfig
                  (configurationRestoredLeftWithBase acceptConfig
                    (List.append ((stageNatBits stage).reverse.map some)
                      (cellListCanonicalRestoredLeftWithBase
                        (input.map some) baseLeft)))))).tape } := by
  let stageSuffix : Word Bool :=
    configurationFieldBits acceptConfig
      (configurationFieldBits rejectConfig
        (boolFieldBits acceptHit (boolFieldBits rejectHit [])))
  rcases stageNatBits_cons_false stage with ⟨stageTail, hstageTail⟩
  let inputSuffixTail : Word Bool :=
    List.append stageTail stageSuffix
  rcases run_boolWordSuffix_raw_to_canonical_handoff_withBase
      input baseLeft inputSuffixTail with
    ⟨inputSteps, hinput⟩
  let TmidTape : Tape Bool :=
    (boolWordCanonicalHandoffConfigWithBase input baseLeft
      (false :: inputSuffixTail)).tape
  let baseAfterInput : List (Option Bool) :=
    cellListCanonicalRestoredLeftWithBase (input.map some) baseLeft
  have hArun :
      BoolWordSuffixScannerDescription.runConfig inputSteps
          { state := BoolWordSuffixScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((boolWordFieldBits input
                  (List.append (stageNatBits stage)
                    (configurationFieldBits acceptConfig
                      (configurationFieldBits rejectConfig
                        (boolFieldBits acceptHit
                          (boolFieldBits rejectHit [])))))).map some) } =
        { state := BoolWordSuffixScannerDescription.halt
          tape := TmidTape } := by
    change
      BoolWordSuffixScannerDescription.runConfig inputSteps
          (config 100 baseLeft
            ((boolWordFieldBits input
              (List.append (stageNatBits stage)
                stageSuffix)).map some)) =
        { state := BoolWordSuffixScannerDescription.halt
          tape := TmidTape }
    rw [show
        ((boolWordFieldBits input
          (List.append (stageNatBits stage) stageSuffix)).map some) =
          List.append ((stageNatBits input.length).map some)
            (List.append ((cellsCodeBits (input.map some)).map some)
              (some false :: inputSuffixTail.map some)) by
      rw [hstageTail]
      simp [boolWordFieldBits, cellListFieldBits, inputSuffixTail,
        stageSuffix, List.map_append]]
    simpa [TmidTape, boolWordCanonicalHandoffConfigWithBase] using
      hinput
  have hBReach :
      exists nB : Nat,
        StageConfigurationsAndFinalFlagsScannerDescription.runConfig nB
            { state :=
                StageConfigurationsAndFinalFlagsScannerDescription.start
              tape := Tape.move Direction.right TmidTape } =
          { state := StageConfigurationsAndFinalFlagsScannerDescription.halt
            tape :=
              (boolFinalHandoffConfigWithBase rejectHit
                (List.append
                  ((cellCodeBits (some acceptHit)).reverse.map some)
                  (configurationRestoredLeftWithBase rejectConfig
                    (configurationRestoredLeftWithBase acceptConfig
                      (List.append ((stageNatBits stage).reverse.map some)
                        baseAfterInput))))).tape } := by
    rcases run_stageConfigurationsAndFinalFlags_raw_to_handoff_withBase
        stage acceptConfig rejectConfig acceptHit rejectHit baseAfterInput with
      ⟨stageSteps, hstage⟩
    have hmove :
        Tape.move Direction.right TmidTape =
          tapeAtCells baseAfterInput
            ((List.append (stageNatBits stage) stageSuffix).map some) := by
      have hraw :
          Tape.move Direction.right TmidTape =
            tapeAtCells baseAfterInput
              ((false :: inputSuffixTail).map some) := by
        simpa [TmidTape, baseAfterInput,
          boolWordCanonicalHandoffConfigWithBase] using
          cellListCanonicalHandoffConfigWithBase_move_right
            (input.map some) baseLeft false inputSuffixTail
      rw [hraw]
      have hsuffixCells :
          (false :: inputSuffixTail).map some =
            (List.append (stageNatBits stage) stageSuffix).map some := by
        rw [hstageTail]
        simp [inputSuffixTail, List.map_append]
      simp [hsuffixCells]
    exact
      CommonGround.SeqComposition.runConfig_reaches_from_move_eq
        (B := StageConfigurationsAndFinalFlagsScannerDescription)
        (handoffMove := Direction.right)
        hmove
        (by simpa [baseAfterInput, stageSuffix] using hstage)
  simpa [InputStageConfigurationsAndFinalFlagsScannerDescription,
    TmidTape, baseAfterInput] using
      CommonGround.SeqComposition.seqSubroutine_runConfig_exists
        (A := BoolWordSuffixScannerDescription)
        (B := StageConfigurationsAndFinalFlagsScannerDescription)
        (handoffMove := Direction.right)
        boolWordSuffixScannerDescription_subroutineReady
        stageConfigurationsAndFinalFlagsScannerDescription_subroutineReady
        hArun hBReach

theorem run_markedDovetailLayoutBody_raw_to_handoff_withBase
    (L : MachineDescription.DovetailLayout)
    (baseLeft : List (Option Bool)) :
    exists steps : Nat,
      MarkedDovetailLayoutBodyScannerDescription.runConfig steps
          { state := MarkedDovetailLayoutBodyScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((List.append transitionRemainderBits
                  (boolWordFieldBits L.input
                    (List.append (stageNatBits L.stage)
                      (configurationFieldBits L.acceptConfig
                        (configurationFieldBits L.rejectConfig
                          (boolFieldBits L.acceptHit
                            (boolFieldBits L.rejectHit []))))))).map
                  some) } =
        { state := MarkedDovetailLayoutBodyScannerDescription.halt
          tape :=
            (boolFinalHandoffConfigWithBase L.rejectHit
              (List.append
                ((cellCodeBits (some L.acceptHit)).reverse.map some)
                (configurationRestoredLeftWithBase L.rejectConfig
                  (configurationRestoredLeftWithBase L.acceptConfig
                    (List.append ((stageNatBits L.stage).reverse.map some)
                      (cellListCanonicalRestoredLeftWithBase
                        (L.input.map some)
                        (List.append
                          (transitionRemainderBits.reverse.map some)
                          baseLeft))))))).tape } := by
  let inputSuffix : Word Bool :=
    List.append (stageNatBits L.stage)
      (configurationFieldBits L.acceptConfig
        (configurationFieldBits L.rejectConfig
          (boolFieldBits L.acceptHit
            (boolFieldBits L.rejectHit []))))
  rcases cellListFieldBits_cons_false (L.input.map some)
      inputSuffix with
    ⟨inputTail, hinputTail⟩
  rcases run_transitionRemainderPrefix_raw_to_handoff_withBase
      baseLeft false inputTail with
    ⟨transitionSteps, htransition⟩
  let TmidTape : Tape Bool :=
    (transitionRemainderHandoffConfigWithBase baseLeft
      (false :: inputTail)).tape
  let baseAfterTransition : List (Option Bool) :=
    List.append (transitionRemainderBits.reverse.map some) baseLeft
  have hArun :
      TransitionRemainderPrefixScannerDescription.runConfig
          transitionSteps
          { state := TransitionRemainderPrefixScannerDescription.start
            tape :=
              tapeAtCells baseLeft
                ((List.append transitionRemainderBits
                  (boolWordFieldBits L.input inputSuffix)).map some) } =
        { state := TransitionRemainderPrefixScannerDescription.halt
          tape := TmidTape } := by
    rw [show
        (List.append transitionRemainderBits
          (boolWordFieldBits L.input inputSuffix)).map some =
          (some false :: some false :: some true ::
            some false :: inputTail.map some) by
      have hinputBits :
          boolWordFieldBits L.input inputSuffix = false :: inputTail := by
        simpa [boolWordFieldBits] using hinputTail
      rw [hinputBits]
      simp [transitionRemainderBits]]
    simpa [TmidTape] using htransition
  have hBReach :
      exists nB : Nat,
        InputStageConfigurationsAndFinalFlagsScannerDescription.runConfig nB
            { state :=
                InputStageConfigurationsAndFinalFlagsScannerDescription.start
              tape := Tape.move Direction.right TmidTape } =
          { state :=
              InputStageConfigurationsAndFinalFlagsScannerDescription.halt
            tape :=
              (boolFinalHandoffConfigWithBase L.rejectHit
                (List.append
                  ((cellCodeBits (some L.acceptHit)).reverse.map some)
                  (configurationRestoredLeftWithBase L.rejectConfig
                    (configurationRestoredLeftWithBase L.acceptConfig
                      (List.append ((stageNatBits L.stage).reverse.map some)
                        (cellListCanonicalRestoredLeftWithBase
                          (L.input.map some)
                          baseAfterTransition)))))).tape } := by
    rcases
        run_inputStageConfigurationsAndFinalFlags_raw_to_handoff_withBase
          L.input L.stage L.acceptConfig L.rejectConfig
          L.acceptHit L.rejectHit baseAfterTransition with
      ⟨inputSteps, hinput⟩
    have hmove :
        Tape.move Direction.right TmidTape =
          tapeAtCells baseAfterTransition
            ((boolWordFieldBits L.input inputSuffix).map some) := by
      have hraw :
          Tape.move Direction.right TmidTape =
            tapeAtCells baseAfterTransition
              ((false :: inputTail).map some) := by
        simpa [TmidTape, baseAfterTransition] using
          transitionRemainderHandoffConfigWithBase_move_right
            baseLeft false inputTail
      rw [hraw]
      have hinputCells :
          (false :: inputTail).map some =
            (boolWordFieldBits L.input inputSuffix).map some := by
        simpa using
          congrArg (fun bits => bits.map some) hinputTail.symm
      simp [hinputCells]
    exact
      CommonGround.SeqComposition.runConfig_reaches_from_move_eq
        (B := InputStageConfigurationsAndFinalFlagsScannerDescription)
        (handoffMove := Direction.right)
        hmove
        (by simpa [baseAfterTransition, inputSuffix] using hinput)
  simpa [MarkedDovetailLayoutBodyScannerDescription, TmidTape,
    baseAfterTransition] using
      CommonGround.SeqComposition.seqSubroutine_runConfig_exists
        (A := TransitionRemainderPrefixScannerDescription)
        (B := InputStageConfigurationsAndFinalFlagsScannerDescription)
        (handoffMove := Direction.right)
        transitionRemainderPrefixScannerDescription_subroutineReady
        inputStageConfigurationsAndFinalFlagsScannerDescription_subroutineReady
        hArun hBReach

theorem run_markedDovetailLayoutBody_return_to_checkedHandoff
    (L : MachineDescription.DovetailLayout) :
    exists steps : Nat,
      (MachineDescription.seqSubroutine
          MarkedDovetailLayoutBodyScannerDescription
          ReturnToFirstMarkerDescription
          Direction.right).runConfig steps
          { state :=
              (MachineDescription.seqSubroutine
                MarkedDovetailLayoutBodyScannerDescription
                ReturnToFirstMarkerDescription
                Direction.right).start
            tape :=
              tapeAtCells [none]
                ((markedDovetailLayoutBodyBits L).map some) } =
        { state :=
            (MachineDescription.seqSubroutine
              MarkedDovetailLayoutBodyScannerDescription
              ReturnToFirstMarkerDescription
              Direction.right).halt
          tape :=
            restoredCheckedHandoffTapeFromTail
              (markedDovetailLayoutBodyRestoredBitsRev L).reverse } := by
  rcases run_markedDovetailLayoutBody_raw_to_handoff_withBase
      L [none] with
    ⟨bodySteps, hbody⟩
  let TmidTape : Tape Bool :=
    (boolFinalHandoffConfigWithBase L.rejectHit
      (List.append
        ((cellCodeBits (some L.acceptHit)).reverse.map some)
        (configurationRestoredLeftWithBase L.rejectConfig
          (configurationRestoredLeftWithBase L.acceptConfig
            (List.append ((stageNatBits L.stage).reverse.map some)
              (cellListCanonicalRestoredLeftWithBase
                (L.input.map some)
                (List.append (transitionRemainderBits.reverse.map some)
                  [none]))))))).tape
  have hArun :
      MarkedDovetailLayoutBodyScannerDescription.runConfig bodySteps
          { state := MarkedDovetailLayoutBodyScannerDescription.start
            tape :=
              tapeAtCells [none]
                ((markedDovetailLayoutBodyBits L).map some) } =
        { state := MarkedDovetailLayoutBodyScannerDescription.halt
          tape := TmidTape } := by
    simpa [markedDovetailLayoutBodyBits, TmidTape] using hbody
  have hBReach :
      exists nB : Nat,
        ReturnToFirstMarkerDescription.runConfig nB
            { state := ReturnToFirstMarkerDescription.start
              tape := Tape.move Direction.right TmidTape } =
          { state := ReturnToFirstMarkerDescription.halt
            tape :=
              restoredCheckedHandoffTapeFromTail
                (markedDovetailLayoutBodyRestoredBitsRev L).reverse } := by
    have hmove :
        Tape.move Direction.right TmidTape =
          tapeAtCells
            (List.append
              ((markedDovetailLayoutBodyRestoredBitsRev L).map some)
              [none])
            [none] := by
      have hraw :
          Tape.move Direction.right TmidTape =
            tapeAtCells
              (finalHitFlagsRestoredLeftWithBase L.acceptHit L.rejectHit
                (configurationRestoredLeftWithBase L.rejectConfig
                  (configurationRestoredLeftWithBase L.acceptConfig
                    (List.append
                      ((stageNatBits L.stage).reverse.map some)
                      (cellListCanonicalRestoredLeftWithBase
                        (L.input.map some)
                        (List.append
                          (transitionRemainderBits.reverse.map some)
                          [none]))))))
              [] := by
        simpa [TmidTape, finalHitFlagsRestoredLeftWithBase] using
          boolFinalHandoffConfigWithBase_move_right
            L.rejectHit
            (List.append
              ((cellCodeBits (some L.acceptHit)).reverse.map some)
              (configurationRestoredLeftWithBase L.rejectConfig
                (configurationRestoredLeftWithBase L.acceptConfig
                  (List.append
                    ((stageNatBits L.stage).reverse.map some)
                    (cellListCanonicalRestoredLeftWithBase
                      (L.input.map some)
                      (List.append
                        (transitionRemainderBits.reverse.map some)
                        [none]))))))
      rw [hraw]
      rw [← markedDovetailLayoutBodyRestoredBitsRev_map_some_withMarker L]
      rfl
    exact
      CommonGround.SeqComposition.runConfig_reaches_from_move_eq
        (B := ReturnToFirstMarkerDescription)
        (handoffMove := Direction.right)
        hmove
        (by
          simpa [ReturnToFirstMarkerDescription, config] using
            run_returnToFirstMarker_from_reversedBits
              (markedDovetailLayoutBodyRestoredBitsRev L))
  simpa [TmidTape] using
    CommonGround.SeqComposition.seqSubroutine_runConfig_exists
      (A := MarkedDovetailLayoutBodyScannerDescription)
      (B := ReturnToFirstMarkerDescription)
      (handoffMove := Direction.right)
      markedDovetailLayoutBodyScannerDescription_subroutineReady
      returnToFirstMarkerDescription_subroutineReady
      hArun hBReach

theorem run_checkedDovetailLayoutScanner_raw_to_checkedHandoff
    (L : MachineDescription.DovetailLayout) :
    exists steps : Nat,
      CheckedDovetailLayoutScannerDescription.runConfig steps
          { state := CheckedDovetailLayoutScannerDescription.start
            tape := tapeAtCells [] ((dovetailLayoutFieldBits L []).map some) } =
        { state := CheckedDovetailLayoutScannerDescription.halt
          tape :=
            restoredCheckedHandoffTapeFromTail
              (markedDovetailLayoutBodyRestoredBitsRev L).reverse } := by
  rcases markedDovetailLayoutBodyBits_cons_false L with
    ⟨bodyTail, hbodyTail⟩
  let TmidTape : Tape Bool :=
    (config MarkFirstTransitionBitDescription.halt []
      (none :: some false :: bodyTail.map some)).tape
  have hArun :
      MarkFirstTransitionBitDescription.runConfig 2
          { state := MarkFirstTransitionBitDescription.start
            tape :=
              tapeAtCells []
                ((dovetailLayoutFieldBits L []).map some) } =
        { state := MarkFirstTransitionBitDescription.halt
          tape := TmidTape } := by
    rw [dovetailLayoutFieldBits_nil_eq_first_body L]
    rw [hbodyTail]
    simpa [TmidTape] using
      run_markFirstTransitionBit_raw bodyTail
  have hBReach :
      exists nB : Nat,
        (MachineDescription.seqSubroutine
          MarkedDovetailLayoutBodyScannerDescription
          ReturnToFirstMarkerDescription
          Direction.right).runConfig nB
            { state :=
                (MachineDescription.seqSubroutine
                  MarkedDovetailLayoutBodyScannerDescription
                  ReturnToFirstMarkerDescription
                  Direction.right).start
              tape := Tape.move Direction.right TmidTape } =
          { state :=
              (MachineDescription.seqSubroutine
                MarkedDovetailLayoutBodyScannerDescription
                ReturnToFirstMarkerDescription
                Direction.right).halt
            tape :=
              restoredCheckedHandoffTapeFromTail
                (markedDovetailLayoutBodyRestoredBitsRev L).reverse } := by
    rcases run_markedDovetailLayoutBody_return_to_checkedHandoff L with
      ⟨bodyReturnSteps, hbodyReturn⟩
    have hmove :
        Tape.move Direction.right TmidTape =
          tapeAtCells [none]
            ((markedDovetailLayoutBodyBits L).map some) := by
      simp [TmidTape, hbodyTail, config, tapeAtCells, Tape.move,
        Tape.moveRight]
    exact
      CommonGround.SeqComposition.runConfig_reaches_from_move_eq
        (B :=
          MachineDescription.seqSubroutine
            MarkedDovetailLayoutBodyScannerDescription
            ReturnToFirstMarkerDescription
            Direction.right)
        (handoffMove := Direction.right)
        hmove
        hbodyReturn
  simpa [CheckedDovetailLayoutScannerDescription, TmidTape] using
    CommonGround.SeqComposition.seqSubroutine_runConfig_exists
      (A := MarkFirstTransitionBitDescription)
      (B :=
        MachineDescription.seqSubroutine
          MarkedDovetailLayoutBodyScannerDescription
          ReturnToFirstMarkerDescription
          Direction.right)
      (handoffMove := Direction.right)
      markFirstTransitionBitDescription_subroutineReady
      (MachineDescription.seqSubroutine_subroutineReady
        markedDovetailLayoutBodyScannerDescription_subroutineReady
        returnToFirstMarkerDescription_subroutineReady)
      hArun hBReach

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
