import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTableChecks
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeTactic

set_option doc.verso true

/-!
# Exact guarded-tape serialization kernel for #18 egress

The guarded physical representation retains the stored left and right tape
windows needed by the exact configuration encoding.  This module begins the
finite serializer directly on that raw representation.

The first phase below consumes the left guard cell and all genuine stored
left cells, emits one encoded {lit}`tick` per genuine cell followed by encoded
{lit}`done`, and halts on the first bit of the encoded head cell.  Its tape-2 output
is therefore exactly {lit}`encodeCodeWordAsInput (encodeNat T.left.length)`; the
representation guard is not counted.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace GuardedEgress
namespace ExactTapeSerializer

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace LeftLength

@[simp] abbrev scanState : Nat := 2
@[simp] abbrev afterFalseState : Nat := 3
@[simp] abbrev afterTrueState : Nat := 4
@[simp] abbrev tickSecondState : Nat := 5
@[simp] abbrev tickThirdState : Nat := 6
@[simp] abbrev tickFourthState : Nat := 7
@[simp] abbrev doneSecondState : Nat := 8
@[simp] abbrev doneThirdState : Nat := 9
@[simp] abbrev doneFourthState : Nat := 10
@[simp] abbrev haltState : Nat := 99

/-- Finite left-window length emitter.  Tape 0 is the raw logical-tape bit
stream, tape 1 is untouched, and tape 2 receives the encoded natural. -/
def rows : List Transition :=
  [ row 0 (some false) none none keepR keepS keepS 1
  , row 1 (some false) none none keepR keepS keepS scanState

  , row scanState (some false) none none
      keepR keepS keepS afterFalseState
  , row scanState (some true) none none
      keepR keepS keepS afterTrueState

  , row afterFalseState (some false) none none
      keepS keepS (writeR (some false)) tickSecondState
  , row afterFalseState (some true) none none
      keepS keepS (writeR (some false)) tickSecondState
  , row afterTrueState (some false) none none
      keepS keepS (writeR (some false)) tickSecondState
  , row afterTrueState (some true) none none
      keepS keepS (writeR (some false)) doneSecondState

  , row tickSecondState (some false) none none
      keepS keepS (writeR (some false)) tickThirdState
  , row tickSecondState (some true) none none
      keepS keepS (writeR (some false)) tickThirdState
  , row tickThirdState (some false) none none
      keepS keepS (writeR (some true)) tickFourthState
  , row tickThirdState (some true) none none
      keepS keepS (writeR (some true)) tickFourthState
  , row tickFourthState (some false) none none
      keepR keepS (writeR (some false)) scanState
  , row tickFourthState (some true) none none
      keepR keepS (writeR (some false)) scanState

  , row doneSecondState (some true) none none
      keepS keepS (writeR (some false)) doneThirdState
  , row doneThirdState (some true) none none
      keepS keepS (writeR (some true)) doneFourthState
  , row doneFourthState (some true) none none
      keepR keepS (writeR (some true)) haltState ]

def description : Description :=
  ThreeTape.description 100 0 haltState rows

theorem description_wellFormed : description.WellFormed :=
  structuredDescription_wellFormed_of_bool description (by decide)

theorem description_haltTransitionFree :
    description.HaltTransitionFree :=
  structuredDescription_haltTransitionFree_of_bool description (by decide)

theorem description_supportsReadWriteRows3 :
    SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

/-! Exact phase shapes. -/

def headMarkerBits : Word Bool := [true, true]

@[simp] theorem tickBits_eq_exactSerializer :
    tickBits = [false, false, true, false] := by
  rfl

@[simp] theorem doneBits_eq_exactSerializer :
    doneBits = [false, false, true, true] := by
  rfl

@[simp] theorem encodeTick_eq_exactSerializer :
    encodeCodeSymbolAsInput MachineCodeSymbol.tick =
      [false, false, true, false] := by
  rfl

@[simp] theorem encodeDone_eq_exactSerializer :
    encodeCodeSymbolAsInput MachineCodeSymbol.done =
      [false, false, true, true] := by
  rfl

def sourceTape
    (baseLeft leftCells : List (Option Bool)) (tail : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells baseLeft
    (List.append
      ((List.append
        (logicalCellListBits (none :: leftCells))
        (List.append headMarkerBits tail)).map some)
      (none :: padding))

def scanTape
    (baseLeft : List (Option Bool))
    (consumed : Word Bool) (remaining : List (Option Bool))
    (tail : Word Bool) (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (consumed.reverse.map some) baseLeft)
    (List.append
      ((List.append (logicalCellListBits remaining)
        (List.append headMarkerBits tail)).map some)
      (none :: padding))

def finalSourceTape
    (baseLeft leftCells : List (Option Bool)) (tail : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      ((List.append
        (logicalCellListBits (none :: leftCells))
        headMarkerBits).reverse.map some)
      baseLeft)
    (List.append (tail.map some) (none :: padding))

def outputTape (leftLength : Nat) : Tape Bool :=
  tapeAtCells
    ((stageNatBits leftLength).reverse.map some) []

def initialConfig
    (baseLeft leftCells : List (Option Bool)) (tail : Word Bool)
    (padding : List (Option Bool)) : Structured.Configuration :=
  ThreeTape.config 0
    (sourceTape baseLeft leftCells tail padding) Tape.blank Tape.blank

def scanConfig
    (baseLeft : List (Option Bool))
    (consumed : Word Bool) (remaining : List (Option Bool))
    (tail emitted : Word Bool) (padding : List (Option Bool)) :
    Structured.Configuration :=
  ThreeTape.config scanState
    (scanTape baseLeft consumed remaining tail padding)
    Tape.blank
    (tapeAtCells (emitted.reverse.map some) [])

def finalConfig
    (baseLeft leftCells : List (Option Bool)) (tail : Word Bool)
    (padding : List (Option Bool)) : Structured.Configuration :=
  ThreeTape.config haltState
    (finalSourceTape baseLeft leftCells tail padding)
    Tape.blank
    (outputTape leftCells.length)

/-! Exact table runs. -/

theorem description_run_enter
    (baseLeft leftCells : List (Option Bool)) (tail : Word Bool)
    (padding : List (Option Bool)) :
    description.runConfig 2
        (initialConfig baseLeft leftCells tail padding) =
      scanConfig baseLeft (logicalCellBits none)
        leftCells tail [] padding := by
  cases leftCells with
  | nil =>
      three_tape_step [description, rows, initialConfig, sourceTape,
        scanConfig, scanTape, headMarkerBits, logicalCellListBits,
        logicalCellBits, tapeAtCells]
  | cons cell rest =>
      cases cell with
      | none =>
          three_tape_step [description, rows, initialConfig, sourceTape,
            scanConfig, scanTape, headMarkerBits, logicalCellListBits,
            logicalCellBits, tapeAtCells]
      | some bit =>
          cases bit <;>
            three_tape_step [description, rows, initialConfig, sourceTape,
              scanConfig, scanTape, headMarkerBits, logicalCellListBits,
              logicalCellBits, tapeAtCells]

theorem description_run_cell
    (baseLeft : List (Option Bool))
    (consumed emitted tail : Word Bool)
    (cell : Option Bool) (remaining : List (Option Bool))
    (padding : List (Option Bool)) :
    description.runConfig 5
        (scanConfig baseLeft consumed (cell :: remaining)
          tail emitted padding) =
      scanConfig baseLeft
        (List.append consumed (logicalCellBits cell))
        remaining tail (List.append emitted tickBits) padding := by
  cases cell with
  | none =>
      cases remaining with
      | nil =>
          three_tape_step [description, rows, scanConfig, scanTape,
            scanState, afterFalseState, tickSecondState, tickThirdState,
            tickFourthState, headMarkerBits, tickBits,
            logicalCellListBits, logicalCellBits, tapeAtCells,
            List.reverse_append]
      | cons next rest =>
          cases next with
          | none =>
              three_tape_step [description, rows, scanConfig, scanTape,
                scanState, afterFalseState, tickSecondState,
                tickThirdState, tickFourthState, headMarkerBits, tickBits,
                logicalCellListBits, logicalCellBits, tapeAtCells,
                List.reverse_append]
          | some nextBit =>
              cases nextBit <;>
                three_tape_step [description, rows, scanConfig, scanTape,
                  scanState, afterFalseState, tickSecondState,
                  tickThirdState, tickFourthState, headMarkerBits, tickBits,
                  logicalCellListBits, logicalCellBits, tapeAtCells,
                  List.reverse_append]
  | some bit =>
      cases bit with
      | false =>
          cases remaining with
          | nil =>
              three_tape_step [description, rows, scanConfig, scanTape,
                scanState, afterFalseState, tickSecondState,
                tickThirdState, tickFourthState, headMarkerBits, tickBits,
                logicalCellListBits, logicalCellBits, tapeAtCells,
                List.reverse_append]
          | cons next rest =>
              cases next with
              | none =>
                  three_tape_step [description, rows, scanConfig, scanTape,
                    scanState, afterFalseState, tickSecondState,
                    tickThirdState, tickFourthState, headMarkerBits,
                    tickBits, logicalCellListBits, logicalCellBits,
                    tapeAtCells, List.reverse_append]
              | some nextBit =>
                  cases nextBit <;>
                    three_tape_step [description, rows, scanConfig, scanTape,
                      scanState, afterFalseState, tickSecondState,
                      tickThirdState, tickFourthState, headMarkerBits,
                      tickBits, logicalCellListBits, logicalCellBits,
                      tapeAtCells, List.reverse_append]
      | true =>
          cases remaining with
          | nil =>
              three_tape_step [description, rows, scanConfig, scanTape,
                scanState, afterTrueState, tickSecondState,
                tickThirdState, tickFourthState, headMarkerBits, tickBits,
                logicalCellListBits, logicalCellBits, tapeAtCells,
                List.reverse_append]
          | cons next rest =>
              cases next with
              | none =>
                  three_tape_step [description, rows, scanConfig, scanTape,
                    scanState, afterTrueState, tickSecondState,
                    tickThirdState, tickFourthState, headMarkerBits,
                    tickBits, logicalCellListBits, logicalCellBits,
                    tapeAtCells, List.reverse_append]
              | some nextBit =>
                  cases nextBit <;>
                    three_tape_step [description, rows, scanConfig, scanTape,
                      scanState, afterTrueState, tickSecondState,
                      tickThirdState, tickFourthState, headMarkerBits,
                      tickBits, logicalCellListBits, logicalCellBits,
                      tapeAtCells, List.reverse_append]

theorem description_run_finish
    (baseLeft : List (Option Bool))
    (consumed emitted : Word Bool) (first : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    description.runConfig 5
        (scanConfig baseLeft consumed []
          (first :: rest) emitted padding) =
      ThreeTape.config haltState
        (tapeAtCells
          (List.append
            ((List.append consumed headMarkerBits).reverse.map some)
            baseLeft)
          (List.append ((first :: rest).map some) (none :: padding)))
        Tape.blank
        (tapeAtCells
          ((List.append emitted doneBits).reverse.map some) []) := by
  cases first <;>
    three_tape_step [description, rows, scanConfig, scanTape,
      scanState, afterTrueState, doneSecondState, doneThirdState,
      doneFourthState, haltState, headMarkerBits, doneBits,
      logicalCellListBits, logicalCellBits, tapeAtCells,
      List.reverse_append]

def scanTargetConfig
    (baseLeft : List (Option Bool))
    (consumed : Word Bool) (remaining : List (Option Bool))
    (first : Bool) (rest emitted : Word Bool)
    (padding : List (Option Bool)) : Structured.Configuration :=
  ThreeTape.config haltState
    (tapeAtCells
      (List.append
        ((List.append
          (List.append consumed (logicalCellListBits remaining))
          headMarkerBits).reverse.map some)
        baseLeft)
      (List.append ((first :: rest).map some) (none :: padding)))
    Tape.blank
    (tapeAtCells
      ((List.append emitted
        (stageNatBits remaining.length)).reverse.map some) [])

theorem description_run_scan
    (baseLeft : List (Option Bool))
    (consumed : Word Bool) (remaining : List (Option Bool))
    (first : Bool) (rest emitted : Word Bool)
    (padding : List (Option Bool)) :
    description.runConfig (5 * remaining.length + 5)
        (scanConfig baseLeft consumed remaining
          (first :: rest) emitted padding) =
      scanTargetConfig baseLeft consumed remaining
        first rest emitted padding := by
  induction remaining generalizing consumed emitted with
  | nil =>
      simpa [scanTargetConfig, stageNatBits_zero, doneBits,
        logicalCellListBits, List.append_assoc] using
        description_run_finish baseLeft consumed emitted
          first rest padding
  | cons cell remaining ih =>
      rw [show 5 * (cell :: remaining).length + 5 =
          5 + (5 * remaining.length + 5) by
        simp
        lia]
      rw [Description.runConfig_add]
      rw [description_run_cell]
      have hrun := ih
        (List.append consumed (logicalCellBits cell))
        (List.append emitted tickBits)
      rw [hrun]
      cases cell with
      | none =>
          simp [scanTargetConfig, logicalCellListBits,
            logicalCellBits, stageNatBits_succ, tickBits,
            List.reverse_append, List.append_assoc]
      | some bit =>
          cases bit <;>
            simp [scanTargetConfig, logicalCellListBits,
              logicalCellBits, stageNatBits_succ, tickBits,
              List.reverse_append, List.append_assoc]

theorem description_run
    (baseLeft leftCells : List (Option Bool))
    (first : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    description.runConfig (5 * leftCells.length + 7)
        (initialConfig baseLeft leftCells
          (first :: rest) padding) =
      finalConfig baseLeft leftCells (first :: rest) padding := by
  rw [show 5 * leftCells.length + 7 =
      2 + (5 * leftCells.length + 5) by lia]
  rw [Description.runConfig_add]
  rw [description_run_enter]
  rw [description_run_scan]
  simp [scanTargetConfig, finalConfig, finalSourceTape, outputTape,
    logicalCellListBits, List.reverse_append, List.append_assoc]

theorem description_haltsWithTapes
    (baseLeft leftCells : List (Option Bool))
    (first : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    description.HaltsWithTapes
      (initialConfig baseLeft leftCells (first :: rest) padding)
      (finalConfig baseLeft leftCells (first :: rest) padding).tapes := by
  refine ⟨5 * leftCells.length + 7, ?_⟩
  simpa [finalConfig, description, ThreeTape.description] using
    description_run baseLeft leftCells first rest padding

end LeftLength

end ExactTapeSerializer
end GuardedEgress
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
