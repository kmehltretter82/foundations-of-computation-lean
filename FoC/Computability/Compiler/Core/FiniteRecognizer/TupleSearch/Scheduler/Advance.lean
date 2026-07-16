import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.SplitLayout
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.Basic
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.RestagedEdits

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.Advance

open Languages
open Scheduler.SplitLayout
open ExactFuel.StrictProbe

namespace ExhaustedSplitReset

inductive Control where
  | seekUsed
  | seekMarker
  | inspectDone
  | inspectPred
  | writeMarker
  | writeTick
  | atMarker
  | returnDone
  | returnMarker
  | halt
deriving DecidableEq

namespace Control

def finite : Foundation.FiniteType Control where
  elems := [.seekUsed, .seekMarker, .inspectDone, .inspectPred,
    .writeMarker, .writeTick, .atMarker, .returnDone,
    .returnMarker, .halt]
  complete := by
    intro control
    cases control <;> simp

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .seekUsed, some .tick =>
      some (some .tick, Direction.right, .seekUsed)
  | .seekUsed, some .done =>
      some (some .done, Direction.right, .seekMarker)
  | .seekMarker, some .transition =>
      some (some .transition, Direction.left, .inspectDone)
  | .inspectDone, some .done =>
      some (some .done, Direction.left, .inspectPred)
  | .inspectPred, some .tick =>
      some (some .done, Direction.right, .writeMarker)
  | .inspectPred, read =>
      some (read, Direction.right, .returnDone)
  | .writeMarker, some .done =>
      some (some .transition, Direction.right, .writeTick)
  | .writeTick, some .transition =>
      some (some .tick, Direction.left, .atMarker)
  | .atMarker, some .transition =>
      some (some .transition, Direction.left, .inspectDone)
  | .returnDone, some .done =>
      some (some .done, Direction.right, .returnMarker)
  | .returnMarker, some .transition =>
      some (some .transition, Direction.right, .halt)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .seekUsed
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def ticks (count : Nat) : Word MachineCodeSymbol :=
  List.replicate count MachineCodeSymbol.tick

theorem encodeNat_eq_ticks_done (count : Nat) :
    MachineDescription.encodeNat count =
      List.append (ticks count) [MachineCodeSymbol.done] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [MachineDescription.encodeNat, ticks, List.replicate_succ, ih]

def config (state : Control) (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := state, tape := tape }

def sourceConfig (used : Nat) (baseRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .seekUsed
    (SerializedShift.cursorTape (MachineCodeSymbol.done :: baseRev)
      (encodeSplitAppend used 0 suffix))

def seekTape (remaining crossed baseRev suffix : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  SerializedShift.cursorTape
    (List.append crossed
      (MachineCodeSymbol.done :: baseRev))
    (List.append remaining
      (MachineCodeSymbol.done :: splitMarker ::
        MachineCodeSymbol.done :: suffix))

def seekConfig (remaining crossed baseRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .seekUsed (seekTape remaining crossed baseRev suffix)

def markerTape (remaining moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  { left := some MachineCodeSymbol.done ::
      List.append ((ticks remaining).map some)
        (some MachineCodeSymbol.done :: baseRev.map some)
    head := some splitMarker
    right := List.append ((ticks moved).map some)
      (some MachineCodeSymbol.done :: suffix.map some) }

def markerConfig (state : Control) (remaining moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config state (markerTape remaining moved baseRev suffix)

def doneTape (remaining moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  { left := List.append ((ticks remaining).map some)
      (some MachineCodeSymbol.done :: baseRev.map some)
    head := some MachineCodeSymbol.done
    right := some splitMarker ::
      List.append ((ticks moved).map some)
        (some MachineCodeSymbol.done :: suffix.map some) }

def doneConfig (remaining moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .inspectDone (doneTape remaining moved baseRev suffix)

def targetConfig (used : Nat) (baseRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .halt
    (SerializedShift.cursorTape
      (splitMarker :: MachineCodeSymbol.done ::
        MachineCodeSymbol.done :: baseRev)
      (MachineDescription.encodeNatAppend used suffix))

theorem seek_tick_step (remaining crossed baseRev suffix :
    Word MachineCodeSymbol) :
    machine.stepConfig
        (seekConfig (MachineCodeSymbol.tick :: remaining)
          crossed baseRev suffix) =
      some (seekConfig remaining
        (MachineCodeSymbol.tick :: crossed) baseRev suffix) := by
  cases remaining <;> cases crossed <;> cases baseRev <;> cases suffix <;>
    rfl

theorem seek_ticks_run_exact (remaining crossed baseRev suffix :
    Word MachineCodeSymbol)
    (hticks : ∀ token, List.Mem token remaining ->
      token = MachineCodeSymbol.tick) :
    machine.runConfigExact? remaining.length
        (seekConfig remaining crossed baseRev suffix) =
      some (seekConfig []
        (List.append remaining.reverse crossed) baseRev suffix) := by
  induction remaining generalizing crossed with
  | nil => rfl
  | cons current rest ih =>
      have hcurrent : current = MachineCodeSymbol.tick :=
        hticks current (List.Mem.head rest)
      subst current
      have hrest : ∀ token, List.Mem token rest ->
          token = MachineCodeSymbol.tick := by
        intro token htoken
        exact hticks token (List.Mem.tail MachineCodeSymbol.tick htoken)
      change machine.runConfigExact? (rest.length + 1)
        (seekConfig (MachineCodeSymbol.tick :: rest)
          crossed baseRev suffix) = _
      rw [TuringMachine.runConfigExact?]
      rw [seek_tick_step]
      simp only
      rw [ih (MachineCodeSymbol.tick :: crossed) hrest]
      simp [List.reverse_cons, List.append_assoc]

theorem seek_to_done_exact (used : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? used
        (sourceConfig used baseRev suffix) =
      some (seekConfig [] (ticks used) baseRev suffix) := by
  have hsource :
      sourceConfig used baseRev suffix =
        seekConfig (ticks used) [] baseRev suffix := by
    simp [sourceConfig, seekConfig, seekTape, encodeSplitAppend,
      encodeNat_eq_ticks_done, MachineDescription.encodeNatAppend,
      config, SerializedShift.cursorTape, ticks, splitMarker,
      List.map_append, List.append_assoc]
  rw [hsource]
  simpa [ticks] using
    (seek_ticks_run_exact (ticks used) [] baseRev suffix (by
      intro token htoken
      exact List.eq_of_mem_replicate htoken))

theorem seek_done_step (used : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig (seekConfig [] (ticks used) baseRev suffix) =
      some (markerConfig .seekMarker used 0 baseRev suffix) := by
  cases used <;> cases baseRev <;> cases suffix <;>
    simp [TuringMachine.stepConfig, machine, transition,
      seekConfig, seekTape, markerConfig, markerTape, config,
      ticks, splitMarker, SerializedShift.cursorTape,
      Tape.read, Tape.write, Tape.move, Tape.moveRight,
      List.replicate_succ, List.map_append, List.append_assoc]

theorem seek_marker_step (used : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig (markerConfig .seekMarker used 0 baseRev suffix) =
      some (doneConfig used 0 baseRev suffix) := by
  cases used <;> cases baseRev <;> cases suffix <;>
    simp [TuringMachine.stepConfig, machine, transition,
      markerConfig, markerTape, doneConfig, doneTape, config,
      ticks, splitMarker, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, List.replicate_succ, List.map_append,
      List.append_assoc]

theorem enter_marker_exact (used : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (seekConfig [] (ticks used) baseRev suffix) =
      some (doneConfig used 0 baseRev suffix) := by
  rw [TuringMachine.runConfigExact?]
  rw [seek_done_step]
  simp only
  rw [TuringMachine.runConfigExact?]
  rw [seek_marker_step]
  rfl

def predTickTape (remaining moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  { left := List.append ((ticks remaining).map some)
      (some MachineCodeSymbol.done :: baseRev.map some)
    head := some MachineCodeSymbol.tick
    right := some MachineCodeSymbol.done :: some splitMarker ::
      List.append ((ticks moved).map some)
        (some MachineCodeSymbol.done :: suffix.map some) }

def predTickConfig (remaining moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .inspectPred (predTickTape remaining moved baseRev suffix)

def writeMarkerTape (remaining moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  { left := some MachineCodeSymbol.done ::
      List.append ((ticks remaining).map some)
        (some MachineCodeSymbol.done :: baseRev.map some)
    head := some MachineCodeSymbol.done
    right := some splitMarker ::
      List.append ((ticks moved).map some)
        (some MachineCodeSymbol.done :: suffix.map some) }

def writeMarkerConfig (remaining moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .writeMarker (writeMarkerTape remaining moved baseRev suffix)

def writeTickTape (remaining moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  { left := some splitMarker :: some MachineCodeSymbol.done ::
      List.append ((ticks remaining).map some)
        (some MachineCodeSymbol.done :: baseRev.map some)
    head := some splitMarker
    right := List.append ((ticks moved).map some)
      (some MachineCodeSymbol.done :: suffix.map some) }

def writeTickConfig (remaining moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .writeTick (writeTickTape remaining moved baseRev suffix)

theorem inspect_done_tick_step (remaining moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (doneConfig (remaining + 1) moved baseRev suffix) =
      some (predTickConfig remaining moved baseRev suffix) := by
  cases remaining <;> cases moved <;> cases baseRev <;> cases suffix <;>
    simp [TuringMachine.stepConfig, machine, transition,
      doneConfig, doneTape, predTickConfig, predTickTape, config,
      ticks, splitMarker, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, List.replicate_succ, List.map_append,
      List.append_assoc]

theorem pred_tick_step (remaining moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig (predTickConfig remaining moved baseRev suffix) =
      some (writeMarkerConfig remaining moved baseRev suffix) := by
  cases remaining <;> cases moved <;> cases baseRev <;> cases suffix <;>
    simp [TuringMachine.stepConfig, machine, transition,
      predTickConfig, predTickTape, writeMarkerConfig,
      writeMarkerTape, config, ticks, splitMarker, Tape.read,
      Tape.write, Tape.move, Tape.moveRight, List.replicate_succ,
      List.map_append, List.append_assoc]

theorem write_marker_step (remaining moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig (writeMarkerConfig remaining moved baseRev suffix) =
      some (writeTickConfig remaining moved baseRev suffix) := by
  cases remaining <;> cases moved <;> cases baseRev <;> cases suffix <;>
    simp [TuringMachine.stepConfig, machine, transition,
      writeMarkerConfig, writeMarkerTape, writeTickConfig,
      writeTickTape, config, ticks, splitMarker, Tape.read,
      Tape.write, Tape.move, Tape.moveRight, List.replicate_succ,
      List.map_append, List.append_assoc]

theorem write_tick_step (remaining moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig (writeTickConfig remaining moved baseRev suffix) =
      some (markerConfig .atMarker remaining (moved + 1)
        baseRev suffix) := by
  cases remaining <;> cases moved <;> cases baseRev <;> cases suffix <;>
    simp [TuringMachine.stepConfig, machine, transition,
      writeTickConfig, writeTickTape, markerConfig, markerTape,
      config, ticks, splitMarker, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, List.replicate_succ, List.map_append,
      List.append_assoc]

theorem at_marker_step (remaining moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (markerConfig .atMarker remaining (moved + 1)
          baseRev suffix) =
      some (doneConfig remaining (moved + 1) baseRev suffix) := by
  cases remaining <;> cases moved <;> cases baseRev <;> cases suffix <;>
    simp [TuringMachine.stepConfig, machine, transition,
      markerConfig, markerTape, doneConfig, doneTape, config,
      ticks, splitMarker, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, List.replicate_succ, List.map_append,
      List.append_assoc]

theorem rotation_step (remaining moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? 5
        (doneConfig (remaining + 1) moved baseRev suffix) =
      some (doneConfig remaining (moved + 1) baseRev suffix) := by
  rw [TuringMachine.runConfigExact?, inspect_done_tick_step]
  simp only
  rw [TuringMachine.runConfigExact?, pred_tick_step]
  simp only
  rw [TuringMachine.runConfigExact?, write_marker_step]
  simp only
  rw [TuringMachine.runConfigExact?, write_tick_step]
  simp only
  rw [TuringMachine.runConfigExact?, at_marker_step]
  rfl

def boundaryTape (moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  { left := baseRev.map some
    head := some MachineCodeSymbol.done
    right := some MachineCodeSymbol.done :: some splitMarker ::
      List.append ((ticks moved).map some)
        (some MachineCodeSymbol.done :: suffix.map some) }

def boundaryConfig (moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .inspectPred (boundaryTape moved baseRev suffix)

def returnDoneTape (moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  { left := some MachineCodeSymbol.done :: baseRev.map some
    head := some MachineCodeSymbol.done
    right := some splitMarker ::
      List.append ((ticks moved).map some)
        (some MachineCodeSymbol.done :: suffix.map some) }

def returnDoneConfig (moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .returnDone (returnDoneTape moved baseRev suffix)

def returnMarkerTape (moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  { left := some MachineCodeSymbol.done ::
      some MachineCodeSymbol.done :: baseRev.map some
    head := some splitMarker
    right := List.append ((ticks moved).map some)
      (some MachineCodeSymbol.done :: suffix.map some) }

def returnMarkerConfig (moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .returnMarker (returnMarkerTape moved baseRev suffix)

theorem inspect_done_boundary_step (moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig (doneConfig 0 moved baseRev suffix) =
      some (boundaryConfig moved baseRev suffix) := by
  cases moved <;> cases baseRev <;> cases suffix <;>
    simp [TuringMachine.stepConfig, machine, transition,
      doneConfig, doneTape, boundaryConfig, boundaryTape, config,
      ticks, splitMarker, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, List.replicate_succ, List.map_append,
      List.append_assoc]

theorem boundary_return_step (moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig (boundaryConfig moved baseRev suffix) =
      some (returnDoneConfig moved baseRev suffix) := by
  cases moved <;> cases baseRev <;> cases suffix <;>
    simp [TuringMachine.stepConfig, machine, transition,
      boundaryConfig, boundaryTape, returnDoneConfig,
      returnDoneTape, config, ticks, splitMarker, Tape.read,
      Tape.write, Tape.move, Tape.moveRight, List.replicate_succ,
      List.map_append, List.append_assoc]

theorem return_done_step (moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig (returnDoneConfig moved baseRev suffix) =
      some (returnMarkerConfig moved baseRev suffix) := by
  cases moved <;> cases baseRev <;> cases suffix <;>
    simp [TuringMachine.stepConfig, machine, transition,
      returnDoneConfig, returnDoneTape, returnMarkerConfig,
      returnMarkerTape, config, ticks, splitMarker, Tape.read,
      Tape.write, Tape.move, Tape.moveRight, List.replicate_succ,
      List.map_append, List.append_assoc]

theorem return_marker_step (moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig (returnMarkerConfig moved baseRev suffix) =
      some (targetConfig moved baseRev suffix) := by
  cases moved <;> cases baseRev <;> cases suffix <;>
    simp [TuringMachine.stepConfig, machine, transition,
      returnMarkerConfig, returnMarkerTape, targetConfig,
      config, ticks, splitMarker, SerializedShift.cursorTape,
      MachineDescription.encodeNatAppend, encodeNat_eq_ticks_done,
      Tape.read, Tape.write, Tape.move, Tape.moveRight,
      List.replicate_succ, List.map_append, List.append_assoc]

theorem rotation_finish (moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? 4
        (doneConfig 0 moved baseRev suffix) =
      some (targetConfig moved baseRev suffix) := by
  rw [TuringMachine.runConfigExact?, inspect_done_boundary_step]
  simp only
  rw [TuringMachine.runConfigExact?, boundary_return_step]
  simp only
  rw [TuringMachine.runConfigExact?, return_done_step]
  simp only
  rw [TuringMachine.runConfigExact?, return_marker_step]
  rfl

theorem rotation_run_exact (remaining moved : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (5 * remaining + 4)
        (doneConfig remaining moved baseRev suffix) =
      some (targetConfig (remaining + moved) baseRev suffix) := by
  induction remaining generalizing moved with
  | zero =>
      simpa using rotation_finish moved baseRev suffix
  | succ remaining ih =>
      rw [show 5 * (remaining + 1) + 4 =
          5 + (5 * remaining + 4) by lia]
      rw [InitialMaterializer.ExactRun.append]
      rw [show remaining + 1 = remaining + 1 by rfl]
      rw [rotation_step]
      simp only
      rw [ih (moved + 1)]
      congr 2
      lia

def runSteps (used : Nat) : Nat :=
  used + 2 + (5 * used + 4)

theorem run_exact (used : Nat) (baseRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (runSteps used)
        (sourceConfig used baseRev suffix) =
      some (targetConfig used baseRev suffix) := by
  unfold runSteps
  rw [show used + 2 + (5 * used + 4) =
      used + (2 + (5 * used + 4)) by lia]
  rw [InitialMaterializer.ExactRun.append]
  rw [seek_to_done_exact]
  simp only
  rw [InitialMaterializer.ExactRun.append]
  rw [enter_marker_exact]
  simp only
  simpa using rotation_run_exact used 0 baseRev suffix

theorem target_tape_eq_reset_split (used : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    (targetConfig used baseRev suffix).tape =
      SerializedShift.cursorTape
        (splitMarker :: MachineCodeSymbol.done ::
          MachineCodeSymbol.done :: baseRev)
        (MachineDescription.encodeNatAppend used suffix) := by
  rfl

end ExhaustedSplitReset

namespace GrowResetInsertion

open SerializedFieldComposer

def buffer : InsertBlock.Buffer :=
  InsertBlock.singletonBuffer MachineCodeSymbol.tick

def leftRev (baseRev : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  splitMarker :: MachineCodeSymbol.done ::
    MachineCodeSymbol.done :: baseRev

def rest (used : Nat) (suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend used suffix

def outputWord (used : Nat) (baseRev suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  List.append baseRev.reverse
    (MachineCodeSymbol.done :: MachineCodeSymbol.done :: splitMarker ::
      MachineDescription.encodeNatAppend (used + 1) suffix)

def sourceConfig (used : Nat) (baseRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control :=
  InsertRestagedMachine.editConfig
    (InsertBlock.config buffer (leftRev baseRev) (rest used suffix))

def targetConfig (used : Nat) (baseRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control :=
  InsertRestagedMachine.rewindConfig
    (RewindWord.gateConfig (outputWord used baseRev suffix) 0)

def runSteps (used : Nat) (baseRev suffix : Word MachineCodeSymbol) : Nat :=
  InsertRestagedMachine.runSteps buffer (leftRev baseRev) (rest used suffix)

theorem source_tape_eq_reset_target (used : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    (sourceConfig used baseRev suffix).tape =
      (ExhaustedSplitReset.targetConfig used baseRev suffix).tape := by
  rfl

theorem insert_output_eq_outputWord (used : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    PhysicalBranch.insertOutput buffer (leftRev baseRev)
        (rest used suffix) =
      outputWord used baseRev suffix := by
  simp [PhysicalBranch.insertOutput, buffer, leftRev, rest, outputWord,
    InsertBlock.singletonBuffer, MachineDescription.encodeNatAppend,
    MachineDescription.encodeNat, List.reverse_cons, List.append_assoc]

theorem run_exact (used : Nat)
    (baseRev suffix : Word MachineCodeSymbol) :
    (InsertRestagedMachine.machine buffer).runConfigExact?
        (runSteps used baseRev suffix)
        (sourceConfig used baseRev suffix) =
      some (targetConfig used baseRev suffix) := by
  unfold runSteps sourceConfig targetConfig
  rw [InsertRestagedMachine.run_exact buffer (leftRev baseRev)
    (rest used suffix) (InsertBlock.singletonBuffer_nonempty
      MachineCodeSymbol.tick)]
  rw [insert_output_eq_outputWord]

end GrowResetInsertion

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.Advance
