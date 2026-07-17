import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Outer.Direct.Cleanup

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.ParserAssembly
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep

def olderMetadataLeftRev
    (fuel stateCount : Nat) : Word MachineCodeSymbol :=
  List.append
    (List.replicate stateCount MachineCodeSymbol.tick)
    (MachineCodeSymbol.header ::
      (MachineDescription.encodeNat fuel).reverse)

def unaryScanTape
    (remaining processed : Nat)
    (deeper tail : Word MachineCodeSymbol)
    (rightPadding : Nat) : Tape MachineCodeSymbol :=
  match remaining with
  | 0 =>
      { left := deeper.map some
        head := some MachineCodeSymbol.done
        right :=
          (List.append
            (List.replicate processed MachineCodeSymbol.tick)
            tail).map some ++
            List.replicate rightPadding none }
  | remaining + 1 =>
      { left :=
          (List.append
            (List.replicate remaining MachineCodeSymbol.tick)
            (MachineCodeSymbol.done :: deeper)).map some
        head := some MachineCodeSymbol.tick
        right :=
          (List.append
            (List.replicate processed MachineCodeSymbol.tick)
            tail).map some ++
            List.replicate rightPadding none }

def haltScanConfig
    (fuel stateCount start : Nat)
    (remaining processed rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .crossHaltTicks
  tape := unaryScanTape remaining processed
    (List.append
      (List.replicate start MachineCodeSymbol.tick)
      (MachineCodeSymbol.done ::
        olderMetadataLeftRev fuel stateCount))
    [MachineCodeSymbol.done, MachineCodeSymbol.blank]
    rightPadding

def startScanTail (halt : Nat) : Word MachineCodeSymbol :=
  MachineCodeSymbol.done ::
    MachineDescription.encodeNatAppend halt
      [MachineCodeSymbol.blank]

def startScanConfig
    (fuel stateCount halt : Nat)
    (remaining processed rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .crossStartTicks
  tape := unaryScanTape remaining processed
    (olderMetadataLeftRev fuel stateCount)
    (startScanTail halt) rightPadding

theorem crossHaltDone_step
    (fuel stateCount start halt rightPadding : Nat) :
    machine.stepConfig
        (crossHaltDoneConfig fuel stateCount start halt rightPadding) =
      some
        (haltScanConfig fuel stateCount start halt 0 rightPadding) := by
  cases halt <;> cases start <;> cases stateCount <;>
    cases fuel <;> cases rightPadding <;>
      simp [crossHaltDoneConfig, haltScanConfig, unaryScanTape,
        olderMetadataLeftRev, machine, transition,
        TuringMachine.stepConfig, MachineDescription.encodeNat,
        encodeNat_reverse_eq_done_ticks,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        List.map_append, List.replicate_succ, replicate_append_self_cons]

theorem haltScan_tick_step
    (fuel stateCount start remaining processed rightPadding : Nat) :
    machine.stepConfig
        (haltScanConfig fuel stateCount start remaining.succ
          processed rightPadding) =
      some
        (haltScanConfig fuel stateCount start remaining
          processed.succ rightPadding) := by
  cases remaining <;> cases processed <;> cases start <;>
    cases stateCount <;> cases fuel <;> cases rightPadding <;>
      simp [haltScanConfig, unaryScanTape, olderMetadataLeftRev,
        machine, transition, TuringMachine.stepConfig,
        MachineDescription.encodeNat, Tape.read, Tape.write,
        Tape.move, Tape.moveLeft, List.map_append,
        List.replicate_succ, List.append_assoc]

theorem haltScan_run_exact
    (fuel stateCount start remaining processed rightPadding : Nat) :
    machine.runConfigExact? remaining
        (haltScanConfig fuel stateCount start remaining
          processed rightPadding) =
      some
        (haltScanConfig fuel stateCount start 0
          (remaining + processed) rightPadding) := by
  induction remaining generalizing processed with
  | zero =>
      change some (haltScanConfig fuel stateCount start 0
          processed rightPadding) =
        some (haltScanConfig fuel stateCount start 0
          (0 + processed) rightPadding)
      simp only [Nat.zero_add]
  | succ remaining ih =>
      rw [TuringMachine.runConfigExact?]
      rw [haltScan_tick_step]
      simp only
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih processed.succ

theorem haltScan_done_step
    (fuel stateCount start halt rightPadding : Nat) :
    machine.stepConfig
        (haltScanConfig fuel stateCount start 0 halt rightPadding) =
      some
        (startScanConfig fuel stateCount halt start 0 rightPadding) := by
  cases start <;> cases halt <;> cases stateCount <;>
    cases fuel <;> cases rightPadding <;>
      simp [haltScanConfig, startScanConfig, unaryScanTape,
        olderMetadataLeftRev, startScanTail, machine, transition,
        TuringMachine.stepConfig, MachineDescription.encodeNat,
        MachineDescription.encodeNatAppend,
        encodeNat_eq_ticks_done,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        List.map_append, List.replicate_succ, List.append_assoc]

theorem startScan_tick_step
    (fuel stateCount halt remaining processed rightPadding : Nat) :
    machine.stepConfig
        (startScanConfig fuel stateCount halt remaining.succ
          processed rightPadding) =
      some
        (startScanConfig fuel stateCount halt remaining
          processed.succ rightPadding) := by
  cases remaining <;> cases processed <;> cases halt <;>
    cases stateCount <;> cases fuel <;> cases rightPadding <;>
      simp [startScanConfig, unaryScanTape, olderMetadataLeftRev,
        startScanTail, machine, transition,
        TuringMachine.stepConfig, MachineDescription.encodeNat,
        MachineDescription.encodeNatAppend,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        List.map_append, List.replicate_succ, List.append_assoc]

theorem startScan_run_exact
    (fuel stateCount halt remaining processed rightPadding : Nat) :
    machine.runConfigExact? remaining
        (startScanConfig fuel stateCount halt remaining
          processed rightPadding) =
      some
        (startScanConfig fuel stateCount halt 0
          (remaining + processed) rightPadding) := by
  induction remaining generalizing processed with
  | zero =>
      change some (startScanConfig fuel stateCount halt 0
          processed rightPadding) =
        some (startScanConfig fuel stateCount halt 0
          (0 + processed) rightPadding)
      simp only [Nat.zero_add]
  | succ remaining ih =>
      rw [TuringMachine.runConfigExact?]
      rw [startScan_tick_step]
      simp only
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih processed.succ

def eraseLeftTape
    (remaining : Word MachineCodeSymbol)
    (markers : Nat)
    (target : Word MachineCodeSymbol)
    (rightPadding : Nat) : Tape MachineCodeSymbol :=
  match remaining with
  | [] =>
      { left := []
        head := none
        right :=
          List.replicate markers (some MachineCodeSymbol.moveLeft) ++
            target.map some ++ List.replicate rightPadding none }
  | current :: more =>
      { left := more.map some
        head := some current
        right :=
          List.replicate markers (some MachineCodeSymbol.moveLeft) ++
            target.map some ++ List.replicate rightPadding none }

def eraseLeftConfig
    (remaining : Word MachineCodeSymbol)
    (markers : Nat)
    (target : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .eraseLeft
  tape := eraseLeftTape remaining markers target rightPadding

theorem startScan_done_step
    (fuel stateCount start halt rightPadding : Nat) :
    machine.stepConfig
        (startScanConfig fuel stateCount halt 0 start rightPadding) =
      some
        (eraseLeftConfig (olderMetadataLeftRev fuel stateCount) 1
          (extractedWord start halt) rightPadding) := by
  cases start <;> cases halt <;> cases stateCount <;>
    cases fuel <;> cases rightPadding <;>
      simp [startScanConfig, unaryScanTape, olderMetadataLeftRev,
        startScanTail, extractedWord, eraseLeftConfig, eraseLeftTape,
        machine, transition, TuringMachine.stepConfig,
        MachineDescription.encodeNat,
        MachineDescription.encodeNatAppend,
        encodeNat_eq_ticks_done,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        List.map_append, List.replicate_succ,
        replicate_append_self_cons, List.append_assoc]

theorem eraseLeft_step
    (current : MachineCodeSymbol)
    (more target : Word MachineCodeSymbol)
    (markers rightPadding : Nat) :
    machine.stepConfig
        (eraseLeftConfig (current :: more) markers target rightPadding) =
      some
        (eraseLeftConfig more markers.succ target rightPadding) := by
  cases current <;> cases more <;> cases markers <;>
    cases target <;> cases rightPadding <;>
      simp [eraseLeftConfig, eraseLeftTape, machine, transition,
        TuringMachine.stepConfig, Tape.read, Tape.write,
        Tape.move, Tape.moveLeft, List.replicate_succ,
        List.append_assoc]

theorem eraseLeft_run_exact
    (remaining target : Word MachineCodeSymbol)
    (markers rightPadding : Nat) :
    machine.runConfigExact? remaining.length
        (eraseLeftConfig remaining markers target rightPadding) =
      some
        (eraseLeftConfig [] (remaining.length + markers)
          target rightPadding) := by
  induction remaining generalizing markers with
  | nil =>
      simp only [List.length_nil, TuringMachine.runConfigExact?,
        Nat.zero_add]
  | cons current more ih =>
      change machine.runConfigExact? (more.length + 1)
        (eraseLeftConfig (current :: more) markers target rightPadding) = _
      rw [TuringMachine.runConfigExact?]
      rw [eraseLeft_step]
      simp only
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih markers.succ

def cleanupLeftTape
    (remainingMarkers leftPadding : Nat)
    (target : Word MachineCodeSymbol)
    (rightPadding : Nat) : Tape MachineCodeSymbol :=
  match remainingMarkers, target with
  | 0, [] =>
      { left := List.replicate leftPadding none
        head := none
        right := List.replicate rightPadding none }
  | 0, first :: rest =>
      { left := List.replicate leftPadding none
        head := some first
        right := rest.map some ++ List.replicate rightPadding none }
  | remaining + 1, _ =>
      { left := List.replicate leftPadding none
        head := some MachineCodeSymbol.moveLeft
        right :=
          List.replicate remaining (some MachineCodeSymbol.moveLeft) ++
            target.map some ++ List.replicate rightPadding none }

def cleanupLeftConfig
    (remainingMarkers leftPadding : Nat)
    (target : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .cleanupLeft
  tape := cleanupLeftTape remainingMarkers leftPadding target rightPadding

theorem eraseLeft_finish_step
    (markers rightPadding : Nat)
    (target : Word MachineCodeSymbol) :
    machine.stepConfig
        (eraseLeftConfig [] markers.succ target rightPadding) =
      some
        (cleanupLeftConfig markers.succ 1
          target rightPadding) := by
  cases markers <;> cases target <;>
    cases rightPadding <;>
      simp [eraseLeftConfig, eraseLeftTape, cleanupLeftConfig,
        cleanupLeftTape, machine, transition,
        TuringMachine.stepConfig, Tape.read, Tape.write,
        Tape.move, Tape.moveRight, List.replicate_succ,
        List.append_assoc]

theorem cleanupLeft_marker_step
    (remaining leftPadding rightPadding : Nat)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (cleanupLeftConfig remaining.succ leftPadding
          (first :: rest) rightPadding) =
      some
        (cleanupLeftConfig remaining leftPadding.succ
          (first :: rest) rightPadding) := by
  cases remaining <;> cases leftPadding <;> cases first <;> cases rest <;>
    cases rightPadding <;>
      simp [cleanupLeftConfig, cleanupLeftTape, machine, transition,
        TuringMachine.stepConfig, Tape.read, Tape.write,
        Tape.move, Tape.moveRight, List.replicate_succ,
        List.append_assoc]

theorem cleanupLeft_run_exact
    (remaining leftPadding rightPadding : Nat)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    machine.runConfigExact? remaining
        (cleanupLeftConfig remaining leftPadding
          (first :: rest) rightPadding) =
      some
        (cleanupLeftConfig 0 (remaining + leftPadding)
          (first :: rest) rightPadding) := by
  induction remaining generalizing leftPadding with
  | zero =>
      simp only [TuringMachine.runConfigExact?, Nat.zero_add]
  | succ remaining ih =>
      rw [TuringMachine.runConfigExact?]
      rw [cleanupLeft_marker_step]
      simp only
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih leftPadding.succ

def readyBounceConfig
    (leftPadding : Nat)
    (target : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .readyBounce
  tape :=
    { left := List.replicate leftPadding none
      head := none
      right := target.map some ++ List.replicate rightPadding none }

def readyConfig
    (leftPadding : Nat)
    (target : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .ready
  tape := cleanupLeftTape 0 leftPadding target rightPadding

theorem cleanupLeft_target_step
    (leftPadding start halt rightPadding : Nat) :
    machine.stepConfig
        (cleanupLeftConfig 0 leftPadding.succ
          (extractedWord start halt) rightPadding) =
      some
        (readyBounceConfig leftPadding
          (extractedWord start halt) rightPadding) := by
  cases leftPadding <;> cases start <;> cases halt <;>
    cases rightPadding <;>
      simp [cleanupLeftConfig, cleanupLeftTape, readyBounceConfig,
        extractedWord, machine, transition,
        TuringMachine.stepConfig, MachineDescription.encodeNat,
        MachineDescription.encodeNatAppend,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        List.map_append, List.replicate_succ, List.append_assoc]

theorem readyBounce_step
    (leftPadding start halt rightPadding : Nat) :
    machine.stepConfig
        (readyBounceConfig leftPadding
          (extractedWord start halt) rightPadding) =
      some
        (readyConfig leftPadding.succ
          (extractedWord start halt) rightPadding) := by
  cases leftPadding <;> cases start <;> cases halt <;>
    cases rightPadding <;>
      simp [readyBounceConfig, readyConfig, cleanupLeftTape,
        extractedWord, machine, transition,
        TuringMachine.stepConfig, MachineDescription.encodeNat,
        MachineDescription.encodeNatAppend,
        Tape.read, Tape.write, Tape.move, Tape.moveRight,
        List.map_append, List.replicate_succ, List.append_assoc]

theorem ready_tape_equiv_input_cons
    (leftPadding rightPadding : Nat)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    Tape.Equiv
      (readyConfig leftPadding
        (first :: rest) rightPadding).tape
      (Tape.input (first :: rest)) := by
  exact ⟨
    FoC.Computability.dropTrailingNone_replicate_none leftPadding,
    rfl,
    FoC.Computability.dropTrailingNone_append_replicate_none
      (rest.map some) rightPadding⟩

theorem extractedWord_ne_nil (start halt : Nat) :
    extractedWord start halt ≠ [] := by
  cases start <;>
    simp [extractedWord, MachineDescription.encodeNatAppend,
      MachineDescription.encodeNat]

theorem ready_tape_equiv_extracted
    (leftPadding start halt rightPadding : Nat) :
    Tape.Equiv
      (readyConfig leftPadding
        (extractedWord start halt) rightPadding).tape
      (Tape.input (extractedWord start halt)) := by
  cases htarget : extractedWord start halt with
  | nil => exact False.elim (extractedWord_ne_nil start halt htarget)
  | cons first rest =>
      simpa [htarget] using
        ready_tape_equiv_input_cons leftPadding rightPadding first rest

theorem crossHaltDone_computes_to_ready
    (fuel stateCount start halt rightPadding : Nat) :
    TuringMachine.Computes machine
      (crossHaltDoneConfig fuel stateCount start halt rightPadding)
      (readyConfig
        ((olderMetadataLeftRev fuel stateCount).length + 2)
        (extractedWord start halt) rightPadding) := by
  cases htarget : extractedWord start halt with
  | nil => exact False.elim (extractedWord_ne_nil start halt htarget)
  | cons targetFirst targetRest =>
      have hcrossHalt := computes_one_of_stepConfig
        (crossHaltDone_step fuel stateCount start halt rightPadding)
      have hscanHalt := computes_of_run_exact
        (haltScan_run_exact fuel stateCount start halt 0 rightPadding)
      have hhaltDone := computes_one_of_stepConfig
        (haltScan_done_step fuel stateCount start halt rightPadding)
      have hscanStart := computes_of_run_exact
        (startScan_run_exact fuel stateCount halt start 0 rightPadding)
      have hstartDone := computes_one_of_stepConfig
        (startScan_done_step fuel stateCount start halt rightPadding)
      have heraseLeft := computes_of_run_exact
        (eraseLeft_run_exact
          (olderMetadataLeftRev fuel stateCount)
          (targetFirst :: targetRest) 1 rightPadding)
      have hfinishLeft := computes_one_of_stepConfig
        (eraseLeft_finish_step
          (olderMetadataLeftRev fuel stateCount).length
          rightPadding (targetFirst :: targetRest))
      have hcleanupLeft := computes_of_run_exact
        (cleanupLeft_run_exact
          ((olderMetadataLeftRev fuel stateCount).length + 1)
          1 rightPadding targetFirst targetRest)
      have htargetStep := computes_one_of_stepConfig
        (cleanupLeft_target_step
          ((olderMetadataLeftRev fuel stateCount).length + 1)
          start halt rightPadding)
      have hbounce := computes_one_of_stepConfig
        (readyBounce_step
          ((olderMetadataLeftRev fuel stateCount).length + 1)
          start halt rightPadding)
      apply TuringMachine.computes_trans hcrossHalt
      apply TuringMachine.computes_trans
        (by simpa using hscanHalt)
      apply TuringMachine.computes_trans hhaltDone
      apply TuringMachine.computes_trans
        (by simpa using hscanStart)
      apply TuringMachine.computes_trans
        (by simpa [htarget] using hstartDone)
      apply TuringMachine.computes_trans
        (by simpa using heraseLeft)
      apply TuringMachine.computes_trans
        (by simpa using hfinishLeft)
      apply TuringMachine.computes_trans
        (by simpa [Nat.succ_eq_add_one] using hcleanupLeft)
      apply TuringMachine.computes_trans
        (by simpa [htarget, Nat.succ_eq_add_one] using htargetStep)
      simpa [htarget, Nat.succ_eq_add_one, Nat.add_assoc] using hbounce

theorem noBarrier_extractor_computes
    (fuel stateCount start halt : Nat)
    (payload : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (noBarrierSourceConfig
        (metadataLeftRev fuel stateCount start halt) payload)
      (readyConfig
        ((olderMetadataLeftRev fuel stateCount).length + 2)
        (extractedWord start halt)
        (((noBarrierPayloadTail payload).length + 1).succ)) := by
  apply TuringMachine.computes_trans
    (noBarrier_cleanup_computes_to_crossHaltDone
      fuel stateCount start halt payload)
  exact crossHaltDone_computes_to_ready fuel stateCount start halt _

theorem contextual_extractor_computes
    (fuel stateCount start halt rowCount : Nat)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (contextSourceConfig
        (parsedTableLeftRev rowCount ++
          (metadataLeftRev fuel stateCount start halt).map some)
        first rest)
      (readyConfig
        ((olderMetadataLeftRev fuel stateCount).length + 2)
        (extractedWord start halt)
        ((MachineCodeSymbol.done ::
          List.replicate rowCount MachineCodeSymbol.blank).length +
          (rest.length + 1)).succ) := by
  apply TuringMachine.computes_trans
    (contextual_cleanup_computes_to_crossHaltDone
      fuel stateCount start halt rowCount first rest)
  exact crossHaltDone_computes_to_ready fuel stateCount start halt _

def parserMarkedTailWord
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  match suffix with
  | [] => [MachineCodeSymbol.header]
  | _ :: rest => MachineCodeSymbol.header :: rest

theorem transitionListParserMarkedTail_eq_map
    (suffix : Word MachineCodeSymbol) :
    transitionListParserMarkedTail suffix =
      (parserMarkedTailWord suffix).map some := by
  cases suffix <;> rfl

def parserPayloadWord
    (symbols suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append symbols (parserMarkedTailWord suffix)

theorem parserPayloadWord_ne_nil
    (symbols suffix : Word MachineCodeSymbol) :
    parserPayloadWord symbols suffix ≠ [] := by
  cases symbols <;> cases suffix <;>
    simp [parserPayloadWord, parserMarkedTailWord]

theorem contextual_parser_endpoint_tape
    (base symbols suffix : Word MachineCodeSymbol)
    (rowCount : Nat)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (hpayload : parserPayloadWord symbols suffix = first :: rest) :
    FiniteRecognizer.Interpreter.ParserAssembly.TransitionParserContextTransport.appendLeftContext
        base (parsedTransitionHaltConfig rowCount symbols suffix).tape =
      (contextSourceConfig
        (parsedTableLeftRev rowCount ++ base.map some)
        first rest).tape := by
  have hmap := congrArg
    (fun word : Word MachineCodeSymbol => word.map some) hpayload
  have hcells :
      symbols.map some ++ (parserMarkedTailWord suffix).map some =
        some first :: rest.map some := by
    simpa [parserPayloadWord, List.map_append] using hmap
  change
    FiniteRecognizer.Interpreter.ParserAssembly.TransitionParserContextTransport.appendLeftContext
        base
        (transitionListParserOptionTape
          (parsedTableLeftRev rowCount)
          (symbols.map some ++ transitionListParserMarkedTail suffix)) =
      contextCursorTape
        (parsedTableLeftRev rowCount ++ base.map some)
        (first :: rest)
  rw [transitionListParserMarkedTail_eq_map]
  rw [hcells]
  rfl

theorem extractor_computes
    (fuel stateCount start halt : Nat)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (sourceConfig fuel stateCount start halt first rest)
      (readyConfig
        ((olderMetadataLeftRev fuel stateCount).length + 2)
        (extractedWord start halt) (rest.length + 1)) := by
  cases htarget : extractedWord start halt with
  | nil => exact False.elim (extractedWord_ne_nil start halt htarget)
  | cons targetFirst targetRest =>
      have hpreserve := computes_one_of_stepConfig
        (preserveBlank_step
          (metadataLeftRev fuel stateCount start halt) first rest)
      have heraseRight := computes_of_run_exact
        (eraseRight_run_exact
          (MachineCodeSymbol.blank ::
            metadataLeftRev fuel stateCount start halt)
          rest 0)
      have hfinishRight := computes_one_of_stepConfig
        (eraseRight_finish_step
          (metadataLeftRev fuel stateCount start halt) rest.length)
      have hcleanupRight := computes_of_run_exact
        (cleanupRight_run_exact
          (metadataLeftRev fuel stateCount start halt) rest.length 1)
      have hrightBoundary := computes_one_of_stepConfig
        (cleanupRight_boundary_step fuel stateCount start halt
          (rest.length + 1))
      have hcrossHalt := computes_one_of_stepConfig
        (crossHaltDone_step fuel stateCount start halt
          (rest.length + 1))
      have hscanHalt := computes_of_run_exact
        (haltScan_run_exact fuel stateCount start halt 0
          (rest.length + 1))
      have hhaltDone := computes_one_of_stepConfig
        (haltScan_done_step fuel stateCount start halt
          (rest.length + 1))
      have hscanStart := computes_of_run_exact
        (startScan_run_exact fuel stateCount halt start 0
          (rest.length + 1))
      have hstartDone := computes_one_of_stepConfig
        (startScan_done_step fuel stateCount start halt
          (rest.length + 1))
      have heraseLeft := computes_of_run_exact
        (eraseLeft_run_exact
          (olderMetadataLeftRev fuel stateCount)
          (targetFirst :: targetRest) 1 (rest.length + 1))
      have hfinishLeft := computes_one_of_stepConfig
        (eraseLeft_finish_step
          (olderMetadataLeftRev fuel stateCount).length
          (rest.length + 1) (targetFirst :: targetRest))
      have hcleanupLeft := computes_of_run_exact
        (cleanupLeft_run_exact
          ((olderMetadataLeftRev fuel stateCount).length + 1)
          1 (rest.length + 1) targetFirst targetRest)
      have htargetStep := computes_one_of_stepConfig
        (cleanupLeft_target_step
          ((olderMetadataLeftRev fuel stateCount).length + 1)
          start halt (rest.length + 1))
      have hbounce := computes_one_of_stepConfig
        (readyBounce_step
          ((olderMetadataLeftRev fuel stateCount).length + 1)
          start halt (rest.length + 1))
      apply TuringMachine.computes_trans
        (by simpa [sourceConfig] using hpreserve)
      apply TuringMachine.computes_trans
        (by simpa using heraseRight)
      apply TuringMachine.computes_trans hfinishRight
      apply TuringMachine.computes_trans
        (by simpa [Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hcleanupRight)
      apply TuringMachine.computes_trans hrightBoundary
      apply TuringMachine.computes_trans hcrossHalt
      apply TuringMachine.computes_trans
        (by simpa using hscanHalt)
      apply TuringMachine.computes_trans hhaltDone
      apply TuringMachine.computes_trans
        (by simpa using hscanStart)
      apply TuringMachine.computes_trans
        (by simpa [htarget] using hstartDone)
      apply TuringMachine.computes_trans
        (by simpa using heraseLeft)
      apply TuringMachine.computes_trans
        (by simpa using hfinishLeft)
      apply TuringMachine.computes_trans
        (by simpa [Nat.succ_eq_add_one] using hcleanupLeft)
      apply TuringMachine.computes_trans
        (by simpa [htarget, Nat.succ_eq_add_one] using htargetStep)
      simpa [htarget, Nat.succ_eq_add_one, Nat.add_assoc] using hbounce

end FiniteRecognizer.Interpreter.ZeroEmptyMetadataFinal
end Computability
end FoC
