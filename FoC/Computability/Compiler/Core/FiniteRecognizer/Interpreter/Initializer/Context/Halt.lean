import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.Context.Ingress

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.BooleanContextHaltAppender

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

namespace Machine

inductive Control where
  | fuel
  | needHeader
  | stateCount
  | startState
  | haltScan
  | seekRight
  | replaceMarker
  | writeMarker
  | rewindRound
  | restore
  | seekEnd
  | installDone
  | rewindOutput
  | ready
deriving DecidableEq

namespace Control

def elems : List Control :=
  [.fuel, .needHeader, .stateCount, .startState, .haltScan,
    .seekRight, .replaceMarker, .writeMarker, .rewindRound,
    .restore, .seekEnd, .installDone, .rewindOutput, .ready]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control <;> simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .fuel, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .fuel)
  | .fuel, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .needHeader)
  | .needHeader, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.right, .stateCount)
  | .stateCount, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .stateCount)
  | .stateCount, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .startState)
  | .startState, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .startState)
  | .startState, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .haltScan)
  | .haltScan, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.blank, Direction.right, .haltScan)
  | .haltScan, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.blank, Direction.right, .seekRight)
  | .haltScan, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.left, .restore)
  | .seekRight, some symbol =>
      some (some symbol, Direction.right, .seekRight)
  | .seekRight, none =>
      some (none, Direction.left, .replaceMarker)
  | .replaceMarker, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.tick, Direction.right, .writeMarker)
  | .writeMarker, none =>
      some (some MachineCodeSymbol.header, Direction.left, .rewindRound)
  | .rewindRound, some symbol =>
      some (some symbol, Direction.left, .rewindRound)
  | .rewindRound, none =>
      some (none, Direction.right, .fuel)
  | .restore, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.tick, Direction.left, .restore)
  | .restore, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .seekEnd)
  | .seekEnd, some symbol =>
      some (some symbol, Direction.right, .seekEnd)
  | .seekEnd, none =>
      some (none, Direction.left, .installDone)
  | .installDone, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.done, Direction.left, .rewindOutput)
  | .rewindOutput, some symbol =>
      some (some symbol, Direction.left, .rewindOutput)
  | .rewindOutput, none =>
      some (none, Direction.right, .ready)
  | .ready, _ => none
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .fuel
  halt := .ready
  transition := transition
  statesFinite := Control.finite

def config
    (state : Control)
    (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := state
    tape := SerializedShift.cursorTape leftRev rest }

theorem cursor_step
    (state next : Control)
    (leftRev rest : Word MachineCodeSymbol)
    (symbol write : MachineCodeSymbol)
    (htransition : transition state (some symbol) =
      some (some write, Direction.right, next)) :
    TuringMachine.Step machine
      (config state leftRev (symbol :: rest))
      (config next (write :: leftRev) rest) := by
  apply TuringMachine.stepConfig_eq_some_iff_step.mp
  cases rest <;>
    simp [TuringMachine.stepConfig, machine, config,
      SerializedShift.cursorTape, htransition, Tape.read,
      Tape.write, Tape.move, Tape.moveRight]

theorem scanUnary_computes
    (state next : Control)
    (htick : transition state (some MachineCodeSymbol.tick) =
      some (some MachineCodeSymbol.tick, Direction.right, state))
    (hdone : transition state (some MachineCodeSymbol.done) =
      some (some MachineCodeSymbol.done, Direction.right, next))
    (count : Nat)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (config state leftRev
        (MachineDescription.encodeNatAppend count suffix))
      (config next
        (List.append (MachineDescription.encodeNat count).reverse leftRev)
        suffix) := by
  induction count generalizing leftRev with
  | zero =>
      exact TuringMachine.Computes.step
        (cursor_step state next leftRev suffix
          MachineCodeSymbol.done MachineCodeSymbol.done hdone)
        (TuringMachine.Computes.refl _)
  | succ count ih =>
      have hstep := cursor_step state state leftRev
        (MachineDescription.encodeNatAppend count suffix)
        MachineCodeSymbol.tick MachineCodeSymbol.tick htick
      have hrest := ih (MachineCodeSymbol.tick :: leftRev)
      exact TuringMachine.Computes.step
        (by
          simpa [MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat] using hstep)
        (by
          simpa [MachineDescription.encodeNatAppend,
            MachineDescription.encodeNat, List.append_assoc] using hrest)

def metadataPrefix
    (fuel stateCount start : Nat) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend fuel
    (MachineCodeSymbol.header ::
      MachineDescription.encodeNatAppend stateCount
        (MachineDescription.encodeNat start))

def markedHaltField
    (marked remaining : Nat) : Word MachineCodeSymbol :=
  List.append
    (List.replicate marked MachineCodeSymbol.blank)
    (MachineDescription.encodeNat remaining)

def copiedTicks (marked : Nat) : Word MachineCodeSymbol :=
  List.replicate marked MachineCodeSymbol.tick

def workWord
    (fuel stateCount start marked remaining : Nat)
    (body : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (metadataPrefix fuel stateCount start)
    (List.append (markedHaltField marked remaining)
      (List.append body
        (List.append (copiedTicks marked)
          [MachineCodeSymbol.header])))

def finalWord
    (fuel stateCount start halt : Nat)
    (body : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (metadataPrefix fuel stateCount start)
    (MachineDescription.encodeNatAppend halt
      (List.append body (MachineDescription.encodeNat halt)))

def sourceConfig
    (fuel stateCount start halt : Nat)
    (body : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .fuel
    tape := Tape.input (workWord fuel stateCount start 0 halt body) }

def targetConfig
    (fuel stateCount start halt : Nat)
    (body : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .ready
    tape := Tape.input (finalWord fuel stateCount start halt body) }

def haltLeftRev
    (fuel stateCount start : Nat) : Word MachineCodeSymbol :=
  (metadataPrefix fuel stateCount start).reverse

theorem metadata_scan_computes
    (fuel stateCount start : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (config .fuel []
        (List.append (metadataPrefix fuel stateCount start) suffix))
      (config .haltScan (haltLeftRev fuel stateCount start) suffix) := by
  let afterFuel : Word MachineCodeSymbol :=
    (MachineDescription.encodeNat fuel).reverse
  let afterHeader : Word MachineCodeSymbol :=
    MachineCodeSymbol.header :: afterFuel
  let afterState : Word MachineCodeSymbol :=
    List.append (MachineDescription.encodeNat stateCount).reverse
      afterHeader
  have hfuel := scanUnary_computes .fuel .needHeader rfl rfl fuel []
    (MachineCodeSymbol.header ::
      MachineDescription.encodeNatAppend stateCount
        (MachineDescription.encodeNatAppend start suffix))
  have hheader : TuringMachine.Computes machine
      (config .needHeader afterFuel
        (MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start suffix)))
      (config .stateCount afterHeader
        (MachineDescription.encodeNatAppend stateCount
          (MachineDescription.encodeNatAppend start suffix))) := by
    exact TuringMachine.Computes.step
      (cursor_step .needHeader .stateCount afterFuel _
        MachineCodeSymbol.header MachineCodeSymbol.header rfl)
      (TuringMachine.Computes.refl _)
  have hstate := scanUnary_computes .stateCount .startState rfl rfl
    stateCount afterHeader (MachineDescription.encodeNatAppend start suffix)
  have hstart := scanUnary_computes .startState .haltScan rfl rfl
    start afterState suffix
  have hrun := TuringMachine.computes_trans hfuel (by
    simpa [afterFuel] using hheader)
  have hrun := TuringMachine.computes_trans hrun (by
    simpa [afterHeader] using hstate)
  have hrun := TuringMachine.computes_trans hrun (by
    simpa [afterState] using hstart)
  simpa [metadataPrefix, haltLeftRev,
    MachineDescription.encodeNatAppend, List.reverse_append,
    afterFuel, afterHeader, afterState, List.append_assoc] using hrun

theorem halt_blank_step
    (leftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .haltScan leftRev
          (MachineCodeSymbol.blank :: rest)) =
      some
        (config .haltScan
          (MachineCodeSymbol.blank :: leftRev) rest) := by
  cases leftRev <;> cases rest <;> rfl

theorem scan_marked_computes
    (marked : Nat)
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (config .haltScan leftRev
        (List.append
          (List.replicate marked MachineCodeSymbol.blank) suffix))
      (config .haltScan
        (List.append
          (List.replicate marked MachineCodeSymbol.blank).reverse leftRev)
        suffix) := by
  induction marked generalizing leftRev with
  | zero => exact TuringMachine.Computes.refl _
  | succ marked ih =>
      exact TuringMachine.Computes.step
        (by
          simpa [List.replicate_succ] using
            TuringMachine.stepConfig_eq_some_iff_step.mp
              (halt_blank_step leftRev
                (List.append
                  (List.replicate marked MachineCodeSymbol.blank)
                  suffix)))
        (by
          simpa [List.replicate_succ, List.reverse_cons,
            List.append_assoc] using
              ih (MachineCodeSymbol.blank :: leftRev))

theorem halt_tick_step
    (leftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .haltScan leftRev
          (MachineCodeSymbol.tick :: rest)) =
      some
        (config .seekRight
          (MachineCodeSymbol.blank :: leftRev) rest) := by
  cases leftRev <;> cases rest <;> rfl

theorem seekRight_symbol_step
    (leftRev rest : Word MachineCodeSymbol)
    (symbol : MachineCodeSymbol) :
    machine.stepConfig
        (config .seekRight leftRev (symbol :: rest)) =
      some
        (config .seekRight (symbol :: leftRev) rest) := by
  cases symbol <;> cases leftRev <;> cases rest <;> rfl

def markerConfig
    (leftRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .replaceMarker
    tape :=
      { left := leftRev.map some
        head := some MachineCodeSymbol.header
        right := [none] } }

theorem seekRight_none_step
    (leftRev : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .seekRight
          (MachineCodeSymbol.header :: leftRev) []) =
      some (markerConfig leftRev) := by
  cases leftRev <;> rfl

theorem seekRight_to_marker_computes
    (leftRev middle : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (config .seekRight leftRev
        (List.append middle [MachineCodeSymbol.header]))
      (markerConfig
        (List.append middle.reverse leftRev)) := by
  induction middle generalizing leftRev with
  | nil =>
      have hheader := seekRight_symbol_step leftRev []
        MachineCodeSymbol.header
      have hnone := seekRight_none_step leftRev
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp hheader)
        (TuringMachine.Computes.step
          (by
            simpa [markerConfig] using
              TuringMachine.stepConfig_eq_some_iff_step.mp hnone)
          (TuringMachine.Computes.refl _))
  | cons symbol rest ih =>
      exact TuringMachine.Computes.step
        (by
          simpa using TuringMachine.stepConfig_eq_some_iff_step.mp
            (seekRight_symbol_step leftRev
              (List.append rest [MachineCodeSymbol.header]) symbol))
        (by
          simpa [List.reverse_cons, List.append_assoc] using
            ih (symbol :: leftRev))

def rewindScanTape
    (remainingRev crossed : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := []
        head := none
        right := crossed.map some }
  | current :: rest =>
      { left := rest.map some
        head := some current
        right := crossed.map some }

def rewindScanConfig
    (remainingRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .rewindRound
    tape := rewindScanTape remainingRev crossed }

def frontTape (word : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match word with
  | [] => { left := [none], head := none, right := [] }
  | first :: rest =>
      { left := [none]
        head := some first
        right := rest.map some }

def frontConfig
    (state : Control) (word : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := state, tape := frontTape word }

theorem marker_append_run_exact
    (leftRev : Word MachineCodeSymbol) :
    machine.runConfigExact? 2 (markerConfig leftRev) =
      some (rewindScanConfig
        (MachineCodeSymbol.tick :: leftRev)
        [MachineCodeSymbol.header]) := by
  cases leftRev <;> rfl

theorem rewind_symbol_step
    (current : MachineCodeSymbol)
    (remainingRev crossed : Word MachineCodeSymbol) :
    machine.stepConfig
        (rewindScanConfig (current :: remainingRev) crossed) =
      some (rewindScanConfig remainingRev (current :: crossed)) := by
  cases current <;> cases remainingRev <;> cases crossed <;> rfl

theorem rewind_finish_step
    (crossed : Word MachineCodeSymbol) :
    machine.stepConfig (rewindScanConfig [] crossed) =
      some (frontConfig .fuel crossed) := by
  cases crossed <;> rfl

theorem rewind_computes
    (remainingRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (rewindScanConfig remainingRev crossed)
      (frontConfig .fuel
        (List.append remainingRev.reverse crossed)) := by
  induction remainingRev generalizing crossed with
  | nil =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (rewind_finish_step crossed))
        (TuringMachine.Computes.refl _)
  | cons current remainingRev ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (rewind_symbol_step current remainingRev crossed))
        (by
          simpa [List.reverse_cons, List.append_assoc] using
            ih (current :: crossed))

theorem frontTape_equiv_input
    (word : Word MachineCodeSymbol) :
    Tape.Equiv (Tape.input word) (frontTape word) := by
  cases word with
  | nil =>
      simp [frontTape, Tape.input, Tape.blank, Tape.Equiv,
        Tape.dropTrailingNone]
  | cons first rest =>
      simp [frontTape, Tape.input, Tape.Equiv,
        Tape.dropTrailingNone]

def roundMiddle
    (remaining marked : Nat)
    (body : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (MachineDescription.encodeNat remaining)
    (List.append body (copiedTicks marked))

def roundMarkedLeftRev
    (fuel stateCount start marked : Nat) : Word MachineCodeSymbol :=
  MachineCodeSymbol.blank ::
    List.append
      (List.replicate marked MachineCodeSymbol.blank).reverse
      (haltLeftRev fuel stateCount start)

def roundMarkerLeftRev
    (fuel stateCount start marked remaining : Nat)
    (body : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (roundMiddle remaining marked body).reverse
    (roundMarkedLeftRev fuel stateCount start marked)

def roundOutput
    (fuel stateCount start marked remaining : Nat)
    (body : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append
    (MachineCodeSymbol.tick ::
      roundMarkerLeftRev fuel stateCount start marked remaining body).reverse
    [MachineCodeSymbol.header]

theorem roundOutput_eq_workWord
    (fuel stateCount start marked remaining : Nat)
    (body : Word MachineCodeSymbol) :
    roundOutput fuel stateCount start marked remaining body =
      workWord fuel stateCount start (marked + 1) remaining body := by
  have hsucc : marked + 1 = Nat.succ marked := by lia
  rw [hsucc]
  simp [roundOutput, roundMarkerLeftRev, roundMiddle,
    roundMarkedLeftRev, haltLeftRev, workWord, markedHaltField,
    copiedTicks, List.reverse_append, List.reverse_replicate,
    List.append_assoc, List.replicate_succ]
  rw [list_replicate_append_cons_eq_cons_append]
  rw [list_replicate_append_cons_eq_cons_append]

theorem tick_round_canonical
    (fuel stateCount start marked remaining : Nat)
    (body : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (config .fuel []
        (workWord fuel stateCount start marked (remaining + 1) body))
      (frontConfig .fuel
        (workWord fuel stateCount start (marked + 1) remaining body)) := by
  let tail : Word MachineCodeSymbol :=
    List.append body
      (List.append (copiedTicks marked) [MachineCodeSymbol.header])
  have hmetadata := metadata_scan_computes fuel stateCount start
    (List.append (markedHaltField marked (remaining + 1)) tail)
  have hmetadata' : TuringMachine.Computes machine
      (config .fuel []
        (workWord fuel stateCount start marked (remaining + 1) body))
      (config .haltScan (haltLeftRev fuel stateCount start)
        (List.append (markedHaltField marked (remaining + 1)) tail)) := by
    simpa [workWord, tail, List.append_assoc] using hmetadata
  have hmarked := scan_marked_computes marked
    (haltLeftRev fuel stateCount start)
    (List.append (MachineDescription.encodeNat (remaining + 1)) tail)
  have hmarked' : TuringMachine.Computes machine
      (config .haltScan (haltLeftRev fuel stateCount start)
        (List.append (markedHaltField marked (remaining + 1)) tail))
      (config .haltScan
        (List.append
          (List.replicate marked MachineCodeSymbol.blank).reverse
          (haltLeftRev fuel stateCount start))
        (List.append (MachineDescription.encodeNat (remaining + 1)) tail)) := by
    simpa [markedHaltField, List.append_assoc] using hmarked
  have htick := TuringMachine.Computes.step
    (TuringMachine.stepConfig_eq_some_iff_step.mp
      (halt_tick_step
        (List.append
          (List.replicate marked MachineCodeSymbol.blank).reverse
          (haltLeftRev fuel stateCount start))
        (List.append (MachineDescription.encodeNat remaining) tail)))
    (TuringMachine.Computes.refl _)
  have htick' : TuringMachine.Computes machine
      (config .haltScan
        (List.append
          (List.replicate marked MachineCodeSymbol.blank).reverse
          (haltLeftRev fuel stateCount start))
        (List.append (MachineDescription.encodeNat (remaining + 1)) tail))
      (config .seekRight
        (roundMarkedLeftRev fuel stateCount start marked)
        (List.append (MachineDescription.encodeNat remaining) tail)) := by
    simpa [MachineDescription.encodeNat, roundMarkedLeftRev] using htick
  have hseek := seekRight_to_marker_computes
    (roundMarkedLeftRev fuel stateCount start marked)
    (roundMiddle remaining marked body)
  have hseek' : TuringMachine.Computes machine
      (config .seekRight
        (roundMarkedLeftRev fuel stateCount start marked)
        (List.append (MachineDescription.encodeNat remaining) tail))
      (markerConfig
        (roundMarkerLeftRev fuel stateCount start marked remaining body)) := by
    simpa [tail, roundMiddle, roundMarkerLeftRev,
      List.append_assoc] using hseek
  have hmarker := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
      (marker_append_run_exact
        (roundMarkerLeftRev fuel stateCount start marked remaining body)))
  have hrewind := rewind_computes
    (MachineCodeSymbol.tick ::
      roundMarkerLeftRev fuel stateCount start marked remaining body)
    [MachineCodeSymbol.header]
  have hrun := TuringMachine.computes_trans hmetadata' hmarked'
  have hrun := TuringMachine.computes_trans hrun htick'
  have hrun := TuringMachine.computes_trans hrun hseek'
  have hrun := TuringMachine.computes_trans hrun hmarker
  have hrun := TuringMachine.computes_trans hrun hrewind
  rw [← roundOutput_eq_workWord]
  simpa [roundOutput, List.reverse_cons, List.append_assoc] using hrun

theorem config_nil_tape_equiv_input
    (state : Control)
    (word : Word MachineCodeSymbol) :
    Tape.Equiv (config state [] word).tape (Tape.input word) := by
  cases word with
  | nil =>
      simp [config, SerializedShift.cursorTape, Tape.input,
        Tape.blank, Tape.Equiv, Tape.dropTrailingNone]
  | cons first rest =>
      simp [config, SerializedShift.cursorTape, Tape.input,
        Tape.Equiv, Tape.dropTrailingNone]

theorem tick_round_of_tape_equiv
    (fuel stateCount start marked remaining : Nat)
    (body : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (workWord fuel stateCount start marked (remaining + 1) body))
      sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := .fuel, tape := sourceTape }
        { state := .fuel, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (workWord fuel stateCount start (marked + 1) remaining body))
        targetTape := by
  have hcanonical := tick_round_canonical
    fuel stateCount start marked remaining body
  rcases TuringMachine.computes_to_computesIn hcanonical with
    ⟨steps, hcanonicalIn⟩
  have hcanonicalSource : Tape.Equiv
      (config .fuel []
        (workWord fuel stateCount start marked (remaining + 1) body)).tape
      sourceTape :=
    Tape.Equiv.trans
      (config_nil_tape_equiv_input .fuel
        (workWord fuel stateCount start marked (remaining + 1) body))
      hsource
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hcanonicalIn hcanonicalSource with
    ⟨target, hrun, hstate, htape⟩
  rcases target with ⟨targetState, targetTape⟩
  simp only at hstate
  subst targetState
  refine ⟨targetTape, ?_, ?_⟩
  · simpa [config, frontConfig] using
      TuringMachine.computesIn_to_computes hrun
  · exact Tape.Equiv.trans
      (frontTape_equiv_input
        (workWord fuel stateCount start (marked + 1) remaining body))
      htape

theorem copy_remaining
    (fuel stateCount start marked remaining : Nat)
    (body : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (workWord fuel stateCount start marked remaining body))
      sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := .fuel, tape := sourceTape }
        { state := .fuel, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (workWord fuel stateCount start (marked + remaining) 0 body))
        targetTape := by
  induction remaining generalizing marked sourceTape with
  | zero =>
      refine ⟨sourceTape, TuringMachine.Computes.refl _, ?_⟩
      simpa using hsource
  | succ remaining ih =>
      rcases tick_round_of_tape_equiv fuel stateCount start marked
          remaining body sourceTape (by simpa using hsource) with
        ⟨roundTape, hround, hroundTape⟩
      rcases ih (marked + 1) roundTape hroundTape with
        ⟨targetTape, htail, htargetTape⟩
      refine ⟨targetTape,
        TuringMachine.computes_trans hround htail, ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        htargetTape

def restoreConfig
    (remaining restored : Nat)
    (prefixLeftRev tail : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  match remaining with
  | 0 =>
      config .restore prefixLeftRev
        (MachineCodeSymbol.done ::
          List.append
            (List.replicate restored MachineCodeSymbol.tick)
            (MachineCodeSymbol.done :: tail))
  | remaining + 1 =>
      config .restore
        (List.append
          (List.replicate remaining MachineCodeSymbol.blank)
          (MachineCodeSymbol.done :: prefixLeftRev))
        (MachineCodeSymbol.blank ::
          List.append
            (List.replicate restored MachineCodeSymbol.tick)
            (MachineCodeSymbol.done :: tail))

theorem halt_done_to_restore_step
    (marked : Nat)
    (prefixLeftRev tail : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .haltScan
          (List.append
            (List.replicate marked MachineCodeSymbol.blank).reverse
            (MachineCodeSymbol.done :: prefixLeftRev))
          (MachineCodeSymbol.done :: tail)) =
      some (restoreConfig marked 0 prefixLeftRev tail) := by
  cases marked <;> cases prefixLeftRev <;> cases tail <;>
    simp [restoreConfig, config, machine, transition,
      TuringMachine.stepConfig, SerializedShift.cursorTape,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      List.replicate_succ, List.reverse_cons,
      list_replicate_append_cons_eq_cons_append]

theorem restore_mark_step
    (remaining restored : Nat)
    (prefixLeftRev tail : Word MachineCodeSymbol) :
    machine.stepConfig
        (restoreConfig (remaining + 1) restored prefixLeftRev tail) =
      some
        (restoreConfig remaining (restored + 1) prefixLeftRev tail) := by
  cases remaining <;> cases restored <;> cases prefixLeftRev <;>
    cases tail <;>
      simp [restoreConfig, config, machine, transition,
        TuringMachine.stepConfig, SerializedShift.cursorTape,
        Tape.read, Tape.write, Tape.move, Tape.moveLeft,
        List.replicate_succ]

theorem restore_finish_step
    (restored : Nat)
    (prefixLeftRev tail : Word MachineCodeSymbol) :
    machine.stepConfig
        (restoreConfig 0 restored prefixLeftRev tail) =
      some
        (config .seekEnd (MachineCodeSymbol.done :: prefixLeftRev)
          (List.append
            (List.replicate restored MachineCodeSymbol.tick)
            (MachineCodeSymbol.done :: tail))) := by
  cases restored <;> cases prefixLeftRev <;> cases tail <;> rfl

theorem restore_computes
    (remaining restored : Nat)
    (prefixLeftRev tail : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (restoreConfig remaining restored prefixLeftRev tail)
      (config .seekEnd (MachineCodeSymbol.done :: prefixLeftRev)
        (List.append
          (List.replicate (remaining + restored) MachineCodeSymbol.tick)
          (MachineCodeSymbol.done :: tail))) := by
  induction remaining generalizing restored with
  | zero =>
      exact TuringMachine.Computes.step
        (by
          simpa using TuringMachine.stepConfig_eq_some_iff_step.mp
            (restore_finish_step restored prefixLeftRev tail))
        (TuringMachine.Computes.refl _)
  | succ remaining ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (restore_mark_step remaining restored prefixLeftRev tail))
        (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (restored + 1))

def outputMarkerConfig
    (leftRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .installDone
    tape :=
      { left := leftRev.map some
        head := some MachineCodeSymbol.header
        right := [none] } }

theorem seekEnd_symbol_step
    (leftRev rest : Word MachineCodeSymbol)
    (symbol : MachineCodeSymbol) :
    machine.stepConfig
        (config .seekEnd leftRev (symbol :: rest)) =
      some
        (config .seekEnd (symbol :: leftRev) rest) := by
  cases symbol <;> cases leftRev <;> cases rest <;> rfl

theorem seekEnd_none_step
    (leftRev : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .seekEnd
          (MachineCodeSymbol.header :: leftRev) []) =
      some (outputMarkerConfig leftRev) := by
  cases leftRev <;> rfl

theorem seekEnd_to_marker_computes
    (leftRev middle : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (config .seekEnd leftRev
        (List.append middle [MachineCodeSymbol.header]))
      (outputMarkerConfig
        (List.append middle.reverse leftRev)) := by
  induction middle generalizing leftRev with
  | nil =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (seekEnd_symbol_step leftRev [] MachineCodeSymbol.header))
        (TuringMachine.Computes.step
          (by
            simpa using TuringMachine.stepConfig_eq_some_iff_step.mp
              (seekEnd_none_step leftRev))
          (TuringMachine.Computes.refl _))
  | cons symbol rest ih =>
      exact TuringMachine.Computes.step
        (by
          simpa using TuringMachine.stepConfig_eq_some_iff_step.mp
            (seekEnd_symbol_step leftRev
              (List.append rest [MachineCodeSymbol.header]) symbol))
        (by
          simpa [List.reverse_cons, List.append_assoc] using
            ih (symbol :: leftRev))

def outputRewindConfig
    (remainingRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .rewindOutput
    tape := RewindWord.scanTape remainingRev crossed 0 }

def outputReadyConfig
    (word : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .ready
    tape := RewindWord.gateTape word 0 }

theorem installDone_step
    (wordPrefix : Word MachineCodeSymbol)
    (hprefix : wordPrefix ≠ []) :
    machine.stepConfig (outputMarkerConfig wordPrefix.reverse) =
      some (outputRewindConfig wordPrefix.reverse
        [MachineCodeSymbol.done]) := by
  cases wordPrefix with
  | nil => contradiction
  | cons first rest =>
      cases hrest : rest.reverse with
      | nil =>
          cases first <;>
            simp [outputMarkerConfig, outputRewindConfig,
              RewindWord.scanTape, RewindWord.paddingCells, machine,
              transition, TuringMachine.stepConfig, Tape.read, Tape.write,
              Tape.move, Tape.moveLeft, List.reverse_cons, hrest]
      | cons current remaining =>
          cases current <;>
            simp [outputMarkerConfig, outputRewindConfig,
              RewindWord.scanTape, RewindWord.paddingCells, machine,
              transition, TuringMachine.stepConfig, Tape.read, Tape.write,
              Tape.move, Tape.moveLeft, List.reverse_cons, hrest]

theorem output_rewind_symbol_step
    (current : MachineCodeSymbol)
    (remainingRev crossed : Word MachineCodeSymbol) :
    machine.stepConfig
        (outputRewindConfig (current :: remainingRev) crossed) =
      some (outputRewindConfig remainingRev (current :: crossed)) := by
  cases current <;> cases remainingRev <;> cases crossed <;> rfl

theorem output_rewind_finish_step
    (crossed : Word MachineCodeSymbol) :
    machine.stepConfig (outputRewindConfig [] crossed) =
      some (outputReadyConfig crossed) := by
  cases crossed <;> rfl

theorem output_rewind_computes
    (remainingRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (outputRewindConfig remainingRev crossed)
      (outputReadyConfig
        (List.append remainingRev.reverse crossed)) := by
  induction remainingRev generalizing crossed with
  | nil =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (output_rewind_finish_step crossed))
        (TuringMachine.Computes.refl _)
  | cons current remainingRev ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (output_rewind_symbol_step current remainingRev crossed))
        (by
          simpa [List.reverse_cons, List.append_assoc] using
            ih (current :: crossed))

theorem encodeNat_reverse_eq_done_ticks
    (value : Nat) :
    (MachineDescription.encodeNat value).reverse =
      MachineCodeSymbol.done ::
        List.replicate value MachineCodeSymbol.tick := by
  induction value with
  | zero => rfl
  | succ value ih =>
      simp [MachineDescription.encodeNat, List.reverse_cons, ih,
        List.replicate_succ,
        list_replicate_append_cons_eq_cons_append]

theorem encodeNat_eq_ticks_done
    (value : Nat) :
    MachineDescription.encodeNat value =
      List.append (List.replicate value MachineCodeSymbol.tick)
        [MachineCodeSymbol.done] := by
  induction value with
  | zero => rfl
  | succ value ih =>
      rw [MachineDescription.encodeNat, ih]
      simp [List.replicate_succ]

def haltPrefixLeftRev
    (fuel stateCount start : Nat) : Word MachineCodeSymbol :=
  List.append (List.replicate start MachineCodeSymbol.tick)
    (List.append (MachineDescription.encodeNat stateCount).reverse
      (MachineCodeSymbol.header ::
        (MachineDescription.encodeNat fuel).reverse))

theorem haltLeftRev_eq_done_cons
    (fuel stateCount start : Nat) :
    haltLeftRev fuel stateCount start =
      MachineCodeSymbol.done ::
        haltPrefixLeftRev fuel stateCount start := by
  simp [haltLeftRev, haltPrefixLeftRev, metadataPrefix,
    MachineDescription.encodeNatAppend, List.reverse_append,
    encodeNat_reverse_eq_done_ticks, List.append_assoc]

def terminalTail
    (marked : Nat) (body : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  List.append body
    (List.append (copiedTicks marked) [MachineCodeSymbol.header])

def terminalMiddle
    (marked : Nat) (body : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend marked
    (List.append body (copiedTicks marked))

def terminalPrefix
    (fuel stateCount start marked : Nat)
    (body : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (metadataPrefix fuel stateCount start)
    (terminalMiddle marked body)

theorem terminalPrefix_ne_nil
    (fuel stateCount start marked : Nat)
    (body : Word MachineCodeSymbol) :
    terminalPrefix fuel stateCount start marked body ≠ [] := by
  cases fuel <;>
    simp [terminalPrefix, terminalMiddle, metadataPrefix,
      MachineDescription.encodeNatAppend, MachineDescription.encodeNat]

theorem terminalMarkerLeftRev_eq
    (fuel stateCount start marked : Nat)
    (body : Word MachineCodeSymbol) :
    List.append (terminalMiddle marked body).reverse
        (haltLeftRev fuel stateCount start) =
      (terminalPrefix fuel stateCount start marked body).reverse := by
  simp [terminalPrefix, haltLeftRev, List.reverse_append]

theorem terminalOutput_eq_finalWord
    (fuel stateCount start marked : Nat)
    (body : Word MachineCodeSymbol) :
    List.append (terminalPrefix fuel stateCount start marked body)
        [MachineCodeSymbol.done] =
      finalWord fuel stateCount start marked body := by
  have hcopied : List.append (copiedTicks marked)
        [MachineCodeSymbol.done] =
      MachineDescription.encodeNat marked := by
    induction marked with
    | zero => rfl
    | succ marked ih =>
        simpa [MachineDescription.encodeNat, copiedTicks,
          List.replicate_succ] using
          congrArg (fun word => MachineCodeSymbol.tick :: word) ih
  have hlift := congrArg
    (fun tail : Word MachineCodeSymbol =>
      List.append (metadataPrefix fuel stateCount start)
        (MachineDescription.encodeNatAppend marked
          (List.append body tail))) hcopied
  simpa [terminalPrefix, terminalMiddle, finalWord,
    MachineDescription.encodeNatAppend, List.append_assoc] using hlift

theorem finish_canonical
    (fuel stateCount start marked : Nat)
    (body : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (config .fuel []
        (workWord fuel stateCount start marked 0 body))
      (outputReadyConfig
        (finalWord fuel stateCount start marked body)) := by
  let tail := terminalTail marked body
  let prefixLeftRev := haltPrefixLeftRev fuel stateCount start
  have hmetadata := metadata_scan_computes fuel stateCount start
    (List.append (markedHaltField marked 0) tail)
  have hmetadata' : TuringMachine.Computes machine
      (config .fuel []
        (workWord fuel stateCount start marked 0 body))
      (config .haltScan (haltLeftRev fuel stateCount start)
        (List.append (markedHaltField marked 0) tail)) := by
    simpa [workWord, tail, terminalTail, List.append_assoc] using
      hmetadata
  have hmarked := scan_marked_computes marked
    (haltLeftRev fuel stateCount start)
    (MachineCodeSymbol.done :: tail)
  have hmarked' : TuringMachine.Computes machine
      (config .haltScan (haltLeftRev fuel stateCount start)
        (List.append (markedHaltField marked 0) tail))
      (config .haltScan
        (List.append
          (List.replicate marked MachineCodeSymbol.blank).reverse
          (haltLeftRev fuel stateCount start))
        (MachineCodeSymbol.done :: tail)) := by
    simpa [markedHaltField, MachineDescription.encodeNat,
      List.append_assoc] using hmarked
  have hdone := TuringMachine.Computes.step
    (TuringMachine.stepConfig_eq_some_iff_step.mp
      (halt_done_to_restore_step marked prefixLeftRev tail))
    (TuringMachine.Computes.refl _)
  have hdone' : TuringMachine.Computes machine
      (config .haltScan
        (List.append
          (List.replicate marked MachineCodeSymbol.blank).reverse
          (haltLeftRev fuel stateCount start))
        (MachineCodeSymbol.done :: tail))
      (restoreConfig marked 0 prefixLeftRev tail) := by
    simpa [prefixLeftRev, haltLeftRev_eq_done_cons] using hdone
  have hrestore := restore_computes marked 0 prefixLeftRev tail
  have hrestore' : TuringMachine.Computes machine
      (restoreConfig marked 0 prefixLeftRev tail)
      (config .seekEnd (haltLeftRev fuel stateCount start)
        (List.append (terminalMiddle marked body)
          [MachineCodeSymbol.header])) := by
    simpa [prefixLeftRev, haltLeftRev_eq_done_cons,
      terminalMiddle, terminalTail, tail,
      MachineDescription.encodeNatAppend, copiedTicks,
      encodeNat_eq_ticks_done, List.append_assoc] using hrestore
  have hseek := seekEnd_to_marker_computes
    (haltLeftRev fuel stateCount start) (terminalMiddle marked body)
  have hseek' : TuringMachine.Computes machine
      (config .seekEnd (haltLeftRev fuel stateCount start)
        (List.append (terminalMiddle marked body)
          [MachineCodeSymbol.header]))
      (outputMarkerConfig
        (terminalPrefix fuel stateCount start marked body).reverse) := by
    rw [terminalMarkerLeftRev_eq] at hseek
    exact hseek
  have hinstall := TuringMachine.Computes.step
    (TuringMachine.stepConfig_eq_some_iff_step.mp
      (installDone_step
        (terminalPrefix fuel stateCount start marked body)
        (terminalPrefix_ne_nil fuel stateCount start marked body)))
    (TuringMachine.Computes.refl _)
  have hrewind := output_rewind_computes
    (terminalPrefix fuel stateCount start marked body).reverse
    [MachineCodeSymbol.done]
  have hrun := TuringMachine.computes_trans hmetadata' hmarked'
  have hrun := TuringMachine.computes_trans hrun hdone'
  have hrun := TuringMachine.computes_trans hrun hrestore'
  have hrun := TuringMachine.computes_trans hrun hseek'
  have hrun := TuringMachine.computes_trans hrun hinstall
  have hrun := TuringMachine.computes_trans hrun hrewind
  have hrun' : TuringMachine.Computes machine
      (config .fuel []
        (workWord fuel stateCount start marked 0 body))
      (outputReadyConfig
        (List.append
          (terminalPrefix fuel stateCount start marked body)
          [MachineCodeSymbol.done])) := by
    simpa using hrun
  rw [terminalOutput_eq_finalWord] at hrun'
  exact hrun'

theorem finish_of_tape_equiv
    (fuel stateCount start marked : Nat)
    (body : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (workWord fuel stateCount start marked 0 body))
      sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := .fuel, tape := sourceTape }
        { state := .ready, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (finalWord fuel stateCount start marked body))
        targetTape := by
  have hcanonical := finish_canonical
    fuel stateCount start marked body
  rcases TuringMachine.computes_to_computesIn hcanonical with
    ⟨steps, hcanonicalIn⟩
  have hcanonicalSource : Tape.Equiv
      (config .fuel []
        (workWord fuel stateCount start marked 0 body)).tape
      sourceTape :=
    Tape.Equiv.trans
      (config_nil_tape_equiv_input .fuel
        (workWord fuel stateCount start marked 0 body))
      hsource
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hcanonicalIn hcanonicalSource with
    ⟨target, hrun, hstate, htape⟩
  rcases target with ⟨targetState, targetTape⟩
  simp only at hstate
  subst targetState
  refine ⟨targetTape, ?_, ?_⟩
  · simpa [config, outputReadyConfig] using
      TuringMachine.computesIn_to_computes hrun
  · exact Tape.Equiv.trans
      (Tape.Equiv.symm
        (RewindWord.gateTape_equiv_input
          (finalWord fuel stateCount start marked body) 0))
      htape

theorem computes_append_halt
    (fuel stateCount start halt : Nat)
    (body : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (workWord fuel stateCount start 0 halt body))
      sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := .fuel, tape := sourceTape }
        { state := .ready, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (finalWord fuel stateCount start halt body))
        targetTape := by
  rcases copy_remaining fuel stateCount start 0 halt body
      sourceTape hsource with
    ⟨copiedTape, hcopy, hcopiedTape⟩
  have hcopiedTape' : Tape.Equiv
      (Tape.input
        (workWord fuel stateCount start halt 0 body))
      copiedTape := by
    simpa using hcopiedTape
  rcases finish_of_tape_equiv fuel stateCount start halt body
      copiedTape hcopiedTape' with
    ⟨targetTape, hfinish, htargetTape⟩
  exact ⟨targetTape,
    TuringMachine.computes_trans hcopy hfinish, htargetTape⟩


end Machine

end FiniteRecognizer.Interpreter.BooleanContextHaltAppender

end Computability
end FoC
