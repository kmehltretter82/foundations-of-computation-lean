import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.FinalGate.MarkerBuilder

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.FinalGateMaterializer

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep.RuntimeKeySingleKeyRepair
open FiniteRecognizer.Interpreter.LoopRestagingAudit
open FiniteRecognizer.Interpreter.StackIteration

namespace HaltCopier

inductive Control where
  | seekSource (token : Bool)
  | seekDestination (token : Bool)
  | advance
  | seekProcessed
  | readNext
  | eraseRight
  | cleanupErased
  | installBlank
  | rewindOutput
  | ready
  | halt
deriving DecidableEq

namespace Control

def elems : List Control :=
  [.seekSource false, .seekSource true,
   .seekDestination false, .seekDestination true,
   .advance, .seekProcessed, .readNext, .eraseRight,
   .cleanupErased, .installBlank, .rewindOutput, .ready, .halt]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | seekSource token => cases token <;> simp [elems]
    | seekDestination token => cases token <;> simp [elems]
    | advance => simp [elems]
    | seekProcessed => simp [elems]
    | readNext => simp [elems]
    | eraseRight => simp [elems]
    | cleanupErased => simp [elems]
    | installBlank => simp [elems]
    | rewindOutput => simp [elems]
    | ready => simp [elems]
    | halt => simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .seekSource token, some MachineCodeSymbol.moveRight =>
      some (some MachineCodeSymbol.moveRight, Direction.left,
        .seekDestination token)
  | .seekSource token, read =>
      some (read, Direction.right, .seekSource token)
  | .seekDestination token, some MachineCodeSymbol.header =>
      if token then
        some (some MachineCodeSymbol.done, Direction.right, .eraseRight)
      else
        some (some MachineCodeSymbol.tick, Direction.right, .advance)
  | .seekDestination token, some symbol =>
      some (some symbol, Direction.left, .seekDestination token)
  | .advance, some MachineCodeSymbol.moveRight =>
      some (some MachineCodeSymbol.header, Direction.right, .readNext)
  | .advance, _ =>
      some (some MachineCodeSymbol.header, Direction.right, .seekProcessed)
  | .seekProcessed, some MachineCodeSymbol.moveRight =>
      some (some MachineCodeSymbol.blank, Direction.right, .readNext)
  | .seekProcessed, read =>
      some (read, Direction.right, .seekProcessed)
  | .readNext, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.moveRight, Direction.left,
        .seekDestination false)
  | .readNext, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.moveRight, Direction.left,
        .seekDestination true)
  | .eraseRight, some _ =>
      some (some MachineCodeSymbol.moveLeft, Direction.right, .eraseRight)
  | .eraseRight, none =>
      some (none, Direction.left, .cleanupErased)
  | .cleanupErased, some MachineCodeSymbol.moveLeft =>
      some (none, Direction.left, .cleanupErased)
  | .cleanupErased, some symbol =>
      some (some symbol, Direction.right, .installBlank)
  | .installBlank, _ =>
      some (some MachineCodeSymbol.blank, Direction.left, .rewindOutput)
  | .rewindOutput, some symbol =>
      some (some symbol, Direction.left, .rewindOutput)
  | .rewindOutput, none =>
      some (none, Direction.right, .ready)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .seekSource false
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def sourceConfig
    (built gap : Word MachineCodeSymbol)
    (value : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .seekSource (firstToken value)
  tape := SerializedShift.cursorTape
    (MachineCodeSymbol.header :: built.reverse)
    (List.append gap
      (MachineCodeSymbol.moveRight ::
        List.append (tokenTail value) suffix))

def seekSourceTargetTape
    (baseLeftRev gap tail : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  Tape.move Direction.left
    (SerializedShift.cursorTape
      (List.append gap.reverse baseLeftRev)
      (MachineCodeSymbol.moveRight :: tail))

def seekSourceConfig
    (token : Bool)
    (baseLeftRev gap tail : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .seekSource token
  tape := SerializedShift.cursorTape baseLeftRev
    (List.append gap (MachineCodeSymbol.moveRight :: tail))

def seekSourceTargetConfig
    (token : Bool)
    (baseLeftRev gap tail : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .seekDestination token
  tape := seekSourceTargetTape baseLeftRev gap tail

theorem step_seekSource_symbol
    (token : Bool)
    (baseLeftRev rest tail : Word MachineCodeSymbol)
    (symbol : MachineCodeSymbol)
    (hsymbol : symbol ≠ MachineCodeSymbol.moveRight) :
    machine.stepConfig
        (seekSourceConfig token baseLeftRev (symbol :: rest) tail) =
      some (seekSourceConfig token (symbol :: baseLeftRev) rest tail) := by
  cases token <;> cases symbol <;> cases rest <;> cases tail <;>
    simp_all [seekSourceConfig, machine, transition,
      TuringMachine.stepConfig, Tape.read, SerializedShift.cursorTape,
      Tape.write, Tape.move, Tape.moveRight, List.map_append]
  done

theorem step_seekSource_marker
    (token : Bool)
    (baseLeftRev tail : Word MachineCodeSymbol) :
    machine.stepConfig
        (seekSourceConfig token baseLeftRev [] tail) =
      some (seekSourceTargetConfig token baseLeftRev [] tail) := by
  cases token <;> cases baseLeftRev <;> cases tail <;> rfl
  done

theorem seekSource_run_exact
    (token : Bool)
    (baseLeftRev gap tail : Word MachineCodeSymbol)
    (hgap : forall symbol : MachineCodeSymbol,
      List.Mem symbol gap -> symbol ≠ MachineCodeSymbol.moveRight) :
    machine.runConfigExact? (gap.length + 1)
        (seekSourceConfig token baseLeftRev gap tail) =
      some (seekSourceTargetConfig token baseLeftRev gap tail) := by
  induction gap generalizing baseLeftRev with
  | nil =>
      rw [TuringMachine.runConfigExact?]
      rw [step_seekSource_marker]
      rfl
  | cons symbol rest ih =>
      have hsymbol := hgap symbol (List.Mem.head rest)
      have hrest : forall candidate : MachineCodeSymbol,
          List.Mem candidate rest ->
            candidate ≠ MachineCodeSymbol.moveRight := by
        intro candidate hmem
        exact hgap candidate (List.Mem.tail symbol hmem)
      change machine.runConfigExact? ((rest.length + 1) + 1)
        (seekSourceConfig token baseLeftRev (symbol :: rest) tail) = _
      rw [TuringMachine.runConfigExact?]
      rw [step_seekSource_symbol token baseLeftRev rest tail symbol hsymbol]
      simp only
      simpa [seekSourceTargetConfig, seekSourceTargetTape,
        List.reverse_cons, List.append_assoc] using
        ih (symbol :: baseLeftRev) hrest
  done

def destinationScanTape
    (built remainingRev crossed tail : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      SerializedShift.cursorTape built.reverse
        (MachineCodeSymbol.header ::
          List.append crossed (MachineCodeSymbol.moveRight :: tail))
  | current :: more =>
      SerializedShift.cursorTape
        (List.append more
          (MachineCodeSymbol.header :: built.reverse))
        (current ::
          List.append crossed (MachineCodeSymbol.moveRight :: tail))

def markedConfig
    (built gap : Word MachineCodeSymbol)
    (value : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .seekDestination (firstToken value)
  tape := destinationScanTape built gap.reverse []
    (List.append (tokenTail value) suffix)

def outputWord
    (built : Word MachineCodeSymbol)
    (value : Nat) : Word MachineCodeSymbol :=
  List.append built
    (MachineDescription.encodeNatAppend value [MachineCodeSymbol.blank])

def nextGap : Word MachineCodeSymbol -> Word MachineCodeSymbol
  | [] => []
  | _ :: rest => List.append rest [MachineCodeSymbol.blank]

def destinationConfig
    (token : Bool)
    (built remainingRev crossed tail : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .seekDestination token
  tape := destinationScanTape built remainingRev crossed tail

theorem step_seekDestination_symbol
    (token : Bool)
    (built : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (remainingRev crossed tail : Word MachineCodeSymbol)
    (hcurrent : current ≠ MachineCodeSymbol.header) :
    machine.stepConfig
        (destinationConfig token built (current :: remainingRev)
          crossed tail) =
      some
        (destinationConfig token built remainingRev
          (current :: crossed) tail) := by
  cases token <;> cases current <;> cases remainingRev <;>
    cases crossed <;> cases tail <;>
      simp_all [destinationConfig, destinationScanTape, machine, transition,
        TuringMachine.stepConfig, Tape.read, SerializedShift.cursorTape,
        Tape.write, Tape.move, Tape.moveLeft, List.map_append]
  done

theorem seekDestination_run_exact
    (token : Bool)
    (built remainingRev crossed tail : Word MachineCodeSymbol)
    (hremaining : forall symbol : MachineCodeSymbol,
      List.Mem symbol remainingRev -> symbol ≠ MachineCodeSymbol.header) :
    machine.runConfigExact? remainingRev.length
        (destinationConfig token built remainingRev crossed tail) =
      some
        (destinationConfig token built []
          (List.append remainingRev.reverse crossed) tail) := by
  induction remainingRev generalizing crossed with
  | nil => rfl
  | cons current more ih =>
      have hcurrent := hremaining current (List.Mem.head more)
      have hmore : forall symbol : MachineCodeSymbol,
          List.Mem symbol more -> symbol ≠ MachineCodeSymbol.header := by
        intro symbol hmem
        exact hremaining symbol (List.Mem.tail current hmem)
      change machine.runConfigExact? (more.length + 1)
        (destinationConfig token built (current :: more) crossed tail) = _
      rw [TuringMachine.runConfigExact?]
      rw [step_seekDestination_symbol token built current more crossed tail
        hcurrent]
      simp only
      simpa [List.reverse_cons, List.append_assoc] using
        ih (current :: crossed) hmore
  done

theorem step_destination_tick
    (built gap tail : Word MachineCodeSymbol) :
    machine.stepConfig
        (destinationConfig false built [] gap tail) =
      some
        { state := .advance
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.tick :: built.reverse)
            (List.append gap (MachineCodeSymbol.moveRight :: tail)) } := by
  cases gap <;> cases tail <;> rfl
  done

theorem step_destination_done
    (built gap tail : Word MachineCodeSymbol) :
    machine.stepConfig
        (destinationConfig true built [] gap tail) =
      some
        { state := .eraseRight
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.done :: built.reverse)
            (List.append gap (MachineCodeSymbol.moveRight :: tail)) } := by
  cases gap <;> cases tail <;> rfl
  done

def seekProcessedConfig
    (baseLeftRev remaining tail : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .seekProcessed
  tape := SerializedShift.cursorTape baseLeftRev
    (List.append remaining (MachineCodeSymbol.moveRight :: tail))

def seekProcessedTargetConfig
    (baseLeftRev remaining tail : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .readNext
  tape := SerializedShift.cursorTape
    (MachineCodeSymbol.blank ::
      List.append remaining.reverse baseLeftRev) tail

theorem step_seekProcessed_symbol
    (baseLeftRev rest tail : Word MachineCodeSymbol)
    (symbol : MachineCodeSymbol)
    (hsymbol : symbol ≠ MachineCodeSymbol.moveRight) :
    machine.stepConfig
        (seekProcessedConfig baseLeftRev (symbol :: rest) tail) =
      some (seekProcessedConfig (symbol :: baseLeftRev) rest tail) := by
  cases symbol <;> cases rest <;> cases tail <;>
    simp_all [seekProcessedConfig, machine, transition,
      TuringMachine.stepConfig, Tape.read, SerializedShift.cursorTape,
      Tape.write, Tape.move, Tape.moveRight, List.map_append]
  done

theorem step_seekProcessed_marker
    (baseLeftRev tail : Word MachineCodeSymbol) :
    machine.stepConfig (seekProcessedConfig baseLeftRev [] tail) =
      some (seekProcessedTargetConfig baseLeftRev [] tail) := by
  cases tail <;> rfl
  done

theorem seekProcessed_run_exact
    (baseLeftRev remaining tail : Word MachineCodeSymbol)
    (hremaining : forall symbol : MachineCodeSymbol,
      List.Mem symbol remaining -> symbol ≠ MachineCodeSymbol.moveRight) :
    machine.runConfigExact? (remaining.length + 1)
        (seekProcessedConfig baseLeftRev remaining tail) =
      some (seekProcessedTargetConfig baseLeftRev remaining tail) := by
  induction remaining generalizing baseLeftRev with
  | nil =>
      rw [TuringMachine.runConfigExact?]
      rw [step_seekProcessed_marker]
      rfl
  | cons symbol rest ih =>
      have hsymbol := hremaining symbol (List.Mem.head rest)
      have hrest : forall candidate : MachineCodeSymbol,
          List.Mem candidate rest ->
            candidate ≠ MachineCodeSymbol.moveRight := by
        intro candidate hmem
        exact hremaining candidate (List.Mem.tail symbol hmem)
      change machine.runConfigExact? ((rest.length + 1) + 1)
        (seekProcessedConfig baseLeftRev (symbol :: rest) tail) = _
      rw [TuringMachine.runConfigExact?]
      rw [step_seekProcessed_symbol baseLeftRev rest tail symbol hsymbol]
      simp only
      simpa [seekProcessedTargetConfig, List.reverse_cons,
        List.append_assoc] using ih (symbol :: baseLeftRev) hrest
  done

def readNextConfig
    (built gap tail : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .readNext
  tape := SerializedShift.cursorTape
    (List.append (nextGap gap).reverse
      (MachineCodeSymbol.header ::
        (List.append built [MachineCodeSymbol.tick]).reverse))
    tail

theorem advance_to_readNext_computes
    (built gap tail : Word MachineCodeSymbol)
    (hgap : forall symbol : MachineCodeSymbol,
      List.Mem symbol gap -> symbol ≠ MachineCodeSymbol.moveRight) :
    TuringMachine.Computes machine
      { state := Control.advance
        tape := SerializedShift.cursorTape
          (MachineCodeSymbol.tick :: built.reverse)
          (List.append gap (MachineCodeSymbol.moveRight :: tail)) }
      (readNextConfig built gap tail) := by
  cases gap with
  | nil =>
      have hstep : TuringMachine.Step machine
          { state := Control.advance
            tape := SerializedShift.cursorTape
              (MachineCodeSymbol.tick :: built.reverse)
              (MachineCodeSymbol.moveRight :: tail) }
          (readNextConfig built [] tail) := by
        apply TuringMachine.stepConfig_eq_some_iff_step.mp
        cases built <;> cases tail <;>
          simp [machine, transition, TuringMachine.stepConfig,
            readNextConfig, nextGap, SerializedShift.cursorTape,
            Tape.read, Tape.write, Tape.move, Tape.moveRight,
            List.reverse_append]
      exact TuringMachine.Computes.step hstep
        (TuringMachine.Computes.refl _)
  | cons first rest =>
      have hfirst := hgap first (List.Mem.head rest)
      have hrest : forall symbol : MachineCodeSymbol,
          List.Mem symbol rest -> symbol ≠ MachineCodeSymbol.moveRight := by
        intro symbol hmem
        exact hgap symbol (List.Mem.tail first hmem)
      have hstep : TuringMachine.Step machine
          { state := Control.advance
            tape := SerializedShift.cursorTape
              (MachineCodeSymbol.tick :: built.reverse)
              (first ::
                List.append rest (MachineCodeSymbol.moveRight :: tail)) }
          (seekProcessedConfig
            (MachineCodeSymbol.header :: MachineCodeSymbol.tick ::
              built.reverse) rest tail) := by
        apply TuringMachine.stepConfig_eq_some_iff_step.mp
        cases first <;> cases rest <;> cases tail <;>
          simp_all [machine, transition, TuringMachine.stepConfig,
            Tape.read, SerializedShift.cursorTape, Tape.write,
            Tape.move, Tape.moveRight, seekProcessedConfig,
            List.map_append]
      have hscan := seekProcessed_run_exact
        (MachineCodeSymbol.header :: MachineCodeSymbol.tick :: built.reverse)
        rest tail hrest
      exact TuringMachine.Computes.step hstep
        (by
          have hcomputes := TuringMachine.computesIn_to_computes
            (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hscan)
          simpa [readNextConfig, seekProcessedTargetConfig, nextGap,
            List.reverse_append, List.reverse_cons,
            List.append_assoc] using hcomputes)
  done

theorem destinationScanTape_reverse
    (built gap tail : Word MachineCodeSymbol) :
    destinationScanTape built gap.reverse [] tail =
      Tape.move Direction.left
        (SerializedShift.cursorTape
          (List.append gap.reverse
            (MachineCodeSymbol.header :: built.reverse))
          (MachineCodeSymbol.moveRight :: tail)) := by
  cases gap with
  | nil => cases tail <;> rfl
  | cons first rest =>
      cases hrev : rest.reverse <;> cases tail <;>
        simp [destinationScanTape, hrev, Tape.move, Tape.moveLeft,
          SerializedShift.cursorTape, List.map_append,
          List.reverse_cons, List.append_assoc]
  done

theorem step_readNext
    (built gap : Word MachineCodeSymbol)
    (value : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (readNextConfig built gap
          (MachineDescription.encodeNatAppend value suffix)) =
      some
        (markedConfig (List.append built [MachineCodeSymbol.tick])
          (nextGap gap) value suffix) := by
  have htail :
      MachineDescription.encodeNatAppend value suffix =
        tokenSymbol (firstToken value) ::
          List.append (tokenTail value) suffix := by
    rw [MachineDescription.encodeNatAppend,
      encodeNat_eq_firstToken_cons_tail]
    rfl
  rw [htail]
  rw [markedConfig, destinationScanTape_reverse]
  cases firstToken value <;> cases gap <;> cases built <;>
    simp [readNextConfig, machine, transition, tokenSymbol,
      TuringMachine.stepConfig, Tape.read, SerializedShift.cursorTape,
      Tape.write, Tape.move, Tape.moveLeft, nextGap,
      List.map_append, List.reverse_append]
  done

theorem nextGap_no_header
    (gap : Word MachineCodeSymbol)
    (hgap : forall symbol : MachineCodeSymbol,
      List.Mem symbol gap -> symbol ≠ MachineCodeSymbol.header) :
    forall symbol : MachineCodeSymbol,
      List.Mem symbol (nextGap gap) ->
        symbol ≠ MachineCodeSymbol.header := by
  cases gap with
  | nil =>
      intro symbol hmem
      cases hmem
  | cons first rest =>
      intro symbol hmem
      rw [nextGap] at hmem
      rcases List.mem_append.mp hmem with hrest | hblank
      · exact hgap symbol (List.Mem.tail first hrest)
      · simp at hblank
        subst symbol
        decide
  done

theorem nextGap_no_moveRight
    (gap : Word MachineCodeSymbol)
    (hgap : forall symbol : MachineCodeSymbol,
      List.Mem symbol gap -> symbol ≠ MachineCodeSymbol.moveRight) :
    forall symbol : MachineCodeSymbol,
      List.Mem symbol (nextGap gap) ->
        symbol ≠ MachineCodeSymbol.moveRight := by
  cases gap with
  | nil =>
      intro symbol hmem
      cases hmem
  | cons first rest =>
      intro symbol hmem
      rw [nextGap] at hmem
      rcases List.mem_append.mp hmem with hrest | hblank
      · exact hgap symbol (List.Mem.tail first hrest)
      · simp at hblank
        subst symbol
        decide
  done

def eraseConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (erased : Nat)
    (remaining : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .eraseRight
  tape := SerializedShift.cursorTape
    (List.append
      (List.replicate erased MachineCodeSymbol.moveLeft)
      baseLeftRev)
    remaining

theorem step_erase_symbol
    (baseLeftRev : Word MachineCodeSymbol)
    (erased : Nat)
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (eraseConfig baseLeftRev erased (first :: rest)) =
      some (eraseConfig baseLeftRev erased.succ rest) := by
  cases first <;> cases erased <;> cases baseLeftRev <;> cases rest <;>
    simp [eraseConfig, machine, transition, TuringMachine.stepConfig,
      SerializedShift.cursorTape, Tape.read, Tape.write, Tape.move,
      Tape.moveRight, List.map_append, List.replicate_succ]
  done

theorem erase_run_exact
    (baseLeftRev remaining : Word MachineCodeSymbol)
    (erased : Nat) :
    machine.runConfigExact? remaining.length
        (eraseConfig baseLeftRev erased remaining) =
      some
        (eraseConfig baseLeftRev (remaining.length + erased) []) := by
  induction remaining generalizing erased with
  | nil =>
      change some (eraseConfig baseLeftRev erased []) = _
      simp only [List.length_nil, Nat.zero_add]
  | cons first rest ih =>
      change machine.runConfigExact? (rest.length + 1)
        (eraseConfig baseLeftRev erased (first :: rest)) = _
      rw [TuringMachine.runConfigExact?]
      rw [step_erase_symbol]
      simp only
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih erased.succ
  done

def cleanupConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (remainingMarkers rightPadding : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .cleanupErased
  tape :=
    { left :=
        (List.append
          (List.replicate remainingMarkers MachineCodeSymbol.moveLeft)
          baseLeftRev).map some
      head := some MachineCodeSymbol.moveLeft
      right := List.replicate rightPadding none }

def cleanupBoundaryConfig
    (boundary : MachineCodeSymbol)
    (baseRest : Word MachineCodeSymbol)
    (rightPaddingTail : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .cleanupErased
  tape :=
    { left := baseRest.map some
      head := some boundary
      right := none :: List.replicate rightPaddingTail none }

def installBlankConfig
    (boundary : MachineCodeSymbol)
    (baseRest : Word MachineCodeSymbol)
    (rightPaddingTail : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .installBlank
  tape :=
    { left := (boundary :: baseRest).map some
      head := none
      right := List.replicate rightPaddingTail none }

def rewindScanConfig
    (remainingRev : Word MachineCodeSymbol)
    (rightCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  match remainingRev with
  | [] =>
      { state := .rewindOutput
        tape := { left := [], head := none, right := rightCells } }
  | current :: more =>
      { state := .rewindOutput
        tape :=
          { left := more.map some
            head := some current
            right := rightCells } }

def readyConfig
    (cells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .ready
  tape := Tape.move Direction.right
    { left := [], head := none, right := cells }

theorem step_erase_blank
    (boundary : MachineCodeSymbol)
    (baseRest : Word MachineCodeSymbol)
    (remainingMarkers : Nat) :
    machine.stepConfig
        (eraseConfig (boundary :: baseRest)
          remainingMarkers.succ []) =
      some
        (cleanupConfig (boundary :: baseRest)
          remainingMarkers 1) := by
  cases boundary <;> cases remainingMarkers <;> cases baseRest <;>
    simp [eraseConfig, cleanupConfig, machine, transition,
      TuringMachine.stepConfig, SerializedShift.cursorTape,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft,
      List.map_append, List.replicate_succ]
  done

theorem step_cleanup_marker
    (baseLeftRev : Word MachineCodeSymbol)
    (remainingMarkers rightPadding : Nat) :
    machine.stepConfig
        (cleanupConfig baseLeftRev remainingMarkers.succ rightPadding) =
      some
        (cleanupConfig baseLeftRev remainingMarkers rightPadding.succ) := by
  cases remainingMarkers <;> cases rightPadding <;>
    cases baseLeftRev <;>
      simp [cleanupConfig, machine, transition,
        TuringMachine.stepConfig, Tape.read, Tape.write, Tape.move,
        Tape.moveLeft, List.map_append, List.replicate_succ]
  done

theorem step_cleanup_last
    (boundary : MachineCodeSymbol)
    (baseRest : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    machine.stepConfig
        (cleanupConfig (boundary :: baseRest) 0 rightPadding) =
      some (cleanupBoundaryConfig boundary baseRest rightPadding) := by
  cases boundary <;> cases rightPadding <;> cases baseRest <;> rfl
  done

theorem cleanup_run_exact
    (boundary : MachineCodeSymbol)
    (baseRest : Word MachineCodeSymbol)
    (remainingMarkers rightPadding : Nat) :
    machine.runConfigExact? (remainingMarkers + 1)
        (cleanupConfig (boundary :: baseRest)
          remainingMarkers rightPadding) =
      some
        (cleanupBoundaryConfig boundary baseRest
          (remainingMarkers + rightPadding)) := by
  induction remainingMarkers generalizing rightPadding with
  | zero =>
      rw [TuringMachine.runConfigExact?]
      rw [step_cleanup_last]
      change some (cleanupBoundaryConfig boundary baseRest rightPadding) = _
      simp only [Nat.zero_add]
  | succ remainingMarkers ih =>
      change machine.runConfigExact? ((remainingMarkers + 1) + 1)
        (cleanupConfig (boundary :: baseRest)
          remainingMarkers.succ rightPadding) = _
      rw [TuringMachine.runConfigExact?]
      rw [step_cleanup_marker]
      simp only
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih rightPadding.succ
  done

theorem step_cleanup_boundary
    (boundary : MachineCodeSymbol)
    (baseRest : Word MachineCodeSymbol)
    (rightPaddingTail : Nat)
    (hboundary : boundary ≠ MachineCodeSymbol.moveLeft) :
    machine.stepConfig
        (cleanupBoundaryConfig boundary baseRest rightPaddingTail) =
      some (installBlankConfig boundary baseRest rightPaddingTail) := by
  cases boundary <;> cases baseRest <;> cases rightPaddingTail <;>
    simp_all [cleanupBoundaryConfig, installBlankConfig, machine,
      transition, TuringMachine.stepConfig, Tape.read, Tape.write,
      Tape.move, Tape.moveRight, List.replicate_succ]
  done

theorem step_install_blank
    (boundary : MachineCodeSymbol)
    (baseRest : Word MachineCodeSymbol)
    (rightPaddingTail : Nat) :
    machine.stepConfig
        (installBlankConfig boundary baseRest rightPaddingTail) =
      some
        (rewindScanConfig (boundary :: baseRest)
          (some MachineCodeSymbol.blank ::
            List.replicate rightPaddingTail none)) := by
  cases boundary <;> cases baseRest <;> cases rightPaddingTail <;> rfl
  done

theorem step_rewind_symbol
    (current : MachineCodeSymbol)
    (more : Word MachineCodeSymbol)
    (rightCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (rewindScanConfig (current :: more) rightCells) =
      some
        (rewindScanConfig more (some current :: rightCells)) := by
  cases current <;> cases more <;> cases rightCells <;> rfl
  done

theorem rewind_run_exact
    (remainingRev : Word MachineCodeSymbol)
    (rightCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? remainingRev.length
        (rewindScanConfig remainingRev rightCells) =
      some
        (rewindScanConfig []
          (List.append (remainingRev.reverse.map some) rightCells)) := by
  induction remainingRev generalizing rightCells with
  | nil =>
      rfl
  | cons current more ih =>
      change machine.runConfigExact? (more.length + 1)
        (rewindScanConfig (current :: more) rightCells) = _
      rw [TuringMachine.runConfigExact?]
      rw [step_rewind_symbol]
      simp only
      simpa [List.reverse_cons, List.map_append,
        List.append_assoc] using ih (some current :: rightCells)
  done

theorem step_rewind_ready
    (cells : List (Option MachineCodeSymbol)) :
    machine.stepConfig (rewindScanConfig [] cells) =
      some (readyConfig cells) := by
  cases cells <;> rfl
  done

theorem computes_of_run_exact
    {steps : Nat}
    {source target :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (hrun : machine.runConfigExact? steps source = some target) :
    TuringMachine.Computes machine source target :=
  TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrun)

theorem computes_one_of_stepConfig
    {source target :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (hstep : machine.stepConfig source = some target) :
    TuringMachine.Computes machine source target :=
  TuringMachine.computes_of_step
    (TuringMachine.stepConfig_eq_some_iff_step.mp hstep)

def cleanupReadyCells
    (built : Word MachineCodeSymbol)
    (rightPadding : Nat) : List (Option MachineCodeSymbol) :=
  List.append
    ((MachineCodeSymbol.done :: built.reverse).reverse.map some)
    (some MachineCodeSymbol.blank ::
      List.replicate rightPadding none)

theorem erase_finish_computes
    (built : Word MachineCodeSymbol)
    (garbageFirst : MachineCodeSymbol)
    (garbageRest : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (eraseConfig (MachineCodeSymbol.done :: built.reverse) 0
        (garbageFirst :: garbageRest))
      (readyConfig
        (cleanupReadyCells built (garbageRest.length + 1))) := by
  let baseLeftRev : Word MachineCodeSymbol :=
    MachineCodeSymbol.done :: built.reverse
  have heraseRaw := erase_run_exact baseLeftRev
    (garbageFirst :: garbageRest) 0
  have herase : TuringMachine.Computes machine
      (eraseConfig baseLeftRev 0 (garbageFirst :: garbageRest))
      (eraseConfig baseLeftRev (garbageRest.length + 1) []) := by
    simpa [Nat.add_zero] using computes_of_run_exact heraseRaw
  have hblank := computes_one_of_stepConfig
    (step_erase_blank MachineCodeSymbol.done built.reverse
      garbageRest.length)
  have hcleanup := computes_of_run_exact
    (cleanup_run_exact MachineCodeSymbol.done built.reverse
      garbageRest.length 1)
  have hboundary := computes_one_of_stepConfig
    (step_cleanup_boundary MachineCodeSymbol.done built.reverse
      (garbageRest.length + 1) (by decide))
  have hinstall := computes_one_of_stepConfig
    (step_install_blank MachineCodeSymbol.done built.reverse
      (garbageRest.length + 1))
  have hrewind := computes_of_run_exact
    (rewind_run_exact
      (MachineCodeSymbol.done :: built.reverse)
      (some MachineCodeSymbol.blank ::
        List.replicate (garbageRest.length + 1) none))
  have hready := computes_one_of_stepConfig
    (step_rewind_ready
      (cleanupReadyCells built (garbageRest.length + 1)))
  apply TuringMachine.computes_trans herase
  apply TuringMachine.computes_trans
    (by simpa [baseLeftRev] using hblank)
  apply TuringMachine.computes_trans hcleanup
  apply TuringMachine.computes_trans hboundary
  apply TuringMachine.computes_trans hinstall
  apply TuringMachine.computes_trans
    (by simpa [cleanupReadyCells, List.reverse_cons,
      List.map_append, List.append_assoc] using hrewind)
  simpa [cleanupReadyCells, List.reverse_cons,
    List.map_append, List.append_assoc] using hready
  done

theorem ready_tape_equiv_output_zero
    (built : Word MachineCodeSymbol)
    (rightPadding : Nat) :
    Tape.Equiv
      (readyConfig (cleanupReadyCells built rightPadding)).tape
      (Tape.input (outputWord built 0)) := by
  cases built with
  | nil =>
      simp [readyConfig, cleanupReadyCells, outputWord,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, Tape.Equiv, Tape.input,
        Tape.move, Tape.moveRight, Tape.dropTrailingNone]
      exact FoC.Computability.dropTrailingNone_replicate_none rightPadding
  | cons first rest =>
      simp [readyConfig, cleanupReadyCells, outputWord,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, Tape.Equiv, Tape.input,
        Tape.move, Tape.moveRight, List.reverse_cons,
        List.map_append, List.append_assoc]
      exact ⟨rfl,
        (by
          simpa [List.append_assoc] using
            (FoC.Computability.dropTrailingNone_append_replicate_none
              (List.append (rest.map some)
                [some MachineCodeSymbol.done,
                  some MachineCodeSymbol.blank])
          rightPadding))⟩
  done

theorem outputWord_succ
    (built : Word MachineCodeSymbol)
    (value : Nat) :
    outputWord
        (List.append built [MachineCodeSymbol.tick]) value =
      outputWord built value.succ := by
  simp [outputWord, MachineDescription.encodeNatAppend,
    MachineDescription.encodeNat, List.append_assoc]
  done

theorem copyMarked_computes
    (built gap : Word MachineCodeSymbol)
    (value : Nat)
    (suffix : Word MachineCodeSymbol)
    (hgapHeader : forall symbol : MachineCodeSymbol,
      List.Mem symbol gap -> symbol ≠ MachineCodeSymbol.header)
    (hgapMarker : forall symbol : MachineCodeSymbol,
      List.Mem symbol gap -> symbol ≠ MachineCodeSymbol.moveRight) :
    exists target : TuringMachine.Configuration MachineCodeSymbol Control,
      TuringMachine.Computes machine
        (markedConfig built gap value suffix) target ∧
      target.state = Control.ready ∧
      Tape.Equiv target.tape (Tape.input (outputWord built value)) := by
  induction value generalizing built gap suffix with
  | zero =>
      have hreverse : forall symbol : MachineCodeSymbol,
          List.Mem symbol gap.reverse ->
            symbol ≠ MachineCodeSymbol.header := by
        intro symbol hmem
        exact hgapHeader symbol (List.mem_reverse.mp hmem)
      have hscanRaw := seekDestination_run_exact true built
        gap.reverse [] suffix hreverse
      have hscan : TuringMachine.Computes machine
          (markedConfig built gap 0 suffix)
          (destinationConfig true built [] gap suffix) := by
        simpa [markedConfig, destinationConfig, tokenTail, firstToken,
          List.reverse_reverse] using computes_of_run_exact hscanRaw
      have hdone := computes_one_of_stepConfig
        (step_destination_done built gap suffix)
      cases gap with
      | nil =>
          let target := readyConfig
            (cleanupReadyCells built (suffix.length + 1))
          have herase := erase_finish_computes built
            MachineCodeSymbol.moveRight suffix
          have herase' : TuringMachine.Computes machine
              { state := Control.eraseRight
                tape := SerializedShift.cursorTape
                  (MachineCodeSymbol.done :: built.reverse)
                  (MachineCodeSymbol.moveRight :: suffix) }
              target := by
            simpa [target, eraseConfig] using herase
          refine ⟨target,
            TuringMachine.computes_trans hscan
              (TuringMachine.computes_trans hdone herase'),
            rfl, ?_⟩
          exact ready_tape_equiv_output_zero built (suffix.length + 1)
      | cons first rest =>
          let garbageRest : Word MachineCodeSymbol :=
            List.append rest (MachineCodeSymbol.moveRight :: suffix)
          let target := readyConfig
            (cleanupReadyCells built (garbageRest.length + 1))
          have herase := erase_finish_computes built first garbageRest
          have herase' : TuringMachine.Computes machine
              { state := Control.eraseRight
                tape := SerializedShift.cursorTape
                  (MachineCodeSymbol.done :: built.reverse)
                  (first :: garbageRest) }
              target := by
            simpa [target, eraseConfig] using herase
          refine ⟨target,
            TuringMachine.computes_trans hscan
              (TuringMachine.computes_trans
                (by simpa [garbageRest, List.append_assoc] using hdone)
                herase'),
            rfl, ?_⟩
          exact ready_tape_equiv_output_zero built
            (garbageRest.length + 1)
  | succ value ih =>
      have hreverse : forall symbol : MachineCodeSymbol,
          List.Mem symbol gap.reverse ->
            symbol ≠ MachineCodeSymbol.header := by
        intro symbol hmem
        exact hgapHeader symbol (List.mem_reverse.mp hmem)
      have hscanRaw := seekDestination_run_exact false built
        gap.reverse []
        (MachineDescription.encodeNatAppend value suffix) hreverse
      have hscan : TuringMachine.Computes machine
          (markedConfig built gap value.succ suffix)
          (destinationConfig false built [] gap
            (MachineDescription.encodeNatAppend value suffix)) := by
        simpa [markedConfig, destinationConfig, tokenTail, firstToken,
          MachineDescription.encodeNatAppend,
          List.reverse_reverse] using computes_of_run_exact hscanRaw
      have htick := computes_one_of_stepConfig
        (step_destination_tick built gap
          (MachineDescription.encodeNatAppend value suffix))
      have hadvance := advance_to_readNext_computes built gap
        (MachineDescription.encodeNatAppend value suffix) hgapMarker
      have hread := computes_one_of_stepConfig
        (step_readNext built gap value suffix)
      have hnextHeader := nextGap_no_header gap hgapHeader
      have hnextMarker := nextGap_no_moveRight gap hgapMarker
      rcases ih
          (List.append built [MachineCodeSymbol.tick])
          (nextGap gap) suffix hnextHeader hnextMarker with
        ⟨target, htail, hstate, htape⟩
      refine ⟨target,
        TuringMachine.computes_trans hscan
          (TuringMachine.computes_trans htick
            (TuringMachine.computes_trans hadvance
              (TuringMachine.computes_trans hread htail))),
        hstate, ?_⟩
      rw [← outputWord_succ]
      exact htape
  done

theorem copy_computes
    (built gap : Word MachineCodeSymbol)
    (value : Nat)
    (suffix : Word MachineCodeSymbol)
    (hgapHeader : forall symbol : MachineCodeSymbol,
      List.Mem symbol gap -> symbol ≠ MachineCodeSymbol.header)
    (hgapMarker : forall symbol : MachineCodeSymbol,
      List.Mem symbol gap -> symbol ≠ MachineCodeSymbol.moveRight) :
    exists target : TuringMachine.Configuration MachineCodeSymbol Control,
      TuringMachine.Computes machine
        (sourceConfig built gap value suffix) target ∧
      target.state = Control.ready ∧
      Tape.Equiv target.tape (Tape.input (outputWord built value)) := by
  have hseekRaw := seekSource_run_exact (firstToken value)
    (MachineCodeSymbol.header :: built.reverse) gap
    (List.append (tokenTail value) suffix) hgapMarker
  have hseek : TuringMachine.Computes machine
      (sourceConfig built gap value suffix)
      (markedConfig built gap value suffix) := by
    have hcomputes := computes_of_run_exact hseekRaw
    simpa [sourceConfig, seekSourceConfig, seekSourceTargetConfig,
      seekSourceTargetTape, markedConfig, destinationScanTape_reverse,
      List.append_assoc] using hcomputes
  rcases copyMarked_computes built gap value suffix
      hgapHeader hgapMarker with
    ⟨target, hcopy, hstate, htape⟩
  exact ⟨target, TuringMachine.computes_trans hseek hcopy,
    hstate, htape⟩
  done


end HaltCopier

end FiniteRecognizer.Interpreter.FinalGateMaterializer

end Computability
end FoC
