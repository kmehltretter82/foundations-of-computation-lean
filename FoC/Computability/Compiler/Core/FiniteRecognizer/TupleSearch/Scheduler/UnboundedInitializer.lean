import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.SplitLayout
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.Basic

set_option doc.verso true

/-!
**Unbounded-scheduler initializer.** This fixed-prefix initializer leaves the
public input in place.  It walks once to the input's left, writes the
construction-time fixed word from right to left, and returns to the first
fixed-word token.
-/

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.UnboundedInitializer

open Languages
open ExactFuel.StrictProbe

namespace LeftPrefixWriter

inductive Control (fixedWord : List MachineCodeSymbol) where
  | enter
  | write (index : Fin (fixedWord.length + 1))
  | halt
deriving DecidableEq

namespace Control

def elems (fixedWord : List MachineCodeSymbol) : List (Control fixedWord) :=
  .enter ::
    List.append
      ((Foundation.FiniteType.fin (fixedWord.length + 1)).elems.map Control.write)
      [.halt]

def finite (fixedWord : List MachineCodeSymbol) :
    Foundation.FiniteType (Control fixedWord) where
  elems := elems fixedWord
  complete := by
    intro control
    cases control with
    | enter => simp [elems]
    | write index =>
        have h := (Foundation.FiniteType.fin
          (fixedWord.length + 1)).complete index
        simp [elems, h]
    | halt => simp [elems]

end Control

def stateAt (fixedWord : List MachineCodeSymbol) (index : Nat)
    (hle : index ≤ fixedWord.length) : Control fixedWord :=
  .write ⟨index, by lia⟩

def transition (fixedWord : List MachineCodeSymbol) :
    Control fixedWord -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control fixedWord)
  | .enter, read =>
      some (read, Direction.left, stateAt fixedWord 0 (by simp))
  | .write index, read =>
      if h : index.val < fixedWord.length then
        some
          (some (fixedWord.get ⟨index.val, h⟩),
            Direction.left,
            stateAt fixedWord (index.val + 1) (by lia))
      else
        some (read, Direction.right, .halt)
  | .halt, _ => none

def machine (fixedWord : List MachineCodeSymbol) :
    TuringMachine MachineCodeSymbol (Control fixedWord) where
  start := .enter
  halt := .halt
  transition := transition fixedWord
  statesFinite := Control.finite fixedWord

def inputCells (input : Word MachineCodeSymbol) :
    List (Option MachineCodeSymbol) :=
  (Tape.input input).head :: (Tape.input input).right

def writeTape (written : List MachineCodeSymbol)
    (input : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  { left := []
    head := none
    right := List.append (written.reverse.map some) (inputCells input) }

def writeConfig (fixedWord written rest : List MachineCodeSymbol)
    (input : Word MachineCodeSymbol)
    (hprefix : fixedWord = List.append written rest) :
    TuringMachine.Configuration MachineCodeSymbol (Control fixedWord) :=
  { state := stateAt fixedWord written.length (by
      rw [hprefix]
      simp)
    tape := writeTape written input }

def endpointTape (fixedWord : List MachineCodeSymbol)
    (input : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  Tape.moveRight (writeTape fixedWord input)

def endpointConfig (fixedWord : List MachineCodeSymbol)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control fixedWord) :=
  { state := .halt
    tape := endpointTape fixedWord input }

theorem enter_step (fixedWord : List MachineCodeSymbol)
    (input : Word MachineCodeSymbol) :
    (machine fixedWord).stepConfig
        (TuringMachine.initial (machine fixedWord) input) =
      some (writeConfig fixedWord [] fixedWord input (by simp)) := by
  cases input <;>
    simp [TuringMachine.stepConfig, TuringMachine.initial, machine,
      transition, writeConfig, writeTape, inputCells, stateAt,
      Tape.input, Tape.blank, Tape.read, Tape.write, Tape.move, Tape.moveLeft]

theorem write_step_of_split
    (fixedWord written rest : List MachineCodeSymbol)
    (input : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (hprefix : fixedWord =
      List.append written (current :: rest)) :
    (machine fixedWord).stepConfig
        (writeConfig fixedWord written (current :: rest) input hprefix) =
      some
        (writeConfig fixedWord (List.append written [current]) rest input
          (hprefix.trans (by
            simpa using
              (List.append_assoc written [current] rest).symm))) := by
  unfold TuringMachine.stepConfig
  dsimp [machine, writeConfig, transition, stateAt]
  have hlt : written.length < fixedWord.length := by
    rw [hprefix]
    simp
  simp only [hlt, ↓reduceDIte]
  have hget : fixedWord[written.length] = current := by
    exact List.getElem_of_append hprefix rfl
  rw [hget]
  simp [writeTape, Tape.write, Tape.move, Tape.moveLeft,
    List.reverse_append]

theorem write_run_of_split
    (fixedWord written rest : List MachineCodeSymbol)
    (input : Word MachineCodeSymbol)
    (hprefix : fixedWord = List.append written rest) :
    (machine fixedWord).runConfigExact? rest.length
        (writeConfig fixedWord written rest input hprefix) =
      some (writeConfig fixedWord fixedWord [] input (by simp)) := by
  induction rest generalizing written with
  | nil =>
      have hwritten : written = fixedWord := by
        have happend : List.append written [] = written := by
          induction written with
          | nil => rfl
          | cons current rest ih => simp [List.append, ih]
        rw [happend] at hprefix
        exact hprefix.symm
      subst written
      simp [TuringMachine.runConfigExact?, writeConfig, stateAt]
  | cons current rest ih =>
      change (machine fixedWord).runConfigExact? (rest.length + 1)
        (writeConfig fixedWord written (current :: rest) input hprefix) = _
      rw [TuringMachine.runConfigExact?]
      rw [write_step_of_split fixedWord written rest input current hprefix]
      simp only
      exact ih (List.append written [current])
        (hprefix.trans (by
          simpa using
            (List.append_assoc written [current] rest).symm))

theorem finish_step (fixedWord : List MachineCodeSymbol)
    (input : Word MachineCodeSymbol) :
    (machine fixedWord).stepConfig
        (writeConfig fixedWord fixedWord [] input (by simp)) =
      some (endpointConfig fixedWord input) := by
  simp [TuringMachine.stepConfig, machine, transition, writeConfig,
    stateAt, endpointConfig, endpointTape, Tape.write_read_eq_self,
    Tape.move]

theorem run_exact (fixedWord : List MachineCodeSymbol)
    (input : Word MachineCodeSymbol) :
    (machine fixedWord).runConfigExact? (fixedWord.length + 2)
        (TuringMachine.initial (machine fixedWord) input) =
      some (endpointConfig fixedWord input) := by
  have hsplit : fixedWord = List.append [] fixedWord := by simp
  have henter :
      (machine fixedWord).runConfigExact? 1
          (TuringMachine.initial (machine fixedWord) input) =
        some (writeConfig fixedWord [] fixedWord input hsplit) := by
    rw [TuringMachine.runConfigExact?]
    rw [enter_step]
    rfl
  rw [show fixedWord.length + 2 = 1 + (fixedWord.length + 1) by lia]
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append]
  rw [henter]
  simp only
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append]
  rw [write_run_of_split fixedWord [] fixedWord input hsplit]
  simp only
  rw [TuringMachine.runConfigExact?, finish_step]
  rfl

theorem endpointTape_equiv_input_append
    (fixedWord : List MachineCodeSymbol) (input : Word MachineCodeSymbol)
    (hnonempty : fixedWord ≠ []) :
    Tape.Equiv (endpointTape fixedWord input)
      (Tape.input
        (show Word MachineCodeSymbol from
          List.append fixedWord.reverse
            (show List MachineCodeSymbol from input))) := by
  cases hreverse : fixedWord.reverse with
  | nil =>
      apply False.elim
      apply hnonempty
      simpa using congrArg List.reverse hreverse
  | cons first rest =>
      cases input <;>
        simp [endpointTape, writeTape, inputCells, hreverse, Tape.input,
          Tape.blank, Tape.moveRight, Tape.Equiv, Tape.dropTrailingNone,
          FoC.Computability.dropTrailingNone_append_none,
          List.map_append]

theorem computes_prefix (fixedWord : List MachineCodeSymbol)
    (input : Word MachineCodeSymbol)
    (hnonempty : fixedWord ≠ []) :
    TuringMachine.Computes (machine fixedWord)
      (TuringMachine.initial (machine fixedWord) input)
      (endpointConfig fixedWord input) ∧
    Tape.Equiv (endpointConfig fixedWord input).tape
      (Tape.input
        (show Word MachineCodeSymbol from
          List.append fixedWord.reverse
            (show List MachineCodeSymbol from input))) := by
  exact ⟨TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
        (run_exact fixedWord input)),
    endpointTape_equiv_input_append fixedWord input hnonempty⟩

end LeftPrefixWriter

def initialCursor : Scheduler.Layout.Cursor :=
  { round := 0, inner := 0, outer := 0, selectedFuel := 0 }

def initialFrame (input : Word MachineCodeSymbol) :
    Scheduler.Layout.Frame :=
  { geometry := .unbounded
    cursor := initialCursor
    input := input }

def initialPrefix : List MachineCodeSymbol :=
  show List MachineCodeSymbol from
    Scheduler.SplitLayout.encode (initialFrame [])

theorem initialFrame_valid (input : Word MachineCodeSymbol) :
    (initialFrame input).cursor.Valid (initialFrame input).geometry := by
  simp [initialFrame, initialCursor, Scheduler.Layout.Cursor.Valid,
    Scheduler.Layout.Geometry.pairBound]

theorem encode_initialFrame_eq (input : Word MachineCodeSymbol) :
    Scheduler.SplitLayout.encode (initialFrame input) =
      (show Word MachineCodeSymbol from
        List.append initialPrefix (show List MachineCodeSymbol from input)) := by
  simp [Scheduler.SplitLayout.encode,
    Scheduler.SplitLayout.encodeSplitAppend,
    Scheduler.SplitLayout.candidateWord,
    Scheduler.Layout.encodeGeometryAppend,
    GeneratedCode.nestedStageCode, GeneratedCode.stageCode,
    MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
    initialFrame, initialCursor, initialPrefix, List.append_assoc]

theorem initialPrefix_ne_nil : initialPrefix ≠ [] := by
  simp [initialPrefix, Scheduler.SplitLayout.encode]

def machine := LeftPrefixWriter.machine initialPrefix.reverse

def targetConfig (input : Word MachineCodeSymbol) :=
  LeftPrefixWriter.endpointConfig initialPrefix.reverse input

theorem initializes (input : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (TuringMachine.initial machine input)
      (targetConfig input) ∧
    Tape.Equiv (targetConfig input).tape
      (Tape.input (Scheduler.SplitLayout.encode (initialFrame input))) := by
  rcases LeftPrefixWriter.computes_prefix initialPrefix.reverse input
      (by simpa using initialPrefix_ne_nil) with ⟨hrun, htape⟩
  refine ⟨hrun, ?_⟩
  rw [encode_initialFrame_eq]
  simpa [targetConfig] using htape

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.UnboundedInitializer
