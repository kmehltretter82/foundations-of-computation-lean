import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.LoopRestaging

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.StackSkip

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep.RuntimeKeySingleKeyRepair
open FiniteRecognizer.Interpreter.LoopRestagingAudit

/-!
**Table-stack context scanner.** Entry records that the selected-action header
lies immediately left of the head. A single header separates adjacent nonempty
table copies, and a double header marks the terminal boundary. The scanner
crosses the second header and exposes the first context-count token while
retaining the crossed stack in baseLeftRev.
-/

inductive Control where
  | afterHeader
  | scan
  | ready
  | halt
deriving DecidableEq

namespace Control

def elems : List Control := [.afterHeader, .scan, .ready, .halt]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control <;> simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .afterHeader, some current =>
      if current = MachineCodeSymbol.header then
        some (some current, Direction.right, .ready)
      else
        some (some current, Direction.right, .scan)
  | .scan, some current =>
      if current = MachineCodeSymbol.header then
        some (some current, Direction.right, .afterHeader)
      else
        some (some current, Direction.right, .scan)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .afterHeader
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def cursorConfig
    (state : Control)
    (baseLeftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := state
  tape := SerializedShift.cursorTape baseLeftRev rest

theorem step_afterHeader_nonheader
    (current : MachineCodeSymbol)
    (baseLeftRev rest : Word MachineCodeSymbol)
    (hcurrent : current ≠ MachineCodeSymbol.header) :
    machine.stepConfig
        (cursorConfig .afterHeader baseLeftRev (current :: rest)) =
      some (cursorConfig .scan (current :: baseLeftRev) rest) := by
  cases rest <;> cases current <;>
    simp [machine, transition, cursorConfig, SerializedShift.cursorTape,
      TuringMachine.stepConfig, Tape.read, Tape.write, Tape.move,
      Tape.moveRight] at hcurrent ⊢
  done

theorem step_scan_nonheader
    (current : MachineCodeSymbol)
    (baseLeftRev rest : Word MachineCodeSymbol)
    (hcurrent : current ≠ MachineCodeSymbol.header) :
    machine.stepConfig
        (cursorConfig .scan baseLeftRev (current :: rest)) =
      some (cursorConfig .scan (current :: baseLeftRev) rest) := by
  cases rest <;> cases current <;>
    simp [machine, transition, cursorConfig, SerializedShift.cursorTape,
      TuringMachine.stepConfig, Tape.read, Tape.write, Tape.move,
      Tape.moveRight] at hcurrent ⊢
  done

theorem step_scan_header
    (baseLeftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (cursorConfig .scan baseLeftRev
          (MachineCodeSymbol.header :: rest)) =
      some
        (cursorConfig .afterHeader
          (MachineCodeSymbol.header :: baseLeftRev) rest) := by
  cases rest <;> cases baseLeftRev <;> rfl
  done

theorem step_terminal_header
    (baseLeftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (cursorConfig .afterHeader baseLeftRev
          (MachineCodeSymbol.header :: rest)) =
      some
        (cursorConfig .ready
          (MachineCodeSymbol.header :: baseLeftRev) rest) := by
  cases rest <;> cases baseLeftRev <;> rfl
  done

theorem runConfigExact_trans
    {first second : Nat}
    {source middle target :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (hfirst : machine.runConfigExact? first source = some middle)
    (hsecond : machine.runConfigExact? second middle = some target) :
    machine.runConfigExact? (first + second) source = some target := by
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr
  exact TuringMachine.computesIn_trans
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hfirst)
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hsecond)
  done

theorem run_scan_noheaders
    (baseLeftRev symbols suffix : Word MachineCodeSymbol)
    (hnoHeader : transitionListParserNoHeader symbols) :
    machine.runConfigExact? symbols.length
        (cursorConfig .scan baseLeftRev
          (List.append symbols suffix)) =
      some
        (cursorConfig .scan
          (List.append symbols.reverse baseLeftRev) suffix) := by
  induction symbols generalizing baseLeftRev with
  | nil =>
      rfl
  | cons current more ih =>
      change machine.runConfigExact? (more.length + 1)
        (cursorConfig .scan baseLeftRev
          (current :: List.append more suffix)) = _
      rw [TuringMachine.runConfigExact?]
      rw [step_scan_nonheader current baseLeftRev
        (List.append more suffix)
        (hnoHeader current (List.Mem.head more))]
      simp only
      have hmore : transitionListParserNoHeader more := by
        intro symbol hmem
        exact hnoHeader symbol (List.Mem.tail current hmem)
      simpa [List.reverse_cons, List.append_assoc] using
        ih (current :: baseLeftRev) hmore
  done

theorem rawTable_nonempty_shape
    (first : TransitionDescription)
    (rest : List TransitionDescription) :
    FiniteRecognizer.Interpreter.LoopRestagingAudit.rawTable (first :: rest) =
      MachineCodeSymbol.transition ::
        runtimeKeyRawTransitionTail first rest [] := by
  rfl
  done

theorem rawTable_no_header
    (first : TransitionDescription)
    (rest : List TransitionDescription) :
    transitionListParserNoHeader
      (FiniteRecognizer.Interpreter.LoopRestagingAudit.rawTable (first :: rest)) := by
  unfold FiniteRecognizer.Interpreter.LoopRestagingAudit.rawTable
    MachineDescription.encodeTransitions
  apply transitionListParser_encodeTransitionsAppend_noHeader
  intro symbol hmem
  simp at hmem
  done

theorem run_one_copy
    (baseLeftRev suffix : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription) :
    let table := FiniteRecognizer.Interpreter.LoopRestagingAudit.rawTable (first :: rest)
    machine.runConfigExact? (table.length + 1)
        (cursorConfig .afterHeader baseLeftRev
          (List.append table (MachineCodeSymbol.header :: suffix))) =
      some
        (cursorConfig .afterHeader
          (MachineCodeSymbol.header ::
            List.append table.reverse baseLeftRev)
          suffix) := by
  dsimp only
  rw [rawTable_nonempty_shape]
  let tail := runtimeKeyRawTransitionTail first rest []
  have htable : transitionListParserNoHeader
      (MachineCodeSymbol.transition :: tail) := by
    simpa [tail, rawTable_nonempty_shape] using
      rawTable_no_header first rest
  have hfirst :
      machine.runConfigExact? 1
          (cursorConfig .afterHeader baseLeftRev
            (MachineCodeSymbol.transition ::
              List.append tail (MachineCodeSymbol.header :: suffix))) =
        some
          (cursorConfig .scan
            (MachineCodeSymbol.transition :: baseLeftRev)
            (List.append tail (MachineCodeSymbol.header :: suffix))) := by
    rw [TuringMachine.runConfigExact?]
    rw [step_afterHeader_nonheader]
    · rfl
    · simp
  have htail := run_scan_noheaders
    (MachineCodeSymbol.transition :: baseLeftRev) tail
    (MachineCodeSymbol.header :: suffix)
    (by
      intro symbol hmem
      exact htable symbol (List.Mem.tail MachineCodeSymbol.transition hmem))
  have hseparator :
      machine.runConfigExact? 1
          (cursorConfig .scan
            (List.append tail.reverse
              (MachineCodeSymbol.transition :: baseLeftRev))
            (MachineCodeSymbol.header :: suffix)) =
        some
          (cursorConfig .afterHeader
            (MachineCodeSymbol.header ::
              List.append tail.reverse
                (MachineCodeSymbol.transition :: baseLeftRev))
            suffix) := by
    rw [TuringMachine.runConfigExact?]
    rw [step_scan_header]
    rfl
  have hfirstTail := runConfigExact_trans hfirst htail
  have hall := runConfigExact_trans hfirstTail hseparator
  simpa [tail, List.reverse_cons, List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall
  done

def sourceConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (context : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  cursorConfig .afterHeader baseLeftRev
    (List.append
      (FiniteRecognizer.Interpreter.LoopRestagingAudit.tableStack (first :: rest) copies)
      context)

def targetConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (context : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  cursorConfig .ready
    (List.append
      (FiniteRecognizer.Interpreter.LoopRestagingAudit.tableStack
        (first :: rest) copies).reverse
      baseLeftRev)
    context

/-- Exact stack skip for every copy count. The nonempty split first :: rest
makes the terminal double header unambiguous. -/
theorem run_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (context : Word MachineCodeSymbol) :
    machine.runConfigExact?
        (FiniteRecognizer.Interpreter.LoopRestagingAudit.tableStack
          (first :: rest) copies).length
        (sourceConfig baseLeftRev first rest copies context) =
      some (targetConfig baseLeftRev first rest copies context) := by
  induction copies generalizing baseLeftRev with
  | zero =>
      rw [FiniteRecognizer.Interpreter.LoopRestagingAudit.tableStack_zero]
      change machine.runConfigExact? 1
        (cursorConfig .afterHeader baseLeftRev
          (MachineCodeSymbol.header :: context)) = _
      rw [TuringMachine.runConfigExact?]
      rw [step_terminal_header]
      rfl
  | succ copies ih =>
      rw [FiniteRecognizer.Interpreter.LoopRestagingAudit.tableStack_succ]
      let table := FiniteRecognizer.Interpreter.LoopRestagingAudit.rawTable (first :: rest)
      have hone := run_one_copy baseLeftRev
        (List.append
          (FiniteRecognizer.Interpreter.LoopRestagingAudit.tableStack
            (first :: rest) copies)
          context)
        first rest
      have hrest := ih
        (MachineCodeSymbol.header ::
          List.append table.reverse baseLeftRev)
      have hall := runConfigExact_trans hone hrest
      simpa [sourceConfig, targetConfig, table,
        FiniteRecognizer.Interpreter.LoopRestagingAudit.tableStack_succ,
        List.reverse_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall
  done

/-- Context specialization used by the direct updater.  The endpoint head is
the first unary token of the encoded left-context count. -/
theorem run_context_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (tape : Tape Bool)
    (haltState : Nat)
    (callerSuffix : Word MachineCodeSymbol) :
    machine.runConfigExact?
        (FiniteRecognizer.Interpreter.LoopRestagingAudit.tableStack
          (first :: rest) copies).length
        (sourceConfig baseLeftRev first rest copies
          (FiniteRecognizer.Interpreter.LoopRestagingAudit.contextTail tape haltState
            callerSuffix)) =
      some
        (targetConfig baseLeftRev first rest copies
          (FiniteRecognizer.Interpreter.LoopRestagingAudit.contextTail tape haltState
            callerSuffix)) := by
  exact run_exact baseLeftRev first rest copies _
  done


end FiniteRecognizer.Interpreter.StackSkip

end Computability
end FoC
