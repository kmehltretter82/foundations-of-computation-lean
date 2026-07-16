import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.PersistentCopy
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.LoopRestaging

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.InitializerRepeatedCopy

open FiniteRecognizer.Interpreter.LoopRestagingAudit
open FiniteRecognizer.Interpreter.InitializerPersistentCopy
open FiniteRecognizer.Interpreter.InitializerPersistentCopy.PersistentMasterCopier

/-!
# Repeated table-copy phase

The inner copier is a terminal phase. The outer driver retargets `ready`,
performs the preserving left move, decrements serialized fuel, and re-enters
the copier. The induction currency gives zero copies the final `header`
sentinel and inserts one delimiter with each copy.
-/

/-- Word obtained by the mathematical repeated-copy recurrence. -/
def repeatedCopyWord
    (transitions : List TransitionDescription) :
    Nat -> Word MachineCodeSymbol -> Word MachineCodeSymbol
  | 0, context => MachineCodeSymbol.header :: context
  | copies + 1, context =>
      List.append (rawTable transitions)
        (MachineCodeSymbol.header ::
          repeatedCopyWord transitions copies context)

/-- Ordinary interpreter-stack currency with a caller-owned context tail. -/
def stackSuffix
    (transitions : List TransitionDescription)
    (copies : Nat)
    (context : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (tableStack transitions copies) context

theorem repeatedCopyWord_eq_stackSuffix
    (transitions : List TransitionDescription)
    (copies : Nat)
    (context : Word MachineCodeSymbol) :
    repeatedCopyWord transitions copies context =
      stackSuffix transitions copies context := by
  induction copies with
  | zero => rfl
  | succ copies ih =>
      rw [repeatedCopyWord, ih]
      change
        List.append
            (show List MachineCodeSymbol from rawTable transitions)
            (MachineCodeSymbol.header ::
              List.append
                (show List MachineCodeSymbol from
                  tableStack transitions copies)
                context) =
          List.append
            (show List MachineCodeSymbol from
              tableStack transitions (copies + 1))
            context
      rw [tableStack_succ]
      exact
        (List.append_assoc
          (show List MachineCodeSymbol from rawTable transitions)
          (MachineCodeSymbol.header ::
            (show List MachineCodeSymbol from tableStack transitions copies))
          context).symm

theorem stackSuffix_zero
    (transitions : List TransitionDescription)
    (context : Word MachineCodeSymbol) :
    stackSuffix transitions 0 context =
      MachineCodeSymbol.header :: context := by
  rfl

theorem copiedActiveWord_eq_stackSuffix_succ
    (transitions : List TransitionDescription)
    (copies : Nat)
    (context : Word MachineCodeSymbol) :
    List.append (MachineDescription.encodeTransitions transitions)
        (MachineCodeSymbol.header ::
          stackSuffix transitions copies context) =
      stackSuffix transitions (copies + 1) context := by
  change
    List.append
        (show List MachineCodeSymbol from
          MachineDescription.encodeTransitions transitions)
        (MachineCodeSymbol.header ::
          List.append
            (show List MachineCodeSymbol from tableStack transitions copies)
            context) =
      List.append
        (show List MachineCodeSymbol from
          tableStack transitions (copies + 1))
        context
  rw [tableStack_succ]
  exact
    (List.append_assoc
      (show List MachineCodeSymbol from rawTable transitions)
      (MachineCodeSymbol.header ::
        (show List MachineCodeSymbol from tableStack transitions copies))
      context).symm

def copyPassSource
    (baseLeftRev : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (context : Word MachineCodeSymbol) :=
  sourceConfig baseLeftRev
    (MachineDescription.encodeTransitions (first :: rest))
    (stackSuffix (first :: rest) copies context)

def copyPassTarget
    (baseLeftRev : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (context : Word MachineCodeSymbol) :=
  readyConfig baseLeftRev
    (MachineDescription.encodeTransitions (first :: rest))
    (MachineCodeSymbol.header ::
      stackSuffix (first :: rest) copies context)

theorem copyPass_run_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (context : Word MachineCodeSymbol) :
    machine.runConfigExact?
        (runSteps
          (MachineDescription.encodeTransitions (first :: rest))
          (stackSuffix (first :: rest) copies context))
        (copyPassSource baseLeftRev first rest copies context) =
      some (copyPassTarget baseLeftRev first rest copies context) := by
  exact raw_transition_table_run_exact baseLeftRev first rest
    (stackSuffix (first :: rest) copies context)

theorem copyPassTarget_active_word
    (baseLeftRev : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (context : Word MachineCodeSymbol) :
    (copyPassTarget baseLeftRev first rest copies context).tape =
      tapeAtCells
        (none ::
          (MachineDescription.encodeTransitions (first :: rest)).reverse.map
            some ++ none :: baseLeftRev.map some)
        (representedCells
          (stackSuffix (first :: rest) (copies + 1) context)) := by
  unfold copyPassTarget readyConfig readyTape
  rw [copiedActiveWord_eq_stackSuffix_succ]

/-- The exact physical handoff between two mathematical copy iterations.
Control-state retargeting belongs to the outer initializer, so this theorem
states only the tape equality it must use. -/
theorem copyPassTarget_move_left_eq_nextSource_tape
    (baseLeftRev : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (context : Word MachineCodeSymbol) :
    Tape.move Direction.left
        (copyPassTarget baseLeftRev first rest copies context).tape =
      (copyPassSource baseLeftRev first rest (copies + 1) context).tape := by
  have hmaster :
      MachineDescription.encodeTransitions (first :: rest) =
        MachineCodeSymbol.transition ::
          (MachineDescription.encodeTransitions (first :: rest)).tail := by
    rfl
  have hmove :=
    FiniteRecognizer.Interpreter.InitializerPersistentCopy.PersistentMasterCopier.move_left_readyConfig_tape_eq_sourceConfig_tape
      baseLeftRev
      (MachineCodeSymbol.header ::
        stackSuffix (first :: rest) copies context)
      MachineCodeSymbol.transition
      (MachineDescription.encodeTransitions (first :: rest)).tail
  rw [← hmaster] at hmove
  rw [copiedActiveWord_eq_stackSuffix_succ] at hmove
  simpa [copyPassTarget, copyPassSource] using hmove

/-!
### Explicit outer initializer branch split

Only the third branch enters the repeated nonempty-master copier.  Zero fuel
and an empty transition list are semantically final comparisons and must not
be sent through a nonempty-table copying theorem.
-/

theorem fuel_and_source_split
    (D : MachineDescription)
    (fuel : Nat) :
    fuel = 0 ∨
      (exists remaining : Nat, fuel = remaining + 1 ∧ D.transitions = []) ∨
      (exists remaining : Nat,
        exists first : TransitionDescription,
        exists rest : List TransitionDescription,
          fuel = remaining + 1 ∧ D.transitions = first :: rest) := by
  cases fuel with
  | zero => exact Or.inl rfl
  | succ remaining =>
      right
      cases htransitions : D.transitions with
      | nil =>
          exact Or.inl ⟨remaining, rfl, rfl⟩
      | cons first rest =>
          exact Or.inr ⟨remaining, first, rest, rfl, rfl⟩

theorem input_start_split
    (input : Word MachineCodeSymbol) :
    input = [] ∨
      exists first : MachineCodeSymbol,
      exists rest : Word MachineCodeSymbol,
        input = first :: rest := by
  cases input with
  | nil => exact Or.inl rfl
  | cons first rest => exact Or.inr ⟨first, rest, rfl⟩


end FiniteRecognizer.Interpreter.InitializerRepeatedCopy

end Computability
end FoC
