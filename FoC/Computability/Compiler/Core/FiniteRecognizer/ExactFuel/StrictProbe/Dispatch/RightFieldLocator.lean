import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.Fuel
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseRetarget

set_option doc.verso true

/-!
# Serialized right-field locator

Finite location and decoding of the right-side fields in a protected exact-fuel
frame.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Dispatch
namespace RightFieldLocator

open SerializedFieldComposer

namespace Counter

/-- The count-driven portion of {lit}`SerializedFieldComposer.HeadLocator`,
stopped exactly when all left
cells have been marked and the head-cell decoder is ready. -/
inductive Control where
  | markCountBoundary
  | returnCountStart
  | countCheck
  | seekCountBoundary
  | seekCellDone
  | returnCount
  | gate
deriving DecidableEq

namespace Control

def elems : List Control :=
  [.markCountBoundary, .returnCountStart, .countCheck,
    .seekCountBoundary, .seekCellDone, .returnCount, .gate]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control <;> simp [elems]

end Control


def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .markCountBoundary, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right,
        .markCountBoundary)
  | .markCountBoundary, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.blank, Direction.left,
        .returnCountStart)
  | .returnCountStart, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.left,
        .returnCountStart)
  | .returnCountStart, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .countCheck)
  | .countCheck, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.transition, Direction.right,
        .seekCountBoundary)
  | .countCheck, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.blank, Direction.right, .gate)
  | .seekCountBoundary, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right,
        .seekCountBoundary)
  | .seekCountBoundary, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.blank, Direction.right,
        .seekCellDone)
  | .seekCellDone, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .seekCellDone)
  | .seekCellDone, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.right, .seekCellDone)
  | .seekCellDone, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.header, Direction.left, .returnCount)
  | .returnCount, some MachineCodeSymbol.transition =>
      some (some MachineCodeSymbol.transition, Direction.right, .countCheck)
  | .returnCount, some symbol =>
      some (some symbol, Direction.left, .returnCount)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .markCountBoundary
  halt := .gate
  transition := transition
  statesFinite := Control.finite

def config (control : Control)
    (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := control
  tape := SerializedShift.cursorTape leftRev rest

def returnCountStartConfig
    (remaining crossed suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  match remaining with
  | [] =>
      config .returnCountStart []
        (List.append crossed (MachineCodeSymbol.blank :: suffix))
  | current :: rest =>
      { state := .returnCountStart
        tape :=
          { left := rest.map some
            head := some current
            right :=
              (List.append crossed
                (MachineCodeSymbol.blank :: suffix)).map some } }

theorem markCount_tick_step (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .markCountBoundary leftRev
          (MachineCodeSymbol.tick :: suffix)) =
      some
        (config .markCountBoundary
          (MachineCodeSymbol.tick :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem markCount_done_step (leftHead : MachineCodeSymbol)
    (leftTail suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .markCountBoundary (leftHead :: leftTail)
          (MachineCodeSymbol.done :: suffix)) =
      some
        (returnCountStartConfig (leftHead :: leftTail) [] suffix) := by
  rfl

theorem markCount_run_exact (count : Nat)
    (leftHead : MachineCodeSymbol)
    (leftTail suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (count + 1)
        (config .markCountBoundary (leftHead :: leftTail)
          (MachineDescription.encodeNatAppend count suffix)) =
      some
        (returnCountStartConfig
          (List.append (HeadLocator.ticks count)
            (leftHead :: leftTail)) [] suffix) := by
  induction count generalizing leftHead leftTail with
  | zero =>
      exact markCount_done_step leftHead leftTail suffix
  | succ count ih =>
      change
        machine.runConfigExact? ((count + 1) + 1)
          (config .markCountBoundary (leftHead :: leftTail)
            (MachineCodeSymbol.tick ::
              MachineDescription.encodeNatAppend count suffix)) = _
      rw [TuringMachine.runConfigExact?]
      rw [markCount_tick_step]
      simp only
      rw [ih MachineCodeSymbol.tick (leftHead :: leftTail)]
      have hwords :
          List.append (HeadLocator.ticks count)
              (MachineCodeSymbol.tick :: leftHead :: leftTail) =
            List.append (HeadLocator.ticks (count + 1))
              (leftHead :: leftTail) := by
        calc
          List.append (HeadLocator.ticks count)
              (MachineCodeSymbol.tick :: leftHead :: leftTail) =
              MachineCodeSymbol.tick ::
                List.append (HeadLocator.ticks count)
                  (leftHead :: leftTail) :=
            HeadLocator.ticks_append_tick count (leftHead :: leftTail)
          _ = List.append (HeadLocator.ticks (count + 1))
                (leftHead :: leftTail) := by
            rfl
      exact congrArg
        (fun word => some (returnCountStartConfig word [] suffix)) hwords

theorem returnCountStart_tick_step_nonempty
    (rest crossed suffix : Word MachineCodeSymbol)
    (hrest : rest ≠ []) :
    machine.stepConfig
        (returnCountStartConfig
          (MachineCodeSymbol.tick :: rest) crossed suffix) =
      some
        (returnCountStartConfig rest
          (MachineCodeSymbol.tick :: crossed) suffix) := by
  cases rest with
  | nil => contradiction
  | cons next remaining => rfl

theorem returnCountStart_done_step
    (baseLeftRev crossed suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (returnCountStartConfig
          (MachineCodeSymbol.done :: baseLeftRev) crossed suffix) =
      some
        (config .countCheck
          (MachineCodeSymbol.done :: baseLeftRev)
          (List.append crossed (MachineCodeSymbol.blank :: suffix))) := by
  cases crossed <;> cases suffix <;> rfl

theorem returnCountStart_run_exact (count : Nat)
    (baseLeftRev crossed suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (count + 1)
        (returnCountStartConfig
          (List.append (HeadLocator.ticks count)
            (MachineCodeSymbol.done :: baseLeftRev)) crossed suffix) =
      some
        (config .countCheck
          (MachineCodeSymbol.done :: baseLeftRev)
          (List.append (HeadLocator.ticks count)
            (List.append crossed
              (MachineCodeSymbol.blank :: suffix)))) := by
  induction count generalizing crossed with
  | zero =>
      exact returnCountStart_done_step baseLeftRev crossed suffix
  | succ count ih =>
      change
        machine.runConfigExact? ((count + 1) + 1)
          (returnCountStartConfig
            (MachineCodeSymbol.tick ::
              List.append (HeadLocator.ticks count)
                (MachineCodeSymbol.done :: baseLeftRev)) crossed suffix) = _
      rw [TuringMachine.runConfigExact?]
      have hrest :
          List.append (HeadLocator.ticks count)
              (MachineCodeSymbol.done :: baseLeftRev) ≠ [] := by
        intro h
        have := congrArg List.length h
        simp at this
      rw [returnCountStart_tick_step_nonempty _ _ _ hrest]
      simp only
      rw [ih (MachineCodeSymbol.tick :: crossed)]
      have hwords :
          List.append (HeadLocator.ticks count)
              (List.append (MachineCodeSymbol.tick :: crossed)
                (MachineCodeSymbol.blank :: suffix)) =
            List.append (HeadLocator.ticks (count + 1))
              (List.append crossed
                (MachineCodeSymbol.blank :: suffix)) := by
        calc
          List.append (HeadLocator.ticks count)
              (List.append (MachineCodeSymbol.tick :: crossed)
                (MachineCodeSymbol.blank :: suffix)) =
              List.append (HeadLocator.ticks count)
                (MachineCodeSymbol.tick ::
                  List.append crossed
                    (MachineCodeSymbol.blank :: suffix)) := by
                rfl
          _ = MachineCodeSymbol.tick ::
                List.append (HeadLocator.ticks count)
                  (List.append crossed
                    (MachineCodeSymbol.blank :: suffix)) :=
              HeadLocator.ticks_append_tick count
                (List.append crossed
                  (MachineCodeSymbol.blank :: suffix))
          _ = List.append (HeadLocator.ticks (count + 1))
                (List.append crossed
                  (MachineCodeSymbol.blank :: suffix)) := by
              rfl
      rw [hwords]

theorem markCountBoundary_roundTrip_exact (count : Nat)
    (baseLeftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (2 * count + 2)
        (config .markCountBoundary
          (MachineCodeSymbol.done :: baseLeftRev)
          (MachineDescription.encodeNatAppend count suffix)) =
      some
        (config .countCheck
          (MachineCodeSymbol.done :: baseLeftRev)
          (List.append (HeadLocator.ticks count)
            (MachineCodeSymbol.blank :: suffix))) := by
  rw [show 2 * count + 2 = (count + 1) + (count + 1) by lia]
  rw [TuringMachine.runConfigExact?_add]
  rw [markCount_run_exact]
  simp only
  simpa using
    returnCountStart_run_exact count baseLeftRev
      ([] : Word MachineCodeSymbol) suffix

theorem countCheck_tick_step (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .countCheck leftRev
          (MachineCodeSymbol.tick :: suffix)) =
      some
        (config .seekCountBoundary
          (MachineCodeSymbol.transition :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem seekCountBoundary_tick_step
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .seekCountBoundary leftRev
          (MachineCodeSymbol.tick :: suffix)) =
      some
        (config .seekCountBoundary
          (MachineCodeSymbol.tick :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem seekCountBoundary_blank_step
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .seekCountBoundary leftRev
          (MachineCodeSymbol.blank :: suffix)) =
      some
        (config .seekCellDone
          (MachineCodeSymbol.blank :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem seekCountBoundary_run_exact (remainingCount : Nat)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (remainingCount + 1)
        (config .seekCountBoundary leftRev
          (List.append (HeadLocator.ticks remainingCount)
            (MachineCodeSymbol.blank :: suffix))) =
      some
        (config .seekCellDone
          (MachineCodeSymbol.blank ::
            List.append (HeadLocator.ticks remainingCount) leftRev)
          suffix) := by
  induction remainingCount generalizing leftRev with
  | zero =>
      exact seekCountBoundary_blank_step leftRev suffix
  | succ remainingCount ih =>
      change
        machine.runConfigExact? ((remainingCount + 1) + 1)
          (config .seekCountBoundary leftRev
            (MachineCodeSymbol.tick ::
              List.append (HeadLocator.ticks remainingCount)
                (MachineCodeSymbol.blank :: suffix))) = _
      rw [TuringMachine.runConfigExact?]
      rw [seekCountBoundary_tick_step]
      simp only
      rw [ih]
      have hwords :
          List.append (HeadLocator.ticks remainingCount)
              (MachineCodeSymbol.tick :: leftRev) =
            List.append (HeadLocator.ticks (remainingCount + 1))
              leftRev := by
        calc
          List.append (HeadLocator.ticks remainingCount)
              (MachineCodeSymbol.tick :: leftRev) =
              MachineCodeSymbol.tick ::
                List.append (HeadLocator.ticks remainingCount) leftRev :=
            HeadLocator.ticks_append_tick remainingCount leftRev
          _ = List.append (HeadLocator.ticks (remainingCount + 1))
                leftRev := by
            rfl
      exact congrArg
        (fun word => some
          (config .seekCellDone (MachineCodeSymbol.blank :: word) suffix))
        hwords

theorem seekCellDone_tick_step
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .seekCellDone leftRev
          (MachineCodeSymbol.tick :: suffix)) =
      some
        (config .seekCellDone
          (MachineCodeSymbol.tick :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem seekCellDone_header_step
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .seekCellDone leftRev
          (MachineCodeSymbol.header :: suffix)) =
      some
        (config .seekCellDone
          (MachineCodeSymbol.header :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem seekCellDone_ticks_run_exact (count : Nat)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? count
        (config .seekCellDone leftRev
          (List.append (HeadLocator.ticks count) suffix)) =
      some
        (config .seekCellDone
          (List.append (HeadLocator.ticks count) leftRev) suffix) := by
  induction count generalizing leftRev with
  | zero =>
      rfl
  | succ count ih =>
      change
        machine.runConfigExact? (count + 1)
          (config .seekCellDone leftRev
            (MachineCodeSymbol.tick ::
              List.append (HeadLocator.ticks count) suffix)) = _
      rw [TuringMachine.runConfigExact?]
      rw [seekCellDone_tick_step]
      simp only
      rw [ih]
      have hwords :
          List.append (HeadLocator.ticks count)
              (MachineCodeSymbol.tick :: leftRev) =
            List.append (HeadLocator.ticks (count + 1)) leftRev := by
        calc
          List.append (HeadLocator.ticks count)
              (MachineCodeSymbol.tick :: leftRev) =
              MachineCodeSymbol.tick ::
                List.append (HeadLocator.ticks count) leftRev :=
            HeadLocator.ticks_append_tick count leftRev
          _ = List.append (HeadLocator.ticks (count + 1)) leftRev := by
            rfl
      exact congrArg
        (fun word => some (config .seekCellDone word suffix)) hwords

theorem seekCellDone_markedCell_run_exact
    (cell : Option MachineCodeSymbol)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (HeadLocator.markedCellWord cell).length
        (config .seekCellDone leftRev
          (List.append (HeadLocator.markedCellWord cell) suffix)) =
      some
        (config .seekCellDone
          (List.append (HeadLocator.markedCellWord cell).reverse leftRev)
          suffix) := by
  rw [HeadLocator.markedCellWord_length]
  rw [HeadLocator.markedCellWord_eq]
  have hassoc :
      List.append
          (List.append
            (HeadLocator.ticks (optionalCodeSymbolTag cell))
            ([MachineCodeSymbol.header] : Word MachineCodeSymbol)) suffix =
        List.append (HeadLocator.ticks (optionalCodeSymbolTag cell))
          (MachineCodeSymbol.header :: suffix) :=
    List.append_assoc _ _ _
  rw [hassoc]
  rw [TuringMachine.runConfigExact?_add]
  rw [seekCellDone_ticks_run_exact]
  simp only
  change
    machine.runConfigExact? 1
        (config .seekCellDone
          (List.append (HeadLocator.ticks (optionalCodeSymbolTag cell))
            leftRev)
          (MachineCodeSymbol.header :: suffix)) = _
  rw [TuringMachine.runConfigExact?]
  rw [seekCellDone_header_step]
  simp only [TuringMachine.runConfigExact?]
  simp [List.reverse_append, HeadLocator.ticks_reverse]

theorem seekCellDone_markedCells_run_exact
    (cells : List (Option MachineCodeSymbol))
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (HeadLocator.markedCellsWord cells).length
        (config .seekCellDone leftRev
          (List.append (HeadLocator.markedCellsWord cells) suffix)) =
      some
        (config .seekCellDone
          (List.append (HeadLocator.markedCellsWord cells).reverse leftRev)
          suffix) := by
  induction cells generalizing leftRev with
  | nil =>
      rfl
  | cons cell cells ih =>
      rw [HeadLocator.markedCellsWord_cons]
      have hlength :
          (List.append (HeadLocator.markedCellWord cell)
            (HeadLocator.markedCellsWord cells) :
              Word MachineCodeSymbol).length =
            (HeadLocator.markedCellWord cell).length +
              (HeadLocator.markedCellsWord cells).length :=
        List.length_append
      rw [hlength]
      have hassoc :
          List.append
              (List.append (HeadLocator.markedCellWord cell)
                (HeadLocator.markedCellsWord cells)) suffix =
            List.append (HeadLocator.markedCellWord cell)
              (List.append (HeadLocator.markedCellsWord cells) suffix) :=
        List.append_assoc _ _ _
      rw [hassoc]
      rw [TuringMachine.runConfigExact?_add]
      rw [seekCellDone_markedCell_run_exact]
      simp only
      rw [ih]
      simp [List.reverse_append, List.append_assoc]

def returnCountConfig
    (remaining crossed rightAfter : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  match remaining with
  | [] =>
      config .returnCount []
        (List.append crossed (MachineCodeSymbol.header :: rightAfter))
  | current :: rest =>
      { state := .returnCount
        tape :=
          { left := rest.map some
            head := some current
            right :=
              (List.append crossed
                (MachineCodeSymbol.header :: rightAfter)).map some } }

theorem seekCellDone_done_step (leftHead : MachineCodeSymbol)
    (leftTail rightAfter : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .seekCellDone (leftHead :: leftTail)
          (MachineCodeSymbol.done :: rightAfter)) =
      some
        (returnCountConfig (leftHead :: leftTail) [] rightAfter) := by
  rfl

theorem seekCellDone_cell_run_exact
    (cell : Option MachineCodeSymbol)
    (leftHead : MachineCodeSymbol)
    (leftTail rightAfter : Word MachineCodeSymbol) :
    machine.runConfigExact? (optionalCodeSymbolTag cell + 1)
        (config .seekCellDone (leftHead :: leftTail)
          (List.append (optionalCellWord cell) rightAfter)) =
      some
        (returnCountConfig
          (List.append
            (HeadLocator.ticks (optionalCodeSymbolTag cell))
            (leftHead :: leftTail)) [] rightAfter) := by
  rw [HeadLocator.optionalCellWord_eq_ticks_done]
  have hassoc :
      List.append
          (List.append
            (HeadLocator.ticks (optionalCodeSymbolTag cell))
            ([MachineCodeSymbol.done] : Word MachineCodeSymbol))
          rightAfter =
        List.append (HeadLocator.ticks (optionalCodeSymbolTag cell))
          (MachineCodeSymbol.done :: rightAfter) :=
    List.append_assoc _ _ _
  rw [hassoc]
  rw [TuringMachine.runConfigExact?_add]
  rw [seekCellDone_ticks_run_exact]
  simp only
  change
    machine.runConfigExact? 1
        (config .seekCellDone
          (List.append (HeadLocator.ticks (optionalCodeSymbolTag cell))
            (leftHead :: leftTail))
          (MachineCodeSymbol.done :: rightAfter)) = _
  rw [TuringMachine.runConfigExact?]
  have hleft :
      List.append (HeadLocator.ticks (optionalCodeSymbolTag cell))
          (leftHead :: leftTail) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
  cases hshape :
      List.append (HeadLocator.ticks (optionalCodeSymbolTag cell))
        (leftHead :: leftTail) with
  | nil => contradiction
  | cons next rest =>
      rw [seekCellDone_done_step]
      simp only [TuringMachine.runConfigExact?]

theorem returnCount_symbol_step
    (current next : MachineCodeSymbol)
    (remaining crossed rightAfter : Word MachineCodeSymbol)
    (hcurrent : current ≠ MachineCodeSymbol.transition) :
    machine.stepConfig
        (returnCountConfig (current :: next :: remaining)
          crossed rightAfter) =
      some
        (returnCountConfig (next :: remaining)
          (current :: crossed) rightAfter) := by
  cases current <;> simp_all [machine, TuringMachine.stepConfig,
    transition, returnCountConfig, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft]

theorem returnCount_finish
    (baseLeftRev crossed rightAfter : Word MachineCodeSymbol) :
    machine.stepConfig
        (returnCountConfig
          (MachineCodeSymbol.transition :: baseLeftRev)
          crossed rightAfter) =
      some
        (config .countCheck
          (MachineCodeSymbol.transition :: baseLeftRev)
          (List.append crossed
            (MachineCodeSymbol.header :: rightAfter))) := by
  cases crossed <;> cases rightAfter <;> rfl

theorem returnCount_run_exact
    (prefixRev baseLeftRev crossed rightAfter : Word MachineCodeSymbol)
    (hsafe : ¬ List.Mem MachineCodeSymbol.transition prefixRev) :
    machine.runConfigExact? (prefixRev.length + 1)
        (returnCountConfig
          (List.append prefixRev
            (MachineCodeSymbol.transition :: baseLeftRev))
          crossed rightAfter) =
      some
        (config .countCheck
          (MachineCodeSymbol.transition :: baseLeftRev)
          (List.append prefixRev.reverse
            (List.append crossed
              (MachineCodeSymbol.header :: rightAfter)))) := by
  induction prefixRev generalizing crossed with
  | nil =>
      exact returnCount_finish baseLeftRev crossed rightAfter
  | cons current prefixRev ih =>
      have hcurrent : current ≠ MachineCodeSymbol.transition := by
        intro h
        subst current
        exact hsafe (List.Mem.head _)
      have htail : ¬ List.Mem MachineCodeSymbol.transition prefixRev := by
        intro h
        exact hsafe (List.Mem.tail _ h)
      change
        machine.runConfigExact? ((prefixRev.length + 1) + 1)
          (returnCountConfig
            (current ::
              List.append prefixRev
                (MachineCodeSymbol.transition :: baseLeftRev))
            crossed rightAfter) = _
      rw [TuringMachine.runConfigExact?]
      have hrest :
          List.append prefixRev
              (MachineCodeSymbol.transition :: baseLeftRev) ≠ [] := by
        intro h
        have := congrArg List.length h
        simp at this
      cases hrestShape :
          List.append prefixRev
            (MachineCodeSymbol.transition :: baseLeftRev) with
      | nil => contradiction
      | cons next remaining =>
          rw [returnCount_symbol_step current next remaining crossed
            rightAfter hcurrent]
          simp only
          have ih' := ih (current :: crossed) htail
          rw [hrestShape] at ih'
          rw [ih']
          simp [List.reverse_cons, List.append_assoc]

theorem processCell_run_exact
    (remainingCount : Nat)
    (processed : List (Option MachineCodeSymbol))
    (cell : Option MachineCodeSymbol)
    (baseLeftRev rightAfter : Word MachineCodeSymbol) :
    machine.runConfigExact?
        (HeadLocator.processCellSteps remainingCount processed cell)
        (config .countCheck baseLeftRev
          (MachineCodeSymbol.tick ::
            List.append (HeadLocator.ticks remainingCount)
              (MachineCodeSymbol.blank ::
                HeadLocator.cellInputBody processed cell rightAfter))) =
      some
        (config .countCheck
          (MachineCodeSymbol.transition :: baseLeftRev)
          (List.append (HeadLocator.ticks remainingCount)
            (MachineCodeSymbol.blank ::
              HeadLocator.cellOutputBody processed cell rightAfter))) := by
  unfold HeadLocator.processCellSteps
  rw [TuringMachine.runConfigExact?_add]
  have hfirst :
      machine.runConfigExact? 1
          (config .countCheck baseLeftRev
            (MachineCodeSymbol.tick ::
              List.append (HeadLocator.ticks remainingCount)
                (MachineCodeSymbol.blank ::
                  HeadLocator.cellInputBody processed cell rightAfter))) =
        some
          (config .seekCountBoundary
            (MachineCodeSymbol.transition :: baseLeftRev)
            (List.append (HeadLocator.ticks remainingCount)
              (MachineCodeSymbol.blank ::
                HeadLocator.cellInputBody processed cell rightAfter))) := by
    rw [TuringMachine.runConfigExact?]
    rw [countCheck_tick_step]
    simp only [TuringMachine.runConfigExact?]
  rw [hfirst]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  rw [seekCountBoundary_run_exact]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  unfold HeadLocator.cellInputBody
  rw [seekCellDone_markedCells_run_exact]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  have hleft :
      List.append (HeadLocator.markedCellsWord processed).reverse
          (MachineCodeSymbol.blank ::
            List.append (HeadLocator.ticks remainingCount)
              (MachineCodeSymbol.transition :: baseLeftRev)) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
  cases hshape :
      List.append (HeadLocator.markedCellsWord processed).reverse
        (MachineCodeSymbol.blank ::
          List.append (HeadLocator.ticks remainingCount)
            (MachineCodeSymbol.transition :: baseLeftRev)) with
  | nil => contradiction
  | cons leftHead leftTail =>
      rw [seekCellDone_cell_run_exact]
      simp only
      have hremaining :
          (List.append (HeadLocator.ticks (optionalCodeSymbolTag cell))
              (leftHead :: leftTail) : Word MachineCodeSymbol) =
            List.append
              (HeadLocator.cellReturnPrefixRev
                remainingCount processed cell)
              (MachineCodeSymbol.transition :: baseLeftRev) := by
        calc
          List.append (HeadLocator.ticks (optionalCodeSymbolTag cell))
              (leftHead :: leftTail) =
              List.append (HeadLocator.ticks (optionalCodeSymbolTag cell))
                (List.append (HeadLocator.markedCellsWord processed).reverse
                  (MachineCodeSymbol.blank ::
                    List.append (HeadLocator.ticks remainingCount)
                      (MachineCodeSymbol.transition :: baseLeftRev))) :=
            congrArg
              (List.append
                (HeadLocator.ticks (optionalCodeSymbolTag cell)))
              hshape.symm
          _ = List.append
                (HeadLocator.cellReturnPrefixRev
                  remainingCount processed cell)
                (MachineCodeSymbol.transition :: baseLeftRev) := by
            simp [HeadLocator.cellReturnPrefixRev, List.append_assoc]
      rw [hremaining]
      rw [returnCount_run_exact
        (prefixRev := HeadLocator.cellReturnPrefixRev
          remainingCount processed cell)
        (baseLeftRev := baseLeftRev) (crossed := [])
        (rightAfter := rightAfter)
        (HeadLocator.cellReturnPrefixRev_no_transition
          remainingCount processed cell)]
      simp [HeadLocator.cellReturnPrefixRev,
        HeadLocator.cellOutputBody, HeadLocator.markedCellWord,
        List.reverse_append, HeadLocator.ticks_reverse,
        List.append_assoc]

theorem processCells_run_exact
    (remaining processed : List (Option MachineCodeSymbol))
    (baseLeftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact?
        (HeadLocator.processCellsSteps processed remaining)
        (config .countCheck baseLeftRev
          (List.append (HeadLocator.ticks remaining.length)
            (MachineCodeSymbol.blank ::
              List.append (HeadLocator.markedCellsWord processed)
                (HeadLocator.cellsPayloadAppend remaining suffix)))) =
      some
        (config .countCheck
          (List.append
            (HeadLocator.transitionMarkers remaining.length) baseLeftRev)
          (MachineCodeSymbol.blank ::
            List.append
              (HeadLocator.markedCellsWord (processed ++ remaining))
              suffix)) := by
  induction remaining generalizing processed baseLeftRev with
  | nil =>
      simp [HeadLocator.processCellsSteps, HeadLocator.ticks,
        HeadLocator.transitionMarkers, HeadLocator.cellsPayloadAppend,
        TuringMachine.runConfigExact?]
  | cons cell rest ih =>
      unfold HeadLocator.processCellsSteps
      rw [TuringMachine.runConfigExact?_add]
      have hsource :
          List.append (HeadLocator.ticks (cell :: rest).length)
              (MachineCodeSymbol.blank ::
                List.append (HeadLocator.markedCellsWord processed)
                  (HeadLocator.cellsPayloadAppend (cell :: rest) suffix)) =
            MachineCodeSymbol.tick ::
              List.append (HeadLocator.ticks rest.length)
                (MachineCodeSymbol.blank ::
                  HeadLocator.cellInputBody processed cell
                    (HeadLocator.cellsPayloadAppend rest suffix)) := by
        rfl
      rw [hsource]
      rw [processCell_run_exact rest.length processed cell
        baseLeftRev (HeadLocator.cellsPayloadAppend rest suffix)]
      simp only
      have hbody :
          HeadLocator.cellOutputBody processed cell
              (HeadLocator.cellsPayloadAppend rest suffix) =
            List.append
              (HeadLocator.markedCellsWord (processed ++ [cell]))
              (HeadLocator.cellsPayloadAppend rest suffix) := by
        simp [HeadLocator.cellOutputBody,
          HeadLocator.markedCellsWord_append,
          HeadLocator.markedCellsWord, List.append_assoc]
      rw [hbody]
      rw [ih (processed ++ [cell])
        (MachineCodeSymbol.transition :: baseLeftRev)]
      have hleft :
          List.append (HeadLocator.transitionMarkers rest.length)
              (MachineCodeSymbol.transition :: baseLeftRev) =
            List.append
              (HeadLocator.transitionMarkers (cell :: rest).length)
              baseLeftRev := by
        rw [HeadLocator.transitionMarkers_append_transition]
        rfl
      have hprocessed :
          (processed ++ [cell]) ++ rest =
            processed ++ (cell :: rest) := by
        simp [List.append_assoc]
      rw [hleft, hprocessed]

theorem processAllCells_run_exact
    (remaining : List (Option MachineCodeSymbol))
    (baseLeftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (HeadLocator.processCellsSteps [] remaining)
        (config .countCheck baseLeftRev
          (List.append (HeadLocator.ticks remaining.length)
            (MachineCodeSymbol.blank ::
              HeadLocator.cellsPayloadAppend remaining suffix))) =
      some
        (config .countCheck
          (List.append
            (HeadLocator.transitionMarkers remaining.length) baseLeftRev)
          (MachineCodeSymbol.blank ::
            List.append (HeadLocator.markedCellsWord remaining) suffix)) := by
  have h := processCells_run_exact remaining [] baseLeftRev suffix
  have hempty :
      List.append
          (HeadLocator.markedCellsWord
            ([] : List (Option MachineCodeSymbol)))
          (HeadLocator.cellsPayloadAppend remaining suffix) =
        HeadLocator.cellsPayloadAppend remaining suffix := by
    rfl
  rw [hempty] at h
  exact h

theorem countCheck_blank_step
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .countCheck leftRev
          (MachineCodeSymbol.blank :: suffix)) =
      some
        (config .gate (MachineCodeSymbol.blank :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem leftCountPrefix_reverse_eq_countBase {stateCount : Nat}
    (L : Layout stateCount) :
    (LeftPrepend.leftCountPrefix L).reverse =
      HeadLocator.countBaseLeftRev L := by
  simpa [LeftPrepend.leftCountPrefix,
    MachineDescription.encodeNatAppend, List.reverse_cons,
    List.reverse_append] using
      HeadLocator.scannedStateLeft_eq_countBase L

def sourceConfig {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .markCountBoundary
    (LeftPrepend.leftCountPrefix L).reverse
    (afterStateWord L callerData)

def gateConfig {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .gate
    (MachineCodeSymbol.blank ::
      List.append (HeadLocator.transitionMarkers L.left.length)
        (HeadLocator.countBaseLeftRev L))
    (List.append (HeadLocator.markedCellsWord L.left)
      (headSuffix L callerData))

def runSteps {stateCount : Nat} (L : Layout stateCount) : Nat :=
  (2 * L.left.length + 2) +
    (HeadLocator.processCellsSteps [] L.left + 1)

theorem run_exact {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    machine.runConfigExact? (runSteps L) (sourceConfig L callerData) =
      some (gateConfig L callerData) := by
  unfold runSteps sourceConfig gateConfig
  rw [leftCountPrefix_reverse_eq_countBase]
  rw [HeadLocator.afterStateWord_eq_count_payload]
  rw [show HeadLocator.countBaseLeftRev L =
      MachineCodeSymbol.done :: HeadLocator.topFieldsRev L by rfl]
  rw [TuringMachine.runConfigExact?_add]
  rw [markCountBoundary_roundTrip_exact]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  rw [processAllCells_run_exact]
  simp only
  change
    machine.runConfigExact? 1
        (config .countCheck
          (List.append (HeadLocator.transitionMarkers L.left.length)
            (HeadLocator.countBaseLeftRev L))
          (MachineCodeSymbol.blank ::
            List.append (HeadLocator.markedCellsWord L.left)
              (headSuffix L callerData))) = _
  rw [TuringMachine.runConfigExact?]
  rw [countCheck_blank_step]
  rfl

end Counter

namespace HeadDecoder

inductive Control where
  | decode (count : Fin 10)
  | gate (head : Option MachineCodeSymbol)
deriving DecidableEq

namespace Control

def elems : List Control :=
  List.append
    ((List.finRange 10).map Control.decode)
    (HeadLocator.Control.optionalSymbols.map Control.gate)

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | decode count => simp [elems, List.mem_finRange]
    | gate head =>
        have h := HeadLocator.Control.optionalSymbols_complete head
        simp [elems, h]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .decode count, some MachineCodeSymbol.tick =>
      match HeadLocator.incrementHeadCount count with
      | none => none
      | some next =>
          some (some MachineCodeSymbol.tick, Direction.right, .decode next)
  | .decode _, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.right,
        .decode ⟨0, by decide⟩)
  | .decode count, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right,
        .gate (HeadLocator.decodedHead count))
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .decode ⟨0, by decide⟩
  halt := .gate none
  transition := transition
  statesFinite := Control.finite

def config (control : Control)
    (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := control
  tape := SerializedShift.cursorTape leftRev rest

theorem markedCell_run_exact
    (cell : Option MachineCodeSymbol)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (HeadLocator.markedCellWord cell).length
        (config (.decode ⟨0, by decide⟩) leftRev
          (List.append (HeadLocator.markedCellWord cell) suffix)) =
      some
        (config (.decode ⟨0, by decide⟩)
          (List.append (HeadLocator.markedCellWord cell).reverse leftRev)
          suffix) := by
  cases cell with
  | none => cases suffix <;> rfl
  | some symbol => cases symbol <;> cases suffix <;> rfl

theorem markedCells_run_exact
    (cells : List (Option MachineCodeSymbol))
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (HeadLocator.markedCellsWord cells).length
        (config (.decode ⟨0, by decide⟩) leftRev
          (List.append (HeadLocator.markedCellsWord cells) suffix)) =
      some
        (config (.decode ⟨0, by decide⟩)
          (List.append (HeadLocator.markedCellsWord cells).reverse leftRev)
          suffix) := by
  induction cells generalizing leftRev with
  | nil =>
      rfl
  | cons cell cells ih =>
      rw [HeadLocator.markedCellsWord_cons]
      have hlength :
          (List.append (HeadLocator.markedCellWord cell)
            (HeadLocator.markedCellsWord cells) :
              Word MachineCodeSymbol).length =
            (HeadLocator.markedCellWord cell).length +
              (HeadLocator.markedCellsWord cells).length :=
        List.length_append
      rw [hlength]
      have hassoc :
          List.append
              (List.append (HeadLocator.markedCellWord cell)
                (HeadLocator.markedCellsWord cells)) suffix =
            List.append (HeadLocator.markedCellWord cell)
              (List.append (HeadLocator.markedCellsWord cells) suffix) :=
        List.append_assoc _ _ _
      rw [hassoc]
      rw [TuringMachine.runConfigExact?_add]
      rw [markedCell_run_exact]
      simp only
      rw [ih]
      simp [List.reverse_append, List.append_assoc]

theorem head_run_exact
    (head : Option MachineCodeSymbol)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (optionalCodeSymbolTag head + 1)
        (config (.decode ⟨0, by decide⟩) leftRev
          (List.append (optionalCellWord head) suffix)) =
      some
        (config (.gate head)
          (List.append (optionalCellWord head).reverse leftRev)
          suffix) := by
  cases head with
  | none => cases suffix <;> rfl
  | some symbol => cases symbol <;> cases suffix <;> rfl

def runSteps (cells : List (Option MachineCodeSymbol))
    (head : Option MachineCodeSymbol) : Nat :=
  (HeadLocator.markedCellsWord cells).length +
    (optionalCodeSymbolTag head + 1)

theorem run_exact
    (cells : List (Option MachineCodeSymbol))
    (head : Option MachineCodeSymbol)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (runSteps cells head)
        (config (.decode ⟨0, by decide⟩) leftRev
          (List.append (HeadLocator.markedCellsWord cells)
            (List.append (optionalCellWord head) suffix))) =
      some
        (config (.gate head)
          (List.append (optionalCellWord head).reverse
            (List.append (HeadLocator.markedCellsWord cells).reverse
              leftRev))
          suffix) := by
  unfold runSteps
  rw [TuringMachine.runConfigExact?_add]
  rw [markedCells_run_exact]
  simp only
  rw [head_run_exact]

def markedCountBaseLeftRev {stateCount : Nat}
    (L : Layout stateCount) : Word MachineCodeSymbol :=
  MachineCodeSymbol.blank ::
    List.append (HeadLocator.transitionMarkers L.left.length)
      (HeadLocator.countBaseLeftRev L)

def sourceConfig {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config (.decode ⟨0, by decide⟩)
    (markedCountBaseLeftRev L)
    (List.append (HeadLocator.markedCellsWord L.left)
      (headSuffix L callerData))

def rightCountConfig {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config (.gate L.head)
    (List.append (optionalCellWord L.head).reverse
      (List.append (HeadLocator.markedCellsWord L.left).reverse
        (markedCountBaseLeftRev L)))
    (HeadLocator.afterHeadWord L callerData)

theorem locate_rightCount_exact {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    machine.runConfigExact? (runSteps L.left L.head)
        (sourceConfig L callerData) =
      some (rightCountConfig L callerData) := by
  simpa [sourceConfig, rightCountConfig, markedCountBaseLeftRev,
    headSuffix, HeadLocator.afterHeadWord] using
      run_exact L.left L.head (markedCountBaseLeftRev L)
        (HeadLocator.afterHeadWord L callerData)

end HeadDecoder

namespace OuterLocator

/-- One finite locator from the canonical protected frame to the first token
of the right-count field.  The intermediate states retain the temporary
left-field markers used to find this boundary. -/
inductive Control where
  | locate (inner : FieldLocator.Control)
  | locateReturn
  | counter (inner : Counter.Control)
  | counterReturn
  | decode (inner : HeadDecoder.Control)
deriving DecidableEq

namespace Control

def elems : List Control :=
  List.append
    (FieldLocator.Control.elems.map Control.locate)
    (Control.locateReturn ::
      List.append
        (Counter.Control.elems.map Control.counter)
        (Control.counterReturn ::
          HeadDecoder.Control.elems.map Control.decode))

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | locate inner =>
        have h := FieldLocator.Control.finite.complete inner
        change inner ∈ FieldLocator.Control.elems at h
        simp [elems, h]
    | locateReturn => simp [elems]
    | counter inner =>
        have h := Counter.Control.finite.complete inner
        change inner ∈ Counter.Control.elems at h
        simp [elems, h]
    | counterReturn => simp [elems]
    | decode inner =>
        have h := HeadDecoder.Control.finite.complete inner
        change inner ∈ HeadDecoder.Control.elems at h
        simp [elems, h]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .locate inner, read =>
      match FieldLocator.transition .leftCount inner read with
      | some (write, direction, target) =>
          some (write, direction, .locate target)
      | none =>
          if inner = .gate then
            some (read, Direction.left, .locateReturn)
          else
            none
  | .locateReturn, read =>
      some (read, Direction.right, .counter .markCountBoundary)
  | .counter inner, read =>
      match Counter.transition inner read with
      | some (write, direction, target) =>
          some (write, direction, .counter target)
      | none =>
          if inner = .gate then
            some (read, Direction.left, .counterReturn)
          else
            none
  | .counterReturn, read =>
      some (read, Direction.right, .decode (.decode ⟨0, by decide⟩))
  | .decode inner, read =>
      match HeadDecoder.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .decode target)

def machine : TuringMachine MachineCodeSymbol Control where
  start := .locate .header
  halt := .decode (.gate none)
  transition := transition
  statesFinite := Control.finite

def locateConfig
    (c : TuringMachine.Configuration MachineCodeSymbol
      FieldLocator.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig Control.locate c

def counterConfig
    (c : TuringMachine.Configuration MachineCodeSymbol Counter.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig Control.counter c

def decodeConfig
    (c : TuringMachine.Configuration MachineCodeSymbol
      HeadDecoder.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig Control.decode c

theorem locate_step_of_some
    (c d : TuringMachine.Configuration MachineCodeSymbol
      FieldLocator.Control)
    (hstep : (FieldLocator.machine .leftCount).stepConfig c = some d) :
    machine.stepConfig (locateConfig c) = some (locateConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [FieldLocator.machine] at hstep
      cases htransition :
          FieldLocator.transition .leftCount inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          simp [machine, transition, locateConfig,
            TuringMachine.PhaseEmbedding.liftConfig, htransition]

theorem counter_step_of_some
    (c d : TuringMachine.Configuration MachineCodeSymbol Counter.Control)
    (hstep : Counter.machine.stepConfig c = some d) :
    machine.stepConfig (counterConfig c) = some (counterConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Counter.machine] at hstep
      cases htransition : Counter.transition inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          simp [machine, transition, counterConfig,
            TuringMachine.PhaseEmbedding.liftConfig, htransition]

theorem decode_step_of_some
    (c d : TuringMachine.Configuration MachineCodeSymbol
      HeadDecoder.Control)
    (hstep : HeadDecoder.machine.stepConfig c = some d) :
    machine.stepConfig (decodeConfig c) = some (decodeConfig d) := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [HeadDecoder.machine] at hstep
      cases htransition : HeadDecoder.transition inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          cases hstep
          simp [machine, transition, decodeConfig,
            TuringMachine.PhaseEmbedding.liftConfig, htransition]

theorem locate_run_of_some
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FieldLocator.Control}
    (hrun : (FieldLocator.machine .leftCount).runConfigExact?
      steps source = some target) :
    machine.runConfigExact? steps (locateConfig source) =
      some (locateConfig target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      Control.locate
  · intro c d hstep
    simpa [locateConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using
        locate_step_of_some c d hstep
  · simpa [locateConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hrun

theorem counter_run_of_some
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Counter.Control}
    (hrun : Counter.machine.runConfigExact? steps source = some target) :
    machine.runConfigExact? steps (counterConfig source) =
      some (counterConfig target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      Control.counter
  · intro c d hstep
    simpa [counterConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using
        counter_step_of_some c d hstep
  · simpa [counterConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hrun

theorem decode_run_of_some
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      HeadDecoder.Control}
    (hrun : HeadDecoder.machine.runConfigExact? steps source = some target) :
    machine.runConfigExact? steps (decodeConfig source) =
      some (decodeConfig target) := by
  apply
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      Control.decode
  · intro c d hstep
    simpa [decodeConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using
        decode_step_of_some c d hstep
  · simpa [decodeConfig,
      TuringMachine.PhaseEmbedding.liftConfig] using hrun

theorem locate_counter_handoff
    (leftHead : MachineCodeSymbol)
    (leftTail rest : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (locateConfig (FieldLocator.config .gate
          (leftHead :: leftTail) rest)) =
      some
        (counterConfig (Counter.config .markCountBoundary
          (leftHead :: leftTail) rest)) := by
  cases rest <;> rfl

theorem counter_decode_handoff
    (leftHead : MachineCodeSymbol)
    (leftTail rest : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (counterConfig (Counter.config .gate
          (leftHead :: leftTail) rest)) =
      some
        (decodeConfig (HeadDecoder.config (.decode ⟨0, by decide⟩)
          (leftHead :: leftTail) rest)) := by
  cases rest <;> rfl

theorem locate_counter_handoff_layout {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (locateConfig (FieldLocator.config .gate
          (LeftPrepend.leftCountPrefix L).reverse
          (afterStateWord L callerData))) =
      some (counterConfig (Counter.sourceConfig L callerData)) := by
  unfold Counter.sourceConfig
  rw [Counter.leftCountPrefix_reverse_eq_countBase]
  simpa [HeadLocator.countBaseLeftRev] using
    locate_counter_handoff MachineCodeSymbol.done
      (HeadLocator.topFieldsRev L) (afterStateWord L callerData)

theorem counter_decode_handoff_layout {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (counterConfig (Counter.gateConfig L callerData)) =
      some (decodeConfig (HeadDecoder.sourceConfig L callerData)) := by
  exact counter_decode_handoff MachineCodeSymbol.blank
    (List.append (HeadLocator.transitionMarkers L.left.length)
      (HeadLocator.countBaseLeftRev L))
    (List.append (HeadLocator.markedCellsWord L.left)
      (headSuffix L callerData))

def runSteps {stateCount : Nat} (L : Layout stateCount) : Nat :=
  (((FieldLocator.leftCountSteps L + 2) + Counter.runSteps L) + 2) +
    HeadDecoder.runSteps L.left L.head

theorem run_exact {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    machine.runConfigExact? (runSteps L)
        (locateConfig (FieldLocator.startConfig L callerData)) =
      some (decodeConfig (HeadDecoder.rightCountConfig L callerData)) := by
  have hlocate := locate_run_of_some
    (FieldLocator.locate_leftCount_exact L callerData)
  have hhandoffOne := locate_counter_handoff_layout L callerData
  have hcounter := counter_run_of_some (Counter.run_exact L callerData)
  have hhandoffTwo := counter_decode_handoff_layout L callerData
  have hdecode := decode_run_of_some
    (HeadDecoder.locate_rightCount_exact L callerData)
  have hfirst := TuringMachine.runConfigExact?_trans hlocate hhandoffOne
  have hsecond := TuringMachine.runConfigExact?_trans hfirst hcounter
  have hthird := TuringMachine.runConfigExact?_trans hsecond hhandoffTwo
  have hfourth := TuringMachine.runConfigExact?_trans hthird hdecode
  simpa [runSteps, Nat.add_assoc] using hfourth

end OuterLocator

end RightFieldLocator
end Dispatch
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
