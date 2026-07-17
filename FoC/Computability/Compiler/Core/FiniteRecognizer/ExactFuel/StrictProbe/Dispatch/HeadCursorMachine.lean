import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.RightFieldLocator
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Edits.OptionalField

set_option doc.verso true

/-!
# Serialized head-cursor post-pass

Finite restoration and cursor positioning after locating the serialized head
field in an exact-fuel strict-probe frame.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Dispatch
namespace HeadCursor

open SerializedFieldComposer

/- This post-pass starts at `OuterLocator`'s first-right-count checkpoint.
It marks the just-crossed head delimiter, restores the temporary left-cell
markers, returns to the top header without crossing the left edge, and uses
the marker to stop exactly on the first token of the head field. -/
namespace Post

inductive Control where
  | entry (head : Option MachineCodeSymbol)
  | markHeadDelimiter (head : Option MachineCodeSymbol)
  | restoreCells (head : Option MachineCodeSymbol)
  | restoreCount (head : Option MachineCodeSymbol)
  | seekTopHeader (head : Option MachineCodeSymbol)
  | scanMarker (head : Option MachineCodeSymbol)
  | returnToHead (head : Option MachineCodeSymbol)
  | positioned (head : Option MachineCodeSymbol)
deriving DecidableEq

namespace Control

def elems : List Control :=
  HeadLocator.Control.optionalSymbols.map Control.entry ++
    HeadLocator.Control.optionalSymbols.map Control.markHeadDelimiter ++
      HeadLocator.Control.optionalSymbols.map Control.restoreCells ++
        HeadLocator.Control.optionalSymbols.map Control.restoreCount ++
          HeadLocator.Control.optionalSymbols.map Control.seekTopHeader ++
            HeadLocator.Control.optionalSymbols.map Control.scanMarker ++
              HeadLocator.Control.optionalSymbols.map Control.returnToHead ++
                HeadLocator.Control.optionalSymbols.map Control.positioned

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control <;> simp [elems] <;>
      exact HeadLocator.Control.optionalSymbols_complete _

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .entry head, read =>
      some (read, Direction.left, .markHeadDelimiter head)
  | .markHeadDelimiter head, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.zero, Direction.left, .restoreCells head)
  | .restoreCells head, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.done, Direction.left, .restoreCells head)
  | .restoreCells head, some MachineCodeSymbol.blank =>
      some (some MachineCodeSymbol.done, Direction.left, .restoreCount head)
  | .restoreCells head, some symbol =>
      some (some symbol, Direction.left, .restoreCells head)
  | .restoreCount head, some MachineCodeSymbol.transition =>
      some (some MachineCodeSymbol.tick, Direction.left, .restoreCount head)
  | .restoreCount head, some symbol =>
      some (some symbol, Direction.left, .seekTopHeader head)
  | .seekTopHeader head, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.right, .scanMarker head)
  | .seekTopHeader head, some symbol =>
      some (some symbol, Direction.left, .seekTopHeader head)
  | .scanMarker head, some MachineCodeSymbol.zero =>
      some (some MachineCodeSymbol.done, Direction.left, .returnToHead head)
  | .scanMarker head, some symbol =>
      some (some symbol, Direction.right, .scanMarker head)
  | .returnToHead head, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.left, .returnToHead head)
  | .returnToHead head, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .positioned head)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .entry none
  halt := .positioned none
  transition := transition
  statesFinite := Control.finite

def cursorConfig (control : Control)
    (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := control
  tape := SerializedShift.cursorTape leftRev rest

def leftScanConfig (control : Control)
    (remaining rightWord : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  match remaining with
  | [] =>
      { state := control
        tape := { left := [], head := none, right := rightWord.map some } }
  | current :: rest =>
      { state := control
        tape :=
          { left := rest.map some
            head := some current
            right := rightWord.map some } }

theorem restoreCells_tick_step
    (head : Option MachineCodeSymbol)
    (next : MachineCodeSymbol)
    (remaining rightWord : Word MachineCodeSymbol) :
    machine.stepConfig
        (leftScanConfig (.restoreCells head)
          (MachineCodeSymbol.tick :: next :: remaining) rightWord) =
      some
        (leftScanConfig (.restoreCells head)
          (next :: remaining) (MachineCodeSymbol.tick :: rightWord)) := by
  rfl

theorem restoreCells_header_step
    (head : Option MachineCodeSymbol)
    (next : MachineCodeSymbol)
    (remaining rightWord : Word MachineCodeSymbol) :
    machine.stepConfig
        (leftScanConfig (.restoreCells head)
          (MachineCodeSymbol.header :: next :: remaining) rightWord) =
      some
        (leftScanConfig (.restoreCells head)
          (next :: remaining) (MachineCodeSymbol.done :: rightWord)) := by
  rfl

theorem restoreCells_blank_step
    (head : Option MachineCodeSymbol)
    (next : MachineCodeSymbol)
    (remaining rightWord : Word MachineCodeSymbol) :
    machine.stepConfig
        (leftScanConfig (.restoreCells head)
          (MachineCodeSymbol.blank :: next :: remaining) rightWord) =
      some
        (leftScanConfig (.restoreCount head)
          (next :: remaining) (MachineCodeSymbol.done :: rightWord)) := by
  rfl

theorem restoreCells_ticks_run_exact
    (count : Nat) (head : Option MachineCodeSymbol)
    (next : MachineCodeSymbol)
    (remaining rightWord : Word MachineCodeSymbol) :
    machine.runConfigExact? count
        (leftScanConfig (.restoreCells head)
          (List.append (HeadLocator.ticks count) (next :: remaining))
          rightWord) =
      some
        (leftScanConfig (.restoreCells head)
          (next :: remaining)
          (List.append (HeadLocator.ticks count) rightWord)) := by
  induction count generalizing rightWord with
  | zero => rfl
  | succ count ih =>
      change
        machine.runConfigExact? (count + 1)
          (leftScanConfig (.restoreCells head)
            (MachineCodeSymbol.tick ::
              List.append (HeadLocator.ticks count) (next :: remaining))
            rightWord) = _
      rw [TuringMachine.runConfigExact?]
      have hrest :
          List.append (HeadLocator.ticks count) (next :: remaining) ≠ [] := by
        intro h
        have := congrArg List.length h
        simp at this
      cases hshape :
          List.append (HeadLocator.ticks count) (next :: remaining) with
      | nil => contradiction
      | cons actualNext actualRemaining =>
          rw [restoreCells_tick_step]
          simp only
          have ih' := ih (MachineCodeSymbol.tick :: rightWord)
          rw [hshape] at ih'
          rw [ih']
          have hwords :
              List.append (HeadLocator.ticks count)
                  (MachineCodeSymbol.tick :: rightWord) =
                List.append (HeadLocator.ticks (count + 1)) rightWord := by
            calc
              List.append (HeadLocator.ticks count)
                  (MachineCodeSymbol.tick :: rightWord) =
                  MachineCodeSymbol.tick ::
                    List.append (HeadLocator.ticks count) rightWord :=
                HeadLocator.ticks_append_tick count rightWord
              _ = List.append (HeadLocator.ticks (count + 1)) rightWord := by
                rfl
          rw [hwords]

theorem restoreCells_ticks_run_exact_nonempty
    (count : Nat) (head : Option MachineCodeSymbol)
    (tail rightWord : Word MachineCodeSymbol)
    (htail : tail ≠ []) :
    machine.runConfigExact? count
        (leftScanConfig (.restoreCells head)
          (List.append (HeadLocator.ticks count) tail) rightWord) =
      some
        (leftScanConfig (.restoreCells head) tail
          (List.append (HeadLocator.ticks count) rightWord)) := by
  cases tail with
  | nil => contradiction
  | cons next remaining =>
      exact restoreCells_ticks_run_exact count head next remaining rightWord

theorem restoreCells_markedCell_run_exact
    (cell : Option MachineCodeSymbol)
    (head : Option MachineCodeSymbol)
    (next : MachineCodeSymbol)
    (remaining rightWord : Word MachineCodeSymbol) :
    machine.runConfigExact? (HeadLocator.markedCellWord cell).length
        (leftScanConfig (.restoreCells head)
          (List.append (HeadLocator.markedCellWord cell).reverse
            (next :: remaining)) rightWord) =
      some
        (leftScanConfig (.restoreCells head)
          (next :: remaining)
          (List.append (optionalCellWord cell) rightWord)) := by
  have hreverse :
      (HeadLocator.markedCellWord cell).reverse =
        MachineCodeSymbol.header ::
          HeadLocator.ticks (optionalCodeSymbolTag cell) := by
    simp [HeadLocator.markedCellWord, List.reverse_append,
      HeadLocator.ticks_reverse]
  rw [HeadLocator.markedCellWord_length, hreverse]
  change
    machine.runConfigExact? (optionalCodeSymbolTag cell + 1)
        (leftScanConfig (.restoreCells head)
          (MachineCodeSymbol.header ::
            List.append (HeadLocator.ticks (optionalCodeSymbolTag cell))
              (next :: remaining)) rightWord) = _
  rw [show optionalCodeSymbolTag cell + 1 =
      1 + optionalCodeSymbolTag cell by lia]
  rw [TuringMachine.runConfigExact?_add, TuringMachine.runConfigExact?]
  simp only [TuringMachine.runConfigExact?]
  have hrest :
      List.append (HeadLocator.ticks (optionalCodeSymbolTag cell))
          (next :: remaining) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
  cases hshape :
      List.append (HeadLocator.ticks (optionalCodeSymbolTag cell))
        (next :: remaining) with
  | nil => contradiction
  | cons actualNext actualRemaining =>
      rw [restoreCells_header_step]
      simp only
      have hticks := restoreCells_ticks_run_exact
        (optionalCodeSymbolTag cell) head next remaining
        (MachineCodeSymbol.done :: rightWord)
      rw [hshape] at hticks
      rw [hticks, HeadLocator.optionalCellWord_eq_ticks_done]
      simp [List.append_assoc]

theorem restoreCells_markedCells_run_exact
    (cells : List (Option MachineCodeSymbol))
    (head : Option MachineCodeSymbol)
    (next : MachineCodeSymbol)
    (remaining rightWord : Word MachineCodeSymbol) :
    machine.runConfigExact? (HeadLocator.markedCellsWord cells).length
        (leftScanConfig (.restoreCells head)
          (List.append (HeadLocator.markedCellsWord cells).reverse
            (next :: remaining)) rightWord) =
      some
        (leftScanConfig (.restoreCells head)
          (next :: remaining)
          (List.append (HeadLocator.cellsPayloadWord cells) rightWord)) := by
  induction cells generalizing next remaining rightWord with
  | nil => rfl
  | cons cell cells ih =>
      have hreverseCell :
          (HeadLocator.markedCellWord cell).reverse =
            MachineCodeSymbol.header ::
              HeadLocator.ticks (optionalCodeSymbolTag cell) := by
        simp [HeadLocator.markedCellWord, List.reverse_append,
          HeadLocator.ticks_reverse]
      rw [HeadLocator.markedCellsWord_cons]
      have hlength :
          (List.append (HeadLocator.markedCellWord cell)
              (HeadLocator.markedCellsWord cells) : Word MachineCodeSymbol).length =
            (HeadLocator.markedCellsWord cells).length +
              (HeadLocator.markedCellWord cell).length := by
        simp
        lia
      rw [hlength, TuringMachine.runConfigExact?_add]
      have hreverseAppend :
          (List.append (HeadLocator.markedCellWord cell)
              (HeadLocator.markedCellsWord cells) : Word MachineCodeSymbol).reverse =
            List.append (HeadLocator.markedCellsWord cells).reverse
              (HeadLocator.markedCellWord cell).reverse :=
        List.reverse_append
      have hsource :
          List.append
              (List.append (HeadLocator.markedCellWord cell)
                (HeadLocator.markedCellsWord cells)).reverse
              (next :: remaining) =
            List.append (HeadLocator.markedCellsWord cells).reverse
              (MachineCodeSymbol.header ::
                List.append (HeadLocator.ticks (optionalCodeSymbolTag cell))
                  (next :: remaining)) := by
        rw [hreverseAppend, hreverseCell]
        exact List.append_assoc _ _ _
      rw [hsource]
      rw [ih
        (next := MachineCodeSymbol.header)
        (remaining := List.append
          (HeadLocator.ticks (optionalCodeSymbolTag cell))
          (next :: remaining))
        (rightWord := rightWord)]
      simp only
      have hcellSource :
          (MachineCodeSymbol.header ::
              List.append (HeadLocator.ticks (optionalCodeSymbolTag cell))
                (next :: remaining) : Word MachineCodeSymbol) =
            List.append (HeadLocator.markedCellWord cell).reverse
              (next :: remaining) := by
        rw [hreverseCell]
        rfl
      rw [hcellSource]
      rw [restoreCells_markedCell_run_exact cell head next remaining
        (List.append (HeadLocator.cellsPayloadWord cells) rightWord)]
      simp [HeadLocator.cellsPayloadWord, List.append_assoc]

def restoreHeadAndCellsSteps
    (head : Option MachineCodeSymbol)
    (cells : List (Option MachineCodeSymbol)) : Nat :=
  optionalCodeSymbolTag head +
    (HeadLocator.markedCellsWord cells).length + 1

theorem restoreHeadAndCells_marker_run_exact
    (head : Option MachineCodeSymbol)
    (cells : List (Option MachineCodeSymbol))
    (tail rightAfter : Word MachineCodeSymbol)
    (htail : tail ≠ []) :
    machine.runConfigExact? (restoreHeadAndCellsSteps head cells)
        (leftScanConfig (.restoreCells head)
          (List.append (HeadLocator.ticks (optionalCodeSymbolTag head))
            (List.append (HeadLocator.markedCellsWord cells).reverse
              (MachineCodeSymbol.blank :: tail)))
          (MachineCodeSymbol.zero :: rightAfter)) =
      some
        (leftScanConfig (.restoreCount head) tail
          (MachineCodeSymbol.done ::
            List.append (HeadLocator.cellsPayloadWord cells)
              (List.append (HeadLocator.ticks (optionalCodeSymbolTag head))
                (MachineCodeSymbol.zero :: rightAfter)))) := by
  cases tail with
  | nil => contradiction
  | cons next remaining =>
      unfold restoreHeadAndCellsSteps
      rw [show
        optionalCodeSymbolTag head +
              (HeadLocator.markedCellsWord cells).length + 1 =
            optionalCodeSymbolTag head +
              ((HeadLocator.markedCellsWord cells).length + 1) by lia]
      rw [TuringMachine.runConfigExact?_add]
      rw [restoreCells_ticks_run_exact_nonempty
        (optionalCodeSymbolTag head) head
        (List.append (HeadLocator.markedCellsWord cells).reverse
          (MachineCodeSymbol.blank :: next :: remaining))
        (MachineCodeSymbol.zero :: rightAfter) (by
          intro h
          have := congrArg List.length h
          simp at this)]
      simp only
      rw [TuringMachine.runConfigExact?_add]
      rw [restoreCells_markedCells_run_exact cells head
        MachineCodeSymbol.blank (next :: remaining)]
      simp only
      change
        machine.runConfigExact? 1
            (leftScanConfig (.restoreCells head)
              (MachineCodeSymbol.blank :: next :: remaining)
              (List.append (HeadLocator.cellsPayloadWord cells)
                (List.append (HeadLocator.ticks
                  (optionalCodeSymbolTag head))
                  (MachineCodeSymbol.zero :: rightAfter)))) = _
      rw [TuringMachine.runConfigExact?, restoreCells_blank_step]
      rfl

theorem restoreCount_transition_step
    (head : Option MachineCodeSymbol)
    (next : MachineCodeSymbol)
    (remaining rightWord : Word MachineCodeSymbol) :
    machine.stepConfig
        (leftScanConfig (.restoreCount head)
          (MachineCodeSymbol.transition :: next :: remaining) rightWord) =
      some
        (leftScanConfig (.restoreCount head)
          (next :: remaining) (MachineCodeSymbol.tick :: rightWord)) := by
  rfl

theorem restoreCount_done_step
    (head : Option MachineCodeSymbol)
    (remaining rightWord : Word MachineCodeSymbol) :
    machine.stepConfig
        (leftScanConfig (.restoreCount head)
          (MachineCodeSymbol.done :: remaining) rightWord) =
      some
        (leftScanConfig (.seekTopHeader head)
          remaining (MachineCodeSymbol.done :: rightWord)) := by
  cases remaining <;> rfl

theorem restoreCount_markers_run_exact
    (count : Nat) (head : Option MachineCodeSymbol)
    (remaining rightWord : Word MachineCodeSymbol) :
    machine.runConfigExact? count
        (leftScanConfig (.restoreCount head)
          (List.append (HeadLocator.transitionMarkers count)
            (MachineCodeSymbol.done :: remaining)) rightWord) =
      some
        (leftScanConfig (.restoreCount head)
          (MachineCodeSymbol.done :: remaining)
          (List.append (HeadLocator.ticks count) rightWord)) := by
  induction count generalizing rightWord with
  | zero => rfl
  | succ count ih =>
      change
        machine.runConfigExact? (count + 1)
          (leftScanConfig (.restoreCount head)
            (MachineCodeSymbol.transition ::
              List.append (HeadLocator.transitionMarkers count)
                (MachineCodeSymbol.done :: remaining)) rightWord) = _
      rw [TuringMachine.runConfigExact?]
      have hrest :
          List.append (HeadLocator.transitionMarkers count)
              (MachineCodeSymbol.done :: remaining) ≠ [] := by
        intro h
        have := congrArg List.length h
        simp at this
      cases hshape :
          List.append (HeadLocator.transitionMarkers count)
            (MachineCodeSymbol.done :: remaining) with
      | nil => contradiction
      | cons next rest =>
          rw [restoreCount_transition_step]
          simp only
          have ih' := ih (MachineCodeSymbol.tick :: rightWord)
          rw [hshape] at ih'
          rw [ih']
          have hwords :
              List.append (HeadLocator.ticks count)
                  (MachineCodeSymbol.tick :: rightWord) =
                List.append (HeadLocator.ticks (count + 1)) rightWord := by
            calc
              List.append (HeadLocator.ticks count)
                  (MachineCodeSymbol.tick :: rightWord) =
                  MachineCodeSymbol.tick ::
                    List.append (HeadLocator.ticks count) rightWord :=
                HeadLocator.ticks_append_tick count rightWord
              _ = List.append (HeadLocator.ticks (count + 1)) rightWord := by
                rfl
          rw [hwords]

theorem restoreCount_run_exact
    (count : Nat) (head : Option MachineCodeSymbol)
    (remaining rightWord : Word MachineCodeSymbol) :
    machine.runConfigExact? (count + 1)
        (leftScanConfig (.restoreCount head)
          (List.append (HeadLocator.transitionMarkers count)
            (MachineCodeSymbol.done :: remaining)) rightWord) =
      some
        (leftScanConfig (.seekTopHeader head) remaining
          (MachineCodeSymbol.done ::
            List.append (HeadLocator.ticks count) rightWord)) := by
  rw [TuringMachine.runConfigExact?_add, restoreCount_markers_run_exact]
  simp only
  change
    machine.runConfigExact? 1
        (leftScanConfig (.restoreCount head)
          (MachineCodeSymbol.done :: remaining)
          (List.append (HeadLocator.ticks count) rightWord)) = _
  rw [TuringMachine.runConfigExact?, restoreCount_done_step]
  rfl

theorem seekTopHeader_tick_step
    (head : Option MachineCodeSymbol)
    (next : MachineCodeSymbol)
    (remaining rightWord : Word MachineCodeSymbol) :
    machine.stepConfig
        (leftScanConfig (.seekTopHeader head)
          (MachineCodeSymbol.tick :: next :: remaining) rightWord) =
      some
        (leftScanConfig (.seekTopHeader head)
          (next :: remaining) (MachineCodeSymbol.tick :: rightWord)) := by
  rfl

theorem seekTopHeader_done_step
    (head : Option MachineCodeSymbol)
    (next : MachineCodeSymbol)
    (remaining rightWord : Word MachineCodeSymbol) :
    machine.stepConfig
        (leftScanConfig (.seekTopHeader head)
          (MachineCodeSymbol.done :: next :: remaining) rightWord) =
      some
        (leftScanConfig (.seekTopHeader head)
          (next :: remaining) (MachineCodeSymbol.done :: rightWord)) := by
  rfl

theorem seekTopHeader_header_right_step
    (head : Option MachineCodeSymbol)
    (rightWord : Word MachineCodeSymbol) :
    machine.stepConfig
        (leftScanConfig (.seekTopHeader head)
          [MachineCodeSymbol.header] rightWord) =
      some
        (cursorConfig (.scanMarker head)
          [MachineCodeSymbol.header] rightWord) := by
  cases rightWord <;> rfl

theorem seekTopHeader_ticks_run_exact
    (count : Nat) (head : Option MachineCodeSymbol)
    (next : MachineCodeSymbol)
    (remaining rightWord : Word MachineCodeSymbol) :
    machine.runConfigExact? count
        (leftScanConfig (.seekTopHeader head)
          (List.append (HeadLocator.ticks count) (next :: remaining))
          rightWord) =
      some
        (leftScanConfig (.seekTopHeader head)
          (next :: remaining)
          (List.append (HeadLocator.ticks count) rightWord)) := by
  induction count generalizing rightWord with
  | zero => rfl
  | succ count ih =>
      change
        machine.runConfigExact? (count + 1)
          (leftScanConfig (.seekTopHeader head)
            (MachineCodeSymbol.tick ::
              List.append (HeadLocator.ticks count) (next :: remaining))
            rightWord) = _
      rw [TuringMachine.runConfigExact?]
      have hrest :
          List.append (HeadLocator.ticks count) (next :: remaining) ≠ [] := by
        intro h
        have := congrArg List.length h
        simp at this
      cases hshape :
          List.append (HeadLocator.ticks count) (next :: remaining) with
      | nil => contradiction
      | cons actualNext actualRemaining =>
          rw [seekTopHeader_tick_step]
          simp only
          have ih' := ih (MachineCodeSymbol.tick :: rightWord)
          rw [hshape] at ih'
          rw [ih']
          have hwords :
              List.append (HeadLocator.ticks count)
                  (MachineCodeSymbol.tick :: rightWord) =
                List.append (HeadLocator.ticks (count + 1)) rightWord := by
            calc
              List.append (HeadLocator.ticks count)
                  (MachineCodeSymbol.tick :: rightWord) =
                  MachineCodeSymbol.tick ::
                    List.append (HeadLocator.ticks count) rightWord :=
                HeadLocator.ticks_append_tick count rightWord
              _ = List.append (HeadLocator.ticks (count + 1)) rightWord := by
                rfl
          rw [hwords]

def beforeHeadMarker {stateCount : Nat}
    (L : Layout stateCount) : Word MachineCodeSymbol :=
  List.append
    (Edits.OptionalField.LayoutSpecialization.middle L)
    (MachineCodeSymbol.done ::
      HeadLocator.ticks (optionalCodeSymbolTag L.head))

theorem beforeHeadMarker_eq_explicit {stateCount : Nat}
    (L : Layout stateCount) :
    beforeHeadMarker L =
      List.append (HeadLocator.ticks L.fuel)
        (MachineCodeSymbol.done ::
          List.append (HeadLocator.ticks L.state.val)
            (MachineCodeSymbol.done ::
              List.append (HeadLocator.ticks L.left.length)
                (MachineCodeSymbol.done ::
                  List.append (HeadLocator.cellsPayloadWord L.left)
                    (HeadLocator.ticks
                      (optionalCodeSymbolTag L.head))))) := by
  have hcount :
      MachineDescription.encodeNat L.left.length =
        Word.Concat (HeadLocator.ticks L.left.length)
          [MachineCodeSymbol.done] :=
    HeadLocator.encodeNat_eq_ticks_done L.left.length
  have hleft :
      Word.Concat
          (Edits.OptionalField.LayoutSpecialization.optionalCellsMiddle
            L.left)
          [MachineCodeSymbol.done] =
        Word.Concat (HeadLocator.ticks L.left.length)
          (Word.Concat [MachineCodeSymbol.done]
            (HeadLocator.cellsPayloadWord L.left)) := by
    calc
      _ = optionalCellsWord L.left :=
        (Edits.OptionalField.LayoutSpecialization.optionalCellsWord_decomp
          L.left).symm
      _ = Word.Concat (MachineDescription.encodeNat L.left.length)
            (HeadLocator.cellsPayloadWord L.left) :=
        Edits.OptionalField.LayoutSpecialization.optionalCellsWord_eq_count_payload
          L.left
      _ = Word.Concat
            (Word.Concat (HeadLocator.ticks L.left.length)
              [MachineCodeSymbol.done])
            (HeadLocator.cellsPayloadWord L.left) := by
        exact congrArg
          (fun word : Word MachineCodeSymbol =>
            Word.Concat word (HeadLocator.cellsPayloadWord L.left)) hcount
      _ = _ := Word.concat_assoc _ _ _
  have hsegment :
      Word.Concat
          (Edits.OptionalField.LayoutSpecialization.optionalCellsMiddle
            L.left)
          (Word.Concat [MachineCodeSymbol.done]
            (HeadLocator.ticks (optionalCodeSymbolTag L.head))) =
        Word.Concat (HeadLocator.ticks L.left.length)
          (Word.Concat [MachineCodeSymbol.done]
            (Word.Concat (HeadLocator.cellsPayloadWord L.left)
              (HeadLocator.ticks (optionalCodeSymbolTag L.head)))) := by
    calc
      Word.Concat
          (Edits.OptionalField.LayoutSpecialization.optionalCellsMiddle
            L.left)
          (Word.Concat [MachineCodeSymbol.done]
            (HeadLocator.ticks (optionalCodeSymbolTag L.head))) =
          Word.Concat
            (Word.Concat
              (Edits.OptionalField.LayoutSpecialization.optionalCellsMiddle
                L.left)
              [MachineCodeSymbol.done])
            (HeadLocator.ticks (optionalCodeSymbolTag L.head)) := by
              exact (Word.concat_assoc _ _ _).symm
      _ = Word.Concat
            (Word.Concat (HeadLocator.ticks L.left.length)
              (Word.Concat [MachineCodeSymbol.done]
                (HeadLocator.cellsPayloadWord L.left)))
            (HeadLocator.ticks (optionalCodeSymbolTag L.head)) := by
              rw [hleft]
      _ = Word.Concat (HeadLocator.ticks L.left.length)
            (Word.Concat
              (Word.Concat [MachineCodeSymbol.done]
                (HeadLocator.cellsPayloadWord L.left))
              (HeadLocator.ticks (optionalCodeSymbolTag L.head))) :=
            Word.concat_assoc _ _ _
      _ = _ := by rw [Word.concat_assoc]
  have hfuel :
      MachineDescription.encodeNat L.fuel =
        Word.Concat (HeadLocator.ticks L.fuel)
          [MachineCodeSymbol.done] :=
    HeadLocator.encodeNat_eq_ticks_done L.fuel
  have hstate :
      MachineDescription.encodeNat L.state.val =
        Word.Concat (HeadLocator.ticks L.state.val)
          [MachineCodeSymbol.done] :=
    HeadLocator.encodeNat_eq_ticks_done L.state.val
  unfold beforeHeadMarker
    Edits.OptionalField.LayoutSpecialization.middle
  change
    Word.Concat
        (Word.Concat (MachineDescription.encodeNat L.fuel)
          (Word.Concat (MachineDescription.encodeNat L.state.val)
            (Edits.OptionalField.LayoutSpecialization.optionalCellsMiddle
              L.left)))
        (Word.Concat [MachineCodeSymbol.done]
          (HeadLocator.ticks (optionalCodeSymbolTag L.head))) = _
  calc
    _ = Word.Concat (MachineDescription.encodeNat L.fuel)
          (Word.Concat (MachineDescription.encodeNat L.state.val)
            (Word.Concat
              (Edits.OptionalField.LayoutSpecialization.optionalCellsMiddle
                L.left)
              (Word.Concat [MachineCodeSymbol.done]
                (HeadLocator.ticks (optionalCodeSymbolTag L.head))))) := by
            rw [Word.concat_assoc, Word.concat_assoc]
    _ = Word.Concat (MachineDescription.encodeNat L.fuel)
          (Word.Concat (MachineDescription.encodeNat L.state.val)
            (Word.Concat (HeadLocator.ticks L.left.length)
              (Word.Concat [MachineCodeSymbol.done]
                (Word.Concat (HeadLocator.cellsPayloadWord L.left)
                  (HeadLocator.ticks (optionalCodeSymbolTag L.head)))))) := by
            rw [hsegment]
    _ = _ := by
      rw [hfuel, hstate]
      rw [Word.concat_assoc, Word.concat_assoc]
      rfl

theorem seekTopHeader_fields_to_scan_general
    (state fuel : Nat) (head : Option MachineCodeSymbol)
    (rightWord : Word MachineCodeSymbol) :
    machine.runConfigExact? (state + 1 + fuel + 1)
        (leftScanConfig (.seekTopHeader head)
          (List.append (HeadLocator.ticks state)
            (MachineCodeSymbol.done ::
              List.append (HeadLocator.ticks fuel)
                [MachineCodeSymbol.header]))
          rightWord) =
      some
        (cursorConfig (.scanMarker head) [MachineCodeSymbol.header]
          (List.append (HeadLocator.ticks fuel)
            (MachineCodeSymbol.done ::
              List.append (HeadLocator.ticks state) rightWord))) := by
  rw [show state + 1 + fuel + 1 =
      state + (1 + (fuel + 1)) by lia]
  rw [TuringMachine.runConfigExact?_add, seekTopHeader_ticks_run_exact]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  have hdone :
      machine.runConfigExact? 1
          (leftScanConfig (.seekTopHeader head)
            (MachineCodeSymbol.done ::
              List.append (HeadLocator.ticks fuel)
                [MachineCodeSymbol.header])
            (List.append (HeadLocator.ticks state) rightWord)) =
        some
          (leftScanConfig (.seekTopHeader head)
            (List.append (HeadLocator.ticks fuel)
              [MachineCodeSymbol.header])
            (MachineCodeSymbol.done ::
              List.append (HeadLocator.ticks state) rightWord)) := by
    rw [TuringMachine.runConfigExact?]
    have hrest :
        List.append (HeadLocator.ticks fuel)
            [MachineCodeSymbol.header] ≠ [] := by
      intro h
      have := congrArg List.length h
      simp at this
    cases hshape :
        List.append (HeadLocator.ticks fuel)
          [MachineCodeSymbol.header] with
    | nil => contradiction
    | cons next remaining =>
        rw [seekTopHeader_done_step]
        rfl
  rw [hdone]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  rw [seekTopHeader_ticks_run_exact fuel head
    MachineCodeSymbol.header []]
  simp only
  change
    machine.runConfigExact? 1
        (leftScanConfig (.seekTopHeader head)
          [MachineCodeSymbol.header]
          (List.append (HeadLocator.ticks fuel)
            (MachineCodeSymbol.done ::
              List.append (HeadLocator.ticks state) rightWord))) = _
  rw [TuringMachine.runConfigExact?]
  rw [seekTopHeader_header_right_step]
  rfl

theorem seekTopHeader_fields_to_scan_exact {stateCount : Nat}
    (L : Layout stateCount) (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (L.state.val + 1 + L.fuel + 1)
        (leftScanConfig (.seekTopHeader L.head)
          (HeadLocator.topFieldsRev L)
          (MachineCodeSymbol.done ::
            List.append (HeadLocator.ticks L.left.length)
              (MachineCodeSymbol.done ::
                List.append (HeadLocator.cellsPayloadWord L.left)
                  (List.append
                    (HeadLocator.ticks (optionalCodeSymbolTag L.head))
                    (MachineCodeSymbol.zero :: suffix))))) =
      some
        (cursorConfig (.scanMarker L.head) [MachineCodeSymbol.header]
          (List.append (beforeHeadMarker L)
            (MachineCodeSymbol.zero :: suffix))) := by
  rw [beforeHeadMarker_eq_explicit]
  simpa [HeadLocator.topFieldsRev, List.append_assoc] using
      seekTopHeader_fields_to_scan_general L.state.val L.fuel L.head
        (MachineCodeSymbol.done ::
          List.append (HeadLocator.ticks L.left.length)
            (MachineCodeSymbol.done ::
              List.append (HeadLocator.cellsPayloadWord L.left)
                (List.append
                  (HeadLocator.ticks (optionalCodeSymbolTag L.head))
                  (MachineCodeSymbol.zero :: suffix))))

abbrev SafePrefix :=
  Edits.OptionalField.MarkerSeek.SafePrefix

theorem ticks_safe (count : Nat) :
    SafePrefix (HeadLocator.ticks count) :=
  Edits.OptionalField.LayoutSpecialization.ticks_safe count

theorem safe_cons_done {word : Word MachineCodeSymbol}
    (hword : SafePrefix word) :
    SafePrefix (MachineCodeSymbol.done :: word) := by
  intro symbol hmem
  cases hmem with
  | head => decide
  | tail _ htail => exact hword symbol htail

theorem safe_append {first second : Word MachineCodeSymbol}
    (hfirst : SafePrefix first) (hsecond : SafePrefix second) :
    SafePrefix (List.append first second) :=
  Edits.OptionalField.LayoutSpecialization.safe_append
    first second hfirst hsecond

theorem beforeHeadMarker_safe {stateCount : Nat}
    (L : Layout stateCount) : SafePrefix (beforeHeadMarker L) := by
  unfold beforeHeadMarker
  exact safe_append
    (Edits.OptionalField.LayoutSpecialization.middle_safe L)
    (safe_cons_done (ticks_safe _))

def scanConfig (head : Option MachineCodeSymbol)
    (leftRev middle suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  cursorConfig (.scanMarker head) leftRev
    (List.append middle (MachineCodeSymbol.zero :: suffix))

def returnConfig (head : Option MachineCodeSymbol)
    (remaining rightWord : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  leftScanConfig (.returnToHead head) remaining rightWord

theorem scan_run_exact
    (head : Option MachineCodeSymbol)
    (leftRev middle suffix : Word MachineCodeSymbol)
    (hsafe : SafePrefix middle) :
    machine.runConfigExact? (middle.length + 1)
        (scanConfig head leftRev middle suffix) =
      some
        (returnConfig head
          (List.append middle.reverse leftRev)
          (MachineCodeSymbol.done :: suffix)) := by
  induction middle generalizing leftRev with
  | nil =>
      cases leftRev <;> cases suffix <;> rfl
  | cons current rest ih =>
      have hcurrent : current ≠ MachineCodeSymbol.zero :=
        hsafe current (List.Mem.head rest)
      have hrest : SafePrefix rest := by
        intro symbol hmem
        exact hsafe symbol (List.Mem.tail current hmem)
      change
        machine.runConfigExact? (rest.length + 1 + 1)
          (scanConfig head leftRev (current :: rest) suffix) = _
      rw [TuringMachine.runConfigExact?]
      have hstep :
          machine.stepConfig
              (scanConfig head leftRev (current :: rest) suffix) =
            some (scanConfig head (current :: leftRev) rest suffix) := by
        cases current <;> cases rest <;>
          simp_all [TuringMachine.stepConfig, scanConfig, cursorConfig,
            machine, transition, SerializedShift.cursorTape, Tape.read,
            Tape.write, Tape.move, Tape.moveRight, List.map_append]
      rw [hstep]
      simp only
      simpa [returnConfig, List.reverse_cons, List.append_assoc] using
        ih (current :: leftRev) hrest

theorem return_ticks_run_exact
    (count : Nat) (head : Option MachineCodeSymbol)
    (tail rightWord : Word MachineCodeSymbol) :
    machine.runConfigExact? (count + 1)
        (returnConfig head
          (List.append (HeadLocator.ticks count)
            (MachineCodeSymbol.done :: tail))
          rightWord) =
      some
        (cursorConfig (.positioned head)
          (MachineCodeSymbol.done :: tail)
          (List.append (HeadLocator.ticks count) rightWord)) := by
  induction count generalizing rightWord with
  | zero => cases tail <;> cases rightWord <;> rfl
  | succ count ih =>
      change
        machine.runConfigExact? (count + 1 + 1)
          (returnConfig head
            (MachineCodeSymbol.tick ::
              List.append (HeadLocator.ticks count)
                (MachineCodeSymbol.done :: tail))
            rightWord) = _
      rw [TuringMachine.runConfigExact?]
      have hstep :
          machine.stepConfig
              (returnConfig head
                (MachineCodeSymbol.tick ::
                  List.append (HeadLocator.ticks count)
                    (MachineCodeSymbol.done :: tail))
                rightWord) =
            some
              (returnConfig head
                (List.append (HeadLocator.ticks count)
                  (MachineCodeSymbol.done :: tail))
                (MachineCodeSymbol.tick :: rightWord)) := by
        have hne :
            List.append (HeadLocator.ticks count)
                (MachineCodeSymbol.done :: tail) ≠ [] := by
          intro h
          have := congrArg List.length h
          simp at this
        cases hshape :
            List.append (HeadLocator.ticks count)
              (MachineCodeSymbol.done :: tail) with
        | nil => contradiction
        | cons next remaining => rfl
      rw [hstep]
      simp only
      rw [ih (MachineCodeSymbol.tick :: rightWord)]
      have hwords :
          List.append (HeadLocator.ticks count)
              (MachineCodeSymbol.tick :: rightWord) =
            List.append (HeadLocator.ticks (count + 1))
              rightWord := by
        calc
          List.append (HeadLocator.ticks count)
              (MachineCodeSymbol.tick :: rightWord) =
              MachineCodeSymbol.tick ::
                List.append (HeadLocator.ticks count) rightWord :=
            HeadLocator.ticks_append_tick count _
          _ = List.append (HeadLocator.ticks (count + 1))
                rightWord := by rfl
      rw [hwords]

theorem optionalCellWord_reverse_append
    (head : Option MachineCodeSymbol) (tail : Word MachineCodeSymbol) :
    List.append (optionalCellWord head).reverse tail =
      MachineCodeSymbol.done ::
        List.append (HeadLocator.ticks (optionalCodeSymbolTag head)) tail := by
  rw [HeadLocator.optionalCellWord_eq_ticks_done]
  simp [List.reverse_append, HeadLocator.ticks_reverse]

theorem entry_marker_handoff
    (head : Option MachineCodeSymbol)
    (tail : Word MachineCodeSymbol)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (cursorConfig (.entry head)
          (MachineCodeSymbol.done :: tail) (first :: rest)) =
      some
        (leftScanConfig (.restoreCells head) tail
          (MachineCodeSymbol.zero :: first :: rest)) := by
  cases tail <;> cases rest <;> rfl

def markedTail {stateCount : Nat}
    (L : Layout stateCount) : Word MachineCodeSymbol :=
  List.append (HeadLocator.markedCellsWord L.left).reverse
    (Dispatch.RightFieldLocator.HeadDecoder.markedCountBaseLeftRev L)

def sourceConfig {stateCount : Nat}
    (L : Layout stateCount)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  cursorConfig (.entry L.head)
    (List.append (optionalCellWord L.head).reverse (markedTail L))
    (first :: rest)

def markerConfig {stateCount : Nat}
    (L : Layout stateCount)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  leftScanConfig (.restoreCells L.head)
    (List.append (HeadLocator.ticks (optionalCodeSymbolTag L.head))
      (markedTail L))
    (MachineCodeSymbol.zero :: first :: rest)

theorem source_marker_handoff {stateCount : Nat}
    (L : Layout stateCount)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    machine.runConfigExact? 2 (sourceConfig L first rest) =
      some (markerConfig L first rest) := by
  unfold sourceConfig markerConfig
  rw [optionalCellWord_reverse_append]
  exact entry_marker_handoff L.head
    (List.append (HeadLocator.ticks (optionalCodeSymbolTag L.head))
      (markedTail L)) first rest

def positionedConfig {stateCount : Nat}
    (L : Layout stateCount)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  cursorConfig (.positioned L.head) (headPrefix L).reverse
    (List.append (optionalCellWord L.head) (first :: rest))

def runSteps {stateCount : Nat} (L : Layout stateCount) : Nat :=
  2 +
    (restoreHeadAndCellsSteps L.head L.left +
      ((L.left.length + 1) +
        ((L.state.val + 1 + L.fuel + 1) +
          (((beforeHeadMarker L).length + 1) +
            (optionalCodeSymbolTag L.head + 1)))))

theorem headPrefix_reverse_shape {stateCount : Nat}
    (L : Layout stateCount) :
    (headPrefix L).reverse =
      MachineCodeSymbol.done ::
        List.append
          (Edits.OptionalField.LayoutSpecialization.middle L).reverse
          [MachineCodeSymbol.header] := by
  rw [Edits.OptionalField.LayoutSpecialization.headPrefix_decomp]
  simp [List.reverse_append]

theorem beforeHeadMarker_reverse_shape {stateCount : Nat}
    (L : Layout stateCount) :
    List.append (beforeHeadMarker L).reverse [MachineCodeSymbol.header] =
      List.append (HeadLocator.ticks (optionalCodeSymbolTag L.head))
        ((headPrefix L).reverse) := by
  unfold beforeHeadMarker
  rw [headPrefix_reverse_shape]
  simp [List.reverse_append, HeadLocator.ticks_reverse,
    List.append_assoc]

theorem run_exact {stateCount : Nat}
    (L : Layout stateCount)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    machine.runConfigExact? (runSteps L) (sourceConfig L first rest) =
      some (positionedConfig L first rest) := by
  unfold runSteps
  rw [TuringMachine.runConfigExact?_add]
  rw [source_marker_handoff]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  unfold markerConfig markedTail
  unfold Dispatch.RightFieldLocator.HeadDecoder.markedCountBaseLeftRev
  rw [restoreHeadAndCells_marker_run_exact L.head L.left
    (List.append (HeadLocator.transitionMarkers L.left.length)
      (HeadLocator.countBaseLeftRev L))
    (first :: rest) (by
      intro h
      have := congrArg List.length h
      simp [HeadLocator.countBaseLeftRev] at this)]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  unfold HeadLocator.countBaseLeftRev
  rw [restoreCount_run_exact]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  rw [seekTopHeader_fields_to_scan_exact]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  rw [show cursorConfig (.scanMarker L.head) [MachineCodeSymbol.header]
        (List.append (beforeHeadMarker L)
          (MachineCodeSymbol.zero :: first :: rest)) =
      scanConfig L.head [MachineCodeSymbol.header]
        (beforeHeadMarker L) (first :: rest) from rfl]
  rw [scan_run_exact L.head [MachineCodeSymbol.header]
    (beforeHeadMarker L) (first :: rest) (beforeHeadMarker_safe L)]
  simp only
  rw [beforeHeadMarker_reverse_shape]
  unfold positionedConfig
  rw [headPrefix_reverse_shape]
  rw [HeadLocator.optionalCellWord_eq_ticks_done]
  rw [return_ticks_run_exact]
  simp [List.append_assoc]

end Post

end HeadCursor
end Dispatch
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
