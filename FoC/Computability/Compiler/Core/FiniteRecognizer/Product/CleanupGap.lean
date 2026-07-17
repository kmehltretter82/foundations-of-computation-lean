import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.CleanupShapes

set_option doc.verso true

/-!
# Product cleanup gap movers

Collision-free local machines shift the retained product-call prefix across a
single protected gap. Both machines turn at caller-independent sentinels and
preserve caller-owned cells as opaque physical-cell suffixes.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductCleanupGap

namespace PrefixLeftShiftOne

inductive Control where
  | eraseHeader
  | takeLast
  | carry (symbol : MachineCodeSymbol)
  | seekGap
  | restoreHeader
  | crossGap
  | rewind
  | halt
deriving DecidableEq

namespace Control

private def elems : List Control :=
  [.eraseHeader, .takeLast, .seekGap, .restoreHeader,
    .crossGap, .rewind, .halt] ++
    MachineCodeSymbol.finite.elems.map Control.carry

private def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | eraseHeader => simp [elems]
    | takeLast => simp [elems]
    | carry symbol =>
        simp [elems]
        exact MachineCodeSymbol.finite.complete symbol
    | seekGap => simp [elems]
    | restoreHeader => simp [elems]
    | crossGap => simp [elems]
    | rewind => simp [elems]
    | halt => simp [elems]

end Control

private def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .eraseHeader, _ =>
      some (none, Direction.left, .takeLast)
  | .takeLast, some current =>
      some (none, Direction.left, .carry current)
  | .takeLast, none => none
  | .carry carried, some current =>
      some (some carried, Direction.left, .carry current)
  | .carry carried, none =>
      some (some carried, Direction.right, .seekGap)
  | .seekGap, some current =>
      some (some current, Direction.right, .seekGap)
  | .seekGap, none =>
      some (none, Direction.right, .restoreHeader)
  | .restoreHeader, _ =>
      some (some MachineCodeSymbol.header, Direction.left, .crossGap)
  | .crossGap, _ =>
      some (none, Direction.left, .rewind)
  | .rewind, some current =>
      some (some current, Direction.left, .rewind)
  | .rewind, none =>
      some (none, Direction.right, .halt)
  | .halt, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .eraseHeader
  halt := .halt
  transition := transition
  statesFinite := Control.finite

private def config (state : Control) (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := state
  tape := tape

def sourceTape (word : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) : Tape MachineCodeSymbol :=
  { left := word.reverse.map some
    head := some MachineCodeSymbol.header
    right := callerCells }

def sourceConfig (word : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .eraseHeader (sourceTape word callerCells)

private def reverseSourceConfig (prefixRev : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .eraseHeader
    { left := prefixRev.map some
      head := some MachineCodeSymbol.header
      right := callerCells }

private def takeConfig (last : MachineCodeSymbol)
    (remainingRev : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .takeLast
    { left := remainingRev.map some
      head := some last
      right := none :: callerCells }

private def carryTape (remainingRev shifted : Word MachineCodeSymbol)
    (_carried : MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) : Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := []
        head := none
        right := List.append (shifted.map some)
          (none :: none :: callerCells) }
  | current :: rest =>
      { left := rest.map some
        head := some current
        right := List.append (shifted.map some)
          (none :: none :: callerCells) }

private def carryConfig (remainingRev shifted : Word MachineCodeSymbol)
    (carried : MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config (.carry carried)
    (carryTape remainingRev shifted carried callerCells)

private def seekTape (crossedRev remaining : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) : Tape MachineCodeSymbol :=
  match remaining with
  | [] =>
      { left := crossedRev.map some
        head := none
        right := none :: callerCells }
  | current :: rest =>
      { left := crossedRev.map some
        head := some current
        right := List.append (rest.map some)
          (none :: none :: callerCells) }

private def seekConfig (crossedRev remaining : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .seekGap (seekTape crossedRev remaining callerCells)

private def restoreConfig (prefixRev : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .restoreHeader
    { left := none :: prefixRev.map some
      head := none
      right := callerCells }

private def seekStartConfig (word : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  match word with
  | [] => restoreConfig [] callerCells
  | first :: rest => seekConfig [first] rest callerCells

private def crossGapConfig (prefixRev : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .crossGap
    { left := prefixRev.map some
      head := none
      right := some MachineCodeSymbol.header :: callerCells }

private def rewindTape (remainingRev crossed : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) : Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := []
        head := none
        right := List.append (crossed.map some)
          (none :: some MachineCodeSymbol.header :: callerCells) }
  | current :: rest =>
      { left := rest.map some
        head := some current
        right := List.append (crossed.map some)
          (none :: some MachineCodeSymbol.header :: callerCells) }

private def rewindConfig (remainingRev crossed : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .rewind (rewindTape remainingRev crossed callerCells)

def targetTape (word : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) : Tape MachineCodeSymbol :=
  match word with
  | [] =>
      { left := [none]
        head := none
        right := some MachineCodeSymbol.header :: callerCells }
  | first :: rest =>
      { left := [none]
        head := some first
        right := List.append (rest.map some)
          (none :: some MachineCodeSymbol.header :: callerCells) }

def targetConfig (word : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .halt (targetTape word callerCells)

def runSteps (word : Word MachineCodeSymbol) : Nat :=
  3 * word.length + 5

private theorem erase_step (last : MachineCodeSymbol)
    (remainingRev : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (reverseSourceConfig (last :: remainingRev) callerCells) =
      some (takeConfig last remainingRev callerCells) := by
  rfl

private theorem take_step (last : MachineCodeSymbol)
    (remainingRev : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig (takeConfig last remainingRev callerCells) =
      some (carryConfig remainingRev [] last callerCells) := by
  cases remainingRev <;> rfl

private theorem erase_take_run_exact (last : MachineCodeSymbol)
    (remainingRev : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? 2
        (reverseSourceConfig (last :: remainingRev) callerCells) =
      some (carryConfig remainingRev [] last callerCells) := by
  rw [TuringMachine.runConfigExact?]
  rw [erase_step]
  exact take_step last remainingRev callerCells

private theorem carry_step (current carried : MachineCodeSymbol)
    (remainingRev shifted : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (carryConfig (current :: remainingRev) shifted carried callerCells) =
      some (carryConfig remainingRev (carried :: shifted) current callerCells) := by
  cases remainingRev <;> rfl

private theorem carry_finish (shifted : Word MachineCodeSymbol)
    (carried : MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig (carryConfig [] shifted carried callerCells) =
      some (seekStartConfig (carried :: shifted) callerCells) := by
  cases shifted <;> rfl

private theorem carry_run_exact (remainingRev shifted : Word MachineCodeSymbol)
    (carried : MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? (remainingRev.length + 1)
        (carryConfig remainingRev shifted carried callerCells) =
      some (seekStartConfig
        (List.append remainingRev.reverse (carried :: shifted)) callerCells) := by
  induction remainingRev generalizing shifted carried with
  | nil =>
      rw [TuringMachine.runConfigExact?]
      exact carry_finish shifted carried callerCells
  | cons current remainingRev ih =>
      change machine.runConfigExact? ((remainingRev.length + 1) + 1)
          (carryConfig (current :: remainingRev) shifted carried callerCells) = _
      rw [TuringMachine.runConfigExact?]
      rw [carry_step]
      simp only
      rw [ih (carried :: shifted) current]
      simp [List.reverse_cons, List.append_assoc]

private theorem seek_step (current : MachineCodeSymbol)
    (crossedRev remaining : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (seekConfig crossedRev (current :: remaining) callerCells) =
      some (seekConfig (current :: crossedRev) remaining callerCells) := by
  cases remaining <;> rfl

private theorem seek_finish (crossedRev : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig (seekConfig crossedRev [] callerCells) =
      some (restoreConfig crossedRev callerCells) := by
  rfl

private theorem seek_run_exact (crossedRev remaining : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? (remaining.length + 1)
        (seekConfig crossedRev remaining callerCells) =
      some (restoreConfig
        (List.append remaining.reverse crossedRev) callerCells) := by
  induction remaining generalizing crossedRev with
  | nil =>
      rw [TuringMachine.runConfigExact?]
      exact seek_finish crossedRev callerCells
  | cons current remaining ih =>
      change machine.runConfigExact? ((remaining.length + 1) + 1)
          (seekConfig crossedRev (current :: remaining) callerCells) = _
      rw [TuringMachine.runConfigExact?]
      rw [seek_step]
      simp only
      rw [ih (current :: crossedRev)]
      simp [List.reverse_cons, List.append_assoc]

private theorem seekStart_run_exact (word : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? word.length
        (seekStartConfig word callerCells) =
      some (restoreConfig word.reverse callerCells) := by
  cases word with
  | nil => rfl
  | cons first rest =>
      simpa [seekStartConfig, List.reverse_cons] using
        seek_run_exact [first] rest callerCells

private theorem restore_step (prefixRev : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig (restoreConfig prefixRev callerCells) =
      some (crossGapConfig prefixRev callerCells) := by
  rfl

private theorem cross_gap_step (last : MachineCodeSymbol)
    (remainingRev : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig (crossGapConfig (last :: remainingRev) callerCells) =
      some (rewindConfig (last :: remainingRev) [] callerCells) := by
  cases remainingRev <;> rfl

private theorem restore_cross_run_exact (last : MachineCodeSymbol)
    (remainingRev : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? 2
        (restoreConfig (last :: remainingRev) callerCells) =
      some (rewindConfig (last :: remainingRev) [] callerCells) := by
  rw [TuringMachine.runConfigExact?]
  rw [restore_step]
  exact cross_gap_step last remainingRev callerCells

private theorem rewind_step (current : MachineCodeSymbol)
    (remainingRev crossed : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (rewindConfig (current :: remainingRev) crossed callerCells) =
      some (rewindConfig remainingRev (current :: crossed) callerCells) := by
  cases remainingRev <;> rfl

private theorem rewind_finish (crossed : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig (rewindConfig [] crossed callerCells) =
      some (targetConfig crossed callerCells) := by
  cases crossed <;> rfl

private theorem rewind_run_exact (remainingRev crossed : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? (remainingRev.length + 1)
        (rewindConfig remainingRev crossed callerCells) =
      some (targetConfig
        (List.append remainingRev.reverse crossed) callerCells) := by
  induction remainingRev generalizing crossed with
  | nil =>
      rw [TuringMachine.runConfigExact?]
      exact rewind_finish crossed callerCells
  | cons current remainingRev ih =>
      change machine.runConfigExact? ((remainingRev.length + 1) + 1)
          (rewindConfig (current :: remainingRev) crossed callerCells) = _
      rw [TuringMachine.runConfigExact?]
      rw [rewind_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]

private theorem reverse_run_exact (last : MachineCodeSymbol)
    (remainingRev : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? (runSteps (last :: remainingRev).reverse)
        (reverseSourceConfig (last :: remainingRev) callerCells) =
      some (targetConfig (last :: remainingRev).reverse callerCells) := by
  let prefixRev := last :: remainingRev
  let word := prefixRev.reverse
  have hlength : word.length = prefixRev.length := by
    simp [word]
  have hcarry :
      machine.runConfigExact? prefixRev.length
          (carryConfig remainingRev [] last callerCells) =
        some (seekStartConfig word callerCells) := by
    simpa [word, prefixRev, List.reverse_cons, List.append_assoc] using
      carry_run_exact remainingRev [] last callerCells
  have hseek :
      machine.runConfigExact? prefixRev.length
          (seekStartConfig word callerCells) =
        some (restoreConfig prefixRev callerCells) := by
    simpa [word, prefixRev] using seekStart_run_exact word callerCells
  have hrewind :
      machine.runConfigExact? (prefixRev.length + 1)
          (rewindConfig prefixRev [] callerCells) =
        some (targetConfig word callerCells) := by
    simpa [word, prefixRev] using
      rewind_run_exact prefixRev [] callerCells
  unfold runSteps
  rw [show 3 * word.length + 5 =
      2 + (prefixRev.length +
        (prefixRev.length + (2 + (prefixRev.length + 1)))) by
    rw [hlength]
    lia]
  rw [TuringMachine.runConfigExact?_add]
  rw [erase_take_run_exact]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  rw [hcarry]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  rw [hseek]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  rw [restore_cross_run_exact]
  simp only
  exact hrewind

theorem run_exact (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? (runSteps (first :: rest))
        (sourceConfig (first :: rest) callerCells) =
      some (targetConfig (first :: rest) callerCells) := by
  have hnonempty : (first :: rest).reverse ≠ [] := by simp
  cases hrev : (first :: rest).reverse with
  | nil => contradiction
  | cons last remainingRev =>
      have hprefix : (last :: remainingRev).reverse = first :: rest := by
        rw [← hrev]
        simp
      have hrun := reverse_run_exact last remainingRev callerCells
      have hsource :
          sourceConfig (first :: rest) callerCells =
            reverseSourceConfig (last :: remainingRev) callerCells := by
        simp [sourceConfig, sourceTape, reverseSourceConfig, hrev]
      rw [hsource]
      simpa [hprefix] using hrun

end PrefixLeftShiftOne

namespace PrefixRightShiftOne

inductive Control where
  | takeFirst
  | carry (symbol : MachineCodeSymbol)
  | turnGap
  | rewind
  | halt
deriving DecidableEq

namespace Control

private def elems : List Control :=
  [.takeFirst, .turnGap, .rewind, .halt] ++
    MachineCodeSymbol.finite.elems.map Control.carry

private def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | takeFirst => simp [elems]
    | carry symbol =>
        simp [elems]
        exact MachineCodeSymbol.finite.complete symbol
    | turnGap => simp [elems]
    | rewind => simp [elems]
    | halt => simp [elems]

end Control

private def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .takeFirst, some current =>
      some (none, Direction.right, .carry current)
  | .takeFirst, none => none
  | .carry carried, some current =>
      some (some carried, Direction.right, .carry current)
  | .carry carried, none =>
      some (some carried, Direction.right, .turnGap)
  | .turnGap, _ =>
      some (none, Direction.left, .rewind)
  | .rewind, some current =>
      some (some current, Direction.left, .rewind)
  | .rewind, none =>
      some (none, Direction.right, .halt)
  | .halt, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .takeFirst
  halt := .halt
  transition := transition
  statesFinite := Control.finite

private def config (state : Control) (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := state
  tape := tape

def sourceTape (word : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) : Tape MachineCodeSymbol :=
  match word with
  | [] =>
      { left := []
        head := none
        right := none :: callerCells }
  | first :: rest =>
      { left := []
        head := some first
        right := List.append (rest.map some)
          (none :: none :: callerCells) }

def sourceConfig (word : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .takeFirst (sourceTape word callerCells)

def paddedSourceTape (word : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) : Tape MachineCodeSymbol :=
  { sourceTape word callerCells with left := [none] }

def paddedSourceConfig (word : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .takeFirst (paddedSourceTape word callerCells)

private def carryTape (processedRev remaining : Word MachineCodeSymbol)
    (_carried : MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) : Tape MachineCodeSymbol :=
  match remaining with
  | [] =>
      { left := List.append (processedRev.map some) [none]
        head := none
        right := none :: callerCells }
  | current :: rest =>
      { left := List.append (processedRev.map some) [none]
        head := some current
        right := List.append (rest.map some)
          (none :: none :: callerCells) }

private def carryConfig (processedRev remaining : Word MachineCodeSymbol)
    (carried : MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config (.carry carried)
    (carryTape processedRev remaining carried callerCells)

private def turnConfig (wordRev : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .turnGap
    { left := List.append (wordRev.map some) [none]
      head := none
      right := callerCells }

private def rewindTape (remainingRev crossed : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) : Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := []
        head := none
        right := List.append (crossed.map some) (none :: callerCells) }
  | current :: rest =>
      { left := List.append (rest.map some) [none]
        head := some current
        right := List.append (crossed.map some) (none :: callerCells) }

private def rewindConfig (remainingRev crossed : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .rewind (rewindTape remainingRev crossed callerCells)

def targetTape (word : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) : Tape MachineCodeSymbol :=
  match word with
  | [] =>
      { left := [none]
        head := none
        right := callerCells }
  | first :: rest =>
      { left := [none]
        head := some first
        right := List.append (rest.map some) (none :: callerCells) }

def targetConfig (word : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .halt (targetTape word callerCells)

def runSteps (word : Word MachineCodeSymbol) : Nat :=
  2 * word.length + 3

private theorem take_step (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig (sourceConfig (first :: rest) callerCells) =
      some (carryConfig [] rest first callerCells) := by
  cases rest <;> rfl

private theorem carry_step (current carried : MachineCodeSymbol)
    (processedRev remaining : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (carryConfig processedRev (current :: remaining)
          carried callerCells) =
      some (carryConfig (carried :: processedRev) remaining
        current callerCells) := by
  cases remaining <;> rfl

private theorem carry_finish (processedRev : Word MachineCodeSymbol)
    (carried : MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (carryConfig processedRev [] carried callerCells) =
      some (turnConfig (carried :: processedRev) callerCells) := by
  rfl

private theorem carry_run_exact (processedRev remaining : Word MachineCodeSymbol)
    (carried : MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? (remaining.length + 1)
        (carryConfig processedRev remaining carried callerCells) =
      some (turnConfig
        (List.append remaining.reverse (carried :: processedRev))
        callerCells) := by
  induction remaining generalizing processedRev carried with
  | nil =>
      rw [TuringMachine.runConfigExact?]
      exact carry_finish processedRev carried callerCells
  | cons current remaining ih =>
      change machine.runConfigExact? ((remaining.length + 1) + 1)
          (carryConfig processedRev (current :: remaining)
            carried callerCells) = _
      rw [TuringMachine.runConfigExact?]
      rw [carry_step]
      simp only
      rw [ih (carried :: processedRev) current]
      simp [List.reverse_cons, List.append_assoc]

private theorem turn_step (last : MachineCodeSymbol)
    (remainingRev : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig (turnConfig (last :: remainingRev) callerCells) =
      some (rewindConfig (last :: remainingRev) [] callerCells) := by
  cases remainingRev <;> rfl

private theorem turn_word_step (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (turnConfig (first :: rest).reverse callerCells) =
      some (rewindConfig (first :: rest).reverse [] callerCells) := by
  have hnonempty : (first :: rest).reverse ≠ [] := by simp
  cases hrev : (first :: rest).reverse with
  | nil => contradiction
  | cons last remainingRev =>
      simpa [hrev] using turn_step last remainingRev callerCells

private theorem rewind_step (current : MachineCodeSymbol)
    (remainingRev crossed : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (rewindConfig (current :: remainingRev) crossed callerCells) =
      some (rewindConfig remainingRev (current :: crossed) callerCells) := by
  cases remainingRev <;> rfl

private theorem rewind_finish (crossed : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.stepConfig (rewindConfig [] crossed callerCells) =
      some (targetConfig crossed callerCells) := by
  cases crossed <;> rfl

private theorem rewind_run_exact (remainingRev crossed : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? (remainingRev.length + 1)
        (rewindConfig remainingRev crossed callerCells) =
      some (targetConfig
        (List.append remainingRev.reverse crossed) callerCells) := by
  induction remainingRev generalizing crossed with
  | nil =>
      rw [TuringMachine.runConfigExact?]
      exact rewind_finish crossed callerCells
  | cons current remainingRev ih =>
      change machine.runConfigExact? ((remainingRev.length + 1) + 1)
          (rewindConfig (current :: remainingRev) crossed callerCells) = _
      rw [TuringMachine.runConfigExact?]
      rw [rewind_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]

theorem run_exact (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    machine.runConfigExact? (runSteps (first :: rest))
        (sourceConfig (first :: rest) callerCells) =
      some (targetConfig (first :: rest) callerCells) := by
  let word := first :: rest
  have htake :
      machine.runConfigExact? 1
          (sourceConfig (first :: rest) callerCells) =
        some (carryConfig [] rest first callerCells) := by
    rw [TuringMachine.runConfigExact?]
    exact take_step first rest callerCells
  have hcarry :
      machine.runConfigExact? word.length
          (carryConfig [] rest first callerCells) =
        some (turnConfig word.reverse callerCells) := by
    simpa [word, List.reverse_cons, List.append_assoc] using
      carry_run_exact [] rest first callerCells
  have hturn :
      machine.runConfigExact? 1 (turnConfig word.reverse callerCells) =
        some (rewindConfig word.reverse [] callerCells) := by
    rw [TuringMachine.runConfigExact?]
    exact turn_word_step first rest callerCells
  have hrewind :
      machine.runConfigExact? (word.length + 1)
          (rewindConfig word.reverse [] callerCells) =
        some (targetConfig word callerCells) := by
    simpa [word] using
      rewind_run_exact word.reverse [] callerCells
  unfold runSteps
  rw [show 2 * (first :: rest).length + 3 =
      1 + (word.length + (1 + (word.length + 1))) by
    simp [word]
    lia]
  rw [TuringMachine.runConfigExact?_add]
  rw [htake]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  rw [hcarry]
  simp only
  rw [TuringMachine.runConfigExact?_add]
  rw [hturn]
  simp only
  exact hrewind

theorem sourceTape_equiv_paddedSourceTape (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    Tape.Equiv
      (sourceTape (first :: rest) callerCells)
      (paddedSourceTape (first :: rest) callerCells) := by
  simp [sourceTape, paddedSourceTape, Tape.Equiv, Tape.dropTrailingNone]

theorem run_from_padded_source (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (callerCells : List (Option MachineCodeSymbol)) :
    exists endpoint :
        TuringMachine.Configuration MachineCodeSymbol Control,
      machine.runConfigExact? (runSteps (first :: rest))
          (paddedSourceConfig (first :: rest) callerCells) =
        some endpoint ∧
      endpoint.state = .halt ∧
      Tape.Equiv (targetTape (first :: rest) callerCells)
        endpoint.tape := by
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        (run_exact first rest callerCells)
        (sourceTape_equiv_paddedSourceTape first rest callerCells) with
    ⟨endpoint, hrun, hstate, htape⟩
  refine ⟨endpoint, ?_, ?_, htape⟩
  · simpa [sourceConfig, paddedSourceConfig, config] using hrun
  · simpa [targetConfig, config] using hstate

end PrefixRightShiftOne

end ProductCleanupGap
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
