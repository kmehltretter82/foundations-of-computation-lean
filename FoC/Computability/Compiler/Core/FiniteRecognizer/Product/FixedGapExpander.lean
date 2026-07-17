import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Contextual.EmptyCallerWriter
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.CleanupPack
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.CallerTail

set_option doc.verso true

/-!
# Fixed product gap expansion

Expand the blank gap before a protected caller word by a construction-time
constant. The pass index lives in finite control, so no runtime counter is
stored on tape.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductGapExpander


inductive Control (gapExtra : Nat) where
  | enterGap
  | crossGap
  | initialRewind
  | seekGap (pass : Fin gapExtra)
  | takeLast (pass : Fin gapExtra)
  | carry (pass : Fin gapExtra) (symbol : MachineCodeSymbol)
  | returnFirst (pass : Fin gapExtra)
  | seekFuel
  | halt
deriving DecidableEq

namespace Control

def passFinite (gapExtra : Nat) : Foundation.FiniteType (Fin gapExtra) :=
  Foundation.FiniteType.fin gapExtra

def carryFinite (gapExtra : Nat) :
    Foundation.FiniteType (Fin gapExtra × MachineCodeSymbol) :=
  Foundation.FiniteType.prod (passFinite gapExtra)
    MachineCodeSymbol.finite

def elems (gapExtra : Nat) : List (Control gapExtra) :=
  [.enterGap, .crossGap, .initialRewind, .seekFuel, .halt] ++
    (passFinite gapExtra).elems.map Control.seekGap ++
    (passFinite gapExtra).elems.map Control.takeLast ++
    ((carryFinite gapExtra).elems.map fun payload =>
      Control.carry payload.1 payload.2) ++
    (passFinite gapExtra).elems.map Control.returnFirst

def finite (gapExtra : Nat) : Foundation.FiniteType (Control gapExtra) where
  elems := elems gapExtra
  complete := by
    intro control
    cases control with
    | enterGap => simp [elems]
    | crossGap => simp [elems]
    | initialRewind => simp [elems]
    | seekGap pass =>
        have h := (passFinite gapExtra).complete pass
        simp [elems, h]
    | takeLast pass =>
        have h := (passFinite gapExtra).complete pass
        simp [elems, h]
    | carry pass symbol =>
        have h := (carryFinite gapExtra).complete (pass, symbol)
        simp [elems, h]
    | returnFirst pass =>
        have h := (passFinite gapExtra).complete pass
        simp [elems, h]
    | seekFuel => simp [elems]
    | halt => simp [elems]

end Control

def nextPass? {gapExtra : Nat} (pass : Fin gapExtra) :
    Option (Fin gapExtra) :=
  if h : pass.val + 1 < gapExtra then
    some ⟨pass.val + 1, h⟩
  else
    none

def afterPassControl {gapExtra : Nat} (pass : Fin gapExtra) :
    Control gapExtra :=
  match nextPass? pass with
  | none => .seekFuel
  | some next => .seekGap next

def transition {gapExtra : Nat} (hpositive : 0 < gapExtra) :
    Control gapExtra -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control gapExtra)
  | .enterGap, some .header =>
      some (some .header, Direction.left, .crossGap)
  | .enterGap, _ => none
  | .crossGap, none =>
      some (none, Direction.left, .initialRewind)
  | .crossGap, _ => none
  | .initialRewind, some current =>
      some (some current, Direction.left, .initialRewind)
  | .initialRewind, none =>
      some (none, Direction.right, .seekGap ⟨0, hpositive⟩)
  | .seekGap pass, some current =>
      some (some current, Direction.right, .seekGap pass)
  | .seekGap pass, none =>
      some (none, Direction.left, .takeLast pass)
  | .takeLast pass, some current =>
      some (none, Direction.left, .carry pass current)
  | .takeLast _, none => none
  | .carry pass carried, some current =>
      some (some carried, Direction.left, .carry pass current)
  | .carry pass carried, none =>
      some (some carried, Direction.right, .returnFirst pass)
  | .returnFirst pass, current =>
      some (current, Direction.left, afterPassControl pass)
  | .seekFuel, some .tick =>
      some (some .tick, Direction.right, .seekFuel)
  | .seekFuel, some .done =>
      some (some .done, Direction.right, .halt)
  | .seekFuel, _ => none
  | .halt, _ => none

def machine {gapExtra : Nat} (hpositive : 0 < gapExtra) :
    TuringMachine MachineCodeSymbol (Control gapExtra) where
  start := .enterGap
  halt := .halt
  transition := transition hpositive
  statesFinite := Control.finite gapExtra

def config {gapExtra : Nat} (state : Control gapExtra)
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control gapExtra) where
  state := state
  tape := tape

def callerSuffix (callerData : Word MachineCodeSymbol) :
    List (Option MachineCodeSymbol) := callerData.map some

def gapSuffix (gap : Nat) (callerData : Word MachineCodeSymbol) :
    List (Option MachineCodeSymbol) :=
  List.append (List.replicate gap (none : Option MachineCodeSymbol))
    (callerSuffix callerData)

def padCells (padded : Bool) : List (Option MachineCodeSymbol) :=
  if padded then [none] else []

def packedSourceTape (word callerData : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  { left := none :: List.append (word.reverse.map some) [none]
    head := some MachineCodeSymbol.header
    right := callerData.tail.map some }

def packedSourceConfig {gapExtra : Nat}
    (word callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control gapExtra) :=
  config .enterGap (packedSourceTape word callerData)

def entryGapConfig {gapExtra : Nat}
    (word callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control gapExtra) :=
  config .crossGap
    { left := List.append (word.reverse.map some) [none]
      head := none
      right := callerSuffix callerData }

def initialRewindTape (remainingRev crossed : Word MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := []
        head := none
        right := List.append (crossed.map some)
          (gapSuffix 1 callerData) }
  | current :: rest =>
      { left := List.append (rest.map some) [none]
        head := some current
        right := List.append (crossed.map some)
          (gapSuffix 1 callerData) }

def initialRewindConfig {gapExtra : Nat}
    (remainingRev crossed callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control gapExtra) :=
  config .initialRewind
    (initialRewindTape remainingRev crossed callerData)

def passTape (padded : Bool) (word : Word MachineCodeSymbol)
    (gap : Nat) (callerData : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match word with
  | [] =>
      { left := padCells padded
        head := none
        right := gapSuffix gap callerData }
  | first :: rest =>
      { left := padCells padded
        head := some first
        right := List.append (rest.map some)
          (gapSuffix gap callerData) }

def passConfig {gapExtra : Nat} (pass : Fin gapExtra)
    (padded : Bool) (word : Word MachineCodeSymbol)
    (gap : Nat) (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control gapExtra) :=
  config (.seekGap pass) (passTape padded word gap callerData)

def seekTape (padded : Bool) (crossedRev remaining : Word MachineCodeSymbol)
    (gap : Nat) (callerData : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match remaining with
  | [] =>
      { left := List.append (crossedRev.map some) (padCells padded)
        head := none
        right := (gapSuffix gap callerData).tail }
  | current :: rest =>
      { left := List.append (crossedRev.map some) (padCells padded)
        head := some current
        right := List.append (rest.map some)
          (gapSuffix gap callerData) }

def seekConfig {gapExtra : Nat} (pass : Fin gapExtra)
    (padded : Bool) (crossedRev remaining : Word MachineCodeSymbol)
    (gap : Nat) (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control gapExtra) :=
  config (.seekGap pass)
    (seekTape padded crossedRev remaining gap callerData)

def takeConfig {gapExtra : Nat} (pass : Fin gapExtra)
    (padded : Bool) (last : MachineCodeSymbol)
    (remainingRev : Word MachineCodeSymbol) (gap : Nat)
    (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control gapExtra) :=
  config (.takeLast pass)
    { left := List.append (remainingRev.map some) (padCells padded)
      head := some last
      right := gapSuffix gap callerData }

def carryTape (padded : Bool) (remainingRev shifted : Word MachineCodeSymbol)
    (gap : Nat) (callerData : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := []
        head := none
        right := List.append (shifted.map some)
          (gapSuffix (gap + 1) callerData) }
  | current :: rest =>
      { left := List.append (rest.map some) (padCells padded)
        head := some current
        right := List.append (shifted.map some)
          (gapSuffix (gap + 1) callerData) }

def carryConfig {gapExtra : Nat} (pass : Fin gapExtra)
    (padded : Bool) (remainingRev shifted : Word MachineCodeSymbol)
    (carried : MachineCodeSymbol) (gap : Nat)
    (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control gapExtra) :=
  config (.carry pass carried)
    (carryTape padded remainingRev shifted gap callerData)

def returnTape (word : Word MachineCodeSymbol) (gap : Nat)
    (callerData : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match word with
  | [] =>
      { left := []
        head := none
        right := (gapSuffix gap callerData).tail }
  | first :: rest =>
      match rest with
      | [] =>
          { left := [some first]
            head := none
            right := (gapSuffix gap callerData).tail }
      | current :: suffix =>
          { left := [some first]
            head := some current
            right := List.append (suffix.map some)
              (gapSuffix gap callerData) }

def returnConfig {gapExtra : Nat} (pass : Fin gapExtra)
    (word : Word MachineCodeSymbol) (gap : Nat)
    (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control gapExtra) :=
  config (.returnFirst pass) (returnTape word gap callerData)

def returnStartConfig {gapExtra : Nat} (pass : Fin gapExtra)
    (word : Word MachineCodeSymbol) (gap : Nat)
    (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control gapExtra) :=
  match word with
  | [] => returnConfig pass [] gap callerData
  | first :: rest => returnConfig pass (first :: rest) gap callerData

def afterPassConfig {gapExtra : Nat} (pass : Fin gapExtra)
    (word : Word MachineCodeSymbol) (gap : Nat)
    (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control gapExtra) :=
  config (afterPassControl pass) (passTape false word gap callerData)

def fuelStartConfig {gapExtra : Nat} (word : Word MachineCodeSymbol)
    (gap : Nat) (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control gapExtra) :=
  config .seekFuel (passTape false word gap callerData)

theorem enter_step {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (word callerRest : Word MachineCodeSymbol) :
    (machine hpositive).stepConfig
        (packedSourceConfig word
          (MachineCodeSymbol.header :: callerRest)) =
      some (entryGapConfig word
        (MachineCodeSymbol.header :: callerRest)) := by
  rfl

theorem cross_step {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (word : Word MachineCodeSymbol) (last : MachineCodeSymbol)
    (remainingRev callerData : Word MachineCodeSymbol)
    (hreverse : word.reverse = last :: remainingRev) :
    (machine hpositive).stepConfig (entryGapConfig word callerData) =
      some (initialRewindConfig (last :: remainingRev) [] callerData) := by
  unfold entryGapConfig
  rw [show word.reverse.map some =
      (last :: remainingRev).map some by rw [hreverse]]
  rfl

theorem initial_rewind_step {gapExtra : Nat}
    (hpositive : 0 < gapExtra) (current : MachineCodeSymbol)
    (remainingRev crossed callerData : Word MachineCodeSymbol) :
    (machine hpositive).stepConfig
        (initialRewindConfig (current :: remainingRev) crossed callerData) =
      some (initialRewindConfig remainingRev
        (current :: crossed) callerData) := by
  cases remainingRev <;> rfl

theorem initial_rewind_finish {gapExtra : Nat}
    (hpositive : 0 < gapExtra) (first : MachineCodeSymbol)
    (rest callerData : Word MachineCodeSymbol) :
    (machine hpositive).stepConfig
        (initialRewindConfig [] (first :: rest) callerData) =
      some (passConfig ⟨0, hpositive⟩ true
        (first :: rest) 1 callerData) := by
  cases rest <;> rfl

theorem initial_rewind_scan_exact {gapExtra : Nat}
    (hpositive : 0 < gapExtra)
    (remainingRev crossed callerData : Word MachineCodeSymbol) :
    (machine hpositive).runConfigExact? remainingRev.length
        (initialRewindConfig remainingRev crossed callerData) =
      some (initialRewindConfig []
        (List.append remainingRev.reverse crossed) callerData) := by
  induction remainingRev generalizing crossed with
  | nil => rfl
  | cons current remainingRev ih =>
      change (machine hpositive).runConfigExact?
          (remainingRev.length + 1)
          (initialRewindConfig (current :: remainingRev)
            crossed callerData) = _
      rw [TuringMachine.runConfigExact?]
      rw [initial_rewind_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]

def initialSteps (word : Word MachineCodeSymbol) : Nat :=
  word.length + 3

theorem initial_run_exact {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (first : MachineCodeSymbol) (rest callerRest : Word MachineCodeSymbol) :
    (machine hpositive).runConfigExact? (initialSteps (first :: rest))
        (packedSourceConfig (first :: rest)
          (MachineCodeSymbol.header :: callerRest)) =
      some (passConfig ⟨0, hpositive⟩ true
        (first :: rest) 1
        (MachineCodeSymbol.header :: callerRest)) := by
  have hnonempty : (first :: rest).reverse ≠ [] := by simp
  cases hreverse : (first :: rest).reverse with
  | nil => contradiction
  | cons last remainingRev =>
      have henter :
          (machine hpositive).runConfigExact? 1
              (packedSourceConfig (first :: rest)
                (MachineCodeSymbol.header :: callerRest)) =
            some (entryGapConfig (first :: rest)
              (MachineCodeSymbol.header :: callerRest)) := by
        rw [TuringMachine.runConfigExact?]
        exact enter_step hpositive (first :: rest) callerRest
      have hcross :
          (machine hpositive).runConfigExact? 1
              (entryGapConfig (first :: rest)
                (MachineCodeSymbol.header :: callerRest)) =
            some (initialRewindConfig (last :: remainingRev) []
              (MachineCodeSymbol.header :: callerRest)) := by
        rw [TuringMachine.runConfigExact?]
        exact cross_step hpositive (first :: rest) last remainingRev
          (MachineCodeSymbol.header :: callerRest) hreverse
      have hscan :
          (machine hpositive).runConfigExact? (first :: rest).length
              (initialRewindConfig (last :: remainingRev) []
                (MachineCodeSymbol.header :: callerRest)) =
            some (initialRewindConfig [] (first :: rest)
              (MachineCodeSymbol.header :: callerRest)) := by
        have hlen : (last :: remainingRev).length =
            (first :: rest).length := by
          have h := congrArg List.length hreverse
          simpa using h.symm
        rw [← hlen]
        have hrun := initial_rewind_scan_exact hpositive
          (last :: remainingRev) []
          (MachineCodeSymbol.header :: callerRest)
        have hword : (last :: remainingRev).reverse = first :: rest := by
          rw [← hreverse]
          simp
        simpa [hword] using hrun
      have hfinish :
          (machine hpositive).runConfigExact? 1
              (initialRewindConfig [] (first :: rest)
                (MachineCodeSymbol.header :: callerRest)) =
            some (passConfig ⟨0, hpositive⟩ true
              (first :: rest) 1
              (MachineCodeSymbol.header :: callerRest)) := by
        rw [TuringMachine.runConfigExact?]
        exact initial_rewind_finish hpositive first rest
          (MachineCodeSymbol.header :: callerRest)
      unfold initialSteps
      rw [show (first :: rest).length + 3 =
          1 + (1 + ((first :: rest).length + 1)) by lia]
      rw [TuringMachine.runConfigExact?_add]
      rw [henter]
      simp only
      rw [TuringMachine.runConfigExact?_add]
      rw [hcross]
      simp only
      rw [TuringMachine.runConfigExact?_add]
      rw [hscan]
      simp only
      exact hfinish

theorem passConfig_eq_seekConfig {gapExtra : Nat} (pass : Fin gapExtra)
    (padded : Bool) (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) (gap : Nat)
    (callerData : Word MachineCodeSymbol) :
    passConfig pass padded (first :: rest) gap callerData =
      seekConfig pass padded [] (first :: rest) gap callerData := by
  rfl

theorem seek_step {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (pass : Fin gapExtra) (padded : Bool)
    (current : MachineCodeSymbol) (crossedRev remaining :
      Word MachineCodeSymbol) (gapTail : Nat)
    (callerData : Word MachineCodeSymbol) :
    (machine hpositive).stepConfig
        (seekConfig pass padded crossedRev (current :: remaining)
          (gapTail + 1) callerData) =
      some (seekConfig pass padded (current :: crossedRev)
        remaining (gapTail + 1) callerData) := by
  cases remaining <;> rfl

theorem seek_finish {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (pass : Fin gapExtra) (padded : Bool)
    (last : MachineCodeSymbol) (remainingRev : Word MachineCodeSymbol)
    (gapTail : Nat) (callerData : Word MachineCodeSymbol) :
    (machine hpositive).stepConfig
        (seekConfig pass padded (last :: remainingRev) []
          (gapTail + 1) callerData) =
      some (takeConfig pass padded last remainingRev
        (gapTail + 1) callerData) := by
  cases remainingRev <;> cases padded <;> rfl

theorem seek_scan_exact {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (pass : Fin gapExtra) (padded : Bool)
    (crossedRev remaining : Word MachineCodeSymbol)
    (gapTail : Nat) (callerData : Word MachineCodeSymbol) :
    (machine hpositive).runConfigExact? remaining.length
        (seekConfig pass padded crossedRev remaining
          (gapTail + 1) callerData) =
      some (seekConfig pass padded
        (List.append remaining.reverse crossedRev) []
        (gapTail + 1) callerData) := by
  induction remaining generalizing crossedRev with
  | nil => rfl
  | cons current remaining ih =>
      change (machine hpositive).runConfigExact?
          (remaining.length + 1)
          (seekConfig pass padded crossedRev (current :: remaining)
            (gapTail + 1) callerData) = _
      rw [TuringMachine.runConfigExact?]
      rw [seek_step]
      simp only
      rw [ih (current :: crossedRev)]
      simp [List.reverse_cons, List.append_assoc]

theorem take_step {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (pass : Fin gapExtra) (padded : Bool)
    (last : MachineCodeSymbol) (remainingRev : Word MachineCodeSymbol)
    (gap : Nat) (callerData : Word MachineCodeSymbol) :
    (machine hpositive).stepConfig
        (takeConfig pass padded last remainingRev gap callerData) =
      some (carryConfig pass padded remainingRev [] last gap callerData) := by
  cases gap <;> cases remainingRev <;> cases padded <;> rfl

theorem carry_step {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (pass : Fin gapExtra) (padded : Bool)
    (current carried : MachineCodeSymbol)
    (remainingRev shifted : Word MachineCodeSymbol)
    (gap : Nat) (callerData : Word MachineCodeSymbol) :
    (machine hpositive).stepConfig
        (carryConfig pass padded (current :: remainingRev)
          shifted carried gap callerData) =
      some (carryConfig pass padded remainingRev
        (carried :: shifted) current gap callerData) := by
  cases gap <;> cases remainingRev <;> cases padded <;> rfl

theorem carry_finish {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (pass : Fin gapExtra) (padded : Bool)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (gap : Nat) (callerData : Word MachineCodeSymbol) :
    (machine hpositive).stepConfig
        (carryConfig pass padded [] rest first gap callerData) =
      some (returnStartConfig pass (first :: rest)
        (gap + 1) callerData) := by
  cases gap <;> cases rest <;> rfl

theorem carry_run_exact {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (pass : Fin gapExtra) (padded : Bool)
    (remainingRev shifted : Word MachineCodeSymbol)
    (carried : MachineCodeSymbol) (gap : Nat)
    (callerData : Word MachineCodeSymbol) :
    (machine hpositive).runConfigExact? (remainingRev.length + 1)
        (carryConfig pass padded remainingRev shifted carried
          gap callerData) =
      some (returnStartConfig pass
        (List.append remainingRev.reverse (carried :: shifted))
        (gap + 1) callerData) := by
  induction remainingRev generalizing shifted carried with
  | nil =>
      rw [TuringMachine.runConfigExact?]
      exact carry_finish hpositive pass padded carried shifted gap callerData
  | cons current remainingRev ih =>
      change (machine hpositive).runConfigExact?
          ((remainingRev.length + 1) + 1)
          (carryConfig pass padded (current :: remainingRev)
            shifted carried gap callerData) = _
      rw [TuringMachine.runConfigExact?]
      rw [carry_step]
      simp only
      rw [ih (carried :: shifted) current]
      simp [List.reverse_cons, List.append_assoc]

theorem return_step {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (pass : Fin gapExtra) (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) (gapTail : Nat)
    (callerData : Word MachineCodeSymbol) :
    (machine hpositive).stepConfig
        (returnConfig pass (first :: rest) (gapTail + 1) callerData) =
      some (afterPassConfig pass (first :: rest)
        (gapTail + 1) callerData) := by
  cases rest <;> rfl

def passSteps (word : Word MachineCodeSymbol) : Nat :=
  2 * word.length + 3

theorem pass_run_exact {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (pass : Fin gapExtra) (padded : Bool)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (gapTail : Nat) (callerData : Word MachineCodeSymbol) :
    (machine hpositive).runConfigExact? (passSteps (first :: rest))
        (passConfig pass padded (first :: rest)
          (gapTail + 1) callerData) =
      some (afterPassConfig pass (first :: rest)
        ((gapTail + 1) + 1) callerData) := by
  have hnonempty : (first :: rest).reverse ≠ [] := by simp
  cases hreverse : (first :: rest).reverse with
  | nil => contradiction
  | cons last remainingRev =>
      have hlength : remainingRev.length + 1 =
          (first :: rest).length := by
        have h := congrArg List.length hreverse
        simp at h
        change remainingRev.length + 1 = rest.length + 1
        rw [h]
      have hword : List.append remainingRev.reverse [last] =
          first :: rest := by
        have hrev : (last :: remainingRev).reverse = first :: rest := by
          rw [← hreverse]
          simp
        simpa [List.reverse_cons] using hrev
      have hseek :
          (machine hpositive).runConfigExact? (first :: rest).length
              (passConfig pass padded (first :: rest)
                (gapTail + 1) callerData) =
            some (seekConfig pass padded (last :: remainingRev) []
              (gapTail + 1) callerData) := by
        rw [passConfig_eq_seekConfig]
        have hrun := seek_scan_exact hpositive pass padded []
          (first :: rest) gapTail callerData
        simpa [hreverse] using hrun
      have hfinish :
          (machine hpositive).runConfigExact? 1
              (seekConfig pass padded (last :: remainingRev) []
                (gapTail + 1) callerData) =
            some (takeConfig pass padded last remainingRev
              (gapTail + 1) callerData) := by
        rw [TuringMachine.runConfigExact?]
        exact seek_finish hpositive pass padded last remainingRev
          gapTail callerData
      have htake :
          (machine hpositive).runConfigExact? 1
              (takeConfig pass padded last remainingRev
                (gapTail + 1) callerData) =
            some (carryConfig pass padded remainingRev [] last
              (gapTail + 1) callerData) := by
        rw [TuringMachine.runConfigExact?]
        exact take_step hpositive pass padded last remainingRev
          (gapTail + 1) callerData
      have hcarry :
          (machine hpositive).runConfigExact? (first :: rest).length
              (carryConfig pass padded remainingRev [] last
                (gapTail + 1) callerData) =
            some (returnStartConfig pass (first :: rest)
              ((gapTail + 1) + 1) callerData) := by
        rw [← hlength]
        rw [carry_run_exact]
        rw [hword]
      have hreturn :
          (machine hpositive).runConfigExact? 1
              (returnStartConfig pass (first :: rest)
                ((gapTail + 1) + 1) callerData) =
            some (afterPassConfig pass (first :: rest)
              ((gapTail + 1) + 1) callerData) := by
        rw [TuringMachine.runConfigExact?]
        exact return_step hpositive pass first rest (gapTail + 1)
          callerData
      unfold passSteps
      rw [show 2 * (first :: rest).length + 3 =
          (first :: rest).length +
            (1 + (1 + ((first :: rest).length + 1))) by lia]
      rw [TuringMachine.runConfigExact?_add]
      rw [hseek]
      simp only
      rw [TuringMachine.runConfigExact?_add]
      rw [hfinish]
      simp only
      rw [TuringMachine.runConfigExact?_add]
      rw [htake]
      simp only
      rw [TuringMachine.runConfigExact?_add]
      rw [hcarry]
      simp only
      exact hreturn

theorem afterPassConfig_eq_next {gapExtra : Nat}
    (pass : Fin gapExtra) (hnext : pass.val + 1 < gapExtra)
    (word : Word MachineCodeSymbol) (gap : Nat)
    (callerData : Word MachineCodeSymbol) :
    afterPassConfig pass word gap callerData =
      passConfig ⟨pass.val + 1, hnext⟩ false word gap callerData := by
  simp [afterPassConfig, afterPassControl, nextPass?, hnext,
    passConfig]

theorem afterPassConfig_eq_fuelStart {gapExtra : Nat}
    (pass : Fin gapExtra) (hfinal : ¬pass.val + 1 < gapExtra)
    (word : Word MachineCodeSymbol) (gap : Nat)
    (callerData : Word MachineCodeSymbol) :
    afterPassConfig pass word gap callerData =
      fuelStartConfig word gap callerData := by
  simp [afterPassConfig, afterPassControl, nextPass?, hfinal,
    fuelStartConfig]

def remainingPassSteps {gapExtra : Nat} (pass : Fin gapExtra)
    (word : Word MachineCodeSymbol) : Nat :=
  (gapExtra - pass.val) * passSteps word

theorem passes_run_exact {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (pass : Fin gapExtra) (padded : Bool)
    (first : MachineCodeSymbol) (rest callerData : Word MachineCodeSymbol) :
    (machine hpositive).runConfigExact?
        (remainingPassSteps pass (first :: rest))
        (passConfig pass padded (first :: rest)
          (pass.val + 1) callerData) =
      some (fuelStartConfig (first :: rest)
        (gapExtra + 1) callerData) := by
  by_cases hnext : pass.val + 1 < gapExtra
  · let next : Fin gapExtra := ⟨pass.val + 1, hnext⟩
    have hpass := pass_run_exact hpositive pass padded first rest
      pass.val callerData
    have hafter := afterPassConfig_eq_next pass hnext
      (first :: rest) ((pass.val + 1) + 1) callerData
    have hrec := passes_run_exact hpositive next false first rest callerData
    have hsub : gapExtra - pass.val =
        (gapExtra - (pass.val + 1)) + 1 := by
      lia
    unfold remainingPassSteps
    rw [hsub, Nat.add_mul, Nat.one_mul]
    rw [Nat.add_comm]
    rw [TuringMachine.runConfigExact?_add]
    rw [hpass]
    simp only
    rw [hafter]
    simpa [next, remainingPassSteps] using hrec
  · have hlast : pass.val + 1 = gapExtra := by
      have hle : gapExtra ≤ pass.val + 1 := by lia
      have hge : pass.val + 1 ≤ gapExtra := pass.isLt
      exact Nat.le_antisymm hge hle
    have hpass := pass_run_exact hpositive pass padded first rest
      pass.val callerData
    have hafter := afterPassConfig_eq_fuelStart pass hnext
      (first :: rest) ((pass.val + 1) + 1) callerData
    unfold remainingPassSteps
    rw [show gapExtra - pass.val = 1 by lia]
    simp only [Nat.one_mul]
    rw [hpass]
    rw [hafter]
    rw [hlast]
termination_by gapExtra - pass.val
decreasing_by
  lia

def shiftSteps (gapExtra : Nat) (word : Word MachineCodeSymbol) : Nat :=
  initialSteps word + gapExtra * passSteps word

theorem shift_run_exact {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (first : MachineCodeSymbol) (rest callerRest : Word MachineCodeSymbol) :
    (machine hpositive).runConfigExact?
        (shiftSteps gapExtra (first :: rest))
        (packedSourceConfig (first :: rest)
          (MachineCodeSymbol.header :: callerRest)) =
      some (fuelStartConfig (first :: rest)
        (gapExtra + 1) (MachineCodeSymbol.header :: callerRest)) := by
  have hinitial := initial_run_exact hpositive first rest callerRest
  have hpasses := passes_run_exact hpositive
    (⟨0, hpositive⟩ : Fin gapExtra) true first rest
    (MachineCodeSymbol.header :: callerRest)
  unfold shiftSteps
  rw [TuringMachine.runConfigExact?_add]
  rw [hinitial]
  simp only
  simpa [remainingPassSteps] using hpasses

def fuelScanTape (crossedRev remainingFuel : Word MachineCodeSymbol)
    (gap : Nat) (callerData : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match remainingFuel with
  | [] =>
      { left := crossedRev.map some
        head := none
        right := (gapSuffix gap callerData).tail }
  | current :: rest =>
      { left := crossedRev.map some
        head := some current
        right := List.append (rest.map some)
          (gapSuffix gap callerData) }

def fuelScanConfig {gapExtra : Nat}
    (crossedRev remainingFuel : Word MachineCodeSymbol)
    (gap : Nat) (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control gapExtra) :=
  config .seekFuel
    (fuelScanTape crossedRev remainingFuel gap callerData)

def expandedConfig {gapExtra : Nat} (leftRev : Word MachineCodeSymbol)
    (gapTail : Nat) (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control gapExtra) :=
  config .halt
    { left := leftRev.map some
      head := none
      right := gapSuffix gapTail callerData }

theorem fuelStartConfig_eq_fuelScanConfig {gapExtra : Nat}
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (gap : Nat) (callerData : Word MachineCodeSymbol) :
    fuelStartConfig (gapExtra := gapExtra)
        (first :: rest) gap callerData =
      fuelScanConfig (gapExtra := gapExtra)
        [] (first :: rest) gap callerData := by
  rfl

theorem fuel_tick_step {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (crossedRev : Word MachineCodeSymbol) (fuel : Nat)
    (gapTail : Nat) (callerData : Word MachineCodeSymbol) :
    (machine hpositive).stepConfig
        (fuelScanConfig crossedRev
          (MachineCodeSymbol.tick :: MachineDescription.encodeNat fuel)
          (gapTail + 1) callerData) =
      some (fuelScanConfig (MachineCodeSymbol.tick :: crossedRev)
        (MachineDescription.encodeNat fuel) (gapTail + 1) callerData) := by
  cases fuel <;> rfl

theorem fuel_done_step {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (crossedRev : Word MachineCodeSymbol)
    (gapTail : Nat) (callerData : Word MachineCodeSymbol) :
    (machine hpositive).stepConfig
        (fuelScanConfig crossedRev [MachineCodeSymbol.done]
          (gapTail + 1) callerData) =
      some (expandedConfig (MachineCodeSymbol.done :: crossedRev)
        gapTail callerData) := by
  rfl

theorem fuel_run_exact {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (fuel : Nat) (crossedRev : Word MachineCodeSymbol)
    (gapTail : Nat) (callerData : Word MachineCodeSymbol) :
    (machine hpositive).runConfigExact?
        (MachineDescription.encodeNat fuel).length
        (fuelScanConfig crossedRev (MachineDescription.encodeNat fuel)
          (gapTail + 1) callerData) =
      some (expandedConfig
        (List.append (MachineDescription.encodeNat fuel).reverse crossedRev)
        gapTail callerData) := by
  induction fuel generalizing crossedRev with
  | zero =>
      change (machine hpositive).runConfigExact? 1
          (fuelScanConfig crossedRev [MachineCodeSymbol.done]
            (gapTail + 1) callerData) = _
      rw [TuringMachine.runConfigExact?]
      rw [fuel_done_step]
      simp [TuringMachine.runConfigExact?, MachineDescription.encodeNat]
  | succ fuel ih =>
      change (machine hpositive).runConfigExact?
          ((MachineDescription.encodeNat fuel).length + 1)
          (fuelScanConfig crossedRev
            (MachineCodeSymbol.tick :: MachineDescription.encodeNat fuel)
            (gapTail + 1) callerData) = _
      rw [TuringMachine.runConfigExact?]
      rw [fuel_tick_step]
      simp only
      rw [ih (MachineCodeSymbol.tick :: crossedRev)]
      simp [MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc]

def runSteps (gapExtra leftFuel : Nat) : Nat :=
  shiftSteps gapExtra (MachineDescription.encodeNat leftFuel) +
    (MachineDescription.encodeNat leftFuel).length

theorem run_generic_exact {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (leftFuel : Nat) (callerRest : Word MachineCodeSymbol) :
    (machine hpositive).runConfigExact? (runSteps gapExtra leftFuel)
        (packedSourceConfig (MachineDescription.encodeNat leftFuel)
          (MachineCodeSymbol.header :: callerRest)) =
      some (expandedConfig (MachineDescription.encodeNat leftFuel).reverse
        gapExtra (MachineCodeSymbol.header :: callerRest)) := by
  have hnonempty : MachineDescription.encodeNat leftFuel ≠ [] := by
    cases leftFuel <;> simp [MachineDescription.encodeNat]
  cases hword : MachineDescription.encodeNat leftFuel with
  | nil => contradiction
  | cons first rest =>
      have hshift := shift_run_exact hpositive first rest callerRest
      have hscan := fuel_run_exact hpositive leftFuel [] gapExtra
        (MachineCodeSymbol.header :: callerRest)
      unfold runSteps
      rw [TuringMachine.runConfigExact?_add]
      rw [hword]
      rw [hshift]
      simp only
      rw [fuelStartConfig_eq_fuelScanConfig]
      rw [← hword]
      simpa using hscan

namespace EmptyContract

def packedOuterLeft (leftFuel : Nat) :
    List (Option MachineCodeSymbol) :=
  List.append
    ((MachineDescription.encodeNat leftFuel).reverse.map some) [none]

theorem pairCallerData_empty_eq_header_body
    {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (rightFuel : Nat) :
    ProductInput.pairCallerData right [] rightFuel =
      MachineCodeSymbol.header ::
        InitialMaterializer.EmptyInputSuffix.body right rightFuel := by
  unfold ProductInput.pairCallerData
  unfold Word
  simpa using
    (ProductInput.emptyBody_append_callerData
      right rightFuel ([] : Word MachineCodeSymbol)).symm

def packedTape
    {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) : Tape MachineCodeSymbol :=
  ProductCleanup.Pack.packedTargetTape
    (packedOuterLeft leftFuel)
    (ProductInput.pairCallerData right [] rightFuel)

theorem packedTape_eq_header_cursor
    {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    packedTape right leftFuel rightFuel =
      { left := none :: List.append
          ((MachineDescription.encodeNat leftFuel).reverse.map some) [none]
        head := some MachineCodeSymbol.header
        right :=
          (InitialMaterializer.EmptyInputSuffix.body
            right rightFuel).map some } := by
  rw [packedTape, pairCallerData_empty_eq_header_body]
  rfl

def expandedTape
    (leftFuel gapTailLength : Nat)
    (callerData : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  { left := (MachineDescription.encodeNat leftFuel).reverse.map some
    head := none
    right := List.append
      (List.replicate gapTailLength (none : Option MachineCodeSymbol))
      (callerData.map some) }

theorem emptySuffix_ne_nil
    {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount)) :
    InitialMaterializer.EmptyInputSuffix.suffix left ≠ [] := by
  intro hnil
  have hlength := congrArg List.length hnil
  simp [InitialMaterializer.EmptyInputSuffix.suffix] at hlength

theorem expandedTape_eq_contextualWriterSource
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    expandedTape leftFuel
        ((InitialMaterializer.EmptyInputSuffix.suffix left).length - 1)
        (ProductInput.pairCallerData right [] rightFuel) =
      (ProductContextual.EmptyCallerWriter.sourceConfig
        (InitialMaterializer.EmptyInputSuffix.suffix left)
        (MachineDescription.encodeNat leftFuel).reverse
        (ProductInput.pairCallerData right [] rightFuel)).tape := by
  have hne := emptySuffix_ne_nil left
  cases hsuffix : InitialMaterializer.EmptyInputSuffix.suffix left with
  | nil => contradiction
  | cons first rest =>
      simp [expandedTape, ProductContextual.EmptyCallerWriter.sourceConfig,
        ProductContextual.EmptyCallerWriter.config,
        ProductContextual.EmptyCallerWriter.gapTape]

end EmptyContract

def emptyExtra {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount)) : Nat :=
  (InitialMaterializer.EmptyInputSuffix.suffix left).length - 1

theorem emptyExtra_positive {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount)) :
    0 < emptyExtra left := by
  unfold emptyExtra
  simp [InitialMaterializer.EmptyInputSuffix.suffix]

def emptyPackedSourceConfig {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    TuringMachine.Configuration MachineCodeSymbol (Control (emptyExtra left)) :=
  config .enterGap
    (EmptyContract.packedTape
      right leftFuel rightFuel)

def emptyWriterTargetConfig {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    TuringMachine.Configuration MachineCodeSymbol (Control (emptyExtra left)) :=
  config .halt
    (ProductContextual.EmptyCallerWriter.sourceConfig
      (InitialMaterializer.EmptyInputSuffix.suffix left)
      (MachineDescription.encodeNat leftFuel).reverse
      (ProductInput.pairCallerData right [] rightFuel)).tape

theorem emptyPackedSourceConfig_eq_generic {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    emptyPackedSourceConfig left right leftFuel rightFuel =
      packedSourceConfig (gapExtra := emptyExtra left)
        (MachineDescription.encodeNat leftFuel)
        (ProductInput.pairCallerData right [] rightFuel) := by
  unfold emptyPackedSourceConfig
  rw [EmptyContract.packedTape_eq_header_cursor]
  rw [EmptyContract.pairCallerData_empty_eq_header_body]
  rfl

theorem emptyWriterTargetConfig_eq_expanded {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    emptyWriterTargetConfig left right leftFuel rightFuel =
      expandedConfig (gapExtra := emptyExtra left)
        (MachineDescription.encodeNat leftFuel).reverse
        (emptyExtra left)
        (ProductInput.pairCallerData right [] rightFuel) := by
  unfold emptyWriterTargetConfig
  rw [← EmptyContract.expandedTape_eq_contextualWriterSource]
  rfl

theorem run_empty_to_writer_exact {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    (machine (emptyExtra_positive left)).runConfigExact?
        (runSteps (emptyExtra left) leftFuel)
        (emptyPackedSourceConfig left right leftFuel rightFuel) =
      some (emptyWriterTargetConfig left right leftFuel rightFuel) := by
  rw [emptyPackedSourceConfig_eq_generic]
  rw [emptyWriterTargetConfig_eq_expanded]
  rw [EmptyContract.pairCallerData_empty_eq_header_body]
  exact run_generic_exact (emptyExtra_positive left) leftFuel
    (InitialMaterializer.EmptyInputSuffix.body right rightFuel)

namespace Nonempty

def fuelScanTape (crossedRev remainingFuel input : Word MachineCodeSymbol)
    (gap : Nat) (callerData : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match remainingFuel with
  | [] =>
      match input with
      | [] =>
          { left := crossedRev.map some
            head := none
            right := gapSuffix gap callerData }
      | first :: rest =>
          { left := crossedRev.map some
            head := some first
            right := List.append (rest.map some)
              (gapSuffix gap callerData) }
  | current :: rest =>
      { left := crossedRev.map some
        head := some current
        right := List.append (rest.map some)
          (List.append (input.map some) (gapSuffix gap callerData)) }

def fuelScanConfig {gapExtra : Nat}
    (crossedRev remainingFuel input : Word MachineCodeSymbol)
    (gap : Nat) (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control gapExtra) :=
  config .seekFuel
    (fuelScanTape crossedRev remainingFuel input gap callerData)

def haltConfig {gapExtra : Nat} (leftRev : Word MachineCodeSymbol)
    (headSymbol : MachineCodeSymbol) (rest callerData :
      Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control gapExtra) :=
  config .halt
    (ProductCallerTail.NonemptyCallerTail.sourceTape
      leftRev headSymbol rest callerData)

theorem tick_step {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (crossedRev : Word MachineCodeSymbol) (fuel : Nat)
    (headSymbol : MachineCodeSymbol) (rest callerData :
      Word MachineCodeSymbol) :
    (machine hpositive).stepConfig
        (fuelScanConfig crossedRev
          (MachineCodeSymbol.tick :: MachineDescription.encodeNat fuel)
          (headSymbol :: rest) 3 callerData) =
      some (fuelScanConfig (MachineCodeSymbol.tick :: crossedRev)
        (MachineDescription.encodeNat fuel) (headSymbol :: rest)
        3 callerData) := by
  cases fuel <;> rfl

theorem done_step {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (crossedRev : Word MachineCodeSymbol)
    (headSymbol : MachineCodeSymbol) (rest callerData :
      Word MachineCodeSymbol) :
    (machine hpositive).stepConfig
        (fuelScanConfig crossedRev [MachineCodeSymbol.done]
          (headSymbol :: rest) 3 callerData) =
      some (haltConfig (MachineCodeSymbol.done :: crossedRev)
        headSymbol rest callerData) := by
  cases rest <;> rfl

theorem fuel_run_exact {gapExtra : Nat} (hpositive : 0 < gapExtra)
    (fuel : Nat) (crossedRev : Word MachineCodeSymbol)
    (headSymbol : MachineCodeSymbol) (rest callerData :
      Word MachineCodeSymbol) :
    (machine hpositive).runConfigExact?
        (MachineDescription.encodeNat fuel).length
        (fuelScanConfig crossedRev (MachineDescription.encodeNat fuel)
          (headSymbol :: rest) 3 callerData) =
      some (haltConfig
        (List.append (MachineDescription.encodeNat fuel).reverse crossedRev)
        headSymbol rest callerData) := by
  induction fuel generalizing crossedRev with
  | zero =>
      change (machine hpositive).runConfigExact? 1
          (fuelScanConfig crossedRev [MachineCodeSymbol.done]
            (headSymbol :: rest) 3 callerData) = _
      rw [TuringMachine.runConfigExact?]
      rw [done_step]
      simp [TuringMachine.runConfigExact?, MachineDescription.encodeNat]
  | succ fuel ih =>
      change (machine hpositive).runConfigExact?
          ((MachineDescription.encodeNat fuel).length + 1)
          (fuelScanConfig crossedRev
            (MachineCodeSymbol.tick :: MachineDescription.encodeNat fuel)
            (headSymbol :: rest) 3 callerData) = _
      rw [TuringMachine.runConfigExact?]
      rw [tick_step]
      simp only
      rw [ih (MachineCodeSymbol.tick :: crossedRev)]
      simp [MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc]

theorem fuelStart_eq_scan {gapExtra : Nat}
    (fuel : Nat) (headSymbol : MachineCodeSymbol)
    (rest callerData : Word MachineCodeSymbol) :
    fuelStartConfig (gapExtra := gapExtra)
        (MachineDescription.encodeNatAppend fuel (headSymbol :: rest))
        3 callerData =
      fuelScanConfig (gapExtra := gapExtra) []
        (MachineDescription.encodeNat fuel) (headSymbol :: rest)
        3 callerData := by
  cases fuel <;>
    simp [MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
      fuelStartConfig, passTape, fuelScanConfig, fuelScanTape,
      config, gapSuffix, callerSuffix, padCells, List.map_append,
      List.append_assoc]

def runSteps (leftFuel : Nat) (input : Word MachineCodeSymbol) : Nat :=
  shiftSteps 2 (MachineDescription.encodeNatAppend leftFuel input) +
    (MachineDescription.encodeNat leftFuel).length

theorem run_generic_exact (leftFuel : Nat)
    (headSymbol : MachineCodeSymbol) (rest callerRest :
      Word MachineCodeSymbol) :
    (machine (by decide : 0 < 2)).runConfigExact?
        (runSteps leftFuel (headSymbol :: rest))
        (packedSourceConfig (gapExtra := 2)
          (MachineDescription.encodeNatAppend leftFuel (headSymbol :: rest))
          (MachineCodeSymbol.header :: callerRest)) =
      some (haltConfig (gapExtra := 2)
        (MachineDescription.encodeNat leftFuel).reverse
        headSymbol rest (MachineCodeSymbol.header :: callerRest)) := by
  let word :=
    MachineDescription.encodeNatAppend leftFuel (headSymbol :: rest)
  have hnonempty : word ≠ [] := by
    cases leftFuel <;> simp [word, MachineDescription.encodeNatAppend,
      MachineDescription.encodeNat]
  cases hword : word with
  | nil => contradiction
  | cons first wordRest =>
      have hshift := shift_run_exact (by decide : 0 < 2)
        first wordRest callerRest
      have hscan := fuel_run_exact (by decide : 0 < 2)
        leftFuel [] headSymbol rest
        (MachineCodeSymbol.header :: callerRest)
      unfold runSteps
      rw [TuringMachine.runConfigExact?_add]
      rw [show MachineDescription.encodeNatAppend leftFuel
          (headSymbol :: rest) = word from rfl]
      rw [hword]
      rw [hshift]
      simp only
      rw [← hword]
      rw [fuelStart_eq_scan]
      simpa using hscan

def pairCallerRest {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (rightFuel : Nat) :
    Word MachineCodeSymbol :=
  (ProductInput.pairCallerData right input rightFuel).tail

theorem pairCallerData_eq_header_cons_rest {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (rightFuel : Nat) :
    ProductInput.pairCallerData right input rightFuel =
      MachineCodeSymbol.header ::
        pairCallerRest right input rightFuel := by
  simp [pairCallerRest, ProductInput.pairCallerData,
    Frame.protectedWord, Layout.encodeAppend]

def packedOuterLeft (input : Word MachineCodeSymbol) (leftFuel : Nat) :
    List (Option MachineCodeSymbol) :=
  List.append
    ((MachineDescription.encodeNatAppend leftFuel input).reverse.map some)
    [none]

def packedSourceConfig {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    TuringMachine.Configuration MachineCodeSymbol (Control 2) :=
  config .enterGap
    (ProductCleanup.Pack.packedTargetTape
      (packedOuterLeft (headSymbol :: rest) leftFuel)
      (ProductInput.pairCallerData
        right (headSymbol :: rest) rightFuel))

def callerTailTargetConfig {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    TuringMachine.Configuration MachineCodeSymbol (Control 2) :=
  haltConfig (MachineDescription.encodeNat leftFuel).reverse
    headSymbol rest
    (ProductInput.pairCallerData right (headSymbol :: rest) rightFuel)

theorem packedSourceConfig_eq_generic {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    packedSourceConfig right headSymbol rest leftFuel rightFuel =
      ProductGapExpander.packedSourceConfig
        (gapExtra := 2)
        (MachineDescription.encodeNatAppend leftFuel (headSymbol :: rest))
        (MachineCodeSymbol.header ::
          pairCallerRest right (headSymbol :: rest) rightFuel) := by
  unfold packedSourceConfig ProductGapExpander.packedSourceConfig
  rw [pairCallerData_eq_header_cons_rest]
  rfl

theorem callerTailTargetConfig_eq_generic {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    callerTailTargetConfig right headSymbol rest leftFuel rightFuel =
      haltConfig (MachineDescription.encodeNat leftFuel).reverse
        headSymbol rest
        (MachineCodeSymbol.header ::
          pairCallerRest right (headSymbol :: rest) rightFuel) := by
  unfold callerTailTargetConfig
  rw [pairCallerData_eq_header_cons_rest]

theorem run_exact {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    (machine (by decide : 0 < 2)).runConfigExact?
        (runSteps leftFuel (headSymbol :: rest))
        (packedSourceConfig right headSymbol rest leftFuel rightFuel) =
      some (callerTailTargetConfig
        right headSymbol rest leftFuel rightFuel) := by
  rw [packedSourceConfig_eq_generic]
  rw [callerTailTargetConfig_eq_generic]
  exact run_generic_exact leftFuel headSymbol rest
    (pairCallerRest right (headSymbol :: rest) rightFuel)

end Nonempty

end ProductGapExpander
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
