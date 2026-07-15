import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Machine
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.SerializedShift
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport

/-!
# Exact-fuel stage-input materializer basics

Finite parser, writer, rewind, and nonempty-region primitives used by the
strict exact-fuel runner's canonical stage-input materializer.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace InitialMaterializer

namespace ExactRun
theorem append (M : TuringMachine symbol state) (first second : Nat)
    (c : TuringMachine.Configuration symbol state) : M.runConfigExact? (first + second) c =
      match M.runConfigExact? first c with
      | none => none
      | some middle => M.runConfigExact? second middle := by
  induction first generalizing c with
  | zero => simp only [Nat.zero_add, TuringMachine.runConfigExact?]
  | succ first ih =>
      rw [Nat.succ_add, TuringMachine.runConfigExact?, TuringMachine.runConfigExact?]
      cases hstep : M.stepConfig c with
      | none => rfl
      | some next => exact ih next
end ExactRun

namespace StageFuelParser

inductive Control (stateCount : Nat) where
  | fuel (carriedState : Fin stateCount)
  | gate (carriedState : Fin stateCount)
deriving DecidableEq

namespace Control
def elems (stateCount : Nat) : List (Control stateCount) :=
  List.append ((List.finRange stateCount).map Control.fuel) ((List.finRange stateCount).map Control.gate)
def finite (stateCount : Nat) : Foundation.FiniteType (Control stateCount) where
  elems := elems stateCount
  complete := by
    intro control
    cases control with
    | fuel state =>
        simp [elems, List.mem_finRange]
    | gate state =>
        simp [elems, List.mem_finRange]
end Control
def transition {stateCount : Nat} : Control stateCount -> Option MachineCodeSymbol -> Option
        (Option MachineCodeSymbol × Direction × Control stateCount)
  | .fuel carriedState, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .fuel carriedState)
  | .fuel carriedState, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .gate carriedState)
  | _, _ => none
def machine {stateCount : Nat} (initialState : Fin stateCount) :
    TuringMachine MachineCodeSymbol (Control stateCount) where
  start := .fuel initialState
  halt := .gate initialState
  transition := transition
  statesFinite := Control.finite stateCount
def config {stateCount : Nat} (control : Control stateCount) (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) where
  state := control
  tape := SerializedShift.cursorTape leftRev rest
def sourceConfig {stateCount : Nat} (initialState : Fin stateCount) (fuel : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) :=
  config (.fuel initialState) [] (MachineDescription.encodeNatAppend fuel input)
def gateConfig {stateCount : Nat} (initialState : Fin stateCount) (fuel : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control stateCount) :=
  config (.gate initialState) (MachineDescription.encodeNat fuel).reverse input
theorem tick_step {stateCount : Nat} (initialState carriedState : Fin stateCount)
    (leftRev suffix : Word MachineCodeSymbol) : (machine initialState).stepConfig
        (config (.fuel carriedState) leftRev (MachineCodeSymbol.tick :: suffix)) = some
        (config (.fuel carriedState) (MachineCodeSymbol.tick :: leftRev) suffix) := by
  cases suffix <;> rfl
theorem done_step {stateCount : Nat} (initialState carriedState : Fin stateCount)
    (leftRev suffix : Word MachineCodeSymbol) : (machine initialState).stepConfig
        (config (.fuel carriedState) leftRev (MachineCodeSymbol.done :: suffix)) = some
        (config (.gate carriedState) (MachineCodeSymbol.done :: leftRev) suffix) := by
  cases suffix <;> rfl
theorem run_from_fuel {stateCount : Nat} (initialState carriedState : Fin stateCount)
    (fuel : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    (machine initialState).runConfigExact? (fuel + 1) (config (.fuel carriedState) leftRev
          (MachineDescription.encodeNatAppend fuel suffix)) = some (config (.gate carriedState)
          (List.append (MachineDescription.encodeNat fuel).reverse leftRev) suffix) := by
  induction fuel generalizing leftRev with
  | zero =>
      exact done_step initialState carriedState leftRev suffix
  | succ fuel ih =>
      change (machine initialState).runConfigExact? ((fuel + 1) + 1)
            (config (.fuel carriedState) leftRev (MachineCodeSymbol.tick ::
                MachineDescription.encodeNatAppend fuel suffix)) = _
      rw [TuringMachine.runConfigExact?]
      rw [tick_step]
      simp only
      rw [ih]
      simp [MachineDescription.encodeNat, List.reverse_cons, List.append_assoc]
theorem run_exact {stateCount : Nat} (initialState : Fin stateCount) (fuel : Nat) (input : Word MachineCodeSymbol) :
    (machine initialState).runConfigExact? (fuel + 1) (sourceConfig initialState fuel input) =
      some (gateConfig initialState fuel input) := by
  simpa [sourceConfig, gateConfig] using run_from_fuel initialState initialState fuel
      ([] : Word MachineCodeSymbol) input
theorem sourceConfig_eq_initial {stateCount : Nat} (initialState : Fin stateCount)
    (fuel : Nat) (input : Word MachineCodeSymbol) : sourceConfig initialState fuel input =
      TuringMachine.initial (machine initialState) (MachineDescription.encodeNatAppend fuel input) := by
  cases fuel <;> rfl
end StageFuelParser

namespace FixedWordWriter
def stateAt (word : Word MachineCodeSymbol) (index : Nat) (hle : index ≤ word.length) : Fin (word.length + 1) :=
  ⟨index, by lia⟩
def transition (word : Word MachineCodeSymbol) : Fin (word.length + 1) -> Option MachineCodeSymbol -> Option
        (Option MachineCodeSymbol × Direction × Fin (word.length + 1))
  | index, none =>
      if h : index.val < word.length then
        some (some (word.get ⟨index.val, h⟩), Direction.right, ⟨index.val + 1, by lia⟩) else
        none
  | _, some _ => none
def machine (word : Word MachineCodeSymbol) : TuringMachine MachineCodeSymbol (Fin (word.length + 1)) where
  start := stateAt word 0 (by simp)
  halt := stateAt word word.length (by simp)
  transition := transition word
  statesFinite := Foundation.FiniteType.fin (word.length + 1)
def config (word : Word MachineCodeSymbol) (index : Nat) (hle : index ≤ word.length)
    (leftRev : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol (Fin (word.length + 1)) where
  state := stateAt word index hle
  tape := SerializedShift.cursorTape leftRev []
theorem step_of_split (word written rest : Word MachineCodeSymbol) (current : MachineCodeSymbol)
    (leftRev : Word MachineCodeSymbol) (hword : word = List.append written (current :: rest)) :
    (machine word).stepConfig (config word written.length (by
          rw [hword]
          simp) leftRev) = some (config word (written.length + 1) (by
          rw [hword]
          simp) (current :: leftRev)) := by
  subst word
  simp [TuringMachine.stepConfig, machine, config, transition, stateAt,
    SerializedShift.cursorTape, Tape.read, Tape.write, Tape.move, Tape.moveRight]
theorem run_of_split (word written rest leftRev : Word MachineCodeSymbol)
    (hword : word = List.append written rest) : (machine word).runConfigExact? rest.length
        (config word written.length (by
          rw [hword]
          simp) leftRev) = some (config word word.length (by simp) (List.append rest.reverse leftRev)) := by
  induction rest generalizing written leftRev with
  | nil =>
      subst word
      simp [TuringMachine.runConfigExact?, config, stateAt]
  | cons current rest ih =>
      change (machine word).runConfigExact? (rest.length + 1) (config word written.length (by
              rw [hword]
              simp) leftRev) = _
      rw [TuringMachine.runConfigExact?]
      rw [step_of_split word written rest current leftRev hword]
      simp only
      have hword' : word = List.append (List.append written [current]) rest := by
        rw [hword]
        simp [List.append_assoc]
      have hrun := ih (List.append written [current]) (current :: leftRev) hword'
      simpa [List.reverse_cons, List.append_assoc] using hrun
theorem run_exact (word leftRev : Word MachineCodeSymbol) :
    (machine word).runConfigExact? word.length (config word 0 (by simp) leftRev) = some
        (config word word.length (by simp) (List.append word.reverse leftRev)) := by
  exact run_of_split word [] word leftRev (by simp)
end FixedWordWriter

namespace PrependHeader

inductive Control where
  | start
  | scan
  | gate
deriving DecidableEq

namespace Control
def elems : List Control := [.start, .scan, .gate]
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control <;> simp [elems]
end Control
abbrev transition : Control -> Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .start, cell => some (cell, Direction.left, .scan)
  | .scan, some symbol =>
      some (some symbol, Direction.left, .scan)
  | .scan, none =>
      some (some MachineCodeSymbol.header, Direction.right, .gate)
  | .gate, _ => none
def machine : TuringMachine MachineCodeSymbol Control where
  start := .start
  halt := .gate
  transition := transition
  statesFinite := Control.finite
def farRightTape (wordRev : Word MachineCodeSymbol) : Tape MachineCodeSymbol where
  left := wordRev.map some
  head := none
  right := []
def startConfig (wordRev : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .start
  tape := farRightTape wordRev
def scanTape (remainingRev crossed : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := []
        head := none
        right := List.append (crossed.map some) [none] }
  | current :: rest =>
      { left := rest.map some
        head := some current
        right := List.append (crossed.map some) [none] }
def scanConfig (remainingRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .scan
  tape := scanTape remainingRev crossed
def gateTape (word : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match word with
  | [] =>
      { left := [some MachineCodeSymbol.header]
        head := none
        right := [] }
  | first :: rest =>
      { left := [some MachineCodeSymbol.header]
        head := some first
        right := List.append (rest.map some) [none] }
def gateConfig (word : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol Control where
  state := .gate
  tape := gateTape word
theorem start_step (wordRev : Word MachineCodeSymbol) :
    machine.stepConfig (startConfig wordRev) = some (scanConfig wordRev []) := by
  cases wordRev <;> rfl
theorem scan_step (current : MachineCodeSymbol) (remainingRev crossed : Word MachineCodeSymbol) : machine.stepConfig
        (scanConfig (current :: remainingRev) crossed) = some (scanConfig remainingRev (current :: crossed)) := by
  cases remainingRev <;> rfl
theorem scan_finish (crossed : Word MachineCodeSymbol) :
    machine.stepConfig (scanConfig [] crossed) = some (gateConfig crossed) := by
  cases crossed <;> rfl
theorem scan_run_exact (remainingRev crossed : Word MachineCodeSymbol) :
    machine.runConfigExact? (remainingRev.length + 1) (scanConfig remainingRev crossed) = some
        (gateConfig (List.append remainingRev.reverse crossed)) := by
  induction remainingRev generalizing crossed with
  | nil =>
      exact scan_finish crossed
  | cons current remainingRev ih =>
      change machine.runConfigExact? ((remainingRev.length + 1) + 1) (scanConfig (current :: remainingRev) crossed) = _
      rw [TuringMachine.runConfigExact?]
      rw [scan_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]
theorem run_exact (wordRev : Word MachineCodeSymbol) :
    machine.runConfigExact? (wordRev.length + 2) (startConfig wordRev) = some (gateConfig wordRev.reverse) := by
  change machine.runConfigExact? ((wordRev.length + 1) + 1) (startConfig wordRev) = _
  rw [TuringMachine.runConfigExact?]
  rw [start_step]
  simp only
  simpa using scan_run_exact wordRev ([] : Word MachineCodeSymbol)
theorem gateTape_normalizedOutput (word : Word MachineCodeSymbol) :
    Tape.normalizedOutput (gateTape word) = MachineCodeSymbol.header :: word := by
  cases word with
  | nil =>
      simp [gateTape, Tape.normalizedOutput, Tape.cells]
  | cons first rest =>
      simp [gateTape, Tape.normalizedOutput, Tape.cells, Function.comp_def]
end PrependHeader

namespace EmptyInputSuffix
def suffix {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Word MachineCodeSymbol :=
  List.append (MachineDescription.encodeNat M.start.val) [ MachineCodeSymbol.done
    , MachineCodeSymbol.done , MachineCodeSymbol.done , Frame.callerTag ]
def body {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat) : Word MachineCodeSymbol :=
  List.append (MachineDescription.encodeNat fuel) (suffix M)
theorem fuel_suffix_eq_initial_protected_tail {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (fuel : Nat) :
    List.append (MachineDescription.encodeNat fuel) (suffix M) = (Frame.protectedWord
        (Layout.initial M ([] : Word MachineCodeSymbol) fuel) []).tail := by
  rw [Layout.initial_empty_eq]
  simp [suffix, Frame.protectedWord, Layout.encodeAppend, encodeOptionalCodeSymbolsAppend,
    encodeOptionalCodeSymbolsPayloadAppend, encodeOptionalCodeSymbolAppend,
    optionalCodeSymbolTag, MachineDescription.encodeNat, MachineDescription.encodeNatAppend]
theorem body_eq_initial_protected_tail {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (fuel : Nat) : body M fuel =
      (Frame.protectedWord (Layout.initial M ([] : Word MachineCodeSymbol) fuel) []).tail := by
  exact fuel_suffix_eq_initial_protected_tail M fuel
theorem writer_leftRev_eq_body_reverse {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (fuel : Nat) :
    List.append (suffix M).reverse (MachineDescription.encodeNat fuel).reverse = (body M fuel).reverse := by
  simp [body, List.reverse_append]
end EmptyInputSuffix


namespace SeparatorRewind

inductive Control where
  | start
  | scan
  | gate
deriving DecidableEq

namespace Control
def elems : List Control := [.start, .scan, .gate]
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control <;> simp [elems]
end Control
def transition : Control -> Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control)
  | .start, cell => some (cell, Direction.left, .scan)
  | .scan, some symbol =>
      some (some symbol, Direction.left, .scan)
  | .scan, none => some (none, Direction.right, .gate)
  | .gate, _ => none
def machine : TuringMachine MachineCodeSymbol Control where
  start := .start
  halt := .gate
  transition := transition
  statesFinite := Control.finite
end SeparatorRewind

namespace InsertOneWithBoundary
def cursorTape (leftCells : List (Option MachineCodeSymbol)) (rest : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := leftCells
        head := none
        right := [] }
  | first :: suffix =>
      { left := leftCells
        head := some first
        right := suffix.map some }
end InsertOneWithBoundary

namespace NonemptyRightRegion
def cellWord (symbol : MachineCodeSymbol) : Word MachineCodeSymbol :=
  encodeOptionalCodeSymbolAppend (some symbol) []
def region (processed : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  encodeOptionalCodeSymbolsAppend (processed.map some) [Frame.callerTag]
theorem region_nil : region [] = [MachineCodeSymbol.done, Frame.callerTag] := by
  rfl
theorem region_cons (symbol : MachineCodeSymbol) (processed : Word MachineCodeSymbol) :
    region (symbol :: processed) = MachineCodeSymbol.tick :: List.append (MachineDescription.encodeNat processed.length)
          (List.append (cellWord symbol) (encodeOptionalCodeSymbolsPayloadAppend
              (processed.map some) [Frame.callerTag])) := by
  simp [region, cellWord, encodeOptionalCodeSymbolsAppend,
    encodeOptionalCodeSymbolsPayloadAppend, encodeOptionalCodeSymbolAppend,
    MachineDescription.encodeNatAppend, MachineDescription.encodeNat]
theorem cellWord_eq_ticks_done (symbol : MachineCodeSymbol) : cellWord symbol = List.append
        (List.replicate (codeSymbolTag symbol + 1) MachineCodeSymbol.tick) [MachineCodeSymbol.done] := by
  cases symbol <;>
    simp [cellWord, encodeOptionalCodeSymbolAppend, optionalCodeSymbolTag, codeSymbolTag,
      MachineDescription.encodeNatAppend, MachineDescription.encodeNat]
theorem cellWord_ne_nil (symbol : MachineCodeSymbol) : cellWord symbol ≠ [] := by
  rw [cellWord_eq_ticks_done]
  intro hnil
  have hlength := congrArg List.length hnil
  simp at hlength
theorem cellWord_length_le_ten (symbol : MachineCodeSymbol) : (cellWord symbol).length ≤ 10 := by
  cases symbol <;> decide
theorem region_ne_nil (processed : Word MachineCodeSymbol) : region processed ≠ [] := by
  cases processed with
  | nil => simp [region_nil]
  | cons symbol rest =>
      rw [region_cons]
      simp
end NonemptyRightRegion

end InitialMaterializer
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
