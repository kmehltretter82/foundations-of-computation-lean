import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Driver.Witnesses
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.Serialized

set_option doc.verso true

/-!
# Product protected-frame handoff

Erase a completed left probe frame through its reserved caller tag, then expose
the protected right probe frame modulo tape-window equivalence.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductHandoff

inductive Control where
  | scan
  | gate
deriving DecidableEq

namespace Control

def finite : Foundation.FiniteType Control where
  elems := [.scan, .gate]
  complete := by
    intro control
    cases control <;> simp

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .scan, some symbol =>
      if symbol = Frame.callerTag then
        some (none, Direction.right, .gate)
      else
        some (none, Direction.right, .scan)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .scan
  halt := .gate
  transition := transition
  statesFinite := Control.finite

def scanTape
    (leftPad : List (Option MachineCodeSymbol))
    (body callerData : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match body with
  | [] =>
      { left := leftPad
        head := some Frame.callerTag
        right := callerData.map some }
  | current :: rest =>
      { left := leftPad
        head := some current
        right := (rest ++ Frame.callerTag :: callerData).map some }

def scanConfig
    (leftPad : List (Option MachineCodeSymbol))
    (body callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .scan
  tape := scanTape leftPad body callerData

def gateTape
    (leftPad : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.right
    (Tape.write none (scanTape leftPad [] callerData))

def gateConfig
    (leftPad : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .gate
  tape := gateTape leftPad callerData

def erasedLeft
    (body : Word MachineCodeSymbol)
    (leftPad : List (Option MachineCodeSymbol)) :
    List (Option MachineCodeSymbol) :=
  match body with
  | [] => leftPad
  | _ :: rest => erasedLeft rest (none :: leftPad)

theorem scan_step
    (current : MachineCodeSymbol)
    (rest callerData : Word MachineCodeSymbol)
    (leftPad : List (Option MachineCodeSymbol))
    (hcurrent : current ≠ Frame.callerTag) :
    machine.stepConfig (scanConfig leftPad (current :: rest) callerData) =
      some (scanConfig (none :: leftPad) rest callerData) := by
  cases rest <;>
    simp [TuringMachine.stepConfig, machine, transition, scanConfig,
      scanTape, Tape.read, Tape.write, Tape.move, Tape.moveRight,
      hcurrent]

theorem scan_finish
    (callerData : Word MachineCodeSymbol)
    (leftPad : List (Option MachineCodeSymbol)) :
    machine.stepConfig (scanConfig leftPad [] callerData) =
      some (gateConfig leftPad callerData) := by
  simp [TuringMachine.stepConfig, machine, transition, scanConfig,
    scanTape, gateConfig, gateTape, Tape.read]

theorem run_exact
    (body callerData : Word MachineCodeSymbol)
    (leftPad : List (Option MachineCodeSymbol))
    (hfree : ¬ List.Mem Frame.callerTag body) :
    machine.runConfigExact? (body.length + 1)
        (scanConfig leftPad body callerData) =
      some (gateConfig (erasedLeft body leftPad) callerData) := by
  induction body generalizing leftPad with
  | nil =>
      exact scan_finish callerData leftPad
  | cons current rest ih =>
      have hcurrent : current ≠ Frame.callerTag := by
        intro heq
        apply hfree
        subst current
        exact List.Mem.head _
      have hrest : ¬ List.Mem Frame.callerTag rest := by
        intro hmem
        exact hfree (List.Mem.tail current hmem)
      change machine.runConfigExact? ((rest.length + 1) + 1)
          (scanConfig leftPad (current :: rest) callerData) = _
      rw [TuringMachine.runConfigExact?]
      rw [scan_step current rest callerData leftPad hcurrent]
      simp only
      exact ih (none :: leftPad) hrest

theorem erasedLeft_dropTrailingNone
    (body : Word MachineCodeSymbol)
    (leftPad : List (Option MachineCodeSymbol))
    (hpad : Tape.dropTrailingNone leftPad = []) :
    Tape.dropTrailingNone (erasedLeft body leftPad) = [] := by
  induction body generalizing leftPad with
  | nil => exact hpad
  | cons current rest ih =>
      apply ih (none :: leftPad)
      simp [Tape.dropTrailingNone_cons, hpad]

theorem gateTape_equiv_input
    (body callerData : Word MachineCodeSymbol) :
    Tape.Equiv
      (gateTape (erasedLeft body []) callerData)
      (Tape.input callerData) := by
  have hpad :
      Tape.dropTrailingNone (erasedLeft body []) = [] :=
    erasedLeft_dropTrailingNone body [] rfl
  cases callerData <;>
    simp [gateTape, scanTape, Tape.input, Tape.blank, Tape.move,
      Tape.moveRight, Tape.write, Tape.Equiv, hpad,
      Tape.dropTrailingNone, Tape.dropTrailingNone_cons]

def NoCallerTag (word : Word MachineCodeSymbol) : Prop :=
  ¬ List.Mem Frame.callerTag word

theorem noCallerTag_encodeNat
    (n : Nat) :
    NoCallerTag (MachineDescription.encodeNat n) := by
  induction n with
  | zero =>
      intro hmem
      exact nomatch hmem
  | succ n ih =>
      intro hmem
      cases hmem with
      | tail _ htail => exact ih htail

theorem noCallerTag_encodeNatAppend
    (n : Nat) (suffix : Word MachineCodeSymbol)
    (hsuffix : NoCallerTag suffix) :
    NoCallerTag (MachineDescription.encodeNatAppend n suffix) := by
  intro hmem
  rcases List.mem_append.mp hmem with hnat | hsuffixMem
  · exact noCallerTag_encodeNat n hnat
  · exact hsuffix hsuffixMem

theorem noCallerTag_encodeOptionalCodeSymbolAppend
    (cell : Option MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol)
    (hsuffix : NoCallerTag suffix) :
    NoCallerTag (encodeOptionalCodeSymbolAppend cell suffix) := by
  exact noCallerTag_encodeNatAppend (optionalCodeSymbolTag cell)
    suffix hsuffix

theorem noCallerTag_encodeOptionalCodeSymbolsPayloadAppend
    (cells : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol)
    (hsuffix : NoCallerTag suffix) :
    NoCallerTag
      (encodeOptionalCodeSymbolsPayloadAppend cells suffix) := by
  induction cells with
  | nil => exact hsuffix
  | cons cell rest ih =>
      exact noCallerTag_encodeOptionalCodeSymbolAppend cell _ ih

theorem noCallerTag_encodeOptionalCodeSymbolsAppend
    (cells : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol)
    (hsuffix : NoCallerTag suffix) :
    NoCallerTag (encodeOptionalCodeSymbolsAppend cells suffix) := by
  exact noCallerTag_encodeNatAppend cells.length _
    (noCallerTag_encodeOptionalCodeSymbolsPayloadAppend cells suffix
      hsuffix)

theorem noCallerTag_layoutEncode
    {stateCount : Nat} (L : Layout stateCount) :
    NoCallerTag (Layout.encode L) := by
  cases L with
  | mk fuel state left head right =>
      unfold Layout.encode Layout.encodeAppend
      intro hmem
      cases hmem with
      | tail _ htail =>
          have hempty : NoCallerTag ([] : Word MachineCodeSymbol) := by
            intro h
            exact nomatch h
          exact noCallerTag_encodeNatAppend fuel _
            (noCallerTag_encodeNatAppend state.val _
              (noCallerTag_encodeOptionalCodeSymbolsAppend left _
                (noCallerTag_encodeOptionalCodeSymbolAppend head _
                  (noCallerTag_encodeOptionalCodeSymbolsAppend right []
                    hempty)))) htail

theorem layoutEncodeAppend_eq_append
    {stateCount : Nat} (L : Layout stateCount)
    (suffix : Word MachineCodeSymbol) :
    Layout.encodeAppend L suffix =
      List.append (Layout.encode L) suffix := by
  cases L with
  | mk fuel state left head right =>
      simp only [Layout.encode, Layout.encodeAppend,
        SerializedFieldComposer.encodeOptionalCodeSymbolsAppend_eq_append,
        SerializedFieldComposer.encodeOptionalCodeSymbolAppend_eq_append,
        MachineDescription.encodeNatAppend]
      simp [List.append_assoc]

theorem protectedWord_eq_layoutEncode_caller
    {stateCount : Nat} (L : Layout stateCount)
    (callerData : Word MachineCodeSymbol) :
    Frame.protectedWord L callerData =
      List.append (Layout.encode L) (Frame.callerTag :: callerData) := by
  unfold Frame.protectedWord
  exact layoutEncodeAppend_eq_append L (Frame.callerTag :: callerData)

theorem layoutEncode_ne_nil
    {stateCount : Nat} (L : Layout stateCount) :
    Layout.encode L ≠ [] := by
  cases L
  intro h
  cases h

theorem scanTape_nil_eq_input
    (body callerData : Word MachineCodeSymbol)
    (hbody : body ≠ []) :
    scanTape [] body callerData =
      Tape.input (List.append body (Frame.callerTag :: callerData)) := by
  cases body with
  | nil => contradiction
  | cons current rest => rfl

theorem run_from_representation
    {stateCount : Nat}
    (callerData : Word MachineCodeSymbol)
    (F : SerializedFieldComposer.CarriedStateFrame.LoopFrame stateCount)
    (T : Tape MachineCodeSymbol)
    (hrep :
      RelationalDriverInduction.Represents callerData 0 F T) :
    let L :=
      (SerializedFieldComposer.CarriedStateFrame.withFuel 0 F).physicalFrame
    exists endpoint : TuringMachine.Configuration MachineCodeSymbol Control,
      machine.runConfigExact? ((Layout.encode L).length + 1)
          { state := .scan, tape := T } = some endpoint ∧
        endpoint.state = .gate ∧
        Tape.Equiv endpoint.tape (Tape.input callerData) := by
  let L :=
    (SerializedFieldComposer.CarriedStateFrame.withFuel 0 F).physicalFrame
  have hcanonical :=
    run_exact (Layout.encode L) callerData []
      (noCallerTag_layoutEncode L)
  have hsourceTape :
      (scanConfig [] (Layout.encode L) callerData).tape =
        Tape.input (Frame.protectedWord L callerData) := by
    rw [protectedWord_eq_layoutEncode_caller]
    exact scanTape_nil_eq_input (Layout.encode L) callerData
      (layoutEncode_ne_nil L)
  have hsourceEquiv :
      Tape.Equiv
        (scanConfig [] (Layout.encode L) callerData).tape T := by
    rw [hsourceTape]
    exact Tape.Equiv.symm hrep
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hcanonical hsourceEquiv with
    ⟨endpoint, hrun, hstate, htargetEquiv⟩
  refine ⟨endpoint, ?_, hstate, ?_⟩
  · simpa [scanConfig] using hrun
  · exact Tape.Equiv.trans (Tape.Equiv.symm htargetEquiv)
      (gateTape_equiv_input (Layout.encode L) callerData)

end ProductHandoff
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC

