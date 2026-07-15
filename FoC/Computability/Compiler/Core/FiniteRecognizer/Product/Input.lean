import FoC.Computability.Compiler.Core.FiniteRecognizer.GeneratedCode
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.Materializer
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.Serialized

set_option doc.verso true

/-!
# Product pair input shapes

Decode the two unary fuel fields in generated order and describe the nested
protected-frame target consumed by the two exact-fuel probes.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductInput

def pairCallerData {rightN : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightN))
    (input : Word MachineCodeSymbol) (rightFuel : Nat) :
    Word MachineCodeSymbol :=
  Frame.protectedWord (Layout.initial right input rightFuel) []

def pairTargetWord {leftN rightN : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN))
    (input : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) : Word MachineCodeSymbol :=
  Frame.protectedWord (Layout.initial left input leftFuel)
    (pairCallerData right input rightFuel)

theorem nestedStageCode_eq_two_fuels
    (input : Word MachineCodeSymbol)
    (rightFuel leftFuel : Nat) :
    GeneratedCode.nestedStageCode input rightFuel leftFuel =
      MachineDescription.encodeNatAppend leftFuel
        (MachineDescription.encodeNatAppend rightFuel input) := by
  rfl

theorem pairTargetWord_decode_left {leftN rightN : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN))
    (input : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    Layout.decode leftN
        (pairTargetWord left right input leftFuel rightFuel) =
      some
        (Layout.initial left input leftFuel,
          Frame.callerTag :: pairCallerData right input rightFuel) := by
  exact Layout.decode_encodeAppend _ _

theorem pairCallerData_decode_right {rightN : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightN))
    (input : Word MachineCodeSymbol) (rightFuel : Nat) :
    Layout.decode rightN (pairCallerData right input rightFuel) =
      some (Layout.initial right input rightFuel, [Frame.callerTag]) := by
  exact Layout.decode_encodeAppend _ _

theorem pairTargetWord_empty {leftN rightN : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN))
    (leftFuel rightFuel : Nat) :
    pairTargetWord left right [] leftFuel rightFuel =
      Frame.protectedWord (Layout.initial left [] leftFuel)
        (Frame.protectedWord (Layout.initial right [] rightFuel) []) := by
  rfl

theorem pairTargetWord_nonempty {leftN rightN : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftN))
    (right : TuringMachine MachineCodeSymbol (Fin rightN))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    pairTargetWord left right (headSymbol :: rest)
        leftFuel rightFuel =
      Frame.protectedWord
        (Layout.initial left (headSymbol :: rest) leftFuel)
        (Frame.protectedWord
          (Layout.initial right (headSymbol :: rest) rightFuel) []) := by
  rfl

theorem emptyBody_append_callerData {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat) (callerData : Word MachineCodeSymbol) :
    MachineCodeSymbol.header ::
        List.append (InitialMaterializer.EmptyInputSuffix.body M fuel)
          callerData =
      Frame.protectedWord
        (Layout.initial M ([] : Word MachineCodeSymbol) fuel)
        callerData := by
  rw [Layout.initial_empty_eq]
  simp [InitialMaterializer.EmptyInputSuffix.body,
    InitialMaterializer.EmptyInputSuffix.suffix,
    Frame.protectedWord, Layout.encodeAppend,
    encodeOptionalCodeSymbolsAppend,
    encodeOptionalCodeSymbolsPayloadAppend,
    encodeOptionalCodeSymbolAppend, optionalCodeSymbolTag,
    MachineDescription.encodeNat,
    MachineDescription.encodeNatAppend, List.append_assoc]

theorem nonemptyBody_append_callerData {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat) (headSymbol : MachineCodeSymbol)
    (rest callerData : Word MachineCodeSymbol) :
    MachineCodeSymbol.header ::
        List.append
          (InitialMaterializer.NonemptyFixedPrefix.body
            M fuel headSymbol rest)
          callerData =
      Frame.protectedWord
        (Layout.initial M (headSymbol :: rest) fuel) callerData := by
  rw [Layout.initial_cons_eq]
  simp [InitialMaterializer.NonemptyFixedPrefix.body,
    InitialMaterializer.NonemptyFixedPrefix.fixedPrefix,
    InitialMaterializer.NonemptyRightRegion.region,
    Frame.protectedWord, Layout.encodeAppend,
    encodeOptionalCodeSymbolsAppend,
    encodeOptionalCodeSymbolsPayloadAppend,
    encodeOptionalCodeSymbolAppend,
    MachineDescription.encodeNatAppend,
    MachineDescription.encodeNat, List.append_assoc]
  rw [SerializedFieldComposer.encodeOptionalCodeSymbolsPayloadAppend_eq_append
      (rest.map some) [Frame.callerTag],
    SerializedFieldComposer.encodeOptionalCodeSymbolsPayloadAppend_eq_append
      (rest.map some) (Frame.callerTag :: callerData)]
  simp

/-!
## Parsing both unary fields

This finite parser is intentionally independent of either simulated machine.
It reaches the first raw input symbol while leaving both unary encodings in
the physical left stack.  The order is outer/left first, inner/right second.
-/

namespace PairFuelParser

inductive Control where
  | outer
  | inner
  | gate
deriving DecidableEq

namespace Control

def elems : List Control := [.outer, .inner, .gate]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control <;> simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .outer, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .outer)
  | .outer, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .inner)
  | .inner, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .inner)
  | .inner, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .gate)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .outer
  halt := .gate
  transition := transition
  statesFinite := Control.finite

def config (control : Control)
    (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := control
  tape := SerializedShift.cursorTape leftRev rest

def sourceConfig (input : Word MachineCodeSymbol)
    (rightFuel leftFuel : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .outer []
    (GeneratedCode.nestedStageCode input rightFuel leftFuel)

def gateConfig (input : Word MachineCodeSymbol)
    (rightFuel leftFuel : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .gate
    (List.append (MachineDescription.encodeNat rightFuel).reverse
      (MachineDescription.encodeNat leftFuel).reverse)
    input

theorem outer_tick_step (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .outer leftRev
          (MachineCodeSymbol.tick :: suffix)) =
      some
        (config .outer (MachineCodeSymbol.tick :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem outer_done_step (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .outer leftRev
          (MachineCodeSymbol.done :: suffix)) =
      some
        (config .inner (MachineCodeSymbol.done :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem inner_tick_step (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .inner leftRev
          (MachineCodeSymbol.tick :: suffix)) =
      some
        (config .inner (MachineCodeSymbol.tick :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem inner_done_step (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .inner leftRev
          (MachineCodeSymbol.done :: suffix)) =
      some
        (config .gate (MachineCodeSymbol.done :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem outer_run (fuel : Nat)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (fuel + 1)
        (config .outer leftRev
          (MachineDescription.encodeNatAppend fuel suffix)) =
      some
        (config .inner
          (List.append (MachineDescription.encodeNat fuel).reverse
            leftRev)
          suffix) := by
  induction fuel generalizing leftRev with
  | zero =>
      exact outer_done_step leftRev suffix
  | succ fuel ih =>
      change
        machine.runConfigExact? ((fuel + 1) + 1)
          (config .outer leftRev
            (MachineCodeSymbol.tick ::
              MachineDescription.encodeNatAppend fuel suffix)) = _
      rw [TuringMachine.runConfigExact?]
      rw [outer_tick_step]
      simp only
      rw [ih]
      simp [MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc]

theorem inner_run (fuel : Nat)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (fuel + 1)
        (config .inner leftRev
          (MachineDescription.encodeNatAppend fuel suffix)) =
      some
        (config .gate
          (List.append (MachineDescription.encodeNat fuel).reverse
            leftRev)
          suffix) := by
  induction fuel generalizing leftRev with
  | zero =>
      exact inner_done_step leftRev suffix
  | succ fuel ih =>
      change
        machine.runConfigExact? ((fuel + 1) + 1)
          (config .inner leftRev
            (MachineCodeSymbol.tick ::
              MachineDescription.encodeNatAppend fuel suffix)) = _
      rw [TuringMachine.runConfigExact?]
      rw [inner_tick_step]
      simp only
      rw [ih]
      simp [MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc]

theorem run_exact (input : Word MachineCodeSymbol)
    (rightFuel leftFuel : Nat) :
    machine.runConfigExact? (leftFuel + 1 + (rightFuel + 1))
        (sourceConfig input rightFuel leftFuel) =
      some (gateConfig input rightFuel leftFuel) := by
  unfold sourceConfig gateConfig GeneratedCode.nestedStageCode
    GeneratedCode.stageCode
  rw [InitialMaterializer.ExactRun.append]
  rw [outer_run]
  simp only
  rw [inner_run]
  simp

end PairFuelParser

end ProductInput
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC

