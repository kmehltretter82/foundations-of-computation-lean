import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.Layout
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StageProgram.Composition
import FoC.Computability.MachineBuilder.TapeCode

set_option doc.verso true

/-!
# Protected exact-fuel layout loop

Executable layout-fuel semantics together with the exact-empty-output
guardrail for finite realizers.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel

def layoutFuelLoopFrom {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Nat -> Layout stateCount -> Option (Layout stateCount)
  | 0, L => some L
  | fuel + 1, L =>
      match Layout.step M L with
      | none => none
      | some L' => layoutFuelLoopFrom M fuel L'

def layoutFuelLoopCode {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match Layout.decode stateCount tokens with
  | none => none
  | some (L, suffix) =>
      match suffix with
      | [] =>
          match layoutFuelLoopFrom M L.fuel L with
          | none => none
          | some final =>
              if final.state = M.halt then
                some ([] : Word MachineCodeSymbol)
              else
                none
      | _ :: _ => none

def layoutFuelLoopCodePrimitive {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    MachineDescription.TapeCodePrimitive where
  transform := layoutFuelLoopCode M

def LayoutFuelLoopDecodedExactOutputForwardSpec
    {stateCount : Nat}
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  forall tokens : Word MachineCodeSymbol,
  forall L : Layout stateCount,
    Layout.decode stateCount tokens = some (L, []) ->
      (TuringMachine.HaltsWithExactOutput runner tokens
          ([] : Word MachineCodeSymbol) <->
        Layout.accepts M L)

def LayoutFuelLoopDecodedExactOutputClosedSpec
    {stateCount : Nat}
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  forall tokens output : Word MachineCodeSymbol,
    TuringMachine.HaltsWithExactOutput runner tokens output ->
      exists L : Layout stateCount,
        Layout.decode stateCount tokens = some (L, []) /\
          output = ([] : Word MachineCodeSymbol) /\
          Layout.accepts M L

def LayoutFuelLoopDecodedExactOutputSpec
    {stateCount : Nat}
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  LayoutFuelLoopDecodedExactOutputForwardSpec runner M /\
    LayoutFuelLoopDecodedExactOutputClosedSpec runner M

def LayoutFuelLoopDecodedExactOutputPrimitiveConstruction
    {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : Prop :=
  exists runnerState : Type,
  exists runner : TuringMachine MachineCodeSymbol runnerState,
    LayoutFuelLoopDecodedExactOutputSpec runner M /\
      StageProgram.ExactOutputCanonicalSpec runner
        (layoutFuelLoopCodePrimitive M).transform /\
      TuringMachine.HaltingTransitionsDisabled runner

def FinStateLayoutFuelLoopDecodedExactOutputPrimitiveConstruction :
    Prop :=
  forall stateCount : Nat,
  forall M : TuringMachine MachineCodeSymbol (Fin stateCount),
    LayoutFuelLoopDecodedExactOutputPrimitiveConstruction M

private def layoutFuelLoopExactOutputCounterexampleMachine :
    TuringMachine MachineCodeSymbol (Fin 1) where
  start := 0
  halt := 0
  transition := fun _ _ => none
  statesFinite := Foundation.FiniteType.fin 1

private theorem layoutFuelLoopExactOutputCounterexampleMachine_haltsIn :
    TuringMachine.HaltsOnInputIn
      layoutFuelLoopExactOutputCounterexampleMachine 0
      ([] : Word MachineCodeSymbol) := by
  refine
    ⟨TuringMachine.initial layoutFuelLoopExactOutputCounterexampleMachine [],
      ?_, ?_⟩
  · exact TuringMachine.ComputesIn.zero _
  · rfl

/--
A layout recognizer cannot erase every encoded layout to the literal blank
tape. The encoded initial layout below is accepted but has nonempty context.
-/
theorem not_finStateLayoutFuelLoopDecodedExactOutputPrimitiveConstruction :
    ¬ FinStateLayoutFuelLoopDecodedExactOutputPrimitiveConstruction := by
  intro hconstruction
  rcases hconstruction 1 layoutFuelLoopExactOutputCounterexampleMachine with
    ⟨_state, runner, hspec, _hcanonical, _hstop⟩
  let L :=
    Layout.initial layoutFuelLoopExactOutputCounterexampleMachine
      ([] : Word MachineCodeSymbol) 0
  have hdecode : Layout.decode 1 (Layout.encode L) = some (L, []) :=
    Layout.decode_encode L
  have haccepts :
      Layout.accepts layoutFuelLoopExactOutputCounterexampleMachine L := by
    simpa [L] using
      (Layout.accepts_initial_iff_haltsOnInputIn
        layoutFuelLoopExactOutputCounterexampleMachine
        ([] : Word MachineCodeSymbol) 0).mpr
        layoutFuelLoopExactOutputCounterexampleMachine_haltsIn
  have hhalt :=
    (hspec.left (Layout.encode L) L hdecode).mpr haccepts
  apply
    TuringMachine.not_haltsWithExactOutput_empty_of_input_contextLength_pos
      (M := runner) (w := Layout.encode L) ?_ hhalt
  decide

end ExactFuel
end FiniteRecognizer
end Computability
end FoC
