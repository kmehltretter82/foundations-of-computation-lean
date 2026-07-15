import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseEmbedding
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Driver.CyclicMachine
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.Materializer
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.TwoBlankCompactor

set_option doc.verso true

/-!
# Exact-fuel stage-runner machine

The stage runner embeds the stage-input materializer, the nonempty-input
compactor, and the generic cyclic exact-fuel driver in one finite control
space.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace StageRunner


/-- The public stage machine embeds the complete materializer and cyclic
driver.  The two return states implement tape-equivalence-preserving bounces
at the nonempty materializer and compactor boundaries. -/
inductive Control {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (updateState : Type) where
  | materializer
      (inner : InitialMaterializer.FullMaterializerMachine.Control M)
  | nonemptyReturn
  | compactor
      (inner : StageInput.TwoBlankCompactor.Control)
  | compactorReturn
  | cyclic
      (inner : CyclicDriverIntegration.Control stateCount updateState)
deriving DecidableEq

namespace Control

def elems {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (updateFinite : Foundation.FiniteType updateState) :
    List (Control M updateState) :=
  List.append
    ((InitialMaterializer.FullMaterializerMachine.Control.finite M).elems.map
      Control.materializer)
    (List.append [.nonemptyReturn]
      (List.append
        (StageInput.TwoBlankCompactor.Control.finite.elems.map
          Control.compactor)
        (List.append [.compactorReturn]
          ((CyclicDriverIntegration.Control.finite
            stateCount updateFinite).elems.map
            Control.cyclic))))

def finite {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (updateFinite : Foundation.FiniteType updateState) :
    Foundation.FiniteType (Control M updateState) where
  elems := elems M updateFinite
  complete := by
    intro control
    cases control with
    | materializer inner =>
        have h :=
          (InitialMaterializer.FullMaterializerMachine.Control.finite M).complete
            inner
        simp [elems, h]
    | nonemptyReturn => simp [elems]
    | compactor inner =>
        have h :=
          StageInput.TwoBlankCompactor.Control.finite.complete
            inner
        simp [elems, h]
    | compactorReturn => simp [elems]
    | cyclic inner =>
        have h :=
          (CyclicDriverIntegration.Control.finite
            stateCount updateFinite).complete inner
        simp [elems, h]

end Control

def emptyEndpoint {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)} :
    InitialMaterializer.FullMaterializerMachine.Control M :=
  .emptyPrepend .gate

def nonemptyEndpoint {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)} :
    InitialMaterializer.FullMaterializerMachine.Control M :=
  .header .halt

def transition {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState) :
    Control M updateState -> Option MachineCodeSymbol ->
      Option
        (Option MachineCodeSymbol × Direction × Control M updateState)
  | .materializer inner, read =>
      if inner = emptyEndpoint then
        some
          (read, Direction.left,
            .cyclic (.gate (.header M.start)))
      else if inner = nonemptyEndpoint then
        some (read, Direction.right, .nonemptyReturn)
      else
        match InitialMaterializer.FullMaterializerMachine.transition
            M inner read with
        | none => none
        | some (write, direction, target) =>
            some (write, direction, .materializer target)
  | .nonemptyReturn, read =>
      some (read, Direction.left, .compactor .seek)
  | .compactor inner, read =>
      if inner =
          StageInput.TwoBlankCompactor.machine.halt then
        some (read, Direction.right, .compactorReturn)
      else
        match StageInput.TwoBlankCompactor.transition
            inner read with
        | none => none
        | some (write, direction, target) =>
            some (write, direction, .compactor target)
  | .compactorReturn, read =>
      some
        (read, Direction.left,
          .cyclic (.gate (.header M.start)))
  | .cyclic inner, read =>
      match CyclicDriverIntegration.transition M K inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .cyclic target)

def machine {stateCount : Nat} {updateState : Type}
    [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState) :
    TuringMachine MachineCodeSymbol (Control M updateState) where
  start := .materializer
    (InitialMaterializer.FullMaterializerMachine.machine M).start
  halt := .cyclic (CyclicDriverIntegration.machine M K).halt
  transition := transition M K
  statesFinite := Control.finite M K.finite

theorem machine_haltingTransitionsDisabled {stateCount : Nat}
    {updateState : Type} [DecidableEq updateState]
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (K : CyclicDriverIntegration.UpdateKernel stateCount updateState) :
    TuringMachine.HaltingTransitionsDisabled (machine M K) := by
  intro read
  rfl

def materializerConfig {stateCount : Nat} {updateState : Type}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (c : TuringMachine.Configuration MachineCodeSymbol
      (InitialMaterializer.FullMaterializerMachine.Control M)) :
    TuringMachine.Configuration MachineCodeSymbol (Control M updateState) :=
  TuringMachine.PhaseEmbedding.liftConfig Control.materializer c

def compactorConfig {stateCount : Nat} {updateState : Type}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (c : TuringMachine.Configuration MachineCodeSymbol
      StageInput.TwoBlankCompactor.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control M updateState) :=
  TuringMachine.PhaseEmbedding.liftConfig Control.compactor c

def cyclicConfig {stateCount : Nat} {updateState : Type}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (c : TuringMachine.Configuration MachineCodeSymbol
      (CyclicDriverIntegration.Control stateCount updateState)) :
    TuringMachine.Configuration MachineCodeSymbol (Control M updateState) :=
  TuringMachine.PhaseEmbedding.liftConfig Control.cyclic c

end StageRunner
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
