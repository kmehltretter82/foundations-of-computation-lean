import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Handoff
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseRetarget

set_option doc.verso true

/-!
# Product probe assembly

Retarget a concrete prefix materializer, two cyclic exact-fuel probes, and the
protected-frame handoff into one finite control space.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductAssembly

abbrev Control
    (materializerState : Type)
    (leftCount rightCount : Nat)
    (leftUpdateState rightUpdateState : Type) :=
  Sum materializerState
    (Sum (CyclicDriverIntegration.Control leftCount leftUpdateState)
      (Sum ProductHandoff.Control
        (CyclicDriverIntegration.Control rightCount rightUpdateState)))

def materializerControl
    {materializerState : Type}
    {leftCount rightCount : Nat}
    {leftUpdateState rightUpdateState : Type}
    (state : materializerState) :
    Control materializerState leftCount rightCount
      leftUpdateState rightUpdateState :=
  .inl state

def leftControl
    {materializerState : Type}
    {leftCount rightCount : Nat}
    {leftUpdateState rightUpdateState : Type}
    (state : CyclicDriverIntegration.Control leftCount leftUpdateState) :
    Control materializerState leftCount rightCount
      leftUpdateState rightUpdateState :=
  .inr (.inl state)

def handoffControl
    {materializerState : Type}
    {leftCount rightCount : Nat}
    {leftUpdateState rightUpdateState : Type}
    (state : ProductHandoff.Control) :
    Control materializerState leftCount rightCount
      leftUpdateState rightUpdateState :=
  .inr (.inr (.inl state))

def rightControl
    {materializerState : Type}
    {leftCount rightCount : Nat}
    {leftUpdateState rightUpdateState : Type}
    (state : CyclicDriverIntegration.Control rightCount rightUpdateState) :
    Control materializerState leftCount rightCount
      leftUpdateState rightUpdateState :=
  .inr (.inr (.inr state))

def embedMaterializer
    {materializerState : Type} [DecidableEq materializerState]
    {leftCount rightCount : Nat}
    {leftUpdateState rightUpdateState : Type}
    (materializer : TuringMachine MachineCodeSymbol materializerState)
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (state : materializerState) :
    Control materializerState leftCount rightCount
      leftUpdateState rightUpdateState :=
  if state = materializer.halt then
    leftControl (.gate (.header left.start))
  else
    materializerControl state

def embedLeft
    {materializerState : Type}
    {leftCount rightCount : Nat}
    {leftUpdateState rightUpdateState : Type} :
    CyclicDriverIntegration.Control leftCount leftUpdateState ->
      Control materializerState leftCount rightCount
        leftUpdateState rightUpdateState
  | .accept => handoffControl .scan
  | state => leftControl state

def embedHandoff
    {materializerState : Type}
    {leftCount rightCount : Nat}
    {leftUpdateState rightUpdateState : Type}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) :
    ProductHandoff.Control ->
      Control materializerState leftCount rightCount
        leftUpdateState rightUpdateState
  | .scan => handoffControl .scan
  | .gate => rightControl (.gate (.header right.start))

def embedRight
    {materializerState : Type}
    {leftCount rightCount : Nat}
    {leftUpdateState rightUpdateState : Type} :
    CyclicDriverIntegration.Control rightCount rightUpdateState ->
      Control materializerState leftCount rightCount
        leftUpdateState rightUpdateState :=
  rightControl

def mapAction
    (embed : innerState -> outerState) :
    Option (Option MachineCodeSymbol × Direction × innerState) ->
      Option (Option MachineCodeSymbol × Direction × outerState)
  | none => none
  | some (write, direction, target) =>
      some (write, direction, embed target)

def transition
    {materializerState : Type} [DecidableEq materializerState]
    {leftCount rightCount : Nat}
    {leftUpdateState rightUpdateState : Type}
    [DecidableEq leftUpdateState] [DecidableEq rightUpdateState]
    (materializer : TuringMachine MachineCodeSymbol materializerState)
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftKernel :
      CyclicDriverIntegration.UpdateKernel leftCount leftUpdateState)
    (rightKernel :
      CyclicDriverIntegration.UpdateKernel rightCount rightUpdateState) :
    Control materializerState leftCount rightCount
        leftUpdateState rightUpdateState ->
      Option MachineCodeSymbol ->
      Option
        (Option MachineCodeSymbol × Direction ×
          Control materializerState leftCount rightCount
            leftUpdateState rightUpdateState)
  | .inl state, read =>
      mapAction (embedMaterializer materializer left)
        (materializer.transition state read)
  | .inr (.inl state), read =>
      mapAction embedLeft
        (CyclicDriverIntegration.transition left leftKernel state read)
  | .inr (.inr (.inl state)), read =>
      mapAction (embedHandoff right)
        (ProductHandoff.transition state read)
  | .inr (.inr (.inr state)), read =>
      mapAction embedRight
        (CyclicDriverIntegration.transition right rightKernel state read)

def machine
    {materializerState : Type} [DecidableEq materializerState]
    {leftCount rightCount : Nat}
    {leftUpdateState rightUpdateState : Type}
    [DecidableEq leftUpdateState] [DecidableEq rightUpdateState]
    (materializer : TuringMachine MachineCodeSymbol materializerState)
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftKernel :
      CyclicDriverIntegration.UpdateKernel leftCount leftUpdateState)
    (rightKernel :
      CyclicDriverIntegration.UpdateKernel rightCount rightUpdateState) :
    TuringMachine MachineCodeSymbol
      (Control materializerState leftCount rightCount
        leftUpdateState rightUpdateState) where
  start := embedMaterializer materializer left materializer.start
  halt := rightControl (.accept)
  transition := transition materializer left right leftKernel rightKernel
  statesFinite :=
    Foundation.FiniteType.sum materializer.statesFinite
      (Foundation.FiniteType.sum
        (CyclicDriverIntegration.Control.finite
          leftCount leftKernel.finite)
        (Foundation.FiniteType.sum ProductHandoff.Control.finite
          (CyclicDriverIntegration.Control.finite
            rightCount rightKernel.finite)))

end ProductAssembly
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC

