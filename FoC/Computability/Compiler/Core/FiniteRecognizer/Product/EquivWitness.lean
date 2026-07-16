import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Construction
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Input
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.Basic

set_option doc.verso true

/-!
# Product equivalence-aware schedules

Compositional schedule currency for the product-prefix materializer.
Each schedule keeps its deterministic physical endpoint while relating that
endpoint to a clean canonical configuration through
{name (full := FoC.Computability.Tape.Equiv)}`Tape.Equiv`.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductEquivWitness

open ProductComposition

abbrev Config (state : Type) :=
  TuringMachine.Configuration MachineCodeSymbol state

/-- An exact schedule whose physical endpoint represents a canonical target. -/
structure RunsToEquiv
    {state : Type} [DecidableEq state]
    (M : TuringMachine MachineCodeSymbol state)
    (source canonical : Config state) where
  endpoint : Config state
  steps : Nat
  run_exact : M.runConfigExact? steps source = some endpoint
  endpoint_state : endpoint.state = canonical.state
  canonical_tape_equiv : Tape.Equiv canonical.tape endpoint.tape

namespace RunsToEquiv

/-- Regard an exact run as an equivalence-aware schedule. -/
def exact
    {state : Type} [DecidableEq state]
    {M : TuringMachine MachineCodeSymbol state}
    {source target : Config state}
    (steps : Nat)
    (hrun : M.runConfigExact? steps source = some target) :
    RunsToEquiv M source target :=
  { endpoint := target
    steps := steps
    run_exact := hrun
    endpoint_state := rfl
    canonical_tape_equiv := Tape.Equiv.refl _ }

/-- Compose exact runs, transporting the second one to the first physical
endpoint rather than demanding literal equality with the canonical seam. -/
def trans
    {state : Type} [DecidableEq state]
    {M : TuringMachine MachineCodeSymbol state}
    {source middle target : Config state}
    (first : RunsToEquiv M source middle)
    (second : RunsToEquiv M middle target) :
    RunsToEquiv M source target := by
  rcases first with
    ⟨⟨firstState, firstTape⟩, firstSteps, firstRun, firstStateEq,
      firstTapeEquiv⟩
  dsimp only at firstStateEq firstTapeEquiv firstRun
  subst firstState
  let firstEndpoint : Config state :=
    { state := middle.state, tape := firstTape }
  let result := M.runConfigExact? second.steps firstEndpoint
  have hexists : exists endpoint,
      result = some endpoint ∧
      endpoint.state = second.endpoint.state ∧
      Tape.Equiv second.endpoint.tape endpoint.tape := by
    rcases
        TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
          second.run_exact firstTapeEquiv with
      ⟨endpoint, hrun, hstate, htape⟩
    refine ⟨endpoint, ?_, hstate, htape⟩
    simpa [result, firstEndpoint] using hrun
  have hsome : result.isSome := by
    rcases hexists with ⟨endpoint, hrun, _, _⟩
    simp [hrun]
  let endpoint := result.get hsome
  have hrunSecond : result = some endpoint :=
    (Option.some_get hsome).symm
  have hendpointState : endpoint.state = target.state := by
    rcases hexists with ⟨other, hrun, hstate, _⟩
    have heq : other = endpoint := by
      exact Option.some.inj (hrun.symm.trans hrunSecond)
    subst other
    exact hstate.trans second.endpoint_state
  have htargetTape : Tape.Equiv target.tape endpoint.tape := by
    rcases hexists with ⟨other, hrun, _, htape⟩
    have heq : other = endpoint := by
      exact Option.some.inj (hrun.symm.trans hrunSecond)
    subst other
    exact Tape.Equiv.trans second.canonical_tape_equiv htape
  refine
    { endpoint := endpoint
      steps := firstSteps + second.steps
      run_exact := ?_
      endpoint_state := hendpointState
      canonical_tape_equiv := htargetTape }
  rw [InitialMaterializer.ExactRun.append, firstRun]
  exact hrunSecond

end RunsToEquiv

theorem computes_of_runConfigExact?_eq_some
    {state symbol : Type}
    {M : TuringMachine symbol state}
    {steps : Nat}
    {source target : TuringMachine.Configuration symbol state}
    (hrun : M.runConfigExact? steps source = some target) :
    TuringMachine.Computes M source target := by
  exact TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrun)

theorem config_eq_of_state_tape_eq
    {symbol state : Type}
    {first second : TuringMachine.Configuration symbol state}
    (hstate : first.state = second.state)
    (htape : first.tape = second.tape) : first = second := by
  cases first with
  | mk firstState firstTape =>
      cases second with
      | mk secondState secondTape =>
          cases hstate
          cases htape
          rfl

theorem represents_pairTarget_of_equiv
    {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat)
    (targetTape : Tape MachineCodeSymbol)
    (htarget : Tape.Equiv
      (Tape.input
        (ProductInput.pairTargetWord
          left right input leftFuel rightFuel))
      targetTape) :
    RelationalDriverInduction.Represents
      (Frame.protectedWord (Layout.initial right input rightFuel) [])
      leftFuel
      (SerializedFieldComposer.CarriedStateFrame.ofParsed
        (Layout.initial left input leftFuel))
      targetTape := by
  unfold RelationalDriverInduction.Represents
  simpa [ProductInput.pairTargetWord, ProductInput.pairCallerData,
    SerializedFieldComposer.CarriedStateFrame.withFuel,
    SerializedFieldComposer.CarriedStateFrame.ofParsed,
    SerializedFieldComposer.FuelDecrementMachine.withFuel,
    Layout.initial, Layout.ofConfig] using Tape.Equiv.symm htarget

def pairCanonicalTarget
    {materializerState : Type} [DecidableEq materializerState]
    {leftCount rightCount : Nat}
    (materializer : TuringMachine MachineCodeSymbol materializerState)
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) : Config materializerState :=
  { state := materializer.halt
    tape := Tape.input
      (ProductInput.pairTargetWord left right input leftFuel rightFuel) }

/-- Turn a final equivalence-aware schedule into the direct product-prefix
witness consumed by product composition. -/
def pairPrefixWitness_of_runsToEquiv
    {materializerState : Type} [DecidableEq materializerState]
    {leftCount rightCount : Nat}
    (materializer : TuringMachine MachineCodeSymbol materializerState)
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat)
    (hdisabled : TuringMachine.HaltingTransitionsDisabled materializer)
    (schedule : RunsToEquiv materializer
      (TuringMachine.initial materializer
        (GeneratedCode.nestedStageCode input rightFuel leftFuel))
      (pairCanonicalTarget materializer left right
        input leftFuel rightFuel)) :
    PairPrefixWitness materializer left right input leftFuel rightFuel := by
  refine
    { source := TuringMachine.initial materializer
        (GeneratedCode.nestedStageCode input rightFuel leftFuel)
      targetTape := schedule.endpoint.tape
      haltingTransitionsDisabled := hdisabled
      run := ?_
      leftRepresents := represents_pairTarget_of_equiv
        left right input leftFuel rightFuel schedule.endpoint.tape
          schedule.canonical_tape_equiv }
  have hrun := computes_of_runConfigExact?_eq_some schedule.run_exact
  have hstate : schedule.endpoint.state = materializer.halt := by
    simpa [pairCanonicalTarget] using schedule.endpoint_state
  have hendpoint : schedule.endpoint =
      ({ state := materializer.halt, tape := schedule.endpoint.tape } :
        Config materializerState) :=
    config_eq_of_state_tape_eq hstate rfl
  rw [hendpoint] at hrun
  exact hrun

/-- A schedule for every generated input supplies the complete constructor
contract without any strict intermediate configuration seams. -/
theorem pairPrefixWitnesses_of_runsToEquiv
    {materializerState : Type} [DecidableEq materializerState]
    {leftCount rightCount : Nat}
    (materializer : TuringMachine MachineCodeSymbol materializerState)
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (hdisabled : TuringMachine.HaltingTransitionsDisabled materializer)
    (schedules : forall input leftFuel rightFuel,
      RunsToEquiv materializer
        (TuringMachine.initial materializer
          (GeneratedCode.nestedStageCode input rightFuel leftFuel))
        (pairCanonicalTarget materializer left right
          input leftFuel rightFuel)) :
    ProductConstruction.PairPrefixWitnesses materializer left right := by
  intro input leftFuel rightFuel
  refine ⟨pairPrefixWitness_of_runsToEquiv materializer left right
    input leftFuel rightFuel hdisabled
      (schedules input leftFuel rightFuel), rfl⟩

end ProductEquivWitness
end StrictProbe
end ExactFuel
end FiniteRecognizer
end Computability
end FoC
