import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Duplicator
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.RestagedEdits
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseEmbedding
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.HaltStoppedMachine

set_option doc.verso true

/-!
# Finite self-append runner

This module composes the existing collision-free source duplicator, a raw
one-cell gap compactor, and an arbitrary finite code-symbol runner.  On every
nonempty input {lit}`w`, the resulting machine halts exactly when the supplied
runner halts on {lit}`w ++ w`.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace SelfAppendRunner

open Languages
open FiniteRecognizer.ExactFuel.StrictProbe
open FiniteRecognizer.ExactFuel.StrictProbe.SerializedFieldComposer

inductive Control (runnerState : Type) where
  | duplicate (inner : ProductDuplicator.Control)
  | compact (inner : DeleteOneRestagedMachine.Control)
  | compactReturn
  | run (inner : runnerState)
deriving DecidableEq

namespace Control

def elems
    (runner : TuringMachine MachineCodeSymbol runnerState) :
    List (Control runnerState) :=
  List.append
    (ProductDuplicator.Control.finite.elems.map Control.duplicate)
    (List.append
      (DeleteOneRestagedMachine.Control.finite.elems.map Control.compact)
      (List.append [.compactReturn]
        (runner.statesFinite.elems.map Control.run)))

def finite
    (runner : TuringMachine MachineCodeSymbol runnerState) :
    Foundation.FiniteType (Control runnerState) where
  elems := elems runner
  complete := by
    intro control
    cases control with
    | duplicate inner =>
        have h := ProductDuplicator.Control.finite.complete inner
        simp [elems, h]
    | compact inner =>
        have h := DeleteOneRestagedMachine.Control.finite.complete inner
        simp [elems, h]
    | compactReturn => simp [elems]
    | run inner =>
        have h := runner.statesFinite.complete inner
        simp [elems, h]

end Control

def mapAction {source target : Type}
    (embed : source -> target) :
    Option (Option MachineCodeSymbol × Direction × source) ->
      Option (Option MachineCodeSymbol × Direction × target)
  | none => none
  | some (write, direction, state) =>
      some (write, direction, embed state)

def transition
    (runner : TuringMachine MachineCodeSymbol runnerState) :
    Control runnerState -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control runnerState)
  | .duplicate .halt, read =>
      some (read, Direction.left,
        .compact DeleteOneRestagedMachine.machine.start)
  | .duplicate inner, read =>
      mapAction Control.duplicate
        (ProductDuplicator.transition inner read)
  | .compact (.rewind .gate), read =>
      some (read, Direction.right, .compactReturn)
  | .compact inner, read =>
      mapAction Control.compact
        (DeleteOneRestagedMachine.transition inner read)
  | .compactReturn, read =>
      some (read, Direction.left, .run runner.start)
  | .run inner, read =>
      mapAction Control.run (runner.transition inner read)

def machine
    (runner : TuringMachine MachineCodeSymbol runnerState) :
    TuringMachine MachineCodeSymbol (Control runnerState) where
  start := .duplicate ProductDuplicator.machine.start
  halt := .run runner.halt
  transition := transition runner
  statesFinite := Control.finite runner

def duplicateConfig
    (configuration : TuringMachine.Configuration MachineCodeSymbol
      ProductDuplicator.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control runnerState) where
  state := .duplicate configuration.state
  tape := configuration.tape

def compactConfig
    (configuration : TuringMachine.Configuration MachineCodeSymbol
      DeleteOneRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control runnerState) where
  state := .compact configuration.state
  tape := configuration.tape

def runnerConfig
    (configuration : TuringMachine.Configuration MachineCodeSymbol
      runnerState) :
    TuringMachine.Configuration MachineCodeSymbol (Control runnerState) where
  state := .run configuration.state
  tape := configuration.tape

def blankGapConfig
    (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteOneRestagedMachine.Control where
  state := DeleteOneRestagedMachine.machine.start
  tape :=
    { left := leftRev.map some
      head := none
      right := suffix.map some }

def sourceConfig
    (_runner : TuringMachine MachineCodeSymbol runnerState)
    (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (Control runnerState) :=
  duplicateConfig (runnerState := runnerState)
    (ProductDuplicator.sourceConfig [] input)

def roundTripTape (tape : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.left (Tape.move Direction.right tape)

theorem roundTripTape_equiv (tape : Tape MachineCodeSymbol) :
    Tape.Equiv (roundTripTape tape) tape :=
  Machine.moveLeft_moveRight_equiv_self tape

private theorem cursorTape_nil_eq_input (input : Word MachineCodeSymbol) :
    SerializedShift.cursorTape [] input = Tape.input input := by
  cases input <;> rfl

theorem sourceTape_equiv_initial
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (input : Word MachineCodeSymbol) :
    Tape.Equiv (sourceConfig runner input).tape
      (TuringMachine.initial (machine runner) input).tape := by
  change Tape.Equiv (ProductDuplicator.sourceTape [] input)
    (Tape.input input)
  rw [← cursorTape_nil_eq_input input]
  exact ProductDuplicator.sourceTape_equiv_cursor [] input

private theorem exactRun_lift_of_some
    {inner : TuringMachine symbol innerState}
    {outer : TuringMachine symbol outerState}
    (embed : TuringMachine.Configuration symbol innerState ->
      TuringMachine.Configuration symbol outerState)
    (hstep : forall
      (source target : TuringMachine.Configuration symbol innerState),
      inner.stepConfig source = some target ->
      outer.stepConfig (embed source) = some (embed target))
    {steps : Nat}
    {source target : TuringMachine.Configuration symbol innerState}
    (hrun : inner.runConfigExact? steps source = some target) :
    outer.runConfigExact? steps (embed source) = some (embed target) := by
  induction steps generalizing source target with
  | zero =>
      simp only [TuringMachine.runConfigExact?] at hrun ⊢
      cases hrun
      rfl
  | succ steps ih =>
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hnext : inner.stepConfig source with
      | none =>
          rw [hnext] at hrun
          contradiction
      | some next =>
          rw [hnext] at hrun
          rw [hstep source next hnext]
          simp only
          exact ih hrun

theorem duplicate_stepConfig_of_some
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      ProductDuplicator.Control)
    (hstep : ProductDuplicator.machine.stepConfig source = some target) :
    (machine runner).stepConfig
        (duplicateConfig (runnerState := runnerState) source) =
      some (duplicateConfig (runnerState := runnerState) target) := by
  cases source with
  | mk sourceState sourceTape =>
      cases target with
      | mk targetState targetTape =>
          cases haction :
              ProductDuplicator.transition sourceState sourceTape.read with
          | none =>
              simp [ProductDuplicator.machine, TuringMachine.stepConfig,
                haction] at hstep
          | some action =>
              rcases action with ⟨write, direction, nextState⟩
              simp [ProductDuplicator.machine, TuringMachine.stepConfig,
                haction] at hstep
              cases hstep
              have hsource : sourceState ≠ ProductDuplicator.Control.halt := by
                intro heq
                subst sourceState
                simp [ProductDuplicator.transition] at haction
              simp_all [machine, TuringMachine.stepConfig, transition,
                mapAction, duplicateConfig]

theorem compact_stepConfig_of_some
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      DeleteOneRestagedMachine.Control)
    (hstep : DeleteOneRestagedMachine.machine.stepConfig source =
      some target) :
    (machine runner).stepConfig
        (compactConfig (runnerState := runnerState) source) =
      some (compactConfig (runnerState := runnerState) target) := by
  cases source with
  | mk sourceState sourceTape =>
      cases target with
      | mk targetState targetTape =>
          cases haction :
              DeleteOneRestagedMachine.transition sourceState sourceTape.read with
          | none =>
              simp [DeleteOneRestagedMachine.machine,
                TuringMachine.stepConfig, haction] at hstep
          | some action =>
              rcases action with ⟨write, direction, nextState⟩
              simp [DeleteOneRestagedMachine.machine,
                TuringMachine.stepConfig, haction] at hstep
              cases hstep
              have hsource :
                  sourceState ≠ DeleteOneRestagedMachine.machine.halt := by
                intro heq
                subst sourceState
                simp [DeleteOneRestagedMachine.machine,
                  DeleteOneRestagedMachine.transition,
                  RewindWord.transition] at haction
              simp_all [machine, TuringMachine.stepConfig, transition,
                mapAction, compactConfig,
                DeleteOneRestagedMachine.machine]

theorem runner_stepConfig
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (configuration : TuringMachine.Configuration MachineCodeSymbol
      runnerState) :
    (machine runner).stepConfig
        (runnerConfig (runnerState := runnerState) configuration) =
      Option.map (runnerConfig (runnerState := runnerState))
        (runner.stepConfig configuration) := by
  cases configuration with
  | mk state tape =>
      cases haction : runner.transition state tape.read with
      | none =>
          simp [machine, transition, mapAction, runnerConfig,
            TuringMachine.stepConfig, haction]
      | some action =>
          rcases action with ⟨write, direction, target⟩
          simp [machine, transition, mapAction, runnerConfig,
            TuringMachine.stepConfig, haction]

theorem duplicate_runConfigExact?_lift
    (runner : TuringMachine MachineCodeSymbol runnerState)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      ProductDuplicator.Control}
    (hrun : ProductDuplicator.machine.runConfigExact? steps source =
      some target) :
    (machine runner).runConfigExact? steps
        (duplicateConfig (runnerState := runnerState) source) =
      some (duplicateConfig (runnerState := runnerState) target) :=
  exactRun_lift_of_some
    (duplicateConfig (runnerState := runnerState))
    (duplicate_stepConfig_of_some runner) hrun

theorem compact_runConfigExact?_lift
    (runner : TuringMachine MachineCodeSymbol runnerState)
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      DeleteOneRestagedMachine.Control}
    (hrun : DeleteOneRestagedMachine.machine.runConfigExact? steps source =
      some target) :
    (machine runner).runConfigExact? steps
        (compactConfig (runnerState := runnerState) source) =
      some (compactConfig (runnerState := runnerState) target) :=
  exactRun_lift_of_some
    (compactConfig (runnerState := runnerState))
    (compact_stepConfig_of_some runner) hrun

theorem duplicate_handoff_step
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    (machine runner).stepConfig
        (duplicateConfig (runnerState := runnerState)
          (ProductDuplicator.haltConfig [] (first :: rest))) =
      some (compactConfig (runnerState := runnerState)
        (blankGapConfig (first :: rest).reverse (first :: rest))) := by
  change (machine runner).stepConfig
      { state := .duplicate .halt,
        tape := ProductDuplicator.haltTape [] (first :: rest) } = _
  rw [ProductDuplicator.haltTape_nonempty_shape]
  simp [machine, transition, compactConfig,
    blankGapConfig, TuringMachine.stepConfig, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, List.map_append]

theorem blankGap_start_step
    (leftRev suffix : Word MachineCodeSymbol) :
    DeleteOneRestagedMachine.machine.stepConfig
        (blankGapConfig leftRev suffix) =
      some (DeleteOneRestagedMachine.editConfig
        (SerializedShift.Delete.pullConfig leftRev suffix)) := by
  cases suffix <;> cases leftRev <;> rfl

def blankGapRunSteps
    (leftRev suffix : Word MachineCodeSymbol) : Nat :=
  (1 + (3 * suffix.length + 1)) +
    ((List.append suffix.reverse leftRev).length + 2)

theorem blankGap_run_exact
    (leftRev suffix : Word MachineCodeSymbol) :
    DeleteOneRestagedMachine.machine.runConfigExact?
        (blankGapRunSteps leftRev suffix)
        (blankGapConfig leftRev suffix) =
      some (DeleteOneRestagedMachine.rewindConfig
        (RewindWord.gateConfig
          (List.append leftRev.reverse suffix) 1)) := by
  have hstart :
      DeleteOneRestagedMachine.machine.runConfigExact? 1
          (blankGapConfig leftRev suffix) =
        some (DeleteOneRestagedMachine.editConfig
          (SerializedShift.Delete.pullConfig leftRev suffix)) := by
    rw [TuringMachine.runConfigExact?, blankGap_start_step]
    rfl
  have hpull :=
    DeleteOneRestagedMachine.edit_pull_run_exact leftRev suffix
  have hrewind := DeleteOneRestagedMachine.rewind_run_exact
    (List.append suffix.reverse leftRev)
  have hfirst := TuringMachine.runConfigExact?_trans hstart hpull
  have hfull := TuringMachine.runConfigExact?_trans hfirst hrewind
  simpa [blankGapRunSteps, List.reverse_append] using hfull

theorem compact_handoff_run_exact
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (tape : Tape MachineCodeSymbol) :
    (machine runner).runConfigExact? 2
        { state := .compact DeleteOneRestagedMachine.machine.halt
          tape := tape } =
      some
        { state := .run runner.start
          tape := roundTripTape tape } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, roundTripTape, Tape.write_read_eq_self,
    DeleteOneRestagedMachine.machine]

theorem clean_prefix_run
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    exists steps : Nat,
      (machine runner).runConfigExact? steps
          (sourceConfig runner (first :: rest)) =
        some
          { state := .run runner.start
            tape := roundTripTape
              (RewindWord.gateTape
                (List.append (first :: rest) (first :: rest)) 1) } := by
  have hduplicate := duplicate_runConfigExact?_lift runner
    (ProductDuplicator.run_exact [] (first :: rest))
  have hhandoff :
      (machine runner).runConfigExact? 1
          (duplicateConfig (runnerState := runnerState)
            (ProductDuplicator.haltConfig [] (first :: rest))) =
        some (compactConfig (runnerState := runnerState)
          (blankGapConfig (first :: rest).reverse (first :: rest))) := by
    rw [TuringMachine.runConfigExact?, duplicate_handoff_step]
    rfl
  have hcompact := compact_runConfigExact?_lift runner
    (blankGap_run_exact (first :: rest).reverse (first :: rest))
  have hcompactHandoff := compact_handoff_run_exact runner
    (RewindWord.gateTape
      (List.append (first :: rest).reverse.reverse (first :: rest)) 1)
  have h0 := TuringMachine.runConfigExact?_trans hduplicate hhandoff
  have h1 := TuringMachine.runConfigExact?_trans h0 hcompact
  have h2 := TuringMachine.runConfigExact?_trans h1 hcompactHandoff
  refine ⟨ProductDuplicator.runSteps (first :: rest) + 1 +
      blankGapRunSteps (first :: rest).reverse (first :: rest) + 2, ?_⟩
  simpa [sourceConfig] using h2

theorem prefix_run
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    exists (steps : Nat)
        (endpoint : TuringMachine.Configuration MachineCodeSymbol
          (Control runnerState)),
      (machine runner).runConfigExact? steps
          (TuringMachine.initial (machine runner) (first :: rest)) =
        some endpoint ∧
      endpoint.state = .run runner.start ∧
      Tape.Equiv
        (Tape.input (List.append (first :: rest) (first :: rest)))
        endpoint.tape := by
  rcases clean_prefix_run runner first rest with ⟨steps, hclean⟩
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hclean (sourceTape_equiv_initial runner (first :: rest)) with
    ⟨endpoint, hrun, hstate, htape⟩
  have hgate := RewindWord.gateTape_equiv_input
    (List.append (first :: rest) (first :: rest)) 1
  have hround := roundTripTape_equiv
    (RewindWord.gateTape
      (List.append (first :: rest) (first :: rest)) 1)
  have hinputClean :
      Tape.Equiv
        (Tape.input (List.append (first :: rest) (first :: rest)))
        (roundTripTape (RewindWord.gateTape
          (List.append (first :: rest) (first :: rest)) 1)) :=
    Tape.Equiv.trans (Tape.Equiv.symm hgate) (Tape.Equiv.symm hround)
  refine ⟨steps, endpoint, ?_, ?_, ?_⟩
  · change (machine runner).runConfigExact? steps
        (TuringMachine.initial (machine runner) (first :: rest)) =
      some endpoint at hrun
    exact hrun
  · exact hstate.trans rfl
  · exact Tape.Equiv.trans hinputClean htape

theorem machine_haltingTransitionsDisabled
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (hstop : TuringMachine.HaltingTransitionsDisabled runner) :
    TuringMachine.HaltingTransitionsDisabled (machine runner) := by
  intro read
  simp [machine, transition, mapAction, hstop read]

theorem runnerConfig_haltsFrom_iff
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (source : TuringMachine.Configuration MachineCodeSymbol runnerState) :
    TuringMachine.HaltsFrom (machine runner)
        (runnerConfig (runnerState := runnerState) source) <->
      TuringMachine.HaltsFrom runner source := by
  constructor
  · rintro ⟨final, hcomputes, hhalt⟩
    rcases TuringMachine.computes_to_computesIn hcomputes with
      ⟨steps, hcomputesIn⟩
    have houter :=
      TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr hcomputesIn
    have hlift := TuringMachine.PhaseEmbedding.runConfigExact?_lift
      (Control.run : runnerState -> Control runnerState)
      (runner_stepConfig runner) steps source
    change (machine runner).runConfigExact? steps
        (runnerConfig (runnerState := runnerState) source) =
      Option.map (runnerConfig (runnerState := runnerState))
        (runner.runConfigExact? steps source) at hlift
    rw [houter] at hlift
    cases hinner : runner.runConfigExact? steps source with
    | none => simp [hinner] at hlift
    | some innerFinal =>
        have hfinalEq :
            final = runnerConfig (runnerState := runnerState) innerFinal := by
          simpa [hinner] using hlift
        subst final
        exact ⟨innerFinal,
          TuringMachine.computesIn_to_computes
            (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hinner),
          by simpa [TuringMachine.Halted, machine, runnerConfig] using hhalt⟩
  · rintro ⟨final, hcomputes, hhalt⟩
    exact ⟨runnerConfig (runnerState := runnerState) final,
      TuringMachine.PhaseEmbedding.computes_lift
        (Control.run : runnerState -> Control runnerState)
        (runner_stepConfig runner) hcomputes,
      by simpa [TuringMachine.Halted, machine, runnerConfig] using hhalt⟩

theorem haltsOnInput_iff
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (hstop : TuringMachine.HaltingTransitionsDisabled runner)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInput (machine runner) (first :: rest) <->
      TuringMachine.HaltsOnInput runner
        (List.append (first :: rest) (first :: rest)) := by
  rcases prefix_run runner first rest with
    ⟨prefixSteps, endpoint, hprefixExact, hendpointState,
      hendpointTape⟩
  have hprefix : TuringMachine.ComputesIn (machine runner) prefixSteps
      (TuringMachine.initial (machine runner) (first :: rest)) endpoint :=
    TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hprefixExact
  constructor
  · intro hhalt
    rcases TuringMachine.halts_from_to_halts_from_in
        (by simpa [TuringMachine.HaltsOnInput] using hhalt) with
      ⟨totalSteps, htotal⟩
    rcases haltsFromIn_suffix_of_computesIn
        (machine_haltingTransitionsDisabled runner hstop)
        hprefix htotal with
      ⟨_remaining, _htotalEq, htail⟩
    have htail' := TuringMachine.halts_from_in_to_halts_from htail
    cases endpoint with
    | mk endpointState endpointTape =>
        simp only at hendpointState hendpointTape htail'
        subst endpointState
        have hrunnerActual : TuringMachine.HaltsFrom runner
            { state := runner.start, tape := endpointTape } :=
          (runnerConfig_haltsFrom_iff runner
            { state := runner.start, tape := endpointTape }).mp htail'
        have hrunnerCanonical := turingMachine_haltsFrom_of_tape_equiv
          (Tape.Equiv.symm hendpointTape) hrunnerActual
        simpa [TuringMachine.HaltsOnInput, TuringMachine.initial] using
          hrunnerCanonical
  · intro hhalt
    have hrunnerCanonical : TuringMachine.HaltsFrom runner
        { state := runner.start,
          tape := Tape.input
            (List.append (first :: rest) (first :: rest)) } := by
      simpa [TuringMachine.HaltsOnInput, TuringMachine.initial] using hhalt
    have hrunnerActual := turingMachine_haltsFrom_of_tape_equiv
      hendpointTape hrunnerCanonical
    have houterTail : TuringMachine.HaltsFrom (machine runner) endpoint := by
      cases endpoint with
      | mk endpointState endpointTape =>
          simp only at hendpointState hendpointTape hrunnerActual
          subst endpointState
          exact (runnerConfig_haltsFrom_iff runner
            { state := runner.start, tape := endpointTape }).mpr hrunnerActual
    exact TuringMachine.halts_from_of_computes_prefix
      (TuringMachine.computesIn_to_computes hprefix) houterTail

theorem haltedRunner_haltsOnInput_iff
    [DecidableEq runnerState]
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInput
        (machine (haltStoppedMachine runner)) (first :: rest) <->
      TuringMachine.HaltsOnInput runner
        (List.append (first :: rest) (first :: rest)) := by
  exact (haltsOnInput_iff (haltStoppedMachine runner)
    (haltStoppedMachine_haltingTransitionsDisabled runner) first rest).trans
      (haltStoppedMachine_haltsOnInput_iff runner
        (List.append (first :: rest) (first :: rest)))

end SelfAppendRunner
end SelfHaltingRecognizer
end Computability
end FoC
