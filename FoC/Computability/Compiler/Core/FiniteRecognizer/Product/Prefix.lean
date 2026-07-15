import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.RightPrefix

set_option doc.verso true

/-!
# Product input prefix staging

Compose the outer-fuel parser, collision-free inner-call duplicator, and
contextual right materializer. Both input branches reach the canonical right
protected-frame endpoint while retaining the raw left call.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductPrefix

inductive Control {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) where
  | parser (phaseState : ProductInput.PairFuelParser.Control)
  | parserReturn
  | duplicator (phaseState : ProductDuplicator.Control)
  | duplicatorReturn
  | materializer
      (phaseState : ProductContextual.Full.Control right)
deriving DecidableEq

namespace Control

def elems {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) :
    List (Control right) :=
  List.append
    (ProductInput.PairFuelParser.Control.finite.elems.map Control.parser)
    (List.append [.parserReturn]
      (List.append
        (ProductDuplicator.Control.finite.elems.map Control.duplicator)
        (List.append [.duplicatorReturn]
          ((InitialMaterializer.FullMaterializerMachine.Control.finite right).elems.map
            Control.materializer))))

def finite {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) :
    Foundation.FiniteType (Control right) where
  elems := elems right
  complete := by
    intro control
    cases control with
    | parser phaseState =>
        have h := ProductInput.PairFuelParser.Control.finite.complete phaseState
        simp [elems, h]
    | parserReturn => simp [elems]
    | duplicator phaseState =>
        have h := ProductDuplicator.Control.finite.complete phaseState
        simp [elems, h]
    | duplicatorReturn => simp [elems]
    | materializer phaseState =>
        have h :=
          (InitialMaterializer.FullMaterializerMachine.Control.finite right).complete
            phaseState
        simp [elems, h]

end Control

def mapAction {source target : Type}
    (embed : source -> target) :
    Option (Option MachineCodeSymbol × Direction × source) ->
      Option (Option MachineCodeSymbol × Direction × target)
  | none => none
  | some (write, direction, state) =>
      some (write, direction, embed state)

def transition {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) :
    Control right -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control right)
  | .parser .inner, read =>
      some (read, Direction.right, .parserReturn)
  | .parser phaseState, read =>
      mapAction Control.parser
        (ProductInput.PairFuelParser.transition phaseState read)
  | .parserReturn, read =>
      some (read, Direction.left, .duplicator .scan)
  | .duplicator .halt, read =>
      some (read, Direction.right, .duplicatorReturn)
  | .duplicator phaseState, read =>
      mapAction Control.duplicator
        (ProductDuplicator.transition phaseState read)
  | .duplicatorReturn, read =>
      some (read, Direction.left,
        .materializer
          (InitialMaterializer.FullMaterializerMachine.machine right).start)
  | .materializer phaseState, read =>
      mapAction Control.materializer
        (InitialMaterializer.FullMaterializerMachine.transition right phaseState read)

def machine {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) :
    TuringMachine MachineCodeSymbol (Control right) where
  start := .parser .outer
  halt := .materializer (.header .halt)
  transition := transition right
  statesFinite := Control.finite right

def parserConfig {rightCount : Nat}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)}
    (c : TuringMachine.Configuration MachineCodeSymbol
      ProductInput.PairFuelParser.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control right) where
  state := .parser c.state
  tape := c.tape

def duplicatorConfig {rightCount : Nat}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)}
    (c : TuringMachine.Configuration MachineCodeSymbol
      ProductDuplicator.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control right) where
  state := .duplicator c.state
  tape := c.tape

def materializerConfig {rightCount : Nat}
    {right : TuringMachine MachineCodeSymbol (Fin rightCount)}
    (c : TuringMachine.Configuration MachineCodeSymbol
      (ProductContextual.Full.Control right)) :
    TuringMachine.Configuration MachineCodeSymbol (Control right) where
  state := .materializer c.state
  tape := c.tape

def sourceConfig {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    TuringMachine.Configuration MachineCodeSymbol (Control right) :=
  parserConfig
    (ProductInput.PairFuelParser.sourceConfig input rightFuel leftFuel)

theorem sourceConfig_eq_initial {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    sourceConfig right input leftFuel rightFuel =
      TuringMachine.initial (machine right)
        (GeneratedCode.nestedStageCode input rightFuel leftFuel) := by
  cases leftFuel <;> rfl

def roundTripTape (T : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.left (Tape.move Direction.right T)

theorem roundTripTape_equiv (T : Tape MachineCodeSymbol) :
    Tape.Equiv (roundTripTape T) T :=
  Machine.moveLeft_moveRight_equiv_self T

private theorem write_read_eq_self (T : Tape MachineCodeSymbol) :
    Tape.write (Tape.read T) T = T := by
  cases T
  rfl

theorem parser_handoff_run_exact {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (T : Tape MachineCodeSymbol) :
    (machine right).runConfigExact? 2
        { state := .parser .inner, tape := T } =
      some
        { state := .duplicator .scan,
          tape := roundTripTape T } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, roundTripTape, write_read_eq_self]

theorem duplicator_handoff_run_exact {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (T : Tape MachineCodeSymbol) :
    (machine right).runConfigExact? 2
        { state := .duplicator .halt, tape := T } =
      some
        { state := .materializer
            (InitialMaterializer.FullMaterializerMachine.machine right).start,
          tape := roundTripTape T } := by
  simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
    machine, transition, roundTripTape, write_read_eq_self]

theorem parser_outer_tick_step {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftRev suffix : Word MachineCodeSymbol) :
    (machine right).stepConfig
        (parserConfig
          (ProductInput.PairFuelParser.config .outer leftRev
            (MachineCodeSymbol.tick :: suffix))) =
      some (parserConfig
        (ProductInput.PairFuelParser.config .outer
          (MachineCodeSymbol.tick :: leftRev) suffix)) := by
  cases suffix <;> rfl

theorem parser_outer_done_step {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftRev suffix : Word MachineCodeSymbol) :
    (machine right).stepConfig
        (parserConfig
          (ProductInput.PairFuelParser.config .outer leftRev
            (MachineCodeSymbol.done :: suffix))) =
      some (parserConfig
        (ProductInput.PairFuelParser.config .inner
          (MachineCodeSymbol.done :: leftRev) suffix)) := by
  cases suffix <;> rfl

theorem parser_outer_run {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (fuel : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    (machine right).runConfigExact? (fuel + 1)
        (parserConfig
          (ProductInput.PairFuelParser.config .outer leftRev
            (MachineDescription.encodeNatAppend fuel suffix))) =
      some (parserConfig
        (ProductInput.PairFuelParser.config .inner
          (List.append (MachineDescription.encodeNat fuel).reverse leftRev)
          suffix)) := by
  induction fuel generalizing leftRev with
  | zero =>
      exact parser_outer_done_step right leftRev suffix
  | succ fuel ih =>
      change
        (machine right).runConfigExact? ((fuel + 1) + 1)
            (parserConfig
              (ProductInput.PairFuelParser.config .outer leftRev
                (MachineCodeSymbol.tick ::
                  MachineDescription.encodeNatAppend fuel suffix))) = _
      rw [TuringMachine.runConfigExact?]
      rw [parser_outer_tick_step]
      simp only
      rw [ih]
      simp [MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc]

theorem outer_parse_run {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    (machine right).runConfigExact? (leftFuel + 1)
        (sourceConfig right input leftFuel rightFuel) =
      some (parserConfig
        (ProductInput.PairFuelParser.config .inner
          (MachineDescription.encodeNat leftFuel).reverse
          (ProductDuplicator.productInnerCode input rightFuel))) := by
  simpa [sourceConfig, ProductInput.PairFuelParser.sourceConfig,
    ProductDuplicator.productInnerCode, GeneratedCode.nestedStageCode,
    GeneratedCode.stageCode] using
      parser_outer_run right leftFuel ([] : Word MachineCodeSymbol)
        (ProductDuplicator.productInnerCode input rightFuel)

theorem duplicator_stepConfig_of_some {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (c d : TuringMachine.Configuration MachineCodeSymbol
      ProductDuplicator.Control)
    (hstep : ProductDuplicator.machine.stepConfig c = some d) :
    (machine right).stepConfig (duplicatorConfig c) =
      some (duplicatorConfig d) := by
  cases c with
  | mk sourceState sourceTape =>
      cases d with
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
                mapAction, duplicatorConfig]

theorem duplicator_runConfigExact?_lift {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (steps : Nat)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      ProductDuplicator.Control)
    (hrun : ProductDuplicator.machine.runConfigExact? steps c = some d) :
    (machine right).runConfigExact? steps (duplicatorConfig c) =
      some (duplicatorConfig d) := by
  induction steps generalizing c d with
  | zero =>
      simp only [TuringMachine.runConfigExact?] at hrun ⊢
      cases hrun
      rfl
  | succ steps ih =>
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep : ProductDuplicator.machine.stepConfig c with
      | none =>
          rw [hstep] at hrun
          contradiction
      | some next =>
          rw [hstep] at hrun
          rw [duplicator_stepConfig_of_some right c next hstep]
          simp only
          exact ih next d hrun

theorem materializer_stepConfig_of_some {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (c d : TuringMachine.Configuration MachineCodeSymbol
      (ProductContextual.Full.Control right))
    (hstep :
      (InitialMaterializer.FullMaterializerMachine.machine right).stepConfig c =
        some d) :
    (machine right).stepConfig (materializerConfig c) =
      some (materializerConfig d) := by
  cases c with
  | mk sourceState sourceTape =>
      cases d with
      | mk targetState targetTape =>
          cases haction :
              InitialMaterializer.FullMaterializerMachine.transition
                right sourceState sourceTape.read with
          | none =>
              simp [InitialMaterializer.FullMaterializerMachine.machine,
                TuringMachine.stepConfig, haction] at hstep
          | some action =>
              rcases action with ⟨write, direction, nextState⟩
              simp [InitialMaterializer.FullMaterializerMachine.machine,
                TuringMachine.stepConfig, haction] at hstep
              cases hstep
              simp_all [machine, TuringMachine.stepConfig, transition,
                mapAction, materializerConfig]

theorem materializer_runConfigExact?_lift {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (steps : Nat)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      (ProductContextual.Full.Control right))
    (hrun :
      (InitialMaterializer.FullMaterializerMachine.machine right).runConfigExact?
        steps c = some d) :
    (machine right).runConfigExact? steps (materializerConfig c) =
      some (materializerConfig d) := by
  induction steps generalizing c d with
  | zero =>
      simp only [TuringMachine.runConfigExact?] at hrun ⊢
      cases hrun
      rfl
  | succ steps ih =>
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep :
          (InitialMaterializer.FullMaterializerMachine.machine right).stepConfig
            c with
      | none =>
          rw [hstep] at hrun
          contradiction
      | some next =>
          rw [hstep] at hrun
          rw [materializer_stepConfig_of_some right c next hstep]
          simp only
          exact ih next d hrun

abbrev retainedOuterRev
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    Word MachineCodeSymbol :=
  ProductRightPrefix.retainedOuterRev input leftFuel rightFuel

abbrev canonicalMaterializerSource {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    TuringMachine.Configuration MachineCodeSymbol
      (ProductContextual.Full.Control right) :=
  ProductRightPrefix.rightSourceConfig right input leftFuel rightFuel

theorem productTargetTape_eq_canonicalMaterializerSourceTape
    {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    (ProductDuplicator.productTargetConfig input leftFuel rightFuel).tape =
      (canonicalMaterializerSource right input leftFuel rightFuel).tape := by
  exact (ProductRightPrefix.rightSourceTape_eq_duplicatorTarget
    right input leftFuel rightFuel).symm

def bouncedDuplicatorSource
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    TuringMachine.Configuration MachineCodeSymbol ProductDuplicator.Control where
  state := .scan
  tape := roundTripTape
    (ProductInput.PairFuelParser.config .inner
      (MachineDescription.encodeNat leftFuel).reverse
      (ProductDuplicator.productInnerCode input rightFuel)).tape

theorem cleanDuplicatorSource_equiv_bounced
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    Tape.Equiv
      (ProductDuplicator.productSourceConfig
        input leftFuel rightFuel).tape
      (bouncedDuplicatorSource input leftFuel rightFuel).tape := by
  exact Tape.Equiv.trans
    (ProductDuplicator.productSourceTape_equiv_outerParserEndpoint
      input leftFuel rightFuel)
    (Tape.Equiv.symm
      (roundTripTape_equiv
        (ProductInput.PairFuelParser.config .inner
          (MachineDescription.encodeNat leftFuel).reverse
          (ProductDuplicator.productInnerCode input rightFuel)).tape))

theorem duplicator_run_from_bounced {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    exists endpoint : TuringMachine.Configuration MachineCodeSymbol
        ProductDuplicator.Control,
      (machine right).runConfigExact?
          (ProductDuplicator.runSteps
            (ProductDuplicator.productInnerCode input rightFuel))
          (duplicatorConfig
            (bouncedDuplicatorSource input leftFuel rightFuel)) =
        some (duplicatorConfig endpoint) ∧
      endpoint.state = .halt ∧
      Tape.Equiv
        (ProductDuplicator.productTargetConfig
          input leftFuel rightFuel).tape endpoint.tape := by
  rcases InitialMaterializer.TuringExactEquiv.runConfigExact?_some_of_equiv
      (clean := ProductDuplicator.productSourceConfig
        input leftFuel rightFuel)
      (padded := bouncedDuplicatorSource input leftFuel rightFuel)
      (cleanFinal := ProductDuplicator.productTargetConfig
        input leftFuel rightFuel)
      ProductDuplicator.machine
      (ProductDuplicator.runSteps
        (ProductDuplicator.productInnerCode input rightFuel))
      rfl (cleanDuplicatorSource_equiv_bounced input leftFuel rightFuel)
      (ProductDuplicator.product_run_exact input leftFuel rightFuel) with
    ⟨endpoint, hrun, hstate, htape⟩
  refine ⟨endpoint, ?_, ?_, htape⟩
  · exact duplicator_runConfigExact?_lift right _ _ _ hrun
  · exact hstate.symm

def bouncedMaterializerSource {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (duplicatorEndpoint : TuringMachine.Configuration MachineCodeSymbol
      ProductDuplicator.Control) :
    TuringMachine.Configuration MachineCodeSymbol
      (ProductContextual.Full.Control right) where
  state := (InitialMaterializer.FullMaterializerMachine.machine right).start
  tape := roundTripTape duplicatorEndpoint.tape

theorem canonicalMaterializerSource_equiv_bounced {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat)
    (duplicatorEndpoint : TuringMachine.Configuration MachineCodeSymbol
      ProductDuplicator.Control)
    (htape : Tape.Equiv
      (ProductDuplicator.productTargetConfig
        input leftFuel rightFuel).tape duplicatorEndpoint.tape) :
    Tape.Equiv
      (canonicalMaterializerSource right input leftFuel rightFuel).tape
      (bouncedMaterializerSource right duplicatorEndpoint).tape := by
  rw [← productTargetTape_eq_canonicalMaterializerSourceTape
    right input leftFuel rightFuel]
  exact Tape.Equiv.trans htape
    (Tape.Equiv.symm (roundTripTape_equiv duplicatorEndpoint.tape))

theorem empty_materializer_run_from_bounced {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat)
    (duplicatorEndpoint : TuringMachine.Configuration MachineCodeSymbol
      ProductDuplicator.Control)
    (htape : Tape.Equiv
      (ProductDuplicator.productTargetConfig
        ([] : Word MachineCodeSymbol) leftFuel rightFuel).tape
      duplicatorEndpoint.tape) :
    exists (steps : Nat)
        (endpoint : TuringMachine.Configuration MachineCodeSymbol
          (ProductContextual.Full.Control right)),
      (machine right).runConfigExact? steps
          (materializerConfig
            (bouncedMaterializerSource right duplicatorEndpoint)) =
        some (materializerConfig endpoint) ∧
      endpoint.state = .emptyPrepend .gate ∧
      Tape.Equiv
        (ProductContextual.Full.emptyHaltTape right
          (retainedOuterRev [] leftFuel rightFuel) rightFuel)
        endpoint.tape := by
  rcases ProductContextual.Full.empty_run_to_contextual_endpoint
      right (retainedOuterRev [] leftFuel rightFuel) rightFuel with
    ⟨cleanSteps, cleanEndpoint, hcleanRun, hcleanState, hcleanTape⟩
  rcases InitialMaterializer.TuringExactEquiv.runConfigExact?_some_of_equiv
      (clean := canonicalMaterializerSource right [] leftFuel rightFuel)
      (padded := bouncedMaterializerSource right duplicatorEndpoint)
      (cleanFinal := cleanEndpoint)
      (InitialMaterializer.FullMaterializerMachine.machine right)
      cleanSteps rfl
      (canonicalMaterializerSource_equiv_bounced right [] leftFuel rightFuel
        duplicatorEndpoint htape)
      hcleanRun with
    ⟨endpoint, hrun, hstate, hendpointTape⟩
  refine ⟨cleanSteps, endpoint, ?_, ?_, ?_⟩
  · exact materializer_runConfigExact?_lift right _ _ _ hrun
  · exact hstate.symm.trans hcleanState
  · rw [hcleanTape] at hendpointTape
    exact hendpointTape

theorem nonempty_materializer_run_from_bounced {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat)
    (duplicatorEndpoint : TuringMachine.Configuration MachineCodeSymbol
      ProductDuplicator.Control)
    (htape : Tape.Equiv
      (ProductDuplicator.productTargetConfig
        (headSymbol :: rest) leftFuel rightFuel).tape
      duplicatorEndpoint.tape) :
    exists (steps : Nat)
        (endpoint : TuringMachine.Configuration MachineCodeSymbol
          (ProductContextual.Full.Control right)),
      (machine right).runConfigExact? steps
          (materializerConfig
            (bouncedMaterializerSource right duplicatorEndpoint)) =
        some (materializerConfig endpoint) ∧
      endpoint.state = .header .halt ∧
      Tape.Equiv
        (ProductContextual.Full.nonemptyHaltTape right
          (retainedOuterRev (headSymbol :: rest) leftFuel rightFuel)
          rightFuel headSymbol rest)
        endpoint.tape := by
  rcases ProductContextual.Full.nonempty_run_to_contextual_endpoint
      right
      (retainedOuterRev (headSymbol :: rest) leftFuel rightFuel)
      rightFuel headSymbol rest with
    ⟨cleanSteps, cleanEndpoint, hcleanRun, hcleanState, hcleanTape⟩
  rcases InitialMaterializer.TuringExactEquiv.runConfigExact?_some_of_equiv
      (clean := canonicalMaterializerSource right
        (headSymbol :: rest) leftFuel rightFuel)
      (padded := bouncedMaterializerSource right duplicatorEndpoint)
      (cleanFinal := cleanEndpoint)
      (InitialMaterializer.FullMaterializerMachine.machine right)
      cleanSteps rfl
      (canonicalMaterializerSource_equiv_bounced right
        (headSymbol :: rest) leftFuel rightFuel duplicatorEndpoint htape)
      hcleanRun with
    ⟨endpoint, hrun, hstate, hendpointTape⟩
  refine ⟨cleanSteps, endpoint, ?_, ?_, ?_⟩
  · exact materializer_runConfigExact?_lift right _ _ _ hrun
  · exact hstate.symm.trans hcleanState
  · exact Tape.Equiv.trans hcleanTape hendpointTape

theorem exactRun_trans {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (first second : Nat)
    (source middle target :
      TuringMachine.Configuration MachineCodeSymbol (Control right))
    (hfirst : (machine right).runConfigExact? first source = some middle)
    (hsecond : (machine right).runConfigExact? second middle = some target) :
    (machine right).runConfigExact? (first + second) source = some target := by
  rw [InitialMaterializer.ExactRun.append]
  rw [hfirst]
  exact hsecond

theorem parser_handoff_to_bounced {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    (machine right).runConfigExact? 2
        (parserConfig
          (ProductInput.PairFuelParser.config .inner
            (MachineDescription.encodeNat leftFuel).reverse
            (ProductDuplicator.productInnerCode input rightFuel))) =
      some (duplicatorConfig
        (bouncedDuplicatorSource input leftFuel rightFuel)) := by
  simpa [parserConfig, duplicatorConfig, bouncedDuplicatorSource,
    ProductInput.PairFuelParser.config] using
    parser_handoff_run_exact right
      (ProductInput.PairFuelParser.config .inner
        (MachineDescription.encodeNat leftFuel).reverse
        (ProductDuplicator.productInnerCode input rightFuel)).tape

theorem duplicator_handoff_from_endpoint {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (endpoint : TuringMachine.Configuration MachineCodeSymbol
      ProductDuplicator.Control)
    (hstate : endpoint.state = .halt) :
    (machine right).runConfigExact? 2 (duplicatorConfig endpoint) =
      some (materializerConfig
        (bouncedMaterializerSource right endpoint)) := by
  cases endpoint with
  | mk state tape =>
      simp only at hstate
      subst state
      simpa [duplicatorConfig, materializerConfig,
        bouncedMaterializerSource] using
        duplicator_handoff_run_exact right tape

theorem empty_prefix_run {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    exists (steps : Nat)
        (endpoint : TuringMachine.Configuration MachineCodeSymbol
          (ProductContextual.Full.Control right)),
      (machine right).runConfigExact? steps
          (TuringMachine.initial (machine right)
            (GeneratedCode.nestedStageCode [] rightFuel leftFuel)) =
        some (materializerConfig endpoint) ∧
      endpoint.state = .emptyPrepend .gate ∧
      Tape.Equiv
        (ProductContextual.Full.emptyHaltTape right
          (retainedOuterRev [] leftFuel rightFuel) rightFuel)
        endpoint.tape := by
  have hparse := outer_parse_run right [] leftFuel rightFuel
  rw [sourceConfig_eq_initial] at hparse
  have hparserHandoff :=
    parser_handoff_to_bounced right [] leftFuel rightFuel
  rcases duplicator_run_from_bounced right [] leftFuel rightFuel with
    ⟨duplicatorEndpoint, hduplicator, hduplicatorState,
      hduplicatorTape⟩
  have hduplicatorHandoff :=
    duplicator_handoff_from_endpoint right duplicatorEndpoint
      hduplicatorState
  rcases empty_materializer_run_from_bounced right leftFuel rightFuel
      duplicatorEndpoint hduplicatorTape with
    ⟨materializerSteps, endpoint, hmaterializer, hendpointState,
      hendpointTape⟩
  have hprefix0 := exactRun_trans right _ _ _ _ _ hparse hparserHandoff
  have hprefix1 := exactRun_trans right _ _ _ _ _ hprefix0 hduplicator
  have hprefix2 :=
    exactRun_trans right _ _ _ _ _ hprefix1 hduplicatorHandoff
  have hfull := exactRun_trans right _ _ _ _ _ hprefix2 hmaterializer
  exact ⟨_, endpoint, hfull, hendpointState, hendpointTape⟩

theorem nonempty_prefix_run {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    exists (steps : Nat)
        (endpoint : TuringMachine.Configuration MachineCodeSymbol
          (ProductContextual.Full.Control right)),
      (machine right).runConfigExact? steps
          (TuringMachine.initial (machine right)
            (GeneratedCode.nestedStageCode
              (headSymbol :: rest) rightFuel leftFuel)) =
        some (materializerConfig endpoint) ∧
      endpoint.state = .header .halt ∧
      Tape.Equiv
        (ProductContextual.Full.nonemptyHaltTape right
          (retainedOuterRev (headSymbol :: rest) leftFuel rightFuel)
          rightFuel headSymbol rest)
        endpoint.tape := by
  have hparse :=
    outer_parse_run right (headSymbol :: rest) leftFuel rightFuel
  rw [sourceConfig_eq_initial] at hparse
  have hparserHandoff :=
    parser_handoff_to_bounced right (headSymbol :: rest)
      leftFuel rightFuel
  rcases duplicator_run_from_bounced right (headSymbol :: rest)
      leftFuel rightFuel with
    ⟨duplicatorEndpoint, hduplicator, hduplicatorState,
      hduplicatorTape⟩
  have hduplicatorHandoff :=
    duplicator_handoff_from_endpoint right duplicatorEndpoint
      hduplicatorState
  rcases nonempty_materializer_run_from_bounced right headSymbol rest
      leftFuel rightFuel duplicatorEndpoint hduplicatorTape with
    ⟨materializerSteps, endpoint, hmaterializer, hendpointState,
      hendpointTape⟩
  have hprefix0 := exactRun_trans right _ _ _ _ _ hparse hparserHandoff
  have hprefix1 := exactRun_trans right _ _ _ _ _ hprefix0 hduplicator
  have hprefix2 :=
    exactRun_trans right _ _ _ _ _ hprefix1 hduplicatorHandoff
  have hfull := exactRun_trans right _ _ _ _ _ hprefix2 hmaterializer
  exact ⟨_, endpoint, hfull, hendpointState, hendpointTape⟩

abbrev canonicalRightEndpointTape {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    Tape MachineCodeSymbol :=
  ProductRightPrefix.canonicalRightEndpointTape
    right input leftFuel rightFuel

abbrev rightTerminalState {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) :
    ProductContextual.Full.Control right :=
  ProductRightPrefix.rightTerminalState right input

theorem prefix_run {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    exists (steps : Nat)
        (endpoint : TuringMachine.Configuration MachineCodeSymbol
          (ProductContextual.Full.Control right)),
      (machine right).runConfigExact? steps
          (TuringMachine.initial (machine right)
            (GeneratedCode.nestedStageCode input rightFuel leftFuel)) =
        some (materializerConfig endpoint) ∧
      endpoint.state = rightTerminalState right input ∧
      Tape.Equiv
        (canonicalRightEndpointTape right input leftFuel rightFuel)
        endpoint.tape := by
  cases input with
  | nil =>
      rcases empty_prefix_run right leftFuel rightFuel with
        ⟨steps, endpoint, hrun, hstate, htape⟩
      exact ⟨steps, endpoint, hrun, hstate, htape⟩
  | cons headSymbol rest =>
      rcases nonempty_prefix_run right headSymbol rest leftFuel rightFuel with
        ⟨steps, endpoint, hrun, hstate, htape⟩
      exact ⟨steps, endpoint, hrun, hstate, htape⟩

theorem machine_haltingTransitionsDisabled {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount)) :
    TuringMachine.HaltingTransitionsDisabled (machine right) := by
  intro read
  rfl

end ProductPrefix
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
