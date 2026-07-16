import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.Context.Separator

namespace FoC
namespace Computability

open Languages

namespace Section53BooleanContextPhase

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open Section53InitializerFrontier
open Section53BooleanContextRawTail

def inputRightCells
    (input : Word MachineCodeSymbol) : List (Option Bool) :=
  Section53BooleanContextSavedCloseout.savedTailCells
    (transitionListParserSavedHead input)
    ((MachineDescription.encodeCodeWordAsInput input.tail).map some)

theorem inputRightCells_eq_initialTape_right
    (input : Word MachineCodeSymbol) :
    inputRightCells input = (initialTape input).right := by
  cases input with
  | nil => rfl
  | cons symbol rest =>
      cases symbol <;>
        simp [inputRightCells, transitionListParserSavedHead,
          Section53BooleanContextSavedCloseout.savedTailCells,
          initialTape_cons, inputBits,
          codeSymbolTailBits,
          Section53BooleanContextOneSymbolRound.codeSymbolSecondBit,
          Section53BooleanContextOneSymbolRound.codeSymbolThirdBit,
          Section53BooleanContextOneSymbolRound.codeSymbolFourthBit]

def layoutBody
    (rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (cells : List (Option Bool)) : Word MachineCodeSymbol :=
  MachineCodeSymbol.blank ::
    List.append (List.replicate rowCount MachineCodeSymbol.blank)
      (MachineCodeSymbol.done ::
        List.append table
          (MachineCodeSymbol.header ::
            MachineDescription.encodeCellListAppend []
              (MachineDescription.encodeCellListAppend cells [])))

theorem layoutWord_eq_appender_workWord
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (cells : List (Option Bool)) :
    Section53BooleanContextOneSymbolRound.Machine.layoutWord
        fuel stateCount start halt rowCount table cells [] =
      Section53BooleanContextHaltAppender.Machine.workWord
        fuel stateCount start 0 halt (layoutBody rowCount table cells) := by
  have hcells :
      MachineDescription.encodeCellsAppend cells
          [MachineCodeSymbol.header] =
        List.append (MachineDescription.encodeCellsAppend cells [])
          [MachineCodeSymbol.header] := by
    simpa using encodeCellsAppend_append cells
      ([] : Word MachineCodeSymbol) [MachineCodeSymbol.header]
  simp [Section53BooleanContextOneSymbolRound.Machine.layoutWord,
    Section53BooleanContextLocator.locatorWord,
    Section53BooleanContextLocator.rightCountPrefix,
    Section53BooleanContextLocator.parsedMetadataAppend,
    Section53BooleanContextLocator.parserTailBeforeRightCount,
    Section53BooleanContextHaltAppender.Machine.workWord,
    Section53BooleanContextHaltAppender.Machine.metadataPrefix,
    Section53BooleanContextHaltAppender.Machine.markedHaltField,
    Section53BooleanContextHaltAppender.Machine.copiedTicks,
    layoutBody, MachineDescription.encodeNatAppend,
    MachineDescription.encodeCellListAppend,
    MachineDescription.encodeCellsAppend, MachineDescription.encodeNat,
    List.append_assoc, hcells]

def initialContextPrefix
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeCellListAppend []
    (MachineDescription.encodeCellListAppend (inputRightCells input) [])

def targetSuffix
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    List.append (initialContextPrefix input)
      (MachineDescription.encodeNat D.halt)

theorem targetSuffix_eq_positiveInitialStackSuffix
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    targetSuffix D input = positiveInitialStackSuffix D input := by
  have hleft : (initialTape input).left = [] := by
    cases input with
    | nil => simp [initialTape_nil, Tape.blank]
    | cons symbol rest => rw [initialTape_cons]
  unfold targetSuffix initialContextPrefix positiveInitialStackSuffix
    positiveInitialContextTail
  rw [inputRightCells_eq_initialTape_right]
  unfold Section53UniformInterpreterOneStep.RuntimeKeySingleKeyRepair.protectedTapeContextsAppend
  rw [hleft]
  have hright :
      MachineDescription.encodeCellsAppend (initialTape input).right
          (MachineDescription.encodeNat D.halt) =
        List.append
          (MachineDescription.encodeCellsAppend (initialTape input).right [])
          (MachineDescription.encodeNat D.halt) := by
    simpa using encodeCellsAppend_append (initialTape input).right
      ([] : Word MachineCodeSymbol) (MachineDescription.encodeNat D.halt)
  simp [
    MachineDescription.encodeCellListAppend,
    MachineDescription.encodeNatAppend, MachineDescription.encodeNat,
    MachineDescription.encodeCellsAppend, List.append_assoc, hright]

theorem appender_finalWord_eq_separator_sourceWord
    (D : MachineDescription)
    (fuel : Nat)
    (input : Word MachineCodeSymbol)
    (table : Word MachineCodeSymbol) :
    Section53BooleanContextHaltAppender.Machine.finalWord
        fuel D.stateCount D.start D.halt
        (layoutBody D.transitions.length table (inputRightCells input)) =
      Section53BooleanContextSeparatorConverter.Machine.sourceWord
        fuel D.stateCount D.start D.halt D.transitions.length table
        (targetSuffix D input) := by
  simp [Section53BooleanContextHaltAppender.Machine.finalWord,
    Section53BooleanContextHaltAppender.Machine.metadataPrefix,
    Section53BooleanContextSeparatorConverter.Machine.sourceWord,
    Section53BooleanContextSeparatorConverter.Machine.metadataWithHalt,
    layoutBody, targetSuffix, initialContextPrefix,
    MachineDescription.encodeNatAppend,
    MachineDescription.encodeCellListAppend,
    MachineDescription.encodeCellsAppend, MachineDescription.encodeNat,
    List.append_assoc]

theorem separatorBaseLeftRev_eq_positiveBase
    (D : MachineDescription)
    (fuel : Nat) :
    Section53BooleanContextSeparatorConverter.Machine.baseLeftRev
        fuel D.stateCount D.start D.halt D.transitions.length =
      positiveMaterializerCopierBaseLeftRev D fuel := by
  simp [Section53BooleanContextSeparatorConverter.Machine.baseLeftRev,
    Section53BooleanContextSeparatorConverter.Machine.metadataWithHalt,
    Section53BooleanContextHaltAppender.Machine.metadataPrefix,
    positiveMaterializerCopierBaseLeftRev,
    Section53ParserAssembly.headerAfterHaltLeftRev,
    Section53ParserAssembly.headerAfterStartLeftRev,
    Section53ParserAssembly.headerAfterStateLeftRev,
    Section53ParserAssembly.headerAfterHeaderLeftRev,
    MachineDescription.encodeNatAppend, List.reverse_append,
    List.append_assoc]

theorem separatorTarget_eq_positiveTarget
    (D : MachineDescription)
    (remainingFuel : Nat)
    (input : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription) :
    Section53BooleanContextSeparatorConverter.Machine.targetConfig
        (remainingFuel + 1) D.stateCount D.start D.halt
        D.transitions.length
        (MachineDescription.encodeTransitions (first :: rest))
        (targetSuffix D input) =
      { state :=
          Section53BooleanContextSeparatorConverter.Machine.Control.ready
        tape :=
          (positiveMaterializerTargetConfig D remainingFuel input
            first rest).tape } := by
  rw [targetSuffix_eq_positiveInitialStackSuffix]
  simp [Section53BooleanContextSeparatorConverter.Machine.targetConfig,
    positiveMaterializerTargetConfig,
    separatorBaseLeftRev_eq_positiveBase,
    Section53InitializerPersistentCopy.PersistentMasterCopier.sourceConfig]

namespace Machine

inductive Control where
  | ingress
      (inner : Section53BooleanContextIngress.Machine.Control)
  | ingressBridge (saved : Option MachineCodeSymbol)
  | ingressBounce (saved : Option MachineCodeSymbol)
  | saved
      (inner : Section53BooleanContextSavedCloseout.Machine.Control)
  | savedBridge
  | savedBounce
  | appender
      (inner : Section53BooleanContextHaltAppender.Machine.Control)
  | appenderBridge
  | appenderBounce
  | separator
      (inner : Section53BooleanContextSeparatorConverter.Machine.Control)
deriving DecidableEq

namespace Control

def savedOptions : List (Option MachineCodeSymbol) :=
  none :: MachineCodeSymbol.finite.elems.map some

theorem savedOptions_complete
    (saved : Option MachineCodeSymbol) : saved ∈ savedOptions := by
  cases saved with
  | none => simp [savedOptions]
  | some symbol =>
      simp [savedOptions, MachineCodeSymbol.finite.complete symbol]

def elems : List Control :=
  Section53BooleanContextIngress.Machine.Control.finite.elems.map ingress ++
    savedOptions.map ingressBridge ++
    savedOptions.map ingressBounce ++
    Section53BooleanContextSavedCloseout.Machine.Control.finite.elems.map
      saved ++
    [savedBridge, savedBounce] ++
    Section53BooleanContextHaltAppender.Machine.Control.finite.elems.map
      appender ++
    [appenderBridge, appenderBounce] ++
    Section53BooleanContextSeparatorConverter.Machine.Control.finite.elems.map
      separator

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | ingress inner =>
        simp [elems,
          Section53BooleanContextIngress.Machine.Control.finite.complete inner]
    | ingressBridge saved =>
        simp [elems, savedOptions_complete saved]
    | ingressBounce saved =>
        simp [elems, savedOptions_complete saved]
    | saved inner =>
        simp [elems,
          Section53BooleanContextSavedCloseout.Machine.Control.finite.complete
            inner]
    | savedBridge => simp [elems]
    | savedBounce => simp [elems]
    | appender inner =>
        simp [elems,
          Section53BooleanContextHaltAppender.Machine.Control.finite.complete
            inner]
    | appenderBridge => simp [elems]
    | appenderBounce => simp [elems]
    | separator inner =>
        simp [elems,
          Section53BooleanContextSeparatorConverter.Machine.Control.finite.complete
            inner]

end Control

def liftIngressControl :
    Section53BooleanContextIngress.Machine.Control -> Control
  | .ready saved => .ingressBridge saved
  | inner => .ingress inner

def liftSavedControl :
    Section53BooleanContextSavedCloseout.Machine.Control -> Control
  | .ready => .savedBridge
  | inner => .saved inner

def liftAppenderControl :
    Section53BooleanContextHaltAppender.Machine.Control -> Control
  | .ready => .appenderBridge
  | inner => .appender inner

def mapIngressAction :
    (Option MachineCodeSymbol × Direction ×
      Section53BooleanContextIngress.Machine.Control) ->
    (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, .ready saved) =>
      (write, direction, .ingressBridge saved)
  | (write, direction, target) =>
      (write, direction, .ingress target)

theorem mapIngressAction_eq_lift
    (write : Option MachineCodeSymbol)
    (direction : Direction)
    (target : Section53BooleanContextIngress.Machine.Control) :
    mapIngressAction (write, direction, target) =
      (write, direction, liftIngressControl target) := by
  cases target <;> rfl

def mapSavedAction :
    (Option MachineCodeSymbol × Direction ×
      Section53BooleanContextSavedCloseout.Machine.Control) ->
    (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, .ready) =>
      (write, direction, .savedBridge)
  | (write, direction, target) =>
      (write, direction, .saved target)

theorem mapSavedAction_eq_lift
    (write : Option MachineCodeSymbol)
    (direction : Direction)
    (target : Section53BooleanContextSavedCloseout.Machine.Control) :
    mapSavedAction (write, direction, target) =
      (write, direction, liftSavedControl target) := by
  cases target <;> rfl

def mapAppenderAction :
    (Option MachineCodeSymbol × Direction ×
      Section53BooleanContextHaltAppender.Machine.Control) ->
    (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, .ready) =>
      (write, direction, .appenderBridge)
  | (write, direction, target) =>
      (write, direction, .appender target)

theorem mapAppenderAction_eq_lift
    (write : Option MachineCodeSymbol)
    (direction : Direction)
    (target : Section53BooleanContextHaltAppender.Machine.Control) :
    mapAppenderAction (write, direction, target) =
      (write, direction, liftAppenderControl target) := by
  cases target <;> rfl

def mapSeparatorAction :
    (Option MachineCodeSymbol × Direction ×
      Section53BooleanContextSeparatorConverter.Machine.Control) ->
    (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, target) =>
      (write, direction, .separator target)

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .ingress inner, read =>
      Option.map mapIngressAction
        (Section53BooleanContextIngress.Machine.transition inner read)
  | .ingressBridge saved, read =>
      some (read, Direction.right, .ingressBounce saved)
  | .ingressBounce saved, read =>
      some (read, Direction.left,
        .saved (Section53BooleanContextSavedCloseout.Machine.entry saved))
  | .saved inner, read =>
      Option.map mapSavedAction
        (Section53BooleanContextSavedCloseout.Machine.transition inner read)
  | .savedBridge, read =>
      some (read, Direction.right, .savedBounce)
  | .savedBounce, read =>
      some (read, Direction.left,
        .appender Section53BooleanContextHaltAppender.Machine.Control.fuel)
  | .appender inner, read =>
      Option.map mapAppenderAction
        (Section53BooleanContextHaltAppender.Machine.transition inner read)
  | .appenderBridge, read =>
      some (read, Direction.right, .appenderBounce)
  | .appenderBounce, read =>
      some (read, Direction.left,
        .separator Section53BooleanContextSeparatorConverter.Machine.Control.fuel)
  | .separator inner, read =>
      Option.map mapSeparatorAction
        (Section53BooleanContextSeparatorConverter.Machine.transition inner read)

def entry (saved : Option MachineCodeSymbol) : Control :=
  .ingress (Section53BooleanContextIngress.Machine.entry saved)

def halt : Control :=
  .separator Section53BooleanContextSeparatorConverter.Machine.Control.ready

def machine : TuringMachine MachineCodeSymbol Control where
  start := entry none
  halt := halt
  transition := transition
  statesFinite := Control.finite

def ingressConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextIngress.Machine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := liftIngressControl config.state, tape := config.tape }

def savedConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextSavedCloseout.Machine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := liftSavedControl config.state, tape := config.tape }

def appenderConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextHaltAppender.Machine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := liftAppenderControl config.state, tape := config.tape }

def separatorConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextSeparatorConverter.Machine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .separator config.state, tape := config.tape }

end Machine

namespace Machine

theorem ingress_step_of_some
    (source target : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextIngress.Machine.Control)
    (hstep : Section53BooleanContextIngress.Machine.machine.stepConfig
      source = some target) :
    machine.stepConfig (ingressConfig source) =
      some (ingressConfig target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Section53BooleanContextIngress.Machine.machine] at hstep
      cases htransition :
          Section53BooleanContextIngress.Machine.transition inner
            (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          have hsourceLift : liftIngressControl inner = .ingress inner := by
            cases inner <;> try rfl
            simp [Section53BooleanContextIngress.Machine.transition] at htransition
          cases hstep
          simp [machine, transition, ingressConfig, hsourceLift,
            htransition, mapIngressAction_eq_lift]

theorem ingress_computes_lift
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextIngress.Machine.Control}
    (hrun : TuringMachine.Computes
      Section53BooleanContextIngress.Machine.machine source target) :
    TuringMachine.Computes machine
      (ingressConfig source) (ingressConfig target) := by
  induction hrun with
  | refl config => exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (ingress_step_of_some _ _
            (TuringMachine.stepConfig_eq_some_iff_step.mpr hstep)))
        ih

theorem saved_step_of_some
    (source target : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextSavedCloseout.Machine.Control)
    (hstep : Section53BooleanContextSavedCloseout.Machine.machine.stepConfig
      source = some target) :
    machine.stepConfig (savedConfig source) =
      some (savedConfig target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Section53BooleanContextSavedCloseout.Machine.machine] at hstep
      cases htransition :
          Section53BooleanContextSavedCloseout.Machine.transition inner
            (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          have hsourceLift : liftSavedControl inner = .saved inner := by
            cases inner <;> try rfl
            simp [Section53BooleanContextSavedCloseout.Machine.transition] at htransition
          cases hstep
          simp [machine, transition, savedConfig, hsourceLift,
            htransition, mapSavedAction_eq_lift]

theorem saved_computes_lift
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextSavedCloseout.Machine.Control}
    (hrun : TuringMachine.Computes
      Section53BooleanContextSavedCloseout.Machine.machine source target) :
    TuringMachine.Computes machine
      (savedConfig source) (savedConfig target) := by
  induction hrun with
  | refl config => exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (saved_step_of_some _ _
            (TuringMachine.stepConfig_eq_some_iff_step.mpr hstep)))
        ih

theorem appender_step_of_some
    (source target : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextHaltAppender.Machine.Control)
    (hstep : Section53BooleanContextHaltAppender.Machine.machine.stepConfig
      source = some target) :
    machine.stepConfig (appenderConfig source) =
      some (appenderConfig target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Section53BooleanContextHaltAppender.Machine.machine] at hstep
      cases htransition :
          Section53BooleanContextHaltAppender.Machine.transition inner
            (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          have hsourceLift :
              liftAppenderControl inner = .appender inner := by
            cases inner <;> try rfl
            simp [Section53BooleanContextHaltAppender.Machine.transition] at htransition
          cases hstep
          simp [machine, transition, appenderConfig, hsourceLift,
            htransition, mapAppenderAction_eq_lift]

theorem appender_computes_lift
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextHaltAppender.Machine.Control}
    (hrun : TuringMachine.Computes
      Section53BooleanContextHaltAppender.Machine.machine source target) :
    TuringMachine.Computes machine
      (appenderConfig source) (appenderConfig target) := by
  induction hrun with
  | refl config => exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (appender_step_of_some _ _
            (TuringMachine.stepConfig_eq_some_iff_step.mpr hstep)))
        ih

theorem separator_step_of_some
    (source target : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextSeparatorConverter.Machine.Control)
    (hstep :
      Section53BooleanContextSeparatorConverter.Machine.machine.stepConfig
        source = some target) :
    machine.stepConfig (separatorConfig source) =
      some (separatorConfig target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Section53BooleanContextSeparatorConverter.Machine.machine] at hstep
      cases htransition :
          Section53BooleanContextSeparatorConverter.Machine.transition inner
            (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          cases hstep
          simp [machine, transition, separatorConfig, mapSeparatorAction,
            htransition]

theorem separator_computes_lift
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextSeparatorConverter.Machine.Control}
    (hrun : TuringMachine.Computes
      Section53BooleanContextSeparatorConverter.Machine.machine source target) :
    TuringMachine.Computes machine
      (separatorConfig source) (separatorConfig target) := by
  induction hrun with
  | refl config => exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (separator_step_of_some _ _
            (TuringMachine.stepConfig_eq_some_iff_step.mpr hstep)))
        ih

def boundaryTape (tape : Tape MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  Tape.move Direction.left (Tape.move Direction.right tape)

theorem boundaryTape_equiv
    (tape : Tape MachineCodeSymbol) :
    Tape.Equiv (boundaryTape tape) tape := by
  cases tape with
  | mk left head right =>
      cases right <;>
        simp [boundaryTape, Tape.Equiv, Tape.move,
          Tape.moveLeft, Tape.moveRight, Tape.dropTrailingNone]

theorem ingress_boundary_run_exact
    (saved : Option MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol) :
    machine.runConfigExact? 2
        (ingressConfig
          { state := Section53BooleanContextIngress.Machine.Control.ready saved
            tape := tape }) =
      some
        (savedConfig
          { state := Section53BooleanContextSavedCloseout.Machine.entry saved
            tape := boundaryTape tape }) := by
  cases tape <;> rfl

theorem ingress_boundary_computes
    (saved : Option MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Computes machine
      (ingressConfig
        { state := Section53BooleanContextIngress.Machine.Control.ready saved
          tape := tape })
      (savedConfig
        { state := Section53BooleanContextSavedCloseout.Machine.entry saved
          tape := boundaryTape tape }) := by
  exact TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
      (ingress_boundary_run_exact saved tape))

theorem saved_boundary_run_exact
    (tape : Tape MachineCodeSymbol) :
    machine.runConfigExact? 2
        (savedConfig
          { state := Section53BooleanContextSavedCloseout.Machine.Control.ready
            tape := tape }) =
      some
        (appenderConfig
          { state := Section53BooleanContextHaltAppender.Machine.Control.fuel
            tape := boundaryTape tape }) := by
  cases tape <;> rfl

theorem saved_boundary_computes
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Computes machine
      (savedConfig
        { state := Section53BooleanContextSavedCloseout.Machine.Control.ready
          tape := tape })
      (appenderConfig
        { state := Section53BooleanContextHaltAppender.Machine.Control.fuel
          tape := boundaryTape tape }) := by
  exact TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
      (saved_boundary_run_exact tape))

theorem appender_boundary_run_exact
    (tape : Tape MachineCodeSymbol) :
    machine.runConfigExact? 2
        (appenderConfig
          { state := Section53BooleanContextHaltAppender.Machine.Control.ready
            tape := tape }) =
      some
        (separatorConfig
          { state :=
              Section53BooleanContextSeparatorConverter.Machine.Control.fuel
            tape := boundaryTape tape }) := by
  cases tape <;> rfl

theorem appender_boundary_computes
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Computes machine
      (appenderConfig
        { state := Section53BooleanContextHaltAppender.Machine.Control.ready
          tape := tape })
      (separatorConfig
        { state :=
            Section53BooleanContextSeparatorConverter.Machine.Control.fuel
          tape := boundaryTape tape }) := by
  exact TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
      (appender_boundary_run_exact tape))

theorem saved_positive_materializer
    (D : MachineDescription)
    (remainingFuel : Nat)
    (input : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (htransitions : D.transitions = first :: rest) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := entry (transitionListParserSavedHead input)
          tape :=
            markedParserMaterializerSourceTape
              (Section53ParserAssembly.headerAfterHaltLeftRev D
                (remainingFuel + 1))
              first rest input }
        { state := halt, tape := targetTape } ∧
      Tape.Equiv
        (positiveMaterializerTargetConfig D remainingFuel input
          first rest).tape
        targetTape := by
  let saved := transitionListParserSavedHead input
  let fuel := remainingFuel + 1
  let table := MachineDescription.encodeTransitions (first :: rest)
  let cells := inputRightCells input
  let body := layoutBody D.transitions.length table cells
  let contextTail := List.append (initialContextPrefix input)
    (MachineDescription.encodeNat D.halt)
  have hnoHeaderRaw :=
    transitionListParser_encodeTransitionsAppend_noHeader
      (first :: rest) (suffix := []) (by
        intro symbol hmem
        simp at hmem)
  have hnoHeader : Section53BooleanContextLocator.noHeader table := by
    change transitionListParserNoHeader
      (MachineDescription.encodeTransitions (first :: rest)) at hnoHeaderRaw
    exact hnoHeaderRaw
  rcases Section53BooleanContextIngress.Machine.parsed_ingress_computes
      D remainingFuel input first rest htransitions with
    ⟨ingressTape, hingress, hingressShape⟩
  have hingressLift := ingress_computes_lift hingress
  have hingressBoundary := ingress_boundary_computes saved ingressTape
  have hingressBoundaryShape : Tape.Equiv
      (RawTailPop.sourceConfig
        (Section53BooleanContextOneSymbolRound.Machine.materializerBaseLeftRev
          fuel D.stateCount D.start D.halt D.transitions.length table)
        [] input.tail).tape
      (boundaryTape ingressTape) := by
    exact Tape.Equiv.trans (by simpa [fuel, table] using hingressShape)
      (Tape.Equiv.symm (boundaryTape_equiv ingressTape))
  rcases Section53BooleanContextSavedCloseout.Machine.full_saved_tail_computes
      saved fuel D.stateCount D.start D.halt D.transitions.length table
      input.tail hnoHeader with
    ⟨savedCanonicalTape, hsavedCanonical, hsavedCanonicalShape⟩
  rcases Section53BooleanContextSavedCloseout.Machine.computes_of_tape_equiv
      hsavedCanonical hingressBoundaryShape with
    ⟨savedTape, hsaved, hsavedTransportShape⟩
  have hsavedShape : Tape.Equiv
      (Tape.input
        (Section53BooleanContextOneSymbolRound.Machine.layoutWord
          fuel D.stateCount D.start D.halt D.transitions.length table
          cells []))
      savedTape := by
    exact Tape.Equiv.trans (by
      simpa [saved, fuel, table, cells, inputRightCells] using
        hsavedCanonicalShape) hsavedTransportShape
  have hsavedLift := saved_computes_lift hsaved
  have hsavedBoundary := saved_boundary_computes savedTape
  have hsavedBoundaryShape : Tape.Equiv
      (Tape.input
        (Section53BooleanContextOneSymbolRound.Machine.layoutWord
          fuel D.stateCount D.start D.halt D.transitions.length table
          cells []))
      (boundaryTape savedTape) :=
    Tape.Equiv.trans hsavedShape
      (Tape.Equiv.symm (boundaryTape_equiv savedTape))
  have happenderSource : Tape.Equiv
      (Tape.input
        (Section53BooleanContextHaltAppender.Machine.workWord
          fuel D.stateCount D.start 0 D.halt body))
      (boundaryTape savedTape) := by
    rw [← layoutWord_eq_appender_workWord]
    simpa [fuel, table, cells, body] using hsavedBoundaryShape
  rcases Section53BooleanContextHaltAppender.Machine.computes_append_halt
      fuel D.stateCount D.start D.halt body (boundaryTape savedTape)
      happenderSource with
    ⟨appenderTape, happender, happenderShape⟩
  have happenderLift := appender_computes_lift happender
  have happenderBoundary := appender_boundary_computes appenderTape
  have happenderBoundaryShape : Tape.Equiv
      (Tape.input
        (Section53BooleanContextHaltAppender.Machine.finalWord
          fuel D.stateCount D.start D.halt body))
      (boundaryTape appenderTape) :=
    Tape.Equiv.trans happenderShape
      (Tape.Equiv.symm (boundaryTape_equiv appenderTape))
  have hseparatorSource : Tape.Equiv
      (Section53BooleanContextSeparatorConverter.Machine.sourceConfig
        fuel D.stateCount D.start D.halt D.transitions.length table
        (MachineCodeSymbol.header :: contextTail)).tape
      (boundaryTape appenderTape) := by
    change Tape.Equiv
      (Tape.input
        (Section53BooleanContextSeparatorConverter.Machine.sourceWord
          fuel D.stateCount D.start D.halt D.transitions.length table
          (MachineCodeSymbol.header :: contextTail)))
      (boundaryTape appenderTape)
    have hword := appender_finalWord_eq_separator_sourceWord
      D fuel input table
    simpa [fuel, table, cells, body, contextTail, targetSuffix] using
      hword ▸ happenderBoundaryShape
  rcases Section53BooleanContextSeparatorConverter.Machine.computes_of_tape_equiv
      fuel D.stateCount D.start D.halt D.transitions.length table
      contextTail (boundaryTape appenderTape) hnoHeader hseparatorSource with
    ⟨targetTape, hseparator, hseparatorShape⟩
  have hseparatorLift := separator_computes_lift hseparator
  have htargetShape : Tape.Equiv
      (positiveMaterializerTargetConfig D remainingFuel input
        first rest).tape targetTape := by
    have hseparatorShape' : Tape.Equiv
        (Section53BooleanContextSeparatorConverter.Machine.targetConfig
          (remainingFuel + 1) D.stateCount D.start D.halt
          D.transitions.length
          (MachineDescription.encodeTransitions (first :: rest))
          (targetSuffix D input)).tape
        targetTape := by
      simpa [fuel, table, contextTail, targetSuffix] using hseparatorShape
    rw [separatorTarget_eq_positiveTarget] at hseparatorShape'
    exact hseparatorShape'
  have hrun := TuringMachine.computes_trans hingressLift hingressBoundary
  have hrun := TuringMachine.computes_trans hrun hsavedLift
  have hrun := TuringMachine.computes_trans hrun hsavedBoundary
  have hrun := TuringMachine.computes_trans hrun happenderLift
  have hrun := TuringMachine.computes_trans hrun happenderBoundary
  have hrun := TuringMachine.computes_trans hrun hseparatorLift
  refine ⟨targetTape, ?_, htargetShape⟩
  simpa [entry, halt, saved, ingressConfig, separatorConfig,
    liftIngressControl, Section53BooleanContextIngress.Machine.entry] using
    hrun

theorem contract :
    SavedPositiveBooleanContextMaterializerContract machine entry halt := by
  intro D remainingFuel input first rest htransitions
  exact saved_positive_materializer D remainingFuel input first rest
    htransitions


end Machine

end Section53BooleanContextPhase

end Computability
end FoC
