import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.Context.Separator

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.BooleanContextPhase

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.InitializerFrontier
open FiniteRecognizer.Interpreter.BooleanContextRawTail

def inputRightCells
    (input : Word MachineCodeSymbol) : List (Option Bool) :=
  FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.savedTailCells
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
          FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.savedTailCells,
          initialTape_cons, inputBits,
          codeSymbolTailBits,
          FiniteRecognizer.Interpreter.BooleanContextOneSymbolRound.codeSymbolSecondBit,
          FiniteRecognizer.Interpreter.BooleanContextOneSymbolRound.codeSymbolThirdBit,
          FiniteRecognizer.Interpreter.BooleanContextOneSymbolRound.codeSymbolFourthBit]

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
    FiniteRecognizer.Interpreter.BooleanContextOneSymbolRound.Machine.layoutWord
        fuel stateCount start halt rowCount table cells [] =
      FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.workWord
        fuel stateCount start 0 halt (layoutBody rowCount table cells) := by
  have hcells :
      MachineDescription.encodeCellsAppend cells
          [MachineCodeSymbol.header] =
        List.append (MachineDescription.encodeCellsAppend cells [])
          [MachineCodeSymbol.header] := by
    simpa using encodeCellsAppend_append cells
      ([] : Word MachineCodeSymbol) [MachineCodeSymbol.header]
  simp [FiniteRecognizer.Interpreter.BooleanContextOneSymbolRound.Machine.layoutWord,
    FiniteRecognizer.Interpreter.BooleanContextLocator.locatorWord,
    FiniteRecognizer.Interpreter.BooleanContextLocator.rightCountPrefix,
    FiniteRecognizer.Interpreter.BooleanContextLocator.parsedMetadataAppend,
    FiniteRecognizer.Interpreter.BooleanContextLocator.parserTailBeforeRightCount,
    FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.workWord,
    FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.metadataPrefix,
    FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.markedHaltField,
    FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.copiedTicks,
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
  unfold FiniteRecognizer.Interpreter.UniformInterpreterOneStep.RuntimeKeySingleKeyRepair.protectedTapeContextsAppend
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
    FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.finalWord
        fuel D.stateCount D.start D.halt
        (layoutBody D.transitions.length table (inputRightCells input)) =
      FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.sourceWord
        fuel D.stateCount D.start D.halt D.transitions.length table
        (targetSuffix D input) := by
  simp [FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.finalWord,
    FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.metadataPrefix,
    FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.sourceWord,
    FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.metadataWithHalt,
    layoutBody, targetSuffix, initialContextPrefix,
    MachineDescription.encodeNatAppend,
    MachineDescription.encodeCellListAppend,
    MachineDescription.encodeCellsAppend, MachineDescription.encodeNat,
    List.append_assoc]

theorem separatorBaseLeftRev_eq_positiveBase
    (D : MachineDescription)
    (fuel : Nat) :
    FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.baseLeftRev
        fuel D.stateCount D.start D.halt D.transitions.length =
      positiveMaterializerCopierBaseLeftRev D fuel := by
  simp [FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.baseLeftRev,
    FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.metadataWithHalt,
    FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.metadataPrefix,
    positiveMaterializerCopierBaseLeftRev,
    FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev,
    FiniteRecognizer.Interpreter.ParserAssembly.headerAfterStartLeftRev,
    FiniteRecognizer.Interpreter.ParserAssembly.headerAfterStateLeftRev,
    FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHeaderLeftRev,
    MachineDescription.encodeNatAppend, List.reverse_append,
    List.append_assoc]

theorem separatorTarget_eq_positiveTarget
    (D : MachineDescription)
    (remainingFuel : Nat)
    (input : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription) :
    FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.targetConfig
        (remainingFuel + 1) D.stateCount D.start D.halt
        D.transitions.length
        (MachineDescription.encodeTransitions (first :: rest))
        (targetSuffix D input) =
      { state :=
          FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.Control.ready
        tape :=
          (positiveMaterializerTargetConfig D remainingFuel input
            first rest).tape } := by
  rw [targetSuffix_eq_positiveInitialStackSuffix]
  simp [FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.targetConfig,
    positiveMaterializerTargetConfig,
    separatorBaseLeftRev_eq_positiveBase,
    FiniteRecognizer.Interpreter.InitializerPersistentCopy.PersistentMasterCopier.sourceConfig]

namespace Machine

inductive Control where
  | ingress
      (inner : FiniteRecognizer.Interpreter.BooleanContextIngress.Machine.Control)
  | ingressBridge (saved : Option MachineCodeSymbol)
  | ingressBounce (saved : Option MachineCodeSymbol)
  | saved
      (inner : FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.Control)
  | savedBridge
  | savedBounce
  | appender
      (inner : FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.Control)
  | appenderBridge
  | appenderBounce
  | separator
      (inner : FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.Control)
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
  FiniteRecognizer.Interpreter.BooleanContextIngress.Machine.Control.finite.elems.map ingress ++
    savedOptions.map ingressBridge ++
    savedOptions.map ingressBounce ++
    FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.Control.finite.elems.map
      saved ++
    [savedBridge, savedBounce] ++
    FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.Control.finite.elems.map
      appender ++
    [appenderBridge, appenderBounce] ++
    FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.Control.finite.elems.map
      separator

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | ingress inner =>
        simp [elems,
          FiniteRecognizer.Interpreter.BooleanContextIngress.Machine.Control.finite.complete inner]
    | ingressBridge saved =>
        simp [elems, savedOptions_complete saved]
    | ingressBounce saved =>
        simp [elems, savedOptions_complete saved]
    | saved inner =>
        simp [elems,
          FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.Control.finite.complete
            inner]
    | savedBridge => simp [elems]
    | savedBounce => simp [elems]
    | appender inner =>
        simp [elems,
          FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.Control.finite.complete
            inner]
    | appenderBridge => simp [elems]
    | appenderBounce => simp [elems]
    | separator inner =>
        simp [elems,
          FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.Control.finite.complete
            inner]

end Control

def liftIngressControl :
    FiniteRecognizer.Interpreter.BooleanContextIngress.Machine.Control -> Control
  | .ready saved => .ingressBridge saved
  | inner => .ingress inner

def liftSavedControl :
    FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.Control -> Control
  | .ready => .savedBridge
  | inner => .saved inner

def liftAppenderControl :
    FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.Control -> Control
  | .ready => .appenderBridge
  | inner => .appender inner

def mapIngressAction :
    (Option MachineCodeSymbol × Direction ×
      FiniteRecognizer.Interpreter.BooleanContextIngress.Machine.Control) ->
    (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, .ready saved) =>
      (write, direction, .ingressBridge saved)
  | (write, direction, target) =>
      (write, direction, .ingress target)

theorem mapIngressAction_eq_lift
    (write : Option MachineCodeSymbol)
    (direction : Direction)
    (target : FiniteRecognizer.Interpreter.BooleanContextIngress.Machine.Control) :
    mapIngressAction (write, direction, target) =
      (write, direction, liftIngressControl target) := by
  cases target <;> rfl

def mapSavedAction :
    (Option MachineCodeSymbol × Direction ×
      FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.Control) ->
    (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, .ready) =>
      (write, direction, .savedBridge)
  | (write, direction, target) =>
      (write, direction, .saved target)

theorem mapSavedAction_eq_lift
    (write : Option MachineCodeSymbol)
    (direction : Direction)
    (target : FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.Control) :
    mapSavedAction (write, direction, target) =
      (write, direction, liftSavedControl target) := by
  cases target <;> rfl

def mapAppenderAction :
    (Option MachineCodeSymbol × Direction ×
      FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.Control) ->
    (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, .ready) =>
      (write, direction, .appenderBridge)
  | (write, direction, target) =>
      (write, direction, .appender target)

theorem mapAppenderAction_eq_lift
    (write : Option MachineCodeSymbol)
    (direction : Direction)
    (target : FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.Control) :
    mapAppenderAction (write, direction, target) =
      (write, direction, liftAppenderControl target) := by
  cases target <;> rfl

def mapSeparatorAction :
    (Option MachineCodeSymbol × Direction ×
      FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.Control) ->
    (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, target) =>
      (write, direction, .separator target)

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .ingress inner, read =>
      Option.map mapIngressAction
        (FiniteRecognizer.Interpreter.BooleanContextIngress.Machine.transition inner read)
  | .ingressBridge saved, read =>
      some (read, Direction.right, .ingressBounce saved)
  | .ingressBounce saved, read =>
      some (read, Direction.left,
        .saved (FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.entry saved))
  | .saved inner, read =>
      Option.map mapSavedAction
        (FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.transition inner read)
  | .savedBridge, read =>
      some (read, Direction.right, .savedBounce)
  | .savedBounce, read =>
      some (read, Direction.left,
        .appender FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.Control.fuel)
  | .appender inner, read =>
      Option.map mapAppenderAction
        (FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.transition inner read)
  | .appenderBridge, read =>
      some (read, Direction.right, .appenderBounce)
  | .appenderBounce, read =>
      some (read, Direction.left,
        .separator FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.Control.fuel)
  | .separator inner, read =>
      Option.map mapSeparatorAction
        (FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.transition inner read)

def entry (saved : Option MachineCodeSymbol) : Control :=
  .ingress (FiniteRecognizer.Interpreter.BooleanContextIngress.Machine.entry saved)

def halt : Control :=
  .separator FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.Control.ready

def machine : TuringMachine MachineCodeSymbol Control where
  start := entry none
  halt := halt
  transition := transition
  statesFinite := Control.finite

def ingressConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.BooleanContextIngress.Machine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := liftIngressControl config.state, tape := config.tape }

def savedConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := liftSavedControl config.state, tape := config.tape }

def appenderConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := liftAppenderControl config.state, tape := config.tape }

def separatorConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .separator config.state, tape := config.tape }

end Machine

namespace Machine

theorem ingress_step_of_some
    (source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.BooleanContextIngress.Machine.Control)
    (hstep : FiniteRecognizer.Interpreter.BooleanContextIngress.Machine.machine.stepConfig
      source = some target) :
    machine.stepConfig (ingressConfig source) =
      some (ingressConfig target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [FiniteRecognizer.Interpreter.BooleanContextIngress.Machine.machine] at hstep
      cases htransition :
          FiniteRecognizer.Interpreter.BooleanContextIngress.Machine.transition inner
            (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          have hsourceLift : liftIngressControl inner = .ingress inner := by
            cases inner <;> try rfl
            simp [FiniteRecognizer.Interpreter.BooleanContextIngress.Machine.transition] at htransition
          cases hstep
          simp [machine, transition, ingressConfig, hsourceLift,
            htransition, mapIngressAction_eq_lift]

theorem ingress_computes_lift
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.BooleanContextIngress.Machine.Control}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.BooleanContextIngress.Machine.machine source target) :
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
      FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.Control)
    (hstep : FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.machine.stepConfig
      source = some target) :
    machine.stepConfig (savedConfig source) =
      some (savedConfig target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.machine] at hstep
      cases htransition :
          FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.transition inner
            (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          have hsourceLift : liftSavedControl inner = .saved inner := by
            cases inner <;> try rfl
            simp [FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.transition] at htransition
          cases hstep
          simp [machine, transition, savedConfig, hsourceLift,
            htransition, mapSavedAction_eq_lift]

theorem saved_computes_lift
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.Control}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.machine source target) :
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
      FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.Control)
    (hstep : FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.machine.stepConfig
      source = some target) :
    machine.stepConfig (appenderConfig source) =
      some (appenderConfig target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.machine] at hstep
      cases htransition :
          FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.transition inner
            (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          have hsourceLift :
              liftAppenderControl inner = .appender inner := by
            cases inner <;> try rfl
            simp [FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.transition] at htransition
          cases hstep
          simp [machine, transition, appenderConfig, hsourceLift,
            htransition, mapAppenderAction_eq_lift]

theorem appender_computes_lift
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.Control}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.machine source target) :
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
      FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.Control)
    (hstep :
      FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.machine.stepConfig
        source = some target) :
    machine.stepConfig (separatorConfig source) =
      some (separatorConfig target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.machine] at hstep
      cases htransition :
          FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.transition inner
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
      FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.Control}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.machine source target) :
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
          { state := FiniteRecognizer.Interpreter.BooleanContextIngress.Machine.Control.ready saved
            tape := tape }) =
      some
        (savedConfig
          { state := FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.entry saved
            tape := boundaryTape tape }) := by
  cases tape <;> rfl

theorem ingress_boundary_computes
    (saved : Option MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Computes machine
      (ingressConfig
        { state := FiniteRecognizer.Interpreter.BooleanContextIngress.Machine.Control.ready saved
          tape := tape })
      (savedConfig
        { state := FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.entry saved
          tape := boundaryTape tape }) := by
  exact TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
      (ingress_boundary_run_exact saved tape))

theorem saved_boundary_run_exact
    (tape : Tape MachineCodeSymbol) :
    machine.runConfigExact? 2
        (savedConfig
          { state := FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.Control.ready
            tape := tape }) =
      some
        (appenderConfig
          { state := FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.Control.fuel
            tape := boundaryTape tape }) := by
  cases tape <;> rfl

theorem saved_boundary_computes
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Computes machine
      (savedConfig
        { state := FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.Control.ready
          tape := tape })
      (appenderConfig
        { state := FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.Control.fuel
          tape := boundaryTape tape }) := by
  exact TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
      (saved_boundary_run_exact tape))

theorem appender_boundary_run_exact
    (tape : Tape MachineCodeSymbol) :
    machine.runConfigExact? 2
        (appenderConfig
          { state := FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.Control.ready
            tape := tape }) =
      some
        (separatorConfig
          { state :=
              FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.Control.fuel
            tape := boundaryTape tape }) := by
  cases tape <;> rfl

theorem appender_boundary_computes
    (tape : Tape MachineCodeSymbol) :
    TuringMachine.Computes machine
      (appenderConfig
        { state := FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.Control.ready
          tape := tape })
      (separatorConfig
        { state :=
            FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.Control.fuel
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
              (FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev D
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
  have hnoHeader : FiniteRecognizer.Interpreter.BooleanContextLocator.noHeader table := by
    change transitionListParserNoHeader
      (MachineDescription.encodeTransitions (first :: rest)) at hnoHeaderRaw
    exact hnoHeaderRaw
  rcases FiniteRecognizer.Interpreter.BooleanContextIngress.Machine.parsed_ingress_computes
      D remainingFuel input first rest htransitions with
    ⟨ingressTape, hingress, hingressShape⟩
  have hingressLift := ingress_computes_lift hingress
  have hingressBoundary := ingress_boundary_computes saved ingressTape
  have hingressBoundaryShape : Tape.Equiv
      (RawTailPop.sourceConfig
        (FiniteRecognizer.Interpreter.BooleanContextOneSymbolRound.Machine.materializerBaseLeftRev
          fuel D.stateCount D.start D.halt D.transitions.length table)
        [] input.tail).tape
      (boundaryTape ingressTape) := by
    exact Tape.Equiv.trans (by simpa [fuel, table] using hingressShape)
      (Tape.Equiv.symm (boundaryTape_equiv ingressTape))
  rcases FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.full_saved_tail_computes
      saved fuel D.stateCount D.start D.halt D.transitions.length table
      input.tail hnoHeader with
    ⟨savedCanonicalTape, hsavedCanonical, hsavedCanonicalShape⟩
  rcases FiniteRecognizer.Interpreter.BooleanContextSavedCloseout.Machine.computes_of_tape_equiv
      hsavedCanonical hingressBoundaryShape with
    ⟨savedTape, hsaved, hsavedTransportShape⟩
  have hsavedShape : Tape.Equiv
      (Tape.input
        (FiniteRecognizer.Interpreter.BooleanContextOneSymbolRound.Machine.layoutWord
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
        (FiniteRecognizer.Interpreter.BooleanContextOneSymbolRound.Machine.layoutWord
          fuel D.stateCount D.start D.halt D.transitions.length table
          cells []))
      (boundaryTape savedTape) :=
    Tape.Equiv.trans hsavedShape
      (Tape.Equiv.symm (boundaryTape_equiv savedTape))
  have happenderSource : Tape.Equiv
      (Tape.input
        (FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.workWord
          fuel D.stateCount D.start 0 D.halt body))
      (boundaryTape savedTape) := by
    rw [← layoutWord_eq_appender_workWord]
    simpa [fuel, table, cells, body] using hsavedBoundaryShape
  rcases FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.computes_append_halt
      fuel D.stateCount D.start D.halt body (boundaryTape savedTape)
      happenderSource with
    ⟨appenderTape, happender, happenderShape⟩
  have happenderLift := appender_computes_lift happender
  have happenderBoundary := appender_boundary_computes appenderTape
  have happenderBoundaryShape : Tape.Equiv
      (Tape.input
        (FiniteRecognizer.Interpreter.BooleanContextHaltAppender.Machine.finalWord
          fuel D.stateCount D.start D.halt body))
      (boundaryTape appenderTape) :=
    Tape.Equiv.trans happenderShape
      (Tape.Equiv.symm (boundaryTape_equiv appenderTape))
  have hseparatorSource : Tape.Equiv
      (FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.sourceConfig
        fuel D.stateCount D.start D.halt D.transitions.length table
        (MachineCodeSymbol.header :: contextTail)).tape
      (boundaryTape appenderTape) := by
    change Tape.Equiv
      (Tape.input
        (FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.sourceWord
          fuel D.stateCount D.start D.halt D.transitions.length table
          (MachineCodeSymbol.header :: contextTail)))
      (boundaryTape appenderTape)
    have hword := appender_finalWord_eq_separator_sourceWord
      D fuel input table
    simpa [fuel, table, cells, body, contextTail, targetSuffix] using
      hword ▸ happenderBoundaryShape
  rcases FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.computes_of_tape_equiv
      fuel D.stateCount D.start D.halt D.transitions.length table
      contextTail (boundaryTape appenderTape) hnoHeader hseparatorSource with
    ⟨targetTape, hseparator, hseparatorShape⟩
  have hseparatorLift := separator_computes_lift hseparator
  have htargetShape : Tape.Equiv
      (positiveMaterializerTargetConfig D remainingFuel input
        first rest).tape targetTape := by
    have hseparatorShape' : Tape.Equiv
        (FiniteRecognizer.Interpreter.BooleanContextSeparatorConverter.Machine.targetConfig
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
    liftIngressControl, FiniteRecognizer.Interpreter.BooleanContextIngress.Machine.entry] using
    hrun

theorem contract :
    SavedPositiveBooleanContextMaterializerContract machine entry halt := by
  intro D remainingFuel input first rest htransitions
  exact saved_positive_materializer D remainingFuel input first rest
    htransitions


end Machine

end FiniteRecognizer.Interpreter.BooleanContextPhase

end Computability
end FoC
