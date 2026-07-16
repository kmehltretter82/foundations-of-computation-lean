import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.Context.TailDriver

namespace FoC
namespace Computability

open Languages

namespace Section53BooleanContextSavedCloseout

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open Section53InitializerFrontier
open Section53RuntimeEncodedList
open Section53BooleanContextMaterializer
open Section53BooleanContextLocator
open Section53BooleanContextRawTail
open Section53BooleanContextOneSymbolRound
open Section53BooleanContextRawTailDriver

inductive TailPhase where
  | fourth
  | third
  | second
deriving DecidableEq

namespace TailPhase

def elems : List TailPhase := [.fourth, .third, .second]

def finite : Foundation.FiniteType TailPhase where
  elems := elems
  complete := by
    intro phase
    cases phase <;> simp [elems]

end TailPhase

def phaseBit
    (symbol : MachineCodeSymbol) : TailPhase -> Bool
  | .fourth =>
      Section53BooleanContextOneSymbolRound.codeSymbolFourthBit symbol
  | .third =>
      Section53BooleanContextOneSymbolRound.codeSymbolThirdBit symbol
  | .second =>
      Section53BooleanContextOneSymbolRound.codeSymbolSecondBit symbol

def nextPhase : TailPhase -> Option TailPhase
  | .fourth => some .third
  | .third => some .second
  | .second => none

def savedTailCells
    (saved : Option MachineCodeSymbol)
    (rest : List (Option Bool)) : List (Option Bool) :=
  match saved with
  | none => rest
  | some symbol =>
      some (Section53BooleanContextOneSymbolRound.codeSymbolSecondBit symbol) ::
        some (Section53BooleanContextOneSymbolRound.codeSymbolThirdBit symbol) ::
        some (Section53BooleanContextOneSymbolRound.codeSymbolFourthBit symbol) ::
        rest

namespace Machine

inductive Control where
  | raw (saved : Option MachineCodeSymbol)
      (inner : Section53BooleanContextRawTailDriver.Driver.Control)
  | rawBounce (saved : Option MachineCodeSymbol)
  | locate (saved : MachineCodeSymbol) (phase : TailPhase)
      (inner : Section53BooleanContextLocator.Control)
  | locatorBounce (saved : MachineCodeSymbol) (phase : TailPhase)
  | prepend (saved : MachineCodeSymbol) (phase : TailPhase)
      (inner : Prepend.Control)
  | prependBounce (saved : MachineCodeSymbol) (phase : TailPhase)
  | finishBounce
  | ready
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

def savedInnerControls
    {inner : Type}
    (innerElems : List inner)
    (f : Option MachineCodeSymbol -> inner -> Control) : List Control :=
  savedOptions.flatMap fun saved => innerElems.map (f saved)

def symbolPhaseControls
    (f : MachineCodeSymbol -> TailPhase -> Control) : List Control :=
  MachineCodeSymbol.finite.elems.flatMap fun saved =>
    TailPhase.finite.elems.map (f saved)

def symbolPhaseInnerControls
    {inner : Type}
    (innerElems : List inner)
    (f : MachineCodeSymbol -> TailPhase -> inner -> Control) : List Control :=
  MachineCodeSymbol.finite.elems.flatMap fun saved =>
    TailPhase.finite.elems.flatMap fun phase =>
      innerElems.map (f saved phase)

theorem savedInnerControls_complete
    {inner : Type}
    (innerElems : List inner)
    (hinner : forall value : inner, value ∈ innerElems)
    (f : Option MachineCodeSymbol -> inner -> Control)
    (saved : Option MachineCodeSymbol) (value : inner) :
    f saved value ∈ savedInnerControls innerElems f := by
  apply List.mem_flatMap.mpr
  refine ⟨saved, savedOptions_complete saved, ?_⟩
  apply List.mem_map.mpr
  exact ⟨value, hinner value, rfl⟩

theorem symbolPhaseControls_complete
    (f : MachineCodeSymbol -> TailPhase -> Control)
    (saved : MachineCodeSymbol) (phase : TailPhase) :
    f saved phase ∈ symbolPhaseControls f := by
  apply List.mem_flatMap.mpr
  refine ⟨saved, MachineCodeSymbol.finite.complete saved, ?_⟩
  apply List.mem_map.mpr
  exact ⟨phase, TailPhase.finite.complete phase, rfl⟩

theorem symbolPhaseInnerControls_complete
    {inner : Type}
    (innerElems : List inner)
    (hinner : forall value : inner, value ∈ innerElems)
    (f : MachineCodeSymbol -> TailPhase -> inner -> Control)
    (saved : MachineCodeSymbol) (phase : TailPhase) (value : inner) :
    f saved phase value ∈ symbolPhaseInnerControls innerElems f := by
  apply List.mem_flatMap.mpr
  refine ⟨saved, MachineCodeSymbol.finite.complete saved, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨phase, TailPhase.finite.complete phase, ?_⟩
  apply List.mem_map.mpr
  exact ⟨value, hinner value, rfl⟩

def elems : List Control :=
  savedInnerControls
      Section53BooleanContextRawTailDriver.Driver.Control.finite.elems
      Control.raw ++
    savedOptions.map Control.rawBounce ++
    symbolPhaseInnerControls
      Section53BooleanContextLocator.Control.finite.elems Control.locate ++
    symbolPhaseControls Control.locatorBounce ++
    symbolPhaseInnerControls Prepend.Control.finite.elems Control.prepend ++
    symbolPhaseControls Control.prependBounce ++
    [Control.finishBounce, Control.ready]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | raw saved inner =>
        have h := savedInnerControls_complete
          Section53BooleanContextRawTailDriver.Driver.Control.finite.elems
          Section53BooleanContextRawTailDriver.Driver.Control.finite.complete
          Control.raw saved inner
        simp [elems, h]
    | rawBounce saved =>
        have h := savedOptions_complete saved
        simp [elems, h]
    | locate saved phase inner =>
        have h := symbolPhaseInnerControls_complete
          Section53BooleanContextLocator.Control.finite.elems
          Section53BooleanContextLocator.Control.finite.complete
          Control.locate saved phase inner
        simp [elems, h]
    | locatorBounce saved phase =>
        have h := symbolPhaseControls_complete Control.locatorBounce
          saved phase
        simp [elems, h]
    | prepend saved phase inner =>
        have h := symbolPhaseInnerControls_complete
          Prepend.Control.finite.elems Prepend.Control.finite.complete
          Control.prepend saved phase inner
        simp [elems, h]
    | prependBounce saved phase =>
        have h := symbolPhaseControls_complete Control.prependBounce
          saved phase
        simp [elems, h]
    | finishBounce => simp [elems]
    | ready => simp [elems]

end Control

def mapRawAction
    (saved : Option MachineCodeSymbol) :
    (Option MachineCodeSymbol × Direction ×
      Section53BooleanContextRawTailDriver.Driver.Control) ->
      (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, next) => (write, direction, .raw saved next)

def mapLocatorAction
    (saved : MachineCodeSymbol) (phase : TailPhase) :
    (Option MachineCodeSymbol × Direction ×
      Section53BooleanContextLocator.Control) ->
      (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, next) =>
      (write, direction, .locate saved phase next)

def mapPrependAction
    (saved : MachineCodeSymbol) (phase : TailPhase) :
    (Option MachineCodeSymbol × Direction × Prepend.Control) ->
      (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, next) =>
      (write, direction, .prepend saved phase next)

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .raw saved (.finish .gate), read =>
      some (read, Direction.left, .rawBounce saved)
  | .raw saved inner, read =>
      Option.map (mapRawAction saved)
        (Section53BooleanContextRawTailDriver.Driver.transition inner read)
  | .rawBounce none, read =>
      some (read, Direction.right, .ready)
  | .rawBounce (some saved), read =>
      some (read, Direction.right, .locate saved .fourth .fuel)
  | .locate saved phase .ready, read =>
      some (read, Direction.left, .locatorBounce saved phase)
  | .locate saved phase inner, read =>
      Option.map (mapLocatorAction saved phase)
        (Section53BooleanContextLocator.transition inner read)
  | .locatorBounce saved phase, read =>
      some (read, Direction.right,
        .prepend saved phase (.locate .count))
  | .prepend _saved .second (.insert (.rewind .gate)), read =>
      some (read, Direction.left, .finishBounce)
  | .prepend saved phase (.insert (.rewind .gate)), read =>
      match nextPhase phase with
      | none => some (read, Direction.left, .finishBounce)
      | some next =>
          some (read, Direction.left, .prependBounce saved next)
  | .prepend saved phase inner, read =>
      Option.map (mapPrependAction saved phase)
        (Prepend.transition (some (phaseBit saved phase)) inner read)
  | .prependBounce saved phase, read =>
      some (read, Direction.right, .locate saved phase .fuel)
  | .finishBounce, read =>
      some (read, Direction.right, .ready)
  | .ready, _ => none

def entry (saved : Option MachineCodeSymbol) : Control :=
  .raw saved Section53BooleanContextRawTailDriver.Driver.machine.start

def machine : TuringMachine MachineCodeSymbol Control where
  start := entry none
  halt := .ready
  transition := transition
  statesFinite := Control.finite

def rawConfig
    (saved : Option MachineCodeSymbol)
    (config : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextRawTailDriver.Driver.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .raw saved config.state, tape := config.tape }

def locatorConfig
    (saved : MachineCodeSymbol) (phase : TailPhase)
    (config : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextLocator.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .locate saved phase config.state, tape := config.tape }

def prependConfig
    (saved : MachineCodeSymbol) (phase : TailPhase)
    (config : TuringMachine.Configuration MachineCodeSymbol
      Prepend.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .prepend saved phase config.state, tape := config.tape }

theorem raw_step_of_some
    (saved : Option MachineCodeSymbol)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextRawTailDriver.Driver.Control)
    (hstep :
      Section53BooleanContextRawTailDriver.Driver.machine.stepConfig source =
        some target) :
    machine.stepConfig (rawConfig saved source) =
      some (rawConfig saved target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Section53BooleanContextRawTailDriver.Driver.machine] at hstep
      cases htransition :
          Section53BooleanContextRawTailDriver.Driver.transition inner
            (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          cases hstep
          have hnotReady :
              inner ≠
                Section53BooleanContextRawTailDriver.Driver.Control.finish
                  .gate := by
            intro heq
            subst inner
            simp [Section53BooleanContextRawTailDriver.Driver.transition,
              RewindWord.transition] at htransition
          simp [machine, transition, rawConfig, mapRawAction,
            htransition]

theorem raw_computes_lift
    (saved : Option MachineCodeSymbol)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextRawTailDriver.Driver.Control}
    (hrun : TuringMachine.Computes
      Section53BooleanContextRawTailDriver.Driver.machine source target) :
    TuringMachine.Computes machine
      (rawConfig saved source) (rawConfig saved target) := by
  induction hrun with
  | refl config => exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (raw_step_of_some saved _ _
            (TuringMachine.stepConfig_eq_some_iff_step.mpr hstep)))
        ih

theorem locator_step_of_some
    (saved : MachineCodeSymbol) (phase : TailPhase)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextLocator.Control)
    (hstep : Section53BooleanContextLocator.machine.stepConfig source =
      some target) :
    machine.stepConfig (locatorConfig saved phase source) =
      some (locatorConfig saved phase target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Section53BooleanContextLocator.machine] at hstep
      cases htransition :
          Section53BooleanContextLocator.transition inner (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          cases hstep
          have hnot : inner ≠ Section53BooleanContextLocator.Control.ready := by
            intro heq
            subst inner
            simp [Section53BooleanContextLocator.transition] at htransition
          simp [machine, transition, locatorConfig, mapLocatorAction,
            htransition]

theorem locator_computes_lift
    (saved : MachineCodeSymbol) (phase : TailPhase)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextLocator.Control}
    (hrun : TuringMachine.Computes
      Section53BooleanContextLocator.machine source target) :
    TuringMachine.Computes machine
      (locatorConfig saved phase source)
      (locatorConfig saved phase target) := by
  induction hrun with
  | refl config => exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (locator_step_of_some saved phase _ _
            (TuringMachine.stepConfig_eq_some_iff_step.mpr hstep)))
        ih

theorem prepend_step_of_some
    (saved : MachineCodeSymbol) (phase : TailPhase)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      Prepend.Control)
    (hstep : (Prepend.machine (some (phaseBit saved phase))).stepConfig
      source = some target) :
    machine.stepConfig (prependConfig saved phase source) =
      some (prependConfig saved phase target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Prepend.machine] at hstep
      cases htransition :
          Prepend.transition (some (phaseBit saved phase)) inner
            (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          cases hstep
          have hnot :
              inner ≠ Prepend.Control.insert (.rewind .gate) := by
            intro heq
            subst inner
            cases Tape.read tape <;>
              simp [Prepend.transition, InsertRestagedMachine.transition,
                RewindWord.transition] at htransition
          cases phase <;>
            simp [machine, transition, prependConfig, mapPrependAction,
              htransition, hnot]

theorem prepend_run_of_some
    (saved : MachineCodeSymbol) (phase : TailPhase) :
    forall (steps : Nat)
      (source target : TuringMachine.Configuration MachineCodeSymbol
        Prepend.Control),
      (Prepend.machine (some (phaseBit saved phase))).runConfigExact?
          steps source = some target ->
        machine.runConfigExact? steps (prependConfig saved phase source) =
          some (prependConfig saved phase target) := by
  intro steps
  induction steps with
  | zero =>
      intro source target hrun
      simpa [TuringMachine.runConfigExact?] using
        congrArg (prependConfig saved phase) (Option.some.inj hrun)
  | succ steps ih =>
      intro source target hrun
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep :
          (Prepend.machine (some (phaseBit saved phase))).stepConfig source with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rw [prepend_step_of_some saved phase source next hstep]
          simp only
          exact ih next target hrun

theorem computes_of_tape_equiv
    {source target : TuringMachine.Configuration MachineCodeSymbol Control}
    {sourceTape : Tape MachineCodeSymbol}
    (hrun : TuringMachine.Computes machine source target)
    (hsource : Tape.Equiv source.tape sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := source.state, tape := sourceTape }
        { state := target.state, tape := targetTape } ∧
      Tape.Equiv target.tape targetTape := by
  rcases TuringMachine.computes_to_computesIn hrun with ⟨steps, hrunIn⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hrunIn hsource with
    ⟨target, htargetRun, htargetState, htargetTape⟩
  rcases target with ⟨state, tape⟩
  simp only at htargetState
  subst state
  exact ⟨tape, TuringMachine.computesIn_to_computes htargetRun,
    htargetTape⟩

def prependTerminal : Prepend.Control :=
  .insert (.rewind .gate)

theorem locator_to_prepend_run_exact
    (saved : MachineCodeSymbol) (phase : TailPhase)
    (baseLeftRev : Word MachineCodeSymbol)
    (count : Nat) (suffix : Word MachineCodeSymbol)
    (hbase : baseLeftRev ≠ []) :
    machine.runConfigExact? 2
        { state := Control.locate saved phase .ready
          tape := (Prepend.sourceConfig baseLeftRev count suffix).tape } =
      some
        (prependConfig saved phase
          (Prepend.sourceConfig baseLeftRev count suffix)) := by
  cases hbaseEq : baseLeftRev with
  | nil => contradiction
  | cons first rest =>
      cases count <;> cases suffix <;> rfl

theorem prepend_to_locator_run_exact
    (saved : MachineCodeSymbol)
    (phase next : TailPhase)
    (hnext : nextPhase phase = some next)
    (word : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        { state := Control.prepend saved phase prependTerminal
          tape := Tape.input word } =
      some
        { state := Control.locate saved next .fuel
          tape :=
            Section53BooleanContextOneSymbolRound.Machine.bounceTape
              (Tape.input word) } := by
  cases phase <;> simp [nextPhase] at hnext
  all_goals cases hnext
  all_goals cases word <;> rfl

theorem prepend_to_ready_run_exact
    (saved : MachineCodeSymbol)
    (word : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        { state := Control.prepend saved .second prependTerminal
          tape := Tape.input word } =
      some
        { state := Control.ready
          tape :=
            Section53BooleanContextOneSymbolRound.Machine.bounceTape
              (Tape.input word) } := by
  cases word <;> rfl

theorem phase_computes_of_tape_equiv
    (saved : MachineCodeSymbol) (phase : TailPhase)
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (raw : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hnoHeader : Section53BooleanContextLocator.noHeader table)
    (hsource : Tape.Equiv
      (Section53BooleanContextOneSymbolRound.Machine.locatorSource
        fuel stateCount start halt rowCount table cells raw).tape
      sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := Control.locate saved phase .fuel
          tape := sourceTape }
        { state := Control.prepend saved phase prependTerminal
          tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (Section53BooleanContextOneSymbolRound.Machine.layoutWord
            fuel stateCount start halt rowCount table
            (some (phaseBit saved phase) :: cells) raw))
        targetTape := by
  let baseLeftRev :=
    Section53BooleanContextOneSymbolRound.Machine.materializerBaseLeftRev
      fuel stateCount start halt rowCount table
  let suffix := MachineDescription.encodeCellsAppend cells
    (MachineCodeSymbol.header :: raw)
  have hlocatorInner :=
    Section53BooleanContextLocator.computes_to_right_count
      fuel stateCount start halt rowCount table cells.length suffix hnoHeader
  have hlocator := locator_computes_lift saved phase hlocatorInner
  have hbase : baseLeftRev ≠ [] := by
    exact
      Section53BooleanContextOneSymbolRound.Machine.materializerBaseLeftRev_ne_nil
        fuel stateCount start halt rowCount table
  have hhandoffExact := locator_to_prepend_run_exact
    saved phase baseLeftRev cells.length suffix hbase
  have hhandoff := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hhandoffExact)
  have hprefix := TuringMachine.computes_trans hlocator hhandoff
  rcases Prepend.run_exact baseLeftRev cells.length
      (some (phaseBit saved phase)) suffix with
    ⟨endpoint, hprependExact, hterminal, htarget⟩
  have hprependLiftExact := prepend_run_of_some saved phase
    _ _ _ hprependExact
  have hprependLift := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
      hprependLiftExact)
  rcases endpoint with ⟨endpointState, endpointTape⟩
  simp only at hterminal
  subst endpointState
  have hcanonical := TuringMachine.computes_trans hprefix hprependLift
  rcases computes_of_tape_equiv hcanonical hsource with
    ⟨targetTape, htransport, htransportTarget⟩
  refine ⟨targetTape, ?_, ?_⟩
  · simpa [locatorConfig,
      Section53BooleanContextOneSymbolRound.Machine.locatorSource,
      Section53BooleanContextLocator.sourceConfig,
      Section53BooleanContextLocator.config,
      prependConfig, prependTerminal] using htransport
  · rw [Section53BooleanContextOneSymbolRound.Machine.layoutWord_eq_prepend_targetWord]
    exact Tape.Equiv.trans htarget htransportTarget

theorem prepend_to_locator_computes_of_tape_equiv
    (saved : MachineCodeSymbol)
    (phase next : TailPhase)
    (hnext : nextPhase phase = some next)
    (word : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv (Tape.input word) sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := Control.prepend saved phase prependTerminal
          tape := sourceTape }
        { state := Control.locate saved next .fuel
          tape := targetTape } ∧
      Tape.Equiv (Tape.input word) targetTape := by
  have hrunExact := prepend_to_locator_run_exact
    saved phase next hnext word
  have hrun := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrunExact)
  rcases computes_of_tape_equiv hrun hsource with
    ⟨targetTape, htransport, htransportTarget⟩
  refine ⟨targetTape, htransport, ?_⟩
  exact Tape.Equiv.trans
    (Section53BooleanContextOneSymbolRound.Machine.bounceTape_input_equiv word)
    htransportTarget

theorem prepend_to_ready_computes_of_tape_equiv
    (saved : MachineCodeSymbol)
    (word : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv (Tape.input word) sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := Control.prepend saved .second prependTerminal
          tape := sourceTape }
        { state := Control.ready
          tape := targetTape } ∧
      Tape.Equiv (Tape.input word) targetTape := by
  have hrunExact := prepend_to_ready_run_exact saved word
  have hrun := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrunExact)
  rcases computes_of_tape_equiv hrun hsource with
    ⟨targetTape, htransport, htransportTarget⟩
  refine ⟨targetTape, htransport, ?_⟩
  exact Tape.Equiv.trans
    (Section53BooleanContextOneSymbolRound.Machine.bounceTape_input_equiv word)
    htransportTarget

theorem raw_none_to_ready_run_exact
    (word : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        { state := Control.raw none (.finish .gate)
          tape := Tape.input word } =
      some
        { state := Control.ready
          tape :=
            Section53BooleanContextOneSymbolRound.Machine.bounceTape
              (Tape.input word) } := by
  cases word <;> rfl

theorem raw_some_to_locator_run_exact
    (saved : MachineCodeSymbol)
    (word : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        { state := Control.raw (some saved) (.finish .gate)
          tape := Tape.input word } =
      some
        { state := Control.locate saved .fourth .fuel
          tape :=
            Section53BooleanContextOneSymbolRound.Machine.bounceTape
              (Tape.input word) } := by
  cases word <;> rfl

theorem raw_none_to_ready_computes_of_tape_equiv
    (word : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv (Tape.input word) sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := Control.raw none (.finish .gate)
          tape := sourceTape }
        { state := Control.ready
          tape := targetTape } ∧
      Tape.Equiv (Tape.input word) targetTape := by
  have hrunExact := raw_none_to_ready_run_exact word
  have hrun := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrunExact)
  rcases computes_of_tape_equiv hrun hsource with
    ⟨targetTape, htransport, htransportTarget⟩
  refine ⟨targetTape, htransport, ?_⟩
  exact Tape.Equiv.trans
    (Section53BooleanContextOneSymbolRound.Machine.bounceTape_input_equiv word)
    htransportTarget

theorem raw_some_to_locator_computes_of_tape_equiv
    (saved : MachineCodeSymbol)
    (word : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv (Tape.input word) sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := Control.raw (some saved) (.finish .gate)
          tape := sourceTape }
        { state := Control.locate saved .fourth .fuel
          tape := targetTape } ∧
      Tape.Equiv (Tape.input word) targetTape := by
  have hrunExact := raw_some_to_locator_run_exact saved word
  have hrun := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrunExact)
  rcases computes_of_tape_equiv hrun hsource with
    ⟨targetTape, htransport, htransportTarget⟩
  refine ⟨targetTape, htransport, ?_⟩
  exact Tape.Equiv.trans
    (Section53BooleanContextOneSymbolRound.Machine.bounceTape_input_equiv word)
    htransportTarget

theorem some_saved_tail_computes
    (saved : MachineCodeSymbol)
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (sourceTape : Tape MachineCodeSymbol)
    (hnoHeader : Section53BooleanContextLocator.noHeader table)
    (hsource : Tape.Equiv
      (Tape.input
        (Section53BooleanContextOneSymbolRound.Machine.layoutWord
          fuel stateCount start halt rowCount table cells []))
      sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := Control.raw (some saved) (.finish .gate)
          tape := sourceTape }
        { state := Control.ready
          tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (Section53BooleanContextOneSymbolRound.Machine.layoutWord
            fuel stateCount start halt rowCount table
            (savedTailCells (some saved) cells) []))
        targetTape := by
  let cells4 : List (Option Bool) :=
    some (phaseBit saved .fourth) :: cells
  let cells3 : List (Option Bool) :=
    some (phaseBit saved .third) :: cells4
  let cells2 : List (Option Bool) :=
    some (phaseBit saved .second) :: cells3
  let word0 :=
    Section53BooleanContextOneSymbolRound.Machine.layoutWord
      fuel stateCount start halt rowCount table cells []
  rcases raw_some_to_locator_computes_of_tape_equiv
      saved word0 sourceTape (by simpa [word0] using hsource) with
    ⟨tape0, hrawBounce, htape0⟩
  have hfourthSource : Tape.Equiv
      (Section53BooleanContextOneSymbolRound.Machine.locatorSource
        fuel stateCount start halt rowCount table cells []).tape
      tape0 := by
    rw [Section53BooleanContextOneSymbolRound.Machine.locatorSource_tape_eq_input]
    simpa [word0] using htape0
  rcases phase_computes_of_tape_equiv saved .fourth
      fuel stateCount start halt rowCount table cells [] tape0
      hnoHeader hfourthSource with
    ⟨tape1, hfourth, htape1⟩
  rcases prepend_to_locator_computes_of_tape_equiv
      saved .fourth .third rfl
      (Section53BooleanContextOneSymbolRound.Machine.layoutWord
        fuel stateCount start halt rowCount table cells4 [])
      tape1 (by simpa [cells4] using htape1) with
    ⟨tape2, hfourthBounce, htape2⟩
  have hthirdSource : Tape.Equiv
      (Section53BooleanContextOneSymbolRound.Machine.locatorSource
        fuel stateCount start halt rowCount table cells4 []).tape
      tape2 := by
    rw [Section53BooleanContextOneSymbolRound.Machine.locatorSource_tape_eq_input]
    exact htape2
  rcases phase_computes_of_tape_equiv saved .third
      fuel stateCount start halt rowCount table cells4 [] tape2
      hnoHeader hthirdSource with
    ⟨tape3, hthird, htape3⟩
  rcases prepend_to_locator_computes_of_tape_equiv
      saved .third .second rfl
      (Section53BooleanContextOneSymbolRound.Machine.layoutWord
        fuel stateCount start halt rowCount table cells3 [])
      tape3 (by simpa [cells3] using htape3) with
    ⟨tape4, hthirdBounce, htape4⟩
  have hsecondSource : Tape.Equiv
      (Section53BooleanContextOneSymbolRound.Machine.locatorSource
        fuel stateCount start halt rowCount table cells3 []).tape
      tape4 := by
    rw [Section53BooleanContextOneSymbolRound.Machine.locatorSource_tape_eq_input]
    exact htape4
  rcases phase_computes_of_tape_equiv saved .second
      fuel stateCount start halt rowCount table cells3 [] tape4
      hnoHeader hsecondSource with
    ⟨tape5, hsecond, htape5⟩
  rcases prepend_to_ready_computes_of_tape_equiv saved
      (Section53BooleanContextOneSymbolRound.Machine.layoutWord
        fuel stateCount start halt rowCount table cells2 [])
      tape5 (by simpa [cells2] using htape5) with
    ⟨targetTape, hfinish, htarget⟩
  refine ⟨targetTape, ?_, ?_⟩
  · exact TuringMachine.computes_trans hrawBounce
      (TuringMachine.computes_trans hfourth
        (TuringMachine.computes_trans hfourthBounce
          (TuringMachine.computes_trans hthird
            (TuringMachine.computes_trans hthirdBounce
              (TuringMachine.computes_trans hsecond hfinish)))))
  · simpa [cells2, cells3, cells4, savedTailCells, phaseBit] using htarget

theorem full_saved_tail_computes
    (saved : Option MachineCodeSymbol)
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (raw : Word MachineCodeSymbol)
    (hnoHeader : Section53BooleanContextLocator.noHeader table) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := entry saved
          tape :=
            (RawTailPop.sourceConfig
              (Section53BooleanContextOneSymbolRound.Machine.materializerBaseLeftRev
                fuel stateCount start halt rowCount table)
              [] raw).tape }
        { state := Control.ready
          tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (Section53BooleanContextOneSymbolRound.Machine.layoutWord
            fuel stateCount start halt rowCount table
            (savedTailCells saved
              ((MachineDescription.encodeCodeWordAsInput raw).map some))
            []))
        targetTape := by
  rcases Section53BooleanContextRawTailDriver.Driver.full_tail_computes
      fuel stateCount start halt rowCount table [] raw hnoHeader with
    ⟨rawTargetTape, hrawInner, hrawShape⟩
  have hraw := raw_computes_lift saved hrawInner
  have hrawShape' : Tape.Equiv
      (Tape.input
        (Section53BooleanContextOneSymbolRound.Machine.layoutWord
          fuel stateCount start halt rowCount table
          ((MachineDescription.encodeCodeWordAsInput raw).map some) []))
      rawTargetTape := by
    let encoded : List (Option Bool) :=
      (MachineDescription.encodeCodeWordAsInput raw).map some
    have hcells : List.append encoded [] = encoded :=
      List.append_nil encoded
    have hinput := congrArg
      (fun cells : List (Option Bool) =>
        Tape.input
          (Section53BooleanContextOneSymbolRound.Machine.layoutWord
            fuel stateCount start halt rowCount table cells []))
      hcells
    exact hinput ▸ hrawShape
  cases saved with
  | none =>
      rcases raw_none_to_ready_computes_of_tape_equiv
          (Section53BooleanContextOneSymbolRound.Machine.layoutWord
            fuel stateCount start halt rowCount table
            ((MachineDescription.encodeCodeWordAsInput raw).map some) [])
          rawTargetTape hrawShape' with
        ⟨targetTape, hfinish, htarget⟩
      refine ⟨targetTape, ?_, ?_⟩
      · simpa [entry, rawConfig,
          Section53BooleanContextRawTailDriver.Driver.roundConfig,
          Section53BooleanContextRawTailDriver.Driver.machine,
          Section53BooleanContextOneSymbolRound.Machine.popConfig,
          Section53BooleanContextOneSymbolRound.Machine.machine,
          RawTailPop.sourceConfig, RawTailPop.locateConfig,
          RawTailPop.machine, PayloadLocator.sourceConfig] using
            TuringMachine.computes_trans hraw hfinish
      · simpa [savedTailCells] using htarget
  | some saved =>
      rcases some_saved_tail_computes saved
          fuel stateCount start halt rowCount table
          ((MachineDescription.encodeCodeWordAsInput raw).map some)
          rawTargetTape hnoHeader hrawShape' with
        ⟨targetTape, hfinish, htarget⟩
      refine ⟨targetTape, ?_, htarget⟩
      simpa [entry, rawConfig,
        Section53BooleanContextRawTailDriver.Driver.roundConfig,
        Section53BooleanContextRawTailDriver.Driver.machine,
        Section53BooleanContextOneSymbolRound.Machine.popConfig,
        Section53BooleanContextOneSymbolRound.Machine.machine,
        RawTailPop.sourceConfig, RawTailPop.locateConfig,
        RawTailPop.machine, PayloadLocator.sourceConfig] using
          TuringMachine.computes_trans hraw hfinish


end Machine

end Section53BooleanContextSavedCloseout

end Computability
end FoC
