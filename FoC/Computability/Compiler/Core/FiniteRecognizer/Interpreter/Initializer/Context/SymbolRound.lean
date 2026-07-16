import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.Context.TailRound

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.BooleanContextOneSymbolRound

open FiniteRecognizer ExactFuel StrictProbe
open FiniteRecognizer.Interpreter.InitializerFrontier
open FiniteRecognizer.Interpreter.RuntimeEncodedList
open FiniteRecognizer.Interpreter.BooleanContextMaterializer
open FiniteRecognizer.Interpreter.BooleanContextLocator
open FiniteRecognizer.Interpreter.BooleanContextRawTail
open ExactFuel.StrictProbe.SerializedFieldComposer

inductive BitPhase where
  | fourth
  | third
  | second
  | first
deriving DecidableEq

namespace BitPhase

def elems : List BitPhase := [.fourth, .third, .second, .first]

def finite : Foundation.FiniteType BitPhase where
  elems := elems
  complete := by
    intro phase
    cases phase <;> simp [elems]

end BitPhase

def codeSymbolSecondBit : MachineCodeSymbol -> Bool
  | MachineCodeSymbol.header
  | MachineCodeSymbol.transition
  | MachineCodeSymbol.tick
  | MachineCodeSymbol.done
  | MachineCodeSymbol.moveRight => false
  | MachineCodeSymbol.blank
  | MachineCodeSymbol.zero
  | MachineCodeSymbol.one
  | MachineCodeSymbol.moveLeft => true

def codeSymbolThirdBit : MachineCodeSymbol -> Bool
  | MachineCodeSymbol.tick
  | MachineCodeSymbol.done
  | MachineCodeSymbol.one
  | MachineCodeSymbol.moveLeft => true
  | _ => false

def codeSymbolFourthBit : MachineCodeSymbol -> Bool
  | MachineCodeSymbol.transition
  | MachineCodeSymbol.done
  | MachineCodeSymbol.zero
  | MachineCodeSymbol.moveLeft => true
  | _ => false

def phaseBit
    (symbol : MachineCodeSymbol) : BitPhase -> Bool
  | .fourth => codeSymbolFourthBit symbol
  | .third => codeSymbolThirdBit symbol
  | .second => codeSymbolSecondBit symbol
  | .first => codeSymbolFirstBit symbol

def nextPhase : BitPhase -> Option BitPhase
  | .fourth => some .third
  | .third => some .second
  | .second => some .first
  | .first => none

theorem encoded_symbol_bits_exact
    (symbol : MachineCodeSymbol) :
    MachineDescription.encodeCodeSymbolAsInput symbol =
      [codeSymbolFirstBit symbol, codeSymbolSecondBit symbol,
        codeSymbolThirdBit symbol, codeSymbolFourthBit symbol] := by
  cases symbol <;> rfl

theorem four_prepend_cells_exact
    (symbol : MachineCodeSymbol)
    (cells : List (Option Bool)) :
    some (phaseBit symbol .first) ::
      some (phaseBit symbol .second) ::
      some (phaseBit symbol .third) ::
      some (phaseBit symbol .fourth) :: cells =
    List.append
      ((MachineDescription.encodeCodeSymbolAsInput symbol).map some)
      cells := by
  cases symbol <;> rfl

namespace Machine

inductive Control where
  | pop (inner : RawTailPop.Control)
  | popBounce (saved : MachineCodeSymbol) (phase : BitPhase)
  | locate (saved : MachineCodeSymbol) (phase : BitPhase)
      (inner : FiniteRecognizer.Interpreter.BooleanContextLocator.Control)
  | locatorBounce (saved : MachineCodeSymbol) (phase : BitPhase)
  | prepend (saved : MachineCodeSymbol) (phase : BitPhase)
      (inner : Prepend.Control)
  | prependBounce (saved : MachineCodeSymbol) (phase : BitPhase)
  | finishBounce
  | ready
deriving DecidableEq

namespace Control

def savedPhaseControls
    (f : MachineCodeSymbol -> BitPhase -> Control) : List Control :=
  MachineCodeSymbol.finite.elems.flatMap fun saved =>
    BitPhase.finite.elems.map (f saved)

def savedPhaseInnerControls
    {inner : Type}
    (innerElems : List inner)
    (f : MachineCodeSymbol -> BitPhase -> inner -> Control) : List Control :=
  MachineCodeSymbol.finite.elems.flatMap fun saved =>
    BitPhase.finite.elems.flatMap fun phase =>
      innerElems.map (f saved phase)

theorem savedPhaseControls_complete
    (f : MachineCodeSymbol -> BitPhase -> Control)
    (saved : MachineCodeSymbol) (phase : BitPhase) :
    f saved phase ∈ savedPhaseControls f := by
  apply List.mem_flatMap.mpr
  refine ⟨saved, MachineCodeSymbol.finite.complete saved, ?_⟩
  apply List.mem_map.mpr
  exact ⟨phase, BitPhase.finite.complete phase, rfl⟩

theorem savedPhaseInnerControls_complete
    {inner : Type}
    (innerElems : List inner)
    (hinner : forall value : inner, value ∈ innerElems)
    (f : MachineCodeSymbol -> BitPhase -> inner -> Control)
    (saved : MachineCodeSymbol) (phase : BitPhase) (value : inner) :
    f saved phase value ∈ savedPhaseInnerControls innerElems f := by
  apply List.mem_flatMap.mpr
  refine ⟨saved, MachineCodeSymbol.finite.complete saved, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨phase, BitPhase.finite.complete phase, ?_⟩
  apply List.mem_map.mpr
  exact ⟨value, hinner value, rfl⟩

def elems : List Control :=
  RawTailPop.Control.finite.elems.map Control.pop ++
    savedPhaseControls Control.popBounce ++
    savedPhaseInnerControls
      FiniteRecognizer.Interpreter.BooleanContextLocator.Control.finite.elems Control.locate ++
    savedPhaseControls Control.locatorBounce ++
    savedPhaseInnerControls Prepend.Control.finite.elems Control.prepend ++
    savedPhaseControls Control.prependBounce ++
    [Control.finishBounce, Control.ready]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | pop inner =>
        simp [elems, RawTailPop.Control.finite.complete inner]
    | popBounce saved phase =>
        have h := savedPhaseControls_complete Control.popBounce saved phase
        simp [elems, h]
    | locate saved phase inner =>
        have h := savedPhaseInnerControls_complete
          FiniteRecognizer.Interpreter.BooleanContextLocator.Control.finite.elems
          FiniteRecognizer.Interpreter.BooleanContextLocator.Control.finite.complete
          Control.locate saved phase inner
        simp [elems, h]
    | locatorBounce saved phase =>
        have h := savedPhaseControls_complete Control.locatorBounce
          saved phase
        simp [elems, h]
    | prepend saved phase inner =>
        have h := savedPhaseInnerControls_complete
          Prepend.Control.finite.elems Prepend.Control.finite.complete
          Control.prepend saved phase inner
        simp [elems, h]
    | prependBounce saved phase =>
        have h := savedPhaseControls_complete Control.prependBounce
          saved phase
        simp [elems, h]
    | finishBounce => simp [elems]
    | ready => simp [elems]

end Control

def mapPopAction :
    (Option MachineCodeSymbol × Direction × RawTailPop.Control) ->
      (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, next) => (write, direction, .pop next)

def mapLocatorAction
    (saved : MachineCodeSymbol) (phase : BitPhase) :
    (Option MachineCodeSymbol × Direction ×
      FiniteRecognizer.Interpreter.BooleanContextLocator.Control) ->
      (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, next) =>
      (write, direction, .locate saved phase next)

def mapPrependAction
    (saved : MachineCodeSymbol) (phase : BitPhase) :
    (Option MachineCodeSymbol × Direction × Prepend.Control) ->
      (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, next) =>
      (write, direction, .prepend saved phase next)

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .pop (.ready saved), read =>
      some (read, Direction.left, .popBounce saved .fourth)
  | .pop inner, read =>
      Option.map mapPopAction (RawTailPop.transition inner read)
  | .popBounce saved phase, read =>
      some (read, Direction.right,
        .locate saved phase .fuel)
  | .locate saved phase .ready, read =>
      some (read, Direction.left, .locatorBounce saved phase)
  | .locate saved phase inner, read =>
      Option.map (mapLocatorAction saved phase)
        (FiniteRecognizer.Interpreter.BooleanContextLocator.transition inner read)
  | .locatorBounce saved phase, read =>
      some (read, Direction.right,
        .prepend saved phase (.locate .count))
  | .prepend _saved .first (.insert (.rewind .gate)), read =>
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
      some (read, Direction.right,
        .locate saved phase .fuel)
  | .finishBounce, read =>
      some (read, Direction.right, .ready)
  | .ready, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .pop RawTailPop.machine.start
  halt := .ready
  transition := transition
  statesFinite := Control.finite

def popConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      RawTailPop.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .pop config.state, tape := config.tape }

def locatorConfig
    (saved : MachineCodeSymbol) (phase : BitPhase)
    (config : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.BooleanContextLocator.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .locate saved phase config.state, tape := config.tape }

def prependConfig
    (saved : MachineCodeSymbol) (phase : BitPhase)
    (config : TuringMachine.Configuration MachineCodeSymbol
      Prepend.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .prepend saved phase config.state, tape := config.tape }

theorem pop_step_of_some
    (source target : TuringMachine.Configuration MachineCodeSymbol
      RawTailPop.Control)
    (hstep : RawTailPop.machine.stepConfig source = some target) :
    machine.stepConfig (popConfig source) = some (popConfig target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [RawTailPop.machine] at hstep
      cases htransition : RawTailPop.transition inner (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          cases hstep
          have hnot : forall saved, inner ≠ RawTailPop.Control.ready saved := by
            intro saved heq
            subst inner
            simp [RawTailPop.transition] at htransition
          simp [machine, transition, popConfig, mapPopAction, htransition]

theorem pop_run_of_some :
    forall (steps : Nat)
      (source target : TuringMachine.Configuration MachineCodeSymbol
        RawTailPop.Control),
      RawTailPop.machine.runConfigExact? steps source = some target ->
        machine.runConfigExact? steps (popConfig source) =
          some (popConfig target) := by
  intro steps
  induction steps with
  | zero =>
      intro source target hrun
      simpa [TuringMachine.runConfigExact?] using
        congrArg popConfig (Option.some.inj hrun)
  | succ steps ih =>
      intro source target hrun
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep : RawTailPop.machine.stepConfig source with
      | none => simp [hstep] at hrun
      | some next =>
          simp only [hstep] at hrun
          rw [pop_step_of_some source next hstep]
          simp only
          exact ih next target hrun

theorem pop_computes_lift
    {source target : TuringMachine.Configuration MachineCodeSymbol
      RawTailPop.Control}
    (hrun : TuringMachine.Computes RawTailPop.machine source target) :
    TuringMachine.Computes machine
      (popConfig source) (popConfig target) := by
  induction hrun with
  | refl config => exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (pop_step_of_some _ _
            (TuringMachine.stepConfig_eq_some_iff_step.mpr hstep)))
        ih

theorem locator_step_of_some
    (saved : MachineCodeSymbol) (phase : BitPhase)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.BooleanContextLocator.Control)
    (hstep : FiniteRecognizer.Interpreter.BooleanContextLocator.machine.stepConfig source =
      some target) :
    machine.stepConfig (locatorConfig saved phase source) =
      some (locatorConfig saved phase target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [FiniteRecognizer.Interpreter.BooleanContextLocator.machine] at hstep
      cases htransition :
          FiniteRecognizer.Interpreter.BooleanContextLocator.transition inner (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          cases hstep
          have hnot : inner ≠ FiniteRecognizer.Interpreter.BooleanContextLocator.Control.ready := by
            intro heq
            subst inner
            simp [FiniteRecognizer.Interpreter.BooleanContextLocator.transition] at htransition
          simp [machine, transition, locatorConfig, mapLocatorAction,
            htransition]

theorem locator_computes_lift
    (saved : MachineCodeSymbol) (phase : BitPhase)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      FiniteRecognizer.Interpreter.BooleanContextLocator.Control}
    (hrun : TuringMachine.Computes
      FiniteRecognizer.Interpreter.BooleanContextLocator.machine source target) :
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
    (saved : MachineCodeSymbol) (phase : BitPhase)
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
    (saved : MachineCodeSymbol) (phase : BitPhase) :
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

def materializerBaseLeftRev
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  FiniteRecognizer.Interpreter.BooleanContextLocator.rightCountBaseLeftRev
    fuel stateCount start halt rowCount table

def layoutWord
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (raw : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  FiniteRecognizer.Interpreter.BooleanContextLocator.locatorWord
    fuel stateCount start halt rowCount table cells.length
    (MachineDescription.encodeCellsAppend cells
      (MachineCodeSymbol.header :: raw))

def locatorSource
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (raw : Word MachineCodeSymbol) :=
  FiniteRecognizer.Interpreter.BooleanContextLocator.sourceConfig
    fuel stateCount start halt rowCount table cells.length
    (MachineDescription.encodeCellsAppend cells
      (MachineCodeSymbol.header :: raw))

def locatorTarget
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (raw : Word MachineCodeSymbol) :=
  FiniteRecognizer.Interpreter.BooleanContextLocator.targetConfig
    fuel stateCount start halt rowCount table cells.length
    (MachineDescription.encodeCellsAppend cells
      (MachineCodeSymbol.header :: raw))

theorem locatorSource_tape_eq_input
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (raw : Word MachineCodeSymbol) :
    (locatorSource fuel stateCount start halt rowCount table cells raw).tape =
      Tape.input
        (layoutWord fuel stateCount start halt rowCount table cells raw) := by
  cases fuel <;> rfl

theorem materializerBaseLeftRev_reverse
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol) :
    (materializerBaseLeftRev fuel stateCount start halt rowCount table).reverse =
      FiniteRecognizer.Interpreter.BooleanContextLocator.rightCountPrefix
        fuel stateCount start halt rowCount table := by
  unfold materializerBaseLeftRev
  exact List.reverse_reverse _

theorem layoutWord_eq_prepend_targetWord
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (raw : Word MachineCodeSymbol)
    (cell : Option Bool) :
    layoutWord fuel stateCount start halt rowCount table
        (cell :: cells) raw =
      Prepend.targetWord
        (materializerBaseLeftRev fuel stateCount start halt rowCount table)
        cells.length cell
        (MachineDescription.encodeCellsAppend cells
          (MachineCodeSymbol.header :: raw)) := by
  rw [prepend_targetWord_eq_encoded_list]
  rw [materializerBaseLeftRev_reverse]
  simp [layoutWord, FiniteRecognizer.Interpreter.BooleanContextLocator.locatorWord,
    FiniteRecognizer.Interpreter.BooleanContextLocator.rightCountPrefix,
    MachineDescription.encodeCellListAppend,
    MachineDescription.encodeNatAppend]

theorem popTargetWord_eq_layoutWord
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (raw : Word MachineCodeSymbol) :
    List.append
        (RawTailPop.wordBeforeRaw
          (materializerBaseLeftRev fuel stateCount start halt rowCount table)
          cells)
        raw =
      layoutWord fuel stateCount start halt rowCount table cells raw := by
  rw [RawTailPop.wordBeforeRaw, materializerBaseLeftRev_reverse]
  change
    Word.Concat
        (Word.Concat
          (FiniteRecognizer.Interpreter.BooleanContextLocator.rightCountPrefix
            fuel stateCount start halt rowCount table)
          (MachineDescription.encodeCellListAppend cells
            [MachineCodeSymbol.header]))
        raw =
      layoutWord fuel stateCount start halt rowCount table cells raw
  calc
    _ = Word.Concat
          (FiniteRecognizer.Interpreter.BooleanContextLocator.rightCountPrefix
            fuel stateCount start halt rowCount table)
          (Word.Concat
            (MachineDescription.encodeCellListAppend cells
              [MachineCodeSymbol.header]) raw) :=
      Word.concat_assoc _ _ _
    _ = Word.Concat
          (FiniteRecognizer.Interpreter.BooleanContextLocator.rightCountPrefix
            fuel stateCount start halt rowCount table)
          (MachineDescription.encodeCellListAppend cells
            (Word.Concat [MachineCodeSymbol.header] raw)) := by
      exact congrArg
        (Word.Concat
          (FiniteRecognizer.Interpreter.BooleanContextLocator.rightCountPrefix
            fuel stateCount start halt rowCount table))
        (encodeCellListAppend_append cells
          [MachineCodeSymbol.header] raw).symm
    _ = layoutWord fuel stateCount start halt rowCount table cells raw := by
      rfl

def bounceTape (tape : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.right (Tape.move Direction.left tape)

theorem bounceTape_input_equiv
    (word : Word MachineCodeSymbol) :
    Tape.Equiv (Tape.input word) (bounceTape (Tape.input word)) := by
  cases word with
  | nil =>
      simp [bounceTape, Tape.input, Tape.blank, Tape.move,
        Tape.moveLeft, Tape.moveRight, Tape.Equiv, Tape.dropTrailingNone]
  | cons first rest =>
      simp [bounceTape, Tape.input, Tape.move, Tape.moveLeft,
        Tape.moveRight, Tape.Equiv, Tape.dropTrailingNone]

def prependTerminal : Prepend.Control :=
  .insert (.rewind .gate)

theorem pop_to_locator_run_exact
    (saved : MachineCodeSymbol)
    (word : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (popConfig (RawTailPop.readyConfig saved word)) =
      some
        { state := Control.locate saved .fourth .fuel
          tape := bounceTape (RawTailPop.readyConfig saved word).tape } := by
  cases word <;> rfl

theorem locator_to_prepend_run_exact
    (saved : MachineCodeSymbol) (phase : BitPhase)
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

theorem materializerBaseLeftRev_ne_nil
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol) :
    materializerBaseLeftRev fuel stateCount start halt rowCount table ≠ [] := by
  intro hnil
  have hreverse := congrArg
    (fun word : Word MachineCodeSymbol => word.reverse) hnil
  rw [materializerBaseLeftRev_reverse] at hreverse
  cases fuel <;>
    simp [FiniteRecognizer.Interpreter.BooleanContextLocator.rightCountPrefix,
      FiniteRecognizer.Interpreter.BooleanContextLocator.parsedMetadataAppend,
      MachineDescription.encodeNatAppend,
      MachineDescription.encodeNat] at hreverse

theorem prepend_to_locator_run_exact
    (saved : MachineCodeSymbol)
    (phase next : BitPhase)
    (hnext : nextPhase phase = some next)
    (word : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        { state := Control.prepend saved phase prependTerminal
          tape := Tape.input word } =
      some
        { state := Control.locate saved next .fuel
          tape := bounceTape (Tape.input word) } := by
  cases phase <;> simp [nextPhase] at hnext
  all_goals cases hnext
  all_goals cases word <;> rfl

theorem prepend_to_ready_run_exact
    (saved : MachineCodeSymbol)
    (word : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        { state := Control.prepend saved .first prependTerminal
          tape := Tape.input word } =
      some
        { state := Control.ready
          tape := bounceTape (Tape.input word) } := by
  cases word <;> rfl

theorem phase_computes_of_tape_equiv
    (saved : MachineCodeSymbol) (phase : BitPhase)
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (raw : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hnoHeader : FiniteRecognizer.Interpreter.BooleanContextLocator.noHeader table)
    (hsource : Tape.Equiv
      (locatorSource fuel stateCount start halt rowCount table cells raw).tape
      sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := Control.locate saved phase .fuel
          tape := sourceTape }
        { state := Control.prepend saved phase prependTerminal
          tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (layoutWord fuel stateCount start halt rowCount table
            (some (phaseBit saved phase) :: cells) raw))
        targetTape := by
  let baseLeftRev :=
    materializerBaseLeftRev fuel stateCount start halt rowCount table
  let suffix := MachineDescription.encodeCellsAppend cells
    (MachineCodeSymbol.header :: raw)
  have hlocatorInner :=
    FiniteRecognizer.Interpreter.BooleanContextLocator.computes_to_right_count
      fuel stateCount start halt rowCount table cells.length suffix hnoHeader
  have hlocator := locator_computes_lift saved phase hlocatorInner
  have hbase : baseLeftRev ≠ [] := by
    exact materializerBaseLeftRev_ne_nil
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
  · simpa [locatorConfig, locatorSource,
      FiniteRecognizer.Interpreter.BooleanContextLocator.sourceConfig,
      FiniteRecognizer.Interpreter.BooleanContextLocator.config,
      prependConfig, prependTerminal] using htransport
  · rw [layoutWord_eq_prepend_targetWord]
    exact Tape.Equiv.trans htarget htransportTarget

theorem prepend_to_locator_computes_of_tape_equiv
    (saved : MachineCodeSymbol)
    (phase next : BitPhase)
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
  exact Tape.Equiv.trans (bounceTape_input_equiv word) htransportTarget

theorem prepend_to_ready_computes_of_tape_equiv
    (saved : MachineCodeSymbol)
    (word : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv (Tape.input word) sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := Control.prepend saved .first prependTerminal
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
  exact Tape.Equiv.trans (bounceTape_input_equiv word) htransportTarget

theorem pop_nonempty_to_locator_computes
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (rawPrefix : Word MachineCodeSymbol)
    (last : MachineCodeSymbol) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (popConfig
          (RawTailPop.sourceConfig
            (materializerBaseLeftRev
              fuel stateCount start halt rowCount table)
            cells (Word.Concat rawPrefix [last])))
        { state := Control.locate last .fourth .fuel
          tape := targetTape } ∧
      Tape.Equiv
        (locatorSource fuel stateCount start halt rowCount table
          cells rawPrefix).tape
        targetTape := by
  let baseLeftRev :=
    materializerBaseLeftRev fuel stateCount start halt rowCount table
  let word := Word.Concat
    (RawTailPop.wordBeforeRaw baseLeftRev cells) rawPrefix
  have hpopInnerExact := RawTailPop.nonempty_run_exact
    baseLeftRev cells rawPrefix last
  have hpopExact := pop_run_of_some _ _ _ hpopInnerExact
  have hpop := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hpopExact)
  have hbounceExact := pop_to_locator_run_exact last word
  have hbounce := TuringMachine.computesIn_to_computes
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hbounceExact)
  have hrun := TuringMachine.computes_trans hpop hbounce
  refine ⟨bounceTape (RawTailPop.readyConfig last word).tape, ?_, ?_⟩
  · simpa [baseLeftRev, word, Word.Concat] using hrun
  · have hready := RawTailPop.nonempty_target_equiv_input
      baseLeftRev cells rawPrefix last
    have hbounced : Tape.Equiv
        (bounceTape (RawTailPop.readyConfig last word).tape)
        (bounceTape (Tape.input word)) :=
      Tape.Equiv.move (Tape.Equiv.move hready Direction.left)
        Direction.right
    rw [locatorSource_tape_eq_input,
      ← popTargetWord_eq_layoutWord]
    exact Tape.Equiv.trans (bounceTape_input_equiv word)
      (Tape.Equiv.symm hbounced)

theorem nonempty_raw_symbol_round_computes
    (fuel stateCount start halt rowCount : Nat)
    (table : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (rawPrefix : Word MachineCodeSymbol)
    (last : MachineCodeSymbol)
    (hnoHeader : FiniteRecognizer.Interpreter.BooleanContextLocator.noHeader table) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (popConfig
          (RawTailPop.sourceConfig
            (materializerBaseLeftRev
              fuel stateCount start halt rowCount table)
            cells (Word.Concat rawPrefix [last])))
        { state := Control.ready
          tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (layoutWord fuel stateCount start halt rowCount table
            (List.append
              ((MachineDescription.encodeCodeSymbolAsInput last).map some)
              cells)
            rawPrefix))
        targetTape := by
  let cells4 : List (Option Bool) :=
    some (phaseBit last .fourth) :: cells
  let cells3 : List (Option Bool) :=
    some (phaseBit last .third) :: cells4
  let cells2 : List (Option Bool) :=
    some (phaseBit last .second) :: cells3
  let cells1 : List (Option Bool) :=
    some (phaseBit last .first) :: cells2
  rcases pop_nonempty_to_locator_computes
      fuel stateCount start halt rowCount table cells rawPrefix last with
    ⟨tape0, hpop, htape0⟩
  rcases phase_computes_of_tape_equiv last .fourth
      fuel stateCount start halt rowCount table cells rawPrefix tape0
      hnoHeader htape0 with
    ⟨tape1, hfourth, htape1⟩
  rcases prepend_to_locator_computes_of_tape_equiv
      last .fourth .third rfl
      (layoutWord fuel stateCount start halt rowCount table cells4 rawPrefix)
      tape1 (by simpa [cells4] using htape1) with
    ⟨tape2, hfourthBounce, htape2⟩
  have hthirdSource : Tape.Equiv
      (locatorSource fuel stateCount start halt rowCount table
        cells4 rawPrefix).tape tape2 := by
    rw [locatorSource_tape_eq_input]
    exact htape2
  rcases phase_computes_of_tape_equiv last .third
      fuel stateCount start halt rowCount table cells4 rawPrefix tape2
      hnoHeader hthirdSource with
    ⟨tape3, hthird, htape3⟩
  rcases prepend_to_locator_computes_of_tape_equiv
      last .third .second rfl
      (layoutWord fuel stateCount start halt rowCount table cells3 rawPrefix)
      tape3 (by simpa [cells3] using htape3) with
    ⟨tape4, hthirdBounce, htape4⟩
  have hsecondSource : Tape.Equiv
      (locatorSource fuel stateCount start halt rowCount table
        cells3 rawPrefix).tape tape4 := by
    rw [locatorSource_tape_eq_input]
    exact htape4
  rcases phase_computes_of_tape_equiv last .second
      fuel stateCount start halt rowCount table cells3 rawPrefix tape4
      hnoHeader hsecondSource with
    ⟨tape5, hsecond, htape5⟩
  rcases prepend_to_locator_computes_of_tape_equiv
      last .second .first rfl
      (layoutWord fuel stateCount start halt rowCount table cells2 rawPrefix)
      tape5 (by simpa [cells2] using htape5) with
    ⟨tape6, hsecondBounce, htape6⟩
  have hfirstSource : Tape.Equiv
      (locatorSource fuel stateCount start halt rowCount table
        cells2 rawPrefix).tape tape6 := by
    rw [locatorSource_tape_eq_input]
    exact htape6
  rcases phase_computes_of_tape_equiv last .first
      fuel stateCount start halt rowCount table cells2 rawPrefix tape6
      hnoHeader hfirstSource with
    ⟨tape7, hfirst, htape7⟩
  rcases prepend_to_ready_computes_of_tape_equiv last
      (layoutWord fuel stateCount start halt rowCount table cells1 rawPrefix)
      tape7 (by simpa [cells1] using htape7) with
    ⟨targetTape, hfinish, htarget⟩
  refine ⟨targetTape, ?_, ?_⟩
  · exact TuringMachine.computes_trans hpop
      (TuringMachine.computes_trans hfourth
        (TuringMachine.computes_trans hfourthBounce
          (TuringMachine.computes_trans hthird
            (TuringMachine.computes_trans hthirdBounce
              (TuringMachine.computes_trans hsecond
                (TuringMachine.computes_trans hsecondBounce
                  (TuringMachine.computes_trans hfirst hfinish)))))))
  · dsimp only [cells1, cells2, cells3, cells4] at htarget
    rw [four_prepend_cells_exact] at htarget
    exact htarget


end Machine

end FiniteRecognizer.Interpreter.BooleanContextOneSymbolRound

end Computability
end FoC
