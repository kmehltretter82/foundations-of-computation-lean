import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.CandidateReset

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.MainRollover

open Languages
open ExactFuel.StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open Scheduler.Rollover

abbrev CandidateControl := Scheduler.CandidateReset.Control
abbrev SplitResetControl := Scheduler.Advance.ExhaustedSplitReset.Control
abbrev LocatorControl := Scheduler.Rollover.Locator.Control

abbrev candidateMachine := Scheduler.CandidateReset.machine
abbrev splitResetMachine := Scheduler.Advance.ExhaustedSplitReset.machine

def growBuffer : InsertBlock.Buffer :=
  Scheduler.Advance.GrowResetInsertion.buffer

inductive Mode where
  | unbounded
  | bounded
deriving DecidableEq

namespace Mode

def finite : Foundation.FiniteType Mode where
  elems := [.unbounded, .bounded]
  complete := by
    intro mode
    cases mode <;> simp

end Mode

inductive Control where
  | header
  | geometry
  | budget
  | insertRound (mode : Mode) (inner : InsertRestagedMachine.Control)
  | locateFuel (mode : Mode) (inner : LocatorControl)
  | resetFuel (mode : Mode) (inner : SplitResetControl)
  | growFuel (mode : Mode) (inner : InsertRestagedMachine.Control)
  | locateOuter (mode : Mode) (inner : LocatorControl)
  | resetOuter (mode : Mode) (inner : SplitResetControl)
  | growOuter (mode : Mode) (inner : InsertRestagedMachine.Control)
  | rewindOuter (mode : Mode) (inner : RewindWord.Control)
  | locateInner (mode : Mode) (inner : LocatorControl)
  | resetInner (mode : Mode) (inner : SplitResetControl)
  | growInner (mode : Mode) (inner : InsertRestagedMachine.Control)
  | rewindInner (mode : Mode) (inner : RewindWord.Control)
  | candidates (inner : CandidateControl)
  | halt
deriving DecidableEq

namespace Control

inductive Tag where
  | header
  | geometry
  | budget
  | insertRound
  | locateFuel
  | resetFuel
  | growFuel
  | locateOuter
  | resetOuter
  | growOuter
  | rewindOuter
  | locateInner
  | resetInner
  | growInner
  | rewindInner
  | candidates
  | halt
deriving DecidableEq

namespace Tag

def finite : Foundation.FiniteType Tag where
  elems := [.header, .geometry, .budget, .insertRound, .locateFuel,
    .resetFuel, .growFuel, .locateOuter, .resetOuter, .growOuter,
    .rewindOuter, .locateInner, .resetInner, .growInner, .rewindInner,
    .candidates, .halt]
  complete := by
    intro tag
    cases tag <;> simp

end Tag

def CodeState : Tag -> Type
  | .header => Unit
  | .geometry => Unit
  | .budget => Unit
  | .insertRound => Mode × InsertRestagedMachine.Control
  | .locateFuel => Mode × LocatorControl
  | .resetFuel => Mode × SplitResetControl
  | .growFuel => Mode × InsertRestagedMachine.Control
  | .locateOuter => Mode × LocatorControl
  | .resetOuter => Mode × SplitResetControl
  | .growOuter => Mode × InsertRestagedMachine.Control
  | .rewindOuter => Mode × RewindWord.Control
  | .locateInner => Mode × LocatorControl
  | .resetInner => Mode × SplitResetControl
  | .growInner => Mode × InsertRestagedMachine.Control
  | .rewindInner => Mode × RewindWord.Control
  | .candidates => CandidateControl
  | .halt => Unit

def codeStateFinite : (tag : Tag) -> Foundation.FiniteType (CodeState tag)
  | .header => Foundation.FiniteType.unit
  | .geometry => Foundation.FiniteType.unit
  | .budget => Foundation.FiniteType.unit
  | .insertRound => Foundation.FiniteType.prod Mode.finite
      InsertRestagedMachine.Control.finite
  | .locateFuel => Foundation.FiniteType.prod Mode.finite
      Scheduler.Rollover.Locator.Control.finite
  | .resetFuel => Foundation.FiniteType.prod Mode.finite
      Scheduler.Advance.ExhaustedSplitReset.Control.finite
  | .growFuel => Foundation.FiniteType.prod Mode.finite
      InsertRestagedMachine.Control.finite
  | .locateOuter => Foundation.FiniteType.prod Mode.finite
      Scheduler.Rollover.Locator.Control.finite
  | .resetOuter => Foundation.FiniteType.prod Mode.finite
      Scheduler.Advance.ExhaustedSplitReset.Control.finite
  | .growOuter => Foundation.FiniteType.prod Mode.finite
      InsertRestagedMachine.Control.finite
  | .rewindOuter => Foundation.FiniteType.prod Mode.finite
      RewindWord.Control.finite
  | .locateInner => Foundation.FiniteType.prod Mode.finite
      Scheduler.Rollover.Locator.Control.finite
  | .resetInner => Foundation.FiniteType.prod Mode.finite
      Scheduler.Advance.ExhaustedSplitReset.Control.finite
  | .growInner => Foundation.FiniteType.prod Mode.finite
      InsertRestagedMachine.Control.finite
  | .rewindInner => Foundation.FiniteType.prod Mode.finite
      RewindWord.Control.finite
  | .candidates => Scheduler.CandidateReset.Control.finite
  | .halt => Foundation.FiniteType.unit

abbrev Code := Sigma CodeState

def decode : Code -> Control
  | ⟨.header, ()⟩ => .header
  | ⟨.geometry, ()⟩ => .geometry
  | ⟨.budget, ()⟩ => .budget
  | ⟨.insertRound, (mode, inner)⟩ => .insertRound mode inner
  | ⟨.locateFuel, (mode, inner)⟩ => .locateFuel mode inner
  | ⟨.resetFuel, (mode, inner)⟩ => .resetFuel mode inner
  | ⟨.growFuel, (mode, inner)⟩ => .growFuel mode inner
  | ⟨.locateOuter, (mode, inner)⟩ => .locateOuter mode inner
  | ⟨.resetOuter, (mode, inner)⟩ => .resetOuter mode inner
  | ⟨.growOuter, (mode, inner)⟩ => .growOuter mode inner
  | ⟨.rewindOuter, (mode, inner)⟩ => .rewindOuter mode inner
  | ⟨.locateInner, (mode, inner)⟩ => .locateInner mode inner
  | ⟨.resetInner, (mode, inner)⟩ => .resetInner mode inner
  | ⟨.growInner, (mode, inner)⟩ => .growInner mode inner
  | ⟨.rewindInner, (mode, inner)⟩ => .rewindInner mode inner
  | ⟨.candidates, inner⟩ => .candidates inner
  | ⟨.halt, ()⟩ => .halt

def encode : Control -> Code
  | .header => ⟨.header, ()⟩
  | .geometry => ⟨.geometry, ()⟩
  | .budget => ⟨.budget, ()⟩
  | .insertRound mode inner => ⟨.insertRound, (mode, inner)⟩
  | .locateFuel mode inner => ⟨.locateFuel, (mode, inner)⟩
  | .resetFuel mode inner => ⟨.resetFuel, (mode, inner)⟩
  | .growFuel mode inner => ⟨.growFuel, (mode, inner)⟩
  | .locateOuter mode inner => ⟨.locateOuter, (mode, inner)⟩
  | .resetOuter mode inner => ⟨.resetOuter, (mode, inner)⟩
  | .growOuter mode inner => ⟨.growOuter, (mode, inner)⟩
  | .rewindOuter mode inner => ⟨.rewindOuter, (mode, inner)⟩
  | .locateInner mode inner => ⟨.locateInner, (mode, inner)⟩
  | .resetInner mode inner => ⟨.resetInner, (mode, inner)⟩
  | .growInner mode inner => ⟨.growInner, (mode, inner)⟩
  | .rewindInner mode inner => ⟨.rewindInner, (mode, inner)⟩
  | .candidates inner => ⟨.candidates, inner⟩
  | .halt => ⟨.halt, ()⟩

theorem decode_encode (control : Control) :
    decode (encode control) = control := by
  cases control <;> rfl

def codeFinite : Foundation.FiniteType Code :=
  Foundation.FiniteType.sigma Tag.finite codeStateFinite

def finite : Foundation.FiniteType Control where
  elems := codeFinite.elems.map decode
  complete := by
    intro control
    exact List.mem_map.mpr
      ⟨encode control, codeFinite.complete (encode control), decode_encode control⟩

end Control

def mapAction (embed : inner -> Control) :
    Option (Option MachineCodeSymbol × Direction × inner) ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | none => none
  | some (write, direction, target) =>
      some (write, direction, embed target)

def insertRoundEmbed (mode : Mode) : InsertRestagedMachine.Control -> Control
  | .rewind .gate => .locateFuel mode .header
  | inner => .insertRound mode inner

def locateFuelEmbed (mode : Mode) : LocatorControl -> Control
  | .halt => .resetFuel mode splitResetMachine.start
  | inner => .locateFuel mode inner

def resetFuelEmbed (mode : Mode) : SplitResetControl -> Control
  | .halt => .growFuel mode (InsertRestagedMachine.machine growBuffer).start
  | inner => .resetFuel mode inner

def growFuelEmbed (mode : Mode) : InsertRestagedMachine.Control -> Control
  | .rewind .gate => .locateOuter mode .header
  | inner => .growFuel mode inner

def locateOuterEmbed (mode : Mode) : LocatorControl -> Control
  | .halt => .resetOuter mode splitResetMachine.start
  | inner => .locateOuter mode inner

def resetOuterEmbed (mode : Mode) : SplitResetControl -> Control
  | .halt =>
      match mode with
      | .unbounded =>
          .growOuter mode (InsertRestagedMachine.machine growBuffer).start
      | .bounded => .rewindOuter mode RewindWord.machine.start
  | inner => .resetOuter mode inner

def growOuterEmbed (mode : Mode) : InsertRestagedMachine.Control -> Control
  | .rewind .gate => .locateInner mode .header
  | inner => .growOuter mode inner

def rewindOuterEmbed (mode : Mode) : RewindWord.Control -> Control
  | .gate => .locateInner mode .header
  | inner => .rewindOuter mode inner

def locateInnerEmbed (mode : Mode) : LocatorControl -> Control
  | .halt => .resetInner mode splitResetMachine.start
  | inner => .locateInner mode inner

def resetInnerEmbed (mode : Mode) : SplitResetControl -> Control
  | .halt =>
      match mode with
      | .unbounded =>
          .growInner mode (InsertRestagedMachine.machine growBuffer).start
      | .bounded => .rewindInner mode RewindWord.machine.start
  | inner => .resetInner mode inner

def growInnerEmbed (mode : Mode) : InsertRestagedMachine.Control -> Control
  | .rewind .gate => .candidates candidateMachine.start
  | inner => .growInner mode inner

def rewindInnerEmbed (mode : Mode) : RewindWord.Control -> Control
  | .gate => .candidates candidateMachine.start
  | inner => .rewindInner mode inner

def candidatesEmbed : CandidateControl -> Control
  | .halt => .halt
  | inner => .candidates inner

def transition : Control -> Option MachineCodeSymbol ->
    Option (Option MachineCodeSymbol × Direction × Control)
  | .header, some .header =>
      some (some .header, Direction.right, .geometry)
  | .geometry, some .blank =>
      some (some .blank, Direction.right,
        .insertRound .unbounded
          (InsertRestagedMachine.machine growBuffer).start)
  | .geometry, some .zero =>
      some (some .zero, Direction.right, .budget)
  | .budget, some .tick =>
      some (some .tick, Direction.right, .budget)
  | .budget, some .done =>
      some (some .done, Direction.right,
        .insertRound .bounded
          (InsertRestagedMachine.machine growBuffer).start)
  | .insertRound mode inner, read =>
      mapAction (insertRoundEmbed mode)
        (InsertRestagedMachine.transition inner read)
  | .locateFuel mode inner, read =>
      mapAction (locateFuelEmbed mode)
        (Scheduler.Rollover.Locator.transition .fuel inner read)
  | .resetFuel mode inner, read =>
      mapAction (resetFuelEmbed mode)
        (Scheduler.Advance.ExhaustedSplitReset.transition inner read)
  | .growFuel mode inner, read =>
      mapAction (growFuelEmbed mode)
        (InsertRestagedMachine.transition inner read)
  | .locateOuter mode inner, read =>
      mapAction (locateOuterEmbed mode)
        (Scheduler.Rollover.Locator.transition .outer inner read)
  | .resetOuter mode inner, read =>
      mapAction (resetOuterEmbed mode)
        (Scheduler.Advance.ExhaustedSplitReset.transition inner read)
  | .growOuter mode inner, read =>
      mapAction (growOuterEmbed mode)
        (InsertRestagedMachine.transition inner read)
  | .rewindOuter mode inner, read =>
      mapAction (rewindOuterEmbed mode) (RewindWord.transition inner read)
  | .locateInner mode inner, read =>
      mapAction (locateInnerEmbed mode)
        (Scheduler.Rollover.Locator.transition .inner inner read)
  | .resetInner mode inner, read =>
      mapAction (resetInnerEmbed mode)
        (Scheduler.Advance.ExhaustedSplitReset.transition inner read)
  | .growInner mode inner, read =>
      mapAction (growInnerEmbed mode)
        (InsertRestagedMachine.transition inner read)
  | .rewindInner mode inner, read =>
      mapAction (rewindInnerEmbed mode) (RewindWord.transition inner read)
  | .candidates inner, read =>
      mapAction candidatesEmbed
        (Scheduler.CandidateReset.transition inner read)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .header
  halt := .halt
  transition := transition
  statesFinite := Control.finite

theorem step_of_mapped_transition
    {innerState : Type}
    (inner : TuringMachine MachineCodeSymbol innerState)
    (embed : innerState -> Control)
    (hmap : ∀ (state : innerState) (read : Option MachineCodeSymbol)
        (action : Option MachineCodeSymbol × Direction × innerState),
      inner.transition state read = some action ->
      transition (embed state) read = mapAction embed (some action))
    (source target : TuringMachine.Configuration MachineCodeSymbol innerState)
    (hstep : inner.stepConfig source = some target) :
    machine.stepConfig
        (TuringMachine.PhaseEmbedding.liftConfig embed source) =
      some (TuringMachine.PhaseEmbedding.liftConfig embed target) := by
  cases source with
  | mk state tape =>
      cases target with
      | mk targetState targetTape =>
          unfold TuringMachine.stepConfig at hstep ⊢
          dsimp [machine]
          simp only [TuringMachine.PhaseEmbedding.liftConfig]
          cases haction : inner.transition state (Tape.read tape) with
          | none =>
              rw [haction] at hstep
              contradiction
          | some action =>
              rcases action with ⟨write, direction, nextState⟩
              rw [haction] at hstep
              simp only at hstep
              have hmapped := hmap state (Tape.read tape)
                (write, direction, nextState) haction
              rw [hmapped]
              cases hstep
              rfl

theorem insertRound_map (mode : Mode)
    (state : InsertRestagedMachine.Control)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction ×
      InsertRestagedMachine.Control)
    (haction : (InsertRestagedMachine.machine growBuffer).transition
      state read = some action) :
    transition (insertRoundEmbed mode state) read =
      mapAction (insertRoundEmbed mode) (some action) := by
  cases state with
  | edit inner =>
      cases inner <;>
        simp_all [InsertRestagedMachine.machine,
          InsertRestagedMachine.transition, transition, insertRoundEmbed,
          mapAction]
  | rewind inner =>
      cases inner <;>
        simp_all [InsertRestagedMachine.machine,
          InsertRestagedMachine.transition, RewindWord.transition,
          transition, insertRoundEmbed, mapAction]

theorem insertRound_step_of_some (mode : Mode)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control)
    (hstep : (InsertRestagedMachine.machine growBuffer).stepConfig source =
      some target) :
    machine.stepConfig
        (TuringMachine.PhaseEmbedding.liftConfig
          (insertRoundEmbed mode) source) =
      some (TuringMachine.PhaseEmbedding.liftConfig
        (insertRoundEmbed mode) target) := by
  exact step_of_mapped_transition
    (InsertRestagedMachine.machine growBuffer) (insertRoundEmbed mode)
    (insertRound_map mode) source target hstep

theorem insertRound_run_of_eq_some (mode : Mode) {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control}
    (hrun : (InsertRestagedMachine.machine growBuffer).runConfigExact?
      steps source = some target) :
    machine.runConfigExact? steps
        (TuringMachine.PhaseEmbedding.liftConfig
          (insertRoundEmbed mode) source) =
      some (TuringMachine.PhaseEmbedding.liftConfig
        (insertRoundEmbed mode) target) := by
  exact TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    (insertRoundEmbed mode) (insertRound_step_of_some mode) hrun

theorem growFuel_map (mode : Mode)
    (state : InsertRestagedMachine.Control)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction ×
      InsertRestagedMachine.Control)
    (haction : (InsertRestagedMachine.machine growBuffer).transition
      state read = some action) :
    transition (growFuelEmbed mode state) read =
      mapAction (growFuelEmbed mode) (some action) := by
  cases state with
  | edit inner =>
      cases inner <;>
        simp_all [InsertRestagedMachine.machine,
          InsertRestagedMachine.transition, transition, growFuelEmbed,
          mapAction]
  | rewind inner =>
      cases inner <;>
        simp_all [InsertRestagedMachine.machine,
          InsertRestagedMachine.transition, RewindWord.transition,
          transition, growFuelEmbed, mapAction]

theorem growOuter_map (mode : Mode)
    (state : InsertRestagedMachine.Control)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction ×
      InsertRestagedMachine.Control)
    (haction : (InsertRestagedMachine.machine growBuffer).transition
      state read = some action) :
    transition (growOuterEmbed mode state) read =
      mapAction (growOuterEmbed mode) (some action) := by
  cases state with
  | edit inner =>
      cases inner <;>
        simp_all [InsertRestagedMachine.machine,
          InsertRestagedMachine.transition, transition, growOuterEmbed,
          mapAction]
  | rewind inner =>
      cases inner <;>
        simp_all [InsertRestagedMachine.machine,
          InsertRestagedMachine.transition, RewindWord.transition,
          transition, growOuterEmbed, mapAction]

theorem growInner_map (mode : Mode)
    (state : InsertRestagedMachine.Control)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction ×
      InsertRestagedMachine.Control)
    (haction : (InsertRestagedMachine.machine growBuffer).transition
      state read = some action) :
    transition (growInnerEmbed mode state) read =
      mapAction (growInnerEmbed mode) (some action) := by
  cases state with
  | edit inner =>
      cases inner <;>
        simp_all [InsertRestagedMachine.machine,
          InsertRestagedMachine.transition, transition, growInnerEmbed,
          mapAction]
  | rewind inner =>
      cases inner <;>
        simp_all [InsertRestagedMachine.machine,
          InsertRestagedMachine.transition, RewindWord.transition,
          transition, growInnerEmbed, mapAction]

theorem locateFuel_map (mode : Mode) (state : LocatorControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × LocatorControl)
    (haction : (Scheduler.Rollover.Locator.machine .fuel).transition
      state read = some action) :
    transition (locateFuelEmbed mode state) read =
      mapAction (locateFuelEmbed mode) (some action) := by
  cases state <;>
    simp_all [Scheduler.Rollover.Locator.machine,
      Scheduler.Rollover.Locator.transition,
      transition, locateFuelEmbed, mapAction]

theorem locateOuter_map (mode : Mode) (state : LocatorControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × LocatorControl)
    (haction : (Scheduler.Rollover.Locator.machine .outer).transition
      state read = some action) :
    transition (locateOuterEmbed mode state) read =
      mapAction (locateOuterEmbed mode) (some action) := by
  cases state <;>
    simp_all [Scheduler.Rollover.Locator.machine,
      Scheduler.Rollover.Locator.transition,
      transition, locateOuterEmbed, mapAction]

theorem locateInner_map (mode : Mode) (state : LocatorControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × LocatorControl)
    (haction : (Scheduler.Rollover.Locator.machine .inner).transition
      state read = some action) :
    transition (locateInnerEmbed mode state) read =
      mapAction (locateInnerEmbed mode) (some action) := by
  cases state <;>
    simp_all [Scheduler.Rollover.Locator.machine,
      Scheduler.Rollover.Locator.transition,
      transition, locateInnerEmbed, mapAction]

theorem resetFuel_map (mode : Mode) (state : SplitResetControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × SplitResetControl)
    (haction : splitResetMachine.transition state read = some action) :
    transition (resetFuelEmbed mode state) read =
      mapAction (resetFuelEmbed mode) (some action) := by
  cases state <;>
    simp_all [splitResetMachine,
      Scheduler.Advance.ExhaustedSplitReset.machine,
      Scheduler.Advance.ExhaustedSplitReset.transition,
      transition, resetFuelEmbed, mapAction]

theorem resetOuter_map (mode : Mode) (state : SplitResetControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × SplitResetControl)
    (haction : splitResetMachine.transition state read = some action) :
    transition (resetOuterEmbed mode state) read =
      mapAction (resetOuterEmbed mode) (some action) := by
  cases mode <;> cases state <;>
    simp_all [splitResetMachine,
      Scheduler.Advance.ExhaustedSplitReset.machine,
      Scheduler.Advance.ExhaustedSplitReset.transition,
      transition, resetOuterEmbed, mapAction]

theorem resetInner_map (mode : Mode) (state : SplitResetControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × SplitResetControl)
    (haction : splitResetMachine.transition state read = some action) :
    transition (resetInnerEmbed mode state) read =
      mapAction (resetInnerEmbed mode) (some action) := by
  cases mode <;> cases state <;>
    simp_all [splitResetMachine,
      Scheduler.Advance.ExhaustedSplitReset.machine,
      Scheduler.Advance.ExhaustedSplitReset.transition,
      transition, resetInnerEmbed, mapAction]

theorem rewindOuter_map (mode : Mode) (state : RewindWord.Control)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × RewindWord.Control)
    (haction : RewindWord.machine.transition state read = some action) :
    transition (rewindOuterEmbed mode state) read =
      mapAction (rewindOuterEmbed mode) (some action) := by
  cases state <;>
    simp_all [RewindWord.machine, RewindWord.transition,
      transition, rewindOuterEmbed, mapAction]

theorem rewindInner_map (mode : Mode) (state : RewindWord.Control)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × RewindWord.Control)
    (haction : RewindWord.machine.transition state read = some action) :
    transition (rewindInnerEmbed mode state) read =
      mapAction (rewindInnerEmbed mode) (some action) := by
  cases state <;>
    simp_all [RewindWord.machine, RewindWord.transition,
      transition, rewindInnerEmbed, mapAction]

theorem candidates_map (state : CandidateControl)
    (read : Option MachineCodeSymbol)
    (action : Option MachineCodeSymbol × Direction × CandidateControl)
    (haction : candidateMachine.transition state read = some action) :
    transition (candidatesEmbed state) read =
      mapAction candidatesEmbed (some action) := by
  cases state with
  | locate field inner =>
      cases field <;> cases inner <;>
        simp_all [candidateMachine, Scheduler.CandidateReset.machine,
          Scheduler.CandidateReset.transition,
          Scheduler.CandidateReset.mapAction,
          transition, candidatesEmbed, mapAction]
  | delete field inner =>
      cases field <;> cases inner with
      | edit editInner =>
          cases editInner <;>
            simp_all [candidateMachine, Scheduler.CandidateReset.machine,
              Scheduler.CandidateReset.transition,
              Scheduler.CandidateReset.mapAction,
              transition, candidatesEmbed, mapAction]
      | rewind rewindInner =>
          cases rewindInner <;>
            simp_all [candidateMachine, Scheduler.CandidateReset.machine,
              Scheduler.CandidateReset.transition,
              Scheduler.CandidateReset.mapAction,
              transition, candidatesEmbed, mapAction]
  | bounceRight field =>
      cases field <;>
        simp_all [candidateMachine, Scheduler.CandidateReset.machine,
          Scheduler.CandidateReset.transition,
          transition, candidatesEmbed, mapAction]
  | halt =>
      simp_all [candidateMachine, Scheduler.CandidateReset.machine,
        Scheduler.CandidateReset.transition]

theorem computes_lift_exact_from_equiv
    {innerState : Type}
    (inner : TuringMachine MachineCodeSymbol innerState)
    (embed : innerState -> Control)
    (hmap : ∀ (state : innerState) (read : Option MachineCodeSymbol)
        (action : Option MachineCodeSymbol × Direction × innerState),
      inner.transition state read = some action ->
      transition (embed state) read = mapAction embed (some action))
    {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol innerState}
    {tape : Tape MachineCodeSymbol}
    (hrun : inner.runConfigExact? steps source = some target)
    (htape : Tape.Equiv source.tape tape) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        (TuringMachine.PhaseEmbedding.liftConfig embed
          { state := source.state, tape := tape })
        (TuringMachine.PhaseEmbedding.liftConfig embed
          { state := target.state, tape := targetTape }) ∧
      Tape.Equiv target.tape targetTape := by
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hrun htape with
    ⟨⟨targetState, targetTape⟩, hactual, hstate, htape'⟩
  simp only at hstate
  subst targetState
  have houter :=
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      embed (step_of_mapped_transition inner embed hmap) hactual
  exact ⟨targetTape,
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp houter),
    htape'⟩

theorem computes_lift
    {innerState : Type}
    (inner : TuringMachine MachineCodeSymbol innerState)
    (embed : innerState -> Control)
    (hmap : ∀ (state : innerState) (read : Option MachineCodeSymbol)
        (action : Option MachineCodeSymbol × Direction × innerState),
      inner.transition state read = some action ->
      transition (embed state) read = mapAction embed (some action))
    {source target : TuringMachine.Configuration MachineCodeSymbol innerState}
    (hrun : TuringMachine.Computes inner source target) :
    TuringMachine.Computes machine
      (TuringMachine.PhaseEmbedding.liftConfig embed source)
      (TuringMachine.PhaseEmbedding.liftConfig embed target) := by
  rcases TuringMachine.computes_to_computesIn hrun with
    ⟨steps, hrunIn⟩
  apply TuringMachine.computesIn_to_computes
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
    embed (step_of_mapped_transition inner embed hmap)
  exact TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr hrunIn

def rolloverTail (round bound : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  Scheduler.SplitLayout.encodeSplitAppend round 0
    (Scheduler.SplitLayout.encodeSplitAppend bound 0
      (Scheduler.SplitLayout.encodeSplitAppend bound 0
        (Scheduler.SplitLayout.candidateMarker ::
          MachineDescription.encodeNatAppend round
            (GeneratedCode.nestedStageCode input bound bound))))

def roundInsertSource (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control :=
  InsertRestagedMachine.editConfig
    (InsertBlock.config growBuffer
      (Scheduler.Rollover.Locator.geometryPrefixRev geometry)
      (MachineDescription.encodeNatAppend round
        (rolloverTail round bound input)))

def roundInsertTarget (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control :=
  InsertRestagedMachine.rewindConfig
    (RewindWord.gateConfig
      (Scheduler.Rollover.afterRoundWord geometry round bound input) 0)

theorem round_insert_output
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    PhysicalBranch.insertOutput growBuffer
        (Scheduler.Rollover.Locator.geometryPrefixRev geometry)
        (MachineDescription.encodeNatAppend round
          (rolloverTail round bound input)) =
      Scheduler.Rollover.afterRoundWord geometry round bound input := by
  cases geometry with
  | unbounded =>
      simp [PhysicalBranch.insertOutput, growBuffer,
        Scheduler.Advance.GrowResetInsertion.buffer,
        Scheduler.Advance.GrowResetInsertion.buffer,
        InsertBlock.singletonBuffer, rolloverTail,
        Scheduler.Rollover.Locator.geometryPrefixRev,
        Scheduler.Layout.encodeGeometryAppend,
        Scheduler.Rollover.afterRoundWord,
        Scheduler.Rollover.word,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, List.reverse_append,
        List.append_assoc]
  | bounded budget =>
      simp [PhysicalBranch.insertOutput, growBuffer,
        Scheduler.Advance.GrowResetInsertion.buffer,
        InsertBlock.singletonBuffer, rolloverTail,
        Scheduler.Rollover.Locator.geometryPrefixRev,
        Scheduler.Layout.encodeGeometryAppend,
        Scheduler.Rollover.afterRoundWord,
        Scheduler.Rollover.word,
        Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
        Scheduler.Advance.ExhaustedSplitReset.ticks,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, List.reverse_append,
        List.append_assoc]

def roundInsertSteps (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) : Nat :=
  InsertRestagedMachine.runSteps growBuffer
    (Scheduler.Rollover.Locator.geometryPrefixRev geometry)
    (MachineDescription.encodeNatAppend round
      (rolloverTail round bound input))

theorem round_insert_exact
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    (InsertRestagedMachine.machine growBuffer).runConfigExact?
        (roundInsertSteps geometry round bound input)
        (roundInsertSource geometry round bound input) =
      some (roundInsertTarget geometry round bound input) := by
  unfold roundInsertSteps roundInsertSource roundInsertTarget
  rw [InsertRestagedMachine.run_exact growBuffer
    (Scheduler.Rollover.Locator.geometryPrefixRev geometry)
    (MachineDescription.encodeNatAppend round
      (rolloverTail round bound input))]
  · rw [round_insert_output]
  · simp [growBuffer, Scheduler.Advance.GrowResetInsertion.buffer,
      InsertBlock.singletonBuffer]

theorem header_step (rest : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .header
          tape := ExactFuel.StrictProbe.SerializedShift.cursorTape []
            (MachineCodeSymbol.header :: rest) } =
      some
        { state := .geometry
          tape := ExactFuel.StrictProbe.SerializedShift.cursorTape
            [MachineCodeSymbol.header] rest } := by
  cases rest <;> rfl

theorem geometry_unbounded_step (leftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .geometry
          tape := ExactFuel.StrictProbe.SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.blank :: rest) } =
      some (TuringMachine.PhaseEmbedding.liftConfig
        (insertRoundEmbed .unbounded)
        (InsertRestagedMachine.editConfig
          (InsertBlock.config growBuffer
            (MachineCodeSymbol.blank :: leftRev) rest))) := by
  cases leftRev <;> cases rest <;> rfl

theorem geometry_bounded_step (leftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .geometry
          tape := ExactFuel.StrictProbe.SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.zero :: rest) } =
      some
        { state := .budget
          tape := ExactFuel.StrictProbe.SerializedShift.cursorTape
            (MachineCodeSymbol.zero :: leftRev) rest } := by
  cases leftRev <;> cases rest <;> rfl

theorem budget_tick_step (leftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .budget
          tape := ExactFuel.StrictProbe.SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.tick :: rest) } =
      some
        { state := .budget
          tape := ExactFuel.StrictProbe.SerializedShift.cursorTape
            (MachineCodeSymbol.tick :: leftRev) rest } := by
  cases leftRev <;> cases rest <;> rfl

theorem budget_done_step (leftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .budget
          tape := ExactFuel.StrictProbe.SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.done :: rest) } =
      some (TuringMachine.PhaseEmbedding.liftConfig
        (insertRoundEmbed .bounded)
        (InsertRestagedMachine.editConfig
          (InsertBlock.config growBuffer
            (MachineCodeSymbol.done :: leftRev) rest))) := by
  cases leftRev <;> cases rest <;> rfl

theorem enter_round_unbounded_exact (round bound : Nat)
    (input : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        { state := machine.start
          tape := Tape.input
            (Scheduler.Rollover.sourceWord .unbounded round bound
              input) } =
      some (TuringMachine.PhaseEmbedding.liftConfig
        (insertRoundEmbed .unbounded)
        (roundInsertSource .unbounded round bound input)) := by
  rw [TuringMachine.runConfigExact?]
  rw [show machine.stepConfig
      { state := machine.start
        tape := Tape.input
          (Scheduler.Rollover.sourceWord .unbounded round bound
            input) } =
    some
      { state := .geometry
        tape := ExactFuel.StrictProbe.SerializedShift.cursorTape
          [MachineCodeSymbol.header]
          (Scheduler.Layout.encodeGeometryAppend .unbounded
            (MachineDescription.encodeNatAppend round
              (rolloverTail round bound input))) } by rfl]
  simp only
  rw [TuringMachine.runConfigExact?]
  rw [show machine.stepConfig
      { state := .geometry
        tape := ExactFuel.StrictProbe.SerializedShift.cursorTape
          [MachineCodeSymbol.header]
          (Scheduler.Layout.encodeGeometryAppend .unbounded
            (MachineDescription.encodeNatAppend round
              (rolloverTail round bound input))) } =
    some (TuringMachine.PhaseEmbedding.liftConfig
      (insertRoundEmbed .unbounded)
      (roundInsertSource .unbounded round bound input)) by
        simpa [Scheduler.Layout.encodeGeometryAppend,
          roundInsertSource,
          Scheduler.Rollover.Locator.geometryPrefixRev]
          using geometry_unbounded_step [MachineCodeSymbol.header]
            (MachineDescription.encodeNatAppend round
              (rolloverTail round bound input))]
  rfl

theorem ticks_append_tick (count : Nat)
    (suffix : Word MachineCodeSymbol) :
    List.append
        (List.replicate count MachineCodeSymbol.tick)
        (MachineCodeSymbol.tick :: suffix) =
      MachineCodeSymbol.tick ::
        List.append (List.replicate count MachineCodeSymbol.tick) suffix := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change MachineCodeSymbol.tick ::
          (List.append (List.replicate count MachineCodeSymbol.tick)
            (MachineCodeSymbol.tick :: suffix)) =
        MachineCodeSymbol.tick :: MachineCodeSymbol.tick ::
          List.append (List.replicate count MachineCodeSymbol.tick) suffix
      exact congrArg (List.cons MachineCodeSymbol.tick) ih

theorem budget_run_exact (budget : Nat)
    (leftRev rest : Word MachineCodeSymbol) :
    machine.runConfigExact? (budget + 1)
        { state := .budget
          tape := ExactFuel.StrictProbe.SerializedShift.cursorTape leftRev
            (MachineDescription.encodeNatAppend budget rest) } =
      some (TuringMachine.PhaseEmbedding.liftConfig
        (insertRoundEmbed .bounded)
        (InsertRestagedMachine.editConfig
          (InsertBlock.config growBuffer
            (Scheduler.Rollover.Locator.natPrefixRev budget leftRev)
            rest))) := by
  induction budget generalizing leftRev with
  | zero =>
      change machine.runConfigExact? 1
        { state := .budget
          tape := ExactFuel.StrictProbe.SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.done :: rest) } = _
      rw [TuringMachine.runConfigExact?]
      rw [budget_done_step]
      simp [Scheduler.Rollover.Locator.natPrefixRev,
        Scheduler.Advance.ExhaustedSplitReset.ticks]
      rfl
  | succ budget ih =>
      change machine.runConfigExact? ((budget + 1) + 1)
        { state := .budget
          tape := ExactFuel.StrictProbe.SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.tick ::
              MachineDescription.encodeNatAppend budget rest) } = _
      rw [TuringMachine.runConfigExact?]
      rw [budget_tick_step]
      simp only
      rw [ih (MachineCodeSymbol.tick :: leftRev)]
      congr 4
      unfold Scheduler.Rollover.Locator.natPrefixRev
        Scheduler.Advance.ExhaustedSplitReset.ticks
      simp only [List.replicate_succ]
      rw [ticks_append_tick]
      rfl

theorem enter_round_bounded_exact (budget round : Nat)
    (input : Word MachineCodeSymbol) :
    machine.runConfigExact? (2 + (budget + 1))
        { state := machine.start
          tape := Tape.input
            (Scheduler.Rollover.sourceWord (.bounded budget) round
              budget input) } =
      some (TuringMachine.PhaseEmbedding.liftConfig
        (insertRoundEmbed .bounded)
        (roundInsertSource (.bounded budget) round budget input)) := by
  have hsource :
      Scheduler.Rollover.sourceWord (.bounded budget) round budget input =
        Scheduler.Rollover.word (.bounded budget) round
          round 0 budget 0 budget 0 round budget budget input := rfl
  rw [hsource]
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append machine 2
    (budget + 1)]
  change (match machine.runConfigExact? 2
      { state := .header
        tape := ExactFuel.StrictProbe.SerializedShift.cursorTape []
          (MachineCodeSymbol.header :: MachineCodeSymbol.zero ::
            MachineDescription.encodeNatAppend budget
              (MachineDescription.encodeNatAppend round
                (rolloverTail round budget input))) } with
    | none => none
    | some middle => machine.runConfigExact? (budget + 1) middle) = _
  rw [TuringMachine.runConfigExact?]
  rw [header_step]
  simp only
  rw [TuringMachine.runConfigExact?]
  rw [geometry_bounded_step]
  change machine.runConfigExact? (budget + 1)
    { state := .budget
      tape := ExactFuel.StrictProbe.SerializedShift.cursorTape
        [MachineCodeSymbol.zero, MachineCodeSymbol.header]
        (MachineDescription.encodeNatAppend budget
          (MachineDescription.encodeNatAppend round
            (rolloverTail round budget input))) } = _
  rw [budget_run_exact]
  congr 4
  simp [roundInsertSource,
    Scheduler.Rollover.Locator.geometryPrefixRev,
    Scheduler.Rollover.Locator.natPrefixRev,
    Scheduler.Layout.encodeGeometryAppend,
    Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
    Scheduler.Advance.ExhaustedSplitReset.ticks,
    MachineDescription.encodeNatAppend, List.reverse_append,
    List.append_assoc]

def roundPhaseStepsUnbounded (round bound : Nat)
    (input : Word MachineCodeSymbol) : Nat :=
  2 + roundInsertSteps .unbounded round bound input

theorem round_phase_unbounded_exact (round bound : Nat)
    (input : Word MachineCodeSymbol) :
    machine.runConfigExact? (roundPhaseStepsUnbounded round bound input)
        { state := machine.start
          tape := Tape.input
            (Scheduler.Rollover.sourceWord .unbounded round bound
              input) } =
      some (TuringMachine.PhaseEmbedding.liftConfig
        (insertRoundEmbed .unbounded)
        (roundInsertTarget .unbounded round bound input)) := by
  unfold roundPhaseStepsUnbounded
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append machine 2
    (roundInsertSteps .unbounded round bound input)]
  rw [enter_round_unbounded_exact]
  simp only
  rw [insertRound_run_of_eq_some .unbounded
    (round_insert_exact .unbounded round bound input)]

def roundPhaseStepsBounded (budget round : Nat)
    (input : Word MachineCodeSymbol) : Nat :=
  (2 + (budget + 1)) +
    roundInsertSteps (.bounded budget) round budget input

theorem round_phase_bounded_exact (budget round : Nat)
    (input : Word MachineCodeSymbol) :
    machine.runConfigExact? (roundPhaseStepsBounded budget round input)
        { state := machine.start
          tape := Tape.input
            (Scheduler.Rollover.sourceWord (.bounded budget) round
              budget input) } =
      some (TuringMachine.PhaseEmbedding.liftConfig
        (insertRoundEmbed .bounded)
        (roundInsertTarget (.bounded budget) round budget input)) := by
  unfold roundPhaseStepsBounded
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append machine
    (2 + (budget + 1))
    (roundInsertSteps (.bounded budget) round budget input)]
  rw [enter_round_bounded_exact]
  simp only
  rw [insertRound_run_of_eq_some .bounded
    (round_insert_exact (.bounded budget) round budget input)]

theorem round_phase_unbounded_target_equiv (round bound : Nat)
    (input : Word MachineCodeSymbol) :
    Tape.Equiv
      (TuringMachine.PhaseEmbedding.liftConfig
        (insertRoundEmbed .unbounded)
        (roundInsertTarget .unbounded round bound input)).tape
      (Tape.input
        (Scheduler.Rollover.afterRoundWord .unbounded round bound
          input)) := by
  exact RewindWord.gateTape_equiv_input
    (Scheduler.Rollover.afterRoundWord .unbounded round bound input) 0

theorem round_phase_bounded_target_equiv (budget round : Nat)
    (input : Word MachineCodeSymbol) :
    Tape.Equiv
      (TuringMachine.PhaseEmbedding.liftConfig
        (insertRoundEmbed .bounded)
        (roundInsertTarget (.bounded budget) round budget input)).tape
      (Tape.input
        (Scheduler.Rollover.afterRoundWord (.bounded budget) round
          budget input)) := by
  exact RewindWord.gateTape_equiv_input
    (Scheduler.Rollover.afterRoundWord (.bounded budget) round budget
      input) 0

def fuelSuffix (round bound : Nat) (input : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  Scheduler.SplitLayout.encodeSplitAppend bound 0
    (Scheduler.SplitLayout.encodeSplitAppend bound 0
      (Scheduler.SplitLayout.candidateMarker ::
        MachineDescription.encodeNatAppend round
          (GeneratedCode.nestedStageCode input bound bound)))

theorem rolloverTail_eq_fuel_split (round bound : Nat)
    (input : Word MachineCodeSymbol) :
    rolloverTail round bound input =
      Scheduler.SplitLayout.encodeSplitAppend round 0
        (fuelSuffix round bound input) := by
  rfl

def fuelBaseRev (geometry : Scheduler.Layout.Geometry)
    (round : Nat) : Word MachineCodeSymbol :=
  List.append
    (Scheduler.Advance.ExhaustedSplitReset.ticks (round + 1))
    (Scheduler.Rollover.Locator.geometryPrefixRev geometry)

def fuelLocatorSource (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol LocatorControl :=
  Scheduler.Rollover.Locator.config .header []
    (Scheduler.Rollover.afterRoundWord geometry round bound input)

def fuelLocatorTarget (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol LocatorControl :=
  Scheduler.Rollover.Locator.config .halt
    (Scheduler.Rollover.Locator.natPrefixRev (round + 1)
      (Scheduler.Rollover.Locator.geometryPrefixRev geometry))
    (Scheduler.SplitLayout.encodeSplitAppend round 0
      (fuelSuffix round bound input))

def fuelLocateSteps (geometry : Scheduler.Layout.Geometry)
    (round : Nat) : Nat :=
  Scheduler.Rollover.Locator.geometrySteps geometry +
    ((round + 1) + 1)

theorem locate_fuel_main_exact
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    (Scheduler.Rollover.Locator.machine .fuel).runConfigExact?
        (fuelLocateSteps geometry round)
        (fuelLocatorSource geometry round bound input) =
      some (fuelLocatorTarget geometry round bound input) := by
  unfold fuelLocateSteps fuelLocatorSource fuelLocatorTarget
  rw [ExactFuel.StrictProbe.InitialMaterializer.ExactRun.append
    (Scheduler.Rollover.Locator.machine .fuel)
    (Scheduler.Rollover.Locator.geometrySteps geometry)
    ((round + 1) + 1)]
  rw [show Scheduler.Rollover.afterRoundWord geometry round bound input =
      List.cons MachineCodeSymbol.header
        (Scheduler.Layout.encodeGeometryAppend geometry
          (MachineDescription.encodeNatAppend (round + 1)
            (Scheduler.SplitLayout.encodeSplitAppend round 0
              (fuelSuffix round bound input)))) by rfl]
  unfold Scheduler.Rollover.Locator.geometrySteps
  rw [Scheduler.Rollover.Locator.geometry_to_round_exact .fuel geometry
    (MachineDescription.encodeNatAppend (round + 1)
      (Scheduler.SplitLayout.encodeSplitAppend round 0
        (fuelSuffix round bound input))) (by decide)]
  simp only
  unfold Scheduler.Rollover.Locator.geometryPrefixRev
  rw [Scheduler.Rollover.Locator.nat_run_exact .fuel .round .halt
    (round + 1)
    (MachineCodeSymbol.header ::
      Scheduler.Layout.encodeGeometryAppend geometry
        ([] : Word MachineCodeSymbol)).reverse
    (Scheduler.SplitLayout.encodeSplitAppend round 0
      (fuelSuffix round bound input)) (by rfl) (by rfl)]
  rfl

def fuelResetSource (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol SplitResetControl :=
  Scheduler.Advance.ExhaustedSplitReset.sourceConfig round
    (fuelBaseRev geometry round) (fuelSuffix round bound input)

def fuelResetTarget (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol SplitResetControl :=
  Scheduler.Advance.ExhaustedSplitReset.targetConfig round
    (fuelBaseRev geometry round) (fuelSuffix round bound input)

theorem fuelLocatorTarget_tape_eq_resetSource
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    (fuelLocatorTarget geometry round bound input).tape =
      (fuelResetSource geometry round bound input).tape := by
  rfl

theorem fuel_reset_exact
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    splitResetMachine.runConfigExact?
        (Scheduler.Advance.ExhaustedSplitReset.runSteps round)
        (fuelResetSource geometry round bound input) =
      some (fuelResetTarget geometry round bound input) := by
  exact Scheduler.Advance.ExhaustedSplitReset.run_exact round
    (fuelBaseRev geometry round) (fuelSuffix round bound input)

def fuelGrowSource (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control :=
  Scheduler.Advance.GrowResetInsertion.sourceConfig round
    (fuelBaseRev geometry round) (fuelSuffix round bound input)

def fuelGrowTarget (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      InsertRestagedMachine.Control :=
  InsertRestagedMachine.rewindConfig
    (RewindWord.gateConfig
      (Scheduler.Rollover.afterFuelWord geometry round bound input) 0)

theorem fuelResetTarget_tape_eq_growSource
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    (fuelResetTarget geometry round bound input).tape =
      (fuelGrowSource geometry round bound input).tape := by
  rfl

theorem fuel_grow_output
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    Scheduler.Advance.GrowResetInsertion.outputWord round
        (fuelBaseRev geometry round) (fuelSuffix round bound input) =
      Scheduler.Rollover.afterFuelWord geometry round bound input := by
  cases geometry with
  | unbounded =>
      simp [Scheduler.Advance.GrowResetInsertion.outputWord,
        fuelBaseRev, fuelSuffix,
        Scheduler.Rollover.Locator.geometryPrefixRev,
        Scheduler.Layout.encodeGeometryAppend,
        Scheduler.Rollover.afterFuelWord,
        Scheduler.Rollover.word,
        Scheduler.SplitLayout.encodeSplitAppend,
        Scheduler.Advance.ExhaustedSplitReset.ticks,
        Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
        MachineDescription.encodeNatAppend, List.reverse_append,
        List.append_assoc]
  | bounded budget =>
      simp [Scheduler.Advance.GrowResetInsertion.outputWord,
        fuelBaseRev, fuelSuffix,
        Scheduler.Rollover.Locator.geometryPrefixRev,
        Scheduler.Layout.encodeGeometryAppend,
        Scheduler.Rollover.afterFuelWord,
        Scheduler.Rollover.word,
        Scheduler.SplitLayout.encodeSplitAppend,
        Scheduler.Advance.ExhaustedSplitReset.ticks,
        Scheduler.Advance.ExhaustedSplitReset.encodeNat_eq_ticks_done,
        MachineDescription.encodeNatAppend, List.reverse_append,
        List.append_assoc]

theorem fuel_grow_exact
    (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol) :
    (InsertRestagedMachine.machine growBuffer).runConfigExact?
        (Scheduler.Advance.GrowResetInsertion.runSteps round
          (fuelBaseRev geometry round) (fuelSuffix round bound input))
        (fuelGrowSource geometry round bound input) =
      some (fuelGrowTarget geometry round bound input) := by
  unfold fuelGrowSource fuelGrowTarget growBuffer
  rw [Scheduler.Advance.GrowResetInsertion.run_exact round
    (fuelBaseRev geometry round) (fuelSuffix round bound input)]
  change some (InsertRestagedMachine.rewindConfig
      (RewindWord.gateConfig
        (Scheduler.Advance.GrowResetInsertion.outputWord round
          (fuelBaseRev geometry round) (fuelSuffix round bound input)) 0)) = _
  rw [fuel_grow_output]

theorem fuel_phase
    (mode : Mode) (geometry : Scheduler.Layout.Geometry)
    (round bound : Nat) (input : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input
        (Scheduler.Rollover.afterRoundWord geometry round bound input))
      sourceTape) :
    ∃ targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
        { state := .locateFuel mode .header, tape := sourceTape }
        { state := .locateOuter mode .header, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (Scheduler.Rollover.afterFuelWord geometry round bound input))
        targetTape := by
  rcases computes_lift_exact_from_equiv
      (Scheduler.Rollover.Locator.machine .fuel)
      (locateFuelEmbed mode) (locateFuel_map mode)
      (locate_fuel_main_exact geometry round bound input) hsource with
    ⟨locatedTape, hlocate, hlocated⟩
  have hresetSource : Tape.Equiv
      (fuelResetSource geometry round bound input).tape locatedTape := by
    rw [← fuelLocatorTarget_tape_eq_resetSource]
    exact hlocated
  rcases computes_lift_exact_from_equiv splitResetMachine
      (resetFuelEmbed mode) (resetFuel_map mode)
      (fuel_reset_exact geometry round bound input) hresetSource with
    ⟨resetTape, hreset, hresetTape⟩
  have hgrowSource : Tape.Equiv
      (fuelGrowSource geometry round bound input).tape resetTape := by
    rw [← fuelResetTarget_tape_eq_growSource]
    exact hresetTape
  rcases computes_lift_exact_from_equiv
      (InsertRestagedMachine.machine growBuffer)
      (growFuelEmbed mode) (growFuel_map mode)
      (fuel_grow_exact geometry round bound input) hgrowSource with
    ⟨targetTape, hgrow, htarget⟩
  refine ⟨targetTape,
    TuringMachine.computes_trans hlocate
      (TuringMachine.computes_trans hreset hgrow), ?_⟩
  exact Tape.Equiv.trans
    (Tape.Equiv.symm
      (RewindWord.gateTape_equiv_input
        (Scheduler.Rollover.afterFuelWord geometry round bound input)
        0)) htarget

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.MainRollover
