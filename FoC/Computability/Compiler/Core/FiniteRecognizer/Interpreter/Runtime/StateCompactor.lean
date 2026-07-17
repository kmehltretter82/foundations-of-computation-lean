import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.RestagedEdits
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseRetarget
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.TapeEquivTransport
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Action

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.RuntimeStateCompactor

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer

/-!
Dynamic target-state compaction for the decoded-description interpreter.

The selected-row handoff exposes

`encodeNat target ++ header ++ encodeNat oldState ++ protectedSuffix`.

The machine keeps the selected finite write/move action in control, deletes
the header and the complete old-state unary field with the existing restaged
one-symbol deletion core, and returns to the start of

`encodeNat target ++ protectedSuffix`.
-/

abbrev Action := FiniteRecognizer.Interpreter.RuntimeAction.Action

namespace Action

def optionBools : List (Option Bool) :=
  [none, some false, some true]

def directions : List Direction :=
  [Direction.left, Direction.right]

theorem optionBools_complete (cell : Option Bool) :
    cell ∈ optionBools := by
  cases cell with
  | none => simp [optionBools]
  | some bit => cases bit <;> simp [optionBools]

theorem directions_complete (move : Direction) :
    move ∈ directions := by
  cases move <;> simp [directions]

def elems : List Action :=
  optionBools.flatMap
    (fun write =>
      directions.map
        (fun move => { write := write, move := move }))

def finite : Foundation.FiniteType Action where
  elems := elems
  complete := by
    intro action
    cases action with
    | mk write move =>
        simp [elems, optionBools_complete write,
          directions_complete move]

end Action

inductive OldDeleteOutcome where
  | continue
  | finish
deriving DecidableEq

namespace OldDeleteOutcome

def finite : Foundation.FiniteType OldDeleteOutcome where
  elems := [.continue, .finish]
  complete := by
    intro outcome
    cases outcome <;> simp

end OldDeleteOutcome

inductive Control where
  | seekMarker (action : Action)
  | atMarker (action : Action)
  | deleteMarker
      (action : Action) (inner : DeleteRestagedMachine.Control)
  | bounceMarker (action : Action)
  | seekOld (action : Action)
  | atOld (action : Action)
  | deleteOld
      (action : Action) (outcome : OldDeleteOutcome)
      (inner : DeleteRestagedMachine.Control)
  | bounceOld (action : Action) (outcome : OldDeleteOutcome)
  | ready (action : Action)
  | halt
deriving DecidableEq

namespace Control

def actionDeleteFinite : Foundation.FiniteType
    (Action × DeleteRestagedMachine.Control) :=
  Foundation.FiniteType.prod Action.finite
    DeleteRestagedMachine.Control.finite

def actionOutcomeFinite : Foundation.FiniteType
    (Action × OldDeleteOutcome) :=
  Foundation.FiniteType.prod Action.finite OldDeleteOutcome.finite

def actionOutcomeDeleteFinite : Foundation.FiniteType
    ((Action × OldDeleteOutcome) ×
      DeleteRestagedMachine.Control) :=
  Foundation.FiniteType.prod actionOutcomeFinite
    DeleteRestagedMachine.Control.finite

def elems : List Control :=
  List.append (Action.finite.elems.map Control.seekMarker)
    (List.append (Action.finite.elems.map Control.atMarker)
      (List.append
        (actionDeleteFinite.elems.map
          (fun payload => Control.deleteMarker payload.1 payload.2))
        (List.append (Action.finite.elems.map Control.bounceMarker)
          (List.append (Action.finite.elems.map Control.seekOld)
            (List.append (Action.finite.elems.map Control.atOld)
              (List.append
                (actionOutcomeDeleteFinite.elems.map
                  (fun payload =>
                    Control.deleteOld payload.1.1 payload.1.2 payload.2))
                (List.append
                  (actionOutcomeFinite.elems.map
                    (fun payload =>
                      Control.bounceOld payload.1 payload.2))
                  (List.append (Action.finite.elems.map Control.ready)
                    [.halt]))))))))

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | seekMarker action =>
        simp [elems, Action.finite.complete action]
    | atMarker action =>
        simp [elems, Action.finite.complete action]
    | deleteMarker action inner =>
        have h := actionDeleteFinite.complete (action, inner)
        simp [elems, h]
    | bounceMarker action =>
        simp [elems, Action.finite.complete action]
    | seekOld action =>
        simp [elems, Action.finite.complete action]
    | atOld action =>
        simp [elems, Action.finite.complete action]
    | deleteOld action outcome inner =>
        have h := actionOutcomeDeleteFinite.complete
          ((action, outcome), inner)
        have hm :
            Control.deleteOld action outcome inner ∈
              actionOutcomeDeleteFinite.elems.map
                (fun payload =>
                  Control.deleteOld payload.1.1 payload.1.2 payload.2) := by
          exact List.mem_map.mpr
            ⟨((action, outcome), inner), h, rfl⟩
        simp [elems, hm]
    | bounceOld action outcome =>
        have h := actionOutcomeFinite.complete (action, outcome)
        simp [elems, h]
    | ready action =>
        simp [elems, Action.finite.complete action]
    | halt =>
        simp [elems]

end Control

def mapAction (wrap : inner -> Control)
    (action : Option MachineCodeSymbol × Direction × inner) :
    Option MachineCodeSymbol × Direction × Control :=
  (action.1, action.2.1, wrap action.2.2)

def deleteStart : DeleteRestagedMachine.Control :=
  .edit (.erase (DeleteBlock.optionalGap none))

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .seekMarker action, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right,
        .seekMarker action)
  | .seekMarker action, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right,
        .atMarker action)
  | .atMarker action, some MachineCodeSymbol.header =>
      match DeleteRestagedMachine.transition none deleteStart
          (some MachineCodeSymbol.header) with
      | none => none
      | some innerAction =>
          some (mapAction (Control.deleteMarker action) innerAction)
  | .deleteMarker action (.rewind .gate), read =>
      some (read, Direction.right, .bounceMarker action)
  | .deleteMarker action inner, read =>
      match DeleteRestagedMachine.transition none inner read with
      | none => none
      | some innerAction =>
          some (mapAction (Control.deleteMarker action) innerAction)
  | .bounceMarker action, read =>
      some (read, Direction.left, .seekOld action)
  | .seekOld action, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right,
        .seekOld action)
  | .seekOld action, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right,
        .atOld action)
  | .atOld action, some MachineCodeSymbol.tick =>
      match DeleteRestagedMachine.transition none deleteStart
          (some MachineCodeSymbol.tick) with
      | none => none
      | some innerAction =>
          some
            (mapAction
              (Control.deleteOld action .continue) innerAction)
  | .atOld action, some MachineCodeSymbol.done =>
      match DeleteRestagedMachine.transition none deleteStart
          (some MachineCodeSymbol.done) with
      | none => none
      | some innerAction =>
          some
            (mapAction
              (Control.deleteOld action .finish) innerAction)
  | .deleteOld action outcome (.rewind .gate), read =>
      some (read, Direction.right, .bounceOld action outcome)
  | .deleteOld action outcome inner, read =>
      match DeleteRestagedMachine.transition none inner read with
      | none => none
      | some innerAction =>
          some
            (mapAction
              (Control.deleteOld action outcome) innerAction)
  | .bounceOld action .continue, read =>
      some (read, Direction.left, .seekOld action)
  | .bounceOld action .finish, read =>
      some (read, Direction.left, .ready action)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .seekMarker { write := none, move := Direction.left }
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def sourceWord
    (target oldState : Nat)
    (protectedSuffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend target
    (MachineCodeSymbol.header ::
      MachineDescription.encodeNatAppend oldState protectedSuffix)

def targetWord
    (target : Nat)
    (protectedSuffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend target protectedSuffix

def sourceConfig
    (action : Action) (target oldState : Nat)
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .seekMarker action
  tape := Tape.input (sourceWord target oldState protectedSuffix)

def targetConfig
    (action : Action) (target : Nat)
    (protectedSuffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .ready action
  tape := Tape.input (targetWord target protectedSuffix)

def cursorConfig
    (state : Control)
    (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := state
  tape := ExactFuel.StrictProbe.SerializedShift.cursorTape leftRev rest

theorem step_seekMarker_succ
    (action : Action)
    (leftRev tail : Word MachineCodeSymbol)
    (value : Nat) :
    machine.stepConfig
        (cursorConfig (.seekMarker action) leftRev
          (MachineDescription.encodeNatAppend (value + 1) tail)) =
      some
        (cursorConfig (.seekMarker action)
          (MachineCodeSymbol.tick :: leftRev)
          (MachineDescription.encodeNatAppend value tail)) := by
  cases value <;> rfl
  done

theorem seekMarker_run_exact
    (action : Action)
    (leftRev tail : Word MachineCodeSymbol)
    (value : Nat) :
    machine.runConfigExact? (value + 1)
        (cursorConfig (.seekMarker action) leftRev
          (MachineDescription.encodeNatAppend value tail)) =
      some
        (cursorConfig (.atMarker action)
          (List.append
            (MachineDescription.encodeNat value).reverse leftRev)
          tail) := by
  induction value generalizing leftRev with
  | zero =>
      cases tail <;> rfl
  | succ value ih =>
      rw [TuringMachine.runConfigExact?]
      rw [step_seekMarker_succ]
      simp only
      rw [ih]
      simp [MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc]
  done

theorem step_seekOld_succ
    (action : Action)
    (leftRev tail : Word MachineCodeSymbol)
    (value : Nat) :
    machine.stepConfig
        (cursorConfig (.seekOld action) leftRev
          (MachineDescription.encodeNatAppend (value + 1) tail)) =
      some
        (cursorConfig (.seekOld action)
          (MachineCodeSymbol.tick :: leftRev)
          (MachineDescription.encodeNatAppend value tail)) := by
  cases value <;> rfl
  done

theorem seekOld_run_exact
    (action : Action)
    (leftRev tail : Word MachineCodeSymbol)
    (value : Nat) :
    machine.runConfigExact? (value + 1)
        (cursorConfig (.seekOld action) leftRev
          (MachineDescription.encodeNatAppend value tail)) =
      some
        (cursorConfig (.atOld action)
          (List.append
            (MachineDescription.encodeNat value).reverse leftRev)
          tail) := by
  induction value generalizing leftRev with
  | zero =>
      cases tail <;> rfl
  | succ value ih =>
      rw [TuringMachine.runConfigExact?]
      rw [step_seekOld_succ]
      simp only
      rw [ih]
      simp [MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc]
  done

def deleteMarkerConfig (action : Action)
    (c : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig
    (Control.deleteMarker action) c

def deleteOldConfig (action : Action) (outcome : OldDeleteOutcome)
    (c : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig
    (Control.deleteOld action outcome) c

theorem deleteMarker_step_of_some
    (action : Action)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control)
    (hstep : (DeleteRestagedMachine.machine none).stepConfig c =
      some d) :
    machine.stepConfig (deleteMarkerConfig action c) =
      some (deleteMarkerConfig action d) := by
  cases c with
  | mk state tape =>
      cases d with
      | mk nextState nextTape =>
          unfold TuringMachine.stepConfig at hstep ⊢
          dsimp [DeleteRestagedMachine.machine] at hstep
          cases haction : DeleteRestagedMachine.transition none state
              (Tape.read tape) with
          | none =>
              rw [haction] at hstep
              contradiction
          | some innerAction =>
              rcases innerAction with ⟨write, direction, targetState⟩
              rw [haction] at hstep
              simp only at hstep
              cases hstep
              cases state with
              | edit inner =>
                  cases inner <;>
                    simp_all [machine, transition, deleteMarkerConfig,
                      mapAction,
                      TuringMachine.PhaseEmbedding.liftConfig]
              | rewind inner =>
                  cases inner <;>
                    simp_all [machine, transition, deleteMarkerConfig,
                      mapAction,
                      TuringMachine.PhaseEmbedding.liftConfig,
                      DeleteRestagedMachine.transition,
                      DeleteEndpointRewind.transition]
  done

theorem deleteOld_step_of_some
    (action : Action) (outcome : OldDeleteOutcome)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control)
    (hstep : (DeleteRestagedMachine.machine none).stepConfig c =
      some d) :
    machine.stepConfig (deleteOldConfig action outcome c) =
      some (deleteOldConfig action outcome d) := by
  cases c with
  | mk state tape =>
      cases d with
      | mk nextState nextTape =>
          unfold TuringMachine.stepConfig at hstep ⊢
          dsimp [DeleteRestagedMachine.machine] at hstep
          cases haction : DeleteRestagedMachine.transition none state
              (Tape.read tape) with
          | none =>
              rw [haction] at hstep
              contradiction
          | some innerAction =>
              rcases innerAction with ⟨write, direction, targetState⟩
              rw [haction] at hstep
              simp only at hstep
              cases hstep
              cases state with
              | edit inner =>
                  cases inner <;>
                    simp_all [machine, transition, deleteOldConfig,
                      mapAction,
                      TuringMachine.PhaseEmbedding.liftConfig]
              | rewind inner =>
                  cases inner <;>
                    simp_all [machine, transition, deleteOldConfig,
                      mapAction,
                      TuringMachine.PhaseEmbedding.liftConfig,
                      DeleteRestagedMachine.transition,
                      DeleteEndpointRewind.transition]
  done

theorem deleteMarker_run_of_eq_some
    (action : Action) {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control}
    (hrun : (DeleteRestagedMachine.machine none).runConfigExact?
      steps source = some target) :
    machine.runConfigExact? steps (deleteMarkerConfig action source) =
      some (deleteMarkerConfig action target) := by
  exact
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      (Control.deleteMarker action) (deleteMarker_step_of_some action)
      hrun
  done

theorem deleteOld_run_of_eq_some
    (action : Action) (outcome : OldDeleteOutcome) {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control}
    (hrun : (DeleteRestagedMachine.machine none).runConfigExact?
      steps source = some target) :
    machine.runConfigExact? steps
        (deleteOldConfig action outcome source) =
      some (deleteOldConfig action outcome target) := by
  exact
    TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some
      (Control.deleteOld action outcome)
      (deleteOld_step_of_some action outcome) hrun
  done

def deleteTailSteps
    (leftRev suffix : Word MachineCodeSymbol) : Nat :=
  ((2 * (DeleteBlock.optionalGap none).val + 1) * suffix.length + 1) +
    DeleteEndpointRewind.runSteps none
      (List.append suffix.reverse leftRev)

theorem delete_tail_exact
    (leftRev suffix : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine none).runConfigExact?
        (deleteTailSteps leftRev suffix)
        (DeleteRestagedMachine.editConfig
          (DeleteBlock.pullConfig (DeleteBlock.optionalGap none)
            leftRev suffix)) =
      some (DeleteRestagedMachine.rewindConfig
        (DeleteEndpointRewind.gateConfig
          (PhysicalBranch.deleteOutput leftRev suffix) none)) := by
  unfold deleteTailSteps
  rw [TuringMachine.runConfigExact?_add]
  rw [DeleteRestagedMachine.edit_run_of_eq_some none _ _ _
    (DeleteBlock.pull_run_exact none leftRev suffix)]
  simp only
  rw [DeleteRestagedMachine.rewind_run_exact]
  simp [PhysicalBranch.deleteOutput, List.reverse_append]
  done

theorem atMarker_step
    (action : Action)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (cursorConfig (.atMarker action) leftRev
          (MachineCodeSymbol.header :: suffix)) =
      some (deleteMarkerConfig action
        (DeleteRestagedMachine.editConfig
          (DeleteBlock.pullConfig (DeleteBlock.optionalGap none)
            leftRev suffix))) := by
  cases suffix <;> rfl
  done

theorem atOld_tick_step
    (action : Action)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (cursorConfig (.atOld action) leftRev
          (MachineCodeSymbol.tick :: suffix)) =
      some (deleteOldConfig action .continue
        (DeleteRestagedMachine.editConfig
          (DeleteBlock.pullConfig (DeleteBlock.optionalGap none)
            leftRev suffix))) := by
  cases suffix <;> rfl
  done

theorem atOld_done_step
    (action : Action)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (cursorConfig (.atOld action) leftRev
          (MachineCodeSymbol.done :: suffix)) =
      some (deleteOldConfig action .finish
        (DeleteRestagedMachine.editConfig
          (DeleteBlock.pullConfig (DeleteBlock.optionalGap none)
            leftRev suffix))) := by
  cases suffix <;> rfl
  done

def gateSeekOldConfig (action : Action)
    (word : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .seekOld action
  tape := (DeleteEndpointRewind.gateConfig word none).tape

def gateReadyConfig (action : Action)
    (word : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .ready action
  tape := (DeleteEndpointRewind.gateConfig word none).tape

theorem marker_bounce_exact
    (action : Action) (word : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (deleteMarkerConfig action
          (DeleteRestagedMachine.rewindConfig
            (DeleteEndpointRewind.gateConfig word none))) =
      some (gateSeekOldConfig action word) := by
  cases word with
  | nil => rfl
  | cons first rest =>
      cases rest <;> rfl
  done

theorem old_continue_bounce_exact
    (action : Action) (word : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (deleteOldConfig action .continue
          (DeleteRestagedMachine.rewindConfig
            (DeleteEndpointRewind.gateConfig word none))) =
      some (gateSeekOldConfig action word) := by
  cases word with
  | nil => rfl
  | cons first rest =>
      cases rest <;> rfl
  done

theorem old_finish_bounce_exact
    (action : Action) (word : Word MachineCodeSymbol) :
    machine.runConfigExact? 2
        (deleteOldConfig action .finish
          (DeleteRestagedMachine.rewindConfig
            (DeleteEndpointRewind.gateConfig word none))) =
      some (gateReadyConfig action word) := by
  cases word with
  | nil => rfl
  | cons first rest =>
      cases rest <;> rfl
  done

def deletePhaseSteps
    (leftRev suffix : Word MachineCodeSymbol) : Nat :=
  1 + deleteTailSteps leftRev suffix + 2

theorem marker_delete_exact
    (action : Action)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (deletePhaseSteps leftRev suffix)
        (cursorConfig (.atMarker action) leftRev
          (MachineCodeSymbol.header :: suffix)) =
      some (gateSeekOldConfig action
        (PhysicalBranch.deleteOutput leftRev suffix)) := by
  unfold deletePhaseSteps
  rw [TuringMachine.runConfigExact?_add]
  rw [TuringMachine.runConfigExact?_add]
  rw [TuringMachine.runConfigExact?, atMarker_step]
  simp only [TuringMachine.runConfigExact?]
  rw [deleteMarker_run_of_eq_some action
    (delete_tail_exact leftRev suffix)]
  simp only
  exact marker_bounce_exact action
    (PhysicalBranch.deleteOutput leftRev suffix)
  done

theorem old_tick_delete_exact
    (action : Action)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (deletePhaseSteps leftRev suffix)
        (cursorConfig (.atOld action) leftRev
          (MachineCodeSymbol.tick :: suffix)) =
      some (gateSeekOldConfig action
        (PhysicalBranch.deleteOutput leftRev suffix)) := by
  unfold deletePhaseSteps
  rw [TuringMachine.runConfigExact?_add]
  rw [TuringMachine.runConfigExact?_add]
  rw [TuringMachine.runConfigExact?, atOld_tick_step]
  simp only [TuringMachine.runConfigExact?]
  rw [deleteOld_run_of_eq_some action .continue
    (delete_tail_exact leftRev suffix)]
  simp only
  exact old_continue_bounce_exact action
    (PhysicalBranch.deleteOutput leftRev suffix)
  done

theorem old_done_delete_exact
    (action : Action)
    (leftRev suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (deletePhaseSteps leftRev suffix)
        (cursorConfig (.atOld action) leftRev
          (MachineCodeSymbol.done :: suffix)) =
      some (gateReadyConfig action
        (PhysicalBranch.deleteOutput leftRev suffix)) := by
  unfold deletePhaseSteps
  rw [TuringMachine.runConfigExact?_add]
  rw [TuringMachine.runConfigExact?_add]
  rw [TuringMachine.runConfigExact?, atOld_done_step]
  simp only [TuringMachine.runConfigExact?]
  rw [deleteOld_run_of_eq_some action .finish
    (delete_tail_exact leftRev suffix)]
  simp only
  exact old_finish_bounce_exact action
    (PhysicalBranch.deleteOutput leftRev suffix)
  done

theorem deleteOutput_encodeNat
    (target : Nat) (suffix : Word MachineCodeSymbol) :
    PhysicalBranch.deleteOutput
        (MachineDescription.encodeNat target).reverse suffix =
      MachineDescription.encodeNatAppend target suffix := by
  simp [PhysicalBranch.deleteOutput,
    MachineDescription.encodeNatAppend]
  done

def oldSymbolPhaseSteps
    (target : Nat) (suffix : Word MachineCodeSymbol) : Nat :=
  target + 1 +
    deletePhaseSteps (MachineDescription.encodeNat target).reverse suffix

theorem old_tick_phase_exact
    (action : Action) (target : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (oldSymbolPhaseSteps target suffix)
        (cursorConfig (.seekOld action) []
          (MachineDescription.encodeNatAppend target
            (MachineCodeSymbol.tick :: suffix))) =
      some (gateSeekOldConfig action
        (MachineDescription.encodeNatAppend target suffix)) := by
  unfold oldSymbolPhaseSteps
  rw [TuringMachine.runConfigExact?_add]
  rw [seekOld_run_exact]
  have hleft :
      List.append (MachineDescription.encodeNat target).reverse
          ([] : Word MachineCodeSymbol) =
        (MachineDescription.encodeNat target).reverse := by
    change List.append
      (MachineDescription.encodeNat target).reverse [] = _
    exact List.append_nil _
  rw [hleft]
  simp only
  rw [old_tick_delete_exact]
  rw [deleteOutput_encodeNat]
  done

theorem old_done_phase_exact
    (action : Action) (target : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? (oldSymbolPhaseSteps target suffix)
        (cursorConfig (.seekOld action) []
          (MachineDescription.encodeNatAppend target
            (MachineCodeSymbol.done :: suffix))) =
      some (gateReadyConfig action
        (MachineDescription.encodeNatAppend target suffix)) := by
  unfold oldSymbolPhaseSteps
  rw [TuringMachine.runConfigExact?_add]
  rw [seekOld_run_exact]
  have hleft :
      List.append (MachineDescription.encodeNat target).reverse
          ([] : Word MachineCodeSymbol) =
        (MachineDescription.encodeNat target).reverse := by
    change List.append
      (MachineDescription.encodeNat target).reverse [] = _
    exact List.append_nil _
  rw [hleft]
  simp only
  rw [old_done_delete_exact]
  rw [deleteOutput_encodeNat]
  done

theorem old_tick_phase_of_tape_equiv
    (action : Action) (target : Nat)
    (suffix : Word MachineCodeSymbol) (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (cursorConfig (.seekOld action) []
        (MachineDescription.encodeNatAppend target
          (MachineCodeSymbol.tick :: suffix))).tape tape) :
    exists targetTape : Tape MachineCodeSymbol,
      machine.runConfigExact? (oldSymbolPhaseSteps target suffix)
          { state := .seekOld action, tape := tape } =
        some { state := .seekOld action, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (MachineDescription.encodeNatAppend target suffix))
        targetTape := by
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        (old_tick_phase_exact action target suffix) htape with
    ⟨targetConfig', hrun, hstate, htarget⟩
  rcases targetConfig' with ⟨targetState, targetTape⟩
  simp only [gateSeekOldConfig] at hstate
  subst targetState
  refine ⟨targetTape, hrun, ?_⟩
  exact Tape.Equiv.trans
    (Tape.Equiv.symm
      (DeleteEndpointRewind.gateTape_equiv_input
        (MachineDescription.encodeNatAppend target suffix) none))
    htarget
  done

theorem old_done_phase_of_tape_equiv
    (action : Action) (target : Nat)
    (suffix : Word MachineCodeSymbol) (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (cursorConfig (.seekOld action) []
        (MachineDescription.encodeNatAppend target
          (MachineCodeSymbol.done :: suffix))).tape tape) :
    exists targetTape : Tape MachineCodeSymbol,
      machine.runConfigExact? (oldSymbolPhaseSteps target suffix)
          { state := .seekOld action, tape := tape } =
        some { state := .ready action, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (MachineDescription.encodeNatAppend target suffix))
        targetTape := by
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        (old_done_phase_exact action target suffix) htape with
    ⟨targetConfig', hrun, hstate, htarget⟩
  rcases targetConfig' with ⟨targetState, targetTape⟩
  simp only [gateReadyConfig] at hstate
  subst targetState
  refine ⟨targetTape, hrun, ?_⟩
  exact Tape.Equiv.trans
    (Tape.Equiv.symm
      (DeleteEndpointRewind.gateTape_equiv_input
        (MachineDescription.encodeNatAppend target suffix) none))
    htarget
  done

theorem encodeNatAppend_zero
    (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeNatAppend 0 suffix =
      MachineCodeSymbol.done :: suffix := by
  rfl
  done

theorem encodeNatAppend_succ
    (value : Nat) (suffix : Word MachineCodeSymbol) :
    MachineDescription.encodeNatAppend (value + 1) suffix =
      MachineCodeSymbol.tick ::
        MachineDescription.encodeNatAppend value suffix := by
  rfl
  done

theorem cursor_nil_tape_eq_input
    (state : Control) (word : Word MachineCodeSymbol) :
    (cursorConfig state [] word).tape = Tape.input word := by
  cases word <;> rfl
  done

def oldLoopSteps (target : Nat)
    (protectedSuffix : Word MachineCodeSymbol) : Nat -> Nat
  | 0 => oldSymbolPhaseSteps target protectedSuffix
  | oldState + 1 =>
      oldSymbolPhaseSteps target
          (MachineDescription.encodeNatAppend oldState protectedSuffix) +
        oldLoopSteps target protectedSuffix oldState

theorem old_loop_of_tape_equiv
    (action : Action) (target oldState : Nat)
    (protectedSuffix : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (htape : Tape.Equiv
      (cursorConfig (.seekOld action) []
        (MachineDescription.encodeNatAppend target
          (MachineDescription.encodeNatAppend oldState
            protectedSuffix))).tape tape) :
    exists targetTape : Tape MachineCodeSymbol,
      machine.runConfigExact?
          (oldLoopSteps target protectedSuffix oldState)
          { state := .seekOld action, tape := tape } =
        some { state := .ready action, tape := targetTape } ∧
      Tape.Equiv
        (Tape.input (targetWord target protectedSuffix)) targetTape := by
  induction oldState generalizing tape with
  | zero =>
      unfold oldLoopSteps
      have hsource : Tape.Equiv
          (cursorConfig (.seekOld action) []
            (MachineDescription.encodeNatAppend target
              (MachineCodeSymbol.done :: protectedSuffix))).tape tape := by
        rw [← encodeNatAppend_zero]
        exact htape
      simpa [targetWord] using
        (old_done_phase_of_tape_equiv action target protectedSuffix
          tape hsource)
  | succ oldState ih =>
      have hsource : Tape.Equiv
          (cursorConfig (.seekOld action) []
            (MachineDescription.encodeNatAppend target
              (MachineCodeSymbol.tick ::
                MachineDescription.encodeNatAppend oldState
                  protectedSuffix))).tape tape := by
        rw [← encodeNatAppend_succ]
        exact htape
      rcases old_tick_phase_of_tape_equiv action target
          (MachineDescription.encodeNatAppend oldState protectedSuffix)
          tape hsource with
        ⟨middleTape, hfirst, hmiddle⟩
      have hmiddle' : Tape.Equiv
          (cursorConfig (.seekOld action) []
            (MachineDescription.encodeNatAppend target
              (MachineDescription.encodeNatAppend oldState
                protectedSuffix))).tape middleTape := by
        rw [cursor_nil_tape_eq_input]
        exact hmiddle
      rcases ih middleTape hmiddle' with
        ⟨targetTape, hrest, htarget⟩
      refine ⟨targetTape, ?_, htarget⟩
      unfold oldLoopSteps
      rw [TuringMachine.runConfigExact?_add, hfirst]
      simp only
      exact hrest
  done

def markerPhaseSteps (target oldState : Nat)
    (protectedSuffix : Word MachineCodeSymbol) : Nat :=
  target + 1 +
    deletePhaseSteps (MachineDescription.encodeNat target).reverse
      (MachineDescription.encodeNatAppend oldState protectedSuffix)

theorem marker_phase_exact
    (action : Action) (target oldState : Nat)
    (protectedSuffix : Word MachineCodeSymbol) :
    machine.runConfigExact?
        (markerPhaseSteps target oldState protectedSuffix)
        (sourceConfig action target oldState protectedSuffix) =
      some (gateSeekOldConfig action
        (MachineDescription.encodeNatAppend target
          (MachineDescription.encodeNatAppend oldState
            protectedSuffix))) := by
  have hsource :
      sourceConfig action target oldState protectedSuffix =
        cursorConfig (.seekMarker action) []
          (MachineDescription.encodeNatAppend target
            (MachineCodeSymbol.header ::
              MachineDescription.encodeNatAppend oldState
                protectedSuffix)) := by
    cases target <;> rfl
  unfold markerPhaseSteps
  rw [hsource]
  rw [TuringMachine.runConfigExact?_add]
  rw [seekMarker_run_exact]
  have hleft :
      List.append (MachineDescription.encodeNat target).reverse
          ([] : Word MachineCodeSymbol) =
        (MachineDescription.encodeNat target).reverse := by
    change List.append
      (MachineDescription.encodeNat target).reverse [] = _
    exact List.append_nil _
  rw [hleft]
  simp only
  rw [marker_delete_exact]
  rw [deleteOutput_encodeNat]
  done

def runSteps (target oldState : Nat)
    (protectedSuffix : Word MachineCodeSymbol) : Nat :=
  markerPhaseSteps target oldState protectedSuffix +
    oldLoopSteps target protectedSuffix oldState

theorem run_exact
    (action : Action) (target oldState : Nat)
    (protectedSuffix : Word MachineCodeSymbol) :
    exists targetTape : Tape MachineCodeSymbol,
      machine.runConfigExact?
          (runSteps target oldState protectedSuffix)
          (sourceConfig action target oldState protectedSuffix) =
        some { state := .ready action, tape := targetTape } ∧
      Tape.Equiv
        (targetConfig action target protectedSuffix).tape targetTape := by
  have hgate : Tape.Equiv
      (cursorConfig (.seekOld action) []
        (MachineDescription.encodeNatAppend target
          (MachineDescription.encodeNatAppend oldState
            protectedSuffix))).tape
      (gateSeekOldConfig action
        (MachineDescription.encodeNatAppend target
          (MachineDescription.encodeNatAppend oldState
            protectedSuffix))).tape := by
    rw [cursor_nil_tape_eq_input]
    exact Tape.Equiv.symm
      (DeleteEndpointRewind.gateTape_equiv_input
        (MachineDescription.encodeNatAppend target
          (MachineDescription.encodeNatAppend oldState protectedSuffix))
        none)
  rcases old_loop_of_tape_equiv action target oldState protectedSuffix
      (gateSeekOldConfig action
        (MachineDescription.encodeNatAppend target
          (MachineDescription.encodeNatAppend oldState
            protectedSuffix))).tape hgate with
    ⟨targetTape, hloop, htape⟩
  refine ⟨targetTape, ?_, ?_⟩
  · unfold runSteps
    rw [TuringMachine.runConfigExact?_add]
    rw [marker_phase_exact]
    simp only
    exact hloop
  · simpa [targetConfig] using htape
  done

theorem computesIn_exact
    (action : Action) (target oldState : Nat)
    (protectedSuffix : Word MachineCodeSymbol) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.ComputesIn machine
          (runSteps target oldState protectedSuffix)
          (sourceConfig action target oldState protectedSuffix)
          { state := .ready action, tape := targetTape } ∧
      Tape.Equiv
        (targetConfig action target protectedSuffix).tape targetTape := by
  rcases run_exact action target oldState protectedSuffix with
    ⟨targetTape, hrun, htape⟩
  exact ⟨targetTape,
    TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hrun,
    htape⟩
  done

theorem computes_to_target_equiv
    (action : Action) (target oldState : Nat)
    (protectedSuffix : Word MachineCodeSymbol) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes machine
          (sourceConfig action target oldState protectedSuffix)
          { state := .ready action, tape := targetTape } ∧
      Tape.Equiv targetTape
        (targetConfig action target protectedSuffix).tape := by
  rcases computesIn_exact action target oldState protectedSuffix with
    ⟨targetTape, hrun, htape⟩
  exact ⟨targetTape, TuringMachine.computesIn_to_computes hrun,
    Tape.Equiv.symm htape⟩
  done

end FiniteRecognizer.Interpreter.RuntimeStateCompactor

end Computability
end FoC
