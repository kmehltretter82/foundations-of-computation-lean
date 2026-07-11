import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.KnownStateLoop
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.OtherStateLoop
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition

set_option doc.verso true

/-!
# Classified run-loop dispatcher

This module assembles the fixed finite-state loop and the generic unmatched-
state loop behind one typed dispatcher.  The parser-facing entry state carries
the result of {lit}`classifyState`: known description states enter the
fixed-step loop, while every other raw state enters the stuttering counter
loop.

The logical source is definitionally aligned with
{lit}`FieldDecomposition.loopTapes`.  Tape 0 is the exact live simulated tape,
tape 1 is the raw unary stage counter, and tape 2 is the compact
input/stage/raw-state metadata followed by a separator, the original scratch-
width markers, and the live hit bit.  The loop changes only the live
configuration, counter, and hit cell.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

/-!
## Shared field-decomposition tape currency
-/

/-- Compact metadata/hit tape from the unique field-decomposition boundary. -/
def loopDispatcherHitTape
    (sourceLayout : SimulatorLayout) (hit : Bool) : Tape Bool :=
  FieldDecomposition.metadataHitTapeWithHit sourceLayout hit

@[simp] theorem loopDispatcherHitTape_read
    (sourceLayout : SimulatorLayout) (hit : Bool) :
    Tape.read (loopDispatcherHitTape sourceLayout hit) = some hit := by
  exact FieldDecomposition.metadataHitTapeWithHit_read sourceLayout hit
  done

@[simp] theorem writeS_apply_loopDispatcherHitTape
    (sourceLayout : SimulatorLayout) (oldHit newHit : Bool) :
    (writeS (some newHit)).apply
        (loopDispatcherHitTape sourceLayout oldHit) =
      loopDispatcherHitTape sourceLayout newHit := by
  exact FieldDecomposition.writeS_apply_metadataHitTapeWithHit
    sourceLayout oldHit newHit
  done

/-- Common counter currency shared definitionally by both completed loops. -/
def loopDispatcherCounterTape
    (leftRev : List (Option Bool)) (consumed remaining : Nat)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  knownStateLoopCounterTape leftRev consumed remaining rightPadding

@[simp] theorem loopDispatcherCounterTape_eq_known
    (leftRev : List (Option Bool)) (consumed remaining : Nat)
    (rightPadding : List (Option Bool)) :
    loopDispatcherCounterTape leftRev consumed remaining rightPadding =
      knownStateLoopCounterTape leftRev consumed remaining rightPadding := by
  rfl

@[simp] theorem loopDispatcherCounterTape_eq_other
    (leftRev : List (Option Bool)) (consumed remaining : Nat)
    (rightPadding : List (Option Bool)) :
    loopDispatcherCounterTape leftRev consumed remaining rightPadding =
      otherStateLoopCounterTape leftRev consumed remaining rightPadding := by
  rfl

/-!
## Sum-state table
-/

/-- Sum of the classifier entry, both completed loop controls, and one common
halt state. -/
inductive LoopDispatcherState (D : MachineDescription) where
  | dispatch (tag : StateClass D)
  | known (state : KnownStateLoopState)
  | other (state : OtherStateLoopState)
  | halt
deriving DecidableEq

/-- Complete finite state enumeration for the combined dispatcher. -/
def loopDispatcherStates (D : MachineDescription) :
    List (LoopDispatcherState D) :=
  List.append
    ((stateClasses D).map LoopDispatcherState.dispatch)
    (List.append
      ((knownStateLoopStates D).map LoopDispatcherState.known)
      (List.append
        (otherStateLoopStates.map LoopDispatcherState.other)
        [LoopDispatcherState.halt]))

theorem dispatch_mem_loopDispatcherStates
    {D : MachineDescription} (tag : StateClass D) :
    LoopDispatcherState.dispatch tag ∈ loopDispatcherStates D := by
  simp [loopDispatcherStates, mem_stateClasses]
  done

theorem known_mem_loopDispatcherStates
    {D : MachineDescription} {state : KnownStateLoopState}
    (hstate : state ∈ knownStateLoopStates D) :
    LoopDispatcherState.known state ∈ loopDispatcherStates D := by
  simp [loopDispatcherStates, hstate]
  done

theorem other_mem_loopDispatcherStates
    {D : MachineDescription} {state : OtherStateLoopState}
    (hstate : state ∈ otherStateLoopStates) :
    LoopDispatcherState.other state ∈ loopDispatcherStates D := by
  simp [loopDispatcherStates, hstate]
  done

theorem halt_mem_loopDispatcherStates (D : MachineDescription) :
    LoopDispatcherState.halt ∈ loopDispatcherStates D := by
  simp [loopDispatcherStates]
  done

theorem stateClasses_of_dispatch_mem
    {D : MachineDescription} {tag : StateClass D}
    (hstate :
      LoopDispatcherState.dispatch tag ∈ loopDispatcherStates D) :
    tag ∈ stateClasses D := by
  simpa [loopDispatcherStates] using hstate
  done

theorem knownStateLoopStates_of_known_mem
    {D : MachineDescription} {state : KnownStateLoopState}
    (hstate :
      LoopDispatcherState.known state ∈ loopDispatcherStates D) :
    state ∈ knownStateLoopStates D := by
  simpa [loopDispatcherStates] using hstate
  done

theorem otherStateLoopStates_of_other_mem
    {D : MachineDescription} {state : OtherStateLoopState}
    (hstate :
      LoopDispatcherState.other state ∈ loopDispatcherStates D) :
    state ∈ otherStateLoopStates := by
  simpa [loopDispatcherStates] using hstate
  done

/-- Embed a known-loop target, identifying its private halt with the common
dispatcher halt. -/
def liftKnownTarget {D : MachineDescription} :
    KnownStateLoopState -> LoopDispatcherState D
  | .halt => .halt
  | state => .known state

/-- Embed an unmatched-loop target, identifying its private halt with the
common dispatcher halt. -/
def liftOtherTarget {D : MachineDescription} :
    OtherStateLoopState -> LoopDispatcherState D
  | .halt => .halt
  | state => .other state

def liftKnownStep {D : MachineDescription}
    (step : TypedStep KnownStateLoopState) :
    TypedStep (LoopDispatcherState D) :=
  { target := liftKnownTarget step.target
    action0 := step.action0
    action1 := step.action1
    action2 := step.action2 }

def liftOtherStep {D : MachineDescription}
    (step : TypedStep OtherStateLoopState) :
    TypedStep (LoopDispatcherState D) :=
  { target := liftOtherTarget step.target
    action0 := step.action0
    action1 := step.action1
    action2 := step.action2 }

/-- One combined typed transition.  Classification itself has already been
performed by the parser and is carried by the dispatch entry state. -/
def loopDispatcherNext (D : MachineDescription) :
    LoopDispatcherState D -> Option Bool -> Option Bool -> Option Bool ->
      Option (TypedStep (LoopDispatcherState D))
  | .dispatch (.known state _), _, _, _ =>
      some
        { target := .known (.seed state)
          action0 := keepS
          action1 := keepS
          action2 := keepS }
  | .dispatch .other, _, _, _ =>
      some
        { target := .other .loop
          action0 := keepS
          action1 := keepS
          action2 := keepS }
  | .known (.done _), _, _, _ => none
  | .other .done, _, _, _ => none
  | .known state, r0, r1, r2 =>
      (knownStateLoopNext D state r0 r1 r2).map liftKnownStep
  | .other state, r0, r1, r2 =>
      (otherStateLoopNext state r0 r1 r2).map liftOtherStep
  | .halt, _, _, _ => none

theorem loopDispatcherNext_target_mem (D : MachineDescription) :
    forall s : LoopDispatcherState D, s ∈ loopDispatcherStates D ->
      forall (r0 r1 r2 : Option Bool)
        (step : TypedStep (LoopDispatcherState D)),
        loopDispatcherNext D s r0 r1 r2 = some step ->
          step.target ∈ loopDispatcherStates D := by
  intro s hs r0 r1 r2 step hnext
  cases s with
  | dispatch tag =>
      cases tag with
      | known state hstate =>
          simp only [loopDispatcherNext] at hnext
          cases hnext
          exact known_mem_loopDispatcherStates
            (seed_mem_knownStateLoopStates hstate)
      | other =>
          simp only [loopDispatcherNext] at hnext
          cases hnext
          exact other_mem_loopDispatcherStates
            loop_mem_otherStateLoopStates
  | known state =>
      cases state with
      | done state =>
          simp [loopDispatcherNext] at hnext
      | halt =>
          simp [loopDispatcherNext, knownStateLoopNext] at hnext
      | seed state =>
          have hsKnown := knownStateLoopStates_of_known_mem hs
          cases hinner :
              knownStateLoopNext D (.seed state) r0 r1 r2 with
          | none =>
              simp [loopDispatcherNext, hinner] at hnext
          | some inner =>
              simp only [loopDispatcherNext, hinner,
                Option.map_some] at hnext
              cases hnext
              have htarget := knownStateLoopNext_target_mem D
                (.seed state) hsKnown r0 r1 r2 inner hinner
              rcases inner with ⟨target, action0, action1, action2⟩
              cases target with
              | seed state =>
                  exact known_mem_loopDispatcherStates htarget
              | loop state =>
                  exact known_mem_loopDispatcherStates htarget
              | done state =>
                  exact known_mem_loopDispatcherStates htarget
              | halt =>
                  exact halt_mem_loopDispatcherStates D
      | loop state =>
          have hsKnown := knownStateLoopStates_of_known_mem hs
          cases hinner :
              knownStateLoopNext D (.loop state) r0 r1 r2 with
          | none =>
              simp [loopDispatcherNext, hinner] at hnext
          | some inner =>
              simp only [loopDispatcherNext, hinner,
                Option.map_some] at hnext
              cases hnext
              have htarget := knownStateLoopNext_target_mem D
                (.loop state) hsKnown r0 r1 r2 inner hinner
              rcases inner with ⟨target, action0, action1, action2⟩
              cases target with
              | seed state =>
                  exact known_mem_loopDispatcherStates htarget
              | loop state =>
                  exact known_mem_loopDispatcherStates htarget
              | done state =>
                  exact known_mem_loopDispatcherStates htarget
              | halt =>
                  exact halt_mem_loopDispatcherStates D
  | other state =>
      cases state with
      | done =>
          simp [loopDispatcherNext] at hnext
      | halt =>
          simp [loopDispatcherNext, otherStateLoopNext] at hnext
      | loop =>
          have hsOther := otherStateLoopStates_of_other_mem hs
          cases hinner : otherStateLoopNext .loop r0 r1 r2 with
          | none =>
              simp [loopDispatcherNext, hinner] at hnext
          | some inner =>
              simp only [loopDispatcherNext, hinner,
                Option.map_some] at hnext
              cases hnext
              have htarget := otherStateLoopNext_target_mem
                .loop hsOther r0 r1 r2 inner hinner
              rcases inner with ⟨target, action0, action1, action2⟩
              cases target with
              | loop => exact other_mem_loopDispatcherStates htarget
              | done => exact other_mem_loopDispatcherStates htarget
              | halt => exact halt_mem_loopDispatcherStates D
  | halt =>
      simp [loopDispatcherNext] at hnext
  done

/-- Generated typed table for the complete classified dispatcher. -/
def loopDispatcherTable (D : MachineDescription) :
    TypedStateTable (LoopDispatcherState D) :=
  TypedStateTable.ofList
    (loopDispatcherStates D)
    (.dispatch
      (.known D.start (start_mem_fixedStepValues D)))
    .halt
    (loopDispatcherNext D)
    (dispatch_mem_loopDispatcherStates _)
    (halt_mem_loopDispatcherStates D)
    (by intro r0 r1 r2; rfl)
    (loopDispatcherNext_target_mem D)

/-- Structured three-tape classified loop dispatcher. -/
def loopDispatcherDescription (D : MachineDescription) : Description :=
  (loopDispatcherTable D).description

theorem loopDispatcherDescription_wellFormed (D : MachineDescription) :
    (loopDispatcherDescription D).WellFormed := by
  exact (loopDispatcherTable D).description_wellFormed
  done

theorem loopDispatcherDescription_haltTransitionFree
    (D : MachineDescription) :
    (loopDispatcherDescription D).HaltTransitionFree := by
  exact (loopDispatcherTable D).description_haltTransitionFree
  done

theorem loopDispatcherDescription_supportsReadWriteRows3
    (D : MachineDescription) :
    SupportsReadWriteRows3 (loopDispatcherDescription D) := by
  exact (loopDispatcherTable D).description_supportsReadWriteRows3
  done

theorem loopDispatcherDescription_subroutineReady
    (D : MachineDescription) :
    (loopDispatcherDescription D).SubroutineReady := by
  exact (loopDispatcherTable D).description_subroutineReady
  done

/-!
## Source and semantic endpoint family
-/

/-- Exhausted stage-counter tape after all raw markers have been erased. -/
def loopDispatcherConsumedStageCounterTape (stage : Nat) : Tape Bool :=
  loopDispatcherCounterTape [] stage 0 []

theorem fieldDecomposition_stageCounterTape_eq_dispatcher
    (stage : Nat) :
    FieldDecomposition.stageCounterTape stage =
      loopDispatcherCounterTape [] 0 stage [] := by
  rfl
  done

/-- Parser-facing classified logical source. -/
def loopDispatcherSourceConfig
    (D : MachineDescription) (L : SimulatorLayout) :
    Structured.Configuration :=
  ThreeTape.config
    ((loopDispatcherTable D).stateId
      (.dispatch (classifyState D L.config.state)))
    L.config.tape
    (FieldDecomposition.stageCounterTape L.stage)
    (FieldDecomposition.metadataHitTape L)

theorem loopDispatcherSourceConfig_tapes
    (D : MachineDescription) (L : SimulatorLayout) :
    (loopDispatcherSourceConfig D L).tapes =
      FieldDecomposition.loopTapes L := by
  rfl
  done

/-- Typed pre-halt endpoint selected by the same semantic classification. -/
def loopDispatcherEndpointState
    (D : MachineDescription) (L : SimulatorLayout) :
    LoopDispatcherState D :=
  match classifyState D L.config.state with
  | .known _ _ =>
      .known (.done (SimulatorLayout.run D L.stage L).config.state)
  | .other => .other .done

/-- Exact endpoint retaining the final semantic configuration and hit together
with all original metadata and caller padding. -/
def loopDispatcherEndpointConfig
    (D : MachineDescription) (L : SimulatorLayout) :
    Structured.Configuration :=
  ThreeTape.config
    ((loopDispatcherTable D).stateId
    (loopDispatcherEndpointState D L))
    (SimulatorLayout.run D L.stage L).config.tape
    (loopDispatcherConsumedStageCounterTape L.stage)
    (loopDispatcherHitTape L
      (SimulatorLayout.run D L.stage L).hit)

/-- Branch-dependent exact number of dispatcher and loop steps to the exposed
pre-halt endpoint. -/
def loopDispatcherRunSteps
    (D : MachineDescription) (L : SimulatorLayout) : Nat :=
  match classifyState D L.config.state with
  | .known _ _ => L.stage + 3
  | .other => L.stage + 2

/-!
## Exact combined execution
-/

/-- One typed dispatcher row executes as one structured-machine step. -/
theorem loopDispatcherDescription_runConfig_one
    (D : MachineDescription) (state : LoopDispatcherState D)
    (hstate : state ∈ loopDispatcherStates D)
    (T0 T1 T2 : Tape Bool)
    (step : TypedStep (LoopDispatcherState D))
    (hnext :
      loopDispatcherNext D state
          (Tape.read T0) (Tape.read T1) (Tape.read T2) = some step) :
    (loopDispatcherDescription D).runConfig 1
        (ThreeTape.config
          ((loopDispatcherTable D).stateId state) T0 T1 T2) =
      ThreeTape.config
        ((loopDispatcherTable D).stateId step.target)
        (step.action0.apply T0)
        (step.action1.apply T1)
        (step.action2.apply T2) := by
  change
    (loopDispatcherTable D).description.runConfig (0 + 1)
        (ThreeTape.config
          ((loopDispatcherTable D).stateId state) T0 T1 T2) = _
  rw [(loopDispatcherTable D).runConfig_succ_config
    hstate hnext 0]
  rfl
  done

theorem loopDispatcherDescription_runConfig_one_dispatch_known
    (D : MachineDescription) (state : Nat)
    (hstate : state ∈ fixedStepValues D)
    (T0 T1 T2 : Tape Bool) :
    (loopDispatcherDescription D).runConfig 1
        (ThreeTape.config
          ((loopDispatcherTable D).stateId
            (.dispatch (.known state hstate))) T0 T1 T2) =
      ThreeTape.config
        ((loopDispatcherTable D).stateId
          (.known (.seed state))) T0 T1 T2 := by
  have hnext :
      loopDispatcherNext D (.dispatch (.known state hstate))
          (Tape.read T0) (Tape.read T1) (Tape.read T2) =
        some
          { target := .known (.seed state)
            action0 := keepS
            action1 := keepS
            action2 := keepS } := by
    rfl
  have hrun :=
    loopDispatcherDescription_runConfig_one D
      (.dispatch (.known state hstate))
      (dispatch_mem_loopDispatcherStates _)
      T0 T1 T2
      { target := .known (.seed state)
        action0 := keepS
        action1 := keepS
        action2 := keepS }
      hnext
  simpa [keepS, TapeAction.stay, TapeAction.apply,
    HeadMove.apply] using hrun
  done

theorem loopDispatcherDescription_runConfig_one_dispatch_other
    (D : MachineDescription) (T0 T1 T2 : Tape Bool) :
    (loopDispatcherDescription D).runConfig 1
        (ThreeTape.config
          ((loopDispatcherTable D).stateId
            (.dispatch (.other : StateClass D))) T0 T1 T2) =
      ThreeTape.config
        ((loopDispatcherTable D).stateId
          (.other .loop)) T0 T1 T2 := by
  have hnext :
      loopDispatcherNext D (.dispatch (.other : StateClass D))
          (Tape.read T0) (Tape.read T1) (Tape.read T2) =
        some
          { target := .other .loop
            action0 := keepS
            action1 := keepS
            action2 := keepS } := by
    rfl
  have hrun :=
    loopDispatcherDescription_runConfig_one D
      (.dispatch (.other : StateClass D))
      (dispatch_mem_loopDispatcherStates _)
      T0 T1 T2
      { target := .other .loop
        action0 := keepS
        action1 := keepS
        action2 := keepS }
      hnext
  simpa [keepS, TapeAction.stay, TapeAction.apply,
    HeadMove.apply] using hrun
  done

theorem loopDispatcherDescription_runConfig_one_known_seed
    (D : MachineDescription) (state : Nat)
    (hstate : state ∈ fixedStepValues D)
    (T0 T1 : Tape Bool)
    (sourceLayout : SimulatorLayout)
    (hit : Bool) :
    (loopDispatcherDescription D).runConfig 1
        (ThreeTape.config
          ((loopDispatcherTable D).stateId
            (.known (.seed state)))
          T0 T1
          (loopDispatcherHitTape sourceLayout hit)) =
      ThreeTape.config
        ((loopDispatcherTable D).stateId
          (.known (.loop state)))
        T0 T1
        (loopDispatcherHitTape sourceLayout
          (hit || (state == D.halt))) := by
  have hnext :
      loopDispatcherNext D (.known (.seed state))
          (Tape.read T0) (Tape.read T1)
          (Tape.read
            (loopDispatcherHitTape sourceLayout hit)) =
        some
          { target := .known (.loop state)
            action0 := keepS
            action1 := keepS
            action2 := writeS (some (hit || (state == D.halt))) } := by
    simp [loopDispatcherNext, knownStateLoopNext,
      liftKnownStep, liftKnownTarget]
    done
  have hrun :=
    loopDispatcherDescription_runConfig_one D
      (.known (.seed state))
      (known_mem_loopDispatcherStates
        (seed_mem_knownStateLoopStates hstate))
      T0 T1
      (loopDispatcherHitTape sourceLayout hit)
      { target := .known (.loop state)
        action0 := keepS
        action1 := keepS
        action2 := writeS (some (hit || (state == D.halt))) }
      hnext
  change
    (loopDispatcherDescription D).runConfig 1 _ =
      ThreeTape.config
        ((loopDispatcherTable D).stateId (.known (.loop state)))
        (keepS.apply T0) (keepS.apply T1)
        ((writeS (some (hit || (state == D.halt)))).apply
          (loopDispatcherHitTape sourceLayout hit)) at hrun
  rw [writeS_apply_loopDispatcherHitTape] at hrun
  simpa [keepS, TapeAction.stay, TapeAction.apply,
    HeadMove.apply] using hrun
  done

theorem loopDispatcherDescription_runConfig_one_known_succ
    (D : MachineDescription) (state : Nat)
    (hstate : state ∈ fixedStepValues D)
    (T0 : Tape Bool) (sourceLayout : SimulatorLayout)
    (hit : Bool)
    (counterLeft : List (Option Bool))
    (consumed remaining : Nat)
    (counterRight : List (Option Bool)) :
    (loopDispatcherDescription D).runConfig 1
        (ThreeTape.config
          ((loopDispatcherTable D).stateId
            (.known (.loop state)))
          T0
          (loopDispatcherCounterTape counterLeft consumed (remaining + 1)
            counterRight)
          (loopDispatcherHitTape sourceLayout hit)) =
      ThreeTape.config
        ((loopDispatcherTable D).stateId
          (.known (.loop
            (fixedStepTargetState D state (Tape.read T0)))))
        ((fixedStepTapeAction D state (Tape.read T0)).apply T0)
        (loopDispatcherCounterTape counterLeft (consumed + 1) remaining
          counterRight)
        (loopDispatcherHitTape sourceLayout
          (hit ||
            (fixedStepTargetState D state (Tape.read T0) == D.halt))) := by
  have hnext :
      loopDispatcherNext D (.known (.loop state))
          (Tape.read T0)
          (Tape.read
            (loopDispatcherCounterTape counterLeft consumed (remaining + 1)
              counterRight))
          (Tape.read
            (loopDispatcherHitTape sourceLayout hit)) =
        some
          { target := .known (.loop
              (fixedStepTargetState D state (Tape.read T0)))
            action0 := fixedStepTapeAction D state (Tape.read T0)
            action1 := eraseR
            action2 := writeS (some
              (hit ||
                (fixedStepTargetState D state (Tape.read T0) == D.halt))) } := by
    simp [loopDispatcherNext, knownStateLoopNext,
      liftKnownStep, liftKnownTarget]
    done
  have hrun :=
    loopDispatcherDescription_runConfig_one D
      (.known (.loop state))
      (known_mem_loopDispatcherStates
        (loop_mem_knownStateLoopStates hstate))
      T0
      (loopDispatcherCounterTape counterLeft consumed (remaining + 1)
        counterRight)
      (loopDispatcherHitTape sourceLayout hit)
      { target := .known (.loop
          (fixedStepTargetState D state (Tape.read T0)))
        action0 := fixedStepTapeAction D state (Tape.read T0)
        action1 := eraseR
        action2 := writeS (some
          (hit ||
            (fixedStepTargetState D state (Tape.read T0) == D.halt))) }
      hnext
  change
    (loopDispatcherDescription D).runConfig 1 _ =
      ThreeTape.config
        ((loopDispatcherTable D).stateId
          (.known (.loop
            (fixedStepTargetState D state (Tape.read T0)))))
        ((fixedStepTapeAction D state (Tape.read T0)).apply T0)
        (eraseR.apply
          (loopDispatcherCounterTape counterLeft consumed (remaining + 1)
            counterRight))
        ((writeS (some
          (hit ||
            (fixedStepTargetState D state (Tape.read T0) == D.halt)))).apply
          (loopDispatcherHitTape sourceLayout hit)) at hrun
  rw [show loopDispatcherCounterTape counterLeft consumed (remaining + 1)
      counterRight =
        knownStateLoopCounterTape counterLeft consumed (remaining + 1)
          counterRight by rfl,
    eraseR_apply_knownStateLoopCounterTape_succ] at hrun
  rw [writeS_apply_loopDispatcherHitTape] at hrun
  exact hrun
  done

theorem loopDispatcherDescription_runConfig_one_known_zero
    (D : MachineDescription) (state : Nat)
    (hstate : state ∈ fixedStepValues D)
    (T0 : Tape Bool) (sourceLayout : SimulatorLayout)
    (hit : Bool)
    (counterLeft : List (Option Bool)) (consumed : Nat)
    (counterRight : List (Option Bool)) :
    (loopDispatcherDescription D).runConfig 1
        (ThreeTape.config
          ((loopDispatcherTable D).stateId
            (.known (.loop state)))
          T0
          (loopDispatcherCounterTape counterLeft consumed 0 counterRight)
          (loopDispatcherHitTape sourceLayout hit)) =
      ThreeTape.config
        ((loopDispatcherTable D).stateId
          (.known (.done state)))
        T0
        (loopDispatcherCounterTape counterLeft consumed 0 counterRight)
        (loopDispatcherHitTape sourceLayout hit) := by
  have hnext :
      loopDispatcherNext D (.known (.loop state))
          (Tape.read T0)
          (Tape.read
            (loopDispatcherCounterTape counterLeft consumed 0 counterRight))
          (Tape.read
            (loopDispatcherHitTape sourceLayout hit)) =
        some
          { target := .known (.done state)
            action0 := keepS
            action1 := keepS
            action2 := keepS } := by
    simp [loopDispatcherNext, knownStateLoopNext,
      liftKnownStep, liftKnownTarget]
    done
  have hrun :=
    loopDispatcherDescription_runConfig_one D
      (.known (.loop state))
      (known_mem_loopDispatcherStates
        (loop_mem_knownStateLoopStates hstate))
      T0
      (loopDispatcherCounterTape counterLeft consumed 0 counterRight)
      (loopDispatcherHitTape sourceLayout hit)
      { target := .known (.done state)
        action0 := keepS
        action1 := keepS
        action2 := keepS }
      hnext
  simpa [keepS, TapeAction.stay, TapeAction.apply,
    HeadMove.apply] using hrun
  done

theorem loopDispatcherDescription_runConfig_one_other_succ
    (D : MachineDescription) (T0 T2 : Tape Bool)
    (counterLeft : List (Option Bool))
    (consumed remaining : Nat)
    (counterRight : List (Option Bool)) :
    (loopDispatcherDescription D).runConfig 1
        (ThreeTape.config
          ((loopDispatcherTable D).stateId
            (.other .loop))
          T0
          (loopDispatcherCounterTape counterLeft consumed (remaining + 1)
            counterRight)
          T2) =
      ThreeTape.config
        ((loopDispatcherTable D).stateId
          (.other .loop))
        T0
        (loopDispatcherCounterTape counterLeft (consumed + 1) remaining
          counterRight)
        T2 := by
  have hnext :
      loopDispatcherNext D (.other .loop)
          (Tape.read T0)
          (Tape.read
            (loopDispatcherCounterTape counterLeft consumed (remaining + 1)
              counterRight))
          (Tape.read T2) =
        some
          { target := .other .loop
            action0 := keepS
            action1 := eraseR
            action2 := keepS } := by
    simp [loopDispatcherNext, otherStateLoopNext,
      liftOtherStep, liftOtherTarget]
    done
  have hrun :=
    loopDispatcherDescription_runConfig_one D
      (.other .loop)
      (other_mem_loopDispatcherStates loop_mem_otherStateLoopStates)
      T0
      (loopDispatcherCounterTape counterLeft consumed (remaining + 1)
        counterRight)
      T2
      { target := .other .loop
        action0 := keepS
        action1 := eraseR
        action2 := keepS }
      hnext
  change
    (loopDispatcherDescription D).runConfig 1 _ =
      ThreeTape.config
        ((loopDispatcherTable D).stateId (.other .loop))
        (keepS.apply T0)
        (eraseR.apply
          (loopDispatcherCounterTape counterLeft consumed (remaining + 1)
            counterRight))
        (keepS.apply T2) at hrun
  rw [show loopDispatcherCounterTape counterLeft consumed (remaining + 1)
      counterRight =
        knownStateLoopCounterTape counterLeft consumed (remaining + 1)
          counterRight by rfl,
    eraseR_apply_knownStateLoopCounterTape_succ] at hrun
  simpa [keepS, TapeAction.stay, TapeAction.apply,
    HeadMove.apply] using hrun
  done

theorem loopDispatcherDescription_runConfig_one_other_zero
    (D : MachineDescription) (T0 T2 : Tape Bool)
    (counterLeft : List (Option Bool)) (consumed : Nat)
    (counterRight : List (Option Bool)) :
    (loopDispatcherDescription D).runConfig 1
        (ThreeTape.config
          ((loopDispatcherTable D).stateId
            (.other .loop))
          T0
          (loopDispatcherCounterTape counterLeft consumed 0 counterRight)
          T2) =
      ThreeTape.config
        ((loopDispatcherTable D).stateId
          (.other .done))
        T0
        (loopDispatcherCounterTape counterLeft consumed 0 counterRight)
        T2 := by
  have hnext :
      loopDispatcherNext D (.other .loop)
          (Tape.read T0)
          (Tape.read
            (loopDispatcherCounterTape counterLeft consumed 0 counterRight))
          (Tape.read T2) =
        some
          { target := .other .done
            action0 := keepS
            action1 := keepS
            action2 := keepS } := by
    simp [loopDispatcherNext, otherStateLoopNext,
      liftOtherStep, liftOtherTarget]
    done
  have hrun :=
    loopDispatcherDescription_runConfig_one D
      (.other .loop)
      (other_mem_loopDispatcherStates loop_mem_otherStateLoopStates)
      T0
      (loopDispatcherCounterTape counterLeft consumed 0 counterRight)
      T2
      { target := .other .done
        action0 := keepS
        action1 := keepS
        action2 := keepS }
      hnext
  simpa [keepS, TapeAction.stay, TapeAction.apply,
    HeadMove.apply] using hrun
  done

/-!
### Known-state branch
-/

def loopDispatcherKnownIterationConfig
    (D : MachineDescription) (L : SimulatorLayout)
    (sourceLayout : SimulatorLayout)
    (counterLeft : List (Option Bool)) (consumed remaining : Nat)
    (counterRight : List (Option Bool)) :
    Structured.Configuration :=
  ThreeTape.config
    ((loopDispatcherTable D).stateId
      (.known (.loop L.config.state)))
    L.config.tape
    (loopDispatcherCounterTape counterLeft consumed remaining counterRight)
    (loopDispatcherHitTape sourceLayout L.hit)

theorem loopDispatcherDescription_runConfig_known_loop
    (D : MachineDescription) (L : SimulatorLayout)
    (hstate : L.config.state ∈ fixedStepValues D)
    (sourceLayout : SimulatorLayout)
    (counterLeft : List (Option Bool)) (consumed steps tail : Nat)
    (counterRight : List (Option Bool)) :
    (loopDispatcherDescription D).runConfig steps
        (loopDispatcherKnownIterationConfig D
          (RunConfigEmitterTheory.iterateStep D consumed L)
          sourceLayout counterLeft consumed (steps + tail) counterRight) =
      loopDispatcherKnownIterationConfig D
        (RunConfigEmitterTheory.iterateStep D (consumed + steps) L)
        sourceLayout counterLeft (consumed + steps) tail counterRight := by
  induction steps generalizing consumed with
  | zero =>
      simp [loopDispatcherKnownIterationConfig,
        Structured.Description.runConfig]
      done
  | succ steps ih =>
      rw [show Nat.succ steps + tail = (steps + tail) + 1 by lia]
      rw [show steps + 1 = 1 + steps by lia]
      rw [Structured.Description.runConfig_add]
      have hiterState :=
        iterateStep_config_state_mem_fixedStepValues D L hstate consumed
      unfold loopDispatcherKnownIterationConfig
      rw [loopDispatcherDescription_runConfig_one_known_succ D
        (RunConfigEmitterTheory.iterateStep D consumed L).config.state
        hiterState
        (RunConfigEmitterTheory.iterateStep D consumed L).config.tape
        sourceLayout
        (RunConfigEmitterTheory.iterateStep D consumed L).hit
        counterLeft consumed (steps + tail) counterRight]
      rw [fixedStepTargetState_eq_runConfig_one_state]
      rw [fixedStepTapeAction_apply_eq_runConfig_one_tape]
      rw [← RunConfigEmitterTheory.nextConfig_eq_runConfig_one]
      change
        (loopDispatcherDescription D).runConfig steps
          (loopDispatcherKnownIterationConfig D
            (SimulatorLayout.step D
              (RunConfigEmitterTheory.iterateStep D consumed L))
            sourceLayout counterLeft (consumed + 1) (steps + tail)
            counterRight) = _
      change
        (loopDispatcherDescription D).runConfig steps
          (loopDispatcherKnownIterationConfig D
            (RunConfigEmitterTheory.iterateStep D (consumed + 1) L)
            sourceLayout counterLeft (consumed + 1) (steps + tail)
            counterRight) = _
      rw [ih (consumed + 1)]
      simp [loopDispatcherKnownIterationConfig, Nat.add_assoc]
      done

def loopDispatcherKnownSourceConfig
    (D : MachineDescription) (L : SimulatorLayout)
    (sourceLayout : SimulatorLayout)
    (counterLeft counterRight : List (Option Bool)) :
    Structured.Configuration :=
  ThreeTape.config
    ((loopDispatcherTable D).stateId
      (.known (.seed L.config.state)))
    L.config.tape
    (loopDispatcherCounterTape counterLeft 0 L.stage counterRight)
    (loopDispatcherHitTape sourceLayout L.hit)

def loopDispatcherKnownDoneConfig
    (D : MachineDescription) (L : SimulatorLayout)
    (sourceLayout : SimulatorLayout)
    (counterLeft counterRight : List (Option Bool)) :
    Structured.Configuration :=
  ThreeTape.config
    ((loopDispatcherTable D).stateId
      (.known (.done L.config.state)))
    L.config.tape
    (loopDispatcherCounterTape counterLeft L.stage 0 counterRight)
    (loopDispatcherHitTape sourceLayout L.hit)

theorem loopDispatcherDescription_runConfig_known_to_done
    (D : MachineDescription) (L : SimulatorLayout)
    (hstate : L.config.state ∈ fixedStepValues D)
    (sourceLayout : SimulatorLayout)
    (counterLeft counterRight : List (Option Bool)) :
    (loopDispatcherDescription D).runConfig (L.stage + 2)
        (loopDispatcherKnownSourceConfig D L sourceLayout
          counterLeft counterRight) =
      loopDispatcherKnownDoneConfig D
        (SimulatorLayout.run D L.stage L) sourceLayout
        counterLeft counterRight := by
  rw [show L.stage + 2 = 1 + L.stage + 1 by lia]
  rw [Structured.Description.runConfig_add]
  rw [Structured.Description.runConfig_add]
  unfold loopDispatcherKnownSourceConfig
  rw [loopDispatcherDescription_runConfig_one_known_seed D
    L.config.state hstate L.config.tape
    (loopDispatcherCounterTape counterLeft 0 L.stage counterRight)
    sourceLayout L.hit]
  change
    (loopDispatcherDescription D).runConfig 1
      ((loopDispatcherDescription D).runConfig L.stage
        (loopDispatcherKnownIterationConfig D
          (RunConfigEmitterTheory.seedHit D L)
          sourceLayout counterLeft 0 (L.stage + 0) counterRight)) = _
  have hseedState :
      (RunConfigEmitterTheory.seedHit D L).config.state ∈
        fixedStepValues D := by
    simpa [RunConfigEmitterTheory.seedHit] using hstate
    done
  change
    (loopDispatcherDescription D).runConfig 1
      ((loopDispatcherDescription D).runConfig L.stage
        (loopDispatcherKnownIterationConfig D
          (RunConfigEmitterTheory.iterateStep D 0
            (RunConfigEmitterTheory.seedHit D L))
          sourceLayout counterLeft 0 (L.stage + 0) counterRight)) = _
  rw [loopDispatcherDescription_runConfig_known_loop D
    (RunConfigEmitterTheory.seedHit D L) hseedState
    sourceLayout counterLeft 0 L.stage 0 counterRight]
  simp only [Nat.zero_add]
  rw [RunConfigEmitterTheory.iterateStep_seedHit_eq_run]
  have hfinalState :
      (SimulatorLayout.run D L.stage L).config.state ∈
        fixedStepValues D := by
    rw [← RunConfigEmitterTheory.iterateStep_seedHit_eq_run]
    exact iterateStep_config_state_mem_fixedStepValues D
      (RunConfigEmitterTheory.seedHit D L) hseedState L.stage
    done
  unfold loopDispatcherKnownIterationConfig loopDispatcherKnownDoneConfig
  exact loopDispatcherDescription_runConfig_one_known_zero D
    (SimulatorLayout.run D L.stage L).config.state hfinalState
    (SimulatorLayout.run D L.stage L).config.tape sourceLayout
    (SimulatorLayout.run D L.stage L).hit
    counterLeft L.stage counterRight
  done

/-!
### Unmatched-state branch
-/

theorem loopDispatcherDescription_runConfig_other_markers
    (D : MachineDescription) (T0 T2 : Tape Bool)
    (counterLeft : List (Option Bool))
    (consumed markers tail : Nat)
    (counterRight : List (Option Bool)) :
    (loopDispatcherDescription D).runConfig markers
        (ThreeTape.config
          ((loopDispatcherTable D).stateId (.other .loop))
          T0
          (loopDispatcherCounterTape counterLeft consumed (markers + tail)
            counterRight)
          T2) =
      ThreeTape.config
        ((loopDispatcherTable D).stateId (.other .loop))
        T0
        (loopDispatcherCounterTape counterLeft (consumed + markers) tail
          counterRight)
        T2 := by
  induction markers generalizing consumed with
  | zero =>
      simp [Structured.Description.runConfig]
      done
  | succ markers ih =>
      rw [show Nat.succ markers + tail = (markers + tail) + 1 by lia]
      rw [show markers + 1 = 1 + markers by lia]
      rw [Structured.Description.runConfig_add]
      rw [loopDispatcherDescription_runConfig_one_other_succ]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (consumed + 1)
      done

theorem loopDispatcherDescription_runConfig_other_to_done
    (D : MachineDescription) (L : SimulatorLayout)
    (hclass : classifyState D L.config.state = StateClass.other)
    (sourceLayout : SimulatorLayout)
    (counterLeft counterRight : List (Option Bool)) :
    (loopDispatcherDescription D).runConfig (L.stage + 1)
        (ThreeTape.config
          ((loopDispatcherTable D).stateId (.other .loop))
          L.config.tape
          (loopDispatcherCounterTape counterLeft 0 L.stage counterRight)
          (loopDispatcherHitTape sourceLayout L.hit)) =
      ThreeTape.config
        ((loopDispatcherTable D).stateId (.other .done))
        (SimulatorLayout.run D L.stage L).config.tape
        (loopDispatcherCounterTape counterLeft L.stage 0 counterRight)
        (loopDispatcherHitTape sourceLayout
          (SimulatorLayout.run D L.stage L).hit) := by
  rw [simulatorLayout_run_eq_self_of_classifyState_other
    D L L.stage hclass]
  rw [Structured.Description.runConfig_add]
  have hmarkers :=
    loopDispatcherDescription_runConfig_other_markers D
      L.config.tape (loopDispatcherHitTape sourceLayout L.hit)
      counterLeft 0 L.stage 0 counterRight
  simp only [Nat.add_zero, Nat.zero_add] at hmarkers
  rw [hmarkers]
  exact loopDispatcherDescription_runConfig_one_other_zero D
    L.config.tape (loopDispatcherHitTape sourceLayout L.hit)
    counterLeft L.stage counterRight
  done

/-- Exact semantic endpoint obligation for the concrete sum-state table. -/
def LoopDispatcherSemanticEndpointObligation : Prop :=
  forall (D : MachineDescription) (L : SimulatorLayout),
    (loopDispatcherDescription D).runConfig
        (loopDispatcherRunSteps D L)
        (loopDispatcherSourceConfig D L) =
      loopDispatcherEndpointConfig D L

/-- The concrete dispatcher reaches the exact metadata-preserving semantic
endpoint. -/
theorem loopDispatcherSemanticEndpoint :
    LoopDispatcherSemanticEndpointObligation := by
  intro D L
  by_cases hstate : L.config.state ∈ fixedStepValues D
  · have hclass := classifyState_of_mem hstate
    rw [show loopDispatcherRunSteps D L = L.stage + 3 by
      simp [loopDispatcherRunSteps, hclass]]
    rw [show L.stage + 3 = 1 + (L.stage + 2) by lia]
    rw [Structured.Description.runConfig_add]
    unfold loopDispatcherSourceConfig
    rw [hclass]
    rw [loopDispatcherDescription_runConfig_one_dispatch_known D
      L.config.state hstate L.config.tape
      (FieldDecomposition.stageCounterTape L.stage)
      (FieldDecomposition.metadataHitTape L)]
    change
      (loopDispatcherDescription D).runConfig (L.stage + 2)
        (loopDispatcherKnownSourceConfig D L L [] []) = _
    rw [loopDispatcherDescription_runConfig_known_to_done D L
      hstate L [] []]
    unfold loopDispatcherKnownDoneConfig loopDispatcherEndpointConfig
      loopDispatcherEndpointState
    simp [hclass, SimulatorLayout.run,
      loopDispatcherConsumedStageCounterTape]
    done
  · have hclass := classifyState_of_not_mem hstate
    rw [show loopDispatcherRunSteps D L = L.stage + 2 by
      simp [loopDispatcherRunSteps, hclass]]
    rw [show L.stage + 2 = 1 + (L.stage + 1) by lia]
    rw [Structured.Description.runConfig_add]
    unfold loopDispatcherSourceConfig
    rw [hclass]
    rw [loopDispatcherDescription_runConfig_one_dispatch_other D
      L.config.tape
      (FieldDecomposition.stageCounterTape L.stage)
      (FieldDecomposition.metadataHitTape L)]
    change
      (loopDispatcherDescription D).runConfig (L.stage + 1)
        (ThreeTape.config
          ((loopDispatcherTable D).stateId (.other .loop))
          L.config.tape
          (loopDispatcherCounterTape [] 0 L.stage [])
          (loopDispatcherHitTape L L.hit)) = _
    rw [loopDispatcherDescription_runConfig_other_to_done D L
      hclass L [] []]
    unfold loopDispatcherEndpointConfig loopDispatcherEndpointState
      loopDispatcherConsumedStageCounterTape
    simp [hclass]
    done

/-!
## Required done-state witness closeout

The semantic dispatcher deliberately stops at the proof-relevant
{lit}`done` controls.  It may not enter a common halt until the final known
state has been made physical: lowering erases typed control, and the compact
metadata retains the original raw state rather than the final known state.
-/

@[simp] theorem loopDispatcherNext_known_done
    (D : MachineDescription) (state : Nat)
    (r0 r1 r2 : Option Bool) :
    loopDispatcherNext D (.known (.done state)) r0 r1 r2 = none := by
  rfl

@[simp] theorem loopDispatcherNext_other_done
    (D : MachineDescription) (r0 r1 r2 : Option Bool) :
    loopDispatcherNext D (.other .done) r0 r1 r2 = none := by
  rfl

/-- Self-delimiting branch witness appended to the right of the hit cell. -/
inductive LoopDispatcherDoneWitness where
  | known (finalState : Nat)
  | other
deriving DecidableEq, Repr

/-- A Boolean branch tag followed, on the known branch, by the fixed unary
encoding of the final state. -/
def LoopDispatcherDoneWitness.code :
    LoopDispatcherDoneWitness -> Word MachineCodeSymbol
  | .known finalState =>
      encodeBoolAppend true (encodeNatAppend finalState [])
  | .other => encodeBoolAppend false []

def LoopDispatcherDoneWitness.bits
    (witness : LoopDispatcherDoneWitness) : Word Bool :=
  encodeCodeWordAsInput witness.code

/-- Exact witness selected by the semantic endpoint. -/
def loopDispatcherDoneWitness
    (D : MachineDescription) (L : SimulatorLayout) :
    LoopDispatcherDoneWitness :=
  match classifyState D L.config.state with
  | .known _ _ =>
      .known (SimulatorLayout.run D L.stage L).config.state
  | .other => .other

/-- Tape-2 closeout target.  The compact original metadata and scratch-width
markers stay to the left of the hit head.  Its existing right blank separates
the hit from the new self-delimiting branch witness. -/
def loopDispatcherDoneWitnessTape
    (D : MachineDescription) (L : SimulatorLayout) : Tape Bool :=
  tapeAtCells
    (FieldDecomposition.metadataPrefixCells L).reverse
    (some (SimulatorLayout.run D L.stage L).hit ::
      none ::
        List.append
          ((loopDispatcherDoneWitness D L).bits.map some) [none])

@[simp] theorem loopDispatcherDoneWitnessTape_read
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.read (loopDispatcherDoneWitnessTape D L) =
      some (SimulatorLayout.run D L.stage L).hit := by
  rfl

theorem loopDispatcherDoneWitnessTape_left
    (D : MachineDescription) (L : SimulatorLayout) :
    (loopDispatcherDoneWitnessTape D L).left =
      (FieldDecomposition.metadataPrefixCells L).reverse := by
  rfl

def loopDispatcherDoneWitnessTapes
    (D : MachineDescription) (L : SimulatorLayout) :
    List (Tape Bool) :=
  [ (SimulatorLayout.run D L.stage L).config.tape
  , loopDispatcherConsumedStageCounterTape L.stage
  , loopDispatcherDoneWitnessTape D L ]

/-- Exact remaining finite-table leaf before common halt.

For fixed {lit}`D`, the known cases range only over {lit}`fixedStepValues D`,
so a finite q-specific emitter can append the known marker and
{lit}`encodeNat q`.  The generic branch appends only the other marker and
leaves the raw state in {name}`FieldDecomposition.metadata`.  No theorem in
this module assumes this construction before it is implemented.
-/
def LoopDispatcherDoneWitnessCloseoutSpec
    (D : MachineDescription) (closeout : Description) : Prop :=
  closeout.WellFormed ∧
    closeout.HaltTransitionFree ∧
    SupportsReadWriteRows3 closeout ∧
    forall L : SimulatorLayout,
      closeout.HaltsWithTapes
        (loopDispatcherEndpointConfig D L)
        (loopDispatcherDoneWitnessTapes D L)

def LoopDispatcherDoneWitnessCloseoutObligation : Prop :=
  forall D : MachineDescription,
    exists closeout : Description,
      LoopDispatcherDoneWitnessCloseoutSpec D closeout

end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
