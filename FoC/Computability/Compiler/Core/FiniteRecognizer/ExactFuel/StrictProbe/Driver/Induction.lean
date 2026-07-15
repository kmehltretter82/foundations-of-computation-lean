import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.StuckSink
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.Fuel

set_option doc.verso true

/-!
# Exact-fuel driver induction

An abstract two-exit driver contract converts the physical strict-probe runs
into exact bounded-halting semantics. The carried-frame adapter supplies the
successor equation required by the induction.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace DriverInduction

/-- The selected-machine configuration after one present transition. -/
def selectedTarget {stateCount : Nat}
    (write : Option MachineCodeSymbol) (direction : Direction)
    (nextState : Fin stateCount)
    (c : TuringMachine.Configuration MachineCodeSymbol (Fin stateCount)) :
    TuringMachine.Configuration MachineCodeSymbol (Fin stateCount) where
  state := nextState
  tape := Tape.move direction (Tape.write write c.tape)

end DriverInduction

namespace RelationalDriverInduction

open SerializedFieldComposer

def semanticConfig {stateCount : Nat}
    (F : CarriedStateFrame.LoopFrame stateCount) :
    TuringMachine.Configuration MachineCodeSymbol (Fin stateCount) :=
  (CarriedStateFrame.semanticLayout F).config

theorem semanticConfig_afterSelected {stateCount : Nat}
    (fuel : Nat) (write : Option MachineCodeSymbol)
    (direction : Direction) (nextState : Fin stateCount)
    (F : CarriedStateFrame.LoopFrame stateCount) :
    semanticConfig
        (CarriedStateFrame.afterSelected
          fuel write direction nextState F) =
      DriverInduction.selectedTarget write direction nextState
        (semanticConfig F) := by
  unfold semanticConfig
  rw [CarriedStateFrame.semanticLayout_afterSelected_eq_transitionTarget]
  cases F with
  | mk carriedState physicalFrame =>
      cases physicalFrame with
      | mk layoutFuel placeholder left head right =>
          cases direction with
          | left => cases left <;> rfl
          | right => cases right <;> rfl

def Represents {stateCount : Nat}
    (callerData : Word MachineCodeSymbol)
    (fuel : Nat) (F : CarriedStateFrame.LoopFrame stateCount)
    (T : Tape MachineCodeSymbol) : Prop :=
  Tape.Equiv T
    (Tape.input
      (Frame.protectedWord
        (CarriedStateFrame.withFuel fuel F).physicalFrame callerData))

theorem represents_of_equiv {stateCount : Nat}
    {callerData : Word MachineCodeSymbol}
    {fuel : Nat} {F : CarriedStateFrame.LoopFrame stateCount}
    {T U : Tape MachineCodeSymbol}
    (hTU : Tape.Equiv T U) (hU : Represents callerData fuel F U) :
    Represents callerData fuel F T := by
  exact Tape.Equiv.trans hTU hU

def SuccessRun
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (source : TuringMachine.Configuration MachineCodeSymbol runnerState) :
    Prop :=
  exists endpoint,
    TuringMachine.Computes runner source endpoint ∧
      TuringMachine.Halted runner endpoint

def FailureRun
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (source : TuringMachine.Configuration MachineCodeSymbol runnerState) :
    Prop :=
  exists endpoint,
    TuringMachine.Computes runner source endpoint ∧
      ¬ TuringMachine.Halted runner endpoint ∧
      forall next, ¬ TuringMachine.Step runner endpoint next

/-- Physical driver contract indexed by the actual tape representative.  A
present successor may choose any representative of the updated protected
frame, which is then threaded into the recursive run. -/
structure RunContract {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (runner : TuringMachine MachineCodeSymbol runnerState)
    (callerData : Word MachineCodeSymbol) where
  source : Nat -> CarriedStateFrame.LoopFrame stateCount ->
    Tape MachineCodeSymbol ->
      TuringMachine.Configuration MachineCodeSymbol runnerState
  sourceTape :
    forall fuel F T, (source fuel F T).tape = T
  zeroAccept :
    forall F T,
      Represents callerData 0 F T ->
      (semanticConfig F).state = M.halt ->
        SuccessRun runner (source 0 F T)
  zeroReject :
    forall F T,
      Represents callerData 0 F T ->
      (semanticConfig F).state ≠ M.halt ->
        FailureRun runner (source 0 F T)
  succMissing :
    forall fuel F T,
      Represents callerData (fuel + 1) F T ->
      M.transition (semanticConfig F).state
          (Tape.read (semanticConfig F).tape) = none ->
        FailureRun runner (source (fuel + 1) F T)
  succPresent :
    forall fuel F T write direction nextState,
      Represents callerData (fuel + 1) F T ->
      M.transition (semanticConfig F).state
          (Tape.read (semanticConfig F).tape) =
        some (write, direction, nextState) ->
      exists T' : Tape MachineCodeSymbol,
        Represents callerData fuel
          (CarriedStateFrame.afterSelected
            fuel write direction nextState F) T' ∧
        TuringMachine.Computes runner (source (fuel + 1) F T)
          (source fuel
            (CarriedStateFrame.afterSelected
              fuel write direction nextState F) T')

theorem total_run {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    {callerData : Word MachineCodeSymbol}
    (D : RunContract M runner callerData) :
    forall fuel F T,
      Represents callerData fuel F T ->
        (TuringMachine.HaltsFromIn M fuel (semanticConfig F) ∧
            SuccessRun runner (D.source fuel F T)) ∨
          (¬ TuringMachine.HaltsFromIn M fuel (semanticConfig F) ∧
            FailureRun runner (D.source fuel F T)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro F T hrep
      by_cases hstate : (semanticConfig F).state = M.halt
      · exact Or.inl ⟨TuringMachine.haltsFromIn_zero_iff.mpr hstate,
          D.zeroAccept F T hrep hstate⟩
      · exact Or.inr ⟨fun hhalt =>
          hstate (TuringMachine.haltsFromIn_zero_iff.mp hhalt),
          D.zeroReject F T hrep hstate⟩
  | succ fuel ih =>
      intro F T hrep
      cases htransition :
          M.transition (semanticConfig F).state
            (Tape.read (semanticConfig F).tape) with
      | none =>
          exact Or.inr ⟨
            TuringMachine.not_haltsFromIn_succ_of_transition_eq_none
              htransition,
            D.succMissing fuel F T hrep htransition⟩
      | some action =>
          rcases action with ⟨write, direction, nextState⟩
          rcases D.succPresent fuel F T write direction nextState
              hrep htransition with
            ⟨T', hrep', hprefix⟩
          let F' := CarriedStateFrame.afterSelected
            fuel write direction nextState F
          rcases ih F' T' hrep' with hsuccess | hfailure
          · have htail := hsuccess.left
            rw [semanticConfig_afterSelected] at htail
            rcases hsuccess.right with ⟨endpoint, hrun, hhalted⟩
            exact Or.inl ⟨
              (TuringMachine.haltsFromIn_succ_iff_of_transition_eq_some
                htransition).mpr htail,
              endpoint, TuringMachine.computes_trans hprefix hrun,
              hhalted⟩
          · have htailFailure := hfailure.left
            rcases hfailure.right with
              ⟨endpoint, hrun, hnotHalted, hstuck⟩
            exact Or.inr ⟨
              fun hhalt => htailFailure (by
                rw [semanticConfig_afterSelected]
                exact
                  (TuringMachine.haltsFromIn_succ_iff_of_transition_eq_some
                    htransition).mp hhalt),
              endpoint, TuringMachine.computes_trans hprefix hrun,
              hnotHalted, hstuck⟩

structure ExitContract {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    {callerData : Word MachineCodeSymbol}
    (D : RunContract M runner callerData) : Prop where
  haltingTransitionsDisabled :
    TuringMachine.HaltingTransitionsDisabled runner

theorem haltsFrom_source_iff {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {runner : TuringMachine MachineCodeSymbol runnerState}
    {callerData : Word MachineCodeSymbol}
    (D : RunContract M runner callerData) (E : ExitContract D)
    (fuel : Nat) (F : CarriedStateFrame.LoopFrame stateCount)
    (T : Tape MachineCodeSymbol)
    (hrep : Represents callerData fuel F T) :
    TuringMachine.HaltsFrom runner (D.source fuel F T) <->
      TuringMachine.HaltsFromIn M fuel (semanticConfig F) := by
  rcases total_run D fuel F T hrep with hsuccess | hfailure
  · constructor
    · intro _
      exact hsuccess.left
    · intro _
      rcases hsuccess.right with ⟨endpoint, hrun, hhalted⟩
      exact ⟨endpoint, hrun, hhalted⟩
  · constructor
    · intro hhalt
      rcases hfailure.right with
        ⟨endpoint, hrun, hnotHalted, hstuck⟩
      exact False.elim
        ((TuringMachine.StuckSink.not_haltsFrom_of_computes_to_stuck_nonhalt
          E.haltingTransitionsDisabled hrun hnotHalted hstuck) hhalt)
    · intro hhalt
      exact False.elim (hfailure.left hhalt)

end RelationalDriverInduction
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
