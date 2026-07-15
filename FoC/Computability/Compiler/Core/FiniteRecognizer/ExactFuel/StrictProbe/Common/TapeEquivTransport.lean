import FoC.Computability.TapeLemmas
import FoC.Computability.TuringMachine

set_option doc.verso true

/-!
# Transport across equivalent tapes

Generic deterministic-step and exact-run transport across physical tape
representatives.
-/

namespace FoC
namespace Computability
namespace TuringMachine
namespace TapeEquivTransport

/-- One deterministic Turing-machine step transports across an equivalent
physical tape while preserving the next control state. -/
theorem step_of_tape_equiv
    {M : TuringMachine symbol state}
    {source target : Configuration symbol state}
    {tape : Tape symbol}
    (hstep : Step M source target)
    (htape : Tape.Equiv source.tape tape) :
    exists nextTape : Tape symbol,
      Step M
        { state := source.state, tape := tape }
        { state := target.state, tape := nextTape } ∧
      Tape.Equiv target.tape nextTape := by
  cases hstep with
  | mk haction =>
      rename_i write direction nextState
      refine ⟨Tape.move direction (Tape.write write tape), ?_, ?_⟩
      · exact Step.mk (by
          rw [← Tape.Equiv.read_eq htape]
          exact haction)
      · exact Tape.Equiv.move (Tape.Equiv.write htape write) direction

/-- A counted computation transports across equivalent source tapes with the
same step count and final control state. -/
theorem computesIn_of_tape_equiv
    {M : TuringMachine symbol state}
    {steps : Nat}
    {source target : Configuration symbol state}
    {tape : Tape symbol}
    (hrun : ComputesIn M steps source target)
    (htape : Tape.Equiv source.tape tape) :
    exists target' : Configuration symbol state,
      ComputesIn M steps
        { state := source.state, tape := tape } target' ∧
      target'.state = target.state ∧
      Tape.Equiv target.tape target'.tape := by
  induction hrun generalizing tape with
  | zero source =>
      exact
        ⟨{ state := source.state, tape := tape },
          ComputesIn.zero _, rfl, htape⟩
  | succ hstep htail ih =>
      rcases step_of_tape_equiv hstep htape with
        ⟨nextTape, hstep', hnextEquiv⟩
      rcases ih hnextEquiv with
        ⟨target', htail', hstate, htargetEquiv⟩
      exact
        ⟨target', ComputesIn.succ hstep' htail',
          hstate, htargetEquiv⟩

/-- Exact-run equation form of tape-equivalence transport. -/
theorem runConfigExact?_some_of_tape_equiv
    {M : TuringMachine symbol state}
    {steps : Nat}
    {source target : Configuration symbol state}
    {tape : Tape symbol}
    (hrun : M.runConfigExact? steps source = some target)
    (htape : Tape.Equiv source.tape tape) :
    exists target' : Configuration symbol state,
      M.runConfigExact? steps
          { state := source.state, tape := tape } = some target' ∧
      target'.state = target.state ∧
      Tape.Equiv target.tape target'.tape := by
  have hrunIn := runConfigExact?_eq_some_iff_computesIn.mp hrun
  rcases computesIn_of_tape_equiv hrunIn htape with
    ⟨target', hrunIn', hstate, htargetEquiv⟩
  exact
    ⟨target', runConfigExact?_eq_some_iff_computesIn.mpr hrunIn',
      hstate, htargetEquiv⟩

end TapeEquivTransport
end TuringMachine
end Computability
end FoC
