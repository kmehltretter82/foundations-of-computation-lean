import FoC.Computability.Compiler.Core.DovetailCode

set_option doc.verso true

/-!
# Output-indexed fuel-pair search contracts

The old bounded fuel-pair enumerator asked one halt-transition-free machine to
produce every result word witnessed by a hidden pair.  That contract is not
functional.  This module instead fixes the observable Boolean at construction
time: one machine searches for evidence of one Boolean and always emits that
same Boolean when it succeeds.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

/-- Existential evidence that some hidden pair makes {name}`runner` produce {name}`b`. -/
def PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence
    (runner : MachineDescription) (w : Word Bool) (b : Bool) : Prop :=
  exists limit : Nat,
  exists fuel : Nat,
    runner.HaltsWithOutput
      (encodeCodeWordAsInput
        (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
          w limit fuel))
      (encodeCodeWordAsInput (encodeBoolWord [b]))

/-- Indexed form of fuel-pair evidence for exact forward/closed proofs. -/
structure PairedRecognizerDovetailControllerStageAttemptFuelPairEvidenceWitness
    (runner : MachineDescription) (b : Bool) where
  input : Word Bool
  limit : Nat
  fuel : Nat
  runner_halts :
    runner.HaltsWithOutput
      (encodeCodeWordAsInput
        (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
          input limit fuel))
      (encodeCodeWordAsInput (encodeBoolWord [b]))

/-- Compatibility with the former result-word existential relation. -/
theorem pairedRecognizerDovetailControllerStageAttemptFuelPairEvidence_iff_exists_result
    {runner : MachineDescription} {w : Word Bool} {b : Bool} :
    PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence runner w b <->
      exists limit : Nat,
      exists fuel : Nat,
      exists result : Word Bool,
        runner.HaltsWithOutput
          (encodeCodeWordAsInput
            (PairedRecognizerDovetailControllerStageAttemptFuelInputCode
              w limit fuel))
          (encodeCodeWordAsInput (encodeBoolWord result)) ∧
        PairedRecognizerDovetailControllerRawOutput result = some [b] := by
  constructor
  · intro h
    rcases h with ⟨limit, fuel, hrun⟩
    refine ⟨limit, fuel, [b], hrun, ?_⟩
    simpa [PairedRecognizerDovetailControllerRawOutput] using
      (DovetailControllerLayout.rawOutput_eq_some_singleton_iff [b] b).mpr rfl
  · intro h
    rcases h with ⟨limit, fuel, result, hrun, hraw⟩
    have hresult : result = [b] :=
      (DovetailControllerLayout.rawOutput_eq_some_singleton_iff result b).mp
        (by simpa [PairedRecognizerDovetailControllerRawOutput] using hraw)
    subst result
    exact ⟨limit, fuel, hrun⟩

/-- The exact fixed-Boolean handoff tape used by an output-indexed searcher. -/
def PairedRecognizerDovetailControllerStageAttemptFuelPairBoolRightShiftedOutputTape
    (b : Bool) : Tape Bool :=
  Tape.move Direction.right (Tape.input [b])

theorem pairedRecognizerDovetailControllerStageAttemptFuelPairBoolRightShiftedOutputTape_normalizedOutput
    (b : Bool) :
    Tape.normalizedOutput
        (PairedRecognizerDovetailControllerStageAttemptFuelPairBoolRightShiftedOutputTape
          b) =
      [b] := by
  rw [PairedRecognizerDovetailControllerStageAttemptFuelPairBoolRightShiftedOutputTape,
    Tape.normalizedOutput_move]
  simpa [Tape.output] using (Tape.normalizedOutput_output [b])

/-- One fixed-Boolean search machine realizes exactly the matching evidence. -/
structure PairedRecognizerDovetailControllerStageAttemptFuelPairBoolSearchSpec
    (runner searcher : MachineDescription) (b : Bool) : Prop where
  subroutineReady : searcher.SubroutineReady
  forward :
    forall w : Word Bool,
      PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence runner w b ->
        searcher.HaltsWithOutput w [b]
  closed :
    forall w out : Word Bool,
      searcher.HaltsWithOutput w out ->
        out = [b] ∧
          PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence
            runner w b

namespace PairedRecognizerDovetailControllerStageAttemptFuelPairBoolSearchSpec

/-- Fixed-output forward/closed behavior gives the expected evidence iff. -/
theorem realizes
    {runner searcher : MachineDescription} {b : Bool}
    (h :
      PairedRecognizerDovetailControllerStageAttemptFuelPairBoolSearchSpec
        runner searcher b)
    (w : Word Bool) :
    searcher.HaltsWithOutput w [b] <->
      PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence
        runner w b := by
  constructor
  · intro hhalt
    exact (h.closed w [b] hhalt).right
  · exact h.forward w

end PairedRecognizerDovetailControllerStageAttemptFuelPairBoolSearchSpec

/-- A construction-time family contains one honest searcher for each Boolean. -/
structure PairedRecognizerDovetailControllerStageAttemptFuelPairSearchFamily
    (runner : MachineDescription) where
  machine : Bool -> MachineDescription
  spec :
    forall b : Bool,
      PairedRecognizerDovetailControllerStageAttemptFuelPairBoolSearchSpec
        runner (machine b) b

def PairedRecognizerDovetailControllerStageAttemptFuelPairSearchFamilyConstruction :
    Prop :=
  forall runner : MachineDescription,
    runner.SubroutineReady ->
      Nonempty
        (PairedRecognizerDovetailControllerStageAttemptFuelPairSearchFamily
          runner)

/-- Optional premise for collapsing the Boolean-indexed family to one output. -/
def PairedRecognizerDovetailControllerStageAttemptFuelPairObservableCoherent
    (runner : MachineDescription) : Prop :=
  forall w : Word Bool,
  forall b₁ b₂ : Bool,
    PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence runner w b₁ ->
    PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence runner w b₂ ->
      b₁ = b₂

end Computability
end FoC
