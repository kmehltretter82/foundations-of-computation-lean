import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.Layout
import FoC.Computability.Compiler.Core.FixedDescBoundedSim.Spec

set_option doc.verso true

/-!
# Total candidate-output validation seam

After the fixed-description bounded simulator returns, fuel-pair search must
make a total decision: either the scheduled runner configuration is halted
with the fixed encoded Boolean output, or the search must reset and advance to
the next candidate.  In particular, an ordinary recognizer is insufficient at
this boundary because divergence on a mismatch would make the search unfair.

This module fixes the pure decision, its exact padded-tape semantics, and the
machine contract needed by the search loop.  The finite-machine realization is
kept as an explicit construction proposition: the existing canonical layout
recognizer validates the encoding but does not return a negative result, while
the fuel-output recognizer likewise diverges on semantic mismatches.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace BoundedFuelPairSearch

/-!
## Pure layout decision
-/

/-- Semantic success for a decoded bounded-run layout. -/
def CandidateLayoutSuccess
    (runner : MachineDescription) (b : Bool)
    (L : SimulatorLayout) : Prop :=
  L.config.state = runner.halt ∧
    Tape.normalizedOutput L.config.tape =
      encodeCodeWordAsInput (encodeBoolWord [b])

instance candidateLayoutSuccessDecidable
    (runner : MachineDescription) (b : Bool)
    (L : SimulatorLayout) :
    Decidable (CandidateLayoutSuccess runner b L) := by
  dsimp [CandidateLayoutSuccess]
  infer_instance

/-- Total Boolean decision for a decoded bounded-run layout. -/
def candidateLayoutDecision
    (runner : MachineDescription) (b : Bool)
    (L : SimulatorLayout) : Bool :=
  decide (CandidateLayoutSuccess runner b L)

theorem candidateLayoutDecision_eq_true_iff
    (runner : MachineDescription) (b : Bool)
    (L : SimulatorLayout) :
    candidateLayoutDecision runner b L = true <->
      CandidateLayoutSuccess runner b L := by
  simp [candidateLayoutDecision]

theorem candidateLayoutDecision_eq_false_iff
    (runner : MachineDescription) (b : Bool)
    (L : SimulatorLayout) :
    candidateLayoutDecision runner b L = false <->
      ¬ CandidateLayoutSuccess runner b L := by
  simp [candidateLayoutDecision]

/-!
## Exact padded-tape decision
-/

/-- Decode a canonical simulator layout from the normalized contents of a
possibly scratch-padded tape. -/
def decodePaddedSimulatorLayout
    (T : Tape Bool) : Option SimulatorLayout :=
  match decodeCodeWordAsInput (Tape.normalizedOutput T) with
  | none => none
  | some code => SimulatorLayout.decodeComplete code

/-- Total validation of a physical padded simulator-output tape.  Malformed
physical inputs are classified as failure. -/
def candidatePaddedTapeDecision
    (runner : MachineDescription) (b : Bool)
    (T : Tape Bool) : Bool :=
  match decodePaddedSimulatorLayout T with
  | none => false
  | some L => candidateLayoutDecision runner b L

/-- Exact padded output produced by the fixed-description simulator for one
scheduled candidate. -/
def CandidatePaddedRunTape
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) : Tape Bool :=
  FixedDescriptionBoundedSimulatorPaddedOutputTape runner
    (CandidateInitialLayout runner w i)

theorem decodePaddedSimulatorLayout_fixedDescriptionOutput
    (runner : MachineDescription) (L : SimulatorLayout) :
    decodePaddedSimulatorLayout
        (FixedDescriptionBoundedSimulatorPaddedOutputTape runner L) =
      some (SimulatorLayout.run runner L.stage L) := by
  have hnormalized :
      Tape.normalizedOutput
          (FixedDescriptionBoundedSimulatorPaddedOutputTape runner L) =
        FixedDescriptionBoundedSimulatorOutput runner L := by
    simpa [FixedDescriptionBoundedSimulatorPaddedOutputTape] using
      FixedDescriptionBoundedSimulatorPaddedTape_normalizedOutput
        (FixedDescriptionBoundedSimulatorOutput runner L)
        (Tape.contextLength
          (Tape.input (FixedDescriptionBoundedSimulatorInput L)))
  unfold decodePaddedSimulatorLayout
  rw [hnormalized]
  simp [FixedDescriptionBoundedSimulatorOutput,
    SimulatorLayout.asBoolInput,
    decodeCodeWordAsInput_encodeCodeWordAsInput,
    SimulatorLayout.decodeComplete_encode]

theorem decodePaddedSimulatorLayout_candidateRun
    (runner : MachineDescription) (w : Word Bool)
    (i : ScheduleIndex) :
    decodePaddedSimulatorLayout (CandidatePaddedRunTape runner w i) =
      some (CandidateRunLayout runner w i) := by
  simpa [CandidatePaddedRunTape, CandidateRunLayout] using
    decodePaddedSimulatorLayout_fixedDescriptionOutput runner
      (CandidateInitialLayout runner w i)

theorem candidatePaddedTapeDecision_eq_true_iff
    (runner : MachineDescription) (w : Word Bool) (b : Bool)
    (i : ScheduleIndex) :
    candidatePaddedTapeDecision runner b
        (CandidatePaddedRunTape runner w i) = true <->
      runner.HaltsWithOutputIn i.scheduleBound
        (CandidateInputBits w i.limit i.candidateFuel)
        (encodeCodeWordAsInput (encodeBoolWord [b])) := by
  rw [candidatePaddedTapeDecision, decodePaddedSimulatorLayout_candidateRun]
  rw [candidateLayoutDecision_eq_true_iff]
  exact candidateRunLayout_fixedBoolSuccess_iff runner w b i

theorem candidatePaddedTapeDecision_eq_false_iff
    (runner : MachineDescription) (w : Word Bool) (b : Bool)
    (i : ScheduleIndex) :
    candidatePaddedTapeDecision runner b
        (CandidatePaddedRunTape runner w i) = false <->
      ¬ runner.HaltsWithOutputIn i.scheduleBound
        (CandidateInputBits w i.limit i.candidateFuel)
        (encodeCodeWordAsInput (encodeBoolWord [b])) := by
  constructor
  · intro hfalse hrun
    have htrue :=
      (candidatePaddedTapeDecision_eq_true_iff runner w b i).mpr hrun
    rw [htrue] at hfalse
    contradiction
  · intro hnot
    have hcases :
        candidatePaddedTapeDecision runner b
              (CandidatePaddedRunTape runner w i) = false ∨
          candidatePaddedTapeDecision runner b
              (CandidatePaddedRunTape runner w i) = true := by
      cases candidatePaddedTapeDecision runner b
          (CandidatePaddedRunTape runner w i) <;> simp
    cases hcases with
    | inl hfalse => exact hfalse
    | inr htrue =>
        exact False.elim
          (hnot
            ((candidatePaddedTapeDecision_eq_true_iff runner w b i).mp
              htrue))

theorem candidatePaddedTapeDecision_total
    (runner : MachineDescription) (w : Word Bool) (b : Bool)
    (i : ScheduleIndex) :
    candidatePaddedTapeDecision runner b
          (CandidatePaddedRunTape runner w i) = true ∨
      candidatePaddedTapeDecision runner b
          (CandidatePaddedRunTape runner w i) = false := by
  cases candidatePaddedTapeDecision runner b
      (CandidatePaddedRunTape runner w i) <;> simp

/-!
## Physical validator contract
-/

/-- Scratch-padded Boolean outcome consumed by the search-loop brancher.
{lit}`true` means success and {lit}`false` means reset/advance.  Retaining the
source context length is essential: an exact one-bit tape would demand an
impossible shrink of the padded simulator window. -/
def CandidateValidationOutputTape
    (source : Tape Bool) (success : Bool) : Tape Bool :=
  FixedDescriptionBoundedSimulatorPaddedTape [success]
    (Tape.contextLength source)

theorem candidateValidationOutputTape_eq
    (source : Tape Bool) (success : Bool) :
    CandidateValidationOutputTape source success =
      { left := []
        head := some success
        right := List.replicate (Tape.contextLength source) none } := by
  rfl

@[simp] theorem candidateValidationOutputTape_read
    (source : Tape Bool) (success : Bool) :
    Tape.read (CandidateValidationOutputTape source success) =
      some success := by
  rfl

theorem candidateValidationOutputTape_normalizedOutput
    (source : Tape Bool) (success : Bool) :
    Tape.normalizedOutput (CandidateValidationOutputTape source success) =
      [success] := by
  exact FixedDescriptionBoundedSimulatorPaddedTape_normalizedOutput
    ([success] : Word Bool) (Tape.contextLength source)

theorem candidateValidationOutputTape_contextLength
    (source : Tape Bool) (success : Bool) :
    Tape.contextLength (CandidateValidationOutputTape source success) =
      Tape.contextLength source := by
  simp [CandidateValidationOutputTape,
    FixedDescriptionBoundedSimulatorPaddedTape,
    Tape.contextLength]

theorem candidateValidationOutputTape_injective
    (source : Tape Bool) {a b : Bool}
    (h : CandidateValidationOutputTape source a =
      CandidateValidationOutputTape source b) :
    a = b := by
  have hout := congrArg Tape.normalizedOutput h
  rw [candidateValidationOutputTape_normalizedOutput source,
    candidateValidationOutputTape_normalizedOutput source] at hout
  exact List.cons.inj hout |>.left

/-- A physical validator always returns on exact padded candidate outputs and
returns precisely the pure decision above. -/
structure CandidatePaddedValidatorSpec
    (runner validator : MachineDescription) (b : Bool) : Prop where
  subroutineReady : validator.SubroutineReady
  forward :
    forall w : Word Bool,
    forall i : ScheduleIndex,
      validator.HaltsFromTape
        (CandidatePaddedRunTape runner w i)
        (CandidateValidationOutputTape
          (CandidatePaddedRunTape runner w i)
          (candidatePaddedTapeDecision runner b
            (CandidatePaddedRunTape runner w i)))
  closed :
    forall w : Word Bool,
    forall i : ScheduleIndex,
    forall T : Tape Bool,
      validator.HaltsFromTape
          (CandidatePaddedRunTape runner w i) T ->
        T = CandidateValidationOutputTape
          (CandidatePaddedRunTape runner w i)
          (candidatePaddedTapeDecision runner b
            (CandidatePaddedRunTape runner w i))

/-- Honest finite-machine leaf for total candidate validation. -/
def CandidatePaddedValidatorConstruction : Prop :=
  forall runner : MachineDescription,
  forall b : Bool,
    exists validator : MachineDescription,
      CandidatePaddedValidatorSpec runner validator b

namespace CandidatePaddedValidatorSpec

theorem haltsOnSuccess_iff
    {runner validator : MachineDescription} {b : Bool}
    (hvalidator : CandidatePaddedValidatorSpec runner validator b)
    (w : Word Bool) (i : ScheduleIndex) :
    validator.HaltsFromTape
        (CandidatePaddedRunTape runner w i)
        (CandidateValidationOutputTape
          (CandidatePaddedRunTape runner w i) true) <->
      runner.HaltsWithOutputIn i.scheduleBound
        (CandidateInputBits w i.limit i.candidateFuel)
        (encodeCodeWordAsInput (encodeBoolWord [b])) := by
  constructor
  · intro hsuccess
    have heq :=
      MachineDescription.haltsFromTape_functional_of_haltTransitionFree
        hvalidator.subroutineReady.right hsuccess
        (hvalidator.forward w i)
    have hdecision :
        candidatePaddedTapeDecision runner b
            (CandidatePaddedRunTape runner w i) = true :=
      candidateValidationOutputTape_injective
        (CandidatePaddedRunTape runner w i) heq.symm
    exact
      (candidatePaddedTapeDecision_eq_true_iff runner w b i).mp
        hdecision
  · intro hrun
    have hdecision :
        candidatePaddedTapeDecision runner b
            (CandidatePaddedRunTape runner w i) = true :=
      (candidatePaddedTapeDecision_eq_true_iff runner w b i).mpr hrun
    simpa [hdecision] using hvalidator.forward w i

theorem haltsOnFailure_iff
    {runner validator : MachineDescription} {b : Bool}
    (hvalidator : CandidatePaddedValidatorSpec runner validator b)
    (w : Word Bool) (i : ScheduleIndex) :
    validator.HaltsFromTape
        (CandidatePaddedRunTape runner w i)
        (CandidateValidationOutputTape
          (CandidatePaddedRunTape runner w i) false) <->
      ¬ runner.HaltsWithOutputIn i.scheduleBound
        (CandidateInputBits w i.limit i.candidateFuel)
        (encodeCodeWordAsInput (encodeBoolWord [b])) := by
  constructor
  · intro hfailure
    have heq :=
      MachineDescription.haltsFromTape_functional_of_haltTransitionFree
        hvalidator.subroutineReady.right hfailure
        (hvalidator.forward w i)
    have hdecision :
        candidatePaddedTapeDecision runner b
            (CandidatePaddedRunTape runner w i) = false :=
      candidateValidationOutputTape_injective
        (CandidatePaddedRunTape runner w i) heq.symm
    exact
      (candidatePaddedTapeDecision_eq_false_iff runner w b i).mp
        hdecision
  · intro hrun
    have hdecision :
        candidatePaddedTapeDecision runner b
            (CandidatePaddedRunTape runner w i) = false :=
      (candidatePaddedTapeDecision_eq_false_iff runner w b i).mpr hrun
    simpa [hdecision] using hvalidator.forward w i

end CandidatePaddedValidatorSpec

end BoundedFuelPairSearch

end Computability
end FoC
