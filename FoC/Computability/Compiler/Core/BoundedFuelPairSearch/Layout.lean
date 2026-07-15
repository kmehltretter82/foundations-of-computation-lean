import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.Contract

set_option doc.verso true

/-!
# Candidate encoding for bounded fuel-pair search

This module fixes the exact code word and Boolean input used for one bounded
fuel-pair candidate.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace BoundedFuelPairSearch

/-- The complete code-word input supplied to the candidate runner. -/
def CandidateCode
    (w : Word Bool) (limit candidateFuel : Nat) :
    Word MachineCodeSymbol :=
  PairedRecognizerDovetailControllerStageAttemptFuelInputCode
    w limit candidateFuel

/-- Exact physical Boolean bits supplied to the candidate runner. -/
def CandidateInputBits
    (w : Word Bool) (limit candidateFuel : Nat) : Word Bool :=
  encodeCodeWordAsInput (CandidateCode w limit candidateFuel)

theorem candidateInputBits_injective
    {w₁ w₂ : Word Bool}
    {limit₁ limit₂ candidateFuel₁ candidateFuel₂ : Nat}
    (h :
      CandidateInputBits w₁ limit₁ candidateFuel₁ =
        CandidateInputBits w₂ limit₂ candidateFuel₂) :
    w₁ = w₂ ∧ limit₁ = limit₂ ∧
      candidateFuel₁ = candidateFuel₂ := by
  apply
    pairedRecognizerDovetailControllerStageAttemptFuelInputCode_injective
  exact encodeCodeWordAsInput_injective h

end BoundedFuelPairSearch
end Computability
end FoC
