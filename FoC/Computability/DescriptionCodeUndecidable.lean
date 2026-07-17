import FoC.Computability.Compiler.Core.Language.BoolOutputAcceptor
import FoC.Computability.DescriptionCodeLanguages

set_option doc.verso true

/-!
# Nondecidability of the valid self-halting language

This module closes the negative half of the Section 5.3 headline directly in
the finite description currency. A halt-stable finite-description decider for a
code language is turned into a well-formed finite-description recognizer by the
generalized pointwise output acceptor from
{module}`FoC.Computability.Compiler.Core.Language.BoolOutputAcceptor`. Applied
to the valid self-halting language, this bridge combines with the diagonal
complement-nonrecognizability theorem in
{module}`FoC.Computability.DescriptionCodeLanguages` to rule out any
finite-description decider, with no decoder universality or compiler premise.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open BoolOutputAcceptor

/--
A halt-stable code-language decider yields a well-formed recognizer of the same
language: run the decider and accept exactly when it outputs the accept symbol.
The pointwise output acceptor needs the decider's output behavior only on the
canonical encoded input, which the stopped decision contract supplies.
-/
theorem descriptionRecognizesCodeLanguage_boolOutputAcceptor_of_stoppedDecides
    {D : MachineDescription} {reject accept : Bool}
    {L : Language MachineCodeSymbol}
    (hD : StoppedDescriptionDecidesCodeLanguage D reject accept L) :
    DescriptionRecognizesCodeLanguage
      (BoolOutputAcceptorDescription D accept) L := by
  have hsource : D.SubroutineReady := ⟨hD.wellFormed, hD.haltTransitionFree⟩
  refine ⟨(boolOutputAcceptorDescription_subroutineReady hsource accept).left, ?_⟩
  intro w
  -- The decider outputs `[accept]` only when it accepts, so on the encoded
  -- input the acceptor halts iff the decider accepts iff `w ∈ L`.
  have hcoh :
      forall {T : Tape Bool},
        D.HaltsWithTape
            (MachineDescription.encodeCodeWordAsInput w) T ->
          List.Mem accept (Tape.normalizedOutput T) ->
            Tape.normalizedOutput T = [accept] := by
    intro T hhalt hmem
    have hout := MachineDescription.haltsWithOutput_of_haltsWithTape hhalt
    have heq := hD.output_eq_of_haltsWithOutput hout
    by_cases hwL : w ∈ L
    · exact heq.left hwL
    · have hrej := heq.right hwL
      rw [hrej] at hmem
      exact absurd (List.mem_singleton.mp hmem).symm hD.answers_ne
  have hiff :=
    boolOutputAcceptorDescription_haltsOnInput_iff_pointwise hsource accept
      (MachineDescription.encodeCodeWordAsInput w) hcoh
  have hmemL :
      D.HaltsWithOutput (MachineDescription.encodeCodeWordAsInput w) [accept] <->
        w ∈ L := by
    constructor
    · intro hout
      by_cases hwL : w ∈ L
      · exact hwL
      · exfalso
        have heq := (hD.output_eq_of_haltsWithOutput hout).right hwL
        injection heq with hac
        exact hD.answers_ne hac.symm
    · intro hwL
      exact (hD.correct w).left hwL
  exact hiff.trans hmemL

/-- A halt-stable finite-description-decidable code language is recognizable. -/
theorem descriptionRecognizableCodeLanguage_of_descriptionDecidable
    {L : Language MachineCodeSymbol}
    (h : DescriptionDecidableCodeLanguage L) :
    DescriptionRecognizableCodeLanguage L := by
  rcases h with ⟨D, reject, accept, hD⟩
  exact ⟨BoolOutputAcceptorDescription D accept,
    descriptionRecognizesCodeLanguage_boolOutputAcceptor_of_stoppedDecides hD⟩

/--
The valid self-halting language is not finite-description-decidable. A decider
would decide the complement too, hence recognize the complement, contradicting
diagonal complement nonrecognizability. This uses no decoder universality or
compiler premise, and does not assume self-halting recognizability, so the
positive conjunct remains isolated for the later recognizer construction.
-/
theorem not_descriptionDecidableCodeLanguage_codeSelfHalting :
    ¬ DescriptionDecidableCodeLanguage CodeSelfHaltingLanguage := by
  intro h
  have hcompl := descriptionDecidableCodeLanguage_complement h
  have hrec := descriptionRecognizableCodeLanguage_of_descriptionDecidable hcompl
  exact not_descriptionRecognizableCodeLanguage_compl_codeSelfHalting hrec

end Computability
end FoC
