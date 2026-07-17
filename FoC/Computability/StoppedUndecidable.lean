import FoC.Computability.TransformPart2
import FoC.Computability.Undecidable

set_option doc.verso true

/-!
# Undecidability in the stopped-decider currency

This module combines the diagonal results from
{module}`FoC.Computability.Undecidable` with the unconditional stopped-decider
transformations from {module}`FoC.Computability.TransformPart2`.

The result below repairs the semantic Section 5.3 endpoint: decoder
universality rules out a halt-stable distinct-output decider for self-halting
without using the collapsed legacy {lit}`TuringDecidable` predicate or a
decidable-to-acceptable Principle. Decoder universality remains an explicit
premise; the unconditional finite-description theorem is a later milestone.
-/

namespace FoC
namespace Computability

open Languages

/--
Universal decoder coverage rules out a stopped decider for the corresponding
self-halting language.
-/
theorem selfHalting_not_stoppedDecidable_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (huniv : DecoderUniversalForAcceptableLanguages decodeAccepts) :
    ¬ StoppedTuringDecidable (SelfHaltingLanguage decodeAccepts) := by
  intro hdec
  apply compl_selfHalting_not_acceptable_if_decoder_universal huniv
  apply TuringMachine.stoppedTuringDecidable_to_turingAcceptable
  exact stoppedTuringDecidable_complement hdec

end Computability
end FoC
