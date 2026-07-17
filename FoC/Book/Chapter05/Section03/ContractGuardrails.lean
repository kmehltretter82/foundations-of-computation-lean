import FoC.Book.Chapter05.Section02.ContractGuardrails
import FoC.Book.Chapter05.Section03.Basic

set_option doc.verso true

/-!
# Section 5.3: Contract Guardrails

This page records the currency collapse that constrains the Section 5.3
book-facing theorems. The results are proof obligations for API repair, not
examples of the intended textbook claims.

Section 5.2 already proves
{name (full := FoC.Book.Chapter05.Section02.every_language_turingDecidable_under_legacy_contract)}`every_language_turingDecidable_under_legacy_contract`:
the legacy {name (full := FoC.Computability.TuringDecidable)}`TuringDecidable`
predicate is satisfied by every language because its two answer symbols may
coincide. Consequently the legacy undecidability endpoint of this section is
unsatisfiable, and the conditional headline theorems have jointly refutable
premises: a decidable-to-acceptable construction would convert the
legacy-decidable complement of self-halting into an acceptor, and decoder
universality refutes exactly that acceptor.

None of the theorems below is a textbook endpoint. They pin the defect so the
repaired currency — stopped finite deciders and description-backed code
languages — cannot silently regress to the collapsed one.
-/

namespace FoC
namespace Book
namespace Chapter05
namespace Section03

open Languages
open Computability

/--
Specialization of the Section 5.2 collapse witness: the concrete self-halting
language is legacy-decidable, so its legacy decidability carries no
information.
-/
theorem concrete_self_halting_turingDecidable_under_legacy_contract :
    RecursiveTuringLanguage ConcreteMachineSelfHaltingLanguage :=
  Section02.every_language_turingDecidable_under_legacy_contract _

/-- The complement of concrete self-halting is legacy-decidable as well. -/
theorem concrete_complement_self_halting_turingDecidable_under_legacy_contract :
    RecursiveTuringLanguage
      (Language.Compl ConcreteMachineSelfHaltingLanguage) :=
  Section02.every_language_turingDecidable_under_legacy_contract _

/--
Under the legacy contract no language whatsoever is undecidable: the
{name}`UndecidableTuringLanguage` endpoint is unsatisfiable and cannot state a
textbook impossibility result.
-/
theorem no_language_undecidable_under_legacy_contract
    (L : Language alpha) :
    ¬ UndecidableTuringLanguage L :=
  fun h => h (Section02.every_language_turingDecidable_under_legacy_contract L)

/--
The two named premises of the Section 5.3 conditional headline cannot coexist.
A decidable-to-acceptable construction converts the legacy-decidable complement
of self-halting into an acceptor, and decoder universality refutes exactly that
acceptor through the diagonal argument.
-/
theorem concrete_decidable_to_acceptable_and_decoder_universal_incompatible :
    ¬ (DecidableToAcceptableConstruction ConcreteMachineCodeSymbol ∧
        ConcreteMachineDecoderUniversalForAcceptableLanguages) := by
  intro h
  exact
    concrete_machine_complement_self_halting_not_recursively_enumerable_if_decoder_universal
      h.right
      (h.left (Language.Compl ConcreteMachineSelfHaltingLanguage)
        (Section02.every_language_turingDecidable_under_legacy_contract _))

/--
Any universal decoder for acceptable languages refutes the legacy
decidable-to-acceptable construction over the machine-code alphabet.
-/
theorem concrete_decoder_universal_refutes_decidable_to_acceptable
    (huniv : ConcreteMachineDecoderUniversalForAcceptableLanguages) :
    ¬ DecidableToAcceptableConstruction ConcreteMachineCodeSymbol :=
  fun haccept =>
    concrete_decidable_to_acceptable_and_decoder_universal_incompatible
      ⟨haccept, huniv⟩

/--
The legacy decidable-to-acceptable construction over the machine-code alphabet
refutes decoder universality for acceptable languages.
-/
theorem concrete_decidable_to_acceptable_refutes_decoder_universal
    (haccept : DecidableToAcceptableConstruction ConcreteMachineCodeSymbol) :
    ¬ ConcreteMachineDecoderUniversalForAcceptableLanguages :=
  fun huniv =>
    concrete_decidable_to_acceptable_and_decoder_universal_incompatible
      ⟨haccept, huniv⟩

end Section03
end Chapter05
end Book
end FoC
