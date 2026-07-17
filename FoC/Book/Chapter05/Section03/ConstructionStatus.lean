import FoC.Book.Chapter05.Section03.Basic
import FoC.Book.Chapter05.Section03.ContractGuardrails

set_option doc.verso true

/-!
# Section 5.3: Construction Status

This page records the current theorem currency of the Section 5.3
development. A conditional theorem is not counted as a closed textbook
endpoint, a legacy-currency theorem is not counted as an honest one, and a
proposition-valued principle is not counted as a finite construction.

Three defect classes appear below. *False currency* marks statements whose
underlying predicate is collapsed: Section 5.2 proves every language satisfies
legacy {lit}`TuringDecidable`, so legacy undecidability conclusions are
unsatisfiable endpoints. *Conditional* marks theorems whose premises name open
or refutable constructions. *Open construction* marks genuine finite-machine
work that has not been performed.

| Topic | Current surface | Status |
|---|---|---|
| Legacy decidability | {lit}`RecursiveTuringLanguage`, {lit}`UndecidableTuringLanguage` | False currency. Every language satisfies legacy {lit}`TuringDecidable` ({lit}`Section02.every_language_turingDecidable_under_legacy_contract`), so {lit}`no_language_undecidable_under_legacy_contract` shows the legacy undecidability endpoint is unsatisfiable. All {lit}`¬ TuringDecidable` conclusions in this section are compatibility-only. |
| Finite code-language contracts | {lit}`DescriptionRecognizesCodeLanguage`, {lit}`DescriptionRecognizableCodeLanguage`, {lit}`StoppedDescriptionDecidesCodeLanguage`, {lit}`DescriptionDecidableCodeLanguage` | Proved semantic foundation. Recognition requires a well-formed finite description and exact agreement on canonical four-bit block encodings. Decision additionally requires halt-transition-freedom and distinct normalized one-bit answers. Equality and complement transport are proved without a compiler Principle. The book-facing aliases are {lit}`RecognizableCodeLanguage`, {lit}`RecursiveCodeLanguage`, and {lit}`UndecidableCodeLanguage`. |
| Stopped semantic diagonal | {lit}`self_halting_not_stopped_decidable_if_decoder_universal` | Proved conditionally on decoder universality, with no decidable-to-acceptable Principle. The theorem uses the honest halt-stable distinct-output currency and is consistent with the legacy-collapse guardrail. It is semantic compatibility evidence, not the unconditional finite-description endpoint. |
| Raw code parsing | {lit}`ConcreteMachineDecode`, {lit}`ConcreteMachineDecodePrefix`, {lit}`ConcreteRawMachineCodeAccepts` | Proved and retained explicitly as raw syntax. Complete records and description prefixes can be parsed and executed without checking {lit}`MachineDescription.WellFormed`; encode/decode and prefix-append inversions are proved. These surfaces are distinct from canonical valid-code acceptance. |
| Semantic valid-code checking | {lit}`ConcreteDescriptionCodeValid`, {lit}`ConcreteDescriptionCodeValidBool`, {lit}`machineDescriptionWellFormedBool` | Proved. Validity is complete decoding followed by finite-description well-formedness, and the executable Boolean checker is sound and complete. Canonical codes satisfy validity exactly when their descriptions are well formed; incomplete records, trailing junk, zero-state descriptions, out-of-range states or transition endpoints, and conflicting lookup keys are rejected. This is an executable semantic checker, not yet the finite Turing-machine construction required by M4. |
| Prefix runner | {lit}`ConcreteUniversalPrefixRunnerConstruction` | Proved unconditionally as a finite construction. It recognizes the description-prefix/input language {lit}`ConcreteMachineCodePrefixAcceptedLanguage`, which is not the self-halting language: its description and input components vary independently. |
| Self-halting recognizer | {lit}`ConcreteMachineSelfHaltingLanguage`, target {lit}`RecognizableCodeLanguage` | Open construction. No unconditional finite-description witness exists; the legacy K-shaped theorem consumes semantic recognizability as its {lit}`hself` premise. An exact-code gate plus diagonal materialization is required. |
| Decoder coverage | {lit}`ConcreteMachineDecoderUniversalForAcceptableLanguages` | Conditional and jointly refutable with the decidable-to-acceptable construction ({lit}`concrete_decidable_to_acceptable_and_decoder_universal_incompatible`). It descends from the open {lit}`SemanticEncodedInputDescriptionCompilerPrinciple`, whose source class quantifies over all acceptable languages and is too broad to discharge as stated. |
| Headline theorem | legacy {lit}`self_halting_re_not_recursive_and_complement_not_re_if_decoder_universal`; targets {lit}`RecognizableCodeLanguage`, {lit}`UndecidableCodeLanguage` | False legacy currency and open construction. The existing statement is conditional on the refutable premise pair and on {lit}`hself`, and its negative conjuncts use the collapsed legacy predicate. The honest target vocabulary is now fixed, but no unconditional headline exists yet. |
| Pair halting | {lit}`ConcreteMachinePairHaltingProblem` | Conditional. Undecidability transport uses proposition-valued preimage constructions; the faithful diagonal-pair machine is proved, but no checked finite composition backs the preimage principle. |

Consequently, the Section 5.3 development should not be described as a closed
formalization of the central theorem. The canonical description-backed finite
currency and semantic valid-code checker are now established. The remaining
repair requires a halt-stable finite machine implementing that checker,
complement nonrecognizability and nondecidability without universality
premises, and a concrete finite self-halting recognizer for the positive
conjunct. The negative conjuncts constitute a publishable intermediate state;
the positive conjunct is a separately gated finite-machine campaign.
-/

namespace FoC
namespace Book
namespace Chapter05
namespace Section03

end Section03
end Chapter05
end Book
end FoC
