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
| Stopped semantic diagonal | {lit}`self_halting_not_stopped_decidable_if_decoder_universal` | Proved conditionally on decoder universality, with no decidable-to-acceptable Principle. The theorem uses the honest halt-stable distinct-output currency and is consistent with the legacy-collapse guardrail. It is semantic compatibility evidence, superseded as the endpoint by the unconditional finite-description negative conjuncts below. |
| Finite-description negative conjuncts (R1) | {lit}`concrete_machine_complement_self_halting_not_recognizable`, {lit}`concrete_machine_self_halting_undecidable_code_language` | Proved unconditionally. The complement of the valid self-halting language is not {lit}`RecognizableCodeLanguage`, and the language is {lit}`UndecidableCodeLanguage`, both in the canonical finite well-formed-description currency with no decoder universality, decidable-to-acceptable, or self-halting recognizability premise. A supposed complement recognizer contradicts itself on its own canonical code ({lit}`Computability.not_descriptionRecognizableCodeLanguage_compl_codeSelfHalting`); a decider would recognize the complement via the pointwise output acceptor. These are the intermediate release state R1: both negative conjuncts closed, positive conjunct isolated. {lit}`#print axioms` shows no {lit}`sorryAx`. |
| Raw code parsing | {lit}`ConcreteMachineDecode`, {lit}`ConcreteMachineDecodePrefix`, {lit}`ConcreteRawMachineCodeAccepts` | Proved and retained explicitly as raw syntax. Complete records and description prefixes can be parsed and executed without checking {lit}`MachineDescription.WellFormed`; encode/decode and prefix-append inversions are proved. These surfaces are distinct from canonical valid-code acceptance. |
| Valid-code checking | {lit}`ConcreteDescriptionCodeValid`, {lit}`ConcreteDescriptionCodeValidBool`, {lit}`concrete_valid_code_language_recursive` | Proved semantically and by a concrete finite description. Validity is complete decoding followed by finite-description well-formedness. The exact-code validator checks token alignment, the complete header, counted transition rows and bounds, the empty suffix, and pairwise determinism; it then emits normalized {lit}`[true]` or {lit}`[false]` through a halt-stable closeout. Incomplete records, trailing junk, zero-state descriptions, out-of-range states or transition endpoints, and conflicting lookup keys are rejected. Thus {lit}`ConcreteValidCodeLanguage` is a {lit}`RecursiveCodeLanguage` with no compiler Principle. |
| Prefix runner | {lit}`ConcreteUniversalPrefixRunnerConstruction` | Proved unconditionally as a finite construction. It recognizes the description-prefix/input language {lit}`ConcreteMachineCodePrefixAcceptedLanguage`, which is not the self-halting language: its description and input components vary independently. |
| Self-halting recognizer | {lit}`ConcreteMachineSelfHaltingLanguage`, target {lit}`RecognizableCodeLanguage` | Open construction, M6-audited, with phase 1 closed. No unconditional finite-description witness exists yet; the legacy K-shaped theorem still consumes semantic recognizability as its {lit}`hself` premise. The M6 audit selected route A (exact-code validator followed by a source-preserving {lit}`w ↦ w ++ w` duplicator into the closed unconditional universal-prefix runner) and proved its correctness at the specification level ({lit}`mem_codeSelfHalting_iff_valid_and_codePrefixAccepts_selfAppend` in {lit}`FoC.Computability.SelfHaltingReferenceSpec`). The halt-stable exact-code validator is now constructed and independently consumed by {lit}`concrete_valid_code_language_recursive`. The remaining M7 work is the route-A validator/duplication/runner composition and its recognizable-language package. |
| Decoder coverage | {lit}`ConcreteMachineDecoderUniversalForAcceptableLanguages` | Conditional and jointly refutable with the decidable-to-acceptable construction ({lit}`concrete_decidable_to_acceptable_and_decoder_universal_incompatible`). It descends from the open {lit}`SemanticEncodedInputDescriptionCompilerPrinciple`, whose source class quantifies over all acceptable languages and is too broad to discharge as stated. |
| Headline theorem | legacy {lit}`self_halting_re_not_recursive_and_complement_not_re_if_decoder_universal`; targets {lit}`RecognizableCodeLanguage`, {lit}`UndecidableCodeLanguage` | Negative conjuncts closed (R1 row above); positive conjunct and full three-way headline still open. The legacy statement remains conditional on the refutable premise pair and on {lit}`hself` with collapsed-predicate negatives. The two unconditional finite-description negative conjuncts are proved; the assumption-free three-way headline awaits the finite self-halting recognizer (positive conjunct). |
| Pair halting | {lit}`ConcreteMachinePairHaltingProblem` | Conditional. Undecidability transport uses proposition-valued preimage constructions; the faithful diagonal-pair machine is proved, but no checked finite composition backs the preimage principle. |

Consequently, the Section 5.3 development is at intermediate release state R1:
both negative conjuncts of the central theorem — complement nonrecognizability
and nondecidability of the valid self-halting language — are closed
unconditionally in the canonical description-backed finite currency, with no
decoder universality or compiler premise and no {lit}`sorryAx`. The canonical
finite contracts, the concrete halt-stable valid-code checker, and these two negative
endpoints are established. It should still not be described as a closed
formalization of the full central theorem: the assumption-free three-way
headline additionally needs the positive conjunct, a concrete finite
self-halting recognizer, which remains a separately gated finite-machine
campaign. The next construction step is to compose the validator with the
source-duplication and universal-prefix-runner phases.
-/

namespace FoC
namespace Book
namespace Chapter05
namespace Section03

end Section03
end Chapter05
end Book
end FoC
