import FoC.Book.Chapter05.Section03.Basic
import FoC.Book.Chapter05.Section03.Cardinality
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
| Finite-description negative conjuncts | {lit}`concrete_machine_complement_self_halting_not_recognizable`, {lit}`concrete_machine_self_halting_undecidable_code_language` | Proved unconditionally. The complement of the valid self-halting language is not {lit}`RecognizableCodeLanguage`, and the language is {lit}`UndecidableCodeLanguage`, both in the canonical finite well-formed-description currency with no decoder universality, decidable-to-acceptable, or self-halting recognizability premise. A supposed complement recognizer contradicts itself on its own canonical code ({lit}`Computability.not_descriptionRecognizableCodeLanguage_compl_codeSelfHalting`); a decider would recognize the complement via the pointwise output acceptor. |
| Raw code parsing | {lit}`ConcreteMachineDecode`, {lit}`ConcreteMachineDecodePrefix`, {lit}`ConcreteRawMachineCodeAccepts` | Proved and retained explicitly as raw syntax. Complete records and description prefixes can be parsed and executed without checking {lit}`MachineDescription.WellFormed`; encode/decode and prefix-append inversions are proved. These surfaces are distinct from canonical valid-code acceptance. |
| Valid-code checking | {lit}`ConcreteDescriptionCodeValid`, {lit}`ConcreteDescriptionCodeValidBool`, {lit}`concrete_valid_code_language_recursive` | Proved semantically and by a concrete finite description. Validity is complete decoding followed by finite-description well-formedness. The exact-code validator checks token alignment, the complete header, counted transition rows and bounds, the empty suffix, and pairwise determinism; it then emits normalized {lit}`[true]` or {lit}`[false]` through a halt-stable closeout. Incomplete records, trailing junk, zero-state descriptions, out-of-range states or transition endpoints, and conflicting lookup keys are rejected. Thus {lit}`ConcreteValidCodeLanguage` is a {lit}`RecursiveCodeLanguage` with no compiler Principle. |
| Prefix runner | {lit}`ConcreteUniversalPrefixRunnerConstruction` | Proved unconditionally as a finite construction. It recognizes the description-prefix/input language {lit}`ConcreteMachineCodePrefixAcceptedLanguage`, which is not the self-halting language: its description and input components vary independently. |
| Self-halting recognizer | {lit}`concreteSelfHaltingRecognizerConstruction`, {lit}`concrete_machine_self_halting_recognizable` | Proved unconditionally by a well-formed finite Boolean description. The route-A machine rejects malformed, incomplete, and prefix-plus-junk codes with the exact validator, rewinds the preserved source, materializes {lit}`w ++ w`, lowers the finite code-alphabet runner, and invokes the unconditional universal-prefix machine. Its closed halting characterization is {lit}`ConcreteRecognizer.description_haltsOnInput_iff`; no {lit}`hself`, generic compiler Principle, or decoder-universality premise remains. The exact validator also retains its distinct valid-code-decider consumer {lit}`concrete_valid_code_language_recursive`. |
| Decoder coverage | {lit}`ConcreteMachineDecoderUniversalForAcceptableLanguages` | Conditional and jointly refutable with the decidable-to-acceptable construction ({lit}`concrete_decidable_to_acceptable_and_decoder_universal_incompatible`). It descends from the open {lit}`SemanticEncodedInputDescriptionCompilerPrinciple`, whose source class quantifies over all acceptable languages and is too broad to discharge as stated. |
| Headline theorem | {lit}`concrete_machine_self_halting_main_theorem` | Proved unconditionally in the canonical finite currency: the valid direct-code self-halting language is {lit}`RecognizableCodeLanguage`, is {lit}`UndecidableCodeLanguage`, and its complement is not {lit}`RecognizableCodeLanguage`. The legacy {lit}`self_halting_re_not_recursive_and_complement_not_re_if_decoder_universal` theorem remains only in its clearly documented compatibility block because it uses collapsed predicates and refutable premises. |
| Pair halting | {lit}`ConcreteMachinePairHaltingCodeLanguage`, {lit}`concrete_machine_pair_halting_undecidable_code_language` | Proved unconditionally in the canonical self-delimiting finite-description currency. The checked machine validates one complete description, rewinds it, materializes {lit}`w ++ w`, invokes any supposed stopped pair decider, and sends malformed inputs through a finite missing-transition reject completion. The older tagged {lit}`ConcreteMachinePairHaltingProblem` theorems remain compatibility surfaces conditional on proposition-valued preimage constructions. |
| Finite-description cardinality | {lit}`concrete_valid_description_codes_countable`, {lit}`concrete_finite_description_languages_countable`, {lit}`exists_concrete_language_not_recognizable_by_finite_description` | Proved unconditionally for the exact class of complete well-formed finite descriptions. Their recognized-language image is countable, whereas all languages over the finite nonempty code alphabet are uncountable. The enumeration-fidelity decision is the direct-code endpoint: no duplicate-free unary {lit}`T_n`, finite {lit}`G`, or equivalence bridge is claimed. |

Consequently, the direct-code version of the Section 5.3 central theorem is
closed in the canonical description-backed finite currency, with no decoder
universality, compiler Principle, assumed self-recognizer, or {lit}`sorryAx`.
The finite valid-code checker, self-halting recognizer, and pair-halting
reduction are current consumers of the exact validation surface.  The printed
duplicate-free unary
{lit}`T_n`/{lit}`G` presentation has not been formalized; neither open fidelity
item is claimed by the direct-code headline.

The post-M11 measurement is +27,694 net Compiler lines for M7 against its
pinned +30,000 allowance, leaving 2,306 campaign lines.  M9 measures +852
against its ordinary +10,000 allowance, leaving 9,148 campaign lines.  With both
campaigns retained as pinned outstanding loans, the aggregate circuit is
40,000/120,000 (80,000 headroom).  Raw Compiler size is 510,096 lines against
the pinned 347,066 baseline, or +163,030/+185,000 (21,970 headroom).  The
campaigns remain pinned until their permanent-growth disposition is reviewed;
these numbers do not reset either base.
-/

namespace FoC
namespace Book
namespace Chapter05
namespace Section03

end Section03
end Chapter05
end Book
end FoC
