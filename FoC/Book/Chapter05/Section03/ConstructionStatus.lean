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
| Raw code parsing | {lit}`ConcreteMachineDecode`, {lit}`ConcreteMachineDecodePrefix` | Proved, but raw. Complete records are parsed without checking {lit}`MachineDescription.WellFormed`; encode/decode and prefix-append inversions are proved. The valid-code distinction is not yet drawn. |
| Valid-code checking | none | Open construction. No {lit}`DescriptionCodeValid` predicate or executable well-formedness checker exists, and therefore no exact self-code gate. |
| Prefix runner | {lit}`ConcreteUniversalPrefixRunnerConstruction` | Proved unconditionally as a finite construction. It recognizes the description-prefix/input language {lit}`ConcreteMachineCodePrefixAcceptedLanguage`, which is not the self-halting language: its description and input components vary independently. |
| Self-halting recognizer | {lit}`ConcreteMachineSelfHaltingLanguage` | Open construction. No unconditional {lit}`TuringAcceptable` witness exists; the K-shaped theorem consumes recognizability as its {lit}`hself` premise. An exact-code gate plus diagonal materialization is required. |
| Decoder coverage | {lit}`ConcreteMachineDecoderUniversalForAcceptableLanguages` | Conditional and jointly refutable with the decidable-to-acceptable construction ({lit}`concrete_decidable_to_acceptable_and_decoder_universal_incompatible`). It descends from the open {lit}`SemanticEncodedInputDescriptionCompilerPrinciple`, whose source class quantifies over all acceptable languages and is too broad to discharge as stated. |
| Headline theorem | {lit}`self_halting_re_not_recursive_and_complement_not_re_if_decoder_universal` | False currency and open construction. The statement is conditional on the refutable premise pair and on {lit}`hself`, and its negative conjuncts use the collapsed legacy predicate. No honest unconditional headline exists yet. |
| Pair halting | {lit}`ConcreteMachinePairHaltingProblem` | Conditional. Undecidability transport uses proposition-valued preimage constructions; the faithful diagonal-pair machine is proved, but no checked finite composition backs the preimage principle. |

Consequently, the Section 5.3 development should not be described as a closed
formalization of the central theorem. The honest repair proceeds in the
description-backed finite currency: canonical code-language contracts, a
valid-code predicate with an executable checker, complement
nonrecognizability and nondecidability without universality premises, and a
concrete finite self-halting recognizer for the positive conjunct. The
negative conjuncts constitute a publishable intermediate state; the positive
conjunct is a separately gated finite-machine campaign.
-/

namespace FoC
namespace Book
namespace Chapter05
namespace Section03

end Section03
end Chapter05
end Book
end FoC
