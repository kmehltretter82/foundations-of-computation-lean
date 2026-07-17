import FoC.Computability.Compiler.UniversalAndRanges.Ranges
import FoC.Computability.FiniteProgram

set_option doc.verso true

/-!
# Section 5.2: Compiler Interfaces

This page collects the compiler principles and concrete finite-presentation
predicates used by the Section 5.2 developments. The semantic vocabulary page
remains independent of these representation boundaries.

Names containing {lit}`Semantic` are assumptions over Lean-level programs or
partial functions. Concrete predicates instead require an explicitly supplied,
well-formed finite description and state its language or range contract
directly.

## Interim Coverage Status

The table below records the current theorem currency. In particular, a
conditional construction theorem is not counted as a completed compiler, and
a semantic Lean function is not counted as finite source syntax.

| Topic | Current surface | Status |
|---|---|---|
| Recursive iff RE/co-RE | {lit}`ConcreteFiniteDecidableLanguage`, {lit}`concrete_finite_decidable_iff_complementary_recognizers_of_stopped_compiler` | The finite decider-to-complementary-recognizers direction is unconditional. The reverse direction exposes only the stopped paired-dovetail compiler premise. The semantic {lit}`StoppedTuringDecidable` forward implication is also unconditional. Legacy {lit}`TuringDecidable` equivalences remain compatibility-only. |
| Finite-description deciders | {lit}`ConcreteFiniteDecidableLanguage`, {lit}`StoppedMachineDescriptionDecidesLanguage` | The canonical finite predicate combines the legacy output clauses with halt-transition-freedom. Consequently every halt output is stable and is exactly the Boolean answer selected by membership. The weaker {lit}`MachineDescriptionDecidesLanguage` remains compatibility-only. |
| Listings and ranges | {lit}`ConcreteFinitePartialUnaryRangeLanguage`, {lit}`ConcreteFiniteTotalUnaryRangeLanguage` | The concrete predicates use halt-stable finite descriptions. The total form explicitly requires halting on every unary input. The older {lit}`Listable` and function-range equivalences quantify over arbitrary Lean functions and remain set-theoretic rather than effective computability theorems. Partial ranges cover the empty language; total ranges are necessarily nonempty. |
| Finite range compilers | {lit}`ConcreteFiniteAcceptorToPartialUnaryRangeConstruction`, {lit}`ConcreteFinitePartialUnaryRangeToAcceptorConstruction`, {lit}`ConcreteFinitePartialUnaryRangeTotalizerConstruction` | The partial and nonempty-total headline equivalences are stated with these three exact finite-source premises. Their implementations remain open; no semantic listing/range bridge manufactures the descriptions. |
| Semantic compiler assumptions | {lit}`SemanticDescriptionAcceptorCompilationAssumption`, {lit}`SemanticDescriptionBoolDeciderCompilationAssumption`, {lit}`Computability.SemanticPartialUnaryRangeCompilerAssumption` | These quantify over arbitrary staged programs or partial Lean functions. They are compatibility assumptions, not finite compiler implementations. |
| Semantic grammars | {lit}`GeneralGrammar.produces`, {lit}`SemanticLanguageGrammar` | The production relation is an arbitrary proposition and can directly encode membership. This is a semantic fact, not the effective finite-grammar theorem. |
| Finite grammar language | {lit}`concrete_finite_recognizable_language_iff_finite_general_grammar_generated` | The recognizer-to-grammar direction is unconditional through the finite machine-history construction. The reverse direction exposes exactly the finite presentation compiler below. |
| Finite grammar pairs | {lit}`concrete_finite_decidable_iff_finite_general_grammar_pair_of_constructions` | The finite stopped-decider-to-grammar-pair direction is unconditional. The reverse direction exposes exactly the stopped paired-dovetail compiler and finite grammar-presentation recognizer compiler premises; the older {lit}`TuringDecidable` grammar-pair equivalences remain compatibility surfaces. |
| Finite decider output acceptors | {lit}`BoolOutputAcceptor.stoppedBoolOutputAcceptorConstruction`, {lit}`stoppedBoolOutputAcceptorCompilerConstruction` | Proved. A four-state arbitrary-head Boolean-presence scanner is sequenced after the stopped source. Its closed inversion recognizes exactly the selected normalized Boolean output, without promising an unnecessary exact final tape. |
| Paired-recognizer dovetail compiler | {lit}`StoppedPairedRecognizerDovetailDescriptionCompilerPrinciple` | Open at the halt-stable scalar level and indexed by actual complementary traces. The unrestricted target is refuted by {lit}`unrestricted_stopped_paired_recognizer_dovetail_compiler_impossible`: one public input can expose false at one limit and true at another. The current finite controller constructs one description per Boolean output; the remaining route is a coherence-aware scalar first-success endpoint, not a wrapper around that family. |
| Finite grammar-presentation recognizer | {lit}`FiniteBoolGeneralGrammarPresentation.CompilerConstruction` | Open. The target is sound finite data, but the checked indexed-certificate scaffold only transports a premise. An honest implementation still needs certificate encoding, fair enumeration, parsing, verification, reset/divergence proofs, and lowering; the audited construction is larger than current Compiler headroom. |
| Machine-backed history grammar | {lit}`MachineDescriptionHistoryGrammar.presentation`, {lit}`MachineDescriptionHistoryGrammar.generated_language` | Proved. A well-formed finite description has an explicit finite history grammar generating exactly its halting language. This closes the machine-to-grammar direction. |
| Alternative machine models | deterministic one-tape {lit}`TuringMachine`; restricted structured lowerers | The structured layer is not a general book-facing multi-tape equivalence, and no nondeterministic-machine datatype or determinization theorem is present. Both prose claims remain outside the current formalization. |

Consequently, conditional closeouts do not discharge their compiler premises.
The Section 5.2 development should not be described as faithful and complete
until the honest predicates and the finite open targets above are settled.
-/

namespace FoC
namespace Book
namespace Chapter05
namespace Section02

open Computability
open Languages

universe u

/-!
## Semantic Principles

These names collect the language-level assumptions used by the chapter without
asserting that a particular finite transition table realizes them.
-/

abbrev SemanticDescriptionAcceptorCompilationAssumption : Prop :=
  DescriptionProgramAcceptorCompilationPrinciple

abbrev SemanticDescriptionBoolDeciderCompilationAssumption : Prop :=
  DescriptionProgramBoolDeciderCompilationPrinciple

/-- Semantic language-class principles used by the RE/co-RE development. -/
structure SemanticLanguagePrincipleSurface (alpha : Type u) where
  decidableToAcceptable :
    DecidableToAcceptablePrinciple alpha
  dovetailingDecidable :
    ReCoReToDecidablePrinciple alpha
  recursiveIffReCoRE :
    TuringDecidableIffReCoRePrinciple alpha
  stagedAcceptorCompilation :
    ProgramAcceptorCompilationPrinciple alpha
  stagedBoolDeciderCompilation :
    ProgramBoolDeciderCompilationPrinciple alpha

/-!
## Concrete Finite Presentations

These predicates state that supplied finite programs recognize a language,
recognize its complement, or present it as a partial unary range.
-/

/-- A supplied finite acceptor recognizes the stated language. -/
def ConcreteFiniteAcceptorRecognizesLanguage
    (P : FiniteAcceptorProgram) (L : Language Bool) : Prop :=
  P.description.WellFormed ∧ AcceptanceTrace P.trace L

/-- A language has a supplied well-formed finite acceptor description. -/
def ConcreteFiniteRecognizableLanguage (L : Language Bool) : Prop :=
  exists P : FiniteAcceptorProgram,
    ConcreteFiniteAcceptorRecognizesLanguage P L

/-- A supplied finite Boolean program is a halt-stable decider for the language. -/
abbrev ConcreteFiniteBoolDeciderDecidesLanguage
    (P : FiniteBoolProgram) (L : Language Bool) : Prop :=
  StoppedMachineDescriptionDecidesLanguage P.description L

/-- A language has a supplied halt-stable finite Boolean decider. -/
def ConcreteFiniteDecidableLanguage (L : Language Bool) : Prop :=
  exists P : FiniteBoolProgram,
    ConcreteFiniteBoolDeciderDecidesLanguage P L

/-- Supplied finite acceptors recognize a language and its complement. -/
def ConcreteFiniteComplementaryRecognizers
    (L : Language Bool) : Prop :=
  exists accept reject : FiniteAcceptorProgram,
    accept.description.WellFormed ∧ reject.description.WellFormed ∧
      ComplementaryAcceptanceTraces accept.trace reject.trace L

/-- A finite partial-unary program presents exactly the stated language. -/
def ConcreteFinitePartialUnaryRangePresentsLanguage
    (P : FinitePartialUnaryRangeProgram)
    (L : Language Bool) : Prop :=
  P.description.SubroutineReady ∧
    Language.Equal P.descriptionOutputRange L

/-- A language has a supplied halt-stable finite partial-unary range program. -/
def ConcreteFinitePartialUnaryRangeLanguage
    (L : Language Bool) : Prop :=
  exists P : FinitePartialUnaryRangeProgram,
    ConcreteFinitePartialUnaryRangePresentsLanguage P L

/--
A supplied finite unary program halts on every unary input and its output range
is exactly the stated language.
-/
def ConcreteFiniteTotalUnaryRangePresentsLanguage
    (P : FinitePartialUnaryRangeProgram)
    (L : Language Bool) : Prop :=
  P.description.SubroutineReady ∧
    (forall w : Word Unit,
      P.description.HaltsOnInput
        (FinitePartialUnaryRangeProgram.encodeInput w)) ∧
    Language.Equal P.descriptionOutputRange L

/-- A language is the total unary output range of a supplied finite program. -/
def ConcreteFiniteTotalUnaryRangeLanguage
    (L : Language Bool) : Prop :=
  exists P : FinitePartialUnaryRangeProgram,
    ConcreteFiniteTotalUnaryRangePresentsLanguage P L

end Section02
end Chapter05
end Book
end FoC
