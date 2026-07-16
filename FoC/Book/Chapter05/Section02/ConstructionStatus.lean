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

def SemanticDescriptionAcceptorCompilationAssumption : Prop :=
  DescriptionProgramAcceptorCompilationPrinciple

def SemanticDescriptionBoolDeciderCompilationAssumption : Prop :=
  DescriptionProgramBoolDeciderCompilationPrinciple

def SemanticPartialUnaryRangeCompilerAssumption : Prop :=
  Computability.SemanticPartialUnaryRangeCompilerAssumption

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
  P.description.WellFormed ∧
    P.OutputComplete ∧ P.OutputFunctional ∧
      Language.Equal P.descriptionOutputRange L

/-- A language has a supplied complete functional finite range program. -/
def ConcreteFinitePartialUnaryRangeLanguage
    (L : Language Bool) : Prop :=
  exists P : FinitePartialUnaryRangeProgram,
    ConcreteFinitePartialUnaryRangePresentsLanguage P L

end Section02
end Chapter05
end Book
end FoC
