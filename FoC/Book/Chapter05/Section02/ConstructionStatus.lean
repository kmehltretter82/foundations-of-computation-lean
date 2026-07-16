import FoC.Computability.Compiler.Core.BoundedTrace
import FoC.Computability.Compiler.Core.ConstructionTargets
import FoC.Computability.Compiler.Core.ControllerCloseout
import FoC.Computability.Compiler.UniversalAndRanges.Ranges
import FoC.Computability.FiniteProgram

set_option doc.verso true

/-!
# Section 5.2 construction status

This page isolates the explicit compiler hypotheses used by the concrete
Section 5.2 developments.  The semantic vocabulary page remains independent of
these implementation boundaries.

Names containing {lit}`Semantic` are assumptions over Lean-level programs or
partial functions.  The grouped records below package genuinely distinct
construction handoffs; their fields use the reusable compiler contracts
directly rather than chapter-local forwarding aliases.
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
## Finite Compiler Handoffs

The following records package the independent description-backed construction
surfaces consumed by dovetailing, bounded simulation, grammar recognition, and
range compilation.
-/

/-- Finite-description handoffs for the paired-recognizer dovetail route. -/
structure PairedRecognizerDovetailSurface where
  finiteSourceCompiler :
    PairedRecognizerDovetailDescriptionCompilerPrinciple
  boundedTableCompiler :
    PairedRecognizerBoundedDovetailTableCompilerConstruction
  layoutOutputRealizer :
    PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction
  totalStageAttemptSubroutine :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction
  controllerCompilerCloseout :
    PairedRecognizerDovetailControllerCompilerCloseout
  finiteControllerCompilerCloseout :
    PairedRecognizerDovetailFiniteControllerCompilerCloseout

/-- Fixed-simulator and layout-runner handoffs used by bounded attempts. -/
structure BoundedLayoutConfigRunnerSurface where
  fixedSimulatorOutput :
    FixedDescriptionBoundedSimulatorCodeOutputRealizerConstruction
  fixedStepConfiguration :
    FixedDescriptionStepCodeConfigurationRealizerConstruction
  boundedLayoutRunner :
    PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction
  totalStageAttempt :
    PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction
  finiteStageLoopController :
    PairedRecognizerDovetailFiniteStageLoopControllerConstruction

/-- Finite trace, grammar, dovetail, and range construction handoffs. -/
structure FiniteGrammarRangeSurface where
  machineTraceSearch :
    MachineBoundedTraceSearchConstruction
  encodedTraceSearch :
    EncodedConfigurationTraceSearchConstruction
  boundedTraceSearch :
    Computability.BoundedTraceSearchConstruction
  finiteDovetailProgram :
    FiniteDovetailProgram.CompilerConstruction
  semanticPartialUnaryRange :
    SemanticPartialUnaryRangeCompilerAssumption
  finitePartialUnaryRangeProgram :
    FinitePartialUnaryRangeProgram.CompilerConstruction
  finitePartialUnaryRangeCloseout :
    FinitePartialUnaryRangeProgram.RangeCloseoutConstruction

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
