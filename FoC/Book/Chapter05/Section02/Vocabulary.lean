import FoC.Computability.Compiler
import FoC.Computability.FiniteProgram
import FoC.Computability.Grammar

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter05
namespace Section02

/-!
# Chapter 5, Section 5.2: Computability

This section connects recursive, recursively enumerable, acceptable, and
listable languages. It also records the statement shape for the theorem that
finite general grammars generate exactly the recursively enumerable languages.
The reusable modules are {module}`FoC.Computability.Enumerable`,
{module}`FoC.Computability.Program`, {module}`FoC.Computability.Compiler`,
{module}`FoC.Computability.FiniteProgram`,
{module}`FoC.Computability.Grammar`, and
{module}`FoC.Grammars.GeneralGrammar`.

The guiding distinction is total decision versus semi-decision. Recursive
languages have deciders. Recursively enumerable languages have recognizers or
listings: members eventually appear, but nonmembers may never be ruled out.

The formal page separates three levels of argument.

* At the semantic level, traces, listings, ranges, partial functions, and staged
  programs are related directly.
* At the bounded-trace level, finite machine runs, encoded configurations,
  finite derivation searches, and recognizer-to-grammar trace simulations are
  checked without requiring a generic transition-table compiler.
* At the compiler-principle level, staged programs and bounded trace checkers
  are connected to Turing machines by named construction hypotheses.
* At the finite-description level, concrete supplied descriptions and finite
  program records expose the construction interfaces used for executable
  machine descriptions.

The finite compiler boundaries are now first-order where possible. Boolean
finite grammar presentations use explicit {lit}`Fin n` nonterminals and a
production list, with the remaining recognizer compiler factored through a
bounded checked-indexed-certificate recognizer. Paired-recognizer dovetailing
is split into a halt-free bounded layout runner and a subroutine-ready
runner-search driver that performs the unbounded stage search.

This makes the theorem statements honest about implementation work. When a
textbook proof says to dovetail two recognizers or check a finite derivation,
this page proves the bounded trace core and names the finite compiler
interfaces instead of treating them as implicit.
-/

open Languages
open Computability
open Grammars

universe u v

/-!
## Recursive and Recursively Enumerable Languages

The definitions name the main language classes and the construction principles
used by the book's proofs: decidable-to-acceptable conversion and dovetailing
paired recognizers for a language and its complement.

The construction principles are kept as explicit hypotheses where the reusable
library avoids assuming a concrete universal machine. This lets the page state
the textbook theorem shapes without smuggling in unproved implementation
details.

The many definitions at the start of the file are mostly vocabulary adapters:
they give book-facing names to reusable predicates, staged-program compiler
principles, finite program descriptions, and concrete machine-description
relations. The theorem groups later in the page explain how those names fit
together.  The compiler vocabulary is split explicitly: names containing
{lit}`Semantic` are assumptions over arbitrary Lean-level programs, traces, or
partial functions; names containing {lit}`FiniteSource` are the finite-data
construction targets that can become concrete transition-table compilers.
-/

def RecursivelyEnumerableLanguage (L : Language alpha) : Prop :=
  RecursivelyEnumerable L

def CoRecursivelyEnumerableLanguage (L : Language alpha) : Prop :=
  CoRecursivelyEnumerable L

def RecursivelyEnumerableLanguageWithComplement (L : Language alpha) : Prop :=
  RecursivelyEnumerableWithComplement L

def RecursiveLanguage (L : Language alpha) : Prop :=
  Recursive L

def StoppedTuringDecidableLanguage (L : Language alpha) : Prop :=
  StoppedTuringDecidable L

def DecidableToAcceptableConstruction (alpha : Type u) : Prop :=
  DecidableToAcceptablePrinciple alpha

def DovetailingDecidableConstruction (alpha : Type u) : Prop :=
  ReCoReToDecidablePrinciple alpha

def RecursiveIffReCoREConstruction (alpha : Type u) : Prop :=
  RecursiveIffReCoRePrinciple alpha

def StagedAcceptorCompilationConstruction (alpha : Type u) : Prop :=
  ProgramAcceptorCompilationPrinciple alpha

def StagedBoolDeciderCompilationConstruction (alpha : Type u) : Prop :=
  ProgramBoolDeciderCompilationPrinciple alpha

def SemanticDescriptionAcceptorCompilationAssumption : Prop :=
  SemanticDescriptionAcceptorCompilerAssumption

def SemanticDescriptionBoolDeciderCompilationAssumption : Prop :=
  SemanticDescriptionBoolDeciderCompilerAssumption

def SemanticDovetailDescriptionCompilerAssumption : Prop :=
  Computability.SemanticDovetailDescriptionCompilerAssumption

def ConcreteDescriptionAcceptorCompilationConstruction : Prop :=
  SemanticDescriptionAcceptorCompilationAssumption

def ConcreteDescriptionBoolDeciderCompilationConstruction : Prop :=
  SemanticDescriptionBoolDeciderCompilationAssumption

def ConcreteDovetailDescriptionCompilerConstruction : Prop :=
  SemanticDovetailDescriptionCompilerAssumption

def ConcreteFiniteSourcePairedRecognizerDovetailCompilerConstruction : Prop :=
  FiniteSourcePairedRecognizerDovetailCompilerConstruction

def ConcretePairedRecognizerDovetailCompilerConstruction : Prop :=
  ConcreteFiniteSourcePairedRecognizerDovetailCompilerConstruction

def ConcreteTapeCodeExactCompilerConstruction : Prop :=
  MachineDescriptionTapeCodeExactCompilerConstruction

def ConcreteTapeCodeOutputCompilerConstruction : Prop :=
  MachineDescriptionTapeCodeOutputCompilerConstruction

def ConcreteBoolOutputDescription (b : Bool) : MachineDescription :=
  MachineDescription.BoolOutputDescription b

def ConcretePairedRecognizerBoundedDovetailTableCompilerConstruction : Prop :=
  FiniteSourcePairedRecognizerBoundedDovetailTableCompilerConstruction

def ConcretePairedRecognizerDovetailSearchDriverCompilerConstruction : Prop :=
  PairedRecognizerDovetailSearchDriverCompilerConstruction

def ConcretePairedRecognizerDovetailSubroutineSearchDriverCompilerConstruction :
    Prop :=
  PairedRecognizerDovetailSubroutineSearchDriverCompilerConstruction

def ConcretePairedRecognizerDovetailRunnerSearchDriverCompilerConstruction :
    Prop :=
  PairedRecognizerDovetailRunnerSearchDriverCompilerConstruction

def ConcretePairedRecognizerDovetailSubroutineRunnerSearchDriverCompilerConstruction :
    Prop :=
  PairedRecognizerDovetailSubroutineRunnerSearchDriverCompilerConstruction

def ConcretePairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction :
    Prop :=
  PairedRecognizerDovetailStageAttemptSearchDriverCompilerConstruction

def ConcretePairedRecognizerDovetailTotalStageAttemptSearchDriverCompilerConstruction :
    Prop :=
  PairedRecognizerDovetailTotalStageAttemptSearchDriverCompilerConstruction

def ConcretePairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction :
    Prop :=
  PairedRecognizerDovetailTotalStageAttemptControllerSearchDriverCompilerConstruction

abbrev ConcretePairedRecognizerDovetailControllerCompilerCloseout :=
  PairedRecognizerDovetailControllerCompilerCloseout

def ConcretePairedRecognizerDovetailTotalStageAttemptControllerResultRealizes
    (accept reject : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  PairedRecognizerDovetailTotalStageAttemptControllerResultRealizes
    accept reject P

def ConcretePairedRecognizerDovetailControllerRawOutputCode :
    MachineDescription.TapeCodePrimitive :=
  PairedRecognizerDovetailControllerRawOutputCode

def ConcretePairedRecognizerDovetailControllerRawOutputCodeRealizes
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  PairedRecognizerDovetailControllerRawOutputCodeRealizes P

def ConcretePairedRecognizerDovetailControllerContinueCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  PairedRecognizerDovetailControllerContinueCode accept reject

def ConcretePairedRecognizerDovetailControllerEmitCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  PairedRecognizerDovetailControllerEmitCode accept reject

def ConcretePairedRecognizerDovetailControllerContinueCodeRealizes
    (accept reject : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  PairedRecognizerDovetailControllerContinueCodeRealizes
    accept reject P

def ConcretePairedRecognizerDovetailControllerEmitCodeRealizes
    (accept reject : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  PairedRecognizerDovetailControllerEmitCodeRealizes
    accept reject P

def ConcretePairedRecognizerDovetailTotalThenRawOutputCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  PairedRecognizerDovetailTotalThenRawOutputCode accept reject

def ConcretePairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction :
    Prop :=
  PairedRecognizerDovetailTotalStageAttemptCodeOutputCompiledSubroutineConstruction

def ConcreteFixedDescriptionBoundedSimulatorCodeCompilerConstruction : Prop :=
  FixedDescriptionBoundedSimulatorCodeCompilerConstruction

def ConcreteFixedDescriptionBoundedSimulatorCodeOutputRealizerConstruction :
    Prop :=
  FixedDescriptionBoundedSimulatorCodeOutputRealizerConstruction

def ConcreteFixedDescriptionStepCodeCompilerConstruction : Prop :=
  FixedDescriptionStepCodeCompilerConstruction

def ConcreteFixedDescriptionStepCodeOutputRealizerConstruction : Prop :=
  FixedDescriptionStepCodeOutputRealizerConstruction

def ConcreteFixedDescriptionStepCodeConfigurationRealizerConstruction :
    Prop :=
  FixedDescriptionStepCodeConfigurationRealizerConstruction

def ConcreteMachineBoundedTraceSearchConstruction : Prop :=
  MachineBoundedTraceSearchConstruction

def ConcreteEncodedConfigurationTraceSearchConstruction : Prop :=
  EncodedConfigurationTraceSearchConstruction

def BoundedTraceSearchConstruction : Prop :=
  Computability.BoundedTraceSearchConstruction

def ConcretePairedRecognizerDovetailLayoutCodeCompilerConstruction : Prop :=
  PairedRecognizerDovetailLayoutCodeCompilerConstruction

def ConcretePairedRecognizerDovetailInitialLayoutCodeOutputRealizerConstruction :
    Prop :=
  PairedRecognizerDovetailInitialLayoutCodeOutputRealizerConstruction

def ConcretePairedRecognizerDovetailLayoutCodeOutputRealizerConstruction :
    Prop :=
  PairedRecognizerDovetailLayoutCodeOutputRealizerConstruction

def ConcretePairedRecognizerDovetailOutputCodeOutputRealizerConstruction :
    Prop :=
  PairedRecognizerDovetailOutputCodeOutputRealizerConstruction

def ConcretePairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction :
    Prop :=
  PairedRecognizerDovetailStageAttemptCodeOutputRealizerConstruction

def ConcretePairedRecognizerDovetailTotalStageAttemptCodeOutputRealizerConstruction :
    Prop :=
  PairedRecognizerDovetailTotalStageAttemptCodeOutputRealizerConstruction

def ConcretePairedRecognizerDovetailTotalThenRawOutputCodeOutputRealizerConstruction :
    Prop :=
  PairedRecognizerDovetailTotalThenRawOutputCodeOutputRealizerConstruction

def ConcretePairedRecognizerDovetailControllerContinueCodeOutputRealizerConstruction :
    Prop :=
  PairedRecognizerDovetailControllerContinueCodeOutputRealizerConstruction

def ConcretePairedRecognizerDovetailControllerEmitCodeOutputRealizerConstruction :
    Prop :=
  PairedRecognizerDovetailControllerEmitCodeOutputRealizerConstruction

def ConcretePairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction :
    Prop :=
  PairedRecognizerDovetailTotalStageAttemptCodeOutputSubroutineRealizerConstruction

def ConcretePairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction :
    Prop :=
  PairedRecognizerDovetailLayoutCodeOutputSubroutineRealizerConstruction

def ConcreteFiniteDovetailCompilerConstruction : Prop :=
  FiniteDovetailProgram.CompilerConstruction

def SemanticPartialUnaryRangeCompilerAssumption : Prop :=
  Computability.SemanticPartialUnaryRangeCompilerAssumption

def ConcretePartialUnaryRangeDescriptionCompilerConstruction : Prop :=
  SemanticPartialUnaryRangeCompilerAssumption

def ConcreteFinitePartialUnaryRangeProgramCompilerConstruction : Prop :=
  FinitePartialUnaryRangeProgram.CompilerConstruction

def ConcreteFinitePartialUnaryRangeProgramCloseoutConstruction : Prop :=
  FinitePartialUnaryRangeProgram.RangeCloseoutConstruction

def PartialFunctionDomainLanguage
    (f : Word input -> Option (Word output)) : Language input :=
  PartialFunctionDomain f

def LanguageAcceptanceTrace
    (trace : Word alpha -> Nat -> Prop)
    (L : Language alpha) : Prop :=
  AcceptanceTrace trace L

def LanguageComplementaryAcceptanceTraces
    (accept reject : Word alpha -> Nat -> Prop)
    (L : Language alpha) : Prop :=
  ComplementaryAcceptanceTraces accept reject L

def LanguageTraceHitsBy
    (trace : Word alpha -> Nat -> Prop)
    (w : Word alpha) (limit : Nat) : Prop :=
  TraceHitsBy trace w limit

def LanguageDovetailSearchHit
    (accept reject : Word alpha -> Nat -> Prop)
    (w : Word alpha) (limit : Nat) : Prop :=
  ComplementaryTraceSearchHit accept reject w limit

noncomputable def TraceDovetailProgram
    (accept reject : Word alpha -> Nat -> Prop) :
    StagedProgram alpha Bool :=
  Computability.DovetailProgram accept reject

def ProgramBoolDecidesLanguage
    (P : StagedProgram alpha Bool) (L : Language alpha) : Prop :=
  ProgramBoolDecides P L

def ProgramBoolDecidableLanguage (L : Language alpha) : Prop :=
  ProgramBoolDecidable L

def ProgramAcceptableLanguage (L : Language alpha) : Prop :=
  ProgramAcceptable L

/-!
The next group changes representation level. The preceding staged-program
predicates are semantic; the description predicates say that a supplied finite
machine description realizes the same staged computation. Later theorems use
these bridges to state exactly which compiler facts are supplied by closeout
records.
-/

def ConcreteMachineDescriptionAccepts
    (D : MachineDescription) (L : Language Bool) : Prop :=
  MachineDescriptionAcceptsLanguage D L

def ConcreteMachineDescriptionDecides
    (D : MachineDescription) (L : Language Bool) : Prop :=
  MachineDescriptionDecidesLanguage D L

def ConcreteProgramCompiledByDescription
    (P : StagedProgram Bool Unit) (D : MachineDescription) : Prop :=
  ProgramCompiledByDescription P D

def ConcreteBoolProgramCompiledByDescription
    (P : StagedProgram Bool Bool) (D : MachineDescription) : Prop :=
  BoolProgramCompiledByDescription P D

def ConcreteProgramAcceptableByDescription
    (L : Language Bool) : Prop :=
  ProgramAcceptableByDescription L

def ConcreteProgramBoolDecidableByDescription
    (L : Language Bool) : Prop :=
  ProgramBoolDecidableByDescription L

theorem concrete_machine_description_acceptance_trace
    {D : MachineDescription} {L : Language Bool}
    (h : ConcreteMachineDescriptionAccepts D L) :
    LanguageAcceptanceTrace (fun w n => D.HaltsIn n w) L := by
  intro w
  exact h.right w

/-!
Finite program wrappers give concrete handles for the examples and compiler
interfaces used below. They expose traces, compiled descriptions, staged
programs, and output-range conditions while keeping the reusable implementation
in the computability library.
-/

def ConcreteFiniteAcceptorProgram : Type :=
  FiniteAcceptorProgram

def ConcreteFiniteBoolProgram : Type :=
  FiniteBoolProgram

def ConcreteFiniteDovetailProgram : Type :=
  FiniteDovetailProgram

def ConcreteFinitePartialUnaryRangeProgram : Type :=
  FinitePartialUnaryRangeProgram

def ConcreteFiniteAcceptorTrace
    (P : ConcreteFiniteAcceptorProgram)
    (w : Word Bool) (n : Nat) : Prop :=
  P.trace w n

def ConcreteFiniteAcceptorDescription
    (P : ConcreteFiniteAcceptorProgram) : MachineDescription :=
  P.compile

def ConcreteFiniteBoolDescription
    (P : ConcreteFiniteBoolProgram) : MachineDescription :=
  P.compile

def ConcreteFiniteDovetailDescription
    (P : ConcreteFiniteDovetailProgram) : MachineDescription :=
  P.decider.compile

def ConcreteFiniteAcceptorStagedProgram
    (P : ConcreteFiniteAcceptorProgram) :
    StagedProgram Bool Unit :=
  P.toStagedProgram

noncomputable def ConcreteFiniteBoolStagedProgram
    (P : ConcreteFiniteBoolProgram) :
    StagedProgram Bool Bool :=
  P.toStagedProgram

noncomputable def ConcreteFiniteDovetailStagedProgram
    (P : ConcreteFiniteDovetailProgram) :
    StagedProgram Bool Bool :=
  P.toStagedProgram

def ConcreteFiniteDovetailCompiled
    (P : ConcreteFiniteDovetailProgram) : Prop :=
  P.Compiled

def ConcreteFinitePartialUnaryOutputComplete
    (P : ConcreteFinitePartialUnaryRangeProgram) : Prop :=
  P.OutputComplete

def ConcreteFinitePartialUnaryOutputFunctional
    (P : ConcreteFinitePartialUnaryRangeProgram) : Prop :=
  P.OutputFunctional

noncomputable def ConcreteFinitePartialUnaryOutputFunction
    (P : ConcreteFinitePartialUnaryRangeProgram) :
    Word Unit -> Option (Word Bool) :=
  P.outputFunction

noncomputable def ConcreteFinitePartialUnaryOutputListing
    (P : ConcreteFinitePartialUnaryRangeProgram) :
    Nat -> Option (Word Bool) :=
  P.outputListing

def ConcreteFinitePartialUnaryRangeStagedProgram
    (P : ConcreteFinitePartialUnaryRangeProgram) :
    StagedProgram Unit Bool :=
  P.toStagedProgram

def ConcreteFinitePartialUnaryOutputRange
    (P : ConcreteFinitePartialUnaryRangeProgram) :
    Language Bool :=
  P.outputRange

def ConcreteFinitePartialUnaryDescriptionOutputRange
    (P : ConcreteFinitePartialUnaryRangeProgram) :
    Language Bool :=
  P.descriptionOutputRange

def ConcreteFiniteAcceptorRecognizesLanguage
    (P : ConcreteFiniteAcceptorProgram) (L : Language Bool) : Prop :=
  P.description.WellFormed ∧
    LanguageAcceptanceTrace (ConcreteFiniteAcceptorTrace P) L

def ConcreteFiniteRecognizableLanguage (L : Language Bool) : Prop :=
  exists P : ConcreteFiniteAcceptorProgram,
    ConcreteFiniteAcceptorRecognizesLanguage P L

def ConcreteFiniteComplementaryRecognizers
    (L : Language Bool) : Prop :=
  exists accept reject : ConcreteFiniteAcceptorProgram,
    accept.description.WellFormed ∧ reject.description.WellFormed ∧
      LanguageComplementaryAcceptanceTraces
        (ConcreteFiniteAcceptorTrace accept)
        (ConcreteFiniteAcceptorTrace reject) L

def ConcreteFinitePartialUnaryRangePresentsLanguage
    (P : ConcreteFinitePartialUnaryRangeProgram)
    (L : Language Bool) : Prop :=
  P.description.WellFormed ∧
    ConcreteFinitePartialUnaryOutputComplete P ∧
      ConcreteFinitePartialUnaryOutputFunctional P ∧
        Language.Equal
          (ConcreteFinitePartialUnaryDescriptionOutputRange P) L

def ConcreteFinitePartialUnaryRangeLanguage
    (L : Language Bool) : Prop :=
  exists P : ConcreteFinitePartialUnaryRangeProgram,
    ConcreteFinitePartialUnaryRangePresentsLanguage P L


end Section02
end Chapter05
end Book
end FoC
