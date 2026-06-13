import FoC.Computability.Grammar.MachineHistory

set_option doc.verso true

/-!
# Section 5.2 grammar closeouts
-/

namespace FoC
namespace Computability

open Languages
open Grammars

/-!
# Chapter 5 grammar construction boundaries

The textbook equivalence between unrestricted grammars and recursively
enumerable languages contains two construction-heavy directions. The recognizer
direction is proved at the staged-program layer above. The definitions below
name the concrete compiler interfaces for Boolean machine descriptions.
The semantic reverse direction is no longer a construction boundary: with
arbitrary production predicates, every language has a one-nonterminal grammar.
The closeout records below now distinguish semantic assumptions over arbitrary
Lean-level recognizers from finite-source construction targets over concrete
description data and first-order finite grammar presentations.
-/

def BooleanGeneralGrammarRecognizerCompilerPrinciple : Prop :=
  forall {nonterminal : Type}, forall G : GeneralGrammar Bool nonterminal,
    exists D : MachineDescription,
      ProgramCompiledByDescription (GeneralGrammarRecognizerProgram G) D

def FiniteBooleanGeneralGrammarRecognizerCompilerPrinciple : Prop :=
  forall {nonterminal : Type}, forall G : GeneralGrammar Bool nonterminal,
    GeneralGrammar.HasFiniteProductions G ->
      exists D : MachineDescription,
        ProgramCompiledByDescription (GeneralGrammarRecognizerProgram G) D

def SemanticBooleanGeneralGrammarRecognizerCompilerAssumption : Prop :=
  BooleanGeneralGrammarRecognizerCompilerPrinciple

def FiniteSourceFiniteGeneralGrammarRecognizerCompilerConstruction : Prop :=
  FiniteBooleanGeneralGrammarRecognizerCompilerPrinciple

def FiniteProductionListGrammarRecognizerCompilerConstruction : Prop :=
  forall {nonterminal : Type},
    forall G : GeneralGrammar Bool nonterminal,
    forall rules : List (GeneralGrammar.Production Bool nonterminal),
      (forall lhs rhs,
        G.produces lhs rhs <->
          GeneralGrammar.ProductionListProduces rules lhs rhs) ->
        exists D : MachineDescription,
          ProgramCompiledByDescription
            (FiniteProductionListRecognizerProgram G rules) D

theorem finiteProductionListGrammarRecognizerCompilerConstruction_of_finitePresentationCompiler
    (hcompile :
      FiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction) :
    FiniteProductionListGrammarRecognizerCompilerConstruction := by
  intro _ G rules hrules
  let P :=
    FiniteBoolGeneralGrammarPresentation.ofGrammarRules G rules hrules
  rcases hcompile P with ⟨D, hD⟩
  exact
    ⟨D,
      programCompiledByDescription_of_same_accepted_language
        (FiniteBoolGeneralGrammarPresentation.recognizerProgram_acceptsLanguage_ofGrammarRules
          G rules hrules)
        (finiteProductionListRecognizerProgram_acceptsLanguage hrules)
        hD⟩

theorem booleanGeneralGrammarRecognizerCompilerPrinciple_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    BooleanGeneralGrammarRecognizerCompilerPrinciple := by
  intro _ G
  exact hcompile (GeneralGrammarRecognizerProgram G)

theorem finiteBooleanGeneralGrammarRecognizerCompilerPrinciple_of_generalCompiler
    (hcompile : BooleanGeneralGrammarRecognizerCompilerPrinciple) :
    FiniteBooleanGeneralGrammarRecognizerCompilerPrinciple := by
  intro _ G _hfinite
  exact hcompile G

theorem finiteProductionListGrammarRecognizerCompilerConstruction_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    FiniteProductionListGrammarRecognizerCompilerConstruction := by
  intro _ G rules _hrules
  exact hcompile (FiniteProductionListRecognizerProgram G rules)

theorem finiteBooleanGeneralGrammarRecognizerCompilerPrinciple_of_productionListCompiler
    (hcompile : FiniteProductionListGrammarRecognizerCompilerConstruction) :
    FiniteBooleanGeneralGrammarRecognizerCompilerPrinciple := by
  intro _ G hfinite
  rcases GeneralGrammar.hasFiniteProductions_productionListProduces
    hfinite with ⟨rules, hrules⟩
  rcases hcompile G rules hrules with ⟨D, hD⟩
  exact
    ⟨D,
      programCompiledByDescription_of_same_accepted_language
        (finiteProductionListRecognizerProgram_acceptsLanguage hrules)
        (generalGrammarRecognizerProgram_acceptsLanguage G)
        hD⟩

theorem finiteBooleanGeneralGrammarRecognizerCompilerPrinciple_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    FiniteBooleanGeneralGrammarRecognizerCompilerPrinciple :=
  finiteBooleanGeneralGrammarRecognizerCompilerPrinciple_of_productionListCompiler
    (finiteProductionListGrammarRecognizerCompilerConstruction_of_descriptionCompiler
      hcompile)

def GeneralGrammarAcceptabilityEquivalence (L : Language terminal) : Prop :=
  GeneralGrammar.Generated L <-> RecursivelyEnumerable L

def GeneralGrammarToRecursivelyEnumerablePrinciple
    (terminal : Type u) : Prop :=
  forall L : Language terminal,
    GeneralGrammar.Generated L -> RecursivelyEnumerable L

def RecursivelyEnumerableToGeneralGrammarPrinciple
    (terminal : Type u) : Prop :=
  forall L : Language terminal,
    RecursivelyEnumerable L -> GeneralGrammar.Generated L

def RecursivelyEnumerableToFiniteGeneralGrammarPrinciple
    (terminal : Type u) : Prop :=
  forall L : Language terminal,
    RecursivelyEnumerable L -> GeneralGrammar.FiniteProductionGenerated L

theorem recursivelyEnumerableToFiniteGeneralGrammarPrinciple_bool_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    RecursivelyEnumerableToFiniteGeneralGrammarPrinciple Bool := by
  intro L hL
  exact
    (programAcceptableByDescriptionToFiniteGeneralGrammarConstruction_of_descriptionRecognizer
      (machineDescriptionAcceptsToFiniteGeneralGrammarConstruction_of_machineConstruction
        machineDescriptionToFiniteGeneralGrammarConstruction))
      L
      (recursivelyEnumerable_programAcceptableByDescription_of_descriptionCompiler
        hcompile hL)

def GeneralGrammarREEquivalencePrinciple
    (terminal : Type u) : Prop :=
  forall L : Language terminal,
    GeneralGrammarAcceptabilityEquivalence L

def FiniteGeneralGrammarAcceptabilityEquivalence
    (L : Language terminal) : Prop :=
  GeneralGrammar.FiniteProductionGenerated L <-> RecursivelyEnumerable L

def FiniteGeneralGrammarREEquivalencePrinciple
    (terminal : Type u) : Prop :=
  forall L : Language terminal,
    FiniteGeneralGrammarAcceptabilityEquivalence L

structure BooleanSection52CompilerCloseout where
  boundedTraceSearch : BoundedTraceSearchConstruction
  decidableToAcceptable : DecidableToAcceptablePrinciple Bool
  dovetailDescription : SemanticDovetailDescriptionCompilerAssumption
  partialUnaryRangeDescription :
    SemanticPartialUnaryRangeCompilerAssumption
  grammarRecognizerDescription :
    SemanticBooleanGeneralGrammarRecognizerCompilerAssumption

structure BooleanFiniteGrammarSection52Closeout where
  boundedTraceSearch : BoundedTraceSearchConstruction
  decidableToAcceptable : DecidableToAcceptablePrinciple Bool
  dovetailDescription : SemanticDovetailDescriptionCompilerAssumption
  finiteGrammarRecognizerDescription :
    FiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction
  recursivelyEnumerableToFiniteGrammar :
    RecursivelyEnumerableToFiniteGeneralGrammarPrinciple Bool

structure BooleanFiniteDataSection52CompilerCloseout where
  boundedTraceSearch : BoundedTraceSearchConstruction
  decidableToAcceptable : DecidableToAcceptablePrinciple Bool
  pairedDovetailDescription :
    FiniteSourcePairedRecognizerDovetailCompilerConstruction
  finiteGrammarRecognizerDescription :
    FiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction
  descriptionRecognizerToFiniteGrammar :
    DescriptionRecognizerToFiniteGeneralGrammarConstruction

theorem booleanFiniteDataSection52CompilerCloseout_programAcceptableByDescriptionToFiniteGrammar
    (hclose : BooleanFiniteDataSection52CompilerCloseout) :
    ProgramAcceptableByDescriptionToFiniteGeneralGrammarConstruction :=
  programAcceptableByDescriptionToFiniteGeneralGrammarConstruction_of_descriptionRecognizer
    hclose.descriptionRecognizerToFiniteGrammar


end Computability
end FoC
