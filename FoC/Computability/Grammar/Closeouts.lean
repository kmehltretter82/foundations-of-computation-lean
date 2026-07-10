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

Canonical finite-grammar interfaces use
{name}`GeneralGrammar.Presentation` when a compiler needs the rules and
{name}`GeneralGrammar.HasFinitePresentation` when only existence matters.
The finite-production principles remain available for compatibility.
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

def FinitePresentationBooleanGeneralGrammarRecognizerCompilerPrinciple : Prop :=
  forall {nonterminal : Type}, forall G : GeneralGrammar Bool nonterminal,
    GeneralGrammar.HasFinitePresentation G ->
      exists D : MachineDescription,
        ProgramCompiledByDescription (GeneralGrammarRecognizerProgram G) D

def SemanticBooleanGeneralGrammarRecognizerCompilerAssumption : Prop :=
  BooleanGeneralGrammarRecognizerCompilerPrinciple

def FiniteSourceFiniteGeneralGrammarRecognizerCompilerConstruction : Prop :=
  FiniteBooleanGeneralGrammarRecognizerCompilerPrinciple

def FiniteProductionListGrammarRecognizerCompilerConstruction : Prop :=
  forall {nonterminal : Type},
    DecidableEq nonterminal ->
    forall G : GeneralGrammar Bool nonterminal,
    forall rules : List (GeneralGrammar.Production Bool nonterminal),
      (forall lhs rhs,
        G.produces lhs rhs <->
          GeneralGrammar.ProductionListProduces rules lhs rhs) ->
        exists D : MachineDescription,
          ProgramCompiledByDescription
            (FiniteProductionListRecognizerProgram G rules) D

/-- Compiler interface for an explicit proof-relevant presentation. Unlike the
compatibility finite-production principle, the executable rule list is retained
as input data. -/
def GeneralGrammarPresentationRecognizerCompilerConstruction : Prop :=
  forall {nonterminal : Type},
    DecidableEq nonterminal ->
    forall {G : GeneralGrammar Bool nonterminal},
    forall presentation : GeneralGrammar.Presentation G,
      exists D : MachineDescription,
        ProgramCompiledByDescription
          (FinitePresentationRecognizerProgram presentation) D

theorem generalGrammarPresentationRecognizerCompilerConstruction_of_finitePresentationCompiler
    (hcompile :
      FiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction) :
    GeneralGrammarPresentationRecognizerCompilerConstruction := by
  intro _ hdec G presentation
  let _ : DecidableEq _ := hdec
  let P := FiniteBoolGeneralGrammarPresentation.ofPresentation presentation
  rcases hcompile P with ⟨D, hD⟩
  exact
    ⟨D,
      programCompiledByDescription_of_same_accepted_language
        (FiniteBoolGeneralGrammarPresentation.recognizerProgram_acceptsLanguage_ofPresentation
          presentation)
        (finitePresentationRecognizerProgram_acceptsLanguage presentation)
        hD⟩

theorem generalGrammarPresentationRecognizerCompilerConstruction_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    GeneralGrammarPresentationRecognizerCompilerConstruction := by
  intro _ _ G presentation
  exact hcompile (FinitePresentationRecognizerProgram presentation)

theorem finiteProductionListGrammarRecognizerCompilerConstruction_of_finitePresentationCompiler
    (hcompile :
      FiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction) :
    FiniteProductionListGrammarRecognizerCompilerConstruction := by
  intro _ hdec G rules hrules
  let _ : DecidableEq _ := hdec
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

theorem finitePresentationBooleanGeneralGrammarRecognizerCompilerPrinciple_of_generalCompiler
    (hcompile : BooleanGeneralGrammarRecognizerCompilerPrinciple) :
    FinitePresentationBooleanGeneralGrammarRecognizerCompilerPrinciple := by
  intro _ G _hfinite
  exact hcompile G

theorem finiteProductionListGrammarRecognizerCompilerConstruction_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    FiniteProductionListGrammarRecognizerCompilerConstruction := by
  intro _ _hdec G rules _hrules
  exact hcompile (FiniteProductionListRecognizerProgram G rules)

theorem finiteBooleanGeneralGrammarRecognizerCompilerPrinciple_of_productionListCompiler
    (hcompile : FiniteProductionListGrammarRecognizerCompilerConstruction) :
    FiniteBooleanGeneralGrammarRecognizerCompilerPrinciple := by
  intro nonterminal G hfinite
  classical
  rcases GeneralGrammar.hasFiniteProductions_productionListProduces
    hfinite with ⟨rules, hrules⟩
  rcases hcompile (inferInstance : DecidableEq nonterminal) G rules hrules with
    ⟨D, hD⟩
  exact
    ⟨D,
      programCompiledByDescription_of_same_accepted_language
        (finiteProductionListRecognizerProgram_acceptsLanguage hrules)
        (generalGrammarRecognizerProgram_acceptsLanguage G)
        hD⟩

theorem finitePresentationBooleanGeneralGrammarRecognizerCompilerPrinciple_of_presentationCompiler
    (hcompile : GeneralGrammarPresentationRecognizerCompilerConstruction) :
    FinitePresentationBooleanGeneralGrammarRecognizerCompilerPrinciple := by
  intro nonterminal G hfinite
  rcases hfinite with ⟨presentation⟩
  classical
  rcases hcompile (inferInstance : DecidableEq nonterminal) presentation with
    ⟨D, hD⟩
  exact
    ⟨D,
      programCompiledByDescription_of_same_accepted_language
        (finitePresentationRecognizerProgram_acceptsLanguage presentation)
        (generalGrammarRecognizerProgram_acceptsLanguage G)
        hD⟩

theorem finiteBooleanGeneralGrammarRecognizerCompilerPrinciple_of_finitePresentationPrinciple
    (hcompile :
      FinitePresentationBooleanGeneralGrammarRecognizerCompilerPrinciple) :
    FiniteBooleanGeneralGrammarRecognizerCompilerPrinciple := by
  intro _ G hfinite
  exact hcompile G
    (GeneralGrammar.hasFinitePresentation_of_hasFiniteProductions hfinite)

theorem finiteBooleanGeneralGrammarRecognizerCompilerPrinciple_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    FiniteBooleanGeneralGrammarRecognizerCompilerPrinciple :=
  finiteBooleanGeneralGrammarRecognizerCompilerPrinciple_of_productionListCompiler
    (finiteProductionListGrammarRecognizerCompilerConstruction_of_descriptionCompiler
      hcompile)

theorem finitePresentationBooleanGeneralGrammarRecognizerCompilerPrinciple_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    FinitePresentationBooleanGeneralGrammarRecognizerCompilerPrinciple :=
  finitePresentationBooleanGeneralGrammarRecognizerCompilerPrinciple_of_presentationCompiler
    (generalGrammarPresentationRecognizerCompilerConstruction_of_descriptionCompiler
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

def RecursivelyEnumerableToFinitePresentationGeneralGrammarPrinciple
    (terminal : Type u) : Prop :=
  forall L : Language terminal,
    RecursivelyEnumerable L -> GeneralGrammar.FinitePresentationGenerated L

theorem recursivelyEnumerableToFinitePresentationGeneralGrammarPrinciple_bool_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    RecursivelyEnumerableToFinitePresentationGeneralGrammarPrinciple Bool := by
  intro L hL
  exact
    (programAcceptableByDescriptionToFiniteGeneralGrammarPresentationConstruction_of_descriptionRecognizer
      (machineDescriptionAcceptsToFiniteGeneralGrammarPresentationConstruction_of_machineConstruction
        machineDescriptionToFiniteGeneralGrammarPresentationConstruction))
      L
      (recursivelyEnumerable_programAcceptableByDescription_of_descriptionCompiler
        hcompile hL)

theorem recursivelyEnumerableToFiniteGeneralGrammarPrinciple_bool_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    RecursivelyEnumerableToFiniteGeneralGrammarPrinciple Bool := by
  intro L hL
  exact GeneralGrammar.finitePresentationGenerated_iff_finiteProductionGenerated.mp
    (recursivelyEnumerableToFinitePresentationGeneralGrammarPrinciple_bool_of_descriptionCompiler
      hcompile L hL)

def GeneralGrammarREEquivalencePrinciple
    (terminal : Type u) : Prop :=
  forall L : Language terminal,
    GeneralGrammarAcceptabilityEquivalence L

def FiniteGeneralGrammarAcceptabilityEquivalence
    (L : Language terminal) : Prop :=
  GeneralGrammar.FiniteProductionGenerated L <-> RecursivelyEnumerable L

def FinitePresentationGeneralGrammarAcceptabilityEquivalence
    (L : Language terminal) : Prop :=
  GeneralGrammar.FinitePresentationGenerated L <-> RecursivelyEnumerable L

def FiniteGeneralGrammarREEquivalencePrinciple
    (terminal : Type u) : Prop :=
  forall L : Language terminal,
    FiniteGeneralGrammarAcceptabilityEquivalence L

def FinitePresentationGeneralGrammarREEquivalencePrinciple
    (terminal : Type u) : Prop :=
  forall L : Language terminal,
    FinitePresentationGeneralGrammarAcceptabilityEquivalence L

/-!
The broad Boolean Section 5.2 closeout is a semantic package. It keeps the
finite trace-search handoff, but its acceptor conversion, dovetail compiler,
partial-unary range compiler, and unrestricted grammar-recognizer compiler are
semantic principles over Lean-level objects. It should not be read as a finite
machine-description closeout.
-/

structure BooleanSection52CompilerCloseout where
  boundedTraceSearch : BoundedTraceSearchConstruction
  decidableToAcceptable : DecidableToAcceptablePrinciple Bool
  dovetailDescription : DovetailDescriptionCompilerPrinciple
  partialUnaryRangeDescription :
    SemanticPartialUnaryRangeCompilerAssumption
  grammarRecognizerDescription :
    SemanticBooleanGeneralGrammarRecognizerCompilerAssumption

/-!
The finite-grammar closeout moves the grammar-recognizer side to finite
presentations, but it still carries semantic acceptor and dovetailing
principles. Use it for finite grammar equivalence statements, not as evidence
that every compiler dependency has already been reduced to first-order finite
machine data.
-/

structure BooleanFiniteGrammarSection52Closeout where
  boundedTraceSearch : BoundedTraceSearchConstruction
  decidableToAcceptable : DecidableToAcceptablePrinciple Bool
  dovetailDescription : DovetailDescriptionCompilerPrinciple
  finiteGrammarRecognizerDescription :
    FiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction
  recursivelyEnumerableToFiniteGrammar :
    RecursivelyEnumerableToFiniteGeneralGrammarPrinciple Bool

theorem BooleanFiniteGrammarSection52Closeout.recursivelyEnumerableToFinitePresentationGrammar
    (hclose : BooleanFiniteGrammarSection52Closeout) :
    RecursivelyEnumerableToFinitePresentationGeneralGrammarPrinciple Bool := by
  intro L hL
  exact GeneralGrammar.finitePresentationGenerated_iff_finiteProductionGenerated.mpr
    (hclose.recursivelyEnumerableToFiniteGrammar L hL)

/-!
The finite-data closeout is the narrowest Section 5.2 package currently used by
the book-facing finite/effective route. Its paired-dovetail and grammar
recognizer fields are finite-source or finite-presentation construction
targets, and the recognizer-to-finite-grammar field is description-backed. It
still includes the semantic decidable-to-acceptable principle because the
recursive-language theorem consuming this package needs that bridge explicitly.
-/

structure BooleanFiniteDataSection52CompilerCloseout where
  boundedTraceSearch : BoundedTraceSearchConstruction
  decidableToAcceptable : DecidableToAcceptablePrinciple Bool
  pairedDovetailDescription :
    PairedRecognizerDovetailDescriptionCompilerPrinciple
  finiteGrammarRecognizerDescription :
    FiniteBoolGeneralGrammarPresentationRecognizerCompilerConstruction
  descriptionRecognizerToFiniteGrammar :
    DescriptionRecognizerToFiniteGeneralGrammarConstruction

theorem booleanFiniteDataSection52CompilerCloseout_programAcceptableByDescriptionToFiniteGrammar
    (hclose : BooleanFiniteDataSection52CompilerCloseout) :
    ProgramAcceptableByDescriptionToFiniteGeneralGrammarConstruction :=
  programAcceptableByDescriptionToFiniteGeneralGrammarConstruction_of_descriptionRecognizer
    hclose.descriptionRecognizerToFiniteGrammar

theorem booleanFiniteDataSection52CompilerCloseout_programAcceptableByDescriptionToFinitePresentationGrammar
    (hclose : BooleanFiniteDataSection52CompilerCloseout) :
    ProgramAcceptableByDescriptionToFiniteGeneralGrammarPresentationConstruction := by
  intro L hL
  exact GeneralGrammar.finitePresentationGenerated_iff_finiteProductionGenerated.mpr
    (booleanFiniteDataSection52CompilerCloseout_programAcceptableByDescriptionToFiniteGrammar
      hclose L hL)


end Computability
end FoC
