import FoC.Computability.Grammar.MachineHistory.Completeness

set_option doc.verso true

/-!
# Construction

Supporting declarations and helper lemmas for Computability Grammar MachineHistory Construction.
-/


namespace FoC
namespace Computability

open Languages
open Grammars

def MachineDescriptionToFiniteGeneralGrammarPresentationConstruction : Prop :=
  forall D : MachineDescription,
    D.WellFormed ->
    exists nonterminal : Type, exists G : GeneralGrammar Bool nonterminal,
      exists _presentation : GeneralGrammar.Presentation G,
        Language.Equal
          (GeneralGrammar.GeneratedLanguage G)
          (fun w : Word Bool => D.HaltsOnInput w)

/-- A well-formed finite machine description has a machine-history grammar
with an explicit finite presentation. -/
theorem machineDescriptionToFiniteGeneralGrammarPresentationConstruction :
    MachineDescriptionToFiniteGeneralGrammarPresentationConstruction := by
  intro D hD
  exact ⟨MachineDescriptionHistoryGrammar.NT D,
    MachineDescriptionHistoryGrammar.grammar D,
    MachineDescriptionHistoryGrammar.presentation D,
    MachineDescriptionHistoryGrammar.generated_language hD⟩

def MachineDescriptionToFiniteGeneralGrammarConstruction : Prop :=
  forall D : MachineDescription,
    D.WellFormed ->
    exists nonterminal : Type, exists G : GeneralGrammar Bool nonterminal,
      GeneralGrammar.HasFiniteProductions G ∧
        Language.Equal
          (GeneralGrammar.GeneratedLanguage G)
          (fun w : Word Bool => D.HaltsOnInput w)

 /-- {name}`machineDescriptionToFiniteGeneralGrammarConstruction` captures the core lemma for this local construction. -/
theorem machineDescriptionToFiniteGeneralGrammarConstruction :
    MachineDescriptionToFiniteGeneralGrammarConstruction := by
  intro D hD
  exact ⟨MachineDescriptionHistoryGrammar.NT D,
    MachineDescriptionHistoryGrammar.grammar D,
    (MachineDescriptionHistoryGrammar.presentation D).hasFiniteProductions,
    MachineDescriptionHistoryGrammar.generated_language hD⟩

def MachineDescriptionAcceptsToFiniteGeneralGrammarPresentationConstruction :
    Prop :=
  forall {D : MachineDescription}, forall {L : Language Bool},
    MachineDescriptionAcceptsLanguage D L ->
      GeneralGrammar.FinitePresentationGenerated L

def MachineDescriptionAcceptsToFiniteGeneralGrammarConstruction : Prop :=
  forall {D : MachineDescription}, forall {L : Language Bool},
    MachineDescriptionAcceptsLanguage D L ->
      GeneralGrammar.FiniteProductionGenerated L

def DescriptionRecognizerToFiniteGeneralGrammarConstruction : Prop :=
  MachineDescriptionAcceptsToFiniteGeneralGrammarConstruction

def DescriptionRecognizerToFiniteGeneralGrammarPresentationConstruction :
    Prop :=
  MachineDescriptionAcceptsToFiniteGeneralGrammarPresentationConstruction

def BooleanRecognizerToFiniteGeneralGrammarConstruction : Prop :=
  DescriptionRecognizerToFiniteGeneralGrammarConstruction

def ProgramAcceptableByDescriptionToFiniteGeneralGrammarConstruction : Prop :=
  forall L : Language Bool,
    ProgramAcceptableByDescription L ->
      GeneralGrammar.FiniteProductionGenerated L

def ProgramAcceptableByDescriptionToFiniteGeneralGrammarPresentationConstruction :
    Prop :=
  forall L : Language Bool,
    ProgramAcceptableByDescription L ->
      GeneralGrammar.FinitePresentationGenerated L

theorem programAcceptableByDescriptionToFiniteGeneralGrammarPresentationConstruction_of_descriptionRecognizer
    (hconstruct :
      DescriptionRecognizerToFiniteGeneralGrammarPresentationConstruction) :
    ProgramAcceptableByDescriptionToFiniteGeneralGrammarPresentationConstruction := by
  intro L hL
  rcases hL with ⟨P, D, hP, hD⟩
  exact hconstruct
    (programCompiledByDescription_acceptsLanguage hP hD)

 /-- {name}`programAcceptableByDescriptionToFiniteGeneralGrammarConstruction_of_descriptionRecognizer` captures the core lemma for this local construction. -/
theorem programAcceptableByDescriptionToFiniteGeneralGrammarConstruction_of_descriptionRecognizer
    (hconstruct : DescriptionRecognizerToFiniteGeneralGrammarConstruction) :
    ProgramAcceptableByDescriptionToFiniteGeneralGrammarConstruction := by
  intro L hL
  rcases hL with ⟨P, D, hP, hD⟩
  exact hconstruct
    (programCompiledByDescription_acceptsLanguage hP hD)

 /-- {name}`machineDescriptionAcceptsToFiniteGeneralGrammarConstruction_of_machineConstruction` captures the core lemma for this local construction. -/
theorem machineDescriptionAcceptsToFiniteGeneralGrammarConstruction_of_machineConstruction
    (hconstruct : MachineDescriptionToFiniteGeneralGrammarConstruction) :
    MachineDescriptionAcceptsToFiniteGeneralGrammarConstruction := by
  intro D L hD
  rcases hconstruct D hD.left with ⟨nonterminal, G, hG⟩
  exists nonterminal
  exists G
  exact ⟨hG.left, FoC.Foundation.FSet.equal_trans hG.right hD.right⟩

theorem machineDescriptionAcceptsToFiniteGeneralGrammarPresentationConstruction_of_machineConstruction
    (hconstruct :
      MachineDescriptionToFiniteGeneralGrammarPresentationConstruction) :
    MachineDescriptionAcceptsToFiniteGeneralGrammarPresentationConstruction := by
  intro D L hD
  rcases hconstruct D hD.left with
    ⟨nonterminal, G, presentation, hG⟩
  exact ⟨nonterminal, G, presentation.hasFinitePresentation,
    FoC.Foundation.FSet.equal_trans hG hD.right⟩

end Computability
end FoC
