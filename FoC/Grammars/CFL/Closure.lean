import FoC.Grammars.CFL
import FoC.Grammars.CFGToPDA
import FoC.Grammars.PDAToCFG
import FoC.Grammars.PDA.Intersection
import FoC.Languages.Regular

set_option doc.verso true

namespace FoC
namespace Grammars

open Languages

/-!
# Context-Free Closure with Regular Languages

Finite-presentation PDA recognition is closed under intersection with and
subtraction by DFA-recognizable languages. Combining the PDA/DFA product with
the CFG/PDA conversions yields the corresponding context-free-language
closure results, including subtraction by finite languages.
-/

theorem pda_intersect_dfa_context_free
    {input stack pstate dstate : Type}
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P)
    [DecidablePred D.accept] :
    CFL.ContextFreeLanguage
      (Language.Inter (PDA.AcceptedLanguage P) (DFA.Language D)) := by
  let productPresentation :=
    pdaIntersectDFA_finitePresentation_auto P D presentation
  have hProduct :
      CFL.ContextFreeLanguage
        (PDA.AcceptedLanguage (PDAIntersectDFA P D)) := by
    exists PDA.ToCFGNonterminal stack
      (PDA.PopNormalizedState
        (M := PDAIntersectDFA P D) productPresentation)
    exists PDA.ToCFGNormalized (PDAIntersectDFA P D) productPresentation
    constructor
    · exact CFG.hasFinitePresentation_of_hasFiniteProductions
        (PDA.toCFGNormalized_hasFiniteProductions
          (PDAIntersectDFA P D) productPresentation)
    · exact PDA.toCFGNormalized_language_exact_original
        (PDAIntersectDFA P D) productPresentation
  rcases hProduct with ⟨nonterminal, G, hfinite, hEq⟩
  exists nonterminal
  exists G
  constructor
  · exact hfinite
  · exact FoC.Foundation.FSet.equal_trans hEq
      (fun w => pda_intersect_dfa_accepted_language_exact P D w)

theorem pda_diff_dfa_context_free
    {input stack pstate dstate : Type}
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P)
    [DecidablePred D.accept] :
    CFL.ContextFreeLanguage
      (Language.Diff (PDA.AcceptedLanguage P) (DFA.Language D)) := by
  let _ : DecidablePred (DFA.Complement D).accept := fun q => by
    unfold DFA.Complement
    infer_instance
  have hProduct :=
    pda_intersect_dfa_context_free P (DFA.Complement D) presentation
  rcases hProduct with ⟨nonterminal, G, hfinite, hEq⟩
  exists nonterminal
  exists G
  constructor
  · exact hfinite
  · intro w
    constructor
    · intro hw
      have hInter := (hEq w).mp hw
      constructor
      · exact hInter.left
      · intro hD
        exact (DFA.complement_accepts D w).mp hInter.right hD
    · intro hw
      apply (hEq w).mpr
      constructor
      · exact hw.left
      · exact (DFA.complement_accepts D w).mpr hw.right

/-!
The following language-level wrappers remove the concrete product machine from
the statement. They say: if {lit}`L` is recognized by a finite-presentation PDA
and {lit}`R` is recognized by a DFA, then {lit}`L ∩ R` and {lit}`L \\ R` are
context-free.
-/

theorem finite_presentation_pda_language_inter_dfa_context_free
    {input stack pstate dstate : Type}
    {L R : Language input}
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P)
    [DecidablePred D.accept]
    (hP : Language.Equal (PDA.AcceptedLanguage P) L)
    (hD : Language.Equal (DFA.Language D) R) :
    CFL.ContextFreeLanguage (Language.Inter L R) := by
  have hBase := pda_intersect_dfa_context_free P D presentation
  rcases hBase with ⟨nonterminal, G, hfinite, hEq⟩
  exists nonterminal
  exists G
  constructor
  · exact hfinite
  · intro w
    constructor
    · intro hw
      have hprod := (hEq w).mp hw
      exact And.intro ((hP w).mp hprod.left) ((hD w).mp hprod.right)
    · intro hw
      apply (hEq w).mpr
      exact And.intro ((hP w).mpr hw.left) ((hD w).mpr hw.right)

theorem finite_presentation_pda_language_diff_dfa_context_free
    {input stack pstate dstate : Type}
    {L R : Language input}
    (P : PDA input stack pstate) (D : DFA input dstate)
    (presentation : PDA.FinitePresentation P)
    [DecidablePred D.accept]
    (hP : Language.Equal (PDA.AcceptedLanguage P) L)
    (hD : Language.Equal (DFA.Language D) R) :
    CFL.ContextFreeLanguage (Language.Diff L R) := by
  have hBase := pda_diff_dfa_context_free P D presentation
  rcases hBase with ⟨nonterminal, G, hfinite, hEq⟩
  exists nonterminal
  exists G
  constructor
  · exact hfinite
  · intro w
    constructor
    · intro hw
      have hdiff := (hEq w).mp hw
      constructor
      · exact (hP w).mp hdiff.left
      · intro hR
        exact hdiff.right ((hD w).mpr hR)
    · intro hw
      apply (hEq w).mpr
      constructor
      · exact (hP w).mpr hw.left
      · intro hDfa
        exact hw.right ((hD w).mp hDfa)

/-!
## Recognizability Wrappers

The final group states the automaton-side closure theorems:
finite-presentation PDA-recognizable languages are closed under intersection
with, and subtraction by, regular languages. Since
{name}`Grammars.PDA.Recognizable` requires a finite presentation and is
definitionally {name}`Grammars.PDA.FinitePresentationRecognizable`, the
closure statements come in two spellings with identical content; the
{lit}`pda_recognizable` spellings simply delegate to the
{lit}`finite_presentation` versions.

These wrappers translate the concrete product construction into the language
classes used in the book. They are also used later to subtract finite
languages from context-free languages.
-/

theorem finite_presentation_pda_recognizable_inter_dfa
    {L R : Language input}
    (hL : PDA.FinitePresentationRecognizable L)
    {dstate : Type} (D : DFA input dstate)
    [DecidablePred D.accept]
    (hR : Language.Equal (DFA.Language D) R) :
    PDA.FinitePresentationRecognizable (Language.Inter L R) := by
  rcases hL with ⟨stack, pstate, P, presentation, hP⟩
  exists stack
  exists pstate × dstate
  exists PDAIntersectDFA P D
  exists pdaIntersectDFA_finitePresentation_auto P D presentation
  intro w
  constructor
  · intro hw
    have hExact :=
      (pda_intersect_dfa_accepted_language_exact P D w).mp hw
    exact And.intro ((hP w).mp hExact.left) ((hR w).mp hExact.right)
  · intro hw
    exact (pda_intersect_dfa_accepted_language_exact P D w).mpr
      (And.intro ((hP w).mpr hw.left) ((hR w).mpr hw.right))

theorem finite_presentation_pda_recognizable_inter_dfa_recognizable
    {L R : Language input}
    (hL : PDA.FinitePresentationRecognizable L)
    (hR : DFA.Recognizable R) :
    PDA.FinitePresentationRecognizable (Language.Inter L R) := by
  classical
  rcases hR with ⟨dstate, D, hD⟩
  exact finite_presentation_pda_recognizable_inter_dfa hL D hD

theorem pda_recognizable_inter_dfa_recognizable
    {L R : Language input}
    (hL : PDA.Recognizable L) (hR : DFA.Recognizable R) :
    PDA.Recognizable (Language.Inter L R) :=
  finite_presentation_pda_recognizable_inter_dfa_recognizable hL hR

theorem finite_presentation_pda_recognizable_diff_dfa
    {L R : Language input}
    (hL : PDA.FinitePresentationRecognizable L)
    {dstate : Type} (D : DFA input dstate)
    [DecidablePred D.accept]
    (hR : Language.Equal (DFA.Language D) R) :
    PDA.FinitePresentationRecognizable (Language.Diff L R) := by
  let _ : DecidablePred (DFA.Complement D).accept := fun q => by
    unfold DFA.Complement
    infer_instance
  have hComplement :
      Language.Equal (DFA.Language (DFA.Complement D)) (Language.Compl R) := by
    intro w
    constructor
    · intro hw hRmem
      exact (DFA.complement_accepts D w).mp hw ((hR w).mpr hRmem)
    · intro hw
      exact (DFA.complement_accepts D w).mpr (by
        intro hAccept
        exact hw ((hR w).mp hAccept))
  have hInter :=
    finite_presentation_pda_recognizable_inter_dfa
      hL (DFA.Complement D) hComplement
  simpa [Language.Diff, Language.Inter, Language.Compl,
    Foundation.FSet.Diff, Foundation.FSet.Inter, Foundation.FSet.Compl]
    using! hInter

theorem finite_presentation_pda_recognizable_diff_dfa_recognizable
    {L R : Language input}
    (hL : PDA.FinitePresentationRecognizable L)
    (hR : DFA.Recognizable R) :
    PDA.FinitePresentationRecognizable (Language.Diff L R) := by
  classical
  rcases hR with ⟨dstate, D, hD⟩
  exact finite_presentation_pda_recognizable_diff_dfa hL D hD

/-!
The next group switches between the two equivalent viewpoints used in the
chapter: a context-free language can be represented by a CFG, and a finite CFG
can be converted into a finite-presentation PDA using the construction from
Section 4.4.
-/

theorem finite_production_context_free_finite_presentation_pda_recognizable
    {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L : Language input}
    (hL : CFL.FiniteProductionContextFreeLanguage L) :
    PDA.FinitePresentationRecognizable L := by
  rcases hL with ⟨nonterminal, G, hG⟩
  exists Symbol input nonterminal
  exists CFG.ToPDAState
  exists CFG.ToPDA G
  exists CFG.toPDA_finitePresentation_of_hasFiniteProductions
    G inputFinite
      (CFG.hasFiniteProductions_of_hasFinitePresentation hG.left)
  exact FoC.Foundation.FSet.equal_trans (CFG.toPDA_acceptedLanguage_exact G) hG.right

theorem finite_production_context_free_pda_recognizable {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L : Language input}
    (hL : CFL.FiniteProductionContextFreeLanguage L) :
    PDA.Recognizable L :=
  finite_production_context_free_finite_presentation_pda_recognizable
    inputFinite hL

theorem context_free_language_finite_presentation_pda_recognizable
    {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L : Language input}
    (hL : CFL.ContextFreeLanguage L) :
    PDA.FinitePresentationRecognizable L :=
  finite_production_context_free_finite_presentation_pda_recognizable
    inputFinite hL

theorem context_free_language_pda_recognizable {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L : Language input}
    (hL : CFL.ContextFreeLanguage L) :
    PDA.Recognizable L :=
  finite_production_context_free_pda_recognizable inputFinite hL

theorem finite_list_dfa_recognizable (ws : List (Word input)) :
    DFA.Recognizable (fun w : Word input => w ∈ ws) :=
  RegularLanguage.regular_is_dfa_recognizable
    (RegExp.finite_language_regular ws)

theorem finite_language_dfa_recognizable {M : Language input}
    (hM : Language.Finite M) :
    DFA.Recognizable M := by
  cases hM with
  | intro ws hws =>
      cases finite_list_dfa_recognizable ws with
      | intro state hstate =>
          cases hstate with
          | intro D hD =>
              exists state
              exists D
              intro w
              constructor
              · intro hw
                exact Foundation.ListEnumerates.right hws ((hD w).mp hw)
              · intro hw
                exact (hD w).mpr (Foundation.ListEnumerates.left hws hw)

theorem finite_language_complement_dfa_recognizable {M : Language input}
    (hM : Language.Finite M) :
    DFA.Recognizable (Language.Compl M) :=
  DFA.recognizable_complement (finite_language_dfa_recognizable hM)

theorem finite_presentation_pda_recognizable_diff_finite_list
    {L : Language input}
    (hL : PDA.FinitePresentationRecognizable L) (ws : List (Word input)) :
    PDA.FinitePresentationRecognizable
      (Language.Diff L (fun w : Word input => w ∈ ws)) :=
  finite_presentation_pda_recognizable_diff_dfa_recognizable hL
    (finite_list_dfa_recognizable ws)

theorem finite_presentation_pda_recognizable_diff_finite_language
    {L M : Language input}
    (hL : PDA.FinitePresentationRecognizable L) (hM : Language.Finite M) :
    PDA.FinitePresentationRecognizable (Language.Diff L M) :=
  finite_presentation_pda_recognizable_diff_dfa_recognizable hL
    (finite_language_dfa_recognizable hM)

theorem pda_recognizable_diff_dfa_recognizable {L R : Language input}
    (hL : PDA.Recognizable L) (hR : DFA.Recognizable R) :
    PDA.Recognizable (Language.Diff L R) :=
  finite_presentation_pda_recognizable_diff_dfa_recognizable hL hR

theorem pda_recognizable_diff_finite_list {L : Language input}
    (hL : PDA.Recognizable L) (ws : List (Word input)) :
    PDA.Recognizable (Language.Diff L (fun w : Word input => w ∈ ws)) :=
  pda_recognizable_diff_dfa_recognizable hL
    (finite_list_dfa_recognizable ws)

theorem pda_recognizable_diff_finite_language {L M : Language input}
    (hL : PDA.Recognizable L) (hM : Language.Finite M) :
    PDA.Recognizable (Language.Diff L M) :=
  pda_recognizable_diff_dfa_recognizable hL
    (finite_language_dfa_recognizable hM)

theorem context_free_diff_finite_language_pda_recognizable
    {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L M : Language input}
    (hL : CFL.ContextFreeLanguage L) (hM : Language.Finite M) :
    PDA.Recognizable (Language.Diff L M) :=
  pda_recognizable_diff_finite_language
    (context_free_language_pda_recognizable inputFinite hL) hM

theorem context_free_diff_finite_language_finite_presentation_pda_recognizable
    {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L M : Language input}
    (hL : CFL.ContextFreeLanguage L) (hM : Language.Finite M) :
    PDA.FinitePresentationRecognizable (Language.Diff L M) :=
  finite_presentation_pda_recognizable_diff_finite_language
    (context_free_language_finite_presentation_pda_recognizable
      inputFinite hL) hM

theorem context_free_inter_dfa_context_free
    {input dstate : Type}
    (inputFinite : Foundation.FiniteType input)
    {L R : Language input}
    (hL : CFL.ContextFreeLanguage L)
    (D : DFA input dstate)
    [DecidablePred D.accept]
    (hR : Language.Equal (DFA.Language D) R) :
    CFL.ContextFreeLanguage (Language.Inter L R) := by
  rcases context_free_language_finite_presentation_pda_recognizable
      inputFinite hL with
    ⟨stack, pstate, P, presentation, hP⟩
  exact finite_presentation_pda_language_inter_dfa_context_free
    P D presentation hP hR

theorem context_free_inter_dfa_recognizable_context_free
    {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L R : Language input}
    (hL : CFL.ContextFreeLanguage L)
    (hR : DFA.Recognizable R) :
    CFL.ContextFreeLanguage (Language.Inter L R) := by
  classical
  rcases hR with ⟨dstate, D, hD⟩
  exact context_free_inter_dfa_context_free inputFinite hL D hD

theorem context_free_diff_dfa_context_free
    {input dstate : Type}
    (inputFinite : Foundation.FiniteType input)
    {L R : Language input}
    (hL : CFL.ContextFreeLanguage L)
    (D : DFA input dstate)
    [DecidablePred D.accept]
    (hR : Language.Equal (DFA.Language D) R) :
    CFL.ContextFreeLanguage (Language.Diff L R) := by
  rcases context_free_language_finite_presentation_pda_recognizable
      inputFinite hL with
    ⟨stack, pstate, P, presentation, hP⟩
  exact finite_presentation_pda_language_diff_dfa_context_free
    P D presentation hP hR

theorem context_free_diff_dfa_recognizable_context_free
    {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L R : Language input}
    (hL : CFL.ContextFreeLanguage L)
    (hR : DFA.Recognizable R) :
    CFL.ContextFreeLanguage (Language.Diff L R) := by
  classical
  rcases hR with ⟨dstate, D, hD⟩
  exact context_free_diff_dfa_context_free inputFinite hL D hD

theorem context_free_inter_regular_context_free
    {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L R : Language input}
    (hL : CFL.ContextFreeLanguage L)
    (hR : RegularLanguage.Regular R) :
    CFL.ContextFreeLanguage (Language.Inter L R) :=
  context_free_inter_dfa_recognizable_context_free inputFinite hL
    (RegularLanguage.regular_is_dfa_recognizable hR)

theorem context_free_diff_regular_context_free
    {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L R : Language input}
    (hL : CFL.ContextFreeLanguage L)
    (hR : RegularLanguage.Regular R) :
    CFL.ContextFreeLanguage (Language.Diff L R) :=
  context_free_diff_dfa_recognizable_context_free inputFinite hL
    (RegularLanguage.regular_is_dfa_recognizable hR)

theorem context_free_diff_finite_list_context_free
    {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L : Language input}
    (hL : CFL.ContextFreeLanguage L)
    (ws : List (Word input)) :
    CFL.ContextFreeLanguage
      (Language.Diff L (fun w : Word input => w ∈ ws)) :=
  context_free_diff_dfa_recognizable_context_free inputFinite hL
    (finite_list_dfa_recognizable ws)

theorem context_free_diff_finite_language_context_free
    {input : Type}
    (inputFinite : Foundation.FiniteType input)
    {L M : Language input}
    (hL : CFL.ContextFreeLanguage L) (hM : Language.Finite M) :
    CFL.ContextFreeLanguage (Language.Diff L M) :=
  context_free_diff_dfa_recognizable_context_free inputFinite hL
    (finite_language_dfa_recognizable hM)

end Grammars
end FoC
