import FoC.Grammars.CFG

namespace FoC
namespace Grammars

/-!
General grammars with unrestricted left-hand sides.

Used by:
- Chapter 4, Section 4.6: general grammars and unrestricted derivations.
- Chapter 5: recursively enumerable languages are later related to general
  grammars.
-/

open Languages

namespace SententialForm

def containsNonterminal : SententialForm terminal nonterminal -> Prop
  | [] => False
  | Symbol.terminal _ :: rest => containsNonterminal rest
  | Symbol.nonterminal _ :: _ => True

theorem containsNonterminal_singleton (A : nonterminal) :
    containsNonterminal ([Symbol.nonterminal A] : SententialForm terminal nonterminal) :=
  trivial

end SententialForm

structure GeneralGrammar (terminal : Type u) (nonterminal : Type v) where
  start : nonterminal
  produces : SententialForm terminal nonterminal ->
    SententialForm terminal nonterminal -> Prop
  lhsContainsNonterminal :
    forall lhs rhs, produces lhs rhs -> SententialForm.containsNonterminal lhs
  nonterminalsFinite : Foundation.FiniteType nonterminal

namespace GeneralGrammar

structure Production (terminal : Type u) (nonterminal : Type v) where
  lhs : SententialForm terminal nonterminal
  rhs : SententialForm terminal nonterminal

def HasFiniteProductions (G : GeneralGrammar terminal nonterminal) : Prop :=
  exists rules : List (Production terminal nonterminal),
    forall lhs rhs,
      G.produces lhs rhs <->
        exists rule, rule ∈ rules ∧ rule.lhs = lhs ∧ rule.rhs = rhs

def Yields (G : GeneralGrammar terminal nonterminal)
    (x y : SententialForm terminal nonterminal) : Prop :=
  exists u, exists v, exists lhs, exists rhs,
    G.produces lhs rhs ∧ x = u ++ lhs ++ v ∧ y = u ++ rhs ++ v

inductive Derives (G : GeneralGrammar terminal nonterminal) :
    SententialForm terminal nonterminal -> SententialForm terminal nonterminal -> Prop where
  | refl (x : SententialForm terminal nonterminal) : Derives G x x
  | step {x y z : SententialForm terminal nonterminal} :
      Yields G x y -> Derives G y z -> Derives G x z

def GeneratedLanguage (G : GeneralGrammar terminal nonterminal) : Language terminal :=
  fun w => Derives G [Symbol.nonterminal G.start] (SententialForm.terminalWord w)

def Generated (L : Language terminal) : Prop :=
  exists nonterminal : Type, exists G : GeneralGrammar terminal nonterminal,
    Language.Equal (GeneratedLanguage G) L

def FiniteProductionGenerated (L : Language terminal) : Prop :=
  exists nonterminal : Type, exists G : GeneralGrammar terminal nonterminal,
    HasFiniteProductions G ∧ Language.Equal (GeneratedLanguage G) L

theorem yields_derives {G : GeneralGrammar terminal nonterminal}
    {x y : SententialForm terminal nonterminal} (h : Yields G x y) :
    Derives G x y :=
  Derives.step h (Derives.refl y)

theorem derives_trans {G : GeneralGrammar terminal nonterminal}
    {x y z : SententialForm terminal nonterminal}
    (hxy : Derives G x y) (hyz : Derives G y z) : Derives G x z := by
  induction hxy with
  | refl _ => exact hyz
  | step hstep _ ih => exact Derives.step hstep (ih hyz)

def FromCFG (G : CFG terminal nonterminal) : GeneralGrammar terminal nonterminal where
  start := G.start
  produces := fun lhs rhs => exists A, lhs = [Symbol.nonterminal A] ∧ G.produces A rhs
  lhsContainsNonterminal := by
    intro lhs rhs h
    cases h with
    | intro A hA =>
        cases hA with
        | intro hlhs _ =>
            rw [hlhs]
            exact SententialForm.containsNonterminal_singleton A
  nonterminalsFinite := G.nonterminalsFinite

theorem fromCFG_hasFiniteProductions {G : CFG terminal nonterminal}
    (hG : CFG.HasFiniteProductions G) :
    HasFiniteProductions (FromCFG G) := by
  cases hG with
  | intro rules hrules =>
      exists rules.map
        (fun rule : CFG.Production terminal nonterminal =>
          { lhs := [Symbol.nonterminal rule.lhs], rhs := rule.rhs })
      intro lhs rhs
      constructor
      · intro hprod
        cases hprod with
        | intro A hA =>
            cases hA with
            | intro hlhs hArhs =>
                cases (hrules A rhs).mp hArhs with
                | intro rule hrule =>
                    exists { lhs := [Symbol.nonterminal rule.lhs], rhs := rule.rhs }
                    constructor
                    · apply List.mem_map.mpr
                      exists rule
                      exact ⟨hrule.left, rfl⟩
                    constructor
                    · rw [hlhs, hrule.right.left]
                    · exact hrule.right.right
      · intro hrule
        cases hrule with
        | intro rule' hrule' =>
            have hmem := List.mem_map.mp hrule'.left
            cases hmem with
            | intro rule hrule =>
                rw [← hrule.right] at hrule'
                exists rule.lhs
                constructor
                · exact hrule'.right.left.symm
                · rw [← hrule'.right.right]
                  exact (hrules rule.lhs rule.rhs).mpr
                    ⟨rule, hrule.left, rfl, rfl⟩

theorem cfg_yields_embeds {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : CFG.Yields G x y) : Yields (FromCFG G) x y := by
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro A hA =>
              cases hA with
              | intro rhs hrhs =>
                  cases hrhs with
                  | intro hprod hrest =>
                      cases hrest with
                      | intro hx hy =>
                          exists u
                          exists v
                          exists [Symbol.nonterminal A]
                          exists rhs
                          constructor
                          · exact Exists.intro A (And.intro rfl hprod)
                          constructor
                          · exact hx
                          · exact hy

theorem cfg_derives_embeds {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : CFG.Derives G x y) : Derives (FromCFG G) x y := by
  induction h with
  | refl _ => exact Derives.refl _
  | step hstep _ ih => exact Derives.step (cfg_yields_embeds hstep) ih

theorem cfg_generated_language_embeds (G : CFG terminal nonterminal)
    {w : Word terminal} (h : w ∈ CFG.GeneratedLanguage G) :
    w ∈ GeneratedLanguage (FromCFG G) :=
  cfg_derives_embeds h

end GeneralGrammar

end Grammars
end FoC
