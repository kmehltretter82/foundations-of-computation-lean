import FoC.Grammars.CFG

set_option doc.verso true

/-!
# General grammars

## Unrestricted productions

General grammars allow productions whose left-hand side is an arbitrary
sentential form containing at least one nonterminal.  This is the unrestricted
grammar model needed at the end of Chapter 4 and for the transition to
recursively enumerable languages in Chapter 5.

The core structure is intentionally semantic: its production component is an
arbitrary relation, not a finite list of rules. Finite/effective grammar
content is supplied later by {lit}`GeneralGrammar.HasFiniteProductions` and
the finite-presentation encodings below. This distinction matters because
semantic unrestricted grammars are much broader than finite grammar
presentations.

Used by:
- Chapter 4, Section 4.6: general grammars and unrestricted derivations.
- Chapter 5: recursively enumerable languages are later related to general
  grammars.
-/

namespace FoC
namespace Grammars

open Languages

/-!
## Left-hand side condition

An unrestricted grammar rule may replace a whole sentential form, not just one
nonterminal.  The only side condition is that the left-hand side must contain at
least one nonterminal; otherwise a rule would rewrite a purely terminal word.
-/

namespace SententialForm

def containsNonterminal : SententialForm terminal nonterminal -> Prop
  | [] => False
  | Symbol.terminal _ :: rest => containsNonterminal rest
  | Symbol.nonterminal _ :: _ => True

theorem containsNonterminal_singleton (A : nonterminal) :
    containsNonterminal ([Symbol.nonterminal A] : SententialForm terminal nonterminal) :=
  trivial

end SententialForm

/--
A semantic unrestricted grammar whose production left sides contain a
nonterminal. The later {lit}`HasFinitePresentation` predicate supplies
explicit finite rule data when required.
-/
structure GeneralGrammar (terminal : Type u) (nonterminal : Type v) where
  start : nonterminal
  produces : SententialForm terminal nonterminal ->
    SententialForm terminal nonterminal -> Prop
  lhsContainsNonterminal :
    forall lhs rhs, produces lhs rhs -> SententialForm.containsNonterminal lhs
  nonterminalsFinite : Foundation.FiniteType nonterminal

namespace GeneralGrammar

/-!
## Finite presentations

The textbook later compares grammars with machines, so this file records a
countable coding of finite grammar presentations.  A production is coded by
coding its left and right sentential forms; a finite presentation is coded by
the start symbol together with a finite list of productions.

These definitions are the finite-data layer for results that need a concrete
grammar presentation rather than an arbitrary production predicate.
-/

/-- A concrete unrestricted-grammar production. -/
structure Production (terminal : Type u) (nonterminal : Type v) where
  lhs : SententialForm terminal nonterminal
  rhs : SententialForm terminal nonterminal

namespace Production

def Code (terminalCode : terminal -> Nat) (nonterminalCode : nonterminal -> Nat)
    (rule : Production terminal nonterminal) : Nat :=
  Foundation.Countability.PairCode
    (Foundation.Countability.ListCode
      (Symbol.Code terminalCode nonterminalCode) rule.lhs)
    (Foundation.Countability.ListCode
      (Symbol.Code terminalCode nonterminalCode) rule.rhs)

theorem code_injective {terminalCode : terminal -> Nat}
    {nonterminalCode : nonterminal -> Nat}
    (hterminal : Foundation.Fn.Injective terminalCode)
    (hnonterminal : Foundation.Fn.Injective nonterminalCode) :
    Foundation.Fn.Injective (Code terminalCode nonterminalCode) := by
  intro x y h
  rcases x with ⟨xLhs, xRhs⟩
  rcases y with ⟨yLhs, yRhs⟩
  rcases Foundation.Countability.pairCode_injective_left h with
    ⟨hlhs, hrhs⟩
  have hLhs : xLhs = yLhs :=
    Foundation.Countability.listCode_injective
      (Symbol.code_injective hterminal hnonterminal) hlhs
  have hRhs : xRhs = yRhs :=
    Foundation.Countability.listCode_injective
      (Symbol.code_injective hterminal hnonterminal) hrhs
  cases hLhs
  cases hRhs
  rfl

theorem encodable
    (hterminal : Foundation.Countability.EncodableByNat terminal)
    (hnonterminal : Foundation.Countability.EncodableByNat nonterminal) :
    Foundation.Countability.EncodableByNat
      (Production terminal nonterminal) := by
  rcases hterminal with ⟨terminalCode, hterminalCode⟩
  rcases hnonterminal with ⟨nonterminalCode, hnonterminalCode⟩
  exact ⟨Code terminalCode nonterminalCode,
    code_injective hterminalCode hnonterminalCode⟩

end Production

/-- Raw finite general-grammar data, independent of a semantic grammar. -/
structure FinitePresentationCode (terminal : Type u) (nonterminal : Type v) where
  start : nonterminal
  rules : List (Production terminal nonterminal)

namespace FinitePresentationCode

def Code (terminalCode : terminal -> Nat) (nonterminalCode : nonterminal -> Nat)
    (presentation : FinitePresentationCode terminal nonterminal) : Nat :=
  Foundation.Countability.PairCode
    (nonterminalCode presentation.start)
    (Foundation.Countability.ListCode
      (Production.Code terminalCode nonterminalCode) presentation.rules)

theorem code_injective {terminalCode : terminal -> Nat}
    {nonterminalCode : nonterminal -> Nat}
    (hterminal : Foundation.Fn.Injective terminalCode)
    (hnonterminal : Foundation.Fn.Injective nonterminalCode) :
    Foundation.Fn.Injective (Code terminalCode nonterminalCode) := by
  intro x y h
  rcases x with ⟨xStart, xRules⟩
  rcases y with ⟨yStart, yRules⟩
  rcases Foundation.Countability.pairCode_injective_left h with
    ⟨hstart, hrules⟩
  have hStart : xStart = yStart := hnonterminal hstart
  have hRules : xRules = yRules :=
    Foundation.Countability.listCode_injective
      (Production.code_injective hterminal hnonterminal) hrules
  cases hStart
  cases hRules
  rfl

theorem encodable
    (hterminal : Foundation.Countability.EncodableByNat terminal)
    (hnonterminal : Foundation.Countability.EncodableByNat nonterminal) :
    Foundation.Countability.EncodableByNat
      (FinitePresentationCode terminal nonterminal) := by
  rcases hterminal with ⟨terminalCode, hterminalCode⟩
  rcases hnonterminal with ⟨nonterminalCode, hnonterminalCode⟩
  exact ⟨Code terminalCode nonterminalCode,
    code_injective hterminalCode hnonterminalCode⟩

theorem countable
    (hterminal : Foundation.Countability.EncodableByNat terminal)
    (hnonterminal : Foundation.Countability.EncodableByNat nonterminal) :
    Foundation.FSet.Countable
      (Foundation.FSet.Univ :
        Foundation.FSet (FinitePresentationCode terminal nonterminal)) :=
  Foundation.Countability.countable_univ_of_encodableByNat
    (encodable hterminal hnonterminal)

end FinitePresentationCode

/-- A clearer name for raw, unverified finite general-grammar data. -/
abbrev Description := FinitePresentationCode

namespace Description

theorem countable
    (hterminal : Foundation.Countability.EncodableByNat terminal)
    (hnonterminal : Foundation.Countability.EncodableByNat nonterminal) :
    Foundation.FSet.Countable
      (Foundation.FSet.Univ :
        Foundation.FSet (Description terminal nonterminal)) :=
  FinitePresentationCode.countable hterminal hnonterminal

end Description

def HasFiniteProductions (G : GeneralGrammar terminal nonterminal) : Prop :=
  exists rules : List (Production terminal nonterminal),
    forall lhs rhs,
      G.produces lhs rhs <->
        exists rule, rule ∈ rules ∧ rule.lhs = lhs ∧ rule.rhs = rhs

def ProductionListProduces
    (rules : List (Production terminal nonterminal))
    (lhs rhs : SententialForm terminal nonterminal) : Prop :=
  exists rule, rule ∈ rules ∧ rule.lhs = lhs ∧ rule.rhs = rhs

/-- A finite rule list that presents exactly the production relation of {lean}`G`. -/
structure Presentation (G : GeneralGrammar terminal nonterminal) where
  rules : List (Production terminal nonterminal)
  complete : forall lhs rhs,
    G.produces lhs rhs <-> ProductionListProduces rules lhs rhs

/-- The finite-presentation condition for a semantic general grammar. -/
def HasFinitePresentation (G : GeneralGrammar terminal nonterminal) : Prop :=
  Nonempty (Presentation G)

theorem hasFinitePresentation_iff_hasFiniteProductions
    {G : GeneralGrammar terminal nonterminal} :
    HasFinitePresentation G <-> HasFiniteProductions G := by
  constructor
  · rintro ⟨presentation⟩
    exact ⟨presentation.rules, by
      intro lhs rhs
      simpa [ProductionListProduces] using presentation.complete lhs rhs⟩
  · rintro ⟨rules, complete⟩
    exact ⟨{
      rules := rules
      complete := by
        intro lhs rhs
        simpa [ProductionListProduces] using complete lhs rhs
    }⟩

theorem hasFinitePresentation_of_hasFiniteProductions
    {G : GeneralGrammar terminal nonterminal} (h : HasFiniteProductions G) :
    HasFinitePresentation G :=
  hasFinitePresentation_iff_hasFiniteProductions.mpr h

theorem hasFiniteProductions_of_hasFinitePresentation
    {G : GeneralGrammar terminal nonterminal} (h : HasFinitePresentation G) :
    HasFiniteProductions G :=
  hasFinitePresentation_iff_hasFiniteProductions.mp h

namespace Presentation

/-- An explicit presentation witnesses the proposition that the grammar is
finitely presented. Executable consumers should retain the presentation itself
rather than discard its rule list through this proposition. -/
def hasFinitePresentation {G : GeneralGrammar terminal nonterminal}
    (presentation : Presentation G) : HasFinitePresentation G :=
  ⟨presentation⟩

/-- Compatibility projection from a proof-relevant presentation to the older
existential finite-production predicate. -/
theorem hasFiniteProductions {G : GeneralGrammar terminal nonterminal}
    (presentation : Presentation G) : HasFiniteProductions G :=
  hasFiniteProductions_of_hasFinitePresentation
    presentation.hasFinitePresentation

end Presentation

namespace ProductionList

/-- Build a semantic general grammar directly from a valid finite rule list. -/
def toGeneralGrammar (start : nonterminal) (finite : Foundation.FiniteType nonterminal)
    (rules : List (Production terminal nonterminal))
    (valid : forall rule, rule ∈ rules ->
      SententialForm.containsNonterminal rule.lhs) :
    GeneralGrammar terminal nonterminal where
  start := start
  produces := ProductionListProduces rules
  lhsContainsNonterminal := by
    intro lhs rhs hprod
    rcases hprod with ⟨rule, hrule, hlhs, _⟩
    rw [← hlhs]
    exact valid rule hrule
  nonterminalsFinite := finite

/-- The source rule list exactly presents the grammar built by {name}`toGeneralGrammar`. -/
def presentation (start : nonterminal) (finite : Foundation.FiniteType nonterminal)
    (rules : List (Production terminal nonterminal))
    (valid : forall rule, rule ∈ rules ->
      SententialForm.containsNonterminal rule.lhs) :
    Presentation (toGeneralGrammar start finite rules valid) where
  rules := rules
  complete := by
    intro lhs rhs
    rfl

end ProductionList

theorem hasFiniteProductions_productionListProduces
    {G : GeneralGrammar terminal nonterminal}
    (h : HasFiniteProductions G) :
    exists rules : List (Production terminal nonterminal),
      forall lhs rhs,
        G.produces lhs rhs <->
          ProductionListProduces rules lhs rhs := by
  rcases h with ⟨rules, hrules⟩
  exact
    ⟨rules, by
      intro lhs rhs
      simpa [ProductionListProduces] using hrules lhs rhs⟩

/-!
## Derivations and generated languages

One step of a general derivation rewrites an occurrence of a left-hand side
inside a larger sentential form.  The reflexive-transitive closure of those
steps defines derivability, and the generated language consists of terminal
words derivable from the start nonterminal.
-/

/-- One unrestricted production application inside a sentential context. -/
def Yields (G : GeneralGrammar terminal nonterminal)
    (x y : SententialForm terminal nonterminal) : Prop :=
  exists u, exists v, exists lhs, exists rhs,
    G.produces lhs rhs ∧ x = u ++ lhs ++ v ∧ y = u ++ rhs ++ v

def ProductionListYields
    (rules : List (Production terminal nonterminal))
    (x y : SententialForm terminal nonterminal) : Prop :=
  exists u, exists v, exists rule,
    rule ∈ rules ∧ x = u ++ rule.lhs ++ v ∧ y = u ++ rule.rhs ++ v

/-- The reflexive-transitive closure of unrestricted production steps. -/
inductive Derives (G : GeneralGrammar terminal nonterminal) :
    SententialForm terminal nonterminal -> SententialForm terminal nonterminal -> Prop where
  | refl (x : SententialForm terminal nonterminal) : Derives G x x
  | step {x y z : SententialForm terminal nonterminal} :
      Yields G x y -> Derives G y z -> Derives G x z

inductive DerivesIn (G : GeneralGrammar terminal nonterminal) :
    Nat -> SententialForm terminal nonterminal ->
      SententialForm terminal nonterminal -> Prop where
  | zero (x : SententialForm terminal nonterminal) : DerivesIn G 0 x x
  | step {n : Nat} {x y z : SententialForm terminal nonterminal} :
      Yields G x y -> DerivesIn G n y z -> DerivesIn G (n + 1) x z

inductive ProductionListDerivesIn
    (rules : List (Production terminal nonterminal)) :
    Nat -> SententialForm terminal nonterminal ->
      SententialForm terminal nonterminal -> Prop where
  | zero (x : SententialForm terminal nonterminal) :
      ProductionListDerivesIn rules 0 x x
  | step {n : Nat} {x y z : SententialForm terminal nonterminal} :
      ProductionListYields rules x y ->
      ProductionListDerivesIn rules n y z ->
      ProductionListDerivesIn rules (n + 1) x z

/-- The terminal words derivable from the start symbol. -/
def GeneratedLanguage (G : GeneralGrammar terminal nonterminal) : Language terminal :=
  fun w => Derives G [Symbol.nonterminal G.start] (SententialForm.terminalWord w)

def Generated (L : Language terminal) : Prop :=
  exists nonterminal : Type, exists G : GeneralGrammar terminal nonterminal,
    Language.Equal (GeneratedLanguage G) L

def FiniteProductionGenerated (L : Language terminal) : Prop :=
  exists nonterminal : Type, exists G : GeneralGrammar terminal nonterminal,
    HasFiniteProductions G ∧ Language.Equal (GeneratedLanguage G) L

/-- A language generated by a general grammar with a proof-relevant finite presentation. -/
def FinitePresentationGenerated (L : Language terminal) : Prop :=
  exists nonterminal : Type, exists G : GeneralGrammar terminal nonterminal,
    HasFinitePresentation G ∧ Language.Equal (GeneratedLanguage G) L

theorem finitePresentationGenerated_iff_finiteProductionGenerated
    {L : Language terminal} :
    FinitePresentationGenerated L <-> FiniteProductionGenerated L := by
  constructor
  · rintro ⟨nonterminal, G, hfinite, hG⟩
    exact ⟨nonterminal, G,
      hasFiniteProductions_of_hasFinitePresentation hfinite, hG⟩
  · rintro ⟨nonterminal, G, hfinite, hG⟩
    exact ⟨nonterminal, G,
      hasFinitePresentation_of_hasFiniteProductions hfinite, hG⟩

/-!
## Derivation algebra

The basic proof API mirrors the context-free grammar layer: every single yield
is a derivation, and derivations compose transitively.
-/

private theorem productionListYields_iff_yields_of_produces
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <-> ProductionListProduces rules lhs rhs)
    {x y : SententialForm terminal nonterminal} :
    ProductionListYields rules x y <-> Yields G x y := by
  constructor
  · intro h
    rcases h with ⟨u, v, rule, hrule, hx, hy⟩
    exact
      ⟨u, v, rule.lhs, rule.rhs,
        (hrules rule.lhs rule.rhs).mpr ⟨rule, hrule, rfl, rfl⟩,
        hx, hy⟩
  · intro h
    rcases h with ⟨u, v, lhs, rhs, hprod, hx, hy⟩
    rcases (hrules lhs rhs).mp hprod with ⟨rule, hrule, hlhs, hrhs⟩
    exact ⟨u, v, rule, hrule, by simpa [hlhs] using hx,
      by simpa [hrhs] using hy⟩

theorem productionListDerivesIn_iff_derivesIn_of_produces
    {G : GeneralGrammar terminal nonterminal}
    {rules : List (Production terminal nonterminal)}
    (hrules : forall lhs rhs,
      G.produces lhs rhs <-> ProductionListProduces rules lhs rhs)
    {n : Nat} {x y : SententialForm terminal nonterminal} :
    ProductionListDerivesIn rules n x y <-> DerivesIn G n x y := by
  constructor
  · intro h
    induction h with
    | zero x =>
        exact DerivesIn.zero x
    | step hstep _ ih =>
        exact DerivesIn.step
          ((productionListYields_iff_yields_of_produces hrules).mp hstep)
          ih
  · intro h
    induction h with
    | zero x =>
        exact ProductionListDerivesIn.zero x
    | step hstep _ ih =>
        exact ProductionListDerivesIn.step
          ((productionListYields_iff_yields_of_produces hrules).mpr hstep)
          ih

namespace Presentation

/-- Length-indexed derivations over the stored finite rule list are exactly the
semantic derivations of the presented grammar. -/
theorem productionListDerivesIn_iff_derivesIn
    {G : GeneralGrammar terminal nonterminal}
    (presentation : Presentation G)
    {n : Nat} {x y : SententialForm terminal nonterminal} :
    ProductionListDerivesIn presentation.rules n x y <->
      DerivesIn G n x y :=
  productionListDerivesIn_iff_derivesIn_of_produces presentation.complete

end Presentation

theorem yields_derives {G : GeneralGrammar terminal nonterminal}
    {x y : SententialForm terminal nonterminal} (h : Yields G x y) :
    Derives G x y :=
  Derives.step h (Derives.refl y)

/-- Apply a production in explicitly supplied left and right contexts. -/
theorem yields_of_produces {G : GeneralGrammar terminal nonterminal}
    {lhs rhs : SententialForm terminal nonterminal}
    (hprod : G.produces lhs rhs)
    (pre suf : SententialForm terminal nonterminal) :
    Yields G (pre ++ lhs ++ suf) (pre ++ rhs ++ suf) :=
  ⟨pre, suf, lhs, rhs, hprod, rfl, rfl⟩

theorem yields_context {G : GeneralGrammar terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (pre suf : SententialForm terminal nonterminal)
    (h : Yields G x y) :
    Yields G (pre ++ x ++ suf) (pre ++ y ++ suf) := by
  rcases h with ⟨u, v, lhs, rhs, hprod, hx, hy⟩
  subst x
  subst y
  refine ⟨pre ++ u, v ++ suf, lhs, rhs, hprod, ?_, ?_⟩
  · simp [List.append_assoc]
  · simp [List.append_assoc]

theorem derives_context {G : GeneralGrammar terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (pre suf : SententialForm terminal nonterminal)
    (h : Derives G x y) :
    Derives G (pre ++ x ++ suf) (pre ++ y ++ suf) := by
  induction h with
  | refl _ =>
      exact Derives.refl _
  | step hstep _ ih =>
      exact Derives.step (yields_context pre suf hstep) ih

theorem derivesIn_derives {G : GeneralGrammar terminal nonterminal}
    {n : Nat} {x y : SententialForm terminal nonterminal}
    (h : DerivesIn G n x y) :
    Derives G x y := by
  induction h with
  | zero x =>
      exact Derives.refl x
  | step hstep _ ih =>
      exact Derives.step hstep ih

theorem derives_derivesIn {G : GeneralGrammar terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : Derives G x y) :
    exists n : Nat, DerivesIn G n x y := by
  induction h with
  | refl x =>
      exact Exists.intro 0 (DerivesIn.zero x)
  | step hstep _ ih =>
      cases ih with
      | intro n hn =>
          exact Exists.intro (n + 1) (DerivesIn.step hstep hn)

theorem derives_iff_exists_derivesIn
    {G : GeneralGrammar terminal nonterminal}
    {x y : SententialForm terminal nonterminal} :
    Derives G x y <-> exists n : Nat, DerivesIn G n x y := by
  constructor
  · exact derives_derivesIn
  · intro h
    cases h with
    | intro _ hn =>
        exact derivesIn_derives hn

theorem derives_trans {G : GeneralGrammar terminal nonterminal}
    {x y z : SententialForm terminal nonterminal}
    (hxy : Derives G x y) (hyz : Derives G y z) : Derives G x z := by
  induction hxy with
  | refl _ => exact hyz
  | step hstep _ ih => exact Derives.step hstep (ih hyz)

/-!
## Embedding context-free grammars

Every context-free grammar is a general grammar whose left-hand sides are
single nonterminals.  The embedding preserves finite production lists,
derivations, and generated languages.
-/

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

theorem cfg_yields_of_fromCFG {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : Yields (FromCFG G) x y) : CFG.Yields G x y := by
  rcases h with ⟨u, v, lhs, rhs, hprod, hx, hy⟩
  rcases hprod with ⟨A, hlhs, hprod⟩
  rw [hlhs] at hx
  exact ⟨u, v, A, rhs, hprod, hx, hy⟩

theorem cfg_derives_embeds {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : CFG.Derives G x y) : Derives (FromCFG G) x y := by
  induction h with
  | refl _ => exact Derives.refl _
  | step hstep _ ih => exact Derives.step (cfg_yields_embeds hstep) ih

theorem cfg_derives_of_fromCFG {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : Derives (FromCFG G) x y) : CFG.Derives G x y := by
  induction h with
  | refl _ => exact CFG.Derives.refl _
  | step hstep _ ih =>
      exact CFG.Derives.step (cfg_yields_of_fromCFG hstep) ih

theorem cfg_generated_language_embeds (G : CFG terminal nonterminal)
    {w : Word terminal} (h : w ∈ CFG.GeneratedLanguage G) :
    w ∈ GeneratedLanguage (FromCFG G) :=
  cfg_derives_embeds h

/-- Embedding a CFG as a general grammar preserves its generated language exactly. -/
theorem cfg_generated_language_eq (G : CFG terminal nonterminal) :
    Language.Equal
      (GeneratedLanguage (FromCFG G))
      (CFG.GeneratedLanguage G) := by
  intro w
  constructor
  · exact cfg_derives_of_fromCFG
  · exact cfg_derives_embeds

end GeneralGrammar

end Grammars
end FoC
