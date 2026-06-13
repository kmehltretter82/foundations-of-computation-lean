import FoC.Grammars.CFG.Mapping

set_option doc.verso true

namespace FoC
namespace Grammars

open Foundation
open Languages

namespace CFG

/-!
The union grammar has one fresh start symbol that chooses the left or right
grammar, then all subsequent derivations remain inside that chosen side. The
finite-production proof compiles this tagged presentation into an explicit
finite rule list.
-/

inductive UnionProduces (G : CFG terminal left) (H : CFG terminal right) :
    SumStart left right -> SententialForm terminal (SumStart left right) -> Prop where
  | chooseLeft :
      UnionProduces G H SumStart.start [Symbol.nonterminal (SumStart.inLeft G.start)]
  | chooseRight :
      UnionProduces G H SumStart.start [Symbol.nonterminal (SumStart.inRight H.start)]
  | leftRule {A rhs} :
      G.produces A rhs -> UnionProduces G H (SumStart.inLeft A) (inLeftForm rhs)
  | rightRule {A rhs} :
      H.produces A rhs -> UnionProduces G H (SumStart.inRight A) (inRightForm rhs)

def UnionGrammar (G : CFG terminal left) (H : CFG terminal right) :
    CFG terminal (SumStart left right) where
  start := SumStart.start
  produces := UnionProduces G H
  nonterminalsFinite := SumStart.finite G.nonterminalsFinite H.nonterminalsFinite

def unionChooseLeftProduction (G : CFG terminal left) :
    Production terminal (SumStart left right) where
  lhs := SumStart.start
  rhs := [Symbol.nonterminal (SumStart.inLeft G.start)]

def unionChooseRightProduction (H : CFG terminal right) :
    Production terminal (SumStart left right) where
  lhs := SumStart.start
  rhs := [Symbol.nonterminal (SumStart.inRight H.start)]

def unionLeftProduction (rule : Production terminal left) :
    Production terminal (SumStart left right) where
  lhs := SumStart.inLeft rule.lhs
  rhs := inLeftForm rule.rhs

def unionRightProduction (rule : Production terminal right) :
    Production terminal (SumStart left right) where
  lhs := SumStart.inRight rule.lhs
  rhs := inRightForm rule.rhs

theorem union_hasFiniteProductions
    {G : CFG terminal left} {H : CFG terminal right}
    (hG : HasFiniteProductions G) (hH : HasFiniteProductions H) :
    HasFiniteProductions (UnionGrammar G H) := by
  cases hG with
  | intro rulesG hrulesG =>
      cases hH with
      | intro rulesH hrulesH =>
          exists [unionChooseLeftProduction (right := right) G,
            unionChooseRightProduction (left := left) H] ++
            rulesG.map (unionLeftProduction (right := right)) ++
            rulesH.map (unionRightProduction (left := left))
          intro A rhs
          constructor
          · intro h
            cases h with
            | chooseLeft =>
                exists unionChooseLeftProduction (right := right) G
                simp [unionChooseLeftProduction]
            | chooseRight =>
                exists unionChooseRightProduction (left := left) H
                simp [unionChooseRightProduction]
            | leftRule hprod =>
                cases (hrulesG _ _).mp hprod with
                | intro rule hrule =>
                    exists unionLeftProduction (right := right) rule
                    constructor
                    · apply List.mem_append_left
                      apply List.mem_append_right
                      exact List.mem_map.mpr
                        (Exists.intro rule (And.intro hrule.left rfl))
                    · constructor
                      · simp [unionLeftProduction, hrule.right.left]
                      · simp [unionLeftProduction, hrule.right.right]
            | rightRule hprod =>
                cases (hrulesH _ _).mp hprod with
                | intro rule hrule =>
                    exists unionRightProduction (left := left) rule
                    constructor
                    · apply List.mem_append_right
                      exact List.mem_map.mpr
                        (Exists.intro rule (And.intro hrule.left rfl))
                    · constructor
                      · simp [unionRightProduction, hrule.right.left]
                      · simp [unionRightProduction, hrule.right.right]
          · intro h
            cases h with
            | intro rule hrule =>
                have hmem := hrule.left
                simp [unionChooseLeftProduction, unionChooseRightProduction,
                  unionLeftProduction, unionRightProduction] at hmem
                cases hmem with
                | inl hleft =>
                    rw [← hrule.right.left, ← hrule.right.right, hleft]
                    exact UnionProduces.chooseLeft
                | inr hrest =>
                    cases hrest with
                    | inl hright =>
                        rw [← hrule.right.left, ← hrule.right.right, hright]
                        exact UnionProduces.chooseRight
                    | inr hrest' =>
                        cases hrest' with
                        | inl hleftRule =>
                            cases hleftRule with
                            | intro base hbase =>
                                cases hbase with
                                | intro hbaseMem hbaseEq =>
                                    rw [← hrule.right.left, ← hrule.right.right, ← hbaseEq]
                                    exact UnionProduces.leftRule
                                      ((hrulesG base.lhs base.rhs).mpr
                                        (Exists.intro base
                                          (And.intro hbaseMem
                                            (And.intro rfl rfl))))
                        | inr hrightRule =>
                            cases hrightRule with
                            | intro base hbase =>
                                cases hbase with
                                | intro hbaseMem hbaseEq =>
                                    rw [← hrule.right.left, ← hrule.right.right, ← hbaseEq]
                                    exact UnionProduces.rightRule
                                      ((hrulesH base.lhs base.rhs).mpr
                                        (Exists.intro base
                                          (And.intro hbaseMem
                                            (And.intro rfl rfl))))

def UnionSymbolLanguage (G : CFG terminal left) (H : CFG terminal right) :
    Symbol terminal (SumStart left right) -> Language terminal
  | Symbol.terminal a => Language.Singleton (Word.Symbol a)
  | Symbol.nonterminal SumStart.start =>
      Language.Union (GeneratedLanguage G) (GeneratedLanguage H)
  | Symbol.nonterminal (SumStart.inLeft A) => GeneratedFrom G A
  | Symbol.nonterminal (SumStart.inRight A) => GeneratedFrom H A

/-!
Union soundness reads a derivation in the tagged grammar back into the language
chosen by the start rule. The inverse direction uses mapped derivations from the
left or right grammar to build a derivation in the union grammar.
-/

theorem inLeftForm_formLanguage_to_derivation
    (G : CFG terminal left) (H : CFG terminal right)
    {sf : SententialForm terminal left} {w : Word terminal}
    (h : w ∈ FormLanguage (UnionSymbolLanguage G H) (inLeftForm sf)) :
    w ∈ FormLanguage (DerivationSymbolLanguage G) sf := by
  induction sf generalizing w with
  | nil =>
      exact h
  | cons s rest ih =>
      cases s with
      | terminal a =>
          cases h with
          | intro first hfirst =>
              cases hfirst with
              | intro tail htail =>
                  exists first
                  exists tail
                  exact And.intro htail.left
                    (And.intro (ih htail.right.left) htail.right.right)
      | nonterminal A =>
          cases h with
          | intro first hfirst =>
              cases hfirst with
              | intro tail htail =>
                  exists first
                  exists tail
                  exact And.intro htail.left
                    (And.intro (ih htail.right.left) htail.right.right)

theorem inRightForm_formLanguage_to_derivation
    (G : CFG terminal left) (H : CFG terminal right)
    {sf : SententialForm terminal right} {w : Word terminal}
    (h : w ∈ FormLanguage (UnionSymbolLanguage G H) (inRightForm sf)) :
    w ∈ FormLanguage (DerivationSymbolLanguage H) sf := by
  induction sf generalizing w with
  | nil =>
      exact h
  | cons s rest ih =>
      cases s with
      | terminal a =>
          cases h with
          | intro first hfirst =>
              cases hfirst with
              | intro tail htail =>
                  exists first
                  exists tail
                  exact And.intro htail.left
                    (And.intro (ih htail.right.left) htail.right.right)
      | nonterminal A =>
          cases h with
          | intro first hfirst =>
              cases hfirst with
              | intro tail htail =>
                  exists first
                  exists tail
                  exact And.intro htail.left
                    (And.intro (ih htail.right.left) htail.right.right)

theorem union_production_sound (G : CFG terminal left) (H : CFG terminal right)
    {A : SumStart left right} {rhs : SententialForm terminal (SumStart left right)}
    (hprod : UnionProduces G H A rhs) :
    forall w, w ∈ FormLanguage (UnionSymbolLanguage G H) rhs ->
      w ∈ UnionSymbolLanguage G H (Symbol.nonterminal A) := by
  intro w hw
  cases hprod with
  | chooseLeft =>
      cases hw with
      | intro first hfirst =>
          cases hfirst with
          | intro tail htail =>
              cases htail.right.left
              rw [htail.right.right, Word.concat_empty_right]
              exact Or.inl htail.left
  | chooseRight =>
      cases hw with
      | intro first hfirst =>
          cases hfirst with
          | intro tail htail =>
              cases htail.right.left
              rw [htail.right.right, Word.concat_empty_right]
              exact Or.inr htail.left
  | leftRule hG =>
      rename_i A rhs
      have hbody := inLeftForm_formLanguage_to_derivation G H hw
      have hstep : Yields G [Symbol.nonterminal A] rhs := by
        exists []
        exists []
        exists A
        exists rhs
        constructor
        · exact hG
        constructor
        · rfl
        · simp
      exact Derives.step hstep (formLanguage_derives hbody)
  | rightRule hH =>
      rename_i A rhs
      have hbody := inRightForm_formLanguage_to_derivation G H hw
      have hstep : Yields H [Symbol.nonterminal A] rhs := by
        exists []
        exists []
        exists A
        exists rhs
        constructor
        · exact hH
        constructor
        · rfl
        · simp
      exact Derives.step hstep (formLanguage_derives hbody)

theorem union_yields_sound (G : CFG terminal left) (H : CFG terminal right)
    {x y : SententialForm terminal (SumStart left right)} {w : Word terminal}
    (h : Yields (UnionGrammar G H) x y)
    (hw : w ∈ FormLanguage (UnionSymbolLanguage G H) y) :
    w ∈ FormLanguage (UnionSymbolLanguage G H) x := by
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
                          rw [hy] at hw
                          rw [hx]
                          exact formLanguage_replace_sound
                            (UnionSymbolLanguage G H)
                            (union_production_sound G H hprod)
                            hw

theorem union_derives_sound (G : CFG terminal left) (H : CFG terminal right)
    {x y : SententialForm terminal (SumStart left right)} {w : Word terminal}
    (h : Derives (UnionGrammar G H) x y)
    (hw : w ∈ FormLanguage (UnionSymbolLanguage G H) y) :
    w ∈ FormLanguage (UnionSymbolLanguage G H) x := by
  induction h with
  | refl _ =>
      exact hw
  | step hstep _ ih =>
      exact union_yields_sound G H hstep (ih hw)

/-!
The union grammar has two constructive directions, one for each summand. These
theorems inject an existing derivation from the left or right grammar into the
tagged grammar under the fresh start symbol.
-/

theorem union_generates_left (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal} (hw : w ∈ GeneratedLanguage G) :
    w ∈ GeneratedLanguage (UnionGrammar G H) := by
  have hStart : Yields (UnionGrammar G H)
      [Symbol.nonterminal SumStart.start]
      [Symbol.nonterminal (SumStart.inLeft G.start)] := by
    exists []
    exists []
    exists SumStart.start
    exists [Symbol.nonterminal (SumStart.inLeft G.start)]
    constructor
    · exact UnionProduces.chooseLeft
    constructor <;> rfl
  have hMap : Derives (UnionGrammar G H)
      [Symbol.nonterminal (SumStart.inLeft G.start)]
      (SententialForm.terminalWord w) := by
    have hMapped := mapDerivesNonterminal SumStart.inLeft G (UnionGrammar G H)
      (by
        intro A rhs hprod
        exact UnionProduces.leftRule hprod)
      hw
    change Derives (UnionGrammar G H)
      [Symbol.nonterminal (SumStart.inLeft G.start)]
      (SententialForm.mapNonterminal SumStart.inLeft (SententialForm.terminalWord w)) at hMapped
    rw [SententialForm.mapNonterminal_terminalWord] at hMapped
    exact hMapped
  exact Derives.step hStart hMap

theorem union_generates_right (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal} (hw : w ∈ GeneratedLanguage H) :
    w ∈ GeneratedLanguage (UnionGrammar G H) := by
  have hStart : Yields (UnionGrammar G H)
      [Symbol.nonterminal SumStart.start]
      [Symbol.nonterminal (SumStart.inRight H.start)] := by
    exists []
    exists []
    exists SumStart.start
    exists [Symbol.nonterminal (SumStart.inRight H.start)]
    constructor
    · exact UnionProduces.chooseRight
    constructor <;> rfl
  have hMap : Derives (UnionGrammar G H)
      [Symbol.nonterminal (SumStart.inRight H.start)]
      (SententialForm.terminalWord w) := by
    have hMapped := mapDerivesNonterminal SumStart.inRight H (UnionGrammar G H)
      (by
        intro A rhs hprod
        exact UnionProduces.rightRule hprod)
      hw
    change Derives (UnionGrammar G H)
      [Symbol.nonterminal (SumStart.inRight H.start)]
      (SententialForm.mapNonterminal SumStart.inRight (SententialForm.terminalWord w)) at hMapped
    rw [SententialForm.mapNonterminal_terminalWord] at hMapped
    exact hMapped
  exact Derives.step hStart hMap

theorem union_generates_inv (G : CFG terminal left) (H : CFG terminal right)
    {w : Word terminal}
    (h : w ∈ GeneratedLanguage (UnionGrammar G H)) :
    w ∈ Language.Union (GeneratedLanguage G) (GeneratedLanguage H) := by
  have hterminal : w ∈ FormLanguage (UnionSymbolLanguage G H)
      (SententialForm.terminalWord (nt := SumStart left right) w) :=
    terminalWord_mem_formLanguage (UnionSymbolLanguage G H) (by intro a; rfl) w
  have hsound := union_derives_sound G H h hterminal
  cases hsound with
  | intro first hfirst =>
      cases hfirst with
      | intro tail htail =>
          cases htail.right.left
          rw [htail.right.right, Word.concat_empty_right]
          exact htail.left

theorem union_generated_language_exact (G : CFG terminal left) (H : CFG terminal right)
    (w : Word terminal) :
    w ∈ GeneratedLanguage (UnionGrammar G H) <->
      w ∈ Language.Union (GeneratedLanguage G) (GeneratedLanguage H) := by
  constructor
  · exact union_generates_inv G H
  · intro hw
    cases hw with
    | inl hleft =>
        exact union_generates_left G H hleft
    | inr hright =>
        exact union_generates_right G H hright


end CFG

end Grammars
end FoC
