import FoC.Grammars.GeneralGrammar

namespace FoC
namespace Book
namespace Chapter04
namespace Section06

/-!
Book: Chapter 4, Section 4.6, General Grammars.
-/

open Languages
open Grammars

-- Book: Chapter 4, Section 4.6, one general-grammar step is a derivation.
theorem general_yields_implies_derives {G : GeneralGrammar terminal nonterminal}
    {x y : SententialForm terminal nonterminal} (h : GeneralGrammar.Yields G x y) :
    GeneralGrammar.Derives G x y :=
  GeneralGrammar.yields_derives h

-- Book: Chapter 4, Section 4.6, derivations are transitive.
theorem general_derives_transitive {G : GeneralGrammar terminal nonterminal}
    {x y z : SententialForm terminal nonterminal}
    (hxy : GeneralGrammar.Derives G x y) (hyz : GeneralGrammar.Derives G y z) :
    GeneralGrammar.Derives G x z :=
  GeneralGrammar.derives_trans hxy hyz

-- Book: Chapter 4, Section 4.6, every CFG rule is a valid general-grammar rule.
def GeneralGrammarFromCFG (G : CFG terminal nonterminal) :
    GeneralGrammar terminal nonterminal :=
  GeneralGrammar.FromCFG G

-- Book: Chapter 4, Section 4.6, finite-production presentation for general
-- grammars.
def FiniteProductionGeneralGrammar
    (G : GeneralGrammar terminal nonterminal) : Prop :=
  GeneralGrammar.HasFiniteProductions G

-- Book: Chapter 4, Section 4.6, finite-production general-grammar language
-- vocabulary.
def FiniteProductionGeneralLanguage (L : Language terminal) : Prop :=
  GeneralGrammar.FiniteProductionGenerated L

-- Book: Chapter 4, finite grammars/countability discussion: a finite CFG
-- presentation is represented by a start nonterminal and a finite production
-- list.
def CFGFinitePresentationCode (terminal nonterminal : Type) :=
  CFG.FinitePresentationCode terminal nonterminal

-- Book: Chapter 4, finite grammars/countability discussion: a finite
-- unrestricted grammar presentation is represented by a start nonterminal and
-- a finite production list with arbitrary sentential-form left-hand sides.
def GeneralGrammarFinitePresentationCode (terminal nonterminal : Type) :=
  GeneralGrammar.FinitePresentationCode terminal nonterminal

-- Book: Chapter 4, finite grammars/countability discussion.  If terminal and
-- nonterminal symbols are explicitly encodable by natural numbers, then the
-- finite CFG presentation descriptions over those symbols are countable.
theorem cfg_finite_presentation_codes_countable
    (hterminal : Foundation.Countability.EncodableByNat terminal)
    (hnonterminal : Foundation.Countability.EncodableByNat nonterminal) :
    Foundation.FSet.Countable
      (Foundation.FSet.Univ :
        Foundation.FSet
          (CFGFinitePresentationCode terminal nonterminal)) :=
  CFG.FinitePresentationCode.countable hterminal hnonterminal

-- Book: Chapter 4, finite grammars/countability discussion.  The same
-- countability statement holds for finite unrestricted grammar presentation
-- descriptions.
theorem general_grammar_finite_presentation_codes_countable
    (hterminal : Foundation.Countability.EncodableByNat terminal)
    (hnonterminal : Foundation.Countability.EncodableByNat nonterminal) :
    Foundation.FSet.Countable
      (Foundation.FSet.Univ :
        Foundation.FSet
          (GeneralGrammarFinitePresentationCode terminal nonterminal)) :=
  GeneralGrammar.FinitePresentationCode.countable hterminal hnonterminal

-- Book: Chapter 4, Section 4.6, finite-production CFGs embed as
-- finite-production general grammars.
theorem finite_production_cfg_is_finite_production_general
    {G : CFG terminal nonterminal}
    (hG : CFG.HasFiniteProductions G) :
    FiniteProductionGeneralGrammar (GeneralGrammarFromCFG G) :=
  GeneralGrammar.fromCFG_hasFiniteProductions hG

-- Book: Chapter 4, Section 4.6, CFG derivations embed in general grammars.
theorem cfg_derivation_is_general_derivation {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : CFG.Derives G x y) :
    GeneralGrammar.Derives (GeneralGrammar.FromCFG G) x y :=
  GeneralGrammar.cfg_derives_embeds h

-- Book: Chapter 4, Section 4.6, CFG-generated words are general-grammar generated.
theorem cfg_generated_word_is_general_generated (G : CFG terminal nonterminal)
    {w : Word terminal} (h : w ∈ CFG.GeneratedLanguage G) :
    w ∈ GeneralGrammar.GeneratedLanguage (GeneralGrammar.FromCFG G) :=
  GeneralGrammar.cfg_generated_language_embeds G h

theorem general_yields_of_production {G : GeneralGrammar terminal nonterminal}
    {lhs rhs : SententialForm terminal nonterminal}
    (hprod : G.produces lhs rhs) (u v : SententialForm terminal nonterminal) :
    GeneralGrammar.Yields G (u ++ lhs ++ v) (u ++ rhs ++ v) := by
  exists u
  exists v
  exists lhs
  exists rhs

-- Book: Chapter 4, Section 4.6, unrestricted grammar steps are closed under
-- arbitrary sentential-form context.
theorem general_yields_context {G : GeneralGrammar terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : GeneralGrammar.Yields G x y)
    (u v : SententialForm terminal nonterminal) :
    GeneralGrammar.Yields G (u ++ x ++ v) (u ++ y ++ v) := by
  rcases h with ⟨u₀, v₀, lhs, rhs, hprod, hx, hy⟩
  exists u ++ u₀
  exists v₀ ++ v
  exists lhs
  exists rhs
  constructor
  · exact hprod
  constructor
  · rw [hx]
    simp [List.append_assoc]
  · rw [hy]
    simp [List.append_assoc]

-- Book: Chapter 4, Section 4.6, unrestricted derivations are closed under
-- arbitrary sentential-form context.
theorem general_derives_context {G : GeneralGrammar terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : GeneralGrammar.Derives G x y)
    (u v : SententialForm terminal nonterminal) :
    GeneralGrammar.Derives G (u ++ x ++ v) (u ++ y ++ v) := by
  induction h with
  | refl z =>
      exact GeneralGrammar.Derives.refl (G := G) (u ++ z ++ v)
  | step hstep _ ih =>
      exact GeneralGrammar.Derives.step
        (general_yields_context hstep u v) ih

theorem general_formLanguage_replace_sound
    (symbolLanguage : Symbol terminal nonterminal -> Language terminal)
    {u lhs rhs v : SententialForm terminal nonterminal}
    {w : Word terminal}
    (hlocal : forall x, x ∈ CFG.FormLanguage symbolLanguage rhs ->
      x ∈ CFG.FormLanguage symbolLanguage lhs)
    (hw : w ∈ CFG.FormLanguage symbolLanguage (u ++ rhs ++ v)) :
    w ∈ CFG.FormLanguage symbolLanguage (u ++ lhs ++ v) := by
  have hu := (CFG.formLanguage_append symbolLanguage u (rhs ++ v) w).mp (by
    simpa [List.append_assoc] using hw)
  rcases hu with ⟨pref, suffix, hpref, hsuffix, hwEq⟩
  have hsSplit :=
    (CFG.formLanguage_append symbolLanguage rhs v suffix).mp hsuffix
  rcases hsSplit with ⟨middle, tail, hmiddle, htail, hsuffixEq⟩
  have hnew : w ∈ CFG.FormLanguage symbolLanguage (u ++ (lhs ++ v)) := by
    apply (CFG.formLanguage_append symbolLanguage u (lhs ++ v) w).mpr
    refine ⟨pref, Word.Concat middle tail, hpref, ?_, ?_⟩
    · apply (CFG.formLanguage_append symbolLanguage lhs v
        (Word.Concat middle tail)).mpr
      exact ⟨middle, tail, hlocal middle hmiddle, htail, rfl⟩
    · calc
        w = Word.Concat pref suffix := hwEq
        _ = Word.Concat pref (Word.Concat middle tail) := by
          rw [hsuffixEq]
  simpa [List.append_assoc] using hnew

theorem general_yields_sound_for_symbol_language
    {G : GeneralGrammar terminal nonterminal}
    (symbolLanguage : Symbol terminal nonterminal -> Language terminal)
    (hprod : forall lhs rhs, G.produces lhs rhs -> forall w,
      w ∈ CFG.FormLanguage symbolLanguage rhs ->
        w ∈ CFG.FormLanguage symbolLanguage lhs)
    {x y : SententialForm terminal nonterminal} {w : Word terminal}
    (h : GeneralGrammar.Yields G x y)
    (hw : w ∈ CFG.FormLanguage symbolLanguage y) :
    w ∈ CFG.FormLanguage symbolLanguage x := by
  rcases h with ⟨u, v, lhs, rhs, hprodRule, hx, hy⟩
  rw [hy] at hw
  rw [hx]
  exact general_formLanguage_replace_sound symbolLanguage
    (hprod lhs rhs hprodRule) hw

theorem general_derives_sound_for_symbol_language_aux
    {G : GeneralGrammar terminal nonterminal}
    (symbolLanguage : Symbol terminal nonterminal -> Language terminal)
    (hterminal : forall a,
      Word.Symbol a ∈ symbolLanguage (Symbol.terminal a))
    (hprod : forall lhs rhs, G.produces lhs rhs -> forall w,
      w ∈ CFG.FormLanguage symbolLanguage rhs ->
        w ∈ CFG.FormLanguage symbolLanguage lhs)
    {x y : SententialForm terminal nonterminal} {w : Word terminal}
    (hy : y = SententialForm.terminalWord w)
    (h : GeneralGrammar.Derives G x y) :
    w ∈ CFG.FormLanguage symbolLanguage x := by
  induction h generalizing w with
  | refl _ =>
      rw [hy]
      exact CFG.terminalWord_mem_formLanguage symbolLanguage hterminal w
  | step hstep _ ih =>
      exact general_yields_sound_for_symbol_language symbolLanguage hprod hstep
        (ih hy)

theorem general_derives_sound_for_symbol_language
    {G : GeneralGrammar terminal nonterminal}
    (symbolLanguage : Symbol terminal nonterminal -> Language terminal)
    (hterminal : forall a,
      Word.Symbol a ∈ symbolLanguage (Symbol.terminal a))
    (hprod : forall lhs rhs, G.produces lhs rhs -> forall w,
      w ∈ CFG.FormLanguage symbolLanguage rhs ->
        w ∈ CFG.FormLanguage symbolLanguage lhs)
    {x : SententialForm terminal nonterminal} {w : Word terminal}
    (h : GeneralGrammar.Derives G x (SententialForm.terminalWord w)) :
    w ∈ CFG.FormLanguage symbolLanguage x :=
  general_derives_sound_for_symbol_language_aux symbolLanguage hterminal hprod
    rfl h

def ggTerminal (a : terminal) : Symbol terminal nonterminal :=
  Symbol.terminal a

def ggNonterminal (A : nonterminal) : Symbol terminal nonterminal :=
  Symbol.nonterminal A

def SententialCountTerminal [DecidableEq terminal] (a : terminal) :
    SententialForm terminal nonterminal -> Nat
  | [] => 0
  | Symbol.terminal b :: rest =>
      (if b = a then 1 else 0) + SententialCountTerminal a rest
  | Symbol.nonterminal _ :: rest => SententialCountTerminal a rest

def SententialCountNonterminal [DecidableEq nonterminal] (A : nonterminal) :
    SententialForm terminal nonterminal -> Nat
  | [] => 0
  | Symbol.terminal _ :: rest => SententialCountNonterminal A rest
  | Symbol.nonterminal B :: rest =>
      (if B = A then 1 else 0) + SententialCountNonterminal A rest

theorem sententialCountTerminal_append [DecidableEq terminal]
    (a : terminal) (x y : SententialForm terminal nonterminal) :
    SententialCountTerminal a (x ++ y) =
      SententialCountTerminal a x + SententialCountTerminal a y := by
  induction x with
  | nil => simp [SententialCountTerminal]
  | cons s rest ih =>
      cases s <;> simp [SententialCountTerminal, ih] <;> omega

theorem sententialCountNonterminal_append [DecidableEq nonterminal]
    (A : nonterminal) (x y : SententialForm terminal nonterminal) :
    SententialCountNonterminal A (x ++ y) =
      SententialCountNonterminal A x + SententialCountNonterminal A y := by
  induction x with
  | nil => simp [SententialCountNonterminal]
  | cons s rest ih =>
      cases s <;> simp [SententialCountNonterminal, ih] <;> omega

theorem sententialCountTerminal_terminalWord [DecidableEq terminal]
    (a : terminal) (w : Word terminal) :
    SententialCountTerminal (nonterminal := nonterminal) a
      (SententialForm.terminalWord w) =
      Word.Count a w := by
  induction w with
  | nil => rfl
  | cons b rest ih =>
      change (if b = a then 1 else 0) +
          SententialCountTerminal a (SententialForm.terminalWord rest) =
        (if b = a then 1 else 0) + Word.Count a rest
      rw [ih]

theorem sententialCountNonterminal_terminalWord [DecidableEq nonterminal]
    (A : nonterminal) (w : Word terminal) :
    SententialCountNonterminal A (SententialForm.terminalWord w) = 0 := by
  induction w with
  | nil => rfl
  | cons _ rest ih =>
      change SententialCountNonterminal A (SententialForm.terminalWord rest) = 0
      exact ih

theorem repeatSymbol_succ_eq_append (a : terminal) (n : Nat) :
    Word.RepeatSymbol a (n + 1) =
      Word.Concat (Word.RepeatSymbol a n) [a] := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change a :: Word.RepeatSymbol a (n + 1) =
        a :: Word.Concat (Word.RepeatSymbol a n) [a]
      rw [ih]

inductive EqualCountTerminal where
  | a
  | b
  | c
deriving DecidableEq

inductive EqualCountNT where
  | start
  | markA
  | markB
  | markC
deriving DecidableEq

namespace EqualCountNT

def finite : Foundation.FiniteType EqualCountNT where
  elems := [start, markA, markB, markC]
  complete := by
    intro A
    cases A <;> simp

end EqualCountNT

def ecT (tok : EqualCountTerminal) :
    Symbol EqualCountTerminal EqualCountNT :=
  ggTerminal tok

def ecN (A : EqualCountNT) :
    Symbol EqualCountTerminal EqualCountNT :=
  ggNonterminal A

inductive EqualCountProduces :
    SententialForm EqualCountTerminal EqualCountNT ->
      SententialForm EqualCountTerminal EqualCountNT -> Prop where
  | grow :
      EqualCountProduces [ecN EqualCountNT.start]
        [ecN EqualCountNT.start, ecN EqualCountNT.markA,
          ecN EqualCountNT.markB, ecN EqualCountNT.markC]
  | stop :
      EqualCountProduces [ecN EqualCountNT.start] []
  | swapAB :
      EqualCountProduces [ecN EqualCountNT.markA, ecN EqualCountNT.markB]
        [ecN EqualCountNT.markB, ecN EqualCountNT.markA]
  | swapBA :
      EqualCountProduces [ecN EqualCountNT.markB, ecN EqualCountNT.markA]
        [ecN EqualCountNT.markA, ecN EqualCountNT.markB]
  | swapAC :
      EqualCountProduces [ecN EqualCountNT.markA, ecN EqualCountNT.markC]
        [ecN EqualCountNT.markC, ecN EqualCountNT.markA]
  | swapCA :
      EqualCountProduces [ecN EqualCountNT.markC, ecN EqualCountNT.markA]
        [ecN EqualCountNT.markA, ecN EqualCountNT.markC]
  | swapBC :
      EqualCountProduces [ecN EqualCountNT.markB, ecN EqualCountNT.markC]
        [ecN EqualCountNT.markC, ecN EqualCountNT.markB]
  | swapCB :
      EqualCountProduces [ecN EqualCountNT.markC, ecN EqualCountNT.markB]
        [ecN EqualCountNT.markB, ecN EqualCountNT.markC]
  | emitA :
      EqualCountProduces [ecN EqualCountNT.markA]
        [ecT EqualCountTerminal.a]
  | emitB :
      EqualCountProduces [ecN EqualCountNT.markB]
        [ecT EqualCountTerminal.b]
  | emitC :
      EqualCountProduces [ecN EqualCountNT.markC]
        [ecT EqualCountTerminal.c]

def EqualCountGrammar :
    GeneralGrammar EqualCountTerminal EqualCountNT where
  start := EqualCountNT.start
  produces := EqualCountProduces
  lhsContainsNonterminal := by
    intro lhs rhs h
    cases h <;> simp [SententialForm.containsNonterminal, ecN,
      ggNonterminal]
  nonterminalsFinite := EqualCountNT.finite

def EqualCountProductionList :
    List (GeneralGrammar.Production EqualCountTerminal EqualCountNT) :=
  [{ lhs := [ecN EqualCountNT.start],
     rhs := [ecN EqualCountNT.start, ecN EqualCountNT.markA,
       ecN EqualCountNT.markB, ecN EqualCountNT.markC] },
   { lhs := [ecN EqualCountNT.start],
     rhs := [] },
   { lhs := [ecN EqualCountNT.markA, ecN EqualCountNT.markB],
     rhs := [ecN EqualCountNT.markB, ecN EqualCountNT.markA] },
   { lhs := [ecN EqualCountNT.markB, ecN EqualCountNT.markA],
     rhs := [ecN EqualCountNT.markA, ecN EqualCountNT.markB] },
   { lhs := [ecN EqualCountNT.markA, ecN EqualCountNT.markC],
     rhs := [ecN EqualCountNT.markC, ecN EqualCountNT.markA] },
   { lhs := [ecN EqualCountNT.markC, ecN EqualCountNT.markA],
     rhs := [ecN EqualCountNT.markA, ecN EqualCountNT.markC] },
   { lhs := [ecN EqualCountNT.markB, ecN EqualCountNT.markC],
     rhs := [ecN EqualCountNT.markC, ecN EqualCountNT.markB] },
   { lhs := [ecN EqualCountNT.markC, ecN EqualCountNT.markB],
     rhs := [ecN EqualCountNT.markB, ecN EqualCountNT.markC] },
   { lhs := [ecN EqualCountNT.markA],
     rhs := [ecT EqualCountTerminal.a] },
   { lhs := [ecN EqualCountNT.markB],
     rhs := [ecT EqualCountTerminal.b] },
   { lhs := [ecN EqualCountNT.markC],
     rhs := [ecT EqualCountTerminal.c] }]

-- Book: Chapter 4, Section 4.6, the equal-count general grammar has a finite
-- production presentation.
theorem equalCountGrammar_has_finite_productions :
    GeneralGrammar.HasFiniteProductions EqualCountGrammar := by
  exists EqualCountProductionList
  intro lhs rhs
  constructor
  · intro h
    cases h <;> simp [EqualCountProductionList]
  · intro h
    rcases h with ⟨rule, hmem, hlhs, hrhs⟩
    simp [EqualCountProductionList] at hmem
    rcases hmem with
      hrule | hrule | hrule | hrule | hrule | hrule |
      hrule | hrule | hrule | hrule | hrule
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.grow
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.stop
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.swapAB
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.swapBA
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.swapAC
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.swapCA
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.swapBC
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.swapCB
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.emitA
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.emitB
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.emitC

-- Book: Chapter 4, Section 4.6, the language generated by the equal-count
-- example grammar is generated by a finite general grammar.
theorem equalCountGrammar_finite_production_generated :
    FiniteProductionGeneralLanguage
      (GeneralGrammar.GeneratedLanguage EqualCountGrammar) := by
  exists EqualCountNT
  exists EqualCountGrammar
  constructor
  · exact equalCountGrammar_has_finite_productions
  · intro w
    rfl

def equalCountTotalA (sf : SententialForm EqualCountTerminal EqualCountNT) :
    Nat :=
  SententialCountTerminal EqualCountTerminal.a sf +
    SententialCountNonterminal EqualCountNT.markA sf

def equalCountTotalB (sf : SententialForm EqualCountTerminal EqualCountNT) :
    Nat :=
  SententialCountTerminal EqualCountTerminal.b sf +
    SententialCountNonterminal EqualCountNT.markB sf

def equalCountTotalC (sf : SententialForm EqualCountTerminal EqualCountNT) :
    Nat :=
  SententialCountTerminal EqualCountTerminal.c sf +
    SententialCountNonterminal EqualCountNT.markC sf

def equalCountBalanced
    (sf : SententialForm EqualCountTerminal EqualCountNT) : Prop :=
  equalCountTotalA sf = equalCountTotalB sf ∧
    equalCountTotalB sf = equalCountTotalC sf

theorem equalCount_start_balanced :
    equalCountBalanced [ecN EqualCountNT.start] := by
  simp [equalCountBalanced, equalCountTotalA, equalCountTotalB,
    equalCountTotalC, SententialCountTerminal, SententialCountNonterminal,
    ecN, ggNonterminal]

-- Book: Chapter 4, Section 4.6, the equal-count general grammar preserves
-- the invariant `n_A+n_a = n_B+n_b = n_C+n_c`.
theorem equalCount_yields_preserves_balanced
    {x y : SententialForm EqualCountTerminal EqualCountNT}
    (h : GeneralGrammar.Yields EqualCountGrammar x y) :
    equalCountBalanced x -> equalCountBalanced y := by
  intro hbalanced
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro lhs hlhs =>
              cases hlhs with
              | intro rhs hrhs =>
                  cases hrhs with
                  | intro hprod hrest =>
                      cases hrest with
                      | intro hx hy =>
                          rw [hx] at hbalanced
                          rw [hy]
                          cases hprod <;>
                            simp [equalCountBalanced, equalCountTotalA,
                              equalCountTotalB, equalCountTotalC,
                              sententialCountTerminal_append,
                              sententialCountNonterminal_append,
                              SententialCountTerminal,
                              SententialCountNonterminal, ecN, ecT,
                              ggNonterminal, ggTerminal] at hbalanced ⊢ <;>
                            omega

-- Book: Chapter 4, Section 4.6, the equal-count invariant is stable through
-- derivations.
theorem equalCount_derives_preserves_balanced
    {x y : SententialForm EqualCountTerminal EqualCountNT}
    (h : GeneralGrammar.Derives EqualCountGrammar x y) :
    equalCountBalanced x -> equalCountBalanced y := by
  induction h with
  | refl _ =>
      intro hbalanced
      exact hbalanced
  | step hstep _ ih =>
      intro hbalanced
      exact ih (equalCount_yields_preserves_balanced hstep hbalanced)

-- Book: Chapter 4, Section 4.6, every terminal word generated by the
-- equal-count grammar has the same number of a's, b's, and c's.
theorem equalCountGrammar_generated_has_equal_terminal_counts
    {w : Word EqualCountTerminal}
    (h : w ∈ GeneralGrammar.GeneratedLanguage EqualCountGrammar) :
    Word.Count EqualCountTerminal.a w = Word.Count EqualCountTerminal.b w ∧
      Word.Count EqualCountTerminal.b w = Word.Count EqualCountTerminal.c w := by
  have hderives :
      GeneralGrammar.Derives EqualCountGrammar [ecN EqualCountNT.start]
        (SententialForm.terminalWord w) := by
    simpa [GeneralGrammar.GeneratedLanguage, EqualCountGrammar, ecN,
      ggNonterminal] using h
  have hbalanced :=
    equalCount_derives_preserves_balanced hderives equalCount_start_balanced
  simpa [equalCountBalanced, equalCountTotalA, equalCountTotalB,
    equalCountTotalC, sententialCountTerminal_terminalWord,
    sententialCountNonterminal_terminalWord] using hbalanced

def baabccWord : Word EqualCountTerminal :=
  [EqualCountTerminal.b, EqualCountTerminal.a, EqualCountTerminal.a,
    EqualCountTerminal.b, EqualCountTerminal.c, EqualCountTerminal.c]

-- Book: Chapter 4, Section 4.6, the sample derivation of `baabcc`.
theorem equalCountGrammar_generates_baabcc :
    baabccWord ∈ GeneralGrammar.GeneratedLanguage EqualCountGrammar := by
  let S := ecN EqualCountNT.start
  let A := ecN EqualCountNT.markA
  let B := ecN EqualCountNT.markB
  let C := ecN EqualCountNT.markC
  let a := ecT EqualCountTerminal.a
  let b := ecT EqualCountTerminal.b
  let c := ecT EqualCountTerminal.c
  have h1 : GeneralGrammar.Yields EqualCountGrammar [S] [S, A, B, C] := by
    simpa [S, A, B, C] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.grow [] []
  have h2 :
      GeneralGrammar.Yields EqualCountGrammar [S, A, B, C]
        [S, A, B, C, A, B, C] := by
    simpa [S, A, B, C] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.grow [] [A, B, C]
  have h3 :
      GeneralGrammar.Yields EqualCountGrammar [S, A, B, C, A, B, C]
        [A, B, C, A, B, C] := by
    simpa [S, A, B, C] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.stop [] [A, B, C, A, B, C]
  have h4 :
      GeneralGrammar.Yields EqualCountGrammar [A, B, C, A, B, C]
        [B, A, C, A, B, C] := by
    simpa [A, B, C] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.swapAB [] [C, A, B, C]
  have h5 :
      GeneralGrammar.Yields EqualCountGrammar [B, A, C, A, B, C]
        [B, A, A, C, B, C] := by
    simpa [A, B, C] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.swapCA [B, A] [B, C]
  have h6 :
      GeneralGrammar.Yields EqualCountGrammar [B, A, A, C, B, C]
        [B, A, A, B, C, C] := by
    simpa [A, B, C] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.swapCB [B, A, A] [C]
  have h7 :
      GeneralGrammar.Yields EqualCountGrammar [B, A, A, B, C, C]
        [b, A, A, B, C, C] := by
    simpa [A, B, C, b] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.emitB [] [A, A, B, C, C]
  have h8 :
      GeneralGrammar.Yields EqualCountGrammar [b, A, A, B, C, C]
        [b, a, A, B, C, C] := by
    simpa [A, B, C, a, b] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.emitA [b] [A, B, C, C]
  have h9 :
      GeneralGrammar.Yields EqualCountGrammar [b, a, A, B, C, C]
        [b, a, a, B, C, C] := by
    simpa [A, B, C, a, b] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.emitA [b, a] [B, C, C]
  have h10 :
      GeneralGrammar.Yields EqualCountGrammar [b, a, a, B, C, C]
        [b, a, a, b, C, C] := by
    simpa [A, B, C, a, b] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.emitB [b, a, a] [C, C]
  have h11 :
      GeneralGrammar.Yields EqualCountGrammar [b, a, a, b, C, C]
        [b, a, a, b, c, C] := by
    simpa [A, B, C, a, b, c] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.emitC [b, a, a, b] [C]
  have h12 :
      GeneralGrammar.Yields EqualCountGrammar [b, a, a, b, c, C]
        [b, a, a, b, c, c] := by
    simpa [A, B, C, a, b, c] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.emitC [b, a, a, b, c] []
  have hderives :
      GeneralGrammar.Derives EqualCountGrammar [S] [b, a, a, b, c, c] :=
    GeneralGrammar.Derives.step h1
      (GeneralGrammar.Derives.step h2
        (GeneralGrammar.Derives.step h3
          (GeneralGrammar.Derives.step h4
            (GeneralGrammar.Derives.step h5
              (GeneralGrammar.Derives.step h6
                (GeneralGrammar.Derives.step h7
                  (GeneralGrammar.Derives.step h8
                    (GeneralGrammar.Derives.step h9
                      (GeneralGrammar.Derives.step h10
                        (GeneralGrammar.Derives.step h11
                          (GeneralGrammar.Derives.step h12
                            (GeneralGrammar.Derives.refl
                              [b, a, a, b, c, c]))))))))))))
  simpa [GeneralGrammar.GeneratedLanguage, EqualCountGrammar, baabccWord,
    SententialForm.terminalWord, S, a, b, c] using hderives

inductive FourCountTerminal where
  | a
  | b
  | c
  | d
deriving DecidableEq

inductive FourCountNT where
  | start
  | markA
  | markB
  | markC
  | markD
deriving DecidableEq

namespace FourCountNT

def finite : Foundation.FiniteType FourCountNT where
  elems := [start, markA, markB, markC, markD]
  complete := by
    intro A
    cases A <;> simp

end FourCountNT

def fcT (tok : FourCountTerminal) :
    Symbol FourCountTerminal FourCountNT :=
  ggTerminal tok

def fcN (A : FourCountNT) :
    Symbol FourCountTerminal FourCountNT :=
  ggNonterminal A

inductive FourCountProduces :
    SententialForm FourCountTerminal FourCountNT ->
      SententialForm FourCountTerminal FourCountNT -> Prop where
  | grow :
      FourCountProduces [fcN FourCountNT.start]
        [fcN FourCountNT.start, fcN FourCountNT.markA,
          fcN FourCountNT.markB, fcN FourCountNT.markC,
          fcN FourCountNT.markD]
  | stop :
      FourCountProduces [fcN FourCountNT.start] []
  | swapAB :
      FourCountProduces [fcN FourCountNT.markA, fcN FourCountNT.markB]
        [fcN FourCountNT.markB, fcN FourCountNT.markA]
  | swapBA :
      FourCountProduces [fcN FourCountNT.markB, fcN FourCountNT.markA]
        [fcN FourCountNT.markA, fcN FourCountNT.markB]
  | swapAC :
      FourCountProduces [fcN FourCountNT.markA, fcN FourCountNT.markC]
        [fcN FourCountNT.markC, fcN FourCountNT.markA]
  | swapCA :
      FourCountProduces [fcN FourCountNT.markC, fcN FourCountNT.markA]
        [fcN FourCountNT.markA, fcN FourCountNT.markC]
  | swapAD :
      FourCountProduces [fcN FourCountNT.markA, fcN FourCountNT.markD]
        [fcN FourCountNT.markD, fcN FourCountNT.markA]
  | swapDA :
      FourCountProduces [fcN FourCountNT.markD, fcN FourCountNT.markA]
        [fcN FourCountNT.markA, fcN FourCountNT.markD]
  | swapBC :
      FourCountProduces [fcN FourCountNT.markB, fcN FourCountNT.markC]
        [fcN FourCountNT.markC, fcN FourCountNT.markB]
  | swapCB :
      FourCountProduces [fcN FourCountNT.markC, fcN FourCountNT.markB]
        [fcN FourCountNT.markB, fcN FourCountNT.markC]
  | swapBD :
      FourCountProduces [fcN FourCountNT.markB, fcN FourCountNT.markD]
        [fcN FourCountNT.markD, fcN FourCountNT.markB]
  | swapDB :
      FourCountProduces [fcN FourCountNT.markD, fcN FourCountNT.markB]
        [fcN FourCountNT.markB, fcN FourCountNT.markD]
  | swapCD :
      FourCountProduces [fcN FourCountNT.markC, fcN FourCountNT.markD]
        [fcN FourCountNT.markD, fcN FourCountNT.markC]
  | swapDC :
      FourCountProduces [fcN FourCountNT.markD, fcN FourCountNT.markC]
        [fcN FourCountNT.markC, fcN FourCountNT.markD]
  | emitA :
      FourCountProduces [fcN FourCountNT.markA]
        [fcT FourCountTerminal.a]
  | emitB :
      FourCountProduces [fcN FourCountNT.markB]
        [fcT FourCountTerminal.b]
  | emitC :
      FourCountProduces [fcN FourCountNT.markC]
        [fcT FourCountTerminal.c]
  | emitD :
      FourCountProduces [fcN FourCountNT.markD]
        [fcT FourCountTerminal.d]

def FourCountGrammar :
    GeneralGrammar FourCountTerminal FourCountNT where
  start := FourCountNT.start
  produces := FourCountProduces
  lhsContainsNonterminal := by
    intro lhs rhs h
    cases h <;> simp [SententialForm.containsNonterminal, fcN,
      ggNonterminal]
  nonterminalsFinite := FourCountNT.finite

def FourCountProductionList :
    List (GeneralGrammar.Production FourCountTerminal FourCountNT) :=
  [{ lhs := [fcN FourCountNT.start],
     rhs := [fcN FourCountNT.start, fcN FourCountNT.markA,
       fcN FourCountNT.markB, fcN FourCountNT.markC,
       fcN FourCountNT.markD] },
   { lhs := [fcN FourCountNT.start],
     rhs := [] },
   { lhs := [fcN FourCountNT.markA, fcN FourCountNT.markB],
     rhs := [fcN FourCountNT.markB, fcN FourCountNT.markA] },
   { lhs := [fcN FourCountNT.markB, fcN FourCountNT.markA],
     rhs := [fcN FourCountNT.markA, fcN FourCountNT.markB] },
   { lhs := [fcN FourCountNT.markA, fcN FourCountNT.markC],
     rhs := [fcN FourCountNT.markC, fcN FourCountNT.markA] },
   { lhs := [fcN FourCountNT.markC, fcN FourCountNT.markA],
     rhs := [fcN FourCountNT.markA, fcN FourCountNT.markC] },
   { lhs := [fcN FourCountNT.markA, fcN FourCountNT.markD],
     rhs := [fcN FourCountNT.markD, fcN FourCountNT.markA] },
   { lhs := [fcN FourCountNT.markD, fcN FourCountNT.markA],
     rhs := [fcN FourCountNT.markA, fcN FourCountNT.markD] },
   { lhs := [fcN FourCountNT.markB, fcN FourCountNT.markC],
     rhs := [fcN FourCountNT.markC, fcN FourCountNT.markB] },
   { lhs := [fcN FourCountNT.markC, fcN FourCountNT.markB],
     rhs := [fcN FourCountNT.markB, fcN FourCountNT.markC] },
   { lhs := [fcN FourCountNT.markB, fcN FourCountNT.markD],
     rhs := [fcN FourCountNT.markD, fcN FourCountNT.markB] },
   { lhs := [fcN FourCountNT.markD, fcN FourCountNT.markB],
     rhs := [fcN FourCountNT.markB, fcN FourCountNT.markD] },
   { lhs := [fcN FourCountNT.markC, fcN FourCountNT.markD],
     rhs := [fcN FourCountNT.markD, fcN FourCountNT.markC] },
   { lhs := [fcN FourCountNT.markD, fcN FourCountNT.markC],
     rhs := [fcN FourCountNT.markC, fcN FourCountNT.markD] },
   { lhs := [fcN FourCountNT.markA],
     rhs := [fcT FourCountTerminal.a] },
   { lhs := [fcN FourCountNT.markB],
     rhs := [fcT FourCountTerminal.b] },
   { lhs := [fcN FourCountNT.markC],
     rhs := [fcT FourCountTerminal.c] },
   { lhs := [fcN FourCountNT.markD],
     rhs := [fcT FourCountTerminal.d] }]

-- Book: Chapter 4, Section 4.6, selected exercise grammar for words with
-- equal numbers of four different terminals.
theorem fourCountGrammar_has_finite_productions :
    GeneralGrammar.HasFiniteProductions FourCountGrammar := by
  exists FourCountProductionList
  intro lhs rhs
  constructor
  · intro h
    cases h <;> simp [FourCountProductionList]
  · intro h
    rcases h with ⟨rule, hmem, hlhs, hrhs⟩
    simp [FourCountProductionList] at hmem
    rcases hmem with
      hrule | hrule | hrule | hrule | hrule | hrule |
      hrule | hrule | hrule | hrule | hrule | hrule |
      hrule | hrule | hrule | hrule | hrule | hrule
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.grow
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.stop
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapAB
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapBA
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapAC
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapCA
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapAD
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapDA
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapBC
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapCB
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapBD
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapDB
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapCD
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapDC
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.emitA
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.emitB
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.emitC
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.emitD

theorem fourCountGrammar_finite_production_generated :
    FiniteProductionGeneralLanguage
      (GeneralGrammar.GeneratedLanguage FourCountGrammar) := by
  exists FourCountNT
  exists FourCountGrammar
  constructor
  · exact fourCountGrammar_has_finite_productions
  · intro w
    rfl

def fourCountTotalA (sf : SententialForm FourCountTerminal FourCountNT) :
    Nat :=
  SententialCountTerminal FourCountTerminal.a sf +
    SententialCountNonterminal FourCountNT.markA sf

def fourCountTotalB (sf : SententialForm FourCountTerminal FourCountNT) :
    Nat :=
  SententialCountTerminal FourCountTerminal.b sf +
    SententialCountNonterminal FourCountNT.markB sf

def fourCountTotalC (sf : SententialForm FourCountTerminal FourCountNT) :
    Nat :=
  SententialCountTerminal FourCountTerminal.c sf +
    SententialCountNonterminal FourCountNT.markC sf

def fourCountTotalD (sf : SententialForm FourCountTerminal FourCountNT) :
    Nat :=
  SententialCountTerminal FourCountTerminal.d sf +
    SententialCountNonterminal FourCountNT.markD sf

def fourCountBalanced
    (sf : SententialForm FourCountTerminal FourCountNT) : Prop :=
  fourCountTotalA sf = fourCountTotalB sf ∧
    fourCountTotalB sf = fourCountTotalC sf ∧
    fourCountTotalC sf = fourCountTotalD sf

theorem fourCount_start_balanced :
    fourCountBalanced [fcN FourCountNT.start] := by
  simp [fourCountBalanced, fourCountTotalA, fourCountTotalB,
    fourCountTotalC, fourCountTotalD, SententialCountTerminal,
    SententialCountNonterminal, fcN, ggNonterminal]

theorem fourCount_yields_preserves_balanced
    {x y : SententialForm FourCountTerminal FourCountNT}
    (h : GeneralGrammar.Yields FourCountGrammar x y) :
    fourCountBalanced x -> fourCountBalanced y := by
  intro hbalanced
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro lhs hlhs =>
              cases hlhs with
              | intro rhs hrhs =>
                  cases hrhs with
                  | intro hprod hrest =>
                      cases hrest with
                      | intro hx hy =>
                          rw [hx] at hbalanced
                          rw [hy]
                          cases hprod <;>
                            simp [fourCountBalanced, fourCountTotalA,
                              fourCountTotalB, fourCountTotalC,
                              fourCountTotalD,
                              sententialCountTerminal_append,
                              sententialCountNonterminal_append,
                              SententialCountTerminal,
                              SententialCountNonterminal, fcN, fcT,
                              ggNonterminal, ggTerminal] at hbalanced ⊢ <;>
                            omega

theorem fourCount_derives_preserves_balanced
    {x y : SententialForm FourCountTerminal FourCountNT}
    (h : GeneralGrammar.Derives FourCountGrammar x y) :
    fourCountBalanced x -> fourCountBalanced y := by
  induction h with
  | refl _ =>
      intro hbalanced
      exact hbalanced
  | step hstep _ ih =>
      intro hbalanced
      exact ih (fourCount_yields_preserves_balanced hstep hbalanced)

theorem fourCountGrammar_generated_has_equal_terminal_counts
    {w : Word FourCountTerminal}
    (h : w ∈ GeneralGrammar.GeneratedLanguage FourCountGrammar) :
    Word.Count FourCountTerminal.a w = Word.Count FourCountTerminal.b w ∧
      Word.Count FourCountTerminal.b w = Word.Count FourCountTerminal.c w ∧
      Word.Count FourCountTerminal.c w = Word.Count FourCountTerminal.d w := by
  have hderives :
      GeneralGrammar.Derives FourCountGrammar [fcN FourCountNT.start]
        (SententialForm.terminalWord w) := by
    simpa [GeneralGrammar.GeneratedLanguage, FourCountGrammar, fcN,
      ggNonterminal] using h
  have hbalanced :=
    fourCount_derives_preserves_balanced hderives fourCount_start_balanced
  simpa [fourCountBalanced, fourCountTotalA, fourCountTotalB,
    fourCountTotalC, fourCountTotalD,
    sententialCountTerminal_terminalWord,
    sententialCountNonterminal_terminalWord] using hbalanced

def dacbWord : Word FourCountTerminal :=
  [FourCountTerminal.d, FourCountTerminal.a, FourCountTerminal.c,
    FourCountTerminal.b]

-- Book: Chapter 4, Section 4.6, concrete derivation from the four-equal-count
-- exercise grammar.
theorem fourCountGrammar_generates_dacb :
    dacbWord ∈ GeneralGrammar.GeneratedLanguage FourCountGrammar := by
  let S := fcN FourCountNT.start
  let A := fcN FourCountNT.markA
  let B := fcN FourCountNT.markB
  let C := fcN FourCountNT.markC
  let D := fcN FourCountNT.markD
  let a := fcT FourCountTerminal.a
  let b := fcT FourCountTerminal.b
  let c := fcT FourCountTerminal.c
  let d := fcT FourCountTerminal.d
  have h1 : GeneralGrammar.Yields FourCountGrammar [S] [S, A, B, C, D] := by
    simpa [S, A, B, C, D] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.grow [] []
  have h2 :
      GeneralGrammar.Yields FourCountGrammar [S, A, B, C, D]
        [A, B, C, D] := by
    simpa [S, A, B, C, D] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.stop [] [A, B, C, D]
  have h3 :
      GeneralGrammar.Yields FourCountGrammar [A, B, C, D]
        [A, B, D, C] := by
    simpa [A, B, C, D] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.swapCD [A, B] []
  have h4 :
      GeneralGrammar.Yields FourCountGrammar [A, B, D, C]
        [A, D, B, C] := by
    simpa [A, B, C, D] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.swapBD [A] [C]
  have h5 :
      GeneralGrammar.Yields FourCountGrammar [A, D, B, C]
        [D, A, B, C] := by
    simpa [A, B, C, D] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.swapAD [] [B, C]
  have h6 :
      GeneralGrammar.Yields FourCountGrammar [D, A, B, C]
        [D, A, C, B] := by
    simpa [A, B, C, D] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.swapBC [D, A] []
  have h7 :
      GeneralGrammar.Yields FourCountGrammar [D, A, C, B]
        [d, A, C, B] := by
    simpa [A, B, C, D, d] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.emitD [] [A, C, B]
  have h8 :
      GeneralGrammar.Yields FourCountGrammar [d, A, C, B]
        [d, a, C, B] := by
    simpa [A, B, C, a, d] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.emitA [d] [C, B]
  have h9 :
      GeneralGrammar.Yields FourCountGrammar [d, a, C, B]
        [d, a, c, B] := by
    simpa [B, C, a, c, d] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.emitC [d, a] [B]
  have h10 :
      GeneralGrammar.Yields FourCountGrammar [d, a, c, B]
        [d, a, c, b] := by
    simpa [B, a, b, c, d] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.emitB [d, a, c] []
  have hderives :
      GeneralGrammar.Derives FourCountGrammar [S] [d, a, c, b] :=
    GeneralGrammar.Derives.step h1
      (GeneralGrammar.Derives.step h2
        (GeneralGrammar.Derives.step h3
          (GeneralGrammar.Derives.step h4
            (GeneralGrammar.Derives.step h5
              (GeneralGrammar.Derives.step h6
                (GeneralGrammar.Derives.step h7
                  (GeneralGrammar.Derives.step h8
                    (GeneralGrammar.Derives.step h9
                      (GeneralGrammar.Derives.step h10
                        (GeneralGrammar.Derives.refl [d, a, c, b]))))))))))
  simpa [GeneralGrammar.GeneratedLanguage, FourCountGrammar, dacbWord,
    SententialForm.terminalWord, S, a, b, c, d] using hderives

inductive OrderedABCNT where
  | start
  | markA
  | markB
  | markC
  | x
  | y
  | z
deriving DecidableEq

namespace OrderedABCNT

def finite : Foundation.FiniteType OrderedABCNT where
  elems := [start, markA, markB, markC, x, y, z]
  complete := by
    intro A
    cases A <;> simp

end OrderedABCNT

def orderedN (A : OrderedABCNT) :
    Symbol EqualCountTerminal OrderedABCNT :=
  ggNonterminal A

def orderedT (tok : EqualCountTerminal) :
    Symbol EqualCountTerminal OrderedABCNT :=
  ggTerminal tok

inductive OrderedABCProduces :
    SententialForm EqualCountTerminal OrderedABCNT ->
      SententialForm EqualCountTerminal OrderedABCNT -> Prop where
  | grow :
      OrderedABCProduces [orderedN OrderedABCNT.start]
        [orderedN OrderedABCNT.start, orderedN OrderedABCNT.markA,
          orderedN OrderedABCNT.markB, orderedN OrderedABCNT.markC]
  | startX :
      OrderedABCProduces [orderedN OrderedABCNT.start] [orderedN OrderedABCNT.x]
  | swapBA :
      OrderedABCProduces [orderedN OrderedABCNT.markB, orderedN OrderedABCNT.markA]
        [orderedN OrderedABCNT.markA, orderedN OrderedABCNT.markB]
  | swapCA :
      OrderedABCProduces [orderedN OrderedABCNT.markC, orderedN OrderedABCNT.markA]
        [orderedN OrderedABCNT.markA, orderedN OrderedABCNT.markC]
  | swapCB :
      OrderedABCProduces [orderedN OrderedABCNT.markC, orderedN OrderedABCNT.markB]
        [orderedN OrderedABCNT.markB, orderedN OrderedABCNT.markC]
  | convertXA :
      OrderedABCProduces [orderedN OrderedABCNT.x, orderedN OrderedABCNT.markA]
        [orderedT EqualCountTerminal.a, orderedN OrderedABCNT.x]
  | xToY :
      OrderedABCProduces [orderedN OrderedABCNT.x] [orderedN OrderedABCNT.y]
  | convertYB :
      OrderedABCProduces [orderedN OrderedABCNT.y, orderedN OrderedABCNT.markB]
        [orderedT EqualCountTerminal.b, orderedN OrderedABCNT.y]
  | yToZ :
      OrderedABCProduces [orderedN OrderedABCNT.y] [orderedN OrderedABCNT.z]
  | convertZC :
      OrderedABCProduces [orderedN OrderedABCNT.z, orderedN OrderedABCNT.markC]
        [orderedT EqualCountTerminal.c, orderedN OrderedABCNT.z]
  | finish :
      OrderedABCProduces [orderedN OrderedABCNT.z] []

def OrderedABCGrammar :
    GeneralGrammar EqualCountTerminal OrderedABCNT where
  start := OrderedABCNT.start
  produces := OrderedABCProduces
  lhsContainsNonterminal := by
    intro lhs rhs h
    cases h <;> simp [SententialForm.containsNonterminal, orderedN,
      ggNonterminal]
  nonterminalsFinite := OrderedABCNT.finite

def OrderedABCProductionList :
    List (GeneralGrammar.Production EqualCountTerminal OrderedABCNT) :=
  [{ lhs := [orderedN OrderedABCNT.start],
     rhs := [orderedN OrderedABCNT.start, orderedN OrderedABCNT.markA,
       orderedN OrderedABCNT.markB, orderedN OrderedABCNT.markC] },
   { lhs := [orderedN OrderedABCNT.start],
     rhs := [orderedN OrderedABCNT.x] },
   { lhs := [orderedN OrderedABCNT.markB, orderedN OrderedABCNT.markA],
     rhs := [orderedN OrderedABCNT.markA, orderedN OrderedABCNT.markB] },
   { lhs := [orderedN OrderedABCNT.markC, orderedN OrderedABCNT.markA],
     rhs := [orderedN OrderedABCNT.markA, orderedN OrderedABCNT.markC] },
   { lhs := [orderedN OrderedABCNT.markC, orderedN OrderedABCNT.markB],
     rhs := [orderedN OrderedABCNT.markB, orderedN OrderedABCNT.markC] },
   { lhs := [orderedN OrderedABCNT.x, orderedN OrderedABCNT.markA],
     rhs := [orderedT EqualCountTerminal.a, orderedN OrderedABCNT.x] },
   { lhs := [orderedN OrderedABCNT.x],
     rhs := [orderedN OrderedABCNT.y] },
   { lhs := [orderedN OrderedABCNT.y, orderedN OrderedABCNT.markB],
     rhs := [orderedT EqualCountTerminal.b, orderedN OrderedABCNT.y] },
   { lhs := [orderedN OrderedABCNT.y],
     rhs := [orderedN OrderedABCNT.z] },
   { lhs := [orderedN OrderedABCNT.z, orderedN OrderedABCNT.markC],
     rhs := [orderedT EqualCountTerminal.c, orderedN OrderedABCNT.z] },
   { lhs := [orderedN OrderedABCNT.z],
     rhs := [] }]

-- Book: Chapter 4, Section 4.6, the ordered a^n b^n c^n example grammar has
-- a finite production presentation.
theorem orderedABCGrammar_has_finite_productions :
    GeneralGrammar.HasFiniteProductions OrderedABCGrammar := by
  exists OrderedABCProductionList
  intro lhs rhs
  constructor
  · intro h
    cases h <;> simp [OrderedABCProductionList]
  · intro h
    rcases h with ⟨rule, hmem, hlhs, hrhs⟩
    simp [OrderedABCProductionList] at hmem
    rcases hmem with
      hrule | hrule | hrule | hrule | hrule | hrule |
      hrule | hrule | hrule | hrule | hrule
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.grow
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.startX
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.swapBA
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.swapCA
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.swapCB
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.convertXA
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.xToY
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.convertYB
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.yToZ
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.convertZC
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.finish

-- Book: Chapter 4, Section 4.6, the language generated by the ordered sample
-- grammar is generated by a finite general grammar.
theorem orderedABCGrammar_finite_production_generated :
    FiniteProductionGeneralLanguage
      (GeneralGrammar.GeneratedLanguage OrderedABCGrammar) := by
  exists OrderedABCNT
  exists OrderedABCGrammar
  constructor
  · exact orderedABCGrammar_has_finite_productions
  · intro w
    rfl

def orderedABCTotalA (sf : SententialForm EqualCountTerminal OrderedABCNT) :
    Nat :=
  SententialCountTerminal EqualCountTerminal.a sf +
    SententialCountNonterminal OrderedABCNT.markA sf

def orderedABCTotalB (sf : SententialForm EqualCountTerminal OrderedABCNT) :
    Nat :=
  SententialCountTerminal EqualCountTerminal.b sf +
    SententialCountNonterminal OrderedABCNT.markB sf

def orderedABCTotalC (sf : SententialForm EqualCountTerminal OrderedABCNT) :
    Nat :=
  SententialCountTerminal EqualCountTerminal.c sf +
    SententialCountNonterminal OrderedABCNT.markC sf

def orderedABCBalanced
    (sf : SententialForm EqualCountTerminal OrderedABCNT) : Prop :=
  orderedABCTotalA sf = orderedABCTotalB sf ∧
    orderedABCTotalB sf = orderedABCTotalC sf

theorem orderedABC_start_balanced :
    orderedABCBalanced [orderedN OrderedABCNT.start] := by
  simp [orderedABCBalanced, orderedABCTotalA, orderedABCTotalB,
    orderedABCTotalC, SententialCountTerminal, SententialCountNonterminal,
    orderedN, ggNonterminal]

theorem orderedABC_yields_preserves_balanced
    {x y : SententialForm EqualCountTerminal OrderedABCNT}
    (h : GeneralGrammar.Yields OrderedABCGrammar x y) :
    orderedABCBalanced x -> orderedABCBalanced y := by
  intro hbalanced
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro lhs hlhs =>
              cases hlhs with
              | intro rhs hrhs =>
                  cases hrhs with
                  | intro hprod hrest =>
                      cases hrest with
                      | intro hx hy =>
                          rw [hx] at hbalanced
                          rw [hy]
                          cases hprod <;>
                            simp [orderedABCBalanced, orderedABCTotalA,
                              orderedABCTotalB, orderedABCTotalC,
                              sententialCountTerminal_append,
                              sententialCountNonterminal_append,
                              SententialCountTerminal,
                              SententialCountNonterminal, orderedN,
                              orderedT, ggNonterminal, ggTerminal] at hbalanced ⊢ <;>
                            omega

theorem orderedABC_derives_preserves_balanced
    {x y : SententialForm EqualCountTerminal OrderedABCNT}
    (h : GeneralGrammar.Derives OrderedABCGrammar x y) :
    orderedABCBalanced x -> orderedABCBalanced y := by
  induction h with
  | refl _ =>
      intro hbalanced
      exact hbalanced
  | step hstep _ ih =>
      intro hbalanced
      exact ih (orderedABC_yields_preserves_balanced hstep hbalanced)

theorem orderedABCGrammar_generated_has_equal_terminal_counts
    {word : Word EqualCountTerminal}
    (h : word ∈ GeneralGrammar.GeneratedLanguage OrderedABCGrammar) :
    Word.Count EqualCountTerminal.a word =
        Word.Count EqualCountTerminal.b word ∧
      Word.Count EqualCountTerminal.b word =
        Word.Count EqualCountTerminal.c word := by
  have hderives :
      GeneralGrammar.Derives OrderedABCGrammar [orderedN OrderedABCNT.start]
        (SententialForm.terminalWord word) := by
    simpa [GeneralGrammar.GeneratedLanguage, OrderedABCGrammar, orderedN,
      ggNonterminal] using h
  have hbalanced :=
    orderedABC_derives_preserves_balanced hderives
      orderedABC_start_balanced
  simpa [orderedABCBalanced, orderedABCTotalA, orderedABCTotalB,
    orderedABCTotalC, sententialCountTerminal_terminalWord,
    sententialCountNonterminal_terminalWord] using hbalanced

def orderedABCBlockWord (n : Nat) : Word EqualCountTerminal :=
  Word.Concat (Word.RepeatSymbol EqualCountTerminal.a n)
    (Word.Concat (Word.RepeatSymbol EqualCountTerminal.b n)
      (Word.RepeatSymbol EqualCountTerminal.c n))

def orderedABCLanguage : Language EqualCountTerminal :=
  fun word => exists n, word = orderedABCBlockWord n

def orderedABCAForm (n : Nat) :
    SententialForm EqualCountTerminal OrderedABCNT :=
  List.replicate n (orderedN OrderedABCNT.markA)

def orderedABCBForm (n : Nat) :
    SententialForm EqualCountTerminal OrderedABCNT :=
  List.replicate n (orderedN OrderedABCNT.markB)

def orderedABCCForm (n : Nat) :
    SententialForm EqualCountTerminal OrderedABCNT :=
  List.replicate n (orderedN OrderedABCNT.markC)

def orderedABCMarkerBlock :
    SententialForm EqualCountTerminal OrderedABCNT :=
  [orderedN OrderedABCNT.markA, orderedN OrderedABCNT.markB,
    orderedN OrderedABCNT.markC]

def orderedABCRepeatedMarkers (n : Nat) :
    SententialForm EqualCountTerminal OrderedABCNT :=
  Word.RepeatWord orderedABCMarkerBlock n

def orderedABCSortedMarkers (n : Nat) :
    SententialForm EqualCountTerminal OrderedABCNT :=
  orderedABCAForm n ++ orderedABCBForm n ++ orderedABCCForm n

theorem orderedABC_moveC_right_over_as
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal OrderedABCNT) :
    GeneralGrammar.Derives OrderedABCGrammar
      (pre ++ [orderedN OrderedABCNT.markC] ++
        orderedABCAForm n ++ suffix)
      (pre ++ orderedABCAForm n ++ [orderedN OrderedABCNT.markC] ++
        suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [orderedABCAForm] using
        (GeneralGrammar.Derives.refl (G := OrderedABCGrammar)
          (pre ++ [orderedN OrderedABCNT.markC] ++ suffix))
  | succ n ih =>
      let A := orderedN OrderedABCNT.markA
      let C := orderedN OrderedABCNT.markC
      have hstep :
          GeneralGrammar.Yields OrderedABCGrammar
            (pre ++ [C, A] ++ orderedABCAForm n ++ suffix)
            (pre ++ [A, C] ++ orderedABCAForm n ++ suffix) := by
        simpa [A, C, List.append_assoc] using
          general_yields_of_production (G := OrderedABCGrammar)
            OrderedABCProduces.swapCA pre
            (orderedABCAForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives OrderedABCGrammar
            (pre ++ [A, C] ++ orderedABCAForm n ++ suffix)
            (pre ++ [A] ++ orderedABCAForm n ++ [C] ++ suffix) := by
        simpa [A, C, List.append_assoc] using ih (pre ++ [A])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [orderedABCAForm, A, C, List.append_assoc] using hall

theorem orderedABC_moveB_right_over_as
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal OrderedABCNT) :
    GeneralGrammar.Derives OrderedABCGrammar
      (pre ++ [orderedN OrderedABCNT.markB] ++
        orderedABCAForm n ++ suffix)
      (pre ++ orderedABCAForm n ++ [orderedN OrderedABCNT.markB] ++
        suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [orderedABCAForm] using
        (GeneralGrammar.Derives.refl (G := OrderedABCGrammar)
          (pre ++ [orderedN OrderedABCNT.markB] ++ suffix))
  | succ n ih =>
      let A := orderedN OrderedABCNT.markA
      let B := orderedN OrderedABCNT.markB
      have hstep :
          GeneralGrammar.Yields OrderedABCGrammar
            (pre ++ [B, A] ++ orderedABCAForm n ++ suffix)
            (pre ++ [A, B] ++ orderedABCAForm n ++ suffix) := by
        simpa [A, B, List.append_assoc] using
          general_yields_of_production (G := OrderedABCGrammar)
            OrderedABCProduces.swapBA pre
            (orderedABCAForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives OrderedABCGrammar
            (pre ++ [A, B] ++ orderedABCAForm n ++ suffix)
            (pre ++ [A] ++ orderedABCAForm n ++ [B] ++ suffix) := by
        simpa [A, B, List.append_assoc] using ih (pre ++ [A])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [orderedABCAForm, A, B, List.append_assoc] using hall

theorem orderedABC_moveC_right_over_bs
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal OrderedABCNT) :
    GeneralGrammar.Derives OrderedABCGrammar
      (pre ++ [orderedN OrderedABCNT.markC] ++
        orderedABCBForm n ++ suffix)
      (pre ++ orderedABCBForm n ++ [orderedN OrderedABCNT.markC] ++
        suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [orderedABCBForm] using
        (GeneralGrammar.Derives.refl (G := OrderedABCGrammar)
          (pre ++ [orderedN OrderedABCNT.markC] ++ suffix))
  | succ n ih =>
      let B := orderedN OrderedABCNT.markB
      let C := orderedN OrderedABCNT.markC
      have hstep :
          GeneralGrammar.Yields OrderedABCGrammar
            (pre ++ [C, B] ++ orderedABCBForm n ++ suffix)
            (pre ++ [B, C] ++ orderedABCBForm n ++ suffix) := by
        simpa [B, C, List.append_assoc] using
          general_yields_of_production (G := OrderedABCGrammar)
            OrderedABCProduces.swapCB pre
            (orderedABCBForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives OrderedABCGrammar
            (pre ++ [B, C] ++ orderedABCBForm n ++ suffix)
            (pre ++ [B] ++ orderedABCBForm n ++ [C] ++ suffix) := by
        simpa [B, C, List.append_assoc] using ih (pre ++ [B])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [orderedABCBForm, B, C, List.append_assoc] using hall

theorem orderedABC_sort_markers_derives (n : Nat) :
    GeneralGrammar.Derives OrderedABCGrammar
      (orderedABCRepeatedMarkers n) (orderedABCSortedMarkers n) := by
  induction n with
  | zero =>
      exact GeneralGrammar.Derives.refl []
  | succ n ih =>
      let A := orderedN OrderedABCNT.markA
      let B := orderedN OrderedABCNT.markB
      let C := orderedN OrderedABCNT.markC
      have hsortTail :
          GeneralGrammar.Derives OrderedABCGrammar
            (orderedABCMarkerBlock ++ orderedABCRepeatedMarkers n)
            (orderedABCMarkerBlock ++ orderedABCSortedMarkers n) := by
        simpa [orderedABCMarkerBlock, A, B, C, List.append_assoc] using
          general_derives_context ih orderedABCMarkerBlock []
      have hmoveCAs :
          GeneralGrammar.Derives OrderedABCGrammar
            (orderedABCMarkerBlock ++ orderedABCSortedMarkers n)
            ([A, B] ++ orderedABCAForm n ++ [C] ++
              orderedABCBForm n ++ orderedABCCForm n) := by
        simpa [orderedABCMarkerBlock, orderedABCSortedMarkers, A, B, C,
          List.append_assoc] using
          orderedABC_moveC_right_over_as n [A, B]
            (orderedABCBForm n ++ orderedABCCForm n)
      have hmoveBAs :
          GeneralGrammar.Derives OrderedABCGrammar
            ([A, B] ++ orderedABCAForm n ++ [C] ++
              orderedABCBForm n ++ orderedABCCForm n)
            ([A] ++ orderedABCAForm n ++ [B, C] ++
              orderedABCBForm n ++ orderedABCCForm n) := by
        simpa [A, B, C, List.append_assoc] using
          orderedABC_moveB_right_over_as n [A]
            ([C] ++ orderedABCBForm n ++ orderedABCCForm n)
      have hmoveCBs :
          GeneralGrammar.Derives OrderedABCGrammar
            ([A] ++ orderedABCAForm n ++ [B, C] ++
              orderedABCBForm n ++ orderedABCCForm n)
            (orderedABCSortedMarkers (n + 1)) := by
        simpa [orderedABCSortedMarkers, orderedABCAForm, orderedABCBForm,
          orderedABCCForm, A, B, C, List.append_assoc] using
          orderedABC_moveC_right_over_bs n
            ([A] ++ orderedABCAForm n ++ [B]) (orderedABCCForm n)
      exact GeneralGrammar.derives_trans hsortTail
        (GeneralGrammar.derives_trans hmoveCAs
          (GeneralGrammar.derives_trans hmoveBAs hmoveCBs))

theorem orderedABC_grow_repeated_markers_derives (n : Nat) :
    GeneralGrammar.Derives OrderedABCGrammar [orderedN OrderedABCNT.start]
      ([orderedN OrderedABCNT.start] ++ orderedABCRepeatedMarkers n) := by
  induction n with
  | zero =>
      simpa [orderedABCRepeatedMarkers, Word.RepeatWord] using
        (GeneralGrammar.Derives.refl (G := OrderedABCGrammar)
          [orderedN OrderedABCNT.start])
  | succ n ih =>
      have hstep :
          GeneralGrammar.Yields OrderedABCGrammar
            ([orderedN OrderedABCNT.start] ++ orderedABCRepeatedMarkers n)
            ([orderedN OrderedABCNT.start] ++ orderedABCMarkerBlock ++
              orderedABCRepeatedMarkers n) := by
        simpa [orderedABCMarkerBlock, List.append_assoc] using
          general_yields_of_production (G := OrderedABCGrammar)
            OrderedABCProduces.grow [] (orderedABCRepeatedMarkers n)
      have hall := GeneralGrammar.derives_trans ih
        (GeneralGrammar.yields_derives hstep)
      simpa [orderedABCRepeatedMarkers, orderedABCMarkerBlock,
        Word.RepeatWord, List.append_assoc] using hall

theorem orderedABC_start_to_repeated_markers_derives (n : Nat) :
    GeneralGrammar.Derives OrderedABCGrammar [orderedN OrderedABCNT.start]
      ([orderedN OrderedABCNT.x] ++ orderedABCRepeatedMarkers n) := by
  have hgrow := orderedABC_grow_repeated_markers_derives n
  have hstep :
      GeneralGrammar.Yields OrderedABCGrammar
        ([orderedN OrderedABCNT.start] ++ orderedABCRepeatedMarkers n)
        ([orderedN OrderedABCNT.x] ++ orderedABCRepeatedMarkers n) := by
    simpa [List.append_assoc] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.startX [] (orderedABCRepeatedMarkers n)
  exact GeneralGrammar.derives_trans hgrow
    (GeneralGrammar.yields_derives hstep)

theorem orderedABC_convert_x_as_derives
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal OrderedABCNT) :
    GeneralGrammar.Derives OrderedABCGrammar
      (pre ++ [orderedN OrderedABCNT.x] ++ orderedABCAForm n ++ suffix)
      (pre ++
        SententialForm.terminalWord
          (Word.RepeatSymbol EqualCountTerminal.a n) ++
        [orderedN OrderedABCNT.x] ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [orderedABCAForm, Word.RepeatSymbol,
        SententialForm.terminalWord, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := OrderedABCGrammar)
          (pre ++ [orderedN OrderedABCNT.x] ++ suffix))
  | succ n ih =>
      let X := orderedN OrderedABCNT.x
      let A := orderedN OrderedABCNT.markA
      let a := orderedT EqualCountTerminal.a
      have hstep :
          GeneralGrammar.Yields OrderedABCGrammar
            (pre ++ [X, A] ++ orderedABCAForm n ++ suffix)
            (pre ++ [a, X] ++ orderedABCAForm n ++ suffix) := by
        simpa [X, A, a, List.append_assoc] using
          general_yields_of_production (G := OrderedABCGrammar)
            OrderedABCProduces.convertXA pre (orderedABCAForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives OrderedABCGrammar
            (pre ++ [a, X] ++ orderedABCAForm n ++ suffix)
            (pre ++ [a] ++
              SententialForm.terminalWord
                (Word.RepeatSymbol EqualCountTerminal.a n) ++
              [X] ++ suffix) := by
        simpa [X, a, List.append_assoc] using ih (pre ++ [a])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [orderedABCAForm, X, A, a, Word.RepeatSymbol,
        SententialForm.terminalWord, List.append_assoc] using hall

theorem orderedABC_convert_y_bs_derives
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal OrderedABCNT) :
    GeneralGrammar.Derives OrderedABCGrammar
      (pre ++ [orderedN OrderedABCNT.y] ++ orderedABCBForm n ++ suffix)
      (pre ++
        SententialForm.terminalWord
          (Word.RepeatSymbol EqualCountTerminal.b n) ++
        [orderedN OrderedABCNT.y] ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [orderedABCBForm, Word.RepeatSymbol,
        SententialForm.terminalWord, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := OrderedABCGrammar)
          (pre ++ [orderedN OrderedABCNT.y] ++ suffix))
  | succ n ih =>
      let Y := orderedN OrderedABCNT.y
      let B := orderedN OrderedABCNT.markB
      let b := orderedT EqualCountTerminal.b
      have hstep :
          GeneralGrammar.Yields OrderedABCGrammar
            (pre ++ [Y, B] ++ orderedABCBForm n ++ suffix)
            (pre ++ [b, Y] ++ orderedABCBForm n ++ suffix) := by
        simpa [Y, B, b, List.append_assoc] using
          general_yields_of_production (G := OrderedABCGrammar)
            OrderedABCProduces.convertYB pre (orderedABCBForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives OrderedABCGrammar
            (pre ++ [b, Y] ++ orderedABCBForm n ++ suffix)
            (pre ++ [b] ++
              SententialForm.terminalWord
                (Word.RepeatSymbol EqualCountTerminal.b n) ++
              [Y] ++ suffix) := by
        simpa [Y, b, List.append_assoc] using ih (pre ++ [b])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [orderedABCBForm, Y, B, b, Word.RepeatSymbol,
        SententialForm.terminalWord, List.append_assoc] using hall

theorem orderedABC_convert_z_cs_derives
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal OrderedABCNT) :
    GeneralGrammar.Derives OrderedABCGrammar
      (pre ++ [orderedN OrderedABCNT.z] ++ orderedABCCForm n ++ suffix)
      (pre ++
        SententialForm.terminalWord
          (Word.RepeatSymbol EqualCountTerminal.c n) ++
        [orderedN OrderedABCNT.z] ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [orderedABCCForm, Word.RepeatSymbol,
        SententialForm.terminalWord, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := OrderedABCGrammar)
          (pre ++ [orderedN OrderedABCNT.z] ++ suffix))
  | succ n ih =>
      let Z := orderedN OrderedABCNT.z
      let C := orderedN OrderedABCNT.markC
      let c := orderedT EqualCountTerminal.c
      have hstep :
          GeneralGrammar.Yields OrderedABCGrammar
            (pre ++ [Z, C] ++ orderedABCCForm n ++ suffix)
            (pre ++ [c, Z] ++ orderedABCCForm n ++ suffix) := by
        simpa [Z, C, c, List.append_assoc] using
          general_yields_of_production (G := OrderedABCGrammar)
            OrderedABCProduces.convertZC pre (orderedABCCForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives OrderedABCGrammar
            (pre ++ [c, Z] ++ orderedABCCForm n ++ suffix)
            (pre ++ [c] ++
              SententialForm.terminalWord
                (Word.RepeatSymbol EqualCountTerminal.c n) ++
              [Z] ++ suffix) := by
        simpa [Z, c, List.append_assoc] using ih (pre ++ [c])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [orderedABCCForm, Z, C, c, Word.RepeatSymbol,
        SententialForm.terminalWord, List.append_assoc] using hall

theorem orderedABC_sorted_markers_to_word_derives (n : Nat) :
    GeneralGrammar.Derives OrderedABCGrammar
      ([orderedN OrderedABCNT.x] ++ orderedABCSortedMarkers n)
      (SententialForm.terminalWord (orderedABCBlockWord n)) := by
  let X := orderedN OrderedABCNT.x
  let Y := orderedN OrderedABCNT.y
  let Z := orderedN OrderedABCNT.z
  let aWord : SententialForm EqualCountTerminal OrderedABCNT :=
    SententialForm.terminalWord (Word.RepeatSymbol EqualCountTerminal.a n)
  let bWord : SententialForm EqualCountTerminal OrderedABCNT :=
    SententialForm.terminalWord (Word.RepeatSymbol EqualCountTerminal.b n)
  let cWord : SententialForm EqualCountTerminal OrderedABCNT :=
    SententialForm.terminalWord (Word.RepeatSymbol EqualCountTerminal.c n)
  have hAs :
      GeneralGrammar.Derives OrderedABCGrammar
        ([X] ++ orderedABCSortedMarkers n)
        (aWord ++ [X] ++ orderedABCBForm n ++ orderedABCCForm n) := by
    simpa [orderedABCSortedMarkers, X, aWord, List.append_assoc] using
      orderedABC_convert_x_as_derives n []
        (orderedABCBForm n ++ orderedABCCForm n)
  have hXToY :
      GeneralGrammar.Derives OrderedABCGrammar
        (aWord ++ [X] ++ orderedABCBForm n ++ orderedABCCForm n)
        (aWord ++ [Y] ++ orderedABCBForm n ++ orderedABCCForm n) := by
    have hstep :
        GeneralGrammar.Yields OrderedABCGrammar
          (aWord ++ [X] ++ orderedABCBForm n ++ orderedABCCForm n)
          (aWord ++ [Y] ++ orderedABCBForm n ++ orderedABCCForm n) := by
      simpa [X, Y, List.append_assoc] using
        general_yields_of_production (G := OrderedABCGrammar)
          OrderedABCProduces.xToY aWord
          (orderedABCBForm n ++ orderedABCCForm n)
    exact GeneralGrammar.yields_derives hstep
  have hBs :
      GeneralGrammar.Derives OrderedABCGrammar
        (aWord ++ [Y] ++ orderedABCBForm n ++ orderedABCCForm n)
        (aWord ++ bWord ++ [Y] ++ orderedABCCForm n) := by
    simpa [Y, bWord, List.append_assoc] using
      orderedABC_convert_y_bs_derives n aWord (orderedABCCForm n)
  have hYToZ :
      GeneralGrammar.Derives OrderedABCGrammar
        (aWord ++ bWord ++ [Y] ++ orderedABCCForm n)
        (aWord ++ bWord ++ [Z] ++ orderedABCCForm n) := by
    have hstep :
        GeneralGrammar.Yields OrderedABCGrammar
          (aWord ++ bWord ++ [Y] ++ orderedABCCForm n)
          (aWord ++ bWord ++ [Z] ++ orderedABCCForm n) := by
      simpa [Y, Z, List.append_assoc] using
        general_yields_of_production (G := OrderedABCGrammar)
          OrderedABCProduces.yToZ (aWord ++ bWord) (orderedABCCForm n)
    exact GeneralGrammar.yields_derives hstep
  have hCs :
      GeneralGrammar.Derives OrderedABCGrammar
        (aWord ++ bWord ++ [Z] ++ orderedABCCForm n)
        (aWord ++ bWord ++ cWord ++ [Z]) := by
    simpa [Z, cWord, List.append_assoc] using
      orderedABC_convert_z_cs_derives n (aWord ++ bWord) []
  have hFinish :
      GeneralGrammar.Derives OrderedABCGrammar
        (aWord ++ bWord ++ cWord ++ [Z])
        (aWord ++ bWord ++ cWord) := by
    have hstep :
        GeneralGrammar.Yields OrderedABCGrammar
          (aWord ++ bWord ++ cWord ++ [Z])
          (aWord ++ bWord ++ cWord) := by
      simpa [Z, List.append_assoc] using
        general_yields_of_production (G := OrderedABCGrammar)
          OrderedABCProduces.finish (aWord ++ bWord ++ cWord) []
    exact GeneralGrammar.yields_derives hstep
  have hall := GeneralGrammar.derives_trans hAs
    (GeneralGrammar.derives_trans hXToY
      (GeneralGrammar.derives_trans hBs
        (GeneralGrammar.derives_trans hYToZ
          (GeneralGrammar.derives_trans hCs hFinish))))
  rw [orderedABCBlockWord, SententialForm.terminalWord_append,
    SententialForm.terminalWord_append]
  simpa [aWord, bWord, cWord, Word.Concat, List.append_assoc] using hall

theorem orderedABC_words_generated (n : Nat) :
    orderedABCBlockWord n ∈
      GeneralGrammar.GeneratedLanguage OrderedABCGrammar := by
  have hstart := orderedABC_start_to_repeated_markers_derives n
  have hsort :
      GeneralGrammar.Derives OrderedABCGrammar
        ([orderedN OrderedABCNT.x] ++ orderedABCRepeatedMarkers n)
        ([orderedN OrderedABCNT.x] ++ orderedABCSortedMarkers n) := by
    simpa [List.append_assoc] using
      general_derives_context (orderedABC_sort_markers_derives n)
        [orderedN OrderedABCNT.x] []
  have hconvert := orderedABC_sorted_markers_to_word_derives n
  have hall := GeneralGrammar.derives_trans hstart
    (GeneralGrammar.derives_trans hsort hconvert)
  simpa [GeneralGrammar.GeneratedLanguage, OrderedABCGrammar, orderedN,
    ggNonterminal] using hall

theorem orderedABC_language_subset_generated {word : Word EqualCountTerminal}
    (h : word ∈ orderedABCLanguage) :
    word ∈ GeneralGrammar.GeneratedLanguage OrderedABCGrammar := by
  rcases h with ⟨n, hword⟩
  rw [hword]
  exact orderedABC_words_generated n

def aabbccWord : Word EqualCountTerminal :=
  [EqualCountTerminal.a, EqualCountTerminal.a, EqualCountTerminal.b,
    EqualCountTerminal.b, EqualCountTerminal.c, EqualCountTerminal.c]

-- Book: Chapter 4, Section 4.6, the ordered general grammar generates
-- `aabbcc`, illustrating the `{a^n b^n c^n}` construction.
theorem orderedABCGrammar_generates_aabbcc :
    aabbccWord ∈ GeneralGrammar.GeneratedLanguage OrderedABCGrammar := by
  let S := orderedN OrderedABCNT.start
  let A := orderedN OrderedABCNT.markA
  let B := orderedN OrderedABCNT.markB
  let C := orderedN OrderedABCNT.markC
  let X := orderedN OrderedABCNT.x
  let Y := orderedN OrderedABCNT.y
  let Z := orderedN OrderedABCNT.z
  let a := orderedT EqualCountTerminal.a
  let b := orderedT EqualCountTerminal.b
  let c := orderedT EqualCountTerminal.c
  have h1 : GeneralGrammar.Yields OrderedABCGrammar [S] [S, A, B, C] := by
    simpa [S, A, B, C] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.grow [] []
  have h2 :
      GeneralGrammar.Yields OrderedABCGrammar [S, A, B, C]
        [S, A, B, C, A, B, C] := by
    simpa [S, A, B, C] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.grow [] [A, B, C]
  have h3 :
      GeneralGrammar.Yields OrderedABCGrammar [S, A, B, C, A, B, C]
        [X, A, B, C, A, B, C] := by
    simpa [S, A, B, C, X] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.startX [] [A, B, C, A, B, C]
  have h4 :
      GeneralGrammar.Yields OrderedABCGrammar [X, A, B, C, A, B, C]
        [X, A, B, A, C, B, C] := by
    simpa [X, A, B, C] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.swapCA [X, A, B] [B, C]
  have h5 :
      GeneralGrammar.Yields OrderedABCGrammar [X, A, B, A, C, B, C]
        [X, A, A, B, C, B, C] := by
    simpa [X, A, B, C] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.swapBA [X, A] [C, B, C]
  have h6 :
      GeneralGrammar.Yields OrderedABCGrammar [X, A, A, B, C, B, C]
        [X, A, A, B, B, C, C] := by
    simpa [X, A, B, C] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.swapCB [X, A, A, B] [C]
  have h7 :
      GeneralGrammar.Yields OrderedABCGrammar [X, A, A, B, B, C, C]
        [a, X, A, B, B, C, C] := by
    simpa [X, A, B, C, a] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.convertXA [] [A, B, B, C, C]
  have h8 :
      GeneralGrammar.Yields OrderedABCGrammar [a, X, A, B, B, C, C]
        [a, a, X, B, B, C, C] := by
    simpa [X, A, B, C, a] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.convertXA [a] [B, B, C, C]
  have h9 :
      GeneralGrammar.Yields OrderedABCGrammar [a, a, X, B, B, C, C]
        [a, a, Y, B, B, C, C] := by
    simpa [X, Y, B, C, a] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.xToY [a, a] [B, B, C, C]
  have h10 :
      GeneralGrammar.Yields OrderedABCGrammar [a, a, Y, B, B, C, C]
        [a, a, b, Y, B, C, C] := by
    simpa [Y, B, C, a, b] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.convertYB [a, a] [B, C, C]
  have h11 :
      GeneralGrammar.Yields OrderedABCGrammar [a, a, b, Y, B, C, C]
        [a, a, b, b, Y, C, C] := by
    simpa [Y, B, C, a, b] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.convertYB [a, a, b] [C, C]
  have h12 :
      GeneralGrammar.Yields OrderedABCGrammar [a, a, b, b, Y, C, C]
        [a, a, b, b, Z, C, C] := by
    simpa [Y, Z, C, a, b] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.yToZ [a, a, b, b] [C, C]
  have h13 :
      GeneralGrammar.Yields OrderedABCGrammar [a, a, b, b, Z, C, C]
        [a, a, b, b, c, Z, C] := by
    simpa [Z, C, a, b, c] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.convertZC [a, a, b, b] [C]
  have h14 :
      GeneralGrammar.Yields OrderedABCGrammar [a, a, b, b, c, Z, C]
        [a, a, b, b, c, c, Z] := by
    simpa [Z, C, a, b, c] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.convertZC [a, a, b, b, c] []
  have h15 :
      GeneralGrammar.Yields OrderedABCGrammar [a, a, b, b, c, c, Z]
        [a, a, b, b, c, c] := by
    simpa [Z, a, b, c] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.finish [a, a, b, b, c, c] []
  have hderives :
      GeneralGrammar.Derives OrderedABCGrammar [S] [a, a, b, b, c, c] :=
    GeneralGrammar.Derives.step h1
      (GeneralGrammar.Derives.step h2
        (GeneralGrammar.Derives.step h3
          (GeneralGrammar.Derives.step h4
            (GeneralGrammar.Derives.step h5
              (GeneralGrammar.Derives.step h6
                (GeneralGrammar.Derives.step h7
                  (GeneralGrammar.Derives.step h8
                    (GeneralGrammar.Derives.step h9
                      (GeneralGrammar.Derives.step h10
                        (GeneralGrammar.Derives.step h11
                          (GeneralGrammar.Derives.step h12
                            (GeneralGrammar.Derives.step h13
                              (GeneralGrammar.Derives.step h14
                                (GeneralGrammar.Derives.step h15
                                  (GeneralGrammar.Derives.refl
                                    [a, a, b, b, c, c])))))))))))))))
  simpa [GeneralGrammar.GeneratedLanguage, OrderedABCGrammar, aabbccWord,
    SententialForm.terminalWord, S, a, b, c] using hderives

inductive OrderedABCDNT where
  | start
  | markA
  | markB
  | markC
  | markD
  | x
  | y
  | z
  | q
deriving DecidableEq

namespace OrderedABCDNT

def finite : Foundation.FiniteType OrderedABCDNT where
  elems := [start, markA, markB, markC, markD, x, y, z, q]
  complete := by
    intro A
    cases A <;> simp

end OrderedABCDNT

def ordered4N (A : OrderedABCDNT) :
    Symbol FourCountTerminal OrderedABCDNT :=
  ggNonterminal A

def ordered4T (tok : FourCountTerminal) :
    Symbol FourCountTerminal OrderedABCDNT :=
  ggTerminal tok

inductive OrderedABCDProduces :
    SententialForm FourCountTerminal OrderedABCDNT ->
      SententialForm FourCountTerminal OrderedABCDNT -> Prop where
  | grow :
      OrderedABCDProduces [ordered4N OrderedABCDNT.start]
        [ordered4N OrderedABCDNT.start, ordered4N OrderedABCDNT.markA,
          ordered4N OrderedABCDNT.markB, ordered4N OrderedABCDNT.markC,
          ordered4N OrderedABCDNT.markD]
  | startX :
      OrderedABCDProduces [ordered4N OrderedABCDNT.start]
        [ordered4N OrderedABCDNT.x]
  | swapBA :
      OrderedABCDProduces
        [ordered4N OrderedABCDNT.markB, ordered4N OrderedABCDNT.markA]
        [ordered4N OrderedABCDNT.markA, ordered4N OrderedABCDNT.markB]
  | swapCA :
      OrderedABCDProduces
        [ordered4N OrderedABCDNT.markC, ordered4N OrderedABCDNT.markA]
        [ordered4N OrderedABCDNT.markA, ordered4N OrderedABCDNT.markC]
  | swapDA :
      OrderedABCDProduces
        [ordered4N OrderedABCDNT.markD, ordered4N OrderedABCDNT.markA]
        [ordered4N OrderedABCDNT.markA, ordered4N OrderedABCDNT.markD]
  | swapCB :
      OrderedABCDProduces
        [ordered4N OrderedABCDNT.markC, ordered4N OrderedABCDNT.markB]
        [ordered4N OrderedABCDNT.markB, ordered4N OrderedABCDNT.markC]
  | swapDB :
      OrderedABCDProduces
        [ordered4N OrderedABCDNT.markD, ordered4N OrderedABCDNT.markB]
        [ordered4N OrderedABCDNT.markB, ordered4N OrderedABCDNT.markD]
  | swapDC :
      OrderedABCDProduces
        [ordered4N OrderedABCDNT.markD, ordered4N OrderedABCDNT.markC]
        [ordered4N OrderedABCDNT.markC, ordered4N OrderedABCDNT.markD]
  | convertXA :
      OrderedABCDProduces
        [ordered4N OrderedABCDNT.x, ordered4N OrderedABCDNT.markA]
        [ordered4T FourCountTerminal.a, ordered4N OrderedABCDNT.x]
  | xToY :
      OrderedABCDProduces [ordered4N OrderedABCDNT.x]
        [ordered4N OrderedABCDNT.y]
  | convertYB :
      OrderedABCDProduces
        [ordered4N OrderedABCDNT.y, ordered4N OrderedABCDNT.markB]
        [ordered4T FourCountTerminal.b, ordered4N OrderedABCDNT.y]
  | yToZ :
      OrderedABCDProduces [ordered4N OrderedABCDNT.y]
        [ordered4N OrderedABCDNT.z]
  | convertZC :
      OrderedABCDProduces
        [ordered4N OrderedABCDNT.z, ordered4N OrderedABCDNT.markC]
        [ordered4T FourCountTerminal.c, ordered4N OrderedABCDNT.z]
  | zToQ :
      OrderedABCDProduces [ordered4N OrderedABCDNT.z]
        [ordered4N OrderedABCDNT.q]
  | convertQD :
      OrderedABCDProduces
        [ordered4N OrderedABCDNT.q, ordered4N OrderedABCDNT.markD]
        [ordered4T FourCountTerminal.d, ordered4N OrderedABCDNT.q]
  | finish :
      OrderedABCDProduces [ordered4N OrderedABCDNT.q] []

def OrderedABCDGrammar :
    GeneralGrammar FourCountTerminal OrderedABCDNT where
  start := OrderedABCDNT.start
  produces := OrderedABCDProduces
  lhsContainsNonterminal := by
    intro lhs rhs h
    cases h <;> simp [SententialForm.containsNonterminal, ordered4N,
      ggNonterminal]
  nonterminalsFinite := OrderedABCDNT.finite

def OrderedABCDProductionList :
    List (GeneralGrammar.Production FourCountTerminal OrderedABCDNT) :=
  [{ lhs := [ordered4N OrderedABCDNT.start],
     rhs := [ordered4N OrderedABCDNT.start, ordered4N OrderedABCDNT.markA,
       ordered4N OrderedABCDNT.markB, ordered4N OrderedABCDNT.markC,
       ordered4N OrderedABCDNT.markD] },
   { lhs := [ordered4N OrderedABCDNT.start],
     rhs := [ordered4N OrderedABCDNT.x] },
   { lhs := [ordered4N OrderedABCDNT.markB, ordered4N OrderedABCDNT.markA],
     rhs := [ordered4N OrderedABCDNT.markA, ordered4N OrderedABCDNT.markB] },
   { lhs := [ordered4N OrderedABCDNT.markC, ordered4N OrderedABCDNT.markA],
     rhs := [ordered4N OrderedABCDNT.markA, ordered4N OrderedABCDNT.markC] },
   { lhs := [ordered4N OrderedABCDNT.markD, ordered4N OrderedABCDNT.markA],
     rhs := [ordered4N OrderedABCDNT.markA, ordered4N OrderedABCDNT.markD] },
   { lhs := [ordered4N OrderedABCDNT.markC, ordered4N OrderedABCDNT.markB],
     rhs := [ordered4N OrderedABCDNT.markB, ordered4N OrderedABCDNT.markC] },
   { lhs := [ordered4N OrderedABCDNT.markD, ordered4N OrderedABCDNT.markB],
     rhs := [ordered4N OrderedABCDNT.markB, ordered4N OrderedABCDNT.markD] },
   { lhs := [ordered4N OrderedABCDNT.markD, ordered4N OrderedABCDNT.markC],
     rhs := [ordered4N OrderedABCDNT.markC, ordered4N OrderedABCDNT.markD] },
   { lhs := [ordered4N OrderedABCDNT.x, ordered4N OrderedABCDNT.markA],
     rhs := [ordered4T FourCountTerminal.a, ordered4N OrderedABCDNT.x] },
   { lhs := [ordered4N OrderedABCDNT.x],
     rhs := [ordered4N OrderedABCDNT.y] },
   { lhs := [ordered4N OrderedABCDNT.y, ordered4N OrderedABCDNT.markB],
     rhs := [ordered4T FourCountTerminal.b, ordered4N OrderedABCDNT.y] },
   { lhs := [ordered4N OrderedABCDNT.y],
     rhs := [ordered4N OrderedABCDNT.z] },
   { lhs := [ordered4N OrderedABCDNT.z, ordered4N OrderedABCDNT.markC],
     rhs := [ordered4T FourCountTerminal.c, ordered4N OrderedABCDNT.z] },
   { lhs := [ordered4N OrderedABCDNT.z],
     rhs := [ordered4N OrderedABCDNT.q] },
   { lhs := [ordered4N OrderedABCDNT.q, ordered4N OrderedABCDNT.markD],
     rhs := [ordered4T FourCountTerminal.d, ordered4N OrderedABCDNT.q] },
   { lhs := [ordered4N OrderedABCDNT.q],
     rhs := [] }]

-- Book: Chapter 4, Section 4.6, selected exercise grammar for ordered
-- `a^n b^n c^n d^n` words.
theorem orderedABCDGrammar_has_finite_productions :
    GeneralGrammar.HasFiniteProductions OrderedABCDGrammar := by
  exists OrderedABCDProductionList
  intro lhs rhs
  constructor
  · intro h
    cases h <;> simp [OrderedABCDProductionList]
  · intro h
    rcases h with ⟨rule, hmem, hlhs, hrhs⟩
    simp [OrderedABCDProductionList] at hmem
    rcases hmem with
      hrule | hrule | hrule | hrule | hrule | hrule |
      hrule | hrule | hrule | hrule | hrule | hrule |
      hrule | hrule | hrule | hrule
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.grow
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.startX
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.swapBA
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.swapCA
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.swapDA
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.swapCB
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.swapDB
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.swapDC
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.convertXA
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.xToY
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.convertYB
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.yToZ
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.convertZC
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.zToQ
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.convertQD
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.finish

-- Book: Chapter 4, Section 4.6, the ordered four-block exercise language is
-- generated by a finite unrestricted grammar.
theorem orderedABCDGrammar_finite_production_generated :
    FiniteProductionGeneralLanguage
      (GeneralGrammar.GeneratedLanguage OrderedABCDGrammar) := by
  exists OrderedABCDNT
  exists OrderedABCDGrammar
  constructor
  · exact orderedABCDGrammar_has_finite_productions
  · intro word
    rfl

def orderedABCDTotalA
    (sf : SententialForm FourCountTerminal OrderedABCDNT) : Nat :=
  SententialCountTerminal FourCountTerminal.a sf +
    SententialCountNonterminal OrderedABCDNT.markA sf

def orderedABCDTotalB
    (sf : SententialForm FourCountTerminal OrderedABCDNT) : Nat :=
  SententialCountTerminal FourCountTerminal.b sf +
    SententialCountNonterminal OrderedABCDNT.markB sf

def orderedABCDTotalC
    (sf : SententialForm FourCountTerminal OrderedABCDNT) : Nat :=
  SententialCountTerminal FourCountTerminal.c sf +
    SententialCountNonterminal OrderedABCDNT.markC sf

def orderedABCDTotalD
    (sf : SententialForm FourCountTerminal OrderedABCDNT) : Nat :=
  SententialCountTerminal FourCountTerminal.d sf +
    SententialCountNonterminal OrderedABCDNT.markD sf

def orderedABCDBalanced
    (sf : SententialForm FourCountTerminal OrderedABCDNT) : Prop :=
  orderedABCDTotalA sf = orderedABCDTotalB sf ∧
    orderedABCDTotalB sf = orderedABCDTotalC sf ∧
    orderedABCDTotalC sf = orderedABCDTotalD sf

theorem orderedABCD_start_balanced :
    orderedABCDBalanced [ordered4N OrderedABCDNT.start] := by
  simp [orderedABCDBalanced, orderedABCDTotalA, orderedABCDTotalB,
    orderedABCDTotalC, orderedABCDTotalD, SententialCountTerminal,
    SententialCountNonterminal, ordered4N, ggNonterminal]

theorem orderedABCD_yields_preserves_balanced
    {x y : SententialForm FourCountTerminal OrderedABCDNT}
    (h : GeneralGrammar.Yields OrderedABCDGrammar x y) :
    orderedABCDBalanced x -> orderedABCDBalanced y := by
  intro hbalanced
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro lhs hlhs =>
              cases hlhs with
              | intro rhs hrhs =>
                  cases hrhs with
                  | intro hprod hrest =>
                      cases hrest with
                      | intro hx hy =>
                          rw [hx] at hbalanced
                          rw [hy]
                          cases hprod <;>
                            simp [orderedABCDBalanced, orderedABCDTotalA,
                              orderedABCDTotalB, orderedABCDTotalC,
                              orderedABCDTotalD,
                              sententialCountTerminal_append,
                              sententialCountNonterminal_append,
                              SententialCountTerminal,
                              SententialCountNonterminal, ordered4N,
                              ordered4T, ggNonterminal, ggTerminal] at hbalanced ⊢ <;>
                            omega

theorem orderedABCD_derives_preserves_balanced
    {x y : SententialForm FourCountTerminal OrderedABCDNT}
    (h : GeneralGrammar.Derives OrderedABCDGrammar x y) :
    orderedABCDBalanced x -> orderedABCDBalanced y := by
  induction h with
  | refl _ =>
      intro hbalanced
      exact hbalanced
  | step hstep _ ih =>
      intro hbalanced
      exact ih (orderedABCD_yields_preserves_balanced hstep hbalanced)

theorem orderedABCDGrammar_generated_has_equal_terminal_counts
    {word : Word FourCountTerminal}
    (h : word ∈ GeneralGrammar.GeneratedLanguage OrderedABCDGrammar) :
    Word.Count FourCountTerminal.a word =
        Word.Count FourCountTerminal.b word ∧
      Word.Count FourCountTerminal.b word =
        Word.Count FourCountTerminal.c word ∧
      Word.Count FourCountTerminal.c word =
        Word.Count FourCountTerminal.d word := by
  have hderives :
      GeneralGrammar.Derives OrderedABCDGrammar
        [ordered4N OrderedABCDNT.start]
        (SententialForm.terminalWord word) := by
    simpa [GeneralGrammar.GeneratedLanguage, OrderedABCDGrammar, ordered4N,
      ggNonterminal] using h
  have hbalanced :=
    orderedABCD_derives_preserves_balanced hderives
      orderedABCD_start_balanced
  simpa [orderedABCDBalanced, orderedABCDTotalA, orderedABCDTotalB,
    orderedABCDTotalC, orderedABCDTotalD,
    sententialCountTerminal_terminalWord,
    sententialCountNonterminal_terminalWord] using hbalanced

def aabbccddWord : Word FourCountTerminal :=
  [FourCountTerminal.a, FourCountTerminal.a, FourCountTerminal.b,
    FourCountTerminal.b, FourCountTerminal.c, FourCountTerminal.c,
    FourCountTerminal.d, FourCountTerminal.d]

-- Book: Chapter 4, Section 4.6, concrete n = 2 derivation for the selected
-- ordered four-block exercise grammar.
theorem orderedABCDGrammar_generates_aabbccdd :
    aabbccddWord ∈ GeneralGrammar.GeneratedLanguage OrderedABCDGrammar := by
  let S := ordered4N OrderedABCDNT.start
  let A := ordered4N OrderedABCDNT.markA
  let B := ordered4N OrderedABCDNT.markB
  let C := ordered4N OrderedABCDNT.markC
  let D := ordered4N OrderedABCDNT.markD
  let X := ordered4N OrderedABCDNT.x
  let Y := ordered4N OrderedABCDNT.y
  let Z := ordered4N OrderedABCDNT.z
  let Q := ordered4N OrderedABCDNT.q
  let a := ordered4T FourCountTerminal.a
  let b := ordered4T FourCountTerminal.b
  let c := ordered4T FourCountTerminal.c
  let d := ordered4T FourCountTerminal.d
  have h1 : GeneralGrammar.Yields OrderedABCDGrammar [S]
      [S, A, B, C, D] := by
    simpa [S, A, B, C, D] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.grow [] []
  have h2 :
      GeneralGrammar.Yields OrderedABCDGrammar [S, A, B, C, D]
        [S, A, B, C, D, A, B, C, D] := by
    simpa [S, A, B, C, D] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.grow [] [A, B, C, D]
  have h3 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [S, A, B, C, D, A, B, C, D]
        [X, A, B, C, D, A, B, C, D] := by
    simpa [S, A, B, C, D, X] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.startX [] [A, B, C, D, A, B, C, D]
  have h4 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [X, A, B, C, D, A, B, C, D]
        [X, A, B, C, A, D, B, C, D] := by
    simpa [X, A, B, C, D] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.swapDA [X, A, B, C] [B, C, D]
  have h5 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [X, A, B, C, A, D, B, C, D]
        [X, A, B, A, C, D, B, C, D] := by
    simpa [X, A, B, C, D] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.swapCA [X, A, B] [D, B, C, D]
  have h6 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [X, A, B, A, C, D, B, C, D]
        [X, A, A, B, C, D, B, C, D] := by
    simpa [X, A, B, C, D] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.swapBA [X, A] [C, D, B, C, D]
  have h7 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [X, A, A, B, C, D, B, C, D]
        [X, A, A, B, C, B, D, C, D] := by
    simpa [X, A, B, C, D] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.swapDB [X, A, A, B, C] [C, D]
  have h8 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [X, A, A, B, C, B, D, C, D]
        [X, A, A, B, B, C, D, C, D] := by
    simpa [X, A, B, C, D] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.swapCB [X, A, A, B] [D, C, D]
  have h9 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [X, A, A, B, B, C, D, C, D]
        [X, A, A, B, B, C, C, D, D] := by
    simpa [X, A, B, C, D] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.swapDC [X, A, A, B, B, C] [D]
  have h10 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [X, A, A, B, B, C, C, D, D]
        [a, X, A, B, B, C, C, D, D] := by
    simpa [X, A, B, C, D, a] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.convertXA [] [A, B, B, C, C, D, D]
  have h11 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, X, A, B, B, C, C, D, D]
        [a, a, X, B, B, C, C, D, D] := by
    simpa [X, A, B, C, D, a] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.convertXA [a] [B, B, C, C, D, D]
  have h12 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, a, X, B, B, C, C, D, D]
        [a, a, Y, B, B, C, C, D, D] := by
    simpa [X, Y, B, C, D, a] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.xToY [a, a] [B, B, C, C, D, D]
  have h13 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, a, Y, B, B, C, C, D, D]
        [a, a, b, Y, B, C, C, D, D] := by
    simpa [Y, B, C, D, a, b] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.convertYB [a, a] [B, C, C, D, D]
  have h14 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, a, b, Y, B, C, C, D, D]
        [a, a, b, b, Y, C, C, D, D] := by
    simpa [Y, B, C, D, a, b] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.convertYB [a, a, b] [C, C, D, D]
  have h15 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, a, b, b, Y, C, C, D, D]
        [a, a, b, b, Z, C, C, D, D] := by
    simpa [Y, Z, C, D, a, b] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.yToZ [a, a, b, b] [C, C, D, D]
  have h16 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, a, b, b, Z, C, C, D, D]
        [a, a, b, b, c, Z, C, D, D] := by
    simpa [Z, C, D, a, b, c] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.convertZC [a, a, b, b] [C, D, D]
  have h17 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, a, b, b, c, Z, C, D, D]
        [a, a, b, b, c, c, Z, D, D] := by
    simpa [Z, C, D, a, b, c] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.convertZC [a, a, b, b, c] [D, D]
  have h18 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, a, b, b, c, c, Z, D, D]
        [a, a, b, b, c, c, Q, D, D] := by
    simpa [Z, Q, D, a, b, c] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.zToQ [a, a, b, b, c, c] [D, D]
  have h19 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, a, b, b, c, c, Q, D, D]
        [a, a, b, b, c, c, d, Q, D] := by
    simpa [Q, D, a, b, c, d] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.convertQD [a, a, b, b, c, c] [D]
  have h20 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, a, b, b, c, c, d, Q, D]
        [a, a, b, b, c, c, d, d, Q] := by
    simpa [Q, D, a, b, c, d] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.convertQD [a, a, b, b, c, c, d] []
  have h21 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, a, b, b, c, c, d, d, Q]
        [a, a, b, b, c, c, d, d] := by
    simpa [Q, a, b, c, d] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.finish [a, a, b, b, c, c, d, d] []
  have hderives :
      GeneralGrammar.Derives OrderedABCDGrammar [S]
        [a, a, b, b, c, c, d, d] :=
    GeneralGrammar.Derives.step h1
      (GeneralGrammar.Derives.step h2
        (GeneralGrammar.Derives.step h3
          (GeneralGrammar.Derives.step h4
            (GeneralGrammar.Derives.step h5
              (GeneralGrammar.Derives.step h6
                (GeneralGrammar.Derives.step h7
                  (GeneralGrammar.Derives.step h8
                    (GeneralGrammar.Derives.step h9
                      (GeneralGrammar.Derives.step h10
                        (GeneralGrammar.Derives.step h11
                          (GeneralGrammar.Derives.step h12
                            (GeneralGrammar.Derives.step h13
                              (GeneralGrammar.Derives.step h14
                                (GeneralGrammar.Derives.step h15
                                  (GeneralGrammar.Derives.step h16
                                    (GeneralGrammar.Derives.step h17
                                      (GeneralGrammar.Derives.step h18
                                        (GeneralGrammar.Derives.step h19
                                          (GeneralGrammar.Derives.step h20
                                            (GeneralGrammar.Derives.step h21
                                              (GeneralGrammar.Derives.refl
                                                [a, a, b, b, c, c, d,
                                                  d])))))))))))))))))))))
  simpa [GeneralGrammar.GeneratedLanguage, OrderedABCDGrammar, aabbccddWord,
    SententialForm.terminalWord, S, a, b, c, d] using hderives

inductive StrictMoreBNT where
  | start
  | tail
deriving DecidableEq

namespace StrictMoreBNT

def finite : Foundation.FiniteType StrictMoreBNT where
  elems := [start, tail]
  complete := by
    intro A
    cases A <;> simp

end StrictMoreBNT

def moreBN (A : StrictMoreBNT) :
    Symbol EqualCountTerminal StrictMoreBNT :=
  ggNonterminal A

def moreBT (tok : EqualCountTerminal) :
    Symbol EqualCountTerminal StrictMoreBNT :=
  ggTerminal tok

inductive StrictMoreBProduces :
    SententialForm EqualCountTerminal StrictMoreBNT ->
      SententialForm EqualCountTerminal StrictMoreBNT -> Prop where
  | wrapPair :
      StrictMoreBProduces [moreBN StrictMoreBNT.start]
        [moreBT EqualCountTerminal.a, moreBN StrictMoreBNT.start,
          moreBT EqualCountTerminal.b]
  | toTail :
      StrictMoreBProduces [moreBN StrictMoreBNT.start]
        [moreBN StrictMoreBNT.tail]
  | tailMore :
      StrictMoreBProduces [moreBN StrictMoreBNT.tail]
        [moreBT EqualCountTerminal.b, moreBN StrictMoreBNT.tail]
  | tailOne :
      StrictMoreBProduces [moreBN StrictMoreBNT.tail]
        [moreBT EqualCountTerminal.b]

def StrictMoreBGrammar :
    GeneralGrammar EqualCountTerminal StrictMoreBNT where
  start := StrictMoreBNT.start
  produces := StrictMoreBProduces
  lhsContainsNonterminal := by
    intro lhs rhs h
    cases h <;> simp [SententialForm.containsNonterminal, moreBN,
      ggNonterminal]
  nonterminalsFinite := StrictMoreBNT.finite

def StrictMoreBProductionList :
    List (GeneralGrammar.Production EqualCountTerminal StrictMoreBNT) :=
  [{ lhs := [moreBN StrictMoreBNT.start],
     rhs := [moreBT EqualCountTerminal.a, moreBN StrictMoreBNT.start,
       moreBT EqualCountTerminal.b] },
   { lhs := [moreBN StrictMoreBNT.start],
     rhs := [moreBN StrictMoreBNT.tail] },
   { lhs := [moreBN StrictMoreBNT.tail],
     rhs := [moreBT EqualCountTerminal.b, moreBN StrictMoreBNT.tail] },
   { lhs := [moreBN StrictMoreBNT.tail],
     rhs := [moreBT EqualCountTerminal.b] }]

-- Book: Chapter 4, Section 4.6, selected exercise grammar for ordered
-- strict-count words `a^n b^m` with `n < m`.
theorem strictMoreBGrammar_has_finite_productions :
    GeneralGrammar.HasFiniteProductions StrictMoreBGrammar := by
  exists StrictMoreBProductionList
  intro lhs rhs
  constructor
  · intro h
    cases h <;> simp [StrictMoreBProductionList]
  · intro h
    rcases h with ⟨rule, hmem, hlhs, hrhs⟩
    simp [StrictMoreBProductionList] at hmem
    rcases hmem with hrule | hrule | hrule | hrule
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictMoreBProduces.wrapPair
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictMoreBProduces.toTail
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictMoreBProduces.tailMore
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictMoreBProduces.tailOne

theorem strictMoreBGrammar_finite_production_generated :
    FiniteProductionGeneralLanguage
      (GeneralGrammar.GeneratedLanguage StrictMoreBGrammar) := by
  exists StrictMoreBNT
  exists StrictMoreBGrammar
  constructor
  · exact strictMoreBGrammar_has_finite_productions
  · intro word
    rfl

def strictMoreBCountA
    (sf : SententialForm EqualCountTerminal StrictMoreBNT) : Nat :=
  SententialCountTerminal EqualCountTerminal.a sf

def strictMoreBCountBWithCredits
    (sf : SententialForm EqualCountTerminal StrictMoreBNT) : Nat :=
  SententialCountTerminal EqualCountTerminal.b sf +
    SententialCountNonterminal StrictMoreBNT.start sf +
    SententialCountNonterminal StrictMoreBNT.tail sf

def strictMoreBMargin
    (sf : SententialForm EqualCountTerminal StrictMoreBNT) : Prop :=
  strictMoreBCountA sf < strictMoreBCountBWithCredits sf

theorem strictMoreB_start_margin :
    strictMoreBMargin [moreBN StrictMoreBNT.start] := by
  simp [strictMoreBMargin, strictMoreBCountA,
    strictMoreBCountBWithCredits, SententialCountTerminal,
    SententialCountNonterminal, moreBN, ggNonterminal]

theorem strictMoreB_yields_preserves_margin
    {x y : SententialForm EqualCountTerminal StrictMoreBNT}
    (h : GeneralGrammar.Yields StrictMoreBGrammar x y) :
    strictMoreBMargin x -> strictMoreBMargin y := by
  intro hmargin
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro lhs hlhs =>
              cases hlhs with
              | intro rhs hrhs =>
                  cases hrhs with
                  | intro hprod hrest =>
                      cases hrest with
                      | intro hx hy =>
                          rw [hx] at hmargin
                          rw [hy]
                          cases hprod <;>
                            simp [strictMoreBMargin, strictMoreBCountA,
                              strictMoreBCountBWithCredits,
                              sententialCountTerminal_append,
                              sententialCountNonterminal_append,
                              SententialCountTerminal,
                              SententialCountNonterminal, moreBN, moreBT,
                              ggNonterminal, ggTerminal] at hmargin ⊢ <;>
                            omega

theorem strictMoreB_derives_preserves_margin
    {x y : SententialForm EqualCountTerminal StrictMoreBNT}
    (h : GeneralGrammar.Derives StrictMoreBGrammar x y) :
    strictMoreBMargin x -> strictMoreBMargin y := by
  induction h with
  | refl _ =>
      intro hmargin
      exact hmargin
  | step hstep _ ih =>
      intro hmargin
      exact ih (strictMoreB_yields_preserves_margin hstep hmargin)

theorem strictMoreBGrammar_generated_has_fewer_as_than_bs
    {word : Word EqualCountTerminal}
    (h : word ∈ GeneralGrammar.GeneratedLanguage StrictMoreBGrammar) :
    Word.Count EqualCountTerminal.a word <
      Word.Count EqualCountTerminal.b word := by
  have hderives :
      GeneralGrammar.Derives StrictMoreBGrammar
        [moreBN StrictMoreBNT.start]
        (SententialForm.terminalWord word) := by
    simpa [GeneralGrammar.GeneratedLanguage, StrictMoreBGrammar, moreBN,
      ggNonterminal] using h
  have hmargin :=
    strictMoreB_derives_preserves_margin hderives
      strictMoreB_start_margin
  simpa [strictMoreBMargin, strictMoreBCountA,
    strictMoreBCountBWithCredits, sententialCountTerminal_terminalWord,
    sententialCountNonterminal_terminalWord] using hmargin

def strictMoreBWord (n extra : Nat) : Word EqualCountTerminal :=
  Word.Concat (Word.RepeatSymbol EqualCountTerminal.a n)
    (Word.RepeatSymbol EqualCountTerminal.b (n + extra + 1))

def strictMoreBTailWord (extra : Nat) : Word EqualCountTerminal :=
  Word.RepeatSymbol EqualCountTerminal.b (extra + 1)

def strictMoreBLanguage : Language EqualCountTerminal :=
  fun word => exists n extra, word = strictMoreBWord n extra

def strictMoreBTailLanguage : Language EqualCountTerminal :=
  fun word => exists extra, word = strictMoreBTailWord extra

theorem strictMoreB_word_zero (extra : Nat) :
    strictMoreBWord 0 extra = strictMoreBTailWord extra := by
  simp [strictMoreBWord, strictMoreBTailWord, Word.Concat,
    Word.RepeatSymbol]

theorem strictMoreB_tail_more_word (extra : Nat) :
    EqualCountTerminal.b :: strictMoreBTailWord extra =
      strictMoreBTailWord (extra + 1) := by
  unfold strictMoreBTailWord
  rw [show extra + 1 + 1 = (extra + 1) + 1 by omega]
  rfl

theorem strictMoreB_wrap_word (n extra : Nat) :
    EqualCountTerminal.a ::
        Word.Concat (strictMoreBWord n extra) [EqualCountTerminal.b] =
      strictMoreBWord (n + 1) extra := by
  unfold strictMoreBWord
  rw [show Word.RepeatSymbol EqualCountTerminal.a (n + 1) =
    EqualCountTerminal.a :: Word.RepeatSymbol EqualCountTerminal.a n by rfl]
  have hb :
      Word.RepeatSymbol EqualCountTerminal.b (n + 1 + extra + 1) =
        Word.Concat
          (Word.RepeatSymbol EqualCountTerminal.b (n + extra + 1))
          [EqualCountTerminal.b] := by
    have hnat : n + 1 + extra + 1 = (n + extra + 1) + 1 := by
      omega
    rw [hnat, repeatSymbol_succ_eq_append]
  rw [hb]
  simp [Word.Concat, List.append_assoc]

def strictMoreBSymbolLanguage :
    Symbol EqualCountTerminal StrictMoreBNT -> Language EqualCountTerminal
  | Symbol.terminal token => Language.Singleton (Word.Symbol token)
  | Symbol.nonterminal StrictMoreBNT.start => strictMoreBLanguage
  | Symbol.nonterminal StrictMoreBNT.tail => strictMoreBTailLanguage

theorem strictMoreB_tail_one_derives :
    GeneralGrammar.Derives StrictMoreBGrammar [moreBN StrictMoreBNT.tail]
      (SententialForm.terminalWord (strictMoreBTailWord 0)) := by
  have hstep :
      GeneralGrammar.Yields StrictMoreBGrammar [moreBN StrictMoreBNT.tail]
        [moreBT EqualCountTerminal.b] := by
    simpa [moreBN, moreBT] using
      general_yields_of_production (G := StrictMoreBGrammar)
        StrictMoreBProduces.tailOne [] []
  simpa [strictMoreBTailWord, SententialForm.terminalWord,
    Word.RepeatSymbol, moreBT] using
    GeneralGrammar.yields_derives hstep

theorem strictMoreB_tail_more_derives {word : Word EqualCountTerminal}
    (h : GeneralGrammar.Derives StrictMoreBGrammar [moreBN StrictMoreBNT.tail]
      (SententialForm.terminalWord word)) :
    GeneralGrammar.Derives StrictMoreBGrammar [moreBN StrictMoreBNT.tail]
      (SententialForm.terminalWord (EqualCountTerminal.b :: word)) := by
  have hstep :
      GeneralGrammar.Yields StrictMoreBGrammar [moreBN StrictMoreBNT.tail]
        [moreBT EqualCountTerminal.b, moreBN StrictMoreBNT.tail] := by
    simpa [moreBN, moreBT] using
      general_yields_of_production (G := StrictMoreBGrammar)
        StrictMoreBProduces.tailMore [] []
  have hcontext :
      GeneralGrammar.Derives StrictMoreBGrammar
        [moreBT EqualCountTerminal.b, moreBN StrictMoreBNT.tail]
        (moreBT EqualCountTerminal.b :: SententialForm.terminalWord word) := by
    simpa [moreBT] using
      general_derives_context h [moreBT EqualCountTerminal.b] []
  exact GeneralGrammar.Derives.step hstep (by
    simpa [SententialForm.terminalWord, moreBT] using hcontext)

theorem strictMoreB_tail_words_derives (extra : Nat) :
    GeneralGrammar.Derives StrictMoreBGrammar [moreBN StrictMoreBNT.tail]
      (SententialForm.terminalWord (strictMoreBTailWord extra)) := by
  induction extra with
  | zero =>
      exact strictMoreB_tail_one_derives
  | succ extra ih =>
      simpa [strictMoreB_tail_more_word extra] using
        strictMoreB_tail_more_derives ih

theorem strictMoreB_zero_words_derives (extra : Nat) :
    GeneralGrammar.Derives StrictMoreBGrammar [moreBN StrictMoreBNT.start]
      (SententialForm.terminalWord (strictMoreBWord 0 extra)) := by
  have hstep :
      GeneralGrammar.Yields StrictMoreBGrammar [moreBN StrictMoreBNT.start]
        [moreBN StrictMoreBNT.tail] := by
    simpa [moreBN] using
      general_yields_of_production (G := StrictMoreBGrammar)
        StrictMoreBProduces.toTail [] []
  have htail := strictMoreB_tail_words_derives extra
  have hall := GeneralGrammar.Derives.step hstep htail
  simpa [strictMoreB_word_zero] using hall

theorem strictMoreB_wrap_derives {word : Word EqualCountTerminal}
    (h : GeneralGrammar.Derives StrictMoreBGrammar [moreBN StrictMoreBNT.start]
      (SententialForm.terminalWord word)) :
    GeneralGrammar.Derives StrictMoreBGrammar [moreBN StrictMoreBNT.start]
      (SententialForm.terminalWord
        (EqualCountTerminal.a :: Word.Concat word [EqualCountTerminal.b])) := by
  have hstep :
      GeneralGrammar.Yields StrictMoreBGrammar [moreBN StrictMoreBNT.start]
        [moreBT EqualCountTerminal.a, moreBN StrictMoreBNT.start,
          moreBT EqualCountTerminal.b] := by
    simpa [moreBN, moreBT] using
      general_yields_of_production (G := StrictMoreBGrammar)
        StrictMoreBProduces.wrapPair [] []
  have hcontext :
      GeneralGrammar.Derives StrictMoreBGrammar
        [moreBT EqualCountTerminal.a, moreBN StrictMoreBNT.start,
          moreBT EqualCountTerminal.b]
        (moreBT EqualCountTerminal.a ::
          SententialForm.terminalWord word ++ [moreBT EqualCountTerminal.b]) := by
    simpa [moreBT] using
      general_derives_context h [moreBT EqualCountTerminal.a]
        [moreBT EqualCountTerminal.b]
  have hall := GeneralGrammar.Derives.step hstep hcontext
  change GeneralGrammar.Derives StrictMoreBGrammar
    [moreBN StrictMoreBNT.start]
    (SententialForm.terminalWord
      (EqualCountTerminal.a :: Word.Concat word [EqualCountTerminal.b]))
  simpa [SententialForm.terminalWord, Word.Concat, moreBT] using hall

theorem strictMoreB_words_generated (n extra : Nat) :
    strictMoreBWord n extra ∈
      GeneralGrammar.GeneratedLanguage StrictMoreBGrammar := by
  induction n with
  | zero =>
      simpa [GeneralGrammar.GeneratedLanguage, StrictMoreBGrammar, moreBN,
        ggNonterminal] using strictMoreB_zero_words_derives extra
  | succ n ih =>
      have hderives :
          GeneralGrammar.Derives StrictMoreBGrammar [moreBN StrictMoreBNT.start]
            (SententialForm.terminalWord
              (EqualCountTerminal.a ::
                Word.Concat (strictMoreBWord n extra)
                  [EqualCountTerminal.b])) := by
        exact strictMoreB_wrap_derives (by
          simpa [GeneralGrammar.GeneratedLanguage, StrictMoreBGrammar, moreBN,
            ggNonterminal] using ih)
      simpa [GeneralGrammar.GeneratedLanguage, StrictMoreBGrammar, moreBN,
        ggNonterminal, strictMoreB_wrap_word n extra] using hderives

theorem strictMoreB_production_sound
    (lhs rhs : SententialForm EqualCountTerminal StrictMoreBNT)
    (hprod : StrictMoreBGrammar.produces lhs rhs) :
    forall word,
      word ∈ CFG.FormLanguage strictMoreBSymbolLanguage rhs ->
        word ∈ CFG.FormLanguage strictMoreBSymbolLanguage lhs := by
  intro word hword
  cases hprod with
  | wrapPair =>
      simp [CFG.FormLanguage, strictMoreBSymbolLanguage,
        moreBN, moreBT, ggNonterminal, ggTerminal] at hword
      rcases hword with
        ⟨first, tail, hfirst, htail, hwordEq⟩
      rcases htail with
        ⟨middle, lastPart, hmiddle, hlastPart, htailEq⟩
      rcases hmiddle with ⟨n, extra, hmiddleEq⟩
      rcases hlastPart with
        ⟨last, empty, hlast, hempty, hlastPartEq⟩
      refine ⟨strictMoreBWord (n + 1) extra, Word.Empty,
        ⟨n + 1, extra, rfl⟩, rfl, ?_⟩
      rw [hwordEq, hfirst, htailEq, hmiddleEq, hlastPartEq, hlast,
        hempty]
      simpa [Word.Symbol, Word.Concat, Word.Empty] using
        strictMoreB_wrap_word n extra
  | toTail =>
      simp [CFG.FormLanguage, strictMoreBSymbolLanguage,
        moreBN, ggNonterminal] at hword
      rcases hword with ⟨tailWord, empty, htailWord, hempty, hwordEq⟩
      rcases htailWord with ⟨extra, htailWordEq⟩
      refine ⟨strictMoreBWord 0 extra, Word.Empty,
        ⟨0, extra, rfl⟩, rfl, ?_⟩
      rw [hwordEq, htailWordEq, hempty]
      simp [Word.Concat, Word.Empty, strictMoreB_word_zero extra]
  | tailMore =>
      simp [CFG.FormLanguage, strictMoreBSymbolLanguage,
        moreBN, moreBT, ggNonterminal, ggTerminal] at hword
      rcases hword with
        ⟨first, tail, hfirst, htail, hwordEq⟩
      rcases htail with
        ⟨middle, empty, hmiddle, hempty, htailEq⟩
      rcases hmiddle with ⟨extra, hmiddleEq⟩
      refine ⟨strictMoreBTailWord (extra + 1), Word.Empty,
        ⟨extra + 1, rfl⟩, rfl, ?_⟩
      rw [hwordEq, hfirst, htailEq, hmiddleEq, hempty]
      simpa [Word.Symbol, Word.Concat, Word.Empty] using
        strictMoreB_tail_more_word extra
  | tailOne =>
      simp [CFG.FormLanguage, strictMoreBSymbolLanguage,
        moreBT, ggTerminal] at hword
      rcases hword with ⟨first, empty, hfirst, hempty, hwordEq⟩
      refine ⟨strictMoreBTailWord 0, Word.Empty, ⟨0, rfl⟩, rfl, ?_⟩
      rw [hwordEq, hfirst, hempty]
      simp [strictMoreBTailWord, Word.Symbol, Word.Concat, Word.Empty,
        Word.RepeatSymbol]

theorem strictMoreB_generated_only_language {word : Word EqualCountTerminal}
    (h : word ∈ GeneralGrammar.GeneratedLanguage StrictMoreBGrammar) :
    word ∈ strictMoreBLanguage := by
  have hderives :
      GeneralGrammar.Derives StrictMoreBGrammar
        [moreBN StrictMoreBNT.start]
        (SententialForm.terminalWord word) := by
    simpa [GeneralGrammar.GeneratedLanguage, StrictMoreBGrammar, moreBN,
      ggNonterminal] using h
  have hs := general_derives_sound_for_symbol_language
    strictMoreBSymbolLanguage (by intro token; rfl)
    strictMoreB_production_sound hderives
  simp [CFG.FormLanguage, strictMoreBSymbolLanguage] at hs
  rcases hs with ⟨startWord, empty, hstartWord, hempty, hwordEq⟩
  rw [hwordEq]
  have hemptyEq : empty = Word.Empty := hempty
  rw [hemptyEq, Word.concat_empty_right]
  exact hstartWord

theorem strictMoreB_generated_language_exact (word : Word EqualCountTerminal) :
    word ∈ GeneralGrammar.GeneratedLanguage StrictMoreBGrammar <->
      word ∈ strictMoreBLanguage := by
  constructor
  · exact strictMoreB_generated_only_language
  · intro h
    rcases h with ⟨n, extra, hword⟩
    rw [hword]
    exact strictMoreB_words_generated n extra

theorem strictMoreBLanguage_finite_production_generated :
    FiniteProductionGeneralLanguage strictMoreBLanguage := by
  exists StrictMoreBNT
  exists StrictMoreBGrammar
  constructor
  · exact strictMoreBGrammar_has_finite_productions
  · intro word
    exact strictMoreB_generated_language_exact word

def aabbbWord : Word EqualCountTerminal :=
  [EqualCountTerminal.a, EqualCountTerminal.a, EqualCountTerminal.b,
    EqualCountTerminal.b, EqualCountTerminal.b]

-- Book: Chapter 4, Section 4.6, concrete derivation for the selected
-- strict-count grammar.
theorem strictMoreBGrammar_generates_aabbb :
    aabbbWord ∈ GeneralGrammar.GeneratedLanguage StrictMoreBGrammar := by
  let S := moreBN StrictMoreBNT.start
  let T := moreBN StrictMoreBNT.tail
  let a := moreBT EqualCountTerminal.a
  let b := moreBT EqualCountTerminal.b
  have h1 :
      GeneralGrammar.Yields StrictMoreBGrammar [S] [a, S, b] := by
    simpa [S, a, b] using
      general_yields_of_production (G := StrictMoreBGrammar)
        StrictMoreBProduces.wrapPair [] []
  have h2 :
      GeneralGrammar.Yields StrictMoreBGrammar [a, S, b]
        [a, a, S, b, b] := by
    simpa [S, a, b] using
      general_yields_of_production (G := StrictMoreBGrammar)
        StrictMoreBProduces.wrapPair [a] [b]
  have h3 :
      GeneralGrammar.Yields StrictMoreBGrammar [a, a, S, b, b]
        [a, a, T, b, b] := by
    simpa [S, T, a, b] using
      general_yields_of_production (G := StrictMoreBGrammar)
        StrictMoreBProduces.toTail [a, a] [b, b]
  have h4 :
      GeneralGrammar.Yields StrictMoreBGrammar [a, a, T, b, b]
        [a, a, b, b, b] := by
    simpa [T, a, b] using
      general_yields_of_production (G := StrictMoreBGrammar)
        StrictMoreBProduces.tailOne [a, a] [b, b]
  have hderives :
      GeneralGrammar.Derives StrictMoreBGrammar [S]
        [a, a, b, b, b] :=
    GeneralGrammar.Derives.step h1
      (GeneralGrammar.Derives.step h2
        (GeneralGrammar.Derives.step h3
          (GeneralGrammar.Derives.step h4
            (GeneralGrammar.Derives.refl [a, a, b, b, b]))))
  simpa [GeneralGrammar.GeneratedLanguage, StrictMoreBGrammar, aabbbWord,
    SententialForm.terminalWord, S, a, b] using hderives

inductive SquareTerminal where
  | a
deriving DecidableEq

inductive SquareNT where
  | start
  | d
  | t
  | e
  | b
  | markA
deriving DecidableEq

namespace SquareNT

def finite : Foundation.FiniteType SquareNT where
  elems := [start, d, t, e, b, markA]
  complete := by
    intro A
    cases A <;> simp

end SquareNT

def squareT (tok : SquareTerminal) : Symbol SquareTerminal SquareNT :=
  ggTerminal tok

def squareN (A : SquareNT) : Symbol SquareTerminal SquareNT :=
  ggNonterminal A

inductive SquareProduces :
    SententialForm SquareTerminal SquareNT ->
      SententialForm SquareTerminal SquareNT -> Prop where
  | start :
      SquareProduces [squareN SquareNT.start]
        [squareN SquareNT.d, squareN SquareNT.t, squareN SquareNT.e]
  | grow :
      SquareProduces [squareN SquareNT.t]
        [squareN SquareNT.b, squareN SquareNT.t, squareN SquareNT.markA]
  | stop :
      SquareProduces [squareN SquareNT.t] []
  | moveBA :
      SquareProduces [squareN SquareNT.b, squareN SquareNT.markA]
        [squareN SquareNT.markA, squareT SquareTerminal.a, squareN SquareNT.b]
  | moveBa :
      SquareProduces [squareN SquareNT.b, squareT SquareTerminal.a]
        [squareT SquareTerminal.a, squareN SquareNT.b]
  | removeBE :
      SquareProduces [squareN SquareNT.b, squareN SquareNT.e]
        [squareN SquareNT.e]
  | removeDA :
      SquareProduces [squareN SquareNT.d, squareN SquareNT.markA]
        [squareN SquareNT.d]
  | moveDa :
      SquareProduces [squareN SquareNT.d, squareT SquareTerminal.a]
        [squareT SquareTerminal.a, squareN SquareNT.d]
  | finish :
      SquareProduces [squareN SquareNT.d, squareN SquareNT.e] []

def SquareGrammar : GeneralGrammar SquareTerminal SquareNT where
  start := SquareNT.start
  produces := SquareProduces
  lhsContainsNonterminal := by
    intro lhs rhs h
    cases h <;> simp [SententialForm.containsNonterminal, squareN,
      ggNonterminal]
  nonterminalsFinite := SquareNT.finite

def SquareProductionList :
    List (GeneralGrammar.Production SquareTerminal SquareNT) :=
  [{ lhs := [squareN SquareNT.start],
     rhs := [squareN SquareNT.d, squareN SquareNT.t, squareN SquareNT.e] },
   { lhs := [squareN SquareNT.t],
     rhs := [squareN SquareNT.b, squareN SquareNT.t, squareN SquareNT.markA] },
   { lhs := [squareN SquareNT.t],
     rhs := [] },
   { lhs := [squareN SquareNT.b, squareN SquareNT.markA],
     rhs := [squareN SquareNT.markA, squareT SquareTerminal.a,
       squareN SquareNT.b] },
   { lhs := [squareN SquareNT.b, squareT SquareTerminal.a],
     rhs := [squareT SquareTerminal.a, squareN SquareNT.b] },
   { lhs := [squareN SquareNT.b, squareN SquareNT.e],
     rhs := [squareN SquareNT.e] },
   { lhs := [squareN SquareNT.d, squareN SquareNT.markA],
     rhs := [squareN SquareNT.d] },
   { lhs := [squareN SquareNT.d, squareT SquareTerminal.a],
     rhs := [squareT SquareTerminal.a, squareN SquareNT.d] },
   { lhs := [squareN SquareNT.d, squareN SquareNT.e],
     rhs := [] }]

-- Book: Chapter 4, Section 4.6, the unary-square example grammar has a finite
-- production presentation.
theorem squareGrammar_has_finite_productions :
    GeneralGrammar.HasFiniteProductions SquareGrammar := by
  exists SquareProductionList
  intro lhs rhs
  constructor
  · intro h
    cases h <;> simp [SquareProductionList]
  · intro h
    rcases h with ⟨rule, hmem, hlhs, hrhs⟩
    simp [SquareProductionList] at hmem
    rcases hmem with
      hrule | hrule | hrule | hrule | hrule |
      hrule | hrule | hrule | hrule
    · subst rule
      cases hlhs
      cases hrhs
      exact SquareProduces.start
    · subst rule
      cases hlhs
      cases hrhs
      exact SquareProduces.grow
    · subst rule
      cases hlhs
      cases hrhs
      exact SquareProduces.stop
    · subst rule
      cases hlhs
      cases hrhs
      exact SquareProduces.moveBA
    · subst rule
      cases hlhs
      cases hrhs
      exact SquareProduces.moveBa
    · subst rule
      cases hlhs
      cases hrhs
      exact SquareProduces.removeBE
    · subst rule
      cases hlhs
      cases hrhs
      exact SquareProduces.removeDA
    · subst rule
      cases hlhs
      cases hrhs
      exact SquareProduces.moveDa
    · subst rule
      cases hlhs
      cases hrhs
      exact SquareProduces.finish

-- Book: Chapter 4, Section 4.6, the language generated by the unary-square
-- sample grammar is generated by a finite general grammar.
theorem squareGrammar_finite_production_generated :
    FiniteProductionGeneralLanguage
      (GeneralGrammar.GeneratedLanguage SquareGrammar) := by
  exists SquareNT
  exists SquareGrammar
  constructor
  · exact squareGrammar_has_finite_productions
  · intro w
    rfl

def fourAsWord : Word SquareTerminal :=
  [SquareTerminal.a, SquareTerminal.a, SquareTerminal.a, SquareTerminal.a]

-- Book: Chapter 4, Section 4.6, a concrete derivation from the
-- `{a^(n^2)}` general grammar: the n = 2 case generates four a's.
theorem squareGrammar_generates_four_as :
    fourAsWord ∈ GeneralGrammar.GeneratedLanguage SquareGrammar := by
  let S := squareN SquareNT.start
  let D := squareN SquareNT.d
  let T := squareN SquareNT.t
  let E := squareN SquareNT.e
  let B := squareN SquareNT.b
  let A := squareN SquareNT.markA
  let a := squareT SquareTerminal.a
  have h1 : GeneralGrammar.Yields SquareGrammar [S] [D, T, E] := by
    simpa [S, D, T, E] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.start [] []
  have h2 :
      GeneralGrammar.Yields SquareGrammar [D, T, E] [D, B, T, A, E] := by
    simpa [D, T, E, B, A] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.grow [D] [E]
  have h3 :
      GeneralGrammar.Yields SquareGrammar [D, B, T, A, E]
        [D, B, B, T, A, A, E] := by
    simpa [D, T, E, B, A] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.grow [D, B] [A, E]
  have h4 :
      GeneralGrammar.Yields SquareGrammar [D, B, B, T, A, A, E]
        [D, B, B, A, A, E] := by
    simpa [D, T, E, B, A] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.stop [D, B, B] [A, A, E]
  have h5 :
      GeneralGrammar.Yields SquareGrammar [D, B, B, A, A, E]
        [D, B, A, a, B, A, E] := by
    simpa [D, E, B, A, a] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.moveBA [D, B] [A, E]
  have h6 :
      GeneralGrammar.Yields SquareGrammar [D, B, A, a, B, A, E]
        [D, B, A, a, A, a, B, E] := by
    simpa [D, E, B, A, a] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.moveBA [D, B, A, a] [E]
  have h7 :
      GeneralGrammar.Yields SquareGrammar [D, B, A, a, A, a, B, E]
        [D, B, A, a, A, a, E] := by
    simpa [D, E, B, A, a] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.removeBE [D, B, A, a, A, a] []
  have h8 :
      GeneralGrammar.Yields SquareGrammar [D, B, A, a, A, a, E]
        [D, A, a, B, a, A, a, E] := by
    simpa [D, E, B, A, a] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.moveBA [D] [a, A, a, E]
  have h9 :
      GeneralGrammar.Yields SquareGrammar [D, A, a, B, a, A, a, E]
        [D, A, a, a, B, A, a, E] := by
    simpa [D, E, B, A, a] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.moveBa [D, A, a] [A, a, E]
  have h10 :
      GeneralGrammar.Yields SquareGrammar [D, A, a, a, B, A, a, E]
        [D, A, a, a, A, a, B, a, E] := by
    simpa [D, E, B, A, a] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.moveBA [D, A, a, a] [a, E]
  have h11 :
      GeneralGrammar.Yields SquareGrammar [D, A, a, a, A, a, B, a, E]
        [D, A, a, a, A, a, a, B, E] := by
    simpa [D, E, B, A, a] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.moveBa [D, A, a, a, A, a] [E]
  have h12 :
      GeneralGrammar.Yields SquareGrammar [D, A, a, a, A, a, a, B, E]
        [D, A, a, a, A, a, a, E] := by
    simpa [D, E, B, A, a] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.removeBE [D, A, a, a, A, a, a] []
  have h13 :
      GeneralGrammar.Yields SquareGrammar [D, A, a, a, A, a, a, E]
        [D, a, a, A, a, a, E] := by
    simpa [D, E, A, a] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.removeDA [] [a, a, A, a, a, E]
  have h14 :
      GeneralGrammar.Yields SquareGrammar [D, a, a, A, a, a, E]
        [a, D, a, A, a, a, E] := by
    simpa [D, E, A, a] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.moveDa [] [a, A, a, a, E]
  have h15 :
      GeneralGrammar.Yields SquareGrammar [a, D, a, A, a, a, E]
        [a, a, D, A, a, a, E] := by
    simpa [D, E, A, a] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.moveDa [a] [A, a, a, E]
  have h16 :
      GeneralGrammar.Yields SquareGrammar [a, a, D, A, a, a, E]
        [a, a, D, a, a, E] := by
    simpa [D, E, A, a] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.removeDA [a, a] [a, a, E]
  have h17 :
      GeneralGrammar.Yields SquareGrammar [a, a, D, a, a, E]
        [a, a, a, D, a, E] := by
    simpa [D, E, a] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.moveDa [a, a] [a, E]
  have h18 :
      GeneralGrammar.Yields SquareGrammar [a, a, a, D, a, E]
        [a, a, a, a, D, E] := by
    simpa [D, E, a] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.moveDa [a, a, a] [E]
  have h19 :
      GeneralGrammar.Yields SquareGrammar [a, a, a, a, D, E]
        [a, a, a, a] := by
    simpa [D, E, a] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.finish [a, a, a, a] []
  have hderives :
      GeneralGrammar.Derives SquareGrammar [S] [a, a, a, a] :=
    GeneralGrammar.Derives.step h1
      (GeneralGrammar.Derives.step h2
        (GeneralGrammar.Derives.step h3
          (GeneralGrammar.Derives.step h4
            (GeneralGrammar.Derives.step h5
              (GeneralGrammar.Derives.step h6
                (GeneralGrammar.Derives.step h7
                  (GeneralGrammar.Derives.step h8
                    (GeneralGrammar.Derives.step h9
                      (GeneralGrammar.Derives.step h10
                        (GeneralGrammar.Derives.step h11
                          (GeneralGrammar.Derives.step h12
                            (GeneralGrammar.Derives.step h13
                              (GeneralGrammar.Derives.step h14
                                (GeneralGrammar.Derives.step h15
                                  (GeneralGrammar.Derives.step h16
                                    (GeneralGrammar.Derives.step h17
                                      (GeneralGrammar.Derives.step h18
                                        (GeneralGrammar.Derives.step h19
                                          (GeneralGrammar.Derives.refl
                                            [a, a, a, a])))))))))))))))))))
  simpa [GeneralGrammar.GeneratedLanguage, SquareGrammar, fourAsWord,
    SententialForm.terminalWord, S, a] using hderives

inductive PowerTwoNT where
  | start
  | h
  | d
  | r
  | boundary
  | markA
deriving DecidableEq

namespace PowerTwoNT

def finite : Foundation.FiniteType PowerTwoNT where
  elems := [start, h, d, r, boundary, markA]
  complete := by
    intro A
    cases A <;> simp

end PowerTwoNT

def powN (A : PowerTwoNT) : Symbol SquareTerminal PowerTwoNT :=
  ggNonterminal A

def powT (tok : SquareTerminal) : Symbol SquareTerminal PowerTwoNT :=
  ggTerminal tok

inductive PowerTwoProduces :
    SententialForm SquareTerminal PowerTwoNT ->
      SententialForm SquareTerminal PowerTwoNT -> Prop where
  | start :
      PowerTwoProduces [powN PowerTwoNT.start]
        [powN PowerTwoNT.h, powN PowerTwoNT.markA,
          powN PowerTwoNT.boundary]
  | beginDouble :
      PowerTwoProduces [powN PowerTwoNT.h] [powN PowerTwoNT.d]
  | duplicate :
      PowerTwoProduces [powN PowerTwoNT.d, powN PowerTwoNT.markA]
        [powN PowerTwoNT.markA, powN PowerTwoNT.markA,
          powN PowerTwoNT.d]
  | turnAround :
      PowerTwoProduces [powN PowerTwoNT.d, powN PowerTwoNT.boundary]
        [powN PowerTwoNT.r, powN PowerTwoNT.boundary]
  | returnLeft :
      PowerTwoProduces [powN PowerTwoNT.markA, powN PowerTwoNT.r]
        [powN PowerTwoNT.r, powN PowerTwoNT.markA]
  | ready :
      PowerTwoProduces [powN PowerTwoNT.r] [powN PowerTwoNT.h]
  | finishH :
      PowerTwoProduces [powN PowerTwoNT.h] []
  | finishBoundary :
      PowerTwoProduces [powN PowerTwoNT.boundary] []
  | emitA :
      PowerTwoProduces [powN PowerTwoNT.markA]
        [powT SquareTerminal.a]

def PowerTwoGrammar : GeneralGrammar SquareTerminal PowerTwoNT where
  start := PowerTwoNT.start
  produces := PowerTwoProduces
  lhsContainsNonterminal := by
    intro lhs rhs h
    cases h <;> simp [SententialForm.containsNonterminal, powN,
      ggNonterminal]
  nonterminalsFinite := PowerTwoNT.finite

def PowerTwoProductionList :
    List (GeneralGrammar.Production SquareTerminal PowerTwoNT) :=
  [{ lhs := [powN PowerTwoNT.start],
     rhs := [powN PowerTwoNT.h, powN PowerTwoNT.markA,
       powN PowerTwoNT.boundary] },
   { lhs := [powN PowerTwoNT.h],
     rhs := [powN PowerTwoNT.d] },
   { lhs := [powN PowerTwoNT.d, powN PowerTwoNT.markA],
     rhs := [powN PowerTwoNT.markA, powN PowerTwoNT.markA,
       powN PowerTwoNT.d] },
   { lhs := [powN PowerTwoNT.d, powN PowerTwoNT.boundary],
     rhs := [powN PowerTwoNT.r, powN PowerTwoNT.boundary] },
   { lhs := [powN PowerTwoNT.markA, powN PowerTwoNT.r],
     rhs := [powN PowerTwoNT.r, powN PowerTwoNT.markA] },
   { lhs := [powN PowerTwoNT.r],
     rhs := [powN PowerTwoNT.h] },
   { lhs := [powN PowerTwoNT.h],
     rhs := [] },
   { lhs := [powN PowerTwoNT.boundary],
     rhs := [] },
   { lhs := [powN PowerTwoNT.markA],
     rhs := [powT SquareTerminal.a] }]

-- Book: Chapter 4, Section 4.6, selected exercise grammar for unary powers
-- of two.  The head `d` doubles the current block of `A` markers and the
-- return head `r` resets the machine for another doubling pass.
theorem powerTwoGrammar_has_finite_productions :
    GeneralGrammar.HasFiniteProductions PowerTwoGrammar := by
  exists PowerTwoProductionList
  intro lhs rhs
  constructor
  · intro h
    cases h <;> simp [PowerTwoProductionList]
  · intro h
    rcases h with ⟨rule, hmem, hlhs, hrhs⟩
    simp [PowerTwoProductionList] at hmem
    rcases hmem with
      hrule | hrule | hrule | hrule | hrule |
      hrule | hrule | hrule | hrule
    · subst rule
      cases hlhs
      cases hrhs
      exact PowerTwoProduces.start
    · subst rule
      cases hlhs
      cases hrhs
      exact PowerTwoProduces.beginDouble
    · subst rule
      cases hlhs
      cases hrhs
      exact PowerTwoProduces.duplicate
    · subst rule
      cases hlhs
      cases hrhs
      exact PowerTwoProduces.turnAround
    · subst rule
      cases hlhs
      cases hrhs
      exact PowerTwoProduces.returnLeft
    · subst rule
      cases hlhs
      cases hrhs
      exact PowerTwoProduces.ready
    · subst rule
      cases hlhs
      cases hrhs
      exact PowerTwoProduces.finishH
    · subst rule
      cases hlhs
      cases hrhs
      exact PowerTwoProduces.finishBoundary
    · subst rule
      cases hlhs
      cases hrhs
      exact PowerTwoProduces.emitA

theorem powerTwoGrammar_finite_production_generated :
    FiniteProductionGeneralLanguage
      (GeneralGrammar.GeneratedLanguage PowerTwoGrammar) := by
  exists PowerTwoNT
  exists PowerTwoGrammar
  constructor
  · exact powerTwoGrammar_has_finite_productions
  · intro word
    rfl

-- Book: Chapter 4, Section 4.6, concrete `2^2` derivation for the selected
-- powers-of-two grammar.
theorem powerTwoGrammar_generates_four_as :
    fourAsWord ∈ GeneralGrammar.GeneratedLanguage PowerTwoGrammar := by
  let S := powN PowerTwoNT.start
  let H := powN PowerTwoNT.h
  let D := powN PowerTwoNT.d
  let R := powN PowerTwoNT.r
  let E := powN PowerTwoNT.boundary
  let A := powN PowerTwoNT.markA
  let a := powT SquareTerminal.a
  have h1 :
      GeneralGrammar.Yields PowerTwoGrammar [S] [H, A, E] := by
    simpa [S, H, A, E] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.start [] []
  have h2 :
      GeneralGrammar.Yields PowerTwoGrammar [H, A, E] [D, A, E] := by
    simpa [H, D, A, E] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.beginDouble [] [A, E]
  have h3 :
      GeneralGrammar.Yields PowerTwoGrammar [D, A, E] [A, A, D, E] := by
    simpa [D, A, E] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.duplicate [] [E]
  have h4 :
      GeneralGrammar.Yields PowerTwoGrammar [A, A, D, E] [A, A, R, E] := by
    simpa [D, R, A, E] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.turnAround [A, A] []
  have h5 :
      GeneralGrammar.Yields PowerTwoGrammar [A, A, R, E] [A, R, A, E] := by
    simpa [R, A, E] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.returnLeft [A] [E]
  have h6 :
      GeneralGrammar.Yields PowerTwoGrammar [A, R, A, E] [R, A, A, E] := by
    simpa [R, A, E] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.returnLeft [] [A, E]
  have h7 :
      GeneralGrammar.Yields PowerTwoGrammar [R, A, A, E] [H, A, A, E] := by
    simpa [H, R, A, E] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.ready [] [A, A, E]
  have h8 :
      GeneralGrammar.Yields PowerTwoGrammar [H, A, A, E] [D, A, A, E] := by
    simpa [H, D, A, E] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.beginDouble [] [A, A, E]
  have h9 :
      GeneralGrammar.Yields PowerTwoGrammar [D, A, A, E]
        [A, A, D, A, E] := by
    simpa [D, A, E] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.duplicate [] [A, E]
  have h10 :
      GeneralGrammar.Yields PowerTwoGrammar [A, A, D, A, E]
        [A, A, A, A, D, E] := by
    simpa [D, A, E] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.duplicate [A, A] [E]
  have h11 :
      GeneralGrammar.Yields PowerTwoGrammar [A, A, A, A, D, E]
        [A, A, A, A, R, E] := by
    simpa [D, R, A, E] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.turnAround [A, A, A, A] []
  have h12 :
      GeneralGrammar.Yields PowerTwoGrammar [A, A, A, A, R, E]
        [A, A, A, R, A, E] := by
    simpa [R, A, E] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.returnLeft [A, A, A] [E]
  have h13 :
      GeneralGrammar.Yields PowerTwoGrammar [A, A, A, R, A, E]
        [A, A, R, A, A, E] := by
    simpa [R, A, E] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.returnLeft [A, A] [A, E]
  have h14 :
      GeneralGrammar.Yields PowerTwoGrammar [A, A, R, A, A, E]
        [A, R, A, A, A, E] := by
    simpa [R, A, E] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.returnLeft [A] [A, A, E]
  have h15 :
      GeneralGrammar.Yields PowerTwoGrammar [A, R, A, A, A, E]
        [R, A, A, A, A, E] := by
    simpa [R, A, E] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.returnLeft [] [A, A, A, E]
  have h16 :
      GeneralGrammar.Yields PowerTwoGrammar [R, A, A, A, A, E]
        [H, A, A, A, A, E] := by
    simpa [H, R, A, E] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.ready [] [A, A, A, A, E]
  have h17 :
      GeneralGrammar.Yields PowerTwoGrammar [H, A, A, A, A, E]
        [A, A, A, A, E] := by
    simpa [H, A, E] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.finishH [] [A, A, A, A, E]
  have h18 :
      GeneralGrammar.Yields PowerTwoGrammar [A, A, A, A, E]
        [A, A, A, A] := by
    simpa [A, E] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.finishBoundary [A, A, A, A] []
  have h19 :
      GeneralGrammar.Yields PowerTwoGrammar [A, A, A, A]
        [a, A, A, A] := by
    simpa [A, a] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.emitA [] [A, A, A]
  have h20 :
      GeneralGrammar.Yields PowerTwoGrammar [a, A, A, A]
        [a, a, A, A] := by
    simpa [A, a] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.emitA [a] [A, A]
  have h21 :
      GeneralGrammar.Yields PowerTwoGrammar [a, a, A, A]
        [a, a, a, A] := by
    simpa [A, a] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.emitA [a, a] [A]
  have h22 :
      GeneralGrammar.Yields PowerTwoGrammar [a, a, a, A]
        [a, a, a, a] := by
    simpa [A, a] using
      general_yields_of_production (G := PowerTwoGrammar)
        PowerTwoProduces.emitA [a, a, a] []
  have hderives :
      GeneralGrammar.Derives PowerTwoGrammar [S] [a, a, a, a] :=
    GeneralGrammar.Derives.step h1
      (GeneralGrammar.Derives.step h2
        (GeneralGrammar.Derives.step h3
          (GeneralGrammar.Derives.step h4
            (GeneralGrammar.Derives.step h5
              (GeneralGrammar.Derives.step h6
                (GeneralGrammar.Derives.step h7
                  (GeneralGrammar.Derives.step h8
                    (GeneralGrammar.Derives.step h9
                      (GeneralGrammar.Derives.step h10
                        (GeneralGrammar.Derives.step h11
                          (GeneralGrammar.Derives.step h12
                            (GeneralGrammar.Derives.step h13
                              (GeneralGrammar.Derives.step h14
                                (GeneralGrammar.Derives.step h15
                                  (GeneralGrammar.Derives.step h16
                                    (GeneralGrammar.Derives.step h17
                                      (GeneralGrammar.Derives.step h18
                                        (GeneralGrammar.Derives.step h19
                                          (GeneralGrammar.Derives.step h20
                                            (GeneralGrammar.Derives.step h21
                                              (GeneralGrammar.Derives.step h22
                                                (GeneralGrammar.Derives.refl
                                                  [a, a, a, a]))))))))))))))))))))))
  simpa [GeneralGrammar.GeneratedLanguage, PowerTwoGrammar, fourAsWord,
    SententialForm.terminalWord, S, a] using hderives

end Section06
end Chapter04
end Book
end FoC
