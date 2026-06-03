import FoC.Grammars.GeneralGrammar

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section06

/-!
# Chapter 4, Section 4.6: General Grammars

General grammars relax context-free productions by allowing arbitrary
sentential forms on the left-hand side. This section records the derivation
API, finite-presentation countability statements, the embedding of CFGs, and
example language arguments. The reusable layer is
{module}`FoC.Grammars.GeneralGrammar`.

The additional power comes from productions that can inspect or move context
around a nonterminal. Many examples below use marker symbols, swapping rules,
and cleanup phases to enforce counting or ordering constraints that are beyond
context-free grammars.
-/

open Languages
open Grammars

/-!
# General Derivations

General-grammar yields generate derivations, derivations compose, and CFG
productions embed as unrestricted grammar productions.

The embedding theorem says every context-free derivation is also a general
grammar derivation. This makes general grammars a genuine extension of the
grammar model from Section 4.1.
-/

theorem general_yields_implies_derives {G : GeneralGrammar terminal nonterminal}
    {x y : SententialForm terminal nonterminal} (h : GeneralGrammar.Yields G x y) :
    GeneralGrammar.Derives G x y :=
  GeneralGrammar.yields_derives h

theorem general_derives_transitive {G : GeneralGrammar terminal nonterminal}
    {x y z : SententialForm terminal nonterminal}
    (hxy : GeneralGrammar.Derives G x y) (hyz : GeneralGrammar.Derives G y z) :
    GeneralGrammar.Derives G x z :=
  GeneralGrammar.derives_trans hxy hyz

def GeneralGrammarFromCFG (G : CFG terminal nonterminal) :
    GeneralGrammar terminal nonterminal :=
  GeneralGrammar.FromCFG G

def FiniteProductionGeneralGrammar
    (G : GeneralGrammar terminal nonterminal) : Prop :=
  GeneralGrammar.HasFiniteProductions G

def FiniteProductionGeneralLanguage (L : Language terminal) : Prop :=
  GeneralGrammar.FiniteProductionGenerated L

def CFGFinitePresentationCode (terminal nonterminal : Type) :=
  CFG.FinitePresentationCode terminal nonterminal

def GeneralGrammarFinitePresentationCode (terminal nonterminal : Type) :=
  GeneralGrammar.FinitePresentationCode terminal nonterminal

theorem cfg_finite_presentation_codes_countable
    (hterminal : Foundation.Countability.EncodableByNat terminal)
    (hnonterminal : Foundation.Countability.EncodableByNat nonterminal) :
    Foundation.FSet.Countable
      (Foundation.FSet.Univ :
        Foundation.FSet
          (CFGFinitePresentationCode terminal nonterminal)) :=
  CFG.FinitePresentationCode.countable hterminal hnonterminal

theorem general_grammar_finite_presentation_codes_countable
    (hterminal : Foundation.Countability.EncodableByNat terminal)
    (hnonterminal : Foundation.Countability.EncodableByNat nonterminal) :
    Foundation.FSet.Countable
      (Foundation.FSet.Univ :
        Foundation.FSet
          (GeneralGrammarFinitePresentationCode terminal nonterminal)) :=
  GeneralGrammar.FinitePresentationCode.countable hterminal hnonterminal

theorem finite_production_cfg_is_finite_production_general
    {G : CFG terminal nonterminal}
    (hG : CFG.HasFiniteProductions G) :
    FiniteProductionGeneralGrammar (GeneralGrammarFromCFG G) :=
  GeneralGrammar.fromCFG_hasFiniteProductions hG

theorem cfg_derivation_is_general_derivation {G : CFG terminal nonterminal}
    {x y : SententialForm terminal nonterminal}
    (h : CFG.Derives G x y) :
    GeneralGrammar.Derives (GeneralGrammar.FromCFG G) x y :=
  GeneralGrammar.cfg_derives_embeds h

theorem cfg_generated_word_is_general_generated (G : CFG terminal nonterminal)
    {w : Word terminal} (h : w ∈ CFG.GeneratedLanguage G) :
    w ∈ GeneralGrammar.GeneratedLanguage (GeneralGrammar.FromCFG G) :=
  GeneralGrammar.cfg_generated_language_embeds G h

/-!
# Finite Presentations and Countability

The chapter's countability discussion is represented by finite presentation
codes. If terminal and nonterminal symbols are encodable by natural numbers,
then finite grammar descriptions over those symbols are countable.

This is the formal version of "finite descriptions can be listed": once each
symbol has a natural-number code, finite production lists can also be encoded.
-/

theorem general_yields_of_production {G : GeneralGrammar terminal nonterminal}
    {lhs rhs : SententialForm terminal nonterminal}
    (hprod : G.produces lhs rhs) (u v : SententialForm terminal nonterminal) :
    GeneralGrammar.Yields G (u ++ lhs ++ v) (u ++ rhs ++ v) := by
  exists u
  exists v
  exists lhs
  exists rhs

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

/-!
# Soundness Helpers and Examples

The remaining helper lemmas interpret sentential forms as languages and count
symbols in sentential forms. They support the concrete unrestricted-grammar
examples later in the file.

The examples use two proof styles. Generation theorems explicitly construct
derivations for target words. Soundness theorems assign invariants to
sentential forms, such as equal symbol counts or ordered block shape, and prove
every production preserves the invariant.
-/

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

theorem language_singleton_empty_only {word : Word terminal}
    (h : word ∈ Language.Singleton (Word.Empty : Word terminal)) :
    word = Word.Empty := h

theorem language_singleton_empty_mem :
    (Word.Empty : Word terminal) ∈
      Language.Singleton (Word.Empty : Word terminal) :=
  rfl

theorem language_concat_empty_only {L M : Language terminal}
    (hL : forall word, word ∈ L -> word = Word.Empty)
    (hM : forall word, word ∈ M -> word = Word.Empty) :
    forall word, word ∈ Language.Concat L M -> word = Word.Empty := by
  intro word h
  rcases h with ⟨left, right, hleft, hright, hword⟩
  rw [hL left hleft, hM right hright] at hword
  simpa [Word.Concat, Word.Empty] using hword

theorem language_concat_empty_mem {L M : Language terminal}
    (hL : (Word.Empty : Word terminal) ∈ L)
    (hM : (Word.Empty : Word terminal) ∈ M) :
    (Word.Empty : Word terminal) ∈ Language.Concat L M := by
  exists Word.Empty
  exists Word.Empty

theorem language_concat_right_empty_only_mem {L M : Language terminal}
    {word : Word terminal}
    (hM : forall suffix, suffix ∈ M -> suffix = Word.Empty)
    (h : word ∈ Language.Concat L M) :
    word ∈ L := by
  rcases h with ⟨left, right, hleft, hright, hword⟩
  rw [hM right hright] at hword
  simp [Word.Concat, Word.Empty] at hword
  rw [hword]
  exact hleft

theorem language_concat_right_empty_mem {L M : Language terminal}
    {word : Word terminal}
    (hM : (Word.Empty : Word terminal) ∈ M)
    (h : word ∈ L) :
    word ∈ Language.Concat L M := by
  exists word
  exists Word.Empty
  exact ⟨h, hM, by simp [Word.Concat, Word.Empty]⟩

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

theorem sententialCountNonterminal_terminal_absurd
    [DecidableEq nonterminal]
    {A : nonterminal} {sf : SententialForm terminal nonterminal}
    {w : Word terminal}
    (hcount : SententialCountNonterminal A sf = 1)
    (hsf : sf = SententialForm.terminalWord w) : False := by
  have hzero : SententialCountNonterminal A sf = 0 := by
    rw [hsf]
    exact sententialCountNonterminal_terminalWord A w
  omega

theorem sententialCountNonterminal_repeat_nonterminal_of_ne
    [DecidableEq nonterminal]
    {A B : nonterminal} (hne : B ≠ A) (n : Nat) :
    SententialCountNonterminal A
      (Word.RepeatSymbol (ggNonterminal B) n :
        SententialForm terminal nonterminal) = 0 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change (if B = A then 1 else 0) +
          SententialCountNonterminal A
            (Word.RepeatSymbol (ggNonterminal B) n) = 0
      simp [hne, ih]

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

theorem repeatSymbol_add_eq_concat (a : terminal) (m n : Nat) :
    Word.RepeatSymbol a (m + n) =
      Word.Concat (Word.RepeatSymbol a m) (Word.RepeatSymbol a n) := by
  simp [Word.RepeatSymbol, Word.Concat, List.replicate_append_replicate]

theorem word_count_concat [DecidableEq terminal]
    (a : terminal) (x y : Word terminal) :
    Word.Count a (Word.Concat x y) = Word.Count a x + Word.Count a y := by
  induction x with
  | nil =>
      simp [Word.Concat, Word.Count]
  | cons b rest ih =>
      change (if b = a then 1 else 0) +
          Word.Count a (Word.Concat rest y) =
        (if b = a then 1 else 0) + Word.Count a rest +
          Word.Count a y
      rw [ih]
      omega

theorem word_count_repeat_same [DecidableEq terminal] (a : terminal) (n : Nat) :
    Word.Count a (Word.RepeatSymbol a n) = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change Word.Count a (a :: Word.RepeatSymbol a n) = n + 1
      simp [Word.Count, ih]
      omega

theorem word_count_repeat_of_ne [DecidableEq terminal]
    {a b : terminal} (h : b ≠ a) (n : Nat) :
    Word.Count a (Word.RepeatSymbol b n) = 0 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change Word.Count a (b :: Word.RepeatSymbol b n) = 0
      simp [Word.Count, h, ih]

/-!
# Equal Counts over Three Symbols

The first unrestricted grammar generates all words with the same number of
`a`, `b`, and `c` symbols, regardless of order. It grows one marker of each
kind, freely swaps markers, and then emits terminals. The proof separates
count preservation from explicit generation of any balanced word.
-/

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

theorem equalCountGrammar_finite_production_generated :
    FiniteProductionGeneralLanguage
      (GeneralGrammar.GeneratedLanguage EqualCountGrammar) := by
  exists EqualCountNT
  exists EqualCountGrammar
  constructor
  · exact equalCountGrammar_has_finite_productions
  · intro w
    rfl

/-!
Soundness for this grammar is an invariant proof. Terminals already emitted and
markers not yet emitted are counted together; every production preserves the
total number of future {lit}`a`s, {lit}`b`s, and {lit}`c`s.
-/

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

def equalCountLanguage : Language EqualCountTerminal :=
  fun w =>
    Word.Count EqualCountTerminal.a w = Word.Count EqualCountTerminal.b w ∧
      Word.Count EqualCountTerminal.b w = Word.Count EqualCountTerminal.c w

def equalCountAForm (n : Nat) :
    SententialForm EqualCountTerminal EqualCountNT :=
  List.replicate n (ecN EqualCountNT.markA)

def equalCountBForm (n : Nat) :
    SententialForm EqualCountTerminal EqualCountNT :=
  List.replicate n (ecN EqualCountNT.markB)

def equalCountCForm (n : Nat) :
    SententialForm EqualCountTerminal EqualCountNT :=
  List.replicate n (ecN EqualCountNT.markC)

def equalCountMarkerBlock :
    SententialForm EqualCountTerminal EqualCountNT :=
  [ecN EqualCountNT.markA, ecN EqualCountNT.markB,
    ecN EqualCountNT.markC]

def equalCountRepeatedMarkers (n : Nat) :
    SententialForm EqualCountTerminal EqualCountNT :=
  Word.RepeatWord equalCountMarkerBlock n

def equalCountMarkerBag (aCount bCount cCount : Nat) :
    SententialForm EqualCountTerminal EqualCountNT :=
  equalCountAForm aCount ++ equalCountBForm bCount ++
    equalCountCForm cCount

def equalCountMarkerOfTerminal :
    EqualCountTerminal -> EqualCountNT
  | EqualCountTerminal.a => EqualCountNT.markA
  | EqualCountTerminal.b => EqualCountNT.markB
  | EqualCountTerminal.c => EqualCountNT.markC

def equalCountMarkerWord (w : Word EqualCountTerminal) :
    SententialForm EqualCountTerminal EqualCountNT :=
  w.map (fun token => ecN (equalCountMarkerOfTerminal token))

/-!
Completeness is constructive. First grow a bag with the same number of
{lit}`A`, {lit}`B`, and {lit}`C` markers. Then use swap rules to reorder the bag
so it matches the target word's symbol order, and finally emit terminals from
those markers.
-/

theorem equalCount_moveB_left_over_as
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal EqualCountNT) :
    GeneralGrammar.Derives EqualCountGrammar
      (pre ++ equalCountAForm n ++ [ecN EqualCountNT.markB] ++ suffix)
      (pre ++ [ecN EqualCountNT.markB] ++ equalCountAForm n ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [equalCountAForm, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := EqualCountGrammar)
          (pre ++ [ecN EqualCountNT.markB] ++ suffix))
  | succ n ih =>
      let A := ecN EqualCountNT.markA
      let B := ecN EqualCountNT.markB
      have htail :
          GeneralGrammar.Derives EqualCountGrammar
            (pre ++ [A] ++ equalCountAForm n ++ [B] ++ suffix)
            (pre ++ [A] ++ [B] ++ equalCountAForm n ++ suffix) := by
        simpa [A, B, List.append_assoc] using ih (pre ++ [A])
      have hswap :
          GeneralGrammar.Yields EqualCountGrammar
            (pre ++ [A] ++ [B] ++ equalCountAForm n ++ suffix)
            (pre ++ [B] ++ [A] ++ equalCountAForm n ++ suffix) := by
        simpa [A, B, List.append_assoc] using
          general_yields_of_production (G := EqualCountGrammar)
            EqualCountProduces.swapAB pre (equalCountAForm n ++ suffix)
      have hall := GeneralGrammar.derives_trans htail
        (GeneralGrammar.yields_derives hswap)
      simpa [equalCountAForm, A, B, List.append_assoc] using hall

theorem equalCount_moveC_left_over_as
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal EqualCountNT) :
    GeneralGrammar.Derives EqualCountGrammar
      (pre ++ equalCountAForm n ++ [ecN EqualCountNT.markC] ++ suffix)
      (pre ++ [ecN EqualCountNT.markC] ++ equalCountAForm n ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [equalCountAForm, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := EqualCountGrammar)
          (pre ++ [ecN EqualCountNT.markC] ++ suffix))
  | succ n ih =>
      let A := ecN EqualCountNT.markA
      let C := ecN EqualCountNT.markC
      have htail :
          GeneralGrammar.Derives EqualCountGrammar
            (pre ++ [A] ++ equalCountAForm n ++ [C] ++ suffix)
            (pre ++ [A] ++ [C] ++ equalCountAForm n ++ suffix) := by
        simpa [A, C, List.append_assoc] using ih (pre ++ [A])
      have hswap :
          GeneralGrammar.Yields EqualCountGrammar
            (pre ++ [A] ++ [C] ++ equalCountAForm n ++ suffix)
            (pre ++ [C] ++ [A] ++ equalCountAForm n ++ suffix) := by
        simpa [A, C, List.append_assoc] using
          general_yields_of_production (G := EqualCountGrammar)
            EqualCountProduces.swapAC pre (equalCountAForm n ++ suffix)
      have hall := GeneralGrammar.derives_trans htail
        (GeneralGrammar.yields_derives hswap)
      simpa [equalCountAForm, A, C, List.append_assoc] using hall

theorem equalCount_moveC_left_over_bs
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal EqualCountNT) :
    GeneralGrammar.Derives EqualCountGrammar
      (pre ++ equalCountBForm n ++ [ecN EqualCountNT.markC] ++ suffix)
      (pre ++ [ecN EqualCountNT.markC] ++ equalCountBForm n ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [equalCountBForm, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := EqualCountGrammar)
          (pre ++ [ecN EqualCountNT.markC] ++ suffix))
  | succ n ih =>
      let B := ecN EqualCountNT.markB
      let C := ecN EqualCountNT.markC
      have htail :
          GeneralGrammar.Derives EqualCountGrammar
            (pre ++ [B] ++ equalCountBForm n ++ [C] ++ suffix)
            (pre ++ [B] ++ [C] ++ equalCountBForm n ++ suffix) := by
        simpa [B, C, List.append_assoc] using ih (pre ++ [B])
      have hswap :
          GeneralGrammar.Yields EqualCountGrammar
            (pre ++ [B] ++ [C] ++ equalCountBForm n ++ suffix)
            (pre ++ [C] ++ [B] ++ equalCountBForm n ++ suffix) := by
        simpa [B, C, List.append_assoc] using
          general_yields_of_production (G := EqualCountGrammar)
            EqualCountProduces.swapBC pre (equalCountBForm n ++ suffix)
      have hall := GeneralGrammar.derives_trans htail
        (GeneralGrammar.yields_derives hswap)
      simpa [equalCountBForm, B, C, List.append_assoc] using hall

theorem equalCount_moveC_right_over_as
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal EqualCountNT) :
    GeneralGrammar.Derives EqualCountGrammar
      (pre ++ [ecN EqualCountNT.markC] ++ equalCountAForm n ++ suffix)
      (pre ++ equalCountAForm n ++ [ecN EqualCountNT.markC] ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [equalCountAForm] using
        (GeneralGrammar.Derives.refl (G := EqualCountGrammar)
          (pre ++ [ecN EqualCountNT.markC] ++ suffix))
  | succ n ih =>
      let A := ecN EqualCountNT.markA
      let C := ecN EqualCountNT.markC
      have hstep :
          GeneralGrammar.Yields EqualCountGrammar
            (pre ++ [C, A] ++ equalCountAForm n ++ suffix)
            (pre ++ [A, C] ++ equalCountAForm n ++ suffix) := by
        simpa [A, C, List.append_assoc] using
          general_yields_of_production (G := EqualCountGrammar)
            EqualCountProduces.swapCA pre (equalCountAForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives EqualCountGrammar
            (pre ++ [A, C] ++ equalCountAForm n ++ suffix)
            (pre ++ [A] ++ equalCountAForm n ++ [C] ++ suffix) := by
        simpa [A, C, List.append_assoc] using ih (pre ++ [A])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [equalCountAForm, A, C, List.append_assoc] using hall

theorem equalCount_moveB_right_over_as
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal EqualCountNT) :
    GeneralGrammar.Derives EqualCountGrammar
      (pre ++ [ecN EqualCountNT.markB] ++ equalCountAForm n ++ suffix)
      (pre ++ equalCountAForm n ++ [ecN EqualCountNT.markB] ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [equalCountAForm] using
        (GeneralGrammar.Derives.refl (G := EqualCountGrammar)
          (pre ++ [ecN EqualCountNT.markB] ++ suffix))
  | succ n ih =>
      let A := ecN EqualCountNT.markA
      let B := ecN EqualCountNT.markB
      have hstep :
          GeneralGrammar.Yields EqualCountGrammar
            (pre ++ [B, A] ++ equalCountAForm n ++ suffix)
            (pre ++ [A, B] ++ equalCountAForm n ++ suffix) := by
        simpa [A, B, List.append_assoc] using
          general_yields_of_production (G := EqualCountGrammar)
            EqualCountProduces.swapBA pre (equalCountAForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives EqualCountGrammar
            (pre ++ [A, B] ++ equalCountAForm n ++ suffix)
            (pre ++ [A] ++ equalCountAForm n ++ [B] ++ suffix) := by
        simpa [A, B, List.append_assoc] using ih (pre ++ [A])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [equalCountAForm, A, B, List.append_assoc] using hall

theorem equalCount_moveC_right_over_bs
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal EqualCountNT) :
    GeneralGrammar.Derives EqualCountGrammar
      (pre ++ [ecN EqualCountNT.markC] ++ equalCountBForm n ++ suffix)
      (pre ++ equalCountBForm n ++ [ecN EqualCountNT.markC] ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [equalCountBForm] using
        (GeneralGrammar.Derives.refl (G := EqualCountGrammar)
          (pre ++ [ecN EqualCountNT.markC] ++ suffix))
  | succ n ih =>
      let B := ecN EqualCountNT.markB
      let C := ecN EqualCountNT.markC
      have hstep :
          GeneralGrammar.Yields EqualCountGrammar
            (pre ++ [C, B] ++ equalCountBForm n ++ suffix)
            (pre ++ [B, C] ++ equalCountBForm n ++ suffix) := by
        simpa [B, C, List.append_assoc] using
          general_yields_of_production (G := EqualCountGrammar)
            EqualCountProduces.swapCB pre (equalCountBForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives EqualCountGrammar
            (pre ++ [B, C] ++ equalCountBForm n ++ suffix)
            (pre ++ [B] ++ equalCountBForm n ++ [C] ++ suffix) := by
        simpa [B, C, List.append_assoc] using ih (pre ++ [B])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [equalCountBForm, B, C, List.append_assoc] using hall

theorem equalCount_sort_repeated_markers_derives (n : Nat) :
    GeneralGrammar.Derives EqualCountGrammar
      (equalCountRepeatedMarkers n)
      (equalCountMarkerBag n n n) := by
  induction n with
  | zero =>
      exact GeneralGrammar.Derives.refl []
  | succ n ih =>
      let A := ecN EqualCountNT.markA
      let B := ecN EqualCountNT.markB
      let C := ecN EqualCountNT.markC
      have hsortTail :
          GeneralGrammar.Derives EqualCountGrammar
            (equalCountMarkerBlock ++ equalCountRepeatedMarkers n)
            (equalCountMarkerBlock ++ equalCountMarkerBag n n n) := by
        simpa [equalCountMarkerBlock, equalCountMarkerBag, A, B, C,
          List.append_assoc] using
          general_derives_context ih equalCountMarkerBlock []
      have hmoveCAs :
          GeneralGrammar.Derives EqualCountGrammar
            (equalCountMarkerBlock ++ equalCountMarkerBag n n n)
            ([A, B] ++ equalCountAForm n ++ [C] ++
              equalCountBForm n ++ equalCountCForm n) := by
        simpa [equalCountMarkerBlock, equalCountMarkerBag, A, B, C,
          List.append_assoc] using
          equalCount_moveC_right_over_as n [A, B]
            (equalCountBForm n ++ equalCountCForm n)
      have hmoveBAs :
          GeneralGrammar.Derives EqualCountGrammar
            ([A, B] ++ equalCountAForm n ++ [C] ++
              equalCountBForm n ++ equalCountCForm n)
            ([A] ++ equalCountAForm n ++ [B, C] ++
              equalCountBForm n ++ equalCountCForm n) := by
        simpa [A, B, C, List.append_assoc] using
          equalCount_moveB_right_over_as n [A]
            ([C] ++ equalCountBForm n ++ equalCountCForm n)
      have hmoveCBs :
          GeneralGrammar.Derives EqualCountGrammar
            ([A] ++ equalCountAForm n ++ [B, C] ++
              equalCountBForm n ++ equalCountCForm n)
            (equalCountMarkerBag (n + 1) (n + 1) (n + 1)) := by
        simpa [equalCountMarkerBag, equalCountAForm, equalCountBForm,
          equalCountCForm, A, B, C, List.append_assoc] using
          equalCount_moveC_right_over_bs n
            ([A] ++ equalCountAForm n ++ [B]) (equalCountCForm n)
      exact GeneralGrammar.derives_trans hsortTail
        (GeneralGrammar.derives_trans hmoveCAs
          (GeneralGrammar.derives_trans hmoveBAs hmoveCBs))

theorem equalCount_grow_repeated_markers_derives (n : Nat) :
    GeneralGrammar.Derives EqualCountGrammar [ecN EqualCountNT.start]
      ([ecN EqualCountNT.start] ++ equalCountRepeatedMarkers n) := by
  induction n with
  | zero =>
      simpa [equalCountRepeatedMarkers, Word.RepeatWord] using
        (GeneralGrammar.Derives.refl (G := EqualCountGrammar)
          [ecN EqualCountNT.start])
  | succ n ih =>
      have hstep :
          GeneralGrammar.Yields EqualCountGrammar
            ([ecN EqualCountNT.start] ++ equalCountRepeatedMarkers n)
            ([ecN EqualCountNT.start] ++ equalCountMarkerBlock ++
              equalCountRepeatedMarkers n) := by
        simpa [equalCountMarkerBlock, List.append_assoc] using
          general_yields_of_production (G := EqualCountGrammar)
            EqualCountProduces.grow [] (equalCountRepeatedMarkers n)
      have hall := GeneralGrammar.derives_trans ih
        (GeneralGrammar.yields_derives hstep)
      simpa [equalCountRepeatedMarkers, equalCountMarkerBlock,
        Word.RepeatWord, List.append_assoc] using hall

theorem equalCount_start_to_marker_bag_derives (n : Nat) :
    GeneralGrammar.Derives EqualCountGrammar [ecN EqualCountNT.start]
      (equalCountMarkerBag n n n) := by
  have hgrow := equalCount_grow_repeated_markers_derives n
  have hstop :
      GeneralGrammar.Yields EqualCountGrammar
        ([ecN EqualCountNT.start] ++ equalCountRepeatedMarkers n)
        (equalCountRepeatedMarkers n) := by
    simpa [List.append_assoc] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.stop [] (equalCountRepeatedMarkers n)
  exact GeneralGrammar.derives_trans hgrow
    (GeneralGrammar.derives_trans (GeneralGrammar.yields_derives hstop)
      (equalCount_sort_repeated_markers_derives n))

theorem equalCount_marker_bag_to_marker_word_derives
    (word : Word EqualCountTerminal)
    (aCount bCount cCount : Nat)
    (ha : Word.Count EqualCountTerminal.a word <= aCount)
    (hb : Word.Count EqualCountTerminal.b word <= bCount)
    (hc : Word.Count EqualCountTerminal.c word <= cCount) :
    GeneralGrammar.Derives EqualCountGrammar
      (equalCountMarkerBag aCount bCount cCount)
      (equalCountMarkerWord word ++
        equalCountMarkerBag
          (aCount - Word.Count EqualCountTerminal.a word)
          (bCount - Word.Count EqualCountTerminal.b word)
          (cCount - Word.Count EqualCountTerminal.c word)) := by
  induction word generalizing aCount bCount cCount with
  | nil =>
      simpa [equalCountMarkerWord, equalCountMarkerBag, Word.Count] using
        (GeneralGrammar.Derives.refl (G := EqualCountGrammar)
          (equalCountMarkerBag aCount bCount cCount))
  | cons token rest ih =>
      cases token with
      | a =>
          cases aCount with
          | zero =>
              simp [Word.Count] at ha
          | succ aRest =>
              have haRest :
                  Word.Count EqualCountTerminal.a rest <= aRest := by
                simp [Word.Count] at ha
                omega
              have hbRest :
                  Word.Count EqualCountTerminal.b rest <= bCount := by
                simpa [Word.Count] using hb
              have hcRest :
                  Word.Count EqualCountTerminal.c rest <= cCount := by
                simpa [Word.Count] using hc
              have hrest :=
                ih aRest bCount cCount haRest hbRest hcRest
              have hcontext :
                  GeneralGrammar.Derives EqualCountGrammar
                    ([ecN EqualCountNT.markA] ++
                      equalCountMarkerBag aRest bCount cCount)
                    ([ecN EqualCountNT.markA] ++
                      equalCountMarkerWord rest ++
                      equalCountMarkerBag
                        (aRest - Word.Count EqualCountTerminal.a rest)
                        (bCount - Word.Count EqualCountTerminal.b rest)
                        (cCount - Word.Count EqualCountTerminal.c rest)) := by
                simpa [List.append_assoc] using
                  general_derives_context hrest [ecN EqualCountNT.markA] []
              have hsubA :
                  aRest + 1 -
                      (1 + Word.Count EqualCountTerminal.a rest) =
                    aRest - Word.Count EqualCountTerminal.a rest := by
                omega
              have hrepA :
                  List.replicate (aRest + 1) (ecN EqualCountNT.markA) =
                    ecN EqualCountNT.markA :: equalCountAForm aRest := by
                rfl
              simpa [equalCountMarkerBag, equalCountAForm,
                equalCountMarkerWord, equalCountMarkerOfTerminal,
                Word.Count, hsubA, hrepA, List.append_assoc] using hcontext
      | b =>
          cases bCount with
          | zero =>
              simp [Word.Count] at hb
          | succ bRest =>
              have haRest :
                  Word.Count EqualCountTerminal.a rest <= aCount := by
                simpa [Word.Count] using ha
              have hbRest :
                  Word.Count EqualCountTerminal.b rest <= bRest := by
                simp [Word.Count] at hb
                omega
              have hcRest :
                  Word.Count EqualCountTerminal.c rest <= cCount := by
                simpa [Word.Count] using hc
              have hmove :
                  GeneralGrammar.Derives EqualCountGrammar
                    (equalCountMarkerBag aCount (bRest + 1) cCount)
                    ([ecN EqualCountNT.markB] ++
                      equalCountMarkerBag aCount bRest cCount) := by
                simpa [equalCountMarkerBag, equalCountBForm,
                  List.append_assoc] using
                  equalCount_moveB_left_over_as aCount []
                    (equalCountBForm bRest ++ equalCountCForm cCount)
              have hrest :=
                ih aCount bRest cCount haRest hbRest hcRest
              have hcontext :
                  GeneralGrammar.Derives EqualCountGrammar
                    ([ecN EqualCountNT.markB] ++
                      equalCountMarkerBag aCount bRest cCount)
                    ([ecN EqualCountNT.markB] ++
                      equalCountMarkerWord rest ++
                      equalCountMarkerBag
                        (aCount - Word.Count EqualCountTerminal.a rest)
                        (bRest - Word.Count EqualCountTerminal.b rest)
                        (cCount - Word.Count EqualCountTerminal.c rest)) := by
                simpa [List.append_assoc] using
                  general_derives_context hrest [ecN EqualCountNT.markB] []
              have hall := GeneralGrammar.derives_trans hmove hcontext
              have hsubB :
                  bRest + 1 -
                      (1 + Word.Count EqualCountTerminal.b rest) =
                    bRest - Word.Count EqualCountTerminal.b rest := by
                omega
              simpa [equalCountMarkerBag, equalCountBForm,
                equalCountMarkerWord, equalCountMarkerOfTerminal,
                Word.Count, hsubB, List.append_assoc] using hall
      | c =>
          cases cCount with
          | zero =>
              simp [Word.Count] at hc
          | succ cRest =>
              have haRest :
                  Word.Count EqualCountTerminal.a rest <= aCount := by
                simpa [Word.Count] using ha
              have hbRest :
                  Word.Count EqualCountTerminal.b rest <= bCount := by
                simpa [Word.Count] using hb
              have hcRest :
                  Word.Count EqualCountTerminal.c rest <= cRest := by
                simp [Word.Count] at hc
                omega
              have hmoveBs :
                  GeneralGrammar.Derives EqualCountGrammar
                    (equalCountMarkerBag aCount bCount (cRest + 1))
                    (equalCountAForm aCount ++ [ecN EqualCountNT.markC] ++
                      equalCountBForm bCount ++ equalCountCForm cRest) := by
                simpa [equalCountMarkerBag, equalCountCForm,
                  List.append_assoc] using
                  equalCount_moveC_left_over_bs bCount
                    (equalCountAForm aCount) (equalCountCForm cRest)
              have hmoveAs :
                  GeneralGrammar.Derives EqualCountGrammar
                    (equalCountAForm aCount ++ [ecN EqualCountNT.markC] ++
                      equalCountBForm bCount ++ equalCountCForm cRest)
                    ([ecN EqualCountNT.markC] ++
                      equalCountMarkerBag aCount bCount cRest) := by
                simpa [equalCountMarkerBag, List.append_assoc] using
                  equalCount_moveC_left_over_as aCount []
                    (equalCountBForm bCount ++ equalCountCForm cRest)
              have hrest :=
                ih aCount bCount cRest haRest hbRest hcRest
              have hcontext :
                  GeneralGrammar.Derives EqualCountGrammar
                    ([ecN EqualCountNT.markC] ++
                      equalCountMarkerBag aCount bCount cRest)
                    ([ecN EqualCountNT.markC] ++
                      equalCountMarkerWord rest ++
                      equalCountMarkerBag
                        (aCount - Word.Count EqualCountTerminal.a rest)
                        (bCount - Word.Count EqualCountTerminal.b rest)
                        (cRest - Word.Count EqualCountTerminal.c rest)) := by
                simpa [List.append_assoc] using
                  general_derives_context hrest [ecN EqualCountNT.markC] []
              have hall := GeneralGrammar.derives_trans hmoveBs
                (GeneralGrammar.derives_trans hmoveAs hcontext)
              have hsubC :
                  cRest + 1 -
                      (1 + Word.Count EqualCountTerminal.c rest) =
                    cRest - Word.Count EqualCountTerminal.c rest := by
                omega
              simpa [equalCountMarkerBag, equalCountCForm,
                equalCountMarkerWord, equalCountMarkerOfTerminal,
                Word.Count, hsubC, List.append_assoc] using hall

theorem equalCount_marker_word_to_terminal_word_derives
    (word : Word EqualCountTerminal) :
    GeneralGrammar.Derives EqualCountGrammar
      (equalCountMarkerWord word)
      (SententialForm.terminalWord word) := by
  induction word with
  | nil =>
      exact GeneralGrammar.Derives.refl []
  | cons token rest ih =>
      cases token with
      | a =>
          have hstep :
              GeneralGrammar.Yields EqualCountGrammar
                ([ecN EqualCountNT.markA] ++ equalCountMarkerWord rest)
                ([ecT EqualCountTerminal.a] ++ equalCountMarkerWord rest) := by
            simpa [List.append_assoc] using
              general_yields_of_production (G := EqualCountGrammar)
                EqualCountProduces.emitA [] (equalCountMarkerWord rest)
          have hcontext :
              GeneralGrammar.Derives EqualCountGrammar
                ([ecT EqualCountTerminal.a] ++ equalCountMarkerWord rest)
                ([ecT EqualCountTerminal.a] ++
                  SententialForm.terminalWord rest) := by
            simpa [List.append_assoc] using
              general_derives_context ih [ecT EqualCountTerminal.a] []
          have hall := GeneralGrammar.Derives.step hstep hcontext
          simpa [equalCountMarkerWord, equalCountMarkerOfTerminal,
            SententialForm.terminalWord, ecT] using hall
      | b =>
          have hstep :
              GeneralGrammar.Yields EqualCountGrammar
                ([ecN EqualCountNT.markB] ++ equalCountMarkerWord rest)
                ([ecT EqualCountTerminal.b] ++ equalCountMarkerWord rest) := by
            simpa [List.append_assoc] using
              general_yields_of_production (G := EqualCountGrammar)
                EqualCountProduces.emitB [] (equalCountMarkerWord rest)
          have hcontext :
              GeneralGrammar.Derives EqualCountGrammar
                ([ecT EqualCountTerminal.b] ++ equalCountMarkerWord rest)
                ([ecT EqualCountTerminal.b] ++
                  SententialForm.terminalWord rest) := by
            simpa [List.append_assoc] using
              general_derives_context ih [ecT EqualCountTerminal.b] []
          have hall := GeneralGrammar.Derives.step hstep hcontext
          simpa [equalCountMarkerWord, equalCountMarkerOfTerminal,
            SententialForm.terminalWord, ecT] using hall
      | c =>
          have hstep :
              GeneralGrammar.Yields EqualCountGrammar
                ([ecN EqualCountNT.markC] ++ equalCountMarkerWord rest)
                ([ecT EqualCountTerminal.c] ++ equalCountMarkerWord rest) := by
            simpa [List.append_assoc] using
              general_yields_of_production (G := EqualCountGrammar)
                EqualCountProduces.emitC [] (equalCountMarkerWord rest)
          have hcontext :
              GeneralGrammar.Derives EqualCountGrammar
                ([ecT EqualCountTerminal.c] ++ equalCountMarkerWord rest)
                ([ecT EqualCountTerminal.c] ++
                  SententialForm.terminalWord rest) := by
            simpa [List.append_assoc] using
              general_derives_context ih [ecT EqualCountTerminal.c] []
          have hall := GeneralGrammar.Derives.step hstep hcontext
          simpa [equalCountMarkerWord, equalCountMarkerOfTerminal,
            SententialForm.terminalWord, ecT] using hall

theorem equalCount_words_generated_of_equal_counts
    {word : Word EqualCountTerminal}
    (hcounts : word ∈ equalCountLanguage) :
    word ∈ GeneralGrammar.GeneratedLanguage EqualCountGrammar := by
  let n := Word.Count EqualCountTerminal.a word
  have hAB :
      Word.Count EqualCountTerminal.a word =
        Word.Count EqualCountTerminal.b word := hcounts.1
  have hBC :
      Word.Count EqualCountTerminal.b word =
        Word.Count EqualCountTerminal.c word := hcounts.2
  have hcEq :
      Word.Count EqualCountTerminal.c word =
        Word.Count EqualCountTerminal.a word :=
    (hAB.trans hBC).symm
  have hbLe : Word.Count EqualCountTerminal.b word <= n := by
    dsimp [n]
    exact Nat.le_of_eq hAB.symm
  have hcLe : Word.Count EqualCountTerminal.c word <= n := by
    dsimp [n]
    exact Nat.le_of_eq hcEq
  have hstart := equalCount_start_to_marker_bag_derives n
  have hmarkers :=
    equalCount_marker_bag_to_marker_word_derives word n n n
      (Nat.le_refl n) hbLe hcLe
  have hmarkersClean :
      GeneralGrammar.Derives EqualCountGrammar
        (equalCountMarkerBag n n n) (equalCountMarkerWord word) := by
    simpa [n, equalCountMarkerBag, equalCountAForm, equalCountBForm,
      equalCountCForm, hcEq, hAB] using hmarkers
  have hemit := equalCount_marker_word_to_terminal_word_derives word
  have hall := GeneralGrammar.derives_trans hstart
    (GeneralGrammar.derives_trans hmarkersClean hemit)
  simpa [GeneralGrammar.GeneratedLanguage, EqualCountGrammar, ecN,
    ggNonterminal] using hall

theorem equalCount_generated_language_exact
    (word : Word EqualCountTerminal) :
    word ∈ GeneralGrammar.GeneratedLanguage EqualCountGrammar <->
      word ∈ equalCountLanguage := by
  constructor
  · intro h
    exact equalCountGrammar_generated_has_equal_terminal_counts h
  · exact equalCount_words_generated_of_equal_counts

theorem equalCountLanguage_finite_production_generated :
    FiniteProductionGeneralLanguage equalCountLanguage := by
  exists EqualCountNT
  exists EqualCountGrammar
  constructor
  · exact equalCountGrammar_has_finite_productions
  · intro word
    exact equalCount_generated_language_exact word

/-!
The concrete word {lit}`baabcc` shows the unrestricted feature directly:
markers can be swapped into an arbitrary order before they are emitted as
terminals.
-/

def baabccWord : Word EqualCountTerminal :=
  [EqualCountTerminal.b, EqualCountTerminal.a, EqualCountTerminal.a,
    EqualCountTerminal.b, EqualCountTerminal.c, EqualCountTerminal.c]

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

/-!
# Equal Counts over Four Symbols

This is the four-symbol analogue of the previous construction. The same marker
and swapping strategy proves that equal counts of `a`, `b`, `c`, and `d` are
preserved by every generated terminal word.
-/

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

/-!
The four-symbol grammar is the same invariant idea with one more marker class.
The grow rule creates one marker for each of {lit}`a`, {lit}`b`, {lit}`c`, and
{lit}`d`; all swap rules preserve the four totals; emission converts markers
into terminals without changing the totals.
-/

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

/-!
The concrete word {lit}`dacb` shows that the grammar is not enforcing order. It
only enforces equal counts.
-/

def dacbWord : Word FourCountTerminal :=
  [FourCountTerminal.d, FourCountTerminal.a, FourCountTerminal.c,
    FourCountTerminal.b]

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

/-!
# Ordered {lit}`a^n b^n c^n`

The ordered construction first creates equal markers, then uses swapping and
phase nonterminals to force all `a`s before all `b`s before all `c`s. The
exactness theorem states that the generated language is exactly the ordered
block language.
-/

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

theorem orderedABCGrammar_finite_production_generated :
    FiniteProductionGeneralLanguage
      (GeneralGrammar.GeneratedLanguage OrderedABCGrammar) := by
  exists OrderedABCNT
  exists OrderedABCGrammar
  constructor
  · exact orderedABCGrammar_has_finite_productions
  · intro w
    rfl

/-!
The ordered grammar still grows one marker of each kind, but the cleanup rules
force the marker blocks into {lit}`A* B* C*` order before terminals are emitted.
The invariant below proves equal counts; a later shape proof proves that the
terminal order is also correct.
-/

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

/-!
The generation proof is a pipeline: sort the generated markers, convert all
{lit}`X` markers to {lit}`a`s, convert all {lit}`Y` markers to {lit}`b`s, and
convert all {lit}`Z` markers to {lit}`c`s.
-/

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

def orderedABCShapeWord (aCount bCount cCount : Nat) :
    Word EqualCountTerminal :=
  Word.Concat (Word.RepeatSymbol EqualCountTerminal.a aCount)
    (Word.Concat (Word.RepeatSymbol EqualCountTerminal.b bCount)
      (Word.RepeatSymbol EqualCountTerminal.c cCount))

def orderedABCBCShapeWord (bCount cCount : Nat) :
    Word EqualCountTerminal :=
  Word.Concat (Word.RepeatSymbol EqualCountTerminal.b bCount)
    (Word.RepeatSymbol EqualCountTerminal.c cCount)

def orderedABCCShapeWord (cCount : Nat) : Word EqualCountTerminal :=
  Word.RepeatSymbol EqualCountTerminal.c cCount

def orderedABCShapeLanguage : Language EqualCountTerminal :=
  fun word => exists aCount bCount cCount,
    word = orderedABCShapeWord aCount bCount cCount

def orderedABCBCShapeLanguage : Language EqualCountTerminal :=
  fun word => exists bCount cCount,
    word = orderedABCBCShapeWord bCount cCount

def orderedABCCShapeLanguage : Language EqualCountTerminal :=
  fun word => exists cCount, word = orderedABCCShapeWord cCount

def orderedABCSymbolLanguage :
    Symbol EqualCountTerminal OrderedABCNT -> Language EqualCountTerminal
  | Symbol.terminal token => Language.Singleton (Word.Symbol token)
  | Symbol.nonterminal OrderedABCNT.start => orderedABCShapeLanguage
  | Symbol.nonterminal OrderedABCNT.markA => Language.Singleton Word.Empty
  | Symbol.nonterminal OrderedABCNT.markB => Language.Singleton Word.Empty
  | Symbol.nonterminal OrderedABCNT.markC => Language.Singleton Word.Empty
  | Symbol.nonterminal OrderedABCNT.x => orderedABCShapeLanguage
  | Symbol.nonterminal OrderedABCNT.y => orderedABCBCShapeLanguage
  | Symbol.nonterminal OrderedABCNT.z => orderedABCCShapeLanguage

/-!
The soundness proof uses shape languages. They track not just the counts, but
also the phase of the ordered block: full {lit}`a* b* c*`, then {lit}`b* c*`,
then {lit}`c*`.
-/

theorem orderedABCShape_cons_a {word : Word EqualCountTerminal}
    (h : word ∈ orderedABCShapeLanguage) :
    Word.Concat [EqualCountTerminal.a] word ∈ orderedABCShapeLanguage := by
  rcases h with ⟨aCount, bCount, cCount, hword⟩
  exists Nat.succ aCount
  exists bCount
  exists cCount
  rw [hword]
  change EqualCountTerminal.a ::
      orderedABCShapeWord aCount bCount cCount =
    orderedABCShapeWord (Nat.succ aCount) bCount cCount
  rfl

theorem orderedABCBCShape_cons_b {word : Word EqualCountTerminal}
    (h : word ∈ orderedABCBCShapeLanguage) :
    Word.Concat [EqualCountTerminal.b] word ∈ orderedABCBCShapeLanguage := by
  rcases h with ⟨bCount, cCount, hword⟩
  exists Nat.succ bCount
  exists cCount
  rw [hword]
  change EqualCountTerminal.b :: orderedABCBCShapeWord bCount cCount =
    orderedABCBCShapeWord (Nat.succ bCount) cCount
  rfl

theorem orderedABCCShape_cons_c {word : Word EqualCountTerminal}
    (h : word ∈ orderedABCCShapeLanguage) :
    Word.Concat [EqualCountTerminal.c] word ∈ orderedABCCShapeLanguage := by
  rcases h with ⟨cCount, hword⟩
  exists Nat.succ cCount
  rw [hword]
  change EqualCountTerminal.c :: orderedABCCShapeWord cCount =
    orderedABCCShapeWord (Nat.succ cCount)
  rfl

theorem orderedABCBCShape_subset_shape {word : Word EqualCountTerminal}
    (h : word ∈ orderedABCBCShapeLanguage) :
    word ∈ orderedABCShapeLanguage := by
  rcases h with ⟨bCount, cCount, hword⟩
  exists 0
  exists bCount
  exists cCount

theorem orderedABCCShape_subset_bcShape {word : Word EqualCountTerminal}
    (h : word ∈ orderedABCCShapeLanguage) :
    word ∈ orderedABCBCShapeLanguage := by
  rcases h with ⟨cCount, hword⟩
  exists 0
  exists cCount

theorem orderedABCCShape_empty :
    Word.Empty ∈ orderedABCCShapeLanguage := by
  exists 0

theorem orderedABCShapeWord_count_a (aCount bCount cCount : Nat) :
    Word.Count EqualCountTerminal.a
      (orderedABCShapeWord aCount bCount cCount) = aCount := by
  simp [orderedABCShapeWord, word_count_concat,
    word_count_repeat_same, word_count_repeat_of_ne]

theorem orderedABCShapeWord_count_b (aCount bCount cCount : Nat) :
    Word.Count EqualCountTerminal.b
      (orderedABCShapeWord aCount bCount cCount) = bCount := by
  simp [orderedABCShapeWord, word_count_concat,
    word_count_repeat_same, word_count_repeat_of_ne]

theorem orderedABCShapeWord_count_c (aCount bCount cCount : Nat) :
    Word.Count EqualCountTerminal.c
      (orderedABCShapeWord aCount bCount cCount) = cCount := by
  simp [orderedABCShapeWord, word_count_concat,
    word_count_repeat_same, word_count_repeat_of_ne]

theorem orderedABCBlockWord_eq_shape (n : Nat) :
    orderedABCBlockWord n = orderedABCShapeWord n n n := by
  rfl

theorem orderedABCShape_equal_counts_language
    {word : Word EqualCountTerminal}
    (hshape : word ∈ orderedABCShapeLanguage)
    (hcounts :
      Word.Count EqualCountTerminal.a word =
          Word.Count EqualCountTerminal.b word ∧
        Word.Count EqualCountTerminal.b word =
          Word.Count EqualCountTerminal.c word) :
    word ∈ orderedABCLanguage := by
  rcases hshape with ⟨aCount, bCount, cCount, hword⟩
  have ha :
      Word.Count EqualCountTerminal.a word = aCount := by
    rw [hword]
    exact orderedABCShapeWord_count_a aCount bCount cCount
  have hb :
      Word.Count EqualCountTerminal.b word = bCount := by
    rw [hword]
    exact orderedABCShapeWord_count_b aCount bCount cCount
  have hc :
      Word.Count EqualCountTerminal.c word = cCount := by
    rw [hword]
    exact orderedABCShapeWord_count_c aCount bCount cCount
  have hab : aCount = bCount := by
    omega
  have hbc : bCount = cCount := by
    omega
  exists aCount
  rw [hword, orderedABCBlockWord_eq_shape, hab, hbc]

theorem orderedABC_production_shape_sound
    {lhs rhs : SententialForm EqualCountTerminal OrderedABCNT}
    (hprod : OrderedABCGrammar.produces lhs rhs) :
    forall word, word ∈ CFG.FormLanguage orderedABCSymbolLanguage rhs ->
      word ∈ CFG.FormLanguage orderedABCSymbolLanguage lhs := by
  intro word hw
  let eps : Language EqualCountTerminal :=
    Language.Singleton (Word.Empty : Word EqualCountTerminal)
  have hepsOnly : forall suffix, suffix ∈ eps -> suffix = Word.Empty := by
    intro suffix hsuffix
    exact hsuffix
  have hepsMem : (Word.Empty : Word EqualCountTerminal) ∈ eps := rfl
  have heps2Only :
      forall suffix, suffix ∈ Language.Concat eps eps ->
        suffix = Word.Empty :=
    language_concat_empty_only hepsOnly hepsOnly
  have heps2Mem :
      (Word.Empty : Word EqualCountTerminal) ∈ Language.Concat eps eps :=
    language_concat_empty_mem hepsMem hepsMem
  have heps3Only :
      forall suffix, suffix ∈ Language.Concat eps (Language.Concat eps eps) ->
        suffix = Word.Empty :=
    language_concat_empty_only hepsOnly heps2Only
  have heps4Only :
      forall suffix,
        suffix ∈
          Language.Concat eps
            (Language.Concat eps (Language.Concat eps eps)) ->
        suffix = Word.Empty :=
    language_concat_empty_only hepsOnly heps3Only
  cases hprod
  · simp [CFG.FormLanguage, orderedABCSymbolLanguage, orderedN,
      ggNonterminal] at hw ⊢
    have hshape :=
      language_concat_right_empty_only_mem heps4Only hw
    exact language_concat_right_empty_mem hepsMem hshape
  · simpa [OrderedABCGrammar, CFG.FormLanguage, orderedABCSymbolLanguage,
      orderedN, orderedT, ggNonterminal, ggTerminal] using hw
  · simpa [OrderedABCGrammar, CFG.FormLanguage, orderedABCSymbolLanguage,
      orderedN, orderedT, ggNonterminal, ggTerminal] using hw
  · simpa [OrderedABCGrammar, CFG.FormLanguage, orderedABCSymbolLanguage,
      orderedN, orderedT, ggNonterminal, ggTerminal] using hw
  · simpa [OrderedABCGrammar, CFG.FormLanguage, orderedABCSymbolLanguage,
      orderedN, orderedT, ggNonterminal, ggTerminal] using hw
  · simp [CFG.FormLanguage, orderedABCSymbolLanguage,
      orderedN, orderedT, ggNonterminal, ggTerminal] at hw ⊢
    rcases hw with ⟨pref, suffix, hpref, hsuffix, hword⟩
    have hsuffixShape :
        suffix ∈ orderedABCShapeLanguage :=
      language_concat_right_empty_only_mem hepsOnly hsuffix
    have hshape : word ∈ orderedABCShapeLanguage := by
      rw [hword, hpref]
      simpa [Word.Symbol] using orderedABCShape_cons_a hsuffixShape
    exact language_concat_right_empty_mem heps2Mem hshape
  · simp [CFG.FormLanguage, orderedABCSymbolLanguage, orderedN,
      ggNonterminal] at hw ⊢
    have htail :=
      language_concat_right_empty_only_mem hepsOnly hw
    exact language_concat_right_empty_mem hepsMem
      (orderedABCBCShape_subset_shape htail)
  · simp [CFG.FormLanguage, orderedABCSymbolLanguage,
      orderedN, orderedT, ggNonterminal, ggTerminal] at hw ⊢
    rcases hw with ⟨pref, suffix, hpref, hsuffix, hword⟩
    have hsuffixShape :
        suffix ∈ orderedABCBCShapeLanguage :=
      language_concat_right_empty_only_mem hepsOnly hsuffix
    have hshape : word ∈ orderedABCBCShapeLanguage := by
      rw [hword, hpref]
      simpa [Word.Symbol] using orderedABCBCShape_cons_b hsuffixShape
    exact language_concat_right_empty_mem heps2Mem hshape
  · simp [CFG.FormLanguage, orderedABCSymbolLanguage, orderedN,
      ggNonterminal] at hw ⊢
    have htail :=
      language_concat_right_empty_only_mem hepsOnly hw
    exact language_concat_right_empty_mem hepsMem
      (orderedABCCShape_subset_bcShape htail)
  · simp [CFG.FormLanguage, orderedABCSymbolLanguage,
      orderedN, orderedT, ggNonterminal, ggTerminal] at hw ⊢
    rcases hw with ⟨pref, suffix, hpref, hsuffix, hword⟩
    have hsuffixShape :
        suffix ∈ orderedABCCShapeLanguage :=
      language_concat_right_empty_only_mem hepsOnly hsuffix
    have hshape : word ∈ orderedABCCShapeLanguage := by
      rw [hword, hpref]
      simpa [Word.Symbol] using orderedABCCShape_cons_c hsuffixShape
    exact language_concat_right_empty_mem heps2Mem hshape
  · simp [CFG.FormLanguage, orderedABCSymbolLanguage, orderedN,
      ggNonterminal] at hw ⊢
    rw [hw]
    exact language_concat_right_empty_mem hepsMem orderedABCCShape_empty

theorem orderedABCGrammar_generated_has_ordered_shape
    {word : Word EqualCountTerminal}
    (h : word ∈ GeneralGrammar.GeneratedLanguage OrderedABCGrammar) :
    word ∈ orderedABCShapeLanguage := by
  have hderives :
      GeneralGrammar.Derives OrderedABCGrammar [orderedN OrderedABCNT.start]
        (SententialForm.terminalWord word) := by
    simpa [GeneralGrammar.GeneratedLanguage, OrderedABCGrammar, orderedN,
      ggNonterminal] using h
  have hs := general_derives_sound_for_symbol_language
    orderedABCSymbolLanguage (by intro token; rfl)
    (by
      intro lhs rhs hprod word hw
      exact orderedABC_production_shape_sound hprod word hw)
    hderives
  simp [CFG.FormLanguage, orderedABCSymbolLanguage, orderedN, ggNonterminal]
    at hs
  exact language_concat_right_empty_only_mem
    (fun suffix hsuffix => hsuffix) hs

theorem orderedABC_generated_only_language
    {word : Word EqualCountTerminal}
    (h : word ∈ GeneralGrammar.GeneratedLanguage OrderedABCGrammar) :
    word ∈ orderedABCLanguage := by
  exact orderedABCShape_equal_counts_language
    (orderedABCGrammar_generated_has_ordered_shape h)
    (orderedABCGrammar_generated_has_equal_terminal_counts h)

theorem orderedABC_generated_language_exact
    (word : Word EqualCountTerminal) :
    word ∈ GeneralGrammar.GeneratedLanguage OrderedABCGrammar <->
      word ∈ orderedABCLanguage := by
  constructor
  · exact orderedABC_generated_only_language
  · exact orderedABC_language_subset_generated

theorem orderedABCLanguage_finite_production_generated :
    FiniteProductionGeneralLanguage orderedABCLanguage := by
  exists OrderedABCNT
  exists OrderedABCGrammar
  constructor
  · exact orderedABCGrammar_has_finite_productions
  · intro word
    exact orderedABC_generated_language_exact word

def aabbccWord : Word EqualCountTerminal :=
  [EqualCountTerminal.a, EqualCountTerminal.a, EqualCountTerminal.b,
    EqualCountTerminal.b, EqualCountTerminal.c, EqualCountTerminal.c]

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

/-!
# Ordered Four-Block Counts

This example extends the ordered-block method to four terminals, producing
words of the form `a^n b^n c^n d^n` and sample derivations such as
`aabbccdd`.
-/

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

/-!
The ordered four-block example repeats the ordered three-block pattern at
larger scale. The long production list consists of grow rules, marker-sorting
rules, phase-change rules, terminal-emission rules, and one final cleanup rule.
-/

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

/-!
# Strict Block Inequalities

The strict-more-`b` grammar generates ordered block words with more `b`s than
`a`s. The proof uses a tail phase that adds at least one extra `b` after all
balanced `a`/`b` pairs have been produced.
-/

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

/-!
Generation and soundness split cleanly here. Generation wraps balanced
{lit}`a`/{lit}`b` pairs around a tail with at least one extra {lit}`b`; soundness
uses the two nonterminal meanings below to prove no other shape can be
generated.
-/

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

/-!
# Strict Three-Way Counts

This grammar targets strict count inequalities among `a`, `b`, and `c`
symbols. The invariant records count margins so each production can be checked
locally against the intended strict ordering.
-/

inductive StrictABCGreaterNT where
  | start
  | pair
  | extraA
  | done
  | markA
  | markB
  | markC
deriving DecidableEq

namespace StrictABCGreaterNT

def finite : Foundation.FiniteType StrictABCGreaterNT where
  elems := [start, pair, extraA, done, markA, markB, markC]
  complete := by
    intro A
    cases A <;> simp

end StrictABCGreaterNT

def strictABCGreaterN (A : StrictABCGreaterNT) :
    Symbol EqualCountTerminal StrictABCGreaterNT :=
  ggNonterminal A

def strictABCGreaterT (tok : EqualCountTerminal) :
    Symbol EqualCountTerminal StrictABCGreaterNT :=
  ggTerminal tok

inductive StrictABCGreaterProduces :
    SententialForm EqualCountTerminal StrictABCGreaterNT ->
      SententialForm EqualCountTerminal StrictABCGreaterNT -> Prop where
  | growTriple :
      StrictABCGreaterProduces [strictABCGreaterN StrictABCGreaterNT.start]
        [strictABCGreaterN StrictABCGreaterNT.start,
          strictABCGreaterN StrictABCGreaterNT.markA,
          strictABCGreaterN StrictABCGreaterNT.markB,
          strictABCGreaterN StrictABCGreaterNT.markC]
  | toPair :
      StrictABCGreaterProduces [strictABCGreaterN StrictABCGreaterNT.start]
        [strictABCGreaterN StrictABCGreaterNT.pair]
  | growPair :
      StrictABCGreaterProduces [strictABCGreaterN StrictABCGreaterNT.pair]
        [strictABCGreaterN StrictABCGreaterNT.pair,
          strictABCGreaterN StrictABCGreaterNT.markA,
          strictABCGreaterN StrictABCGreaterNT.markB]
  | endPair :
      StrictABCGreaterProduces [strictABCGreaterN StrictABCGreaterNT.pair]
        [strictABCGreaterN StrictABCGreaterNT.extraA,
          strictABCGreaterN StrictABCGreaterNT.markA,
          strictABCGreaterN StrictABCGreaterNT.markB]
  | growExtraA :
      StrictABCGreaterProduces [strictABCGreaterN StrictABCGreaterNT.extraA]
        [strictABCGreaterN StrictABCGreaterNT.extraA,
          strictABCGreaterN StrictABCGreaterNT.markA]
  | endExtraA :
      StrictABCGreaterProduces [strictABCGreaterN StrictABCGreaterNT.extraA]
        [strictABCGreaterN StrictABCGreaterNT.done,
          strictABCGreaterN StrictABCGreaterNT.markA]
  | finish :
      StrictABCGreaterProduces [strictABCGreaterN StrictABCGreaterNT.done] []
  | swapAB :
      StrictABCGreaterProduces
        [strictABCGreaterN StrictABCGreaterNT.markA,
          strictABCGreaterN StrictABCGreaterNT.markB]
        [strictABCGreaterN StrictABCGreaterNT.markB,
          strictABCGreaterN StrictABCGreaterNT.markA]
  | swapBA :
      StrictABCGreaterProduces
        [strictABCGreaterN StrictABCGreaterNT.markB,
          strictABCGreaterN StrictABCGreaterNT.markA]
        [strictABCGreaterN StrictABCGreaterNT.markA,
          strictABCGreaterN StrictABCGreaterNT.markB]
  | swapAC :
      StrictABCGreaterProduces
        [strictABCGreaterN StrictABCGreaterNT.markA,
          strictABCGreaterN StrictABCGreaterNT.markC]
        [strictABCGreaterN StrictABCGreaterNT.markC,
          strictABCGreaterN StrictABCGreaterNT.markA]
  | swapCA :
      StrictABCGreaterProduces
        [strictABCGreaterN StrictABCGreaterNT.markC,
          strictABCGreaterN StrictABCGreaterNT.markA]
        [strictABCGreaterN StrictABCGreaterNT.markA,
          strictABCGreaterN StrictABCGreaterNT.markC]
  | swapBC :
      StrictABCGreaterProduces
        [strictABCGreaterN StrictABCGreaterNT.markB,
          strictABCGreaterN StrictABCGreaterNT.markC]
        [strictABCGreaterN StrictABCGreaterNT.markC,
          strictABCGreaterN StrictABCGreaterNT.markB]
  | swapCB :
      StrictABCGreaterProduces
        [strictABCGreaterN StrictABCGreaterNT.markC,
          strictABCGreaterN StrictABCGreaterNT.markB]
        [strictABCGreaterN StrictABCGreaterNT.markB,
          strictABCGreaterN StrictABCGreaterNT.markC]
  | emitA :
      StrictABCGreaterProduces [strictABCGreaterN StrictABCGreaterNT.markA]
        [strictABCGreaterT EqualCountTerminal.a]
  | emitB :
      StrictABCGreaterProduces [strictABCGreaterN StrictABCGreaterNT.markB]
        [strictABCGreaterT EqualCountTerminal.b]
  | emitC :
      StrictABCGreaterProduces [strictABCGreaterN StrictABCGreaterNT.markC]
        [strictABCGreaterT EqualCountTerminal.c]

def StrictABCGreaterGrammar :
    GeneralGrammar EqualCountTerminal StrictABCGreaterNT where
  start := StrictABCGreaterNT.start
  produces := StrictABCGreaterProduces
  lhsContainsNonterminal := by
    intro lhs rhs h
    cases h <;> simp [SententialForm.containsNonterminal,
      strictABCGreaterN, ggNonterminal]
  nonterminalsFinite := StrictABCGreaterNT.finite

def StrictABCGreaterProductionList :
    List (GeneralGrammar.Production EqualCountTerminal StrictABCGreaterNT) :=
  [{ lhs := [strictABCGreaterN StrictABCGreaterNT.start],
     rhs := [strictABCGreaterN StrictABCGreaterNT.start,
       strictABCGreaterN StrictABCGreaterNT.markA,
       strictABCGreaterN StrictABCGreaterNT.markB,
       strictABCGreaterN StrictABCGreaterNT.markC] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.start],
     rhs := [strictABCGreaterN StrictABCGreaterNT.pair] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.pair],
     rhs := [strictABCGreaterN StrictABCGreaterNT.pair,
       strictABCGreaterN StrictABCGreaterNT.markA,
       strictABCGreaterN StrictABCGreaterNT.markB] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.pair],
     rhs := [strictABCGreaterN StrictABCGreaterNT.extraA,
       strictABCGreaterN StrictABCGreaterNT.markA,
       strictABCGreaterN StrictABCGreaterNT.markB] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.extraA],
     rhs := [strictABCGreaterN StrictABCGreaterNT.extraA,
       strictABCGreaterN StrictABCGreaterNT.markA] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.extraA],
     rhs := [strictABCGreaterN StrictABCGreaterNT.done,
       strictABCGreaterN StrictABCGreaterNT.markA] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.done],
     rhs := [] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.markA,
       strictABCGreaterN StrictABCGreaterNT.markB],
     rhs := [strictABCGreaterN StrictABCGreaterNT.markB,
       strictABCGreaterN StrictABCGreaterNT.markA] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.markB,
       strictABCGreaterN StrictABCGreaterNT.markA],
     rhs := [strictABCGreaterN StrictABCGreaterNT.markA,
       strictABCGreaterN StrictABCGreaterNT.markB] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.markA,
       strictABCGreaterN StrictABCGreaterNT.markC],
     rhs := [strictABCGreaterN StrictABCGreaterNT.markC,
       strictABCGreaterN StrictABCGreaterNT.markA] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.markC,
       strictABCGreaterN StrictABCGreaterNT.markA],
     rhs := [strictABCGreaterN StrictABCGreaterNT.markA,
       strictABCGreaterN StrictABCGreaterNT.markC] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.markB,
       strictABCGreaterN StrictABCGreaterNT.markC],
     rhs := [strictABCGreaterN StrictABCGreaterNT.markC,
       strictABCGreaterN StrictABCGreaterNT.markB] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.markC,
       strictABCGreaterN StrictABCGreaterNT.markB],
     rhs := [strictABCGreaterN StrictABCGreaterNT.markB,
       strictABCGreaterN StrictABCGreaterNT.markC] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.markA],
     rhs := [strictABCGreaterT EqualCountTerminal.a] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.markB],
     rhs := [strictABCGreaterT EqualCountTerminal.b] },
   { lhs := [strictABCGreaterN StrictABCGreaterNT.markC],
     rhs := [strictABCGreaterT EqualCountTerminal.c] }]

theorem strictABCGreaterGrammar_has_finite_productions :
    GeneralGrammar.HasFiniteProductions StrictABCGreaterGrammar := by
  exists StrictABCGreaterProductionList
  intro lhs rhs
  constructor
  · intro h
    cases h <;> simp [StrictABCGreaterProductionList]
  · intro h
    rcases h with ⟨rule, hmem, hlhs, hrhs⟩
    simp [StrictABCGreaterProductionList] at hmem
    rcases hmem with
      hrule | hrule | hrule | hrule | hrule | hrule |
      hrule | hrule | hrule | hrule | hrule | hrule |
      hrule | hrule | hrule | hrule
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.growTriple
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.toPair
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.growPair
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.endPair
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.growExtraA
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.endExtraA
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.finish
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.swapAB
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.swapBA
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.swapAC
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.swapCA
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.swapBC
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.swapCB
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.emitA
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.emitB
    · subst rule
      cases hlhs
      cases hrhs
      exact StrictABCGreaterProduces.emitC

theorem strictABCGreaterGrammar_finite_production_generated :
    FiniteProductionGeneralLanguage
      (GeneralGrammar.GeneratedLanguage StrictABCGreaterGrammar) := by
  exists StrictABCGreaterNT
  exists StrictABCGreaterGrammar
  constructor
  · exact strictABCGreaterGrammar_has_finite_productions
  · intro word
    rfl

def strictABCGreaterTotalA
    (sf : SententialForm EqualCountTerminal StrictABCGreaterNT) : Nat :=
  SententialCountTerminal EqualCountTerminal.a sf +
    SententialCountNonterminal StrictABCGreaterNT.markA sf +
    2 * SententialCountNonterminal StrictABCGreaterNT.start sf +
    2 * SententialCountNonterminal StrictABCGreaterNT.pair sf +
    SententialCountNonterminal StrictABCGreaterNT.extraA sf

def strictABCGreaterTotalB
    (sf : SententialForm EqualCountTerminal StrictABCGreaterNT) : Nat :=
  SententialCountTerminal EqualCountTerminal.b sf +
    SententialCountNonterminal StrictABCGreaterNT.markB sf +
    SententialCountNonterminal StrictABCGreaterNT.start sf +
    SententialCountNonterminal StrictABCGreaterNT.pair sf

def strictABCGreaterTotalC
    (sf : SententialForm EqualCountTerminal StrictABCGreaterNT) : Nat :=
  SententialCountTerminal EqualCountTerminal.c sf +
    SententialCountNonterminal StrictABCGreaterNT.markC sf

def strictABCGreaterMargin
    (sf : SententialForm EqualCountTerminal StrictABCGreaterNT) : Prop :=
  strictABCGreaterTotalA sf > strictABCGreaterTotalB sf ∧
    strictABCGreaterTotalB sf > strictABCGreaterTotalC sf

theorem strictABCGreater_start_margin :
    strictABCGreaterMargin
      [strictABCGreaterN StrictABCGreaterNT.start] := by
  simp [strictABCGreaterMargin, strictABCGreaterTotalA,
    strictABCGreaterTotalB, strictABCGreaterTotalC,
    SententialCountTerminal, SententialCountNonterminal,
    strictABCGreaterN, ggNonterminal]

theorem strictABCGreater_yields_preserves_margin
    {x y : SententialForm EqualCountTerminal StrictABCGreaterNT}
    (h : GeneralGrammar.Yields StrictABCGreaterGrammar x y) :
    strictABCGreaterMargin x -> strictABCGreaterMargin y := by
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
                            simp [strictABCGreaterMargin,
                              strictABCGreaterTotalA,
                              strictABCGreaterTotalB,
                              strictABCGreaterTotalC,
                              sententialCountTerminal_append,
                              sententialCountNonterminal_append,
                              SententialCountTerminal,
                              SententialCountNonterminal,
                              strictABCGreaterN, strictABCGreaterT,
                              ggNonterminal, ggTerminal] at hmargin ⊢ <;>
                            omega

theorem strictABCGreater_derives_preserves_margin
    {x y : SententialForm EqualCountTerminal StrictABCGreaterNT}
    (h : GeneralGrammar.Derives StrictABCGreaterGrammar x y) :
    strictABCGreaterMargin x -> strictABCGreaterMargin y := by
  induction h with
  | refl _ =>
      intro hmargin
      exact hmargin
  | step hstep _ ih =>
      intro hmargin
      exact ih (strictABCGreater_yields_preserves_margin hstep hmargin)

theorem strictABCGreaterGrammar_generated_has_strict_counts
    {word : Word EqualCountTerminal}
    (h : word ∈
      GeneralGrammar.GeneratedLanguage StrictABCGreaterGrammar) :
    Word.Count EqualCountTerminal.a word >
        Word.Count EqualCountTerminal.b word ∧
      Word.Count EqualCountTerminal.b word >
        Word.Count EqualCountTerminal.c word := by
  have hderives :
      GeneralGrammar.Derives StrictABCGreaterGrammar
        [strictABCGreaterN StrictABCGreaterNT.start]
        (SententialForm.terminalWord word) := by
    simpa [GeneralGrammar.GeneratedLanguage, StrictABCGreaterGrammar,
      strictABCGreaterN, ggNonterminal] using h
  have hmargin :=
    strictABCGreater_derives_preserves_margin hderives
      strictABCGreater_start_margin
  simpa [strictABCGreaterMargin, strictABCGreaterTotalA,
    strictABCGreaterTotalB, strictABCGreaterTotalC,
    sententialCountTerminal_terminalWord,
    sententialCountNonterminal_terminalWord] using hmargin

/-!
The strict three-way grammar is used mainly as a count-invariant example. It
guarantees a strict inequality among the three terminal counts, and the concrete
derivation below witnesses a small generated word.
-/

def strictABCGreaterAABWord : Word EqualCountTerminal :=
  [EqualCountTerminal.a, EqualCountTerminal.a, EqualCountTerminal.b]

theorem strictABCGreaterGrammar_generates_aab :
    strictABCGreaterAABWord ∈
      GeneralGrammar.GeneratedLanguage StrictABCGreaterGrammar := by
  let S := strictABCGreaterN StrictABCGreaterNT.start
  let P := strictABCGreaterN StrictABCGreaterNT.pair
  let X := strictABCGreaterN StrictABCGreaterNT.extraA
  let R := strictABCGreaterN StrictABCGreaterNT.done
  let A := strictABCGreaterN StrictABCGreaterNT.markA
  let B := strictABCGreaterN StrictABCGreaterNT.markB
  let a := strictABCGreaterT EqualCountTerminal.a
  let b := strictABCGreaterT EqualCountTerminal.b
  have h1 : GeneralGrammar.Yields StrictABCGreaterGrammar [S] [P] := by
    simpa [S, P] using
      general_yields_of_production (G := StrictABCGreaterGrammar)
        StrictABCGreaterProduces.toPair [] []
  have h2 :
      GeneralGrammar.Yields StrictABCGreaterGrammar [P] [X, A, B] := by
    simpa [P, X, A, B] using
      general_yields_of_production (G := StrictABCGreaterGrammar)
        StrictABCGreaterProduces.endPair [] []
  have h3 :
      GeneralGrammar.Yields StrictABCGreaterGrammar [X, A, B]
        [R, A, A, B] := by
    simpa [X, R, A, B] using
      general_yields_of_production (G := StrictABCGreaterGrammar)
        StrictABCGreaterProduces.endExtraA [] [A, B]
  have h4 :
      GeneralGrammar.Yields StrictABCGreaterGrammar [R, A, A, B]
        [A, A, B] := by
    simpa [R, A, B] using
      general_yields_of_production (G := StrictABCGreaterGrammar)
        StrictABCGreaterProduces.finish [] [A, A, B]
  have h5 :
      GeneralGrammar.Yields StrictABCGreaterGrammar [A, A, B]
        [a, A, B] := by
    simpa [A, B, a] using
      general_yields_of_production (G := StrictABCGreaterGrammar)
        StrictABCGreaterProduces.emitA [] [A, B]
  have h6 :
      GeneralGrammar.Yields StrictABCGreaterGrammar [a, A, B]
        [a, a, B] := by
    simpa [A, B, a] using
      general_yields_of_production (G := StrictABCGreaterGrammar)
        StrictABCGreaterProduces.emitA [a] [B]
  have h7 :
      GeneralGrammar.Yields StrictABCGreaterGrammar [a, a, B]
        [a, a, b] := by
    simpa [A, B, a, b] using
      general_yields_of_production (G := StrictABCGreaterGrammar)
        StrictABCGreaterProduces.emitB [a, a] []
  have hderives :
      GeneralGrammar.Derives StrictABCGreaterGrammar [S] [a, a, b] :=
    GeneralGrammar.Derives.step h1
      (GeneralGrammar.Derives.step h2
        (GeneralGrammar.Derives.step h3
          (GeneralGrammar.Derives.step h4
            (GeneralGrammar.Derives.step h5
              (GeneralGrammar.Derives.step h6
                (GeneralGrammar.Derives.step h7
                  (GeneralGrammar.Derives.refl [a, a, b])))))))
  simpa [GeneralGrammar.GeneratedLanguage, StrictABCGreaterGrammar,
    strictABCGreaterAABWord, SententialForm.terminalWord, S, a, b] using
    hderives

/-!
# Unary Squares

The square grammar generates words `a^(n^2)`. Its marker phases simulate
building an `n` by `n` grid and then emitting one `a` for each cell. The
theorems prove both a family of generated square words and a concrete
derivation of `aaaa`.
-/

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

theorem squareGrammar_finite_production_generated :
    FiniteProductionGeneralLanguage
      (GeneralGrammar.GeneratedLanguage SquareGrammar) := by
  exists SquareNT
  exists SquareGrammar
  constructor
  · exact squareGrammar_has_finite_productions
  · intro w
    rfl

def squareWord (n : Nat) : Word SquareTerminal :=
  Word.RepeatSymbol SquareTerminal.a (n * n)

def squareLanguage : Language SquareTerminal :=
  fun word => exists n, word = squareWord n

/-!
The forms below name the stages of the square derivation. The grammar first
creates {lit}`n` row markers and {lit}`n` moving {lit}`b` markers. Each moving
marker crosses all rows, adding one terminal {lit}`a` to every row; after
{lit}`n` passes, the rows contain {lit}`n * n` terminals.
-/

def squareTerminalAForm (n : Nat) :
    SententialForm SquareTerminal SquareNT :=
  SententialForm.terminalWord (Word.RepeatSymbol SquareTerminal.a n)

def squareBForm (n : Nat) :
    SententialForm SquareTerminal SquareNT :=
  Word.RepeatSymbol (squareN SquareNT.b) n

def squareMarkerAForm (n : Nat) :
    SententialForm SquareTerminal SquareNT :=
  Word.RepeatSymbol (squareN SquareNT.markA) n

def squareRows (rowWidth rows : Nat) :
    SententialForm SquareTerminal SquareNT :=
  match rows with
  | 0 => []
  | rows + 1 =>
      [squareN SquareNT.markA] ++ squareTerminalAForm rowWidth ++
        squareRows rowWidth rows

theorem squareRows_zero_eq_markerAForm (n : Nat) :
    squareRows 0 n = squareMarkerAForm n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change [squareN SquareNT.markA] ++ squareTerminalAForm 0 ++
          squareRows 0 n =
        squareMarkerAForm (Nat.succ n)
      rw [ih]
      rfl

def squareGrowForm (n : Nat) :
    SententialForm SquareTerminal SquareNT :=
  [squareN SquareNT.d] ++ squareBForm n ++ [squareN SquareNT.t] ++
    squareMarkerAForm n ++ [squareN SquareNT.e]

def squareProcessForm (remaining rowWidth rows : Nat) :
    SententialForm SquareTerminal SquareNT :=
  [squareN SquareNT.d] ++ squareBForm remaining ++
    squareRows rowWidth rows ++ [squareN SquareNT.e]

theorem squareBForm_succ_eq_append (n : Nat) :
    squareBForm (n + 1) =
      squareBForm n ++ [squareN SquareNT.b] := by
  simpa [squareBForm] using
    repeatSymbol_succ_eq_append (squareN SquareNT.b) n

/-!
The generation proof follows the stage names. Grow the row and mover markers,
process every mover through every row, then remove the control markers while
concatenating the terminal rows into one unary word.
-/

theorem square_t_grow_derives (n : Nat) :
    GeneralGrammar.Derives SquareGrammar
      [squareN SquareNT.d, squareN SquareNT.t, squareN SquareNT.e]
      (squareGrowForm n) := by
  induction n with
  | zero =>
      simpa [squareGrowForm, squareBForm, squareMarkerAForm,
        Word.RepeatSymbol] using
        (GeneralGrammar.Derives.refl (G := SquareGrammar)
          [squareN SquareNT.d, squareN SquareNT.t, squareN SquareNT.e])
  | succ n ih =>
      have hstep :
          GeneralGrammar.Yields SquareGrammar
            (squareGrowForm n)
            ([squareN SquareNT.d] ++ squareBForm n ++
              [squareN SquareNT.b, squareN SquareNT.t,
                squareN SquareNT.markA] ++
              squareMarkerAForm n ++ [squareN SquareNT.e]) := by
        simpa [squareGrowForm, List.append_assoc] using
          general_yields_of_production (G := SquareGrammar)
            SquareProduces.grow
            ([squareN SquareNT.d] ++ squareBForm n)
            (squareMarkerAForm n ++ [squareN SquareNT.e])
      have hall := GeneralGrammar.Derives.step hstep
        (GeneralGrammar.Derives.refl _)
      have htail := GeneralGrammar.derives_trans ih hall
      simpa [squareGrowForm, squareBForm_succ_eq_append,
        squareMarkerAForm, Word.RepeatSymbol, List.append_assoc] using htail

theorem square_start_to_process_zero_derives (n : Nat) :
    GeneralGrammar.Derives SquareGrammar [squareN SquareNT.start]
      (squareProcessForm n 0 n) := by
  have hstart :
      GeneralGrammar.Yields SquareGrammar [squareN SquareNT.start]
        [squareN SquareNT.d, squareN SquareNT.t, squareN SquareNT.e] := by
    simpa using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.start [] []
  have hgrow := square_t_grow_derives n
  have hstop :
      GeneralGrammar.Yields SquareGrammar (squareGrowForm n)
        ([squareN SquareNT.d] ++ squareBForm n ++
          squareMarkerAForm n ++ [squareN SquareNT.e]) := by
    simpa [squareGrowForm, List.append_assoc] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.stop ([squareN SquareNT.d] ++ squareBForm n)
        (squareMarkerAForm n ++ [squareN SquareNT.e])
  have hall := GeneralGrammar.Derives.step hstart
    (GeneralGrammar.derives_trans hgrow (GeneralGrammar.yields_derives hstop))
  simpa [squareProcessForm, squareRows, squareMarkerAForm,
    squareRows_zero_eq_markerAForm, squareTerminalAForm, Word.RepeatSymbol,
    SententialForm.terminalWord, List.append_assoc] using hall

theorem square_move_b_right_over_terminal_as
    (n : Nat) (pre suffix : SententialForm SquareTerminal SquareNT) :
    GeneralGrammar.Derives SquareGrammar
      (pre ++ [squareN SquareNT.b] ++ squareTerminalAForm n ++ suffix)
      (pre ++ squareTerminalAForm n ++ [squareN SquareNT.b] ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [squareTerminalAForm, Word.RepeatSymbol,
        SententialForm.terminalWord] using
        (GeneralGrammar.Derives.refl (G := SquareGrammar)
          (pre ++ [squareN SquareNT.b] ++ suffix))
  | succ n ih =>
      let B := squareN SquareNT.b
      let a := squareT SquareTerminal.a
      have hstep :
          GeneralGrammar.Yields SquareGrammar
            (pre ++ [B, a] ++ squareTerminalAForm n ++ suffix)
            (pre ++ [a, B] ++ squareTerminalAForm n ++ suffix) := by
        simpa [B, a, List.append_assoc] using
          general_yields_of_production (G := SquareGrammar)
            SquareProduces.moveBa pre (squareTerminalAForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives SquareGrammar
            (pre ++ [a, B] ++ squareTerminalAForm n ++ suffix)
            (pre ++ [a] ++ squareTerminalAForm n ++ [B] ++ suffix) := by
        simpa [B, a, List.append_assoc] using ih (pre ++ [a])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [squareTerminalAForm, Word.RepeatSymbol,
        SententialForm.terminalWord, B, a, List.append_assoc] using hall

theorem square_move_b_right_over_rows
    (rowWidth rows : Nat)
    (pre suffix : SententialForm SquareTerminal SquareNT) :
    GeneralGrammar.Derives SquareGrammar
      (pre ++ [squareN SquareNT.b] ++ squareRows rowWidth rows ++ suffix)
      (pre ++ squareRows (rowWidth + 1) rows ++
        [squareN SquareNT.b] ++ suffix) := by
  induction rows generalizing pre with
  | zero =>
      simpa [squareRows] using
        (GeneralGrammar.Derives.refl (G := SquareGrammar)
          (pre ++ [squareN SquareNT.b] ++ suffix))
  | succ rows ih =>
      let A := squareN SquareNT.markA
      let B := squareN SquareNT.b
      let a := squareT SquareTerminal.a
      have hstep :
          GeneralGrammar.Yields SquareGrammar
            (pre ++ [B, A] ++ squareTerminalAForm rowWidth ++
              squareRows rowWidth rows ++ suffix)
            (pre ++ [A, a, B] ++ squareTerminalAForm rowWidth ++
              squareRows rowWidth rows ++ suffix) := by
        simpa [A, B, a, List.append_assoc] using
          general_yields_of_production (G := SquareGrammar)
            SquareProduces.moveBA pre
            (squareTerminalAForm rowWidth ++ squareRows rowWidth rows ++
              suffix)
      have hmoveAs :
          GeneralGrammar.Derives SquareGrammar
            (pre ++ [A, a, B] ++ squareTerminalAForm rowWidth ++
              squareRows rowWidth rows ++ suffix)
            (pre ++ [A, a] ++ squareTerminalAForm rowWidth ++
              [B] ++ squareRows rowWidth rows ++ suffix) := by
        simpa [A, B, a, List.append_assoc] using
          square_move_b_right_over_terminal_as rowWidth
            (pre ++ [A, a]) (squareRows rowWidth rows ++ suffix)
      have hrest :
          GeneralGrammar.Derives SquareGrammar
            (pre ++ [A, a] ++ squareTerminalAForm rowWidth ++
              [B] ++ squareRows rowWidth rows ++ suffix)
            (pre ++ [A, a] ++ squareTerminalAForm rowWidth ++
              squareRows (rowWidth + 1) rows ++ [B] ++ suffix) := by
        simpa [A, B, a, squareTerminalAForm, Word.RepeatSymbol,
          SententialForm.terminalWord, List.append_assoc] using
          ih (pre ++ [A] ++ squareTerminalAForm (rowWidth + 1))
      have hall := GeneralGrammar.Derives.step hstep
        (GeneralGrammar.derives_trans hmoveAs hrest)
      simpa [squareRows, A, B, a, squareTerminalAForm, Word.RepeatSymbol,
        SententialForm.terminalWord, List.append_assoc] using hall

theorem square_process_one_b_derives
    (rowWidth rows : Nat)
    (pre : SententialForm SquareTerminal SquareNT) :
    GeneralGrammar.Derives SquareGrammar
      (pre ++ [squareN SquareNT.b] ++ squareRows rowWidth rows ++
        [squareN SquareNT.e])
      (pre ++ squareRows (rowWidth + 1) rows ++ [squareN SquareNT.e]) := by
  have hmove :=
    square_move_b_right_over_rows rowWidth rows pre [squareN SquareNT.e]
  have hremove :
      GeneralGrammar.Yields SquareGrammar
        (pre ++ squareRows (rowWidth + 1) rows ++
          [squareN SquareNT.b, squareN SquareNT.e])
        (pre ++ squareRows (rowWidth + 1) rows ++
          [squareN SquareNT.e]) := by
    simpa [List.append_assoc] using
      general_yields_of_production (G := SquareGrammar)
        SquareProduces.removeBE
        (pre ++ squareRows (rowWidth + 1) rows) []
  have hremoveDerives :
      GeneralGrammar.Derives SquareGrammar
        (pre ++ squareRows (rowWidth + 1) rows ++
          [squareN SquareNT.b] ++ [squareN SquareNT.e])
        (pre ++ squareRows (rowWidth + 1) rows ++
          [squareN SquareNT.e]) := by
    simpa [List.append_assoc] using GeneralGrammar.yields_derives hremove
  exact GeneralGrammar.derives_trans hmove hremoveDerives

theorem square_process_all_b_derives
    (rows rowWidth remaining : Nat) :
    GeneralGrammar.Derives SquareGrammar
      (squareProcessForm remaining rowWidth rows)
      (squareProcessForm 0 (rowWidth + remaining) rows) := by
  induction remaining generalizing rowWidth with
  | zero =>
      simpa [squareProcessForm, squareBForm, Word.RepeatSymbol] using
        (GeneralGrammar.Derives.refl (G := SquareGrammar)
          (squareProcessForm 0 rowWidth rows))
  | succ remaining ih =>
      have hpass :
          GeneralGrammar.Derives SquareGrammar
            (squareProcessForm (remaining + 1) rowWidth rows)
            (squareProcessForm remaining (rowWidth + 1) rows) := by
        simpa [squareProcessForm, squareBForm_succ_eq_append,
          List.append_assoc] using
          square_process_one_b_derives rowWidth rows
            ([squareN SquareNT.d] ++ squareBForm remaining)
      have hrest := ih (rowWidth + 1)
      have hall := GeneralGrammar.derives_trans hpass hrest
      have hnat : rowWidth + (remaining + 1) = rowWidth + 1 + remaining := by
        omega
      simpa [squareProcessForm, hnat, List.append_assoc] using hall

theorem square_move_d_right_over_terminal_as
    (n : Nat) (pre suffix : SententialForm SquareTerminal SquareNT) :
    GeneralGrammar.Derives SquareGrammar
      (pre ++ [squareN SquareNT.d] ++ squareTerminalAForm n ++ suffix)
      (pre ++ squareTerminalAForm n ++ [squareN SquareNT.d] ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [squareTerminalAForm, Word.RepeatSymbol,
        SententialForm.terminalWord] using
        (GeneralGrammar.Derives.refl (G := SquareGrammar)
          (pre ++ [squareN SquareNT.d] ++ suffix))
  | succ n ih =>
      let D := squareN SquareNT.d
      let a := squareT SquareTerminal.a
      have hstep :
          GeneralGrammar.Yields SquareGrammar
            (pre ++ [D, a] ++ squareTerminalAForm n ++ suffix)
            (pre ++ [a, D] ++ squareTerminalAForm n ++ suffix) := by
        simpa [D, a, List.append_assoc] using
          general_yields_of_production (G := SquareGrammar)
            SquareProduces.moveDa pre (squareTerminalAForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives SquareGrammar
            (pre ++ [a, D] ++ squareTerminalAForm n ++ suffix)
            (pre ++ [a] ++ squareTerminalAForm n ++ [D] ++ suffix) := by
        simpa [D, a, List.append_assoc] using ih (pre ++ [a])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [squareTerminalAForm, Word.RepeatSymbol,
        SententialForm.terminalWord, D, a, List.append_assoc] using hall

theorem square_terminal_rows_append (rowWidth rows : Nat) :
    squareTerminalAForm rowWidth ++
        SententialForm.terminalWord
          (Word.RepeatSymbol SquareTerminal.a (rowWidth * rows)) =
      SententialForm.terminalWord
        (Word.RepeatSymbol SquareTerminal.a (rowWidth * (rows + 1))) := by
  have hnat : rowWidth * (rows + 1) = rowWidth + rowWidth * rows := by
    rw [Nat.mul_succ]
    omega
  rw [hnat]
  simp [squareTerminalAForm, SententialForm.terminalWord,
    Word.RepeatSymbol, List.replicate_append_replicate]

theorem square_finish_rows_derives (rowWidth rows : Nat) :
    GeneralGrammar.Derives SquareGrammar
      ([squareN SquareNT.d] ++ squareRows rowWidth rows ++
        [squareN SquareNT.e])
      (SententialForm.terminalWord
        (Word.RepeatSymbol SquareTerminal.a (rowWidth * rows))) := by
  induction rows with
  | zero =>
      have hfinish :
          GeneralGrammar.Yields SquareGrammar
            [squareN SquareNT.d, squareN SquareNT.e] [] := by
        simpa using
          general_yields_of_production (G := SquareGrammar)
            SquareProduces.finish [] []
      simpa [squareRows, Word.RepeatSymbol,
        SententialForm.terminalWord] using
        GeneralGrammar.yields_derives hfinish
  | succ rows ih =>
      have hremove :
          GeneralGrammar.Yields SquareGrammar
            ([squareN SquareNT.d, squareN SquareNT.markA] ++
              squareTerminalAForm rowWidth ++ squareRows rowWidth rows ++
              [squareN SquareNT.e])
            ([squareN SquareNT.d] ++ squareTerminalAForm rowWidth ++
              squareRows rowWidth rows ++ [squareN SquareNT.e]) := by
        simpa [List.append_assoc] using
          general_yields_of_production (G := SquareGrammar)
            SquareProduces.removeDA []
            (squareTerminalAForm rowWidth ++ squareRows rowWidth rows ++
              [squareN SquareNT.e])
      have hmove :
          GeneralGrammar.Derives SquareGrammar
            ([squareN SquareNT.d] ++ squareTerminalAForm rowWidth ++
              squareRows rowWidth rows ++ [squareN SquareNT.e])
            (squareTerminalAForm rowWidth ++ [squareN SquareNT.d] ++
              squareRows rowWidth rows ++ [squareN SquareNT.e]) := by
        simpa [List.append_assoc] using
          square_move_d_right_over_terminal_as rowWidth []
            (squareRows rowWidth rows ++ [squareN SquareNT.e])
      have hrest :
          GeneralGrammar.Derives SquareGrammar
            (squareTerminalAForm rowWidth ++ [squareN SquareNT.d] ++
              squareRows rowWidth rows ++ [squareN SquareNT.e])
            (squareTerminalAForm rowWidth ++
              SententialForm.terminalWord
                (Word.RepeatSymbol SquareTerminal.a (rowWidth * rows))) := by
        simpa [List.append_assoc] using
          general_derives_context ih (squareTerminalAForm rowWidth) []
      have hall := GeneralGrammar.Derives.step hremove
        (GeneralGrammar.derives_trans hmove hrest)
      simpa [squareRows, square_terminal_rows_append, List.append_assoc] using
        hall

theorem square_words_generated (n : Nat) :
    squareWord n ∈ GeneralGrammar.GeneratedLanguage SquareGrammar := by
  have hstart := square_start_to_process_zero_derives n
  have hprocess := square_process_all_b_derives n 0 n
  have hfinish := square_finish_rows_derives n n
  have hprocess' :
      GeneralGrammar.Derives SquareGrammar
        (squareProcessForm n 0 n)
        ([squareN SquareNT.d] ++ squareRows n n ++ [squareN SquareNT.e]) := by
    simpa [squareProcessForm] using hprocess
  have hall := GeneralGrammar.derives_trans hstart
    (GeneralGrammar.derives_trans hprocess' hfinish)
  simpa [GeneralGrammar.GeneratedLanguage, SquareGrammar, squareWord,
    squareN, ggNonterminal] using hall

theorem square_language_subset_generated {word : Word SquareTerminal}
    (h : word ∈ squareLanguage) :
    word ∈ GeneralGrammar.GeneratedLanguage SquareGrammar := by
  rcases h with ⟨n, hword⟩
  rw [hword]
  exact square_words_generated n

/-!
The remaining square lemmas are soundness checks. They classify every reachable
sentential form into one of the derivation stages above; if a derivation is
already terminal, that terminal word must be one of the square-length words.
-/

def squareFinishRowsForm (rowWidth processed remaining : Nat) :
    SententialForm SquareTerminal SquareNT :=
  squareTerminalAForm (rowWidth * processed) ++ [squareN SquareNT.d] ++
    squareRows rowWidth remaining ++ [squareN SquareNT.e]

def squareFinishMoveForm
    (rowWidth processed moved remaining : Nat) :
    SententialForm SquareTerminal SquareNT :=
  squareTerminalAForm (rowWidth * processed + moved) ++
    [squareN SquareNT.d] ++
      squareTerminalAForm (rowWidth - moved) ++
        squareRows rowWidth remaining ++ [squareN SquareNT.e]

inductive SquareDerivationShape :
    SententialForm SquareTerminal SquareNT -> Prop where
  | start :
      SquareDerivationShape [squareN SquareNT.start]
  | grow (n : Nat) :
      SquareDerivationShape (squareGrowForm n)
  | process (total remaining rowWidth : Nat)
      (hbalance : rowWidth + remaining = total) :
      SquareDerivationShape
        (squareProcessForm remaining rowWidth total)
  | finishRows (rowWidth processed remaining : Nat)
      (hbalance : processed + remaining = rowWidth) :
      SquareDerivationShape
        (squareFinishRowsForm rowWidth processed remaining)
  | finishMove (rowWidth processed moved remaining : Nat)
      (hmoved : moved <= rowWidth)
      (hbalance : processed + 1 + remaining = rowWidth) :
      SquareDerivationShape
        (squareFinishMoveForm rowWidth processed moved remaining)
  | terminal (n : Nat) :
      SquareDerivationShape
        (SententialForm.terminalWord (squareWord n))

theorem square_start_form_count_start :
    SententialCountNonterminal SquareNT.start [squareN SquareNT.start] = 1 := by
  simp [SententialCountNonterminal, squareN, ggNonterminal]

theorem squareTerminalAForm_count_nonterminal (A : SquareNT) (n : Nat) :
    SententialCountNonterminal A (squareTerminalAForm n) = 0 := by
  simp [squareTerminalAForm, sententialCountNonterminal_terminalWord]

theorem squareBForm_count_d (n : Nat) :
    SententialCountNonterminal SquareNT.d (squareBForm n) = 0 := by
  simpa [squareBForm] using
    (sententialCountNonterminal_repeat_nonterminal_of_ne
      (terminal := SquareTerminal) (A := SquareNT.d) (B := SquareNT.b)
      (by intro h; cases h) n)

theorem squareMarkerAForm_count_d (n : Nat) :
    SententialCountNonterminal SquareNT.d (squareMarkerAForm n) = 0 := by
  simpa [squareMarkerAForm] using
    (sententialCountNonterminal_repeat_nonterminal_of_ne
      (terminal := SquareTerminal) (A := SquareNT.d)
      (B := SquareNT.markA) (by intro h; cases h) n)

theorem squareRows_count_d (rowWidth rows : Nat) :
    SententialCountNonterminal SquareNT.d
      (squareRows rowWidth rows) = 0 := by
  induction rows with
  | zero =>
      rfl
  | succ rows ih =>
      simp [squareRows, sententialCountNonterminal_append,
        squareTerminalAForm_count_nonterminal, ih, squareN,
        ggNonterminal, SententialCountNonterminal]

theorem squareGrowForm_count_d (n : Nat) :
    SententialCountNonterminal SquareNT.d (squareGrowForm n) = 1 := by
  simp [squareGrowForm, sententialCountNonterminal_append,
    squareBForm_count_d, squareMarkerAForm_count_d, squareN,
    ggNonterminal, SententialCountNonterminal]

theorem squareProcessForm_count_d
    (remaining rowWidth rows : Nat) :
    SententialCountNonterminal SquareNT.d
      (squareProcessForm remaining rowWidth rows) = 1 := by
  simp [squareProcessForm, sententialCountNonterminal_append,
    squareBForm_count_d, squareRows_count_d, squareN,
    ggNonterminal, SententialCountNonterminal]

theorem squareFinishRowsForm_count_d
    (rowWidth processed remaining : Nat) :
    SententialCountNonterminal SquareNT.d
      (squareFinishRowsForm rowWidth processed remaining) = 1 := by
  simp [squareFinishRowsForm, sententialCountNonterminal_append,
    squareTerminalAForm_count_nonterminal, squareRows_count_d, squareN,
    ggNonterminal, SententialCountNonterminal]

theorem squareFinishMoveForm_count_d
    (rowWidth processed moved remaining : Nat) :
    SententialCountNonterminal SquareNT.d
      (squareFinishMoveForm rowWidth processed moved remaining) = 1 := by
  simp [squareFinishMoveForm, sententialCountNonterminal_append,
    squareTerminalAForm_count_nonterminal, squareRows_count_d, squareN,
    ggNonterminal, SententialCountNonterminal]

theorem square_derivation_shape_terminal_square
    {sf : SententialForm SquareTerminal SquareNT}
    (hshape : SquareDerivationShape sf)
    {word : Word SquareTerminal}
    (hsf : sf = SententialForm.terminalWord word) :
    word ∈ squareLanguage := by
  cases hshape with
  | start =>
      exact False.elim
        (sententialCountNonterminal_terminal_absurd
          square_start_form_count_start hsf)
  | grow n =>
      exact False.elim
        (sententialCountNonterminal_terminal_absurd
          (squareGrowForm_count_d n) hsf)
  | process total remaining rowWidth hbalance =>
      exact False.elim
        (sententialCountNonterminal_terminal_absurd
          (squareProcessForm_count_d remaining rowWidth total) hsf)
  | finishRows rowWidth processed remaining hbalance =>
      exact False.elim
        (sententialCountNonterminal_terminal_absurd
          (squareFinishRowsForm_count_d rowWidth processed remaining) hsf)
  | finishMove rowWidth processed moved remaining hmoved hbalance =>
      exact False.elim
        (sententialCountNonterminal_terminal_absurd
          (squareFinishMoveForm_count_d rowWidth processed moved remaining)
          hsf)
  | terminal n =>
      have hword : squareWord n = word := by
        have hto := congrArg SententialForm.toWord? hsf
        simpa [SententialForm.terminalWord_toWord] using hto
      exists n
      exact hword.symm

theorem square_derivation_shape_terminal_square_of_terminal
    {word : Word SquareTerminal}
    (hshape : SquareDerivationShape (SententialForm.terminalWord word)) :
    word ∈ squareLanguage :=
  square_derivation_shape_terminal_square hshape rfl

def fourAsWord : Word SquareTerminal :=
  [SquareTerminal.a, SquareTerminal.a, SquareTerminal.a, SquareTerminal.a]

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

/-!
# Powers of Two

The final example uses a doubling phase: each pass duplicates the current
markers and returns to the left before either doubling again or finishing.
-/

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

/-!
As above, the finite-production theorem only checks that the displayed rules
are exactly the grammar's rules. The final concrete derivation shows the
intended doubling behavior on the word of length four.
-/

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

/-!
The sample derivation demonstrates generation of four `a`s by running two
doubling passes and then emitting the accumulated markers.
-/

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
