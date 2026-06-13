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

theorem cfg_generated_language_subset_general_generated
    (G : CFG terminal nonterminal) :
    Language.Subset (CFG.GeneratedLanguage G)
      (GeneralGrammar.GeneratedLanguage (GeneralGrammar.FromCFG G)) := by
  intro w hw
  exact cfg_generated_word_is_general_generated G hw

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

/-!
The count lemmas provide the invariant language used throughout the large
grammar examples. They relate sentential-form counts to terminal-word counts and
make append/repetition arithmetic available to the preservation proofs.
-/

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

theorem sentential_no_nonterminal_occurrence_absurd
    [DecidableEq nonterminal]
    {A : nonterminal} {sf u v : SententialForm terminal nonterminal}
    (hcount : SententialCountNonterminal A sf = 0)
    (h : sf = u ++ [ggNonterminal A] ++ v) : False := by
  have hc := congrArg (SententialCountNonterminal A) h
  rw [hcount, sententialCountNonterminal_append,
    sententialCountNonterminal_append] at hc
  simp [SententialCountNonterminal, ggNonterminal] at hc
  omega

theorem sentential_no_terminal_occurrence_absurd
    [DecidableEq terminal]
    {a : terminal} {sf u v : SententialForm terminal nonterminal}
    (hcount : SententialCountTerminal a sf = 0)
    (h : sf = u ++ [ggTerminal a] ++ v) : False := by
  have hc := congrArg (SententialCountTerminal a) h
  rw [hcount, sententialCountTerminal_append,
    sententialCountTerminal_append] at hc
  simp [SententialCountTerminal, ggTerminal] at hc
  omega

theorem sentential_unique_nonterminal_occurrence
    [DecidableEq nonterminal]
    {A : nonterminal}
    {pref tail u v : SententialForm terminal nonterminal}
    (hpref : SententialCountNonterminal A pref = 0)
    (htail : SententialCountNonterminal A tail = 0)
    (h : pref ++ [ggNonterminal A] ++ tail =
      u ++ [ggNonterminal A] ++ v) :
    u = pref ∧ v = tail := by
  induction pref generalizing u v with
  | nil =>
      simp at h
      cases u with
      | nil =>
          simp at h
          exact ⟨rfl, h.symm⟩
      | cons _ rest =>
          simp at h
          have htailEq : tail = rest ++ [ggNonterminal A] ++ v := by
            simpa using h.right
          exact False.elim
            (sentential_no_nonterminal_occurrence_absurd htail htailEq)
  | cons head rest ih =>
      cases u with
      | nil =>
          simp at h
          cases head with
          | terminal _ =>
              simp [ggNonterminal] at h
          | nonterminal B =>
              simp [ggNonterminal] at h
              have hBA : B = A := h.left
              subst B
              simp [SententialCountNonterminal] at hpref
      | cons uhead urest =>
          simp at h
          have hhead : uhead = head := h.left.symm
          subst uhead
          have hrestCount :
              SententialCountNonterminal A rest = 0 := by
            cases head with
            | terminal _ =>
                simpa [SententialCountNonterminal] using hpref
            | nonterminal B =>
                simp [SententialCountNonterminal] at hpref
                exact hpref.right
          have htailEq : rest ++ [ggNonterminal A] ++ tail =
              urest ++ [ggNonterminal A] ++ v := by
            simpa using h.right
          cases ih hrestCount htailEq with
          | intro hrestEq hv =>
              constructor
              · rw [hrestEq]
              · exact hv

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


end Section06
end Chapter04
end Book
end FoC
