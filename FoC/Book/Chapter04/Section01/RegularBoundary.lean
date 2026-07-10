import FoC.Book.Chapter03.Section07
import FoC.Book.Chapter04.Section01.AnBn

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section01

/-!
# Chapter 4, Section 4.1: The Regular Boundary of Context-Free Languages

This submodule assembles the book's corollary that the inclusion of regular
languages in context-free languages is strict: the language {lit}`a^n b^n` is
context-free but not regular, so there exist context-free languages which are
not regular.

The context-free half is {name}`anbn_context_free` from
{module}`FoC.Book.Chapter04.Section01.AnBn`. The non-regularity half was proved by
a pumping argument in {module}`FoC.Book.Chapter03.Section07`, but over
Chapter 3's own two-letter alphabet type, which is distinct from (though
isomorphic to) this chapter's {name}`AB`. The declarations below transport
non-regularity across that alphabet renaming: a DFA over one alphabet can be
relabeled into a DFA over the other, so a regular {lit}`a^n b^n` language on
the Chapter 4 alphabet would make Chapter 3's {lit}`a^n b^n` language regular
as well, contradicting the pumping result.
-/

open Foundation
open Languages
open Grammars

/-!
## Alphabet Renaming

The two chapters name their two-letter alphabets independently. The renaming
functions below are mutually inverse, and both {lit}`a^n b^n` block words map
to each other under them.
-/

def abFromChapter03 : Chapter03.Section01.AB -> AB
  | Chapter03.Section01.AB.a => AB.a
  | Chapter03.Section01.AB.b => AB.b

def abToChapter03 : AB -> Chapter03.Section01.AB
  | AB.a => Chapter03.Section01.AB.a
  | AB.b => Chapter03.Section01.AB.b

theorem abToChapter03_abFromChapter03 (c : Chapter03.Section01.AB) :
    abToChapter03 (abFromChapter03 c) = c := by
  cases c <;> rfl

theorem map_abFromChapter03_roundtrip (w : Word Chapter03.Section01.AB) :
    List.map abToChapter03 (List.map abFromChapter03 w) = w := by
  induction w with
  | nil => rfl
  | cons c t ih =>
      simp only [List.map_cons, abToChapter03_abFromChapter03, ih]

theorem map_abFromChapter03_anbnWord (n : Nat) :
    List.map abFromChapter03
      (Word.Concat (Word.RepeatSymbol Chapter03.Section01.AB.a n)
        (Word.RepeatSymbol Chapter03.Section01.AB.b n)) = AnBnWord n := by
  simp [Word.Concat, Word.RepeatSymbol, AnBnWord, List.map_append,
    List.map_replicate, abFromChapter03]

theorem map_abToChapter03_anbnWord (n : Nat) :
    List.map abToChapter03 (AnBnWord n)
      = Word.Concat (Word.RepeatSymbol Chapter03.Section01.AB.a n)
        (Word.RepeatSymbol Chapter03.Section01.AB.b n) := by
  simp [Word.Concat, Word.RepeatSymbol, AnBnWord, List.map_append,
    List.map_replicate, abToChapter03]

/-!
## Relabeled Automata

Precomposing a DFA's transition function with a symbol renaming yields a DFA
whose accepted language is the preimage of the original language under the
word-level renaming. This is the transport step between the two alphabet
types.
-/

def RelabelDFA (f : beta -> alpha) (M : DFA alpha state) : DFA beta state where
  start := M.start
  step := fun q b => M.step q (f b)
  accept := M.accept
  statesFinite := M.statesFinite

theorem relabelDFA_runFrom (f : beta -> alpha) (M : DFA alpha state)
    (q : state) (w : Word beta) :
    DFA.RunFrom (RelabelDFA f M) q w = DFA.RunFrom M q (List.map f w) := by
  induction w generalizing q with
  | nil => rfl
  | cons c t ih => exact ih (M.step q (f c))

theorem relabelDFA_language (f : beta -> alpha) (M : DFA alpha state)
    (w : Word beta) :
    w ∈ DFA.Language (RelabelDFA f M) <-> List.map f w ∈ DFA.Language M := by
  have hrun : DFA.RunFrom (RelabelDFA f M) M.start w
      = DFA.RunFrom M M.start (List.map f w) :=
    relabelDFA_runFrom f M M.start w
  constructor
  · intro hw
    have hw' : (RelabelDFA f M).accept
        (DFA.RunFrom (RelabelDFA f M) M.start w) := hw
    rw [hrun] at hw'
    exact hw'
  · intro hw
    have hw' : M.accept (DFA.RunFrom M M.start (List.map f w)) := hw
    rw [← hrun] at hw'
    exact hw'

/-!
## The Boundary Corollary

If the Chapter 4 {lit}`a^n b^n` language were regular, some DFA would
recognize it, and the relabeled DFA would witness regularity of Chapter 3's
{lit}`a^n b^n` language, contradicting the pumping-lemma result. Together
with {name}`anbn_context_free`, this yields the book's corollary that the
context-free languages properly contain the regular languages.
-/

theorem anbn_language_not_regular :
    ¬ RegularLanguage.Regular AnBnLanguage := by
  intro hreg
  apply Chapter03.Section07.anbn_not_regular
  cases RegularLanguage.regular_is_dfa_recognizable hreg with
  | intro state hstate =>
      cases hstate with
      | intro M hM =>
          apply RegularLanguage.dfa_recognizable_regular
            Chapter03.Section01.ABAlphabet
          exists state
          exists RelabelDFA abFromChapter03 M
          intro w
          constructor
          · intro hw
            have hmem : List.map abFromChapter03 w ∈ AnBnLanguage :=
              (hM (List.map abFromChapter03 w)).mp
                ((relabelDFA_language abFromChapter03 M w).mp hw)
            cases hmem with
            | intro n hn =>
                exists n
                have hw_eq : w = List.map abToChapter03 (AnBnWord n) := by
                  rw [← hn, map_abFromChapter03_roundtrip]
                rw [hw_eq, map_abToChapter03_anbnWord]
          · intro hw
            cases hw with
            | intro n hn =>
                apply (relabelDFA_language abFromChapter03 M w).mpr
                apply (hM (List.map abFromChapter03 w)).mpr
                exists n
                rw [hn, map_abFromChapter03_anbnWord]

theorem exists_context_free_language_not_regular :
    exists L : Language AB,
      ContextFreeLanguage L ∧ ¬ RegularLanguage.Regular L := by
  exists AnBnLanguage
  constructor
  · exact anbn_context_free
  · exact anbn_language_not_regular

end Section01
end Chapter04
end Book
end FoC
