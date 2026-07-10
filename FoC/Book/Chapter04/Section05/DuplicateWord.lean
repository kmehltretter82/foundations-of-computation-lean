import FoC.Book.Chapter04.Section05.Pumping

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section05

open Languages
open Grammars

/-!
# The Duplicate-Word Pumping Argument

This module records the completed counting core for the language
{lit}`{ w w }`. The remaining position argument is intentionally not stated
as a completed non-context-freeness theorem.
-/

/-!
## The Duplicate-Word Language

The book's second pumping example is {lit}`{ w w | w in {a,b}* }`. This module
proves the counting core of the argument: every duplicate word has an even
number of any fixed symbol, so a pumped word with five {lit}`b`s cannot be a
duplicate. That closes every decomposition whose pumped block {lit}`x z`
contains a {lit}`b`; see the later
{lit}`duplicate_pump_two_not_mem_of_middle_count_b_le_one` theorem.

The complementary case, where {lit}`x z` consists entirely of {lit}`a`s, cannot
be closed by any symbol count: duplicating an all-{lit}`a` block leaves every
symbol count even. Settling it needs the book's position argument over the four
{lit}`a`-blocks of {lit}`a^K b a^K b a^K b a^K b`, which is not formalized
here. The reusable count lemmas below are the honest partial result; the full
non-context-freeness theorem for {lit}`{ w w }` is left as future work.
-/

def duplicateWordLanguage : Language Section01.AB :=
  fun w => exists u : Word Section01.AB, w = Word.Concat u u

def duplicateSeedWord (n : Nat) : Word Section01.AB :=
  Word.Concat (Word.RepeatSymbol Section01.AB.a n)
    (Word.Concat (Word.Symbol Section01.AB.b)
      (Word.Concat (Word.RepeatSymbol Section01.AB.a n)
        (Word.Symbol Section01.AB.b)))

def duplicateBadWord (n : Nat) : Word Section01.AB :=
  Word.Concat (duplicateSeedWord n) (duplicateSeedWord n)

theorem duplicate_word_membership (w : Word Section01.AB) :
    w ∈ duplicateWordLanguage <->
      exists u : Word Section01.AB, w = Word.Concat u u :=
  Iff.rfl

theorem duplicateBadWord_mem (n : Nat) :
    duplicateBadWord n ∈ duplicateWordLanguage := by
  exists duplicateSeedWord n

theorem duplicateSeedWord_count_b (n : Nat) :
    Word.Count Section01.AB.b (duplicateSeedWord n) = 2 := by
  unfold duplicateSeedWord
  rw [Word.count_concat]
  rw [Word.count_repeatSymbol_different
    (a := Section01.AB.b) (b := Section01.AB.a)]
  rw [Word.count_concat]
  rw [Word.count_concat]
  rw [Word.count_repeatSymbol_different
    (a := Section01.AB.b) (b := Section01.AB.a)]
  · simp [Word.Count, Word.Symbol]
  · intro h
    cases h
  · intro h
    cases h

theorem duplicateBadWord_count_b (n : Nat) :
    Word.Count Section01.AB.b (duplicateBadWord n) = 4 := by
  unfold duplicateBadWord
  rw [Word.count_concat, duplicateSeedWord_count_b]

theorem duplicateSeedWord_length (n : Nat) :
    Word.Length (duplicateSeedWord n) = 2 * n + 2 := by
  unfold duplicateSeedWord
  simp [Word.Length, Word.Concat, Word.RepeatSymbol, Word.Symbol]
  lia

theorem duplicateBadWord_length (n : Nat) :
    Word.Length (duplicateBadWord n) = 4 * n + 4 := by
  unfold duplicateBadWord
  rw [Word.length_concat, duplicateSeedWord_length]
  lia

theorem duplicate_word_count_even
    (sym : Section01.AB) {w : Word Section01.AB}
    (hw : w ∈ duplicateWordLanguage) :
    exists n : Nat, Word.Count sym w = 2 * n := by
  rcases hw with ⟨u, hu⟩
  exists Word.Count sym u
  rw [hu, Word.count_concat]
  lia

theorem duplicate_word_not_count_b_five {w : Word Section01.AB}
    (hcount : Word.Count Section01.AB.b w = 5) :
    ¬ w ∈ duplicateWordLanguage := by
  intro hw
  rcases duplicate_word_count_even Section01.AB.b hw with ⟨n, hn⟩
  rw [hcount] at hn
  lia

theorem duplicate_pump_two_not_mem_of_xz_count_b_one
    {u x y z v : Word Section01.AB} {K : Nat}
    (hword : duplicateBadWord K = CFL.Concat5 u x y z v)
    (hcount : Word.Count Section01.AB.b (Word.Concat x z) = 1) :
    ¬ CFL.Pumped u x y z v 2 ∈ duplicateWordLanguage := by
  apply duplicate_word_not_count_b_five
  rw [cfl_pumped_two_count_symbol, ← hword, duplicateBadWord_count_b, hcount]

theorem duplicate_xz_count_b_le_middle_count_b
    (x y z : Word Section01.AB) :
    Word.Count Section01.AB.b (Word.Concat x z) <=
      Word.Count Section01.AB.b (CFL.Concat3 x y z) := by
  unfold CFL.Concat3
  repeat rw [Word.count_concat]
  lia

theorem duplicate_pump_two_not_mem_of_xz_count_b_pos_le_one
    {u x y z v : Word Section01.AB} {K : Nat}
    (hword : duplicateBadWord K = CFL.Concat5 u x y z v)
    (hpos : 0 < Word.Count Section01.AB.b (Word.Concat x z))
    (hle : Word.Count Section01.AB.b (Word.Concat x z) <= 1) :
    ¬ CFL.Pumped u x y z v 2 ∈ duplicateWordLanguage := by
  have hcount : Word.Count Section01.AB.b (Word.Concat x z) = 1 := by
    lia
  exact duplicate_pump_two_not_mem_of_xz_count_b_one hword hcount

theorem duplicate_pump_two_not_mem_of_middle_count_b_le_one
    {u x y z v : Word Section01.AB} {K : Nat}
    (hword : duplicateBadWord K = CFL.Concat5 u x y z v)
    (hpos : 0 < Word.Count Section01.AB.b (Word.Concat x z))
    (hmiddle :
      Word.Count Section01.AB.b (CFL.Concat3 x y z) <= 1) :
    ¬ CFL.Pumped u x y z v 2 ∈ duplicateWordLanguage := by
  exact duplicate_pump_two_not_mem_of_xz_count_b_pos_le_one hword hpos
    (Nat.le_trans (duplicate_xz_count_b_le_middle_count_b x y z) hmiddle)

end Section05
end Chapter04
end Book
end FoC
