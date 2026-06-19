set_option doc.verso true

/-!
# Words

## Words as lists

Chapter 3 treats strings as finite words over an alphabet.  In Lean, a word is
represented by a list of alphabet symbols.  This file fixes that representation
and collects the basic operations used throughout the language, automata,
grammar, and computability developments.

## Book coordinates

Used by:
- Chapter 3, Section 3.1: Languages
- Chapter 3, Section 3.2: Regular Expressions
- Chapter 3, Section 3.4: Finite-State Automata
- Chapter 3, Section 3.5: Nondeterministic Finite-State Automata
- Chapter 3, Section 3.7: Non-regular Languages
- Later grammar and computability chapters that use strings of symbols
-/

namespace FoC
namespace Languages

/-!
# Word representation

Words are lists, with named constructors for the empty word, one-symbol words,
concatenation, length, and reversal. These names keep the book-facing Lean
statements close to the textbook notation.
-/

def Word (alpha : Type u) : Type u :=
  List alpha

namespace Word

def Empty : Word alpha :=
  []

def Symbol (a : alpha) : Word alpha :=
  [a]

def Concat (x y : Word alpha) : Word alpha :=
  List.append x y

def Length (w : Word alpha) : Nat :=
  w.length

def Reverse (w : Word alpha) : Word alpha :=
  w.reverse

def RepeatWord (w : Word alpha) : Nat -> Word alpha
  | 0 => []
  | n + 1 => List.append w (RepeatWord w n)

def RepeatSymbol (a : alpha) (n : Nat) : Word alpha :=
  List.replicate n a

/-!
# Counting symbols

The counting operation is used in non-regular-language and context-free
language examples where statements compare the number of occurrences of
particular alphabet symbols.
-/

def Count [DecidableEq alpha] (a : alpha) : Word alpha -> Nat
  | [] => 0
  | b :: w => (if b = a then 1 else 0) + Count a w

/-!
# Word algebra

These lemmas collect the algebra of empty words, associativity, reversal,
repetition, and symbol counts needed by later automata and pumping arguments.
-/

theorem length_empty : Length (Empty : Word alpha) = 0 :=
  rfl

theorem reverse_empty : Reverse (Empty : Word alpha) = Empty :=
  rfl

theorem concat_empty_left (w : Word alpha) : Concat Empty w = w :=
  rfl

theorem concat_empty_right (w : Word alpha) : Concat w Empty = w := by
  simp [Concat, Empty]

theorem concat_assoc (x y z : Word alpha) :
    Concat (Concat x y) z = Concat x (Concat y z) := by
  simp [Concat, List.append_assoc]

theorem length_concat (x y : Word alpha) :
    Length (Concat x y) = Length x + Length y := by
  simp [Length, Concat]

theorem repeatWord_succ (w : Word alpha) (n : Nat) :
    RepeatWord w (n + 1) = Concat w (RepeatWord w n) :=
  rfl

theorem repeatWord_concat_self (w : Word alpha) (n : Nat) :
    Concat (RepeatWord w n) w = Concat w (RepeatWord w n) := by
  induction n with
  | zero =>
      simp [RepeatWord, Concat]
  | succ n ih =>
      calc
        Concat (RepeatWord w (n + 1)) w =
            Concat (Concat w (RepeatWord w n)) w := rfl
        _ = Concat w (Concat (RepeatWord w n) w) := by
              simp [Concat, List.append_assoc]
        _ = Concat w (Concat w (RepeatWord w n)) := by
              rw [ih]
        _ = Concat w (RepeatWord w (n + 1)) := rfl

theorem length_repeatSymbol (a : alpha) (n : Nat) :
    Length (RepeatSymbol a n) = n := by
  simp [Length, RepeatSymbol]

theorem count_concat [DecidableEq alpha] (a : alpha) (x y : Word alpha) :
    Count a (Concat x y) = Count a x + Count a y := by
  unfold Concat
  induction x with
  | nil =>
      simp [Count]
  | cons b x ih =>
      change Count a (List.append x y) = Count a x + Count a y at ih
      by_cases h : b = a
      · simp [Count, h]
        have ih' : Count a (List.append x y) = Count a x + Count a y := ih
        change 1 + Count a (List.append x y) = 1 + Count a x + Count a y
        omega
      · simp [Count, h]
        simpa using ih

theorem count_repeatSymbol_same [DecidableEq alpha] (a : alpha) (n : Nat) :
    Count a (RepeatSymbol a n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show RepeatSymbol a (n + 1) = a :: RepeatSymbol a n by rfl]
      simp [Count, ih, Nat.add_comm]

theorem count_repeatSymbol_different [DecidableEq alpha] {a b : alpha}
    (h : b ≠ a) (n : Nat) :
    Count a (RepeatSymbol b n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show RepeatSymbol b (n + 1) = b :: RepeatSymbol b n by rfl]
      simp [Count, h, ih]

end Word
end Languages
end FoC
