namespace FoC
namespace Languages

/-!
Words over an alphabet.

Used by:
- Chapter 3, Section 3.1: Languages
- Chapter 3, Section 3.2: Regular Expressions
- Chapter 3, Section 3.4: Finite-State Automata
- Chapter 3, Section 3.5: Nondeterministic Finite-State Automata
- Chapter 3, Section 3.7: Non-regular Languages
- Later grammar and computability chapters that use strings of symbols
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

def Count [DecidableEq alpha] (a : alpha) : Word alpha -> Nat
  | [] => 0
  | b :: w => (if b = a then 1 else 0) + Count a w

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

theorem reverse_concat (x y : Word alpha) :
    Reverse (Concat x y) = Concat (Reverse y) (Reverse x) := by
  simp [Reverse, Concat]

theorem repeatWord_zero (w : Word alpha) : RepeatWord w 0 = Empty :=
  rfl

theorem repeatWord_succ (w : Word alpha) (n : Nat) :
    RepeatWord w (n + 1) = Concat w (RepeatWord w n) :=
  rfl

theorem repeatSymbol_zero (a : alpha) : RepeatSymbol a 0 = Empty :=
  rfl

theorem length_repeatSymbol (a : alpha) (n : Nat) :
    Length (RepeatSymbol a n) = n := by
  simp [Length, RepeatSymbol]

theorem count_empty [DecidableEq alpha] (a : alpha) :
    Count a (Empty : Word alpha) = 0 :=
  rfl

theorem count_cons_same [DecidableEq alpha] (a : alpha) (w : Word alpha) :
    Count a (a :: w) = Count a w + 1 := by
  simp [Count, Nat.add_comm]

theorem count_cons_different [DecidableEq alpha] {a b : alpha} (h : b ≠ a)
    (w : Word alpha) : Count a (b :: w) = Count a w := by
  simp [Count, h]

end Word
end Languages
end FoC
