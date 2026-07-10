import FoC.Book.Chapter04.Section06.UnarySquares.Basic

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section06

open Languages
open Grammars

/-!
# Shared Count and Occurrence Lemmas

Book: Section 4.6, third sample grammar (the unary-square language
{lit}`a^(n^2)`).

This module collects the nonterminal-count and unique-occurrence lemmas about
start, grow, and marker forms on which the soundness development in the
sibling modules {lit}`UnarySquares.Potential`, {lit}`UnarySquares.PostStop`,
and {lit}`UnarySquares.Reachability` builds. An earlier shape-classification
route toward completeness that used to live here (a
{lit}`SquareDerivationShape` predicate whose completeness was left as an
assumption) was superseded by the reachability invariant in
{lit}`UnarySquares.Reachability`, which proves the exact generated language
outright; the superseded route has been removed.
-/

theorem square_start_form_count_start :
    SententialCountNonterminal SquareNT.start [squareN SquareNT.start] = 1 := by
  simp [SententialCountNonterminal, squareN, ggNonterminal]

theorem squareTerminalAForm_count_nonterminal (A : SquareNT) (n : Nat) :
    SententialCountNonterminal A (squareTerminalAForm n) = 0 := by
  simp [squareTerminalAForm, sententialCountNonterminal_terminalWord]

theorem squareBForm_count_d (n : Nat) :
    SententialCountNonterminal SquareNT.d (squareBForm n) = 0 := by
  simpa [squareBForm] using!
    (sententialCountNonterminal_repeat_nonterminal_of_ne
      (terminal := SquareTerminal) (A := SquareNT.d) (B := SquareNT.b)
      (by intro h; cases h) n)

theorem squareMarkerAForm_count_d (n : Nat) :
    SententialCountNonterminal SquareNT.d (squareMarkerAForm n) = 0 := by
  simpa [squareMarkerAForm] using!
    (sententialCountNonterminal_repeat_nonterminal_of_ne
      (terminal := SquareTerminal) (A := SquareNT.d)
      (B := SquareNT.markA) (by intro h; cases h) n)

theorem squareGrowForm_count_d (n : Nat) :
    SententialCountNonterminal SquareNT.d (squareGrowForm n) = 1 := by
  simp [squareGrowForm, sententialCountNonterminal_append,
    squareBForm_count_d, squareMarkerAForm_count_d, squareN,
    ggNonterminal, SententialCountNonterminal]

theorem square_no_t_occurrence_absurd
    {sf u v : SententialForm SquareTerminal SquareNT}
    (hcount : SententialCountNonterminal SquareNT.t sf = 0)
    (h : sf = u ++ [squareN SquareNT.t] ++ v) : False := by
  have hc := congrArg (SententialCountNonterminal SquareNT.t) h
  rw [hcount, sententialCountNonterminal_append,
    sententialCountNonterminal_append] at hc
  simp [SententialCountNonterminal, squareN, ggNonterminal] at hc
  lia

theorem squareBForm_count_t (n : Nat) :
    SententialCountNonterminal SquareNT.t (squareBForm n) = 0 := by
  simpa [squareBForm] using!
    (sententialCountNonterminal_repeat_nonterminal_of_ne
      (terminal := SquareTerminal) (A := SquareNT.t) (B := SquareNT.b)
      (by intro h; cases h) n)

theorem squareMarkerAForm_count_t (n : Nat) :
    SententialCountNonterminal SquareNT.t (squareMarkerAForm n) = 0 := by
  simpa [squareMarkerAForm] using!
    (sententialCountNonterminal_repeat_nonterminal_of_ne
      (terminal := SquareTerminal) (A := SquareNT.t)
      (B := SquareNT.markA) (by intro h; cases h) n)

theorem squareGrowForm_tail_count_t (n : Nat) :
    SententialCountNonterminal SquareNT.t
      (squareMarkerAForm n ++ [squareN SquareNT.e]) = 0 := by
  simp [sententialCountNonterminal_append, squareMarkerAForm_count_t,
    SententialCountNonterminal, squareN, ggNonterminal]

/-!
The occurrence lemmas locate the unique {name}`SquareNT.t` head inside a grow
form: any decomposition that exhibits a {name}`SquareNT.t` must split the form
exactly at the head position. The reachability case analysis uses this to pin
down where a production can apply.
-/

theorem squareBForm_t_occurrence
    {tail u v : SententialForm SquareTerminal SquareNT} (n : Nat)
    (htail : SententialCountNonterminal SquareNT.t tail = 0)
    (h : squareBForm n ++ [squareN SquareNT.t] ++ tail =
      u ++ [squareN SquareNT.t] ++ v) :
    u = squareBForm n ∧ v = tail := by
  induction n generalizing u v with
  | zero =>
      simp [squareBForm, Word.RepeatSymbol] at h
      cases u with
      | nil =>
          simp at h
          exact ⟨rfl, h.symm⟩
      | cons _ rest =>
          simp at h
          have htailEq : tail = rest ++ [squareN SquareNT.t] ++ v := by
            simpa using h.right
          exact False.elim (square_no_t_occurrence_absurd htail htailEq)
  | succ n ih =>
      change squareN SquareNT.b ::
          (squareBForm n ++ [squareN SquareNT.t] ++ tail) =
        u ++ [squareN SquareNT.t] ++ v at h
      cases u with
      | nil =>
          simp [squareN, ggNonterminal] at h
      | cons head rest =>
          simp at h
          have hhead : head = squareN SquareNT.b := h.left.symm
          subst head
          have hrest : squareBForm n ++ [squareN SquareNT.t] ++ tail =
              rest ++ [squareN SquareNT.t] ++ v := by
            simpa using h.right
          cases ih hrest with
          | intro hrestEq hv =>
              constructor
              · rw [hrestEq]
                rfl
              · exact hv

theorem squareGrowForm_t_occurrence
    {u v : SententialForm SquareTerminal SquareNT} (n : Nat)
    (h : squareGrowForm n = u ++ [squareN SquareNT.t] ++ v) :
    u = [squareN SquareNT.d] ++ squareBForm n ∧
      v = squareMarkerAForm n ++ [squareN SquareNT.e] := by
  simp [squareGrowForm, List.append_assoc] at h
  cases u with
  | nil =>
      simp [squareN, ggNonterminal] at h
  | cons head rest =>
      simp at h
      have hhead : head = squareN SquareNT.d := h.left.symm
      subst head
      have htail : squareBForm n ++ [squareN SquareNT.t] ++
          (squareMarkerAForm n ++ [squareN SquareNT.e]) =
        rest ++ [squareN SquareNT.t] ++ v := by
        simpa [List.append_assoc] using h.right
      have hocc := squareBForm_t_occurrence n
        (squareGrowForm_tail_count_t n) htail
      constructor
      · rw [hocc.left]
        rfl
      · exact hocc.right

end Section06
end Chapter04
end Book
end FoC
