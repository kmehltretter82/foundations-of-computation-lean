import FoC.Book.Chapter04.Section06.UnarySquares.Shape

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section06

open Languages
open Grammars

/-!
The square grammar now has a constructive completeness direction for every
square word. The named phase-shape theorem above is retained as a compact
terminal-state consequence, but the exact proof below uses a stronger
reachability invariant: start, growth, post-stop, and terminal-square states
are each preserved by every unrestricted one-step yield. Derivation induction
then gives the reverse generated-language inclusion without any remaining
shape-completeness assumption.
-/

def squareMiddleInversionsFrom (seenB : Nat) :
    SententialForm SquareTerminal SquareNT -> Nat
  | [] => 0
  | Symbol.nonterminal SquareNT.b :: rest =>
      squareMiddleInversionsFrom (seenB + 1) rest
  | Symbol.nonterminal SquareNT.markA :: rest =>
      seenB + squareMiddleInversionsFrom seenB rest
  | _ :: rest =>
      squareMiddleInversionsFrom seenB rest

def squareMiddleInversions (middle : SententialForm SquareTerminal SquareNT) :
    Nat :=
  squareMiddleInversionsFrom 0 middle

def squareMiddlePotential
    (middle : SententialForm SquareTerminal SquareNT) : Nat :=
  SententialCountTerminal SquareTerminal.a middle +
    squareMiddleInversions middle

/-!
For the square grammar's post-stop phase, the central invariant is the number
of terminal {lit}`a`s plus the number of remaining {lit}`B`-before-{lit}`A`
pairs. The unrestricted rule {lit}`BA -> AaB` preserves that sum by exchanging
one inversion for one emitted terminal.
-/

theorem squareMiddleInversionsFrom_trailing_b
    (seenB : Nat) (middle : SententialForm SquareTerminal SquareNT) :
    squareMiddleInversionsFrom seenB
        (middle ++ [squareN SquareNT.b]) =
      squareMiddleInversionsFrom seenB middle := by
  induction middle generalizing seenB with
  | nil =>
      simp [squareMiddleInversionsFrom, squareN, ggNonterminal]
  | cons head tail ih =>
      cases head with
      | terminal tok =>
          change squareMiddleInversionsFrom seenB
              (tail ++ [squareN SquareNT.b]) =
            squareMiddleInversionsFrom seenB tail
          exact ih seenB
      | nonterminal A =>
          cases A
          · change squareMiddleInversionsFrom seenB
              (tail ++ [squareN SquareNT.b]) =
              squareMiddleInversionsFrom seenB tail
            exact ih seenB
          · change squareMiddleInversionsFrom seenB
              (tail ++ [squareN SquareNT.b]) =
              squareMiddleInversionsFrom seenB tail
            exact ih seenB
          · change squareMiddleInversionsFrom seenB
              (tail ++ [squareN SquareNT.b]) =
              squareMiddleInversionsFrom seenB tail
            exact ih seenB
          · change squareMiddleInversionsFrom seenB
              (tail ++ [squareN SquareNT.b]) =
              squareMiddleInversionsFrom seenB tail
            exact ih seenB
          · change squareMiddleInversionsFrom (seenB + 1)
              (tail ++ [squareN SquareNT.b]) =
              squareMiddleInversionsFrom (seenB + 1) tail
            exact ih (seenB + 1)
          · change seenB +
              squareMiddleInversionsFrom seenB
                (tail ++ [squareN SquareNT.b]) =
              seenB + squareMiddleInversionsFrom seenB tail
            rw [ih seenB]

theorem squareMiddlePotential_trailing_b
    (middle : SententialForm SquareTerminal SquareNT) :
    squareMiddlePotential (middle ++ [squareN SquareNT.b]) =
      squareMiddlePotential middle := by
  have hinv := squareMiddleInversionsFrom_trailing_b 0 middle
  rw [squareMiddlePotential, squareMiddlePotential]
  simp [squareMiddleInversions, sententialCountTerminal_append,
    SententialCountTerminal, squareN, ggNonterminal] at hinv ⊢
  exact hinv

theorem squareMiddlePotential_leading_markA
    (middle : SententialForm SquareTerminal SquareNT) :
    squareMiddlePotential ([squareN SquareNT.markA] ++ middle) =
      squareMiddlePotential middle := by
  simp [squareMiddlePotential, squareMiddleInversions,
    squareMiddleInversionsFrom, SententialCountTerminal, squareN,
    ggNonterminal]

theorem squareMiddlePotential_leading_terminal_a
    (middle : SententialForm SquareTerminal SquareNT) :
    squareMiddlePotential ([squareT SquareTerminal.a] ++ middle) =
      squareMiddlePotential middle + 1 := by
  simp [squareMiddlePotential, squareMiddleInversions,
    squareMiddleInversionsFrom, SententialCountTerminal, squareT,
    ggTerminal]
  omega

def squareMiddleCreditFrom (seenB : Nat)
    (middle : SententialForm SquareTerminal SquareNT) : Nat :=
  SententialCountTerminal SquareTerminal.a middle +
    squareMiddleInversionsFrom seenB middle

theorem squareMiddleCreditFrom_moveBA
    (seenB : Nat)
    (left right : SententialForm SquareTerminal SquareNT) :
    squareMiddleCreditFrom seenB
        (left ++ [squareN SquareNT.b, squareN SquareNT.markA] ++ right) =
      squareMiddleCreditFrom seenB
        (left ++ [squareN SquareNT.markA, squareT SquareTerminal.a,
          squareN SquareNT.b] ++ right) := by
  induction left generalizing seenB with
  | nil =>
      simp [squareMiddleCreditFrom,
        squareMiddleInversionsFrom, SententialCountTerminal, squareN,
        squareT, ggNonterminal, ggTerminal]
      omega
  | cons head tail ih =>
      cases head with
      | terminal tok =>
          cases tok
          have htail := ih seenB
          simp [squareMiddleCreditFrom, squareMiddleInversionsFrom,
            SententialCountTerminal, squareN, squareT, ggNonterminal,
            ggTerminal] at htail ⊢
          omega
      | nonterminal A =>
          cases A
          · simpa [squareMiddleCreditFrom, squareMiddleInversionsFrom,
              SententialCountTerminal, squareN, squareT, ggNonterminal,
              ggTerminal] using ih seenB
          · simpa [squareMiddleCreditFrom, squareMiddleInversionsFrom,
              SententialCountTerminal, squareN, squareT, ggNonterminal,
              ggTerminal] using ih seenB
          · simpa [squareMiddleCreditFrom, squareMiddleInversionsFrom,
              SententialCountTerminal, squareN, squareT, ggNonterminal,
              ggTerminal] using ih seenB
          · simpa [squareMiddleCreditFrom, squareMiddleInversionsFrom,
              SententialCountTerminal, squareN, squareT, ggNonterminal,
              ggTerminal] using ih seenB
          · simpa [squareMiddleCreditFrom, squareMiddleInversionsFrom,
              SententialCountTerminal, squareN, squareT, ggNonterminal,
              ggTerminal] using ih (seenB + 1)
          · have htail := ih seenB
            simp [squareMiddleCreditFrom, squareMiddleInversionsFrom,
              SententialCountTerminal, squareN, squareT, ggNonterminal,
              ggTerminal] at htail ⊢
            omega

theorem squareMiddlePotential_moveBA
    (left right : SententialForm SquareTerminal SquareNT) :
    squareMiddlePotential
        (left ++ [squareN SquareNT.b, squareN SquareNT.markA] ++ right) =
      squareMiddlePotential
        (left ++ [squareN SquareNT.markA, squareT SquareTerminal.a,
          squareN SquareNT.b] ++ right) := by
  simpa [squareMiddlePotential, squareMiddleInversions,
    squareMiddleCreditFrom] using
    squareMiddleCreditFrom_moveBA 0 left right

theorem squareMiddleCreditFrom_moveBa
    (seenB : Nat)
    (left right : SententialForm SquareTerminal SquareNT) :
    squareMiddleCreditFrom seenB
        (left ++ [squareN SquareNT.b, squareT SquareTerminal.a] ++ right) =
      squareMiddleCreditFrom seenB
        (left ++ [squareT SquareTerminal.a, squareN SquareNT.b] ++ right) := by
  induction left generalizing seenB with
  | nil =>
      simp [squareMiddleCreditFrom,
        squareMiddleInversionsFrom, SententialCountTerminal, squareN,
        squareT, ggNonterminal, ggTerminal]
  | cons head tail ih =>
      cases head with
      | terminal tok =>
          cases tok
          have htail := ih seenB
          simp [squareMiddleCreditFrom, squareMiddleInversionsFrom,
            SententialCountTerminal, squareN, squareT, ggNonterminal,
            ggTerminal] at htail ⊢
          omega
      | nonterminal A =>
          cases A
          · simpa [squareMiddleCreditFrom, squareMiddleInversionsFrom,
              SententialCountTerminal, squareN, squareT, ggNonterminal,
              ggTerminal] using ih seenB
          · simpa [squareMiddleCreditFrom, squareMiddleInversionsFrom,
              SententialCountTerminal, squareN, squareT, ggNonterminal,
              ggTerminal] using ih seenB
          · simpa [squareMiddleCreditFrom, squareMiddleInversionsFrom,
              SententialCountTerminal, squareN, squareT, ggNonterminal,
              ggTerminal] using ih seenB
          · simpa [squareMiddleCreditFrom, squareMiddleInversionsFrom,
              SententialCountTerminal, squareN, squareT, ggNonterminal,
              ggTerminal] using ih seenB
          · simpa [squareMiddleCreditFrom, squareMiddleInversionsFrom,
              SententialCountTerminal, squareN, squareT, ggNonterminal,
              ggTerminal] using ih (seenB + 1)
          · have htail := ih seenB
            simp [squareMiddleCreditFrom, squareMiddleInversionsFrom,
              SententialCountTerminal, squareN, squareT, ggNonterminal,
              ggTerminal] at htail ⊢
            omega

theorem squareMiddlePotential_moveBa
    (left right : SententialForm SquareTerminal SquareNT) :
    squareMiddlePotential
        (left ++ [squareN SquareNT.b, squareT SquareTerminal.a] ++ right) =
      squareMiddlePotential
        (left ++ [squareT SquareTerminal.a, squareN SquareNT.b] ++ right) := by
  simpa [squareMiddlePotential, squareMiddleInversions,
    squareMiddleCreditFrom] using
    squareMiddleCreditFrom_moveBa 0 left right

theorem squareMiddleInversionsFrom_markerAForm
    (seenB n : Nat) :
    squareMiddleInversionsFrom seenB (squareMarkerAForm n) =
      seenB * n := by
  induction n with
  | zero =>
      simp [squareMarkerAForm, Word.RepeatSymbol,
        squareMiddleInversionsFrom]
  | succ n ih =>
      change squareMiddleInversionsFrom seenB
          (squareN SquareNT.markA :: squareMarkerAForm n) =
        seenB * (n + 1)
      simp [squareMiddleInversionsFrom, squareN, ggNonterminal, ih,
        Nat.mul_succ]
      omega

theorem squareMiddleInversionsFrom_bForm_append_markerAForm
    (seenB bCount aCount : Nat) :
    squareMiddleInversionsFrom seenB
        (squareBForm bCount ++ squareMarkerAForm aCount) =
      (seenB + bCount) * aCount := by
  induction bCount generalizing seenB with
  | zero =>
      simpa [squareBForm, Word.RepeatSymbol, Nat.zero_add] using
        squareMiddleInversionsFrom_markerAForm seenB aCount
  | succ bCount ih =>
      change squareMiddleInversionsFrom seenB
          (squareN SquareNT.b ::
            (squareBForm bCount ++ squareMarkerAForm aCount)) =
        (seenB + (bCount + 1)) * aCount
      have htail := ih (seenB + 1)
      have hnat : seenB + 1 + bCount = seenB + (bCount + 1) := by
        omega
      simp [squareMiddleInversionsFrom, squareN, ggNonterminal] at htail ⊢
      simpa [hnat] using htail

theorem squareBForm_count_terminal_a (n : Nat) :
    SententialCountTerminal SquareTerminal.a (squareBForm n) = 0 := by
  induction n with
  | zero =>
      simp [squareBForm, Word.RepeatSymbol, SententialCountTerminal]
  | succ n ih =>
      change SententialCountTerminal SquareTerminal.a
          (squareN SquareNT.b :: squareBForm n) = 0
      simp [SententialCountTerminal, squareN, ggNonterminal, ih]

theorem squareMarkerAForm_count_terminal_a (n : Nat) :
    SententialCountTerminal SquareTerminal.a (squareMarkerAForm n) = 0 := by
  induction n with
  | zero =>
      simp [squareMarkerAForm, Word.RepeatSymbol, SententialCountTerminal]
  | succ n ih =>
      change SententialCountTerminal SquareTerminal.a
          (squareN SquareNT.markA :: squareMarkerAForm n) = 0
      simp [SententialCountTerminal, squareN, ggNonterminal, ih]

theorem squareMiddlePotential_initial_stopped (n : Nat) :
    squareMiddlePotential (squareBForm n ++ squareMarkerAForm n) =
      n * n := by
  rw [squareMiddlePotential, squareMiddleInversions,
    sententialCountTerminal_append,
    squareBForm_count_terminal_a, squareMarkerAForm_count_terminal_a,
    squareMiddleInversionsFrom_bForm_append_markerAForm]
  simp

def SquareMiddleClean :
    SententialForm SquareTerminal SquareNT -> Prop
  | [] => True
  | Symbol.nonterminal SquareNT.b :: rest => SquareMiddleClean rest
  | Symbol.nonterminal SquareNT.markA :: rest => SquareMiddleClean rest
  | Symbol.terminal SquareTerminal.a :: rest => SquareMiddleClean rest
  | _ :: _ => False

theorem squareMiddleClean_append
    {left right : SententialForm SquareTerminal SquareNT}
    (hleft : SquareMiddleClean left)
    (hright : SquareMiddleClean right) :
    SquareMiddleClean (left ++ right) := by
  induction left with
  | nil =>
      exact hright
  | cons head tail ih =>
      cases head with
      | terminal tok =>
          cases tok
          exact ih hleft
      | nonterminal A =>
          cases A <;> try cases hleft
          · exact ih hleft
          · exact ih hleft

theorem squareMiddleClean_append_left
    {left right : SententialForm SquareTerminal SquareNT}
    (h : SquareMiddleClean (left ++ right)) :
    SquareMiddleClean left := by
  induction left with
  | nil =>
      trivial
  | cons head tail ih =>
      cases head with
      | terminal tok =>
          cases tok
          exact ih h
      | nonterminal A =>
          cases A <;> try cases h
          · exact ih h
          · exact ih h

theorem squareMiddleClean_append_right
    {left right : SententialForm SquareTerminal SquareNT}
    (h : SquareMiddleClean (left ++ right)) :
    SquareMiddleClean right := by
  induction left with
  | nil =>
      simpa using h
  | cons head tail ih =>
      cases head with
      | terminal tok =>
          cases tok
          exact ih h
      | nonterminal A =>
          cases A <;> try cases h
          · exact ih h
          · exact ih h

theorem squareMiddleClean_single_b :
    SquareMiddleClean [squareN SquareNT.b] := by
  simp [SquareMiddleClean, squareN, ggNonterminal]

theorem squareMiddleClean_single_markA :
    SquareMiddleClean [squareN SquareNT.markA] := by
  simp [SquareMiddleClean, squareN, ggNonterminal]

theorem squareMiddleClean_single_terminal_a :
    SquareMiddleClean [squareT SquareTerminal.a] := by
  simp [SquareMiddleClean, squareT, ggTerminal]

theorem squareBForm_clean (n : Nat) :
    SquareMiddleClean (squareBForm n) := by
  induction n with
  | zero =>
      trivial
  | succ n ih =>
      change SquareMiddleClean (squareN SquareNT.b :: squareBForm n)
      exact ih

theorem squareMarkerAForm_clean (n : Nat) :
    SquareMiddleClean (squareMarkerAForm n) := by
  induction n with
  | zero =>
      trivial
  | succ n ih =>
      change SquareMiddleClean (squareN SquareNT.markA ::
        squareMarkerAForm n)
      exact ih

theorem squareTerminalAForm_clean (n : Nat) :
    SquareMiddleClean (squareTerminalAForm n) := by
  induction n with
  | zero =>
      trivial
  | succ n ih =>
      change SquareMiddleClean (squareT SquareTerminal.a ::
        squareTerminalAForm n)
      exact ih

theorem squareMiddleClean_count_d
    {middle : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle) :
    SententialCountNonterminal SquareNT.d middle = 0 := by
  induction middle with
  | nil =>
      rfl
  | cons head tail ih =>
      cases head with
      | terminal tok =>
          cases tok
          exact ih hclean
      | nonterminal A =>
          cases A <;> try cases hclean
          · simpa [SententialCountNonterminal] using ih hclean
          · simpa [SententialCountNonterminal] using ih hclean

theorem squareMiddleClean_count_start
    {middle : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle) :
    SententialCountNonterminal SquareNT.start middle = 0 := by
  induction middle with
  | nil =>
      rfl
  | cons head tail ih =>
      cases head with
      | terminal tok =>
          cases tok
          exact ih hclean
      | nonterminal A =>
          cases A <;> try cases hclean
          · simpa [SententialCountNonterminal] using ih hclean
          · simpa [SententialCountNonterminal] using ih hclean

theorem squareMiddleClean_count_t
    {middle : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle) :
    SententialCountNonterminal SquareNT.t middle = 0 := by
  induction middle with
  | nil =>
      rfl
  | cons head tail ih =>
      cases head with
      | terminal tok =>
          cases tok
          exact ih hclean
      | nonterminal A =>
          cases A <;> try cases hclean
          · simpa [SententialCountNonterminal] using ih hclean
          · simpa [SententialCountNonterminal] using ih hclean

theorem squareMiddle_leading_markA_of_tail
    {middle v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (h : [squareN SquareNT.markA] ++ v =
      middle ++ [squareN SquareNT.e]) :
    exists rest,
      middle = [squareN SquareNT.markA] ++ rest ∧
        v = rest ++ [squareN SquareNT.e] := by
  cases middle with
  | nil =>
      simp [squareN, ggNonterminal] at h
  | cons head rest =>
      simp at h
      have hhead : head = squareN SquareNT.markA := h.left.symm
      subst head
      exists rest
      simp [h.right]

theorem squareMiddle_leading_terminal_a_of_tail
    {middle v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (h : [squareT SquareTerminal.a] ++ v =
      middle ++ [squareN SquareNT.e]) :
    exists rest,
      middle = [squareT SquareTerminal.a] ++ rest ∧
        v = rest ++ [squareN SquareNT.e] := by
  cases middle with
  | nil =>
      simp [squareN, squareT, ggNonterminal, ggTerminal] at h
  | cons head rest =>
      simp at h
      have hhead : head = squareT SquareTerminal.a := h.left.symm
      subst head
      exists rest
      simp [h.right]

theorem squareMiddle_empty_of_E_tail
    {middle v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (h : [squareN SquareNT.e] ++ v =
      middle ++ [squareN SquareNT.e]) :
    middle = [] ∧ v = [] := by
  cases middle with
  | nil =>
      simp at h
      exact ⟨rfl, h⟩
  | cons head rest =>
      cases head with
      | terminal tok =>
          cases tok
          simp [squareN, ggNonterminal] at h
      | nonterminal A =>
          cases A <;> try cases hclean
          all_goals simp [squareN, ggNonterminal] at h


end Section06
end Chapter04
end Book
end FoC
