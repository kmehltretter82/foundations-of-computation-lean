import FoC.Book.Chapter04.Section06.UnarySquares.Basic

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section06

open Languages
open Grammars

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

def squareProcessMoveForm
    (remaining rowWidth processed moved afterRows : Nat) :
    SententialForm SquareTerminal SquareNT :=
  [squareN SquareNT.d] ++ squareBForm remaining ++
    squareRows (rowWidth + 1) processed ++
      [squareN SquareNT.markA] ++ squareTerminalAForm (moved + 1) ++
        [squareN SquareNT.b] ++ squareTerminalAForm (rowWidth - moved) ++
          squareRows rowWidth afterRows ++ [squareN SquareNT.e]

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
  | processMove (remaining rowWidth processed moved afterRows : Nat)
      (hmoved : moved <= rowWidth) :
      SquareDerivationShape
        (squareProcessMoveForm remaining rowWidth processed moved afterRows)
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

theorem square_no_t_occurrence_absurd
    {sf u v : SententialForm SquareTerminal SquareNT}
    (hcount : SententialCountNonterminal SquareNT.t sf = 0)
    (h : sf = u ++ [squareN SquareNT.t] ++ v) : False := by
  have hc := congrArg (SententialCountNonterminal SquareNT.t) h
  rw [hcount, sententialCountNonterminal_append,
    sententialCountNonterminal_append] at hc
  simp [SententialCountNonterminal, squareN, ggNonterminal] at hc
  omega

theorem squareBForm_count_t (n : Nat) :
    SententialCountNonterminal SquareNT.t (squareBForm n) = 0 := by
  simpa [squareBForm] using
    (sententialCountNonterminal_repeat_nonterminal_of_ne
      (terminal := SquareTerminal) (A := SquareNT.t) (B := SquareNT.b)
      (by intro h; cases h) n)

theorem squareMarkerAForm_count_t (n : Nat) :
    SententialCountNonterminal SquareNT.t (squareMarkerAForm n) = 0 := by
  simpa [squareMarkerAForm] using
    (sententialCountNonterminal_repeat_nonterminal_of_ne
      (terminal := SquareTerminal) (A := SquareNT.t)
      (B := SquareNT.markA) (by intro h; cases h) n)

theorem squareGrowForm_tail_count_t (n : Nat) :
    SententialCountNonterminal SquareNT.t
      (squareMarkerAForm n ++ [squareN SquareNT.e]) = 0 := by
  simp [sententialCountNonterminal_append, squareMarkerAForm_count_t,
    SententialCountNonterminal, squareN, ggNonterminal]

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

theorem squareGrowForm_grow_shape
    {u v : SententialForm SquareTerminal SquareNT} (n : Nat)
    (h : squareGrowForm n = u ++ [squareN SquareNT.t] ++ v) :
    SquareDerivationShape
      (u ++ [squareN SquareNT.b, squareN SquareNT.t,
        squareN SquareNT.markA] ++ v) := by
  have hocc := squareGrowForm_t_occurrence n h
  rw [hocc.left, hocc.right]
  simpa [squareGrowForm, squareBForm_succ_eq_append, squareMarkerAForm,
    Word.RepeatSymbol, List.append_assoc] using
    SquareDerivationShape.grow (n + 1)

theorem squareGrowForm_stop_shape
    {u v : SententialForm SquareTerminal SquareNT} (n : Nat)
    (h : squareGrowForm n = u ++ [squareN SquareNT.t] ++ v) :
    SquareDerivationShape (u ++ v) := by
  have hocc := squareGrowForm_t_occurrence n h
  rw [hocc.left, hocc.right]
  have hbalance : 0 + n = n := by omega
  simpa [squareProcessForm, squareRows_zero_eq_markerAForm,
    List.append_assoc] using
    SquareDerivationShape.process n n 0 hbalance

theorem squareProcessForm_count_d
    (remaining rowWidth rows : Nat) :
    SententialCountNonterminal SquareNT.d
      (squareProcessForm remaining rowWidth rows) = 1 := by
  simp [squareProcessForm, sententialCountNonterminal_append,
    squareBForm_count_d, squareRows_count_d, squareN,
    ggNonterminal, SententialCountNonterminal]

theorem squareProcessMoveForm_count_d
    (remaining rowWidth processed moved afterRows : Nat) :
    SententialCountNonterminal SquareNT.d
      (squareProcessMoveForm remaining rowWidth processed moved afterRows) = 1 := by
  simp [squareProcessMoveForm, sententialCountNonterminal_append,
    squareBForm_count_d, squareRows_count_d,
    squareTerminalAForm_count_nonterminal, squareN,
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

/-!
The reverse direction for square words is count-based. The derivation-shape
lemmas track the remaining marker state and conclude that any terminal result
has square length.
-/

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
  | processMove remaining rowWidth processed moved afterRows hmoved =>
      exact False.elim
        (sententialCountNonterminal_terminal_absurd
          (squareProcessMoveForm_count_d remaining rowWidth processed moved afterRows)
          hsf)
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

def SquareDerivationShapeCompleteness : Prop :=
  forall {sf : SententialForm SquareTerminal SquareNT},
    GeneralGrammar.Derives SquareGrammar [squareN SquareNT.start] sf ->
      SquareDerivationShape sf

theorem square_generated_only_language_of_shape_completeness
    (hcomplete : SquareDerivationShapeCompleteness)
    {word : Word SquareTerminal}
    (h : word ∈ GeneralGrammar.GeneratedLanguage SquareGrammar) :
    word ∈ squareLanguage := by
  have hderives :
      GeneralGrammar.Derives SquareGrammar [squareN SquareNT.start]
        (SententialForm.terminalWord word) := by
    simpa [GeneralGrammar.GeneratedLanguage, SquareGrammar, squareN,
      ggNonterminal] using h
  exact square_derivation_shape_terminal_square_of_terminal
    (hcomplete hderives)

theorem square_generated_language_exact_of_shape_completeness
    (hcomplete : SquareDerivationShapeCompleteness) :
    Language.Equal (GeneralGrammar.GeneratedLanguage SquareGrammar)
      squareLanguage := by
  intro word
  constructor
  · exact square_generated_only_language_of_shape_completeness hcomplete
  · exact square_language_subset_generated

end Section06
end Chapter04
end Book
end FoC
