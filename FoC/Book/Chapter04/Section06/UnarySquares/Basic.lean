import FoC.Book.Chapter04.Section06.StrictInequalities

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section06

/-!
# Section 4.6 unary squares
-/

open Languages
open Grammars

/-!
# Unary Squares

The square grammar generates words {lit}`a^(n^2)`. Its marker phases simulate
building an {lit}`n` by {lit}`n` grid and then emitting one {lit}`a` for each cell. The
theorems prove both a family of generated square words and a concrete
derivation of {lit}`aaaa`.
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

/-!
The square-language construction uses marker rows. Processing one {lit}`b`
extends each row; processing all {lit}`b`s builds the rectangular marker grid
that later collapses to {lit}`a^(n^2)`.
-/

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

/-!
Finishing the rows turns the marker grid into terminal {lit}`a`s. This is the
last constructive phase before the generated-word theorem for square lengths.
-/

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

end Section06
end Chapter04
end Book
end FoC
