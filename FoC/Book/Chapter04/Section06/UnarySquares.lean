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

def squarePostStopForm
    (emitted : Nat) (middle : SententialForm SquareTerminal SquareNT) :
    SententialForm SquareTerminal SquareNT :=
  squareTerminalAForm emitted ++ [squareN SquareNT.d] ++ middle ++
    [squareN SquareNT.e]

def SquarePostStopState (n : Nat)
    (sf : SententialForm SquareTerminal SquareNT) : Prop :=
  exists emitted middle,
    sf = squarePostStopForm emitted middle ∧
      SquareMiddleClean middle ∧
        emitted + squareMiddlePotential middle = n * n

def SquarePostStopLocalState (n emitted : Nat)
    (middle : SententialForm SquareTerminal SquareNT) : Prop :=
  SquareMiddleClean middle ∧
    emitted + squareMiddlePotential middle = n * n

/-!
**Local square invariant.** The existential state above is convenient for
derivation statements, while {name}`SquarePostStopLocalState` is the exact
payload needed after a list split has located a rewrite inside the middle
segment. The lemmas below show that each post-stop rule preserves that local
payload, or in the terminal case produces a square word.
-/

theorem squarePostStopState_of_local
    {n emitted : Nat}
    {middle : SententialForm SquareTerminal SquareNT}
    (hlocal : SquarePostStopLocalState n emitted middle) :
    SquarePostStopState n (squarePostStopForm emitted middle) := by
  exact ⟨emitted, middle, rfl, hlocal.left, hlocal.right⟩

theorem squarePostStopLocal_initial (n : Nat) :
    SquarePostStopLocalState n 0
      (squareBForm n ++ squareMarkerAForm n) := by
  constructor
  · exact squareMiddleClean_append (squareBForm_clean n)
      (squareMarkerAForm_clean n)
  · rw [squareMiddlePotential_initial_stopped]
    omega

theorem squarePostStop_initial (n : Nat) :
    SquarePostStopState n
      ([squareN SquareNT.d] ++ squareBForm n ++
        squareMarkerAForm n ++ [squareN SquareNT.e]) := by
  exists 0
  exists squareBForm n ++ squareMarkerAForm n
  constructor
  · simp [squarePostStopForm, squareTerminalAForm,
      SententialForm.terminalWord, Word.RepeatSymbol, List.append_assoc]
  constructor
  · exact squareMiddleClean_append (squareBForm_clean n)
      (squareMarkerAForm_clean n)
  · rw [squareMiddlePotential_initial_stopped]
    omega

theorem squareGrowForm_stop_post_state
    {u v : SententialForm SquareTerminal SquareNT} (n : Nat)
    (h : squareGrowForm n = u ++ [squareN SquareNT.t] ++ v) :
    SquarePostStopState n (u ++ v) := by
  have hocc := squareGrowForm_t_occurrence n h
  rw [hocc.left, hocc.right]
  simpa [List.append_assoc] using squarePostStop_initial n

theorem squareMiddleClean_moveBA
    (left right : SententialForm SquareTerminal SquareNT)
    (hleft : SquareMiddleClean left)
    (hright : SquareMiddleClean right) :
    SquareMiddleClean
      (left ++ [squareN SquareNT.markA, squareT SquareTerminal.a,
        squareN SquareNT.b] ++ right) := by
  have hlocal :
      SquareMiddleClean
        ([squareN SquareNT.markA, squareT SquareTerminal.a,
          squareN SquareNT.b] ++ right) := by
    apply squareMiddleClean_append
    · exact squareMiddleClean_append squareMiddleClean_single_markA
        (squareMiddleClean_append squareMiddleClean_single_terminal_a
          squareMiddleClean_single_b)
    · exact hright
  simpa [List.append_assoc] using
    squareMiddleClean_append hleft hlocal

theorem squareMiddleClean_moveBa
    (left right : SententialForm SquareTerminal SquareNT)
    (hleft : SquareMiddleClean left)
    (hright : SquareMiddleClean right) :
    SquareMiddleClean
      (left ++ [squareT SquareTerminal.a, squareN SquareNT.b] ++ right) := by
  have hlocal :
      SquareMiddleClean
        ([squareT SquareTerminal.a, squareN SquareNT.b] ++ right) := by
    apply squareMiddleClean_append
    · exact squareMiddleClean_append squareMiddleClean_single_terminal_a
        squareMiddleClean_single_b
    · exact hright
  simpa [List.append_assoc] using
    squareMiddleClean_append hleft hlocal

theorem squareMiddleClean_trailing_b_iff
    (middle : SententialForm SquareTerminal SquareNT) :
    SquareMiddleClean (middle ++ [squareN SquareNT.b]) <->
      SquareMiddleClean middle := by
  constructor
  · induction middle with
    | nil =>
        intro _
        trivial
    | cons head tail ih =>
        intro h
        cases head with
        | terminal tok =>
            cases tok
            exact ih h
        | nonterminal A =>
            cases A <;> try cases h
            · exact ih h
            · exact ih h
  · intro h
    exact squareMiddleClean_append h squareMiddleClean_single_b

theorem squareMiddle_pair_split_before_E_markA
    {middle u v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (h : middle ++ [squareN SquareNT.e] =
      u ++ [squareN SquareNT.b, squareN SquareNT.markA] ++ v) :
    exists left right,
      middle = left ++ [squareN SquareNT.b, squareN SquareNT.markA] ++ right ∧
        u = left ∧ v = right ++ [squareN SquareNT.e] := by
  induction middle generalizing u with
  | nil =>
      cases u <;> simp [squareN, ggNonterminal] at h
  | cons head tail ih =>
      cases u with
      | nil =>
          simp at h
          have hhead : head = squareN SquareNT.b := h.left
          subst head
          cases tail with
          | nil =>
              simp [squareN, ggNonterminal] at h
          | cons tailHead tailRest =>
              simp at h
              have htailHead : tailHead = squareN SquareNT.markA := h.left
              subst tailHead
              exists []
              exists tailRest
              simp [h.right]
      | cons uhead urest =>
          simp at h
          have hhead : uhead = head := h.left.symm
          subst uhead
          have htailClean : SquareMiddleClean tail := by
            cases head with
            | terminal tok =>
                cases tok
                exact hclean
            | nonterminal A =>
                cases A <;> try cases hclean
                · exact hclean
                · exact hclean
          have htail :
              tail ++ [squareN SquareNT.e] =
                urest ++ [squareN SquareNT.b, squareN SquareNT.markA] ++ v := by
            simpa using h.right
          rcases ih htailClean htail with ⟨left, right, hmid, hu, hv⟩
          exists head :: left
          exists right
          constructor
          · simp [hmid, List.append_assoc]
          constructor
          · simp [hu]
          · exact hv

theorem squareMiddle_pair_split_before_E_terminal_a
    {middle u v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (h : middle ++ [squareN SquareNT.e] =
      u ++ [squareN SquareNT.b, squareT SquareTerminal.a] ++ v) :
    exists left right,
      middle = left ++ [squareN SquareNT.b, squareT SquareTerminal.a] ++ right ∧
        u = left ∧ v = right ++ [squareN SquareNT.e] := by
  induction middle generalizing u with
  | nil =>
      cases u <;> simp [squareN, squareT, ggNonterminal, ggTerminal] at h
  | cons head tail ih =>
      cases u with
      | nil =>
          simp at h
          have hhead : head = squareN SquareNT.b := h.left
          subst head
          cases tail with
          | nil =>
              simp [squareN, squareT, ggNonterminal, ggTerminal] at h
          | cons tailHead tailRest =>
              simp at h
              have htailHead : tailHead = squareT SquareTerminal.a := h.left
              subst tailHead
              exists []
              exists tailRest
              simp [h.right]
      | cons uhead urest =>
          simp at h
          have hhead : uhead = head := h.left.symm
          subst uhead
          have htailClean : SquareMiddleClean tail := by
            cases head with
            | terminal tok =>
                cases tok
                exact hclean
            | nonterminal A =>
                cases A <;> try cases hclean
                · exact hclean
                · exact hclean
          have htail :
              tail ++ [squareN SquareNT.e] =
                urest ++ [squareN SquareNT.b, squareT SquareTerminal.a] ++ v := by
            simpa using h.right
          rcases ih htailClean htail with ⟨left, right, hmid, hu, hv⟩
          exists head :: left
          exists right
          constructor
          · simp [hmid, List.append_assoc]
          constructor
          · simp [hu]
          · exact hv

theorem sentential_pair_after_nonterminal_delimiter
    [DecidableEq nonterminal]
    {A C : nonterminal}
    {second : Symbol terminal nonterminal}
    {pref tail u v : SententialForm terminal nonterminal}
    (hne : C ≠ A)
    (hpref : SententialCountNonterminal A pref = 0)
    (h : pref ++ [ggNonterminal C] ++ tail =
      u ++ [ggNonterminal A, second] ++ v) :
    exists rest,
      u = pref ++ [ggNonterminal C] ++ rest ∧
        tail = rest ++ [ggNonterminal A, second] ++ v := by
  induction pref generalizing u with
  | nil =>
      simp at h
      cases u with
      | nil =>
          simp [ggNonterminal] at h
          exact False.elim (hne h.left)
      | cons uhead urest =>
          simp at h
          exists urest
          constructor
          · simp [h.left]
          · simpa using h.right
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
          have htail :
              rest ++ [ggNonterminal C] ++ tail =
                urest ++ [ggNonterminal A, second] ++ v := by
            simpa using h.right
          rcases ih hrestCount htail with ⟨after, hu, htailEq⟩
          exists after
          constructor
          · simp [hu]
          · exact htailEq

theorem sentential_single_after_nonterminal_delimiter
    [DecidableEq nonterminal]
    {A C : nonterminal}
    {pref tail u : SententialForm terminal nonterminal}
    (hne : C ≠ A)
    (hpref : SententialCountNonterminal A pref = 0)
    (h : pref ++ [ggNonterminal C] ++ tail =
      u ++ [ggNonterminal A]) :
    exists rest,
      u = pref ++ [ggNonterminal C] ++ rest ∧
        tail = rest ++ [ggNonterminal A] := by
  induction pref generalizing u with
  | nil =>
      simp at h
      cases u with
      | nil =>
          simp [ggNonterminal] at h
          exact False.elim (hne h.left)
      | cons uhead urest =>
          simp at h
          exists urest
          constructor
          · simp [h.left]
          · simpa using h.right
  | cons head rest ih =>
      cases u with
      | nil =>
          simp at h
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
          have htail :
              rest ++ [ggNonterminal C] ++ tail =
                urest ++ [ggNonterminal A] := by
            simpa using h.right
          rcases ih hrestCount htail with ⟨after, hu, htailEq⟩
          exists after
          constructor
          · simp [hu]
          · exact htailEq

theorem squareMiddle_trailing_b_split_before_E
    {middle u v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (h : middle ++ [squareN SquareNT.e] =
      u ++ [squareN SquareNT.b, squareN SquareNT.e] ++ v) :
    exists left,
      middle = left ++ [squareN SquareNT.b] ∧ u = left ∧ v = [] := by
  induction middle generalizing u with
  | nil =>
      cases u <;> simp [squareN, ggNonterminal] at h
  | cons head tail ih =>
      cases u with
      | nil =>
          simp at h
          have hhead : head = squareN SquareNT.b := h.left
          subst head
          cases tail with
          | nil =>
              simp at h
              exists []
          | cons tailHead tailRest =>
              simp at h
              have htailHead : tailHead = squareN SquareNT.e := h.left
              subst tailHead
              simp [SquareMiddleClean, squareN, ggNonterminal] at hclean
      | cons uhead urest =>
          simp at h
          have hhead : uhead = head := h.left.symm
          subst uhead
          have htailClean : SquareMiddleClean tail := by
            cases head with
            | terminal tok =>
                cases tok
                exact hclean
            | nonterminal A =>
                cases A <;> try cases hclean
                · exact hclean
                · exact hclean
          have htail :
              tail ++ [squareN SquareNT.e] =
                urest ++ [squareN SquareNT.b, squareN SquareNT.e] ++ v := by
            simpa using h.right
          rcases ih htailClean htail with ⟨left, hmid, hu, hv⟩
          exists head :: left
          constructor
          · simp [hmid]
          constructor
          · simp [hu]
          · exact hv

theorem squareSeparatedTail_no_B_pair
    (bCount aCount : Nat)
    {second : Symbol SquareTerminal SquareNT}
    (hsecondT : squareN SquareNT.t ≠ second)
    (hsecondB : squareN SquareNT.b ≠ second)
    {u v : SententialForm SquareTerminal SquareNT}
    (h : squareBForm bCount ++ [squareN SquareNT.t] ++
        squareMarkerAForm aCount ++ [squareN SquareNT.e] =
      u ++ [squareN SquareNT.b, second] ++ v) :
    False := by
  induction bCount generalizing u with
  | zero =>
      have hcount :
          SententialCountNonterminal SquareNT.b
            (squareBForm 0 ++ [squareN SquareNT.t] ++
              squareMarkerAForm aCount ++ [squareN SquareNT.e]) = 0 := by
        have hmarkers :
            SententialCountNonterminal SquareNT.b
              (squareMarkerAForm aCount) = 0 := by
          simpa [squareMarkerAForm] using
            (sententialCountNonterminal_repeat_nonterminal_of_ne
              (terminal := SquareTerminal) (A := SquareNT.b)
              (B := SquareNT.markA) (by intro hba; cases hba) aCount)
        simp [squareBForm, Word.RepeatSymbol,
          sententialCountNonterminal_append, hmarkers,
          SententialCountNonterminal, squareN, ggNonterminal]
      exact sentential_no_nonterminal_occurrence_absurd hcount (by
        simpa [List.append_assoc] using
          (show squareBForm 0 ++ [squareN SquareNT.t] ++
              squareMarkerAForm aCount ++ [squareN SquareNT.e] =
            u ++ [squareN SquareNT.b] ++ (second :: v) by
              simpa [List.append_assoc] using h))
  | succ bCount ih =>
      change squareN SquareNT.b ::
          (squareBForm bCount ++ [squareN SquareNT.t] ++
            squareMarkerAForm aCount ++ [squareN SquareNT.e]) =
        u ++ [squareN SquareNT.b, second] ++ v at h
      cases u with
      | nil =>
          simp at h
          have htail :
              squareBForm bCount ++ [squareN SquareNT.t] ++
                  squareMarkerAForm aCount ++ [squareN SquareNT.e] =
                second :: v := by
            simpa [List.append_assoc] using h
          cases bCount with
          | zero =>
              simp [squareBForm, Word.RepeatSymbol] at htail
              exact hsecondT htail.left
          | succ b =>
              change squareN SquareNT.b ::
                  (squareBForm b ++ [squareN SquareNT.t] ++
                    squareMarkerAForm aCount ++ [squareN SquareNT.e]) =
                second :: v at htail
              simp at htail
              exact hsecondB htail.left
      | cons head rest =>
          simp at h
          have hhead : head = squareN SquareNT.b := h.left.symm
          subst head
          exact ih (by simpa [List.append_assoc] using h.right)

theorem squarePostStop_moveBA
    {n emitted : Nat}
    {left right : SententialForm SquareTerminal SquareNT}
    (hleft : SquareMiddleClean left)
    (hright : SquareMiddleClean right)
    (hbalance :
      emitted + squareMiddlePotential
        (left ++ [squareN SquareNT.b, squareN SquareNT.markA] ++ right) =
        n * n) :
    SquarePostStopState n
      (squarePostStopForm emitted
        (left ++ [squareN SquareNT.markA, squareT SquareTerminal.a,
          squareN SquareNT.b] ++ right)) := by
  exists emitted
  exists left ++ [squareN SquareNT.markA, squareT SquareTerminal.a,
    squareN SquareNT.b] ++ right
  constructor
  · rfl
  constructor
  · exact squareMiddleClean_moveBA left right hleft hright
  · rw [← squareMiddlePotential_moveBA]
    exact hbalance

theorem squarePostStopState_step_moveBA
    {n emitted : Nat}
    {middle u v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (hbalance : emitted + squareMiddlePotential middle = n * n)
    (h : squarePostStopForm emitted middle =
      u ++ [squareN SquareNT.b, squareN SquareNT.markA] ++ v) :
    SquarePostStopState n
      (u ++ [squareN SquareNT.markA, squareT SquareTerminal.a,
        squareN SquareNT.b] ++ v) := by
  have hafter := sentential_pair_after_nonterminal_delimiter
    (terminal := SquareTerminal) (nonterminal := SquareNT)
    (A := SquareNT.b) (C := SquareNT.d)
    (second := squareN SquareNT.markA)
    (by intro hbd; cases hbd)
    (squareTerminalAForm_count_nonterminal SquareNT.b emitted)
    (pref := squareTerminalAForm emitted) (tail := middle ++ [squareN SquareNT.e])
    (u := u) (v := v) (by
      simpa [squarePostStopForm, squareN, List.append_assoc] using h)
  rcases hafter with ⟨afterD, hu, htail⟩
  rcases squareMiddle_pair_split_before_E_markA hclean htail with
    ⟨left, right, hmiddle, hafterEq, hv⟩
  have hlocalClean :
      SquareMiddleClean
        (left ++ [squareN SquareNT.b, squareN SquareNT.markA] ++ right) := by
    rw [← hmiddle]
    exact hclean
  have hleft : SquareMiddleClean left := by
    have hclean' :
        SquareMiddleClean
          (left ++ ([squareN SquareNT.b, squareN SquareNT.markA] ++
            right)) := by
      simpa [List.append_assoc] using hlocalClean
    exact squareMiddleClean_append_left hclean'
  have htailClean :
      SquareMiddleClean
        ([squareN SquareNT.b, squareN SquareNT.markA] ++ right) := by
    have hclean' :
        SquareMiddleClean
          (left ++ ([squareN SquareNT.b, squareN SquareNT.markA] ++
            right)) := by
      simpa [List.append_assoc] using hlocalClean
    exact squareMiddleClean_append_right hclean'
  have hright : SquareMiddleClean right :=
    squareMiddleClean_append_right htailClean
  have hbalance' :
      emitted + squareMiddlePotential
        (left ++ [squareN SquareNT.b, squareN SquareNT.markA] ++ right) =
        n * n := by
    rw [← hmiddle]
    exact hbalance
  have hstate := squarePostStop_moveBA hleft hright hbalance'
  rw [hu, hafterEq, hv]
  simpa [squarePostStopForm, List.append_assoc] using hstate

theorem squarePostStopLocal_moveBA
    {n emitted : Nat}
    {left right : SententialForm SquareTerminal SquareNT}
    (hlocal : SquarePostStopLocalState n emitted
      (left ++ [squareN SquareNT.b, squareN SquareNT.markA] ++ right)) :
    SquarePostStopLocalState n emitted
      (left ++ [squareN SquareNT.markA, squareT SquareTerminal.a,
        squareN SquareNT.b] ++ right) := by
  constructor
  · have hclean :
        SquareMiddleClean
          (left ++ ([squareN SquareNT.b, squareN SquareNT.markA] ++
            right)) := by
      simpa [List.append_assoc] using hlocal.left
    have hleft : SquareMiddleClean left :=
      squareMiddleClean_append_left hclean
    have htail :
        SquareMiddleClean
          ([squareN SquareNT.b, squareN SquareNT.markA] ++ right) :=
      squareMiddleClean_append_right hclean
    have hright : SquareMiddleClean right :=
      squareMiddleClean_append_right htail
    exact squareMiddleClean_moveBA left right hleft hright
  · rw [← squareMiddlePotential_moveBA]
    exact hlocal.right

theorem squarePostStop_moveBa
    {n emitted : Nat}
    {left right : SententialForm SquareTerminal SquareNT}
    (hleft : SquareMiddleClean left)
    (hright : SquareMiddleClean right)
    (hbalance :
      emitted + squareMiddlePotential
        (left ++ [squareN SquareNT.b, squareT SquareTerminal.a] ++ right) =
        n * n) :
    SquarePostStopState n
      (squarePostStopForm emitted
        (left ++ [squareT SquareTerminal.a, squareN SquareNT.b] ++ right)) := by
  exists emitted
  exists left ++ [squareT SquareTerminal.a, squareN SquareNT.b] ++ right
  constructor
  · rfl
  constructor
  · exact squareMiddleClean_moveBa left right hleft hright
  · rw [← squareMiddlePotential_moveBa]
    exact hbalance

theorem squarePostStopState_step_moveBa
    {n emitted : Nat}
    {middle u v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (hbalance : emitted + squareMiddlePotential middle = n * n)
    (h : squarePostStopForm emitted middle =
      u ++ [squareN SquareNT.b, squareT SquareTerminal.a] ++ v) :
    SquarePostStopState n
      (u ++ [squareT SquareTerminal.a, squareN SquareNT.b] ++ v) := by
  have hafter := sentential_pair_after_nonterminal_delimiter
    (terminal := SquareTerminal) (nonterminal := SquareNT)
    (A := SquareNT.b) (C := SquareNT.d)
    (second := squareT SquareTerminal.a)
    (by intro hbd; cases hbd)
    (squareTerminalAForm_count_nonterminal SquareNT.b emitted)
    (pref := squareTerminalAForm emitted) (tail := middle ++ [squareN SquareNT.e])
    (u := u) (v := v) (by
      simpa [squarePostStopForm, squareN, List.append_assoc] using h)
  rcases hafter with ⟨afterD, hu, htail⟩
  rcases squareMiddle_pair_split_before_E_terminal_a hclean htail with
    ⟨left, right, hmiddle, hafterEq, hv⟩
  have hlocalClean :
      SquareMiddleClean
        (left ++ [squareN SquareNT.b, squareT SquareTerminal.a] ++ right) := by
    rw [← hmiddle]
    exact hclean
  have hleft : SquareMiddleClean left := by
    have hclean' :
        SquareMiddleClean
          (left ++ ([squareN SquareNT.b, squareT SquareTerminal.a] ++
            right)) := by
      simpa [List.append_assoc] using hlocalClean
    exact squareMiddleClean_append_left hclean'
  have htailClean :
      SquareMiddleClean
        ([squareN SquareNT.b, squareT SquareTerminal.a] ++ right) := by
    have hclean' :
        SquareMiddleClean
          (left ++ ([squareN SquareNT.b, squareT SquareTerminal.a] ++
            right)) := by
      simpa [List.append_assoc] using hlocalClean
    exact squareMiddleClean_append_right hclean'
  have hright : SquareMiddleClean right :=
    squareMiddleClean_append_right htailClean
  have hbalance' :
      emitted + squareMiddlePotential
        (left ++ [squareN SquareNT.b, squareT SquareTerminal.a] ++ right) =
        n * n := by
    rw [← hmiddle]
    exact hbalance
  have hstate := squarePostStop_moveBa hleft hright hbalance'
  rw [hu, hafterEq, hv]
  simpa [squarePostStopForm, List.append_assoc] using hstate

theorem squarePostStopLocal_moveBa
    {n emitted : Nat}
    {left right : SententialForm SquareTerminal SquareNT}
    (hlocal : SquarePostStopLocalState n emitted
      (left ++ [squareN SquareNT.b, squareT SquareTerminal.a] ++ right)) :
    SquarePostStopLocalState n emitted
      (left ++ [squareT SquareTerminal.a, squareN SquareNT.b] ++ right) := by
  constructor
  · have hclean :
        SquareMiddleClean
          (left ++ ([squareN SquareNT.b, squareT SquareTerminal.a] ++
            right)) := by
      simpa [List.append_assoc] using hlocal.left
    have hleft : SquareMiddleClean left :=
      squareMiddleClean_append_left hclean
    have htail :
        SquareMiddleClean
          ([squareN SquareNT.b, squareT SquareTerminal.a] ++ right) :=
      squareMiddleClean_append_right hclean
    have hright : SquareMiddleClean right :=
      squareMiddleClean_append_right htail
    exact squareMiddleClean_moveBa left right hleft hright
  · rw [← squareMiddlePotential_moveBa]
    exact hlocal.right

theorem squarePostStop_removeBE
    {n emitted : Nat}
    {middle : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean (middle ++ [squareN SquareNT.b]))
    (hbalance :
      emitted + squareMiddlePotential (middle ++ [squareN SquareNT.b]) =
        n * n) :
    SquarePostStopState n (squarePostStopForm emitted middle) := by
  exists emitted
  exists middle
  constructor
  · rfl
  constructor
  · exact (squareMiddleClean_trailing_b_iff middle).mp hclean
  · rw [squareMiddlePotential_trailing_b] at hbalance
    exact hbalance

theorem squarePostStopState_step_removeBE
    {n emitted : Nat}
    {middle u v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (hbalance : emitted + squareMiddlePotential middle = n * n)
    (h : squarePostStopForm emitted middle =
      u ++ [squareN SquareNT.b, squareN SquareNT.e] ++ v) :
    SquarePostStopState n (u ++ [squareN SquareNT.e] ++ v) := by
  have hafter := sentential_pair_after_nonterminal_delimiter
    (terminal := SquareTerminal) (nonterminal := SquareNT)
    (A := SquareNT.b) (C := SquareNT.d)
    (second := squareN SquareNT.e)
    (by intro hbd; cases hbd)
    (squareTerminalAForm_count_nonterminal SquareNT.b emitted)
    (pref := squareTerminalAForm emitted) (tail := middle ++ [squareN SquareNT.e])
    (u := u) (v := v) (by
      simpa [squarePostStopForm, squareN, List.append_assoc] using h)
  rcases hafter with ⟨afterD, hu, htail⟩
  rcases squareMiddle_trailing_b_split_before_E hclean htail with
    ⟨left, hmiddle, hafterEq, hv⟩
  have hlocalClean : SquareMiddleClean (left ++ [squareN SquareNT.b]) := by
    rw [← hmiddle]
    exact hclean
  have hbalance' :
      emitted + squareMiddlePotential (left ++ [squareN SquareNT.b]) =
        n * n := by
    rw [← hmiddle]
    exact hbalance
  have hstate := squarePostStop_removeBE hlocalClean hbalance'
  rw [hu, hafterEq, hv]
  simpa [squarePostStopForm, List.append_assoc] using hstate

theorem squarePostStopLocal_removeBE
    {n emitted : Nat}
    {middle : SententialForm SquareTerminal SquareNT}
    (hlocal : SquarePostStopLocalState n emitted
      (middle ++ [squareN SquareNT.b])) :
    SquarePostStopLocalState n emitted middle := by
  constructor
  · exact (squareMiddleClean_trailing_b_iff middle).mp hlocal.left
  · have hbalance := hlocal.right
    rw [squareMiddlePotential_trailing_b] at hbalance
    exact hbalance

theorem squarePostStop_removeDA
    {n emitted : Nat}
    {middle : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean ([squareN SquareNT.markA] ++ middle))
    (hbalance :
      emitted + squareMiddlePotential ([squareN SquareNT.markA] ++ middle) =
        n * n) :
    SquarePostStopState n (squarePostStopForm emitted middle) := by
  exists emitted
  exists middle
  constructor
  · rfl
  constructor
  · exact hclean
  · rw [squareMiddlePotential_leading_markA] at hbalance
    exact hbalance

theorem squarePostStopState_step_removeDA
    {n emitted : Nat}
    {middle u v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (hbalance : emitted + squareMiddlePotential middle = n * n)
    (h : squarePostStopForm emitted middle =
      u ++ [squareN SquareNT.d, squareN SquareNT.markA] ++ v) :
    SquarePostStopState n (u ++ [squareN SquareNT.d] ++ v) := by
  have htailCount :
      SententialCountNonterminal SquareNT.d
        (middle ++ [squareN SquareNT.e]) = 0 := by
    rw [sententialCountNonterminal_append, squareMiddleClean_count_d hclean]
    simp [SententialCountNonterminal, squareN, ggNonterminal]
  have huniq := sentential_unique_nonterminal_occurrence
    (terminal := SquareTerminal) (nonterminal := SquareNT)
    (A := SquareNT.d)
    (pref := squareTerminalAForm emitted) (tail := middle ++ [squareN SquareNT.e])
    (u := u) (v := [squareN SquareNT.markA] ++ v)
    (squareTerminalAForm_count_nonterminal SquareNT.d emitted)
    htailCount
    (by simpa [squarePostStopForm, squareN, List.append_assoc] using h)
  rcases huniq with ⟨hu, htail⟩
  rcases squareMiddle_leading_markA_of_tail hclean htail with
    ⟨rest, hmiddle, hv⟩
  have hlocalClean : SquareMiddleClean ([squareN SquareNT.markA] ++ rest) := by
    rw [← hmiddle]
    exact hclean
  have hbalance' :
      emitted + squareMiddlePotential ([squareN SquareNT.markA] ++ rest) =
        n * n := by
    rw [← hmiddle]
    exact hbalance
  have hstate := squarePostStop_removeDA hlocalClean hbalance'
  rw [hu, hv]
  simpa [squarePostStopForm, List.append_assoc] using hstate

theorem squarePostStopLocal_removeDA
    {n emitted : Nat}
    {middle : SententialForm SquareTerminal SquareNT}
    (hlocal : SquarePostStopLocalState n emitted
      ([squareN SquareNT.markA] ++ middle)) :
    SquarePostStopLocalState n emitted middle := by
  constructor
  · exact hlocal.left
  · have hbalance := hlocal.right
    rw [squareMiddlePotential_leading_markA] at hbalance
    exact hbalance

theorem squarePostStop_moveDa
    {n emitted : Nat}
    {middle : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean ([squareT SquareTerminal.a] ++ middle))
    (hbalance :
      emitted + squareMiddlePotential ([squareT SquareTerminal.a] ++ middle) =
        n * n) :
    SquarePostStopState n (squarePostStopForm (emitted + 1) middle) := by
  exists emitted + 1
  exists middle
  constructor
  · rfl
  constructor
  · exact hclean
  · rw [squareMiddlePotential_leading_terminal_a] at hbalance
    omega

theorem squareTerminalAForm_succ_eq_append (n : Nat) :
    squareTerminalAForm (n + 1) =
      squareTerminalAForm n ++ [squareT SquareTerminal.a] := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change squareT SquareTerminal.a :: squareTerminalAForm (n + 1) =
        squareT SquareTerminal.a ::
          (squareTerminalAForm n ++ [squareT SquareTerminal.a])
      rw [ih]

theorem squarePostStopState_step_moveDa
    {n emitted : Nat}
    {middle u v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (hbalance : emitted + squareMiddlePotential middle = n * n)
    (h : squarePostStopForm emitted middle =
      u ++ [squareN SquareNT.d, squareT SquareTerminal.a] ++ v) :
    SquarePostStopState n
      (u ++ [squareT SquareTerminal.a, squareN SquareNT.d] ++ v) := by
  have htailCount :
      SententialCountNonterminal SquareNT.d
        (middle ++ [squareN SquareNT.e]) = 0 := by
    rw [sententialCountNonterminal_append, squareMiddleClean_count_d hclean]
    simp [SententialCountNonterminal, squareN, ggNonterminal]
  have huniq := sentential_unique_nonterminal_occurrence
    (terminal := SquareTerminal) (nonterminal := SquareNT)
    (A := SquareNT.d)
    (pref := squareTerminalAForm emitted) (tail := middle ++ [squareN SquareNT.e])
    (u := u) (v := [squareT SquareTerminal.a] ++ v)
    (squareTerminalAForm_count_nonterminal SquareNT.d emitted)
    htailCount
    (by simpa [squarePostStopForm, squareN, List.append_assoc] using h)
  rcases huniq with ⟨hu, htail⟩
  rcases squareMiddle_leading_terminal_a_of_tail hclean htail with
    ⟨rest, hmiddle, hv⟩
  have hlocalClean : SquareMiddleClean ([squareT SquareTerminal.a] ++ rest) := by
    rw [← hmiddle]
    exact hclean
  have hbalance' :
      emitted + squareMiddlePotential ([squareT SquareTerminal.a] ++ rest) =
        n * n := by
    rw [← hmiddle]
    exact hbalance
  have hstate := squarePostStop_moveDa hlocalClean hbalance'
  rw [hu, hv]
  simpa [squarePostStopForm, squareTerminalAForm_succ_eq_append,
    List.append_assoc] using hstate

theorem squarePostStopLocal_moveDa
    {n emitted : Nat}
    {middle : SententialForm SquareTerminal SquareNT}
    (hlocal : SquarePostStopLocalState n emitted
      ([squareT SquareTerminal.a] ++ middle)) :
    SquarePostStopLocalState n (emitted + 1) middle := by
  constructor
  · exact hlocal.left
  · have hbalance := hlocal.right
    rw [squareMiddlePotential_leading_terminal_a] at hbalance
    omega

theorem squarePostStop_finish_word
    {n emitted : Nat}
    (hbalance : emitted + squareMiddlePotential [] = n * n) :
    Word.RepeatSymbol SquareTerminal.a emitted ∈ squareLanguage := by
  simp [squareMiddlePotential, squareMiddleInversions,
    squareMiddleInversionsFrom, SententialCountTerminal] at hbalance
  have hemitted : emitted = n * n := by omega
  exists n
  simp [squareWord, hemitted]

theorem squarePostStopState_step_finish_square
    {n emitted : Nat}
    {middle u v : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle)
    (hbalance : emitted + squareMiddlePotential middle = n * n)
    (h : squarePostStopForm emitted middle =
      u ++ [squareN SquareNT.d, squareN SquareNT.e] ++ v) :
    exists word,
      u ++ v = SententialForm.terminalWord word ∧
        word ∈ squareLanguage := by
  have htailCount :
      SententialCountNonterminal SquareNT.d
        (middle ++ [squareN SquareNT.e]) = 0 := by
    rw [sententialCountNonterminal_append, squareMiddleClean_count_d hclean]
    simp [SententialCountNonterminal, squareN, ggNonterminal]
  have huniq := sentential_unique_nonterminal_occurrence
    (terminal := SquareTerminal) (nonterminal := SquareNT)
    (A := SquareNT.d)
    (pref := squareTerminalAForm emitted) (tail := middle ++ [squareN SquareNT.e])
    (u := u) (v := [squareN SquareNT.e] ++ v)
    (squareTerminalAForm_count_nonterminal SquareNT.d emitted)
    htailCount
    (by simpa [squarePostStopForm, squareN, List.append_assoc] using h)
  rcases huniq with ⟨hu, htail⟩
  rcases squareMiddle_empty_of_E_tail hclean htail with ⟨hmiddle, hv⟩
  have hbalance' : emitted + squareMiddlePotential [] = n * n := by
    rw [← hmiddle]
    exact hbalance
  exists Word.RepeatSymbol SquareTerminal.a emitted
  constructor
  · rw [hu, hv]
    simp [squareTerminalAForm, SententialForm.terminalWord]
  · exact squarePostStop_finish_word hbalance'

theorem squarePostStopLocal_finish_word
    {n emitted : Nat}
    (hlocal : SquarePostStopLocalState n emitted []) :
    Word.RepeatSymbol SquareTerminal.a emitted ∈ squareLanguage :=
  squarePostStop_finish_word hlocal.right

inductive SquareReachableState :
    SententialForm SquareTerminal SquareNT -> Prop where
  | start :
      SquareReachableState [squareN SquareNT.start]
  | grow (n : Nat) :
      SquareReachableState (squareGrowForm n)
  | post {sf : SententialForm SquareTerminal SquareNT}
      (n : Nat) (hpost : SquarePostStopState n sf) :
      SquareReachableState sf
  | terminal {word : Word SquareTerminal}
      (hword : word ∈ squareLanguage) :
      SquareReachableState (SententialForm.terminalWord word)

theorem squarePostStopForm_count_start
    {emitted : Nat} {middle : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle) :
    SententialCountNonterminal SquareNT.start
      (squarePostStopForm emitted middle) = 0 := by
  simp [squarePostStopForm, sententialCountNonterminal_append,
    squareTerminalAForm_count_nonterminal,
    squareMiddleClean_count_start hclean, SententialCountNonterminal,
    squareN, ggNonterminal]

theorem squarePostStopForm_count_t
    {emitted : Nat} {middle : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle) :
    SententialCountNonterminal SquareNT.t
      (squarePostStopForm emitted middle) = 0 := by
  simp [squarePostStopForm, sententialCountNonterminal_append,
    squareTerminalAForm_count_nonterminal,
    squareMiddleClean_count_t hclean, SententialCountNonterminal,
    squareN, ggNonterminal]

theorem squarePostStopState_yields_reachable
    {x y : SententialForm SquareTerminal SquareNT}
    {n : Nat}
    (hpost : SquarePostStopState n x)
    (hstep : GeneralGrammar.Yields SquareGrammar x y) :
    SquareReachableState y := by
  rcases hpost with ⟨emitted, middle, hx, hclean, hbalance⟩
  rcases hstep with ⟨u, v, lhs, rhs, hprod, hxstep, hystep⟩
  rw [hx] at hxstep
  rw [hystep]
  cases hprod with
  | start =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (squarePostStopForm_count_start hclean) hxstep)
  | grow =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (squarePostStopForm_count_t hclean) hxstep)
  | stop =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (squarePostStopForm_count_t hclean) hxstep)
  | moveBA =>
      exact SquareReachableState.post n
        (squarePostStopState_step_moveBA hclean hbalance hxstep)
  | moveBa =>
      exact SquareReachableState.post n
        (squarePostStopState_step_moveBa hclean hbalance hxstep)
  | removeBE =>
      exact SquareReachableState.post n
        (squarePostStopState_step_removeBE hclean hbalance hxstep)
  | removeDA =>
      exact SquareReachableState.post n
        (squarePostStopState_step_removeDA hclean hbalance hxstep)
  | moveDa =>
      exact SquareReachableState.post n
        (squarePostStopState_step_moveDa hclean hbalance hxstep)
  | finish =>
      rcases squarePostStopState_step_finish_square hclean hbalance hxstep with
        ⟨word, hy, hword⟩
      have hterminal : SquareReachableState (u ++ v) := by
        rw [hy]
        exact SquareReachableState.terminal hword
      simpa using hterminal

theorem squareGrowForm_count_start (n : Nat) :
    SententialCountNonterminal SquareNT.start (squareGrowForm n) = 0 := by
  have hb :
      SententialCountNonterminal SquareNT.start (squareBForm n) = 0 := by
    simpa [squareBForm] using
      (sententialCountNonterminal_repeat_nonterminal_of_ne
        (terminal := SquareTerminal) (A := SquareNT.start) (B := SquareNT.b)
        (by intro h; cases h) n)
  have ha :
      SententialCountNonterminal SquareNT.start (squareMarkerAForm n) = 0 := by
    simpa [squareMarkerAForm] using
      (sententialCountNonterminal_repeat_nonterminal_of_ne
        (terminal := SquareTerminal) (A := SquareNT.start)
        (B := SquareNT.markA) (by intro h; cases h) n)
  simp [squareGrowForm, sententialCountNonterminal_append,
    hb, ha, SententialCountNonterminal, squareN, ggNonterminal]

theorem squareGrowForm_count_terminal_a (n : Nat) :
    SententialCountTerminal SquareTerminal.a (squareGrowForm n) = 0 := by
  simp [squareGrowForm, sententialCountTerminal_append,
    squareBForm_count_terminal_a, squareMarkerAForm_count_terminal_a,
    SententialCountTerminal, squareN, ggNonterminal]

theorem squareGrowForm_yields_reachable
    {y : SententialForm SquareTerminal SquareNT}
    (n : Nat)
    (hstep : GeneralGrammar.Yields SquareGrammar (squareGrowForm n) y) :
    SquareReachableState y := by
  rcases hstep with ⟨u, v, lhs, rhs, hprod, hxstep, hystep⟩
  rw [hystep]
  cases hprod with
  | start =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (squareGrowForm_count_start n) hxstep)
  | grow =>
      have hocc := squareGrowForm_t_occurrence n hxstep
      rw [hocc.left, hocc.right]
      simpa [squareGrowForm, squareBForm_succ_eq_append,
        squareMarkerAForm, Word.RepeatSymbol, List.append_assoc] using
        SquareReachableState.grow (n + 1)
  | stop =>
      exact SquareReachableState.post n
        (squareGrowForm_stop_post_state n (by simpa using hxstep))
  | moveBA =>
      have hafter := sentential_pair_after_nonterminal_delimiter
        (terminal := SquareTerminal) (nonterminal := SquareNT)
        (A := SquareNT.b) (C := SquareNT.d)
        (second := squareN SquareNT.markA)
        (by intro hbd; cases hbd)
        (by simp [SententialCountNonterminal])
        (pref := []) (tail := squareBForm n ++ [squareN SquareNT.t] ++
          squareMarkerAForm n ++ [squareN SquareNT.e])
        (u := u) (v := v) (by
          simpa [squareGrowForm, squareN, List.append_assoc] using hxstep)
      rcases hafter with ⟨afterD, hu, htail⟩
      exact False.elim
        (squareSeparatedTail_no_B_pair n n
          (by intro htm; cases htm)
          (by intro hbm; cases hbm)
          htail)
  | moveBa =>
      exact False.elim
        (sentential_no_terminal_occurrence_absurd
          (squareGrowForm_count_terminal_a n) (by
            exact
              (show squareGrowForm n =
                  (u ++ [squareN SquareNT.b]) ++
                    [ggTerminal SquareTerminal.a] ++ v by
                simpa [squareT, List.append_assoc] using hxstep)))
  | removeBE =>
      have hafter := sentential_pair_after_nonterminal_delimiter
        (terminal := SquareTerminal) (nonterminal := SquareNT)
        (A := SquareNT.b) (C := SquareNT.d)
        (second := squareN SquareNT.e)
        (by intro hbd; cases hbd)
        (by simp [SententialCountNonterminal])
        (pref := []) (tail := squareBForm n ++ [squareN SquareNT.t] ++
          squareMarkerAForm n ++ [squareN SquareNT.e])
        (u := u) (v := v) (by
          simpa [squareGrowForm, squareN, List.append_assoc] using hxstep)
      rcases hafter with ⟨afterD, hu, htail⟩
      exact False.elim
        (squareSeparatedTail_no_B_pair n n
          (by intro hte; cases hte)
          (by intro hbe; cases hbe)
          htail)
  | removeDA =>
      have htailCount :
          SententialCountNonterminal SquareNT.d
            (squareBForm n ++ [squareN SquareNT.t] ++
              squareMarkerAForm n ++ [squareN SquareNT.e]) = 0 := by
        simp [sententialCountNonterminal_append, squareBForm_count_d,
          squareMarkerAForm_count_d, SententialCountNonterminal,
          squareN, ggNonterminal]
      have huniq := sentential_unique_nonterminal_occurrence
        (terminal := SquareTerminal) (nonterminal := SquareNT)
        (A := SquareNT.d)
        (pref := []) (tail := squareBForm n ++ [squareN SquareNT.t] ++
          squareMarkerAForm n ++ [squareN SquareNT.e])
        (u := u) (v := [squareN SquareNT.markA] ++ v)
        (by simp [SententialCountNonterminal]) htailCount
        (by simpa [squareGrowForm, squareN, List.append_assoc] using hxstep)
      rcases huniq with ⟨hu, htail⟩
      cases n with
      | zero =>
          simp [squareBForm, squareMarkerAForm, Word.RepeatSymbol,
            squareN, ggNonterminal] at htail
      | succ n =>
          change squareN SquareNT.markA :: v =
            squareN SquareNT.b ::
              (squareBForm n ++ [squareN SquareNT.t] ++
                squareMarkerAForm (n + 1) ++ [squareN SquareNT.e]) at htail
          simp [squareN, ggNonterminal] at htail
  | moveDa =>
      exact False.elim
        (sentential_no_terminal_occurrence_absurd
          (squareGrowForm_count_terminal_a n) (by
            exact
              (show squareGrowForm n =
                  (u ++ [squareN SquareNT.d]) ++
                    [ggTerminal SquareTerminal.a] ++ v by
                simpa [squareT, List.append_assoc] using hxstep)))
  | finish =>
      have htailCount :
          SententialCountNonterminal SquareNT.d
            (squareBForm n ++ [squareN SquareNT.t] ++
              squareMarkerAForm n ++ [squareN SquareNT.e]) = 0 := by
        simp [sententialCountNonterminal_append, squareBForm_count_d,
          squareMarkerAForm_count_d, SententialCountNonterminal,
          squareN, ggNonterminal]
      have huniq := sentential_unique_nonterminal_occurrence
        (terminal := SquareTerminal) (nonterminal := SquareNT)
        (A := SquareNT.d)
        (pref := []) (tail := squareBForm n ++ [squareN SquareNT.t] ++
          squareMarkerAForm n ++ [squareN SquareNT.e])
        (u := u) (v := [squareN SquareNT.e] ++ v)
        (by simp [SententialCountNonterminal]) htailCount
        (by simpa [squareGrowForm, squareN, List.append_assoc] using hxstep)
      rcases huniq with ⟨hu, htail⟩
      cases n with
      | zero =>
          simp [squareBForm, squareMarkerAForm, Word.RepeatSymbol,
            squareN, ggNonterminal] at htail
      | succ n =>
          change squareN SquareNT.e :: v =
            squareN SquareNT.b ::
              (squareBForm n ++ [squareN SquareNT.t] ++
                squareMarkerAForm (n + 1) ++ [squareN SquareNT.e]) at htail
          simp [squareN, ggNonterminal] at htail

theorem squareStart_yields_reachable
    {y : SententialForm SquareTerminal SquareNT}
    (hstep : GeneralGrammar.Yields SquareGrammar [squareN SquareNT.start] y) :
    SquareReachableState y := by
  rcases hstep with ⟨u, v, lhs, rhs, hprod, hxstep, hystep⟩
  rw [hystep]
  cases hprod with
  | start =>
      have huniq := sentential_unique_nonterminal_occurrence
        (terminal := SquareTerminal) (nonterminal := SquareNT)
        (A := SquareNT.start)
        (pref := []) (tail := []) (u := u) (v := v)
        (by simp [SententialCountNonterminal])
        (by simp [SententialCountNonterminal])
        (by simpa [squareN] using hxstep)
      rcases huniq with ⟨hu, hv⟩
      rw [hu, hv]
      simpa [squareGrowForm, squareBForm, squareMarkerAForm,
        Word.RepeatSymbol, List.append_assoc] using
        SquareReachableState.grow 0
  | grow =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (by simp [SententialCountNonterminal, squareN, ggNonterminal] :
            SententialCountNonterminal SquareNT.t [squareN SquareNT.start] = 0)
          (by simpa [squareN] using hxstep))
  | stop =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (by simp [SententialCountNonterminal, squareN, ggNonterminal] :
            SententialCountNonterminal SquareNT.t [squareN SquareNT.start] = 0)
          (by simpa [squareN] using hxstep))
  | moveBA =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (by simp [SententialCountNonterminal, squareN, ggNonterminal] :
            SententialCountNonterminal SquareNT.b [squareN SquareNT.start] = 0)
          (by simpa [squareN, List.append_assoc] using
            (show [squareN SquareNT.start] =
                u ++ [squareN SquareNT.b] ++
                  ([squareN SquareNT.markA] ++ v) by
              simpa [List.append_assoc] using hxstep)))
  | moveBa =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (by simp [SententialCountNonterminal, squareN, ggNonterminal] :
            SententialCountNonterminal SquareNT.b [squareN SquareNT.start] = 0)
          (by simpa [squareN, List.append_assoc] using
            (show [squareN SquareNT.start] =
                u ++ [squareN SquareNT.b] ++
                  ([squareT SquareTerminal.a] ++ v) by
              simpa [List.append_assoc] using hxstep)))
  | removeBE =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (by simp [SententialCountNonterminal, squareN, ggNonterminal] :
            SententialCountNonterminal SquareNT.b [squareN SquareNT.start] = 0)
          (by simpa [squareN, List.append_assoc] using
            (show [squareN SquareNT.start] =
                u ++ [squareN SquareNT.b] ++
                  ([squareN SquareNT.e] ++ v) by
              simpa [List.append_assoc] using hxstep)))
  | removeDA =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (by simp [SententialCountNonterminal, squareN, ggNonterminal] :
            SententialCountNonterminal SquareNT.d [squareN SquareNT.start] = 0)
          (by simpa [squareN, List.append_assoc] using
            (show [squareN SquareNT.start] =
                u ++ [squareN SquareNT.d] ++
                  ([squareN SquareNT.markA] ++ v) by
              simpa [List.append_assoc] using hxstep)))
  | moveDa =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (by simp [SententialCountNonterminal, squareN, ggNonterminal] :
            SententialCountNonterminal SquareNT.d [squareN SquareNT.start] = 0)
          (by simpa [squareN, List.append_assoc] using
            (show [squareN SquareNT.start] =
                u ++ [squareN SquareNT.d] ++
                  ([squareT SquareTerminal.a] ++ v) by
              simpa [List.append_assoc] using hxstep)))
  | finish =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (by simp [SententialCountNonterminal, squareN, ggNonterminal] :
            SententialCountNonterminal SquareNT.d [squareN SquareNT.start] = 0)
          (by simpa [squareN, List.append_assoc] using
            (show [squareN SquareNT.start] =
                u ++ [squareN SquareNT.d] ++
                  ([squareN SquareNT.e] ++ v) by
              simpa [List.append_assoc] using hxstep)))

theorem squareTerminalState_yields_reachable
    {word : Word SquareTerminal}
    (_hword : word ∈ squareLanguage)
    {y : SententialForm SquareTerminal SquareNT}
    (hstep : GeneralGrammar.Yields SquareGrammar
      (SententialForm.terminalWord word) y) :
    SquareReachableState y := by
  rcases hstep with ⟨u, v, lhs, rhs, hprod, hxstep, hystep⟩
  cases hprod with
  | start =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (sententialCountNonterminal_terminalWord SquareNT.start word)
          (by simpa [squareN] using hxstep))
  | grow =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (sententialCountNonterminal_terminalWord SquareNT.t word)
          (by simpa [squareN] using hxstep))
  | stop =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (sententialCountNonterminal_terminalWord SquareNT.t word)
          (by simpa [squareN] using hxstep))
  | moveBA =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (sententialCountNonterminal_terminalWord SquareNT.b word)
          (by simpa [squareN, List.append_assoc] using
            (show SententialForm.terminalWord word =
                u ++ [squareN SquareNT.b] ++
                  ([squareN SquareNT.markA] ++ v) by
              simpa [List.append_assoc] using hxstep)))
  | moveBa =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (sententialCountNonterminal_terminalWord SquareNT.b word)
          (by simpa [squareN, List.append_assoc] using
            (show SententialForm.terminalWord word =
                u ++ [squareN SquareNT.b] ++
                  ([squareT SquareTerminal.a] ++ v) by
              simpa [List.append_assoc] using hxstep)))
  | removeBE =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (sententialCountNonterminal_terminalWord SquareNT.b word)
          (by simpa [squareN, List.append_assoc] using
            (show SententialForm.terminalWord word =
                u ++ [squareN SquareNT.b] ++
                  ([squareN SquareNT.e] ++ v) by
              simpa [List.append_assoc] using hxstep)))
  | removeDA =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (sententialCountNonterminal_terminalWord SquareNT.d word)
          (by simpa [squareN, List.append_assoc] using
            (show SententialForm.terminalWord word =
                u ++ [squareN SquareNT.d] ++
                  ([squareN SquareNT.markA] ++ v) by
              simpa [List.append_assoc] using hxstep)))
  | moveDa =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (sententialCountNonterminal_terminalWord SquareNT.d word)
          (by simpa [squareN, List.append_assoc] using
            (show SententialForm.terminalWord word =
                u ++ [squareN SquareNT.d] ++
                  ([squareT SquareTerminal.a] ++ v) by
              simpa [List.append_assoc] using hxstep)))
  | finish =>
      exact False.elim
        (sentential_no_nonterminal_occurrence_absurd
          (sententialCountNonterminal_terminalWord SquareNT.d word)
          (by simpa [squareN, List.append_assoc] using
            (show SententialForm.terminalWord word =
                u ++ [squareN SquareNT.d] ++
                  ([squareN SquareNT.e] ++ v) by
              simpa [List.append_assoc] using hxstep)))

theorem squareReachableState_yields_reachable
    {x y : SententialForm SquareTerminal SquareNT}
    (hx : SquareReachableState x)
    (hstep : GeneralGrammar.Yields SquareGrammar x y) :
    SquareReachableState y := by
  cases hx with
  | start =>
      exact squareStart_yields_reachable hstep
  | grow n =>
      exact squareGrowForm_yields_reachable n hstep
  | post n hpost =>
      exact squarePostStopState_yields_reachable hpost hstep
  | terminal hword =>
      exact squareTerminalState_yields_reachable hword hstep

theorem squareReachableState_derives
    {x y : SententialForm SquareTerminal SquareNT}
    (h : GeneralGrammar.Derives SquareGrammar x y)
    (hx : SquareReachableState x) :
    SquareReachableState y := by
  induction h with
  | refl _ =>
      exact hx
  | step hstep _ ih =>
      exact ih (squareReachableState_yields_reachable hx hstep)

theorem squarePostStopForm_count_d
    {emitted : Nat} {middle : SententialForm SquareTerminal SquareNT}
    (hclean : SquareMiddleClean middle) :
    SententialCountNonterminal SquareNT.d
      (squarePostStopForm emitted middle) = 1 := by
  simp [squarePostStopForm, sententialCountNonterminal_append,
    squareTerminalAForm_count_nonterminal, squareMiddleClean_count_d hclean,
    SententialCountNonterminal, squareN, ggNonterminal]

theorem squareReachableState_terminal_square
    {word : Word SquareTerminal}
    (hstate : SquareReachableState (SententialForm.terminalWord word)) :
    word ∈ squareLanguage := by
  generalize hsf : SententialForm.terminalWord word = sf at hstate
  cases hstate with
  | start =>
      exact False.elim
        (sententialCountNonterminal_terminal_absurd
          square_start_form_count_start hsf.symm)
  | grow n =>
      exact False.elim
        (sententialCountNonterminal_terminal_absurd
          (squareGrowForm_count_d n) hsf.symm)
  | post n hpost =>
      rcases hpost with ⟨emitted, middle, hpostForm, hclean, hbalance⟩
      have hcount :
          SententialCountNonterminal SquareNT.d sf = 1 := by
        rw [hpostForm]
        exact squarePostStopForm_count_d hclean
      exact False.elim
        (sententialCountNonterminal_terminal_absurd hcount hsf.symm)
  | terminal hword =>
      have hto :=
        congrArg
          (SententialForm.toWord?
            (term := SquareTerminal) (nt := SquareNT)) hsf
      simp [SententialForm.terminalWord_toWord] at hto
      cases hto
      exact hword

theorem square_generated_only_language
    {word : Word SquareTerminal}
    (h : word ∈ GeneralGrammar.GeneratedLanguage SquareGrammar) :
    word ∈ squareLanguage := by
  have hderives :
      GeneralGrammar.Derives SquareGrammar [squareN SquareNT.start]
        (SententialForm.terminalWord word) := by
    simpa [GeneralGrammar.GeneratedLanguage, SquareGrammar, squareN,
      ggNonterminal] using h
  exact squareReachableState_terminal_square
    (squareReachableState_derives hderives SquareReachableState.start)

theorem square_generated_language_exact :
    Language.Equal (GeneralGrammar.GeneratedLanguage SquareGrammar)
      squareLanguage := by
  intro word
  constructor
  · exact square_generated_only_language
  · exact square_language_subset_generated

theorem squareGrammar_finite_production_squareLanguage :
    FiniteProductionGeneralLanguage squareLanguage := by
  exists SquareNT
  exists SquareGrammar
  constructor
  · exact squareGrammar_has_finite_productions
  · exact square_generated_language_exact

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


end Section06
end Chapter04
end Book
end FoC
