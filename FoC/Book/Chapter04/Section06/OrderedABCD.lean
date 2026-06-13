import FoC.Book.Chapter04.Section06.OrderedABC

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section06

/-!
# Section 4.6 ordered four-block counts
-/

open Languages
open Grammars

/-!
# Ordered Four-Block Counts

This example extends the ordered-block method to four terminals, producing
words of the form {lit}`a^n b^n c^n d^n` and sample derivations such as
{lit}`aabbccdd`.
-/

inductive OrderedABCDNT where
  | start
  | markA
  | markB
  | markC
  | markD
  | x
  | y
  | z
  | q
deriving DecidableEq

namespace OrderedABCDNT

def finite : Foundation.FiniteType OrderedABCDNT where
  elems := [start, markA, markB, markC, markD, x, y, z, q]
  complete := by
    intro A
    cases A <;> simp

end OrderedABCDNT

def ordered4N (A : OrderedABCDNT) :
    Symbol FourCountTerminal OrderedABCDNT :=
  ggNonterminal A

def ordered4T (tok : FourCountTerminal) :
    Symbol FourCountTerminal OrderedABCDNT :=
  ggTerminal tok

inductive OrderedABCDProduces :
    SententialForm FourCountTerminal OrderedABCDNT ->
      SententialForm FourCountTerminal OrderedABCDNT -> Prop where
  | grow :
      OrderedABCDProduces [ordered4N OrderedABCDNT.start]
        [ordered4N OrderedABCDNT.start, ordered4N OrderedABCDNT.markA,
          ordered4N OrderedABCDNT.markB, ordered4N OrderedABCDNT.markC,
          ordered4N OrderedABCDNT.markD]
  | startX :
      OrderedABCDProduces [ordered4N OrderedABCDNT.start]
        [ordered4N OrderedABCDNT.x]
  | swapBA :
      OrderedABCDProduces
        [ordered4N OrderedABCDNT.markB, ordered4N OrderedABCDNT.markA]
        [ordered4N OrderedABCDNT.markA, ordered4N OrderedABCDNT.markB]
  | swapCA :
      OrderedABCDProduces
        [ordered4N OrderedABCDNT.markC, ordered4N OrderedABCDNT.markA]
        [ordered4N OrderedABCDNT.markA, ordered4N OrderedABCDNT.markC]
  | swapDA :
      OrderedABCDProduces
        [ordered4N OrderedABCDNT.markD, ordered4N OrderedABCDNT.markA]
        [ordered4N OrderedABCDNT.markA, ordered4N OrderedABCDNT.markD]
  | swapCB :
      OrderedABCDProduces
        [ordered4N OrderedABCDNT.markC, ordered4N OrderedABCDNT.markB]
        [ordered4N OrderedABCDNT.markB, ordered4N OrderedABCDNT.markC]
  | swapDB :
      OrderedABCDProduces
        [ordered4N OrderedABCDNT.markD, ordered4N OrderedABCDNT.markB]
        [ordered4N OrderedABCDNT.markB, ordered4N OrderedABCDNT.markD]
  | swapDC :
      OrderedABCDProduces
        [ordered4N OrderedABCDNT.markD, ordered4N OrderedABCDNT.markC]
        [ordered4N OrderedABCDNT.markC, ordered4N OrderedABCDNT.markD]
  | convertXA :
      OrderedABCDProduces
        [ordered4N OrderedABCDNT.x, ordered4N OrderedABCDNT.markA]
        [ordered4T FourCountTerminal.a, ordered4N OrderedABCDNT.x]
  | xToY :
      OrderedABCDProduces [ordered4N OrderedABCDNT.x]
        [ordered4N OrderedABCDNT.y]
  | convertYB :
      OrderedABCDProduces
        [ordered4N OrderedABCDNT.y, ordered4N OrderedABCDNT.markB]
        [ordered4T FourCountTerminal.b, ordered4N OrderedABCDNT.y]
  | yToZ :
      OrderedABCDProduces [ordered4N OrderedABCDNT.y]
        [ordered4N OrderedABCDNT.z]
  | convertZC :
      OrderedABCDProduces
        [ordered4N OrderedABCDNT.z, ordered4N OrderedABCDNT.markC]
        [ordered4T FourCountTerminal.c, ordered4N OrderedABCDNT.z]
  | zToQ :
      OrderedABCDProduces [ordered4N OrderedABCDNT.z]
        [ordered4N OrderedABCDNT.q]
  | convertQD :
      OrderedABCDProduces
        [ordered4N OrderedABCDNT.q, ordered4N OrderedABCDNT.markD]
        [ordered4T FourCountTerminal.d, ordered4N OrderedABCDNT.q]
  | finish :
      OrderedABCDProduces [ordered4N OrderedABCDNT.q] []

def OrderedABCDGrammar :
    GeneralGrammar FourCountTerminal OrderedABCDNT where
  start := OrderedABCDNT.start
  produces := OrderedABCDProduces
  lhsContainsNonterminal := by
    intro lhs rhs h
    cases h <;> simp [SententialForm.containsNonterminal, ordered4N,
      ggNonterminal]
  nonterminalsFinite := OrderedABCDNT.finite

def OrderedABCDProductionList :
    List (GeneralGrammar.Production FourCountTerminal OrderedABCDNT) :=
  [{ lhs := [ordered4N OrderedABCDNT.start],
     rhs := [ordered4N OrderedABCDNT.start, ordered4N OrderedABCDNT.markA,
       ordered4N OrderedABCDNT.markB, ordered4N OrderedABCDNT.markC,
       ordered4N OrderedABCDNT.markD] },
   { lhs := [ordered4N OrderedABCDNT.start],
     rhs := [ordered4N OrderedABCDNT.x] },
   { lhs := [ordered4N OrderedABCDNT.markB, ordered4N OrderedABCDNT.markA],
     rhs := [ordered4N OrderedABCDNT.markA, ordered4N OrderedABCDNT.markB] },
   { lhs := [ordered4N OrderedABCDNT.markC, ordered4N OrderedABCDNT.markA],
     rhs := [ordered4N OrderedABCDNT.markA, ordered4N OrderedABCDNT.markC] },
   { lhs := [ordered4N OrderedABCDNT.markD, ordered4N OrderedABCDNT.markA],
     rhs := [ordered4N OrderedABCDNT.markA, ordered4N OrderedABCDNT.markD] },
   { lhs := [ordered4N OrderedABCDNT.markC, ordered4N OrderedABCDNT.markB],
     rhs := [ordered4N OrderedABCDNT.markB, ordered4N OrderedABCDNT.markC] },
   { lhs := [ordered4N OrderedABCDNT.markD, ordered4N OrderedABCDNT.markB],
     rhs := [ordered4N OrderedABCDNT.markB, ordered4N OrderedABCDNT.markD] },
   { lhs := [ordered4N OrderedABCDNT.markD, ordered4N OrderedABCDNT.markC],
     rhs := [ordered4N OrderedABCDNT.markC, ordered4N OrderedABCDNT.markD] },
   { lhs := [ordered4N OrderedABCDNT.x, ordered4N OrderedABCDNT.markA],
     rhs := [ordered4T FourCountTerminal.a, ordered4N OrderedABCDNT.x] },
   { lhs := [ordered4N OrderedABCDNT.x],
     rhs := [ordered4N OrderedABCDNT.y] },
   { lhs := [ordered4N OrderedABCDNT.y, ordered4N OrderedABCDNT.markB],
     rhs := [ordered4T FourCountTerminal.b, ordered4N OrderedABCDNT.y] },
   { lhs := [ordered4N OrderedABCDNT.y],
     rhs := [ordered4N OrderedABCDNT.z] },
   { lhs := [ordered4N OrderedABCDNT.z, ordered4N OrderedABCDNT.markC],
     rhs := [ordered4T FourCountTerminal.c, ordered4N OrderedABCDNT.z] },
   { lhs := [ordered4N OrderedABCDNT.z],
     rhs := [ordered4N OrderedABCDNT.q] },
   { lhs := [ordered4N OrderedABCDNT.q, ordered4N OrderedABCDNT.markD],
     rhs := [ordered4T FourCountTerminal.d, ordered4N OrderedABCDNT.q] },
   { lhs := [ordered4N OrderedABCDNT.q],
     rhs := [] }]

/-!
The ordered four-block example repeats the ordered three-block pattern at
larger scale. The long production list consists of grow rules, marker-sorting
rules, phase-change rules, terminal-emission rules, and one final cleanup rule.
-/

theorem orderedABCDGrammar_has_finite_productions :
    GeneralGrammar.HasFiniteProductions OrderedABCDGrammar := by
  exists OrderedABCDProductionList
  intro lhs rhs
  constructor
  · intro h
    cases h <;> simp [OrderedABCDProductionList]
  · intro h
    rcases h with ⟨rule, hmem, hlhs, hrhs⟩
    simp [OrderedABCDProductionList] at hmem
    rcases hmem with
      hrule | hrule | hrule | hrule | hrule | hrule |
      hrule | hrule | hrule | hrule | hrule | hrule |
      hrule | hrule | hrule | hrule
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.grow
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.startX
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.swapBA
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.swapCA
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.swapDA
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.swapCB
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.swapDB
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.swapDC
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.convertXA
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.xToY
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.convertYB
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.yToZ
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.convertZC
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.zToQ
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.convertQD
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCDProduces.finish

/-!
The four-symbol ordered grammar is the same construction one dimension higher.
The following block records finite production data, count preservation, and one
concrete generated witness before returning to smaller counterexample grammars.
-/

theorem orderedABCDGrammar_finite_production_generated :
    FiniteProductionGeneralLanguage
      (GeneralGrammar.GeneratedLanguage OrderedABCDGrammar) := by
  exists OrderedABCDNT
  exists OrderedABCDGrammar
  constructor
  · exact orderedABCDGrammar_has_finite_productions
  · intro word
    rfl

def orderedABCDTotalA
    (sf : SententialForm FourCountTerminal OrderedABCDNT) : Nat :=
  SententialCountTerminal FourCountTerminal.a sf +
    SententialCountNonterminal OrderedABCDNT.markA sf

def orderedABCDTotalB
    (sf : SententialForm FourCountTerminal OrderedABCDNT) : Nat :=
  SententialCountTerminal FourCountTerminal.b sf +
    SententialCountNonterminal OrderedABCDNT.markB sf

def orderedABCDTotalC
    (sf : SententialForm FourCountTerminal OrderedABCDNT) : Nat :=
  SententialCountTerminal FourCountTerminal.c sf +
    SententialCountNonterminal OrderedABCDNT.markC sf

def orderedABCDTotalD
    (sf : SententialForm FourCountTerminal OrderedABCDNT) : Nat :=
  SententialCountTerminal FourCountTerminal.d sf +
    SententialCountNonterminal OrderedABCDNT.markD sf

def orderedABCDBalanced
    (sf : SententialForm FourCountTerminal OrderedABCDNT) : Prop :=
  orderedABCDTotalA sf = orderedABCDTotalB sf ∧
    orderedABCDTotalB sf = orderedABCDTotalC sf ∧
    orderedABCDTotalC sf = orderedABCDTotalD sf

theorem orderedABCD_start_balanced :
    orderedABCDBalanced [ordered4N OrderedABCDNT.start] := by
  simp [orderedABCDBalanced, orderedABCDTotalA, orderedABCDTotalB,
    orderedABCDTotalC, orderedABCDTotalD, SententialCountTerminal,
    SententialCountNonterminal, ordered4N, ggNonterminal]

theorem orderedABCD_yields_preserves_balanced
    {x y : SententialForm FourCountTerminal OrderedABCDNT}
    (h : GeneralGrammar.Yields OrderedABCDGrammar x y) :
    orderedABCDBalanced x -> orderedABCDBalanced y := by
  intro hbalanced
  cases h with
  | intro u hu =>
      cases hu with
      | intro v hv =>
          cases hv with
          | intro lhs hlhs =>
              cases hlhs with
              | intro rhs hrhs =>
                  cases hrhs with
                  | intro hprod hrest =>
                      cases hrest with
                      | intro hx hy =>
                          rw [hx] at hbalanced
                          rw [hy]
                          cases hprod <;>
                            simp [orderedABCDBalanced, orderedABCDTotalA,
                              orderedABCDTotalB, orderedABCDTotalC,
                              orderedABCDTotalD,
                              sententialCountTerminal_append,
                              sententialCountNonterminal_append,
                              SententialCountTerminal,
                              SententialCountNonterminal, ordered4N,
                              ordered4T, ggNonterminal, ggTerminal] at hbalanced ⊢ <;>
                            omega

theorem orderedABCD_derives_preserves_balanced
    {x y : SententialForm FourCountTerminal OrderedABCDNT}
    (h : GeneralGrammar.Derives OrderedABCDGrammar x y) :
    orderedABCDBalanced x -> orderedABCDBalanced y := by
  induction h with
  | refl _ =>
      intro hbalanced
      exact hbalanced
  | step hstep _ ih =>
      intro hbalanced
      exact ih (orderedABCD_yields_preserves_balanced hstep hbalanced)

theorem orderedABCDGrammar_generated_has_equal_terminal_counts
    {word : Word FourCountTerminal}
    (h : word ∈ GeneralGrammar.GeneratedLanguage OrderedABCDGrammar) :
    Word.Count FourCountTerminal.a word =
        Word.Count FourCountTerminal.b word ∧
      Word.Count FourCountTerminal.b word =
        Word.Count FourCountTerminal.c word ∧
      Word.Count FourCountTerminal.c word =
        Word.Count FourCountTerminal.d word := by
  have hderives :
      GeneralGrammar.Derives OrderedABCDGrammar
        [ordered4N OrderedABCDNT.start]
        (SententialForm.terminalWord word) := by
    simpa [GeneralGrammar.GeneratedLanguage, OrderedABCDGrammar, ordered4N,
      ggNonterminal] using h
  have hbalanced :=
    orderedABCD_derives_preserves_balanced hderives
      orderedABCD_start_balanced
  simpa [orderedABCDBalanced, orderedABCDTotalA, orderedABCDTotalB,
    orderedABCDTotalC, orderedABCDTotalD,
    sententialCountTerminal_terminalWord,
    sententialCountNonterminal_terminalWord] using hbalanced

def aabbccddWord : Word FourCountTerminal :=
  [FourCountTerminal.a, FourCountTerminal.a, FourCountTerminal.b,
    FourCountTerminal.b, FourCountTerminal.c, FourCountTerminal.c,
    FourCountTerminal.d, FourCountTerminal.d]

/-!
The explicit {lit}`aabbccdd` derivation is a sanity check for the four-count
grammar. It follows the same production pattern as the general construction but
keeps the concrete word visible.
-/

theorem orderedABCDGrammar_generates_aabbccdd :
    aabbccddWord ∈ GeneralGrammar.GeneratedLanguage OrderedABCDGrammar := by
  let S := ordered4N OrderedABCDNT.start
  let A := ordered4N OrderedABCDNT.markA
  let B := ordered4N OrderedABCDNT.markB
  let C := ordered4N OrderedABCDNT.markC
  let D := ordered4N OrderedABCDNT.markD
  let X := ordered4N OrderedABCDNT.x
  let Y := ordered4N OrderedABCDNT.y
  let Z := ordered4N OrderedABCDNT.z
  let Q := ordered4N OrderedABCDNT.q
  let a := ordered4T FourCountTerminal.a
  let b := ordered4T FourCountTerminal.b
  let c := ordered4T FourCountTerminal.c
  let d := ordered4T FourCountTerminal.d
  have h1 : GeneralGrammar.Yields OrderedABCDGrammar [S]
      [S, A, B, C, D] := by
    simpa [S, A, B, C, D] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.grow [] []
  have h2 :
      GeneralGrammar.Yields OrderedABCDGrammar [S, A, B, C, D]
        [S, A, B, C, D, A, B, C, D] := by
    simpa [S, A, B, C, D] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.grow [] [A, B, C, D]
  have h3 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [S, A, B, C, D, A, B, C, D]
        [X, A, B, C, D, A, B, C, D] := by
    simpa [S, A, B, C, D, X] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.startX [] [A, B, C, D, A, B, C, D]
  have h4 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [X, A, B, C, D, A, B, C, D]
        [X, A, B, C, A, D, B, C, D] := by
    simpa [X, A, B, C, D] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.swapDA [X, A, B, C] [B, C, D]
  have h5 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [X, A, B, C, A, D, B, C, D]
        [X, A, B, A, C, D, B, C, D] := by
    simpa [X, A, B, C, D] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.swapCA [X, A, B] [D, B, C, D]
  have h6 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [X, A, B, A, C, D, B, C, D]
        [X, A, A, B, C, D, B, C, D] := by
    simpa [X, A, B, C, D] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.swapBA [X, A] [C, D, B, C, D]
  have h7 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [X, A, A, B, C, D, B, C, D]
        [X, A, A, B, C, B, D, C, D] := by
    simpa [X, A, B, C, D] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.swapDB [X, A, A, B, C] [C, D]
  have h8 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [X, A, A, B, C, B, D, C, D]
        [X, A, A, B, B, C, D, C, D] := by
    simpa [X, A, B, C, D] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.swapCB [X, A, A, B] [D, C, D]
  have h9 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [X, A, A, B, B, C, D, C, D]
        [X, A, A, B, B, C, C, D, D] := by
    simpa [X, A, B, C, D] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.swapDC [X, A, A, B, B, C] [D]
  have h10 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [X, A, A, B, B, C, C, D, D]
        [a, X, A, B, B, C, C, D, D] := by
    simpa [X, A, B, C, D, a] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.convertXA [] [A, B, B, C, C, D, D]
  have h11 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, X, A, B, B, C, C, D, D]
        [a, a, X, B, B, C, C, D, D] := by
    simpa [X, A, B, C, D, a] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.convertXA [a] [B, B, C, C, D, D]
  have h12 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, a, X, B, B, C, C, D, D]
        [a, a, Y, B, B, C, C, D, D] := by
    simpa [X, Y, B, C, D, a] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.xToY [a, a] [B, B, C, C, D, D]
  have h13 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, a, Y, B, B, C, C, D, D]
        [a, a, b, Y, B, C, C, D, D] := by
    simpa [Y, B, C, D, a, b] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.convertYB [a, a] [B, C, C, D, D]
  have h14 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, a, b, Y, B, C, C, D, D]
        [a, a, b, b, Y, C, C, D, D] := by
    simpa [Y, B, C, D, a, b] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.convertYB [a, a, b] [C, C, D, D]
  have h15 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, a, b, b, Y, C, C, D, D]
        [a, a, b, b, Z, C, C, D, D] := by
    simpa [Y, Z, C, D, a, b] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.yToZ [a, a, b, b] [C, C, D, D]
  have h16 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, a, b, b, Z, C, C, D, D]
        [a, a, b, b, c, Z, C, D, D] := by
    simpa [Z, C, D, a, b, c] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.convertZC [a, a, b, b] [C, D, D]
  have h17 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, a, b, b, c, Z, C, D, D]
        [a, a, b, b, c, c, Z, D, D] := by
    simpa [Z, C, D, a, b, c] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.convertZC [a, a, b, b, c] [D, D]
  have h18 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, a, b, b, c, c, Z, D, D]
        [a, a, b, b, c, c, Q, D, D] := by
    simpa [Z, Q, D, a, b, c] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.zToQ [a, a, b, b, c, c] [D, D]
  have h19 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, a, b, b, c, c, Q, D, D]
        [a, a, b, b, c, c, d, Q, D] := by
    simpa [Q, D, a, b, c, d] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.convertQD [a, a, b, b, c, c] [D]
  have h20 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, a, b, b, c, c, d, Q, D]
        [a, a, b, b, c, c, d, d, Q] := by
    simpa [Q, D, a, b, c, d] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.convertQD [a, a, b, b, c, c, d] []
  have h21 :
      GeneralGrammar.Yields OrderedABCDGrammar
        [a, a, b, b, c, c, d, d, Q]
        [a, a, b, b, c, c, d, d] := by
    simpa [Q, a, b, c, d] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.finish [a, a, b, b, c, c, d, d] []
  have hderives :
      GeneralGrammar.Derives OrderedABCDGrammar [S]
        [a, a, b, b, c, c, d, d] :=
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
                                          (GeneralGrammar.Derives.step h20
                                            (GeneralGrammar.Derives.step h21
                                              (GeneralGrammar.Derives.refl
                                                [a, a, b, b, c, c, d,
                                                  d])))))))))))))))))))))
  simpa [GeneralGrammar.GeneratedLanguage, OrderedABCDGrammar, aabbccddWord,
    SententialForm.terminalWord, S, a, b, c, d] using hderives


end Section06
end Chapter04
end Book
end FoC
