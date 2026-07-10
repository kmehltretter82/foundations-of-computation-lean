import FoC.Book.Chapter04.Section06.FourCounts

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section06

/-!
# Section 4.6 ordered four-block counts

Book: Section 4.6, Exercise 4a (a grammar for the ordered four-block language
{lit}`a^n b^n c^n d^n`).
-/

open Languages
open Grammars

/-!
## Ordered Four-Block Counts

This example extends the ordered-block method of the second sample grammar to
four terminals. The grammar is intended to generate the words
{lit}`a^n b^n c^n d^n`, but this file does not prove that language equality in
either direction. What is proved: every generated word has equal counts of
{lit}`a`, {lit}`b`, {lit}`c`, and {lit}`d` (a count-preservation invariant,
which does not constrain the order of the letters), together with concrete
witness derivations of the empty word and of {lit}`aabbccdd`. Neither the
soundness inclusion (every generated word is ordered) nor the generation
inclusion (every {lit}`a^n b^n c^n d^n` is generated) is formalized. The
separate three-letter ordered example proves its analogue exactly.
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

theorem orderedABCDProductionList_valid :
    forall rule, rule ∈ OrderedABCDProductionList ->
      SententialForm.containsNonterminal rule.lhs := by
  intro rule h
  simp [OrderedABCDProductionList] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [SententialForm.containsNonterminal, ordered4N, ggNonterminal]

def OrderedABCDGrammar :
    GeneralGrammar FourCountTerminal OrderedABCDNT :=
  GeneralGrammar.ProductionList.toGeneralGrammar OrderedABCDNT.start
    OrderedABCDNT.finite OrderedABCDProductionList orderedABCDProductionList_valid

def orderedABCDPresentation : GeneralGrammar.Presentation OrderedABCDGrammar :=
  GeneralGrammar.ProductionList.presentation OrderedABCDNT.start
    OrderedABCDNT.finite OrderedABCDProductionList orderedABCDProductionList_valid

namespace OrderedABCDProduces

theorem grow :
      OrderedABCDGrammar.produces [ordered4N OrderedABCDNT.start]
        [ordered4N OrderedABCDNT.start, ordered4N OrderedABCDNT.markA,
          ordered4N OrderedABCDNT.markB, ordered4N OrderedABCDNT.markC,
          ordered4N OrderedABCDNT.markD] := by
  simp [OrderedABCDGrammar, GeneralGrammar.ProductionList.toGeneralGrammar,
    GeneralGrammar.ProductionListProduces, OrderedABCDProductionList]

theorem startX :
      OrderedABCDGrammar.produces [ordered4N OrderedABCDNT.start]
        [ordered4N OrderedABCDNT.x] := by
  simp [OrderedABCDGrammar, GeneralGrammar.ProductionList.toGeneralGrammar,
    GeneralGrammar.ProductionListProduces, OrderedABCDProductionList]

theorem swapBA :
      OrderedABCDGrammar.produces
        [ordered4N OrderedABCDNT.markB, ordered4N OrderedABCDNT.markA]
        [ordered4N OrderedABCDNT.markA, ordered4N OrderedABCDNT.markB] := by
  simp [OrderedABCDGrammar, GeneralGrammar.ProductionList.toGeneralGrammar,
    GeneralGrammar.ProductionListProduces, OrderedABCDProductionList]

theorem swapCA :
      OrderedABCDGrammar.produces
        [ordered4N OrderedABCDNT.markC, ordered4N OrderedABCDNT.markA]
        [ordered4N OrderedABCDNT.markA, ordered4N OrderedABCDNT.markC] := by
  simp [OrderedABCDGrammar, GeneralGrammar.ProductionList.toGeneralGrammar,
    GeneralGrammar.ProductionListProduces, OrderedABCDProductionList]

theorem swapDA :
      OrderedABCDGrammar.produces
        [ordered4N OrderedABCDNT.markD, ordered4N OrderedABCDNT.markA]
        [ordered4N OrderedABCDNT.markA, ordered4N OrderedABCDNT.markD] := by
  simp [OrderedABCDGrammar, GeneralGrammar.ProductionList.toGeneralGrammar,
    GeneralGrammar.ProductionListProduces, OrderedABCDProductionList]

theorem swapCB :
      OrderedABCDGrammar.produces
        [ordered4N OrderedABCDNT.markC, ordered4N OrderedABCDNT.markB]
        [ordered4N OrderedABCDNT.markB, ordered4N OrderedABCDNT.markC] := by
  simp [OrderedABCDGrammar, GeneralGrammar.ProductionList.toGeneralGrammar,
    GeneralGrammar.ProductionListProduces, OrderedABCDProductionList]

theorem swapDB :
      OrderedABCDGrammar.produces
        [ordered4N OrderedABCDNT.markD, ordered4N OrderedABCDNT.markB]
        [ordered4N OrderedABCDNT.markB, ordered4N OrderedABCDNT.markD] := by
  simp [OrderedABCDGrammar, GeneralGrammar.ProductionList.toGeneralGrammar,
    GeneralGrammar.ProductionListProduces, OrderedABCDProductionList]

theorem swapDC :
      OrderedABCDGrammar.produces
        [ordered4N OrderedABCDNT.markD, ordered4N OrderedABCDNT.markC]
        [ordered4N OrderedABCDNT.markC, ordered4N OrderedABCDNT.markD] := by
  simp [OrderedABCDGrammar, GeneralGrammar.ProductionList.toGeneralGrammar,
    GeneralGrammar.ProductionListProduces, OrderedABCDProductionList]

theorem convertXA :
      OrderedABCDGrammar.produces
        [ordered4N OrderedABCDNT.x, ordered4N OrderedABCDNT.markA]
        [ordered4T FourCountTerminal.a, ordered4N OrderedABCDNT.x] := by
  simp [OrderedABCDGrammar, GeneralGrammar.ProductionList.toGeneralGrammar,
    GeneralGrammar.ProductionListProduces, OrderedABCDProductionList]

theorem xToY :
      OrderedABCDGrammar.produces [ordered4N OrderedABCDNT.x]
        [ordered4N OrderedABCDNT.y] := by
  simp [OrderedABCDGrammar, GeneralGrammar.ProductionList.toGeneralGrammar,
    GeneralGrammar.ProductionListProduces, OrderedABCDProductionList]

theorem convertYB :
      OrderedABCDGrammar.produces
        [ordered4N OrderedABCDNT.y, ordered4N OrderedABCDNT.markB]
        [ordered4T FourCountTerminal.b, ordered4N OrderedABCDNT.y] := by
  simp [OrderedABCDGrammar, GeneralGrammar.ProductionList.toGeneralGrammar,
    GeneralGrammar.ProductionListProduces, OrderedABCDProductionList]

theorem yToZ :
      OrderedABCDGrammar.produces [ordered4N OrderedABCDNT.y]
        [ordered4N OrderedABCDNT.z] := by
  simp [OrderedABCDGrammar, GeneralGrammar.ProductionList.toGeneralGrammar,
    GeneralGrammar.ProductionListProduces, OrderedABCDProductionList]

theorem convertZC :
      OrderedABCDGrammar.produces
        [ordered4N OrderedABCDNT.z, ordered4N OrderedABCDNT.markC]
        [ordered4T FourCountTerminal.c, ordered4N OrderedABCDNT.z] := by
  simp [OrderedABCDGrammar, GeneralGrammar.ProductionList.toGeneralGrammar,
    GeneralGrammar.ProductionListProduces, OrderedABCDProductionList]

theorem zToQ :
      OrderedABCDGrammar.produces [ordered4N OrderedABCDNT.z]
        [ordered4N OrderedABCDNT.q] := by
  simp [OrderedABCDGrammar, GeneralGrammar.ProductionList.toGeneralGrammar,
    GeneralGrammar.ProductionListProduces, OrderedABCDProductionList]

theorem convertQD :
      OrderedABCDGrammar.produces
        [ordered4N OrderedABCDNT.q, ordered4N OrderedABCDNT.markD]
        [ordered4T FourCountTerminal.d, ordered4N OrderedABCDNT.q] := by
  simp [OrderedABCDGrammar, GeneralGrammar.ProductionList.toGeneralGrammar,
    GeneralGrammar.ProductionListProduces, OrderedABCDProductionList]

theorem finish :
      OrderedABCDGrammar.produces [ordered4N OrderedABCDNT.q] []
 := by
  simp [OrderedABCDGrammar, GeneralGrammar.ProductionList.toGeneralGrammar,
    GeneralGrammar.ProductionListProduces, OrderedABCDProductionList]

end OrderedABCDProduces

/-!
The ordered four-block example repeats the ordered three-block pattern at
larger scale. The long production list consists of grow rules, marker-sorting
rules, phase-change rules, terminal-emission rules, and one final cleanup rule.
-/

theorem orderedABCDGrammar_has_finite_productions :
    GeneralGrammar.HasFiniteProductions OrderedABCDGrammar :=
  orderedABCDPresentation.hasFiniteProductions
theorem orderedABCDGrammar_finite_production_generated :
    FiniteProductionGeneralLanguage
      (GeneralGrammar.GeneratedLanguage OrderedABCDGrammar) := by
  exists OrderedABCDNT
  exists OrderedABCDGrammar
  constructor
  · exact GeneralGrammar.hasFinitePresentation_of_hasFiniteProductions
      orderedABCDGrammar_has_finite_productions
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
                          change GeneralGrammar.ProductionListProduces
                            OrderedABCDProductionList lhs rhs at hprod
                          rcases hprod with ⟨rule, hmem, rfl, rfl⟩
                          simp [OrderedABCDProductionList] at hmem
                          rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                            simp [orderedABCDBalanced, orderedABCDTotalA,
                              orderedABCDTotalB, orderedABCDTotalC,
                              orderedABCDTotalD,
                              sententialCountTerminal_append,
                              sententialCountNonterminal_append,
                              SententialCountTerminal,
                              SententialCountNonterminal, ordered4N,
                              ordered4T, ggNonterminal, ggTerminal] at hbalanced ⊢ <;>
                            lia

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
      ggNonterminal] using! h
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
The two explicit derivations below are sanity checks for the four-block
grammar: the empty word (finishing immediately through the phase
nonterminals) and {lit}`aabbccdd` (two grow steps, marker sorting, and the
four emission phases). They are individual witnesses, not a proof that every
ordered four-block word is generated.
-/

theorem orderedABCDGrammar_generates_empty :
    (Word.Empty : Word FourCountTerminal) ∈
      GeneralGrammar.GeneratedLanguage OrderedABCDGrammar := by
  let S := ordered4N OrderedABCDNT.start
  let X := ordered4N OrderedABCDNT.x
  let Y := ordered4N OrderedABCDNT.y
  let Z := ordered4N OrderedABCDNT.z
  let Q := ordered4N OrderedABCDNT.q
  have h1 : GeneralGrammar.Yields OrderedABCDGrammar [S] [X] := by
    simpa [S, X] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.startX [] []
  have h2 : GeneralGrammar.Yields OrderedABCDGrammar [X] [Y] := by
    simpa [X, Y] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.xToY [] []
  have h3 : GeneralGrammar.Yields OrderedABCDGrammar [Y] [Z] := by
    simpa [Y, Z] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.yToZ [] []
  have h4 : GeneralGrammar.Yields OrderedABCDGrammar [Z] [Q] := by
    simpa [Z, Q] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.zToQ [] []
  have h5 : GeneralGrammar.Yields OrderedABCDGrammar [Q] [] := by
    simpa [Q] using
      general_yields_of_production (G := OrderedABCDGrammar)
        OrderedABCDProduces.finish [] []
  have hderives :
      GeneralGrammar.Derives OrderedABCDGrammar [S] [] :=
    GeneralGrammar.Derives.step h1
      (GeneralGrammar.Derives.step h2
        (GeneralGrammar.Derives.step h3
          (GeneralGrammar.Derives.step h4
            (GeneralGrammar.Derives.step h5
              (GeneralGrammar.Derives.refl [])))))
  simpa [GeneralGrammar.GeneratedLanguage, OrderedABCDGrammar, Word.Empty,
    SententialForm.terminalWord, S, ordered4N, ggNonterminal] using! hderives

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
    SententialForm.terminalWord, S, a, b, c, d] using! hderives


end Section06
end Chapter04
end Book
end FoC
