import FoC.Book.Chapter04.Section06.Basics

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section06

/-!
# Section 4.6 equal counts over three symbols
-/

open Languages
open Grammars

/-!
# Equal Counts over Three Symbols

The first unrestricted grammar generates all words with the same number of
{lit}`a`, {lit}`b`, and {lit}`c` symbols, regardless of order. It grows one marker of each
kind, freely swaps markers, and then emits terminals. The proof separates
count preservation from explicit generation of any balanced word.
-/

inductive EqualCountTerminal where
  | a
  | b
  | c
deriving DecidableEq

inductive EqualCountNT where
  | start
  | markA
  | markB
  | markC
deriving DecidableEq

namespace EqualCountNT

def finite : Foundation.FiniteType EqualCountNT where
  elems := [start, markA, markB, markC]
  complete := by
    intro A
    cases A <;> simp

end EqualCountNT

def ecT (tok : EqualCountTerminal) :
    Symbol EqualCountTerminal EqualCountNT :=
  ggTerminal tok

def ecN (A : EqualCountNT) :
    Symbol EqualCountTerminal EqualCountNT :=
  ggNonterminal A

inductive EqualCountProduces :
    SententialForm EqualCountTerminal EqualCountNT ->
      SententialForm EqualCountTerminal EqualCountNT -> Prop where
  | grow :
      EqualCountProduces [ecN EqualCountNT.start]
        [ecN EqualCountNT.start, ecN EqualCountNT.markA,
          ecN EqualCountNT.markB, ecN EqualCountNT.markC]
  | stop :
      EqualCountProduces [ecN EqualCountNT.start] []
  | swapAB :
      EqualCountProduces [ecN EqualCountNT.markA, ecN EqualCountNT.markB]
        [ecN EqualCountNT.markB, ecN EqualCountNT.markA]
  | swapBA :
      EqualCountProduces [ecN EqualCountNT.markB, ecN EqualCountNT.markA]
        [ecN EqualCountNT.markA, ecN EqualCountNT.markB]
  | swapAC :
      EqualCountProduces [ecN EqualCountNT.markA, ecN EqualCountNT.markC]
        [ecN EqualCountNT.markC, ecN EqualCountNT.markA]
  | swapCA :
      EqualCountProduces [ecN EqualCountNT.markC, ecN EqualCountNT.markA]
        [ecN EqualCountNT.markA, ecN EqualCountNT.markC]
  | swapBC :
      EqualCountProduces [ecN EqualCountNT.markB, ecN EqualCountNT.markC]
        [ecN EqualCountNT.markC, ecN EqualCountNT.markB]
  | swapCB :
      EqualCountProduces [ecN EqualCountNT.markC, ecN EqualCountNT.markB]
        [ecN EqualCountNT.markB, ecN EqualCountNT.markC]
  | emitA :
      EqualCountProduces [ecN EqualCountNT.markA]
        [ecT EqualCountTerminal.a]
  | emitB :
      EqualCountProduces [ecN EqualCountNT.markB]
        [ecT EqualCountTerminal.b]
  | emitC :
      EqualCountProduces [ecN EqualCountNT.markC]
        [ecT EqualCountTerminal.c]

def EqualCountGrammar :
    GeneralGrammar EqualCountTerminal EqualCountNT where
  start := EqualCountNT.start
  produces := EqualCountProduces
  lhsContainsNonterminal := by
    intro lhs rhs h
    cases h <;> simp [SententialForm.containsNonterminal, ecN,
      ggNonterminal]
  nonterminalsFinite := EqualCountNT.finite

def EqualCountProductionList :
    List (GeneralGrammar.Production EqualCountTerminal EqualCountNT) :=
  [{ lhs := [ecN EqualCountNT.start],
     rhs := [ecN EqualCountNT.start, ecN EqualCountNT.markA,
       ecN EqualCountNT.markB, ecN EqualCountNT.markC] },
   { lhs := [ecN EqualCountNT.start],
     rhs := [] },
   { lhs := [ecN EqualCountNT.markA, ecN EqualCountNT.markB],
     rhs := [ecN EqualCountNT.markB, ecN EqualCountNT.markA] },
   { lhs := [ecN EqualCountNT.markB, ecN EqualCountNT.markA],
     rhs := [ecN EqualCountNT.markA, ecN EqualCountNT.markB] },
   { lhs := [ecN EqualCountNT.markA, ecN EqualCountNT.markC],
     rhs := [ecN EqualCountNT.markC, ecN EqualCountNT.markA] },
   { lhs := [ecN EqualCountNT.markC, ecN EqualCountNT.markA],
     rhs := [ecN EqualCountNT.markA, ecN EqualCountNT.markC] },
   { lhs := [ecN EqualCountNT.markB, ecN EqualCountNT.markC],
     rhs := [ecN EqualCountNT.markC, ecN EqualCountNT.markB] },
   { lhs := [ecN EqualCountNT.markC, ecN EqualCountNT.markB],
     rhs := [ecN EqualCountNT.markB, ecN EqualCountNT.markC] },
   { lhs := [ecN EqualCountNT.markA],
     rhs := [ecT EqualCountTerminal.a] },
   { lhs := [ecN EqualCountNT.markB],
     rhs := [ecT EqualCountTerminal.b] },
   { lhs := [ecN EqualCountNT.markC],
     rhs := [ecT EqualCountTerminal.c] }]

theorem equalCountGrammar_has_finite_productions :
    GeneralGrammar.HasFiniteProductions EqualCountGrammar := by
  exists EqualCountProductionList
  intro lhs rhs
  constructor
  · intro h
    cases h <;> simp [EqualCountProductionList]
  · intro h
    rcases h with ⟨rule, hmem, hlhs, hrhs⟩
    simp [EqualCountProductionList] at hmem
    rcases hmem with
      hrule | hrule | hrule | hrule | hrule | hrule |
      hrule | hrule | hrule | hrule | hrule
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.grow
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.stop
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.swapAB
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.swapBA
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.swapAC
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.swapCA
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.swapBC
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.swapCB
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.emitA
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.emitB
    · subst rule
      cases hlhs
      cases hrhs
      exact EqualCountProduces.emitC

theorem equalCountGrammar_finite_production_generated :
    FiniteProductionGeneralLanguage
      (GeneralGrammar.GeneratedLanguage EqualCountGrammar) := by
  exists EqualCountNT
  exists EqualCountGrammar
  constructor
  · exact equalCountGrammar_has_finite_productions
  · intro w
    rfl

/-!
Soundness for this grammar is an invariant proof. Terminals already emitted and
markers not yet emitted are counted together; every production preserves the
total number of future {lit}`a`s, {lit}`b`s, and {lit}`c`s.
-/

def equalCountTotalA (sf : SententialForm EqualCountTerminal EqualCountNT) :
    Nat :=
  SententialCountTerminal EqualCountTerminal.a sf +
    SententialCountNonterminal EqualCountNT.markA sf

def equalCountTotalB (sf : SententialForm EqualCountTerminal EqualCountNT) :
    Nat :=
  SententialCountTerminal EqualCountTerminal.b sf +
    SententialCountNonterminal EqualCountNT.markB sf

def equalCountTotalC (sf : SententialForm EqualCountTerminal EqualCountNT) :
    Nat :=
  SententialCountTerminal EqualCountTerminal.c sf +
    SententialCountNonterminal EqualCountNT.markC sf

def equalCountBalanced
    (sf : SententialForm EqualCountTerminal EqualCountNT) : Prop :=
  equalCountTotalA sf = equalCountTotalB sf ∧
    equalCountTotalB sf = equalCountTotalC sf

theorem equalCount_start_balanced :
    equalCountBalanced [ecN EqualCountNT.start] := by
  simp [equalCountBalanced, equalCountTotalA, equalCountTotalB,
    equalCountTotalC, SententialCountTerminal, SententialCountNonterminal,
    ecN, ggNonterminal]

theorem equalCount_yields_preserves_balanced
    {x y : SententialForm EqualCountTerminal EqualCountNT}
    (h : GeneralGrammar.Yields EqualCountGrammar x y) :
    equalCountBalanced x -> equalCountBalanced y := by
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
                            simp [equalCountBalanced, equalCountTotalA,
                              equalCountTotalB, equalCountTotalC,
                              sententialCountTerminal_append,
                              sententialCountNonterminal_append,
                              SententialCountTerminal,
                              SententialCountNonterminal, ecN, ecT,
                              ggNonterminal, ggTerminal] at hbalanced ⊢ <;>
                            omega

theorem equalCount_derives_preserves_balanced
    {x y : SententialForm EqualCountTerminal EqualCountNT}
    (h : GeneralGrammar.Derives EqualCountGrammar x y) :
    equalCountBalanced x -> equalCountBalanced y := by
  induction h with
  | refl _ =>
      intro hbalanced
      exact hbalanced
  | step hstep _ ih =>
      intro hbalanced
      exact ih (equalCount_yields_preserves_balanced hstep hbalanced)

theorem equalCountGrammar_generated_has_equal_terminal_counts
    {w : Word EqualCountTerminal}
    (h : w ∈ GeneralGrammar.GeneratedLanguage EqualCountGrammar) :
    Word.Count EqualCountTerminal.a w = Word.Count EqualCountTerminal.b w ∧
      Word.Count EqualCountTerminal.b w = Word.Count EqualCountTerminal.c w := by
  have hderives :
      GeneralGrammar.Derives EqualCountGrammar [ecN EqualCountNT.start]
        (SententialForm.terminalWord w) := by
    simpa [GeneralGrammar.GeneratedLanguage, EqualCountGrammar, ecN,
      ggNonterminal] using h
  have hbalanced :=
    equalCount_derives_preserves_balanced hderives equalCount_start_balanced
  simpa [equalCountBalanced, equalCountTotalA, equalCountTotalB,
    equalCountTotalC, sententialCountTerminal_terminalWord,
    sententialCountNonterminal_terminalWord] using hbalanced

def equalCountLanguage : Language EqualCountTerminal :=
  fun w =>
    Word.Count EqualCountTerminal.a w = Word.Count EqualCountTerminal.b w ∧
      Word.Count EqualCountTerminal.b w = Word.Count EqualCountTerminal.c w

def equalCountAForm (n : Nat) :
    SententialForm EqualCountTerminal EqualCountNT :=
  List.replicate n (ecN EqualCountNT.markA)

def equalCountBForm (n : Nat) :
    SententialForm EqualCountTerminal EqualCountNT :=
  List.replicate n (ecN EqualCountNT.markB)

def equalCountCForm (n : Nat) :
    SententialForm EqualCountTerminal EqualCountNT :=
  List.replicate n (ecN EqualCountNT.markC)

def equalCountMarkerBlock :
    SententialForm EqualCountTerminal EqualCountNT :=
  [ecN EqualCountNT.markA, ecN EqualCountNT.markB,
    ecN EqualCountNT.markC]

def equalCountRepeatedMarkers (n : Nat) :
    SententialForm EqualCountTerminal EqualCountNT :=
  Word.RepeatWord equalCountMarkerBlock n

def equalCountMarkerBag (aCount bCount cCount : Nat) :
    SententialForm EqualCountTerminal EqualCountNT :=
  equalCountAForm aCount ++ equalCountBForm bCount ++
    equalCountCForm cCount

def equalCountMarkerOfTerminal :
    EqualCountTerminal -> EqualCountNT
  | EqualCountTerminal.a => EqualCountNT.markA
  | EqualCountTerminal.b => EqualCountNT.markB
  | EqualCountTerminal.c => EqualCountNT.markC

def equalCountMarkerWord (w : Word EqualCountTerminal) :
    SententialForm EqualCountTerminal EqualCountNT :=
  w.map (fun token => ecN (equalCountMarkerOfTerminal token))

/-!
Completeness is constructive. First grow a bag with the same number of
{lit}`A`, {lit}`B`, and {lit}`C` markers. Then use swap rules to reorder the bag
so it matches the target word's symbol order, and finally emit terminals from
those markers.
-/

theorem equalCount_moveB_left_over_as
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal EqualCountNT) :
    GeneralGrammar.Derives EqualCountGrammar
      (pre ++ equalCountAForm n ++ [ecN EqualCountNT.markB] ++ suffix)
      (pre ++ [ecN EqualCountNT.markB] ++ equalCountAForm n ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [equalCountAForm, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := EqualCountGrammar)
          (pre ++ [ecN EqualCountNT.markB] ++ suffix))
  | succ n ih =>
      let A := ecN EqualCountNT.markA
      let B := ecN EqualCountNT.markB
      have htail :
          GeneralGrammar.Derives EqualCountGrammar
            (pre ++ [A] ++ equalCountAForm n ++ [B] ++ suffix)
            (pre ++ [A] ++ [B] ++ equalCountAForm n ++ suffix) := by
        simpa [A, B, List.append_assoc] using ih (pre ++ [A])
      have hswap :
          GeneralGrammar.Yields EqualCountGrammar
            (pre ++ [A] ++ [B] ++ equalCountAForm n ++ suffix)
            (pre ++ [B] ++ [A] ++ equalCountAForm n ++ suffix) := by
        simpa [A, B, List.append_assoc] using
          general_yields_of_production (G := EqualCountGrammar)
            EqualCountProduces.swapAB pre (equalCountAForm n ++ suffix)
      have hall := GeneralGrammar.derives_trans htail
        (GeneralGrammar.yields_derives hswap)
      simpa [equalCountAForm, A, B, List.append_assoc] using hall

theorem equalCount_moveC_left_over_as
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal EqualCountNT) :
    GeneralGrammar.Derives EqualCountGrammar
      (pre ++ equalCountAForm n ++ [ecN EqualCountNT.markC] ++ suffix)
      (pre ++ [ecN EqualCountNT.markC] ++ equalCountAForm n ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [equalCountAForm, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := EqualCountGrammar)
          (pre ++ [ecN EqualCountNT.markC] ++ suffix))
  | succ n ih =>
      let A := ecN EqualCountNT.markA
      let C := ecN EqualCountNT.markC
      have htail :
          GeneralGrammar.Derives EqualCountGrammar
            (pre ++ [A] ++ equalCountAForm n ++ [C] ++ suffix)
            (pre ++ [A] ++ [C] ++ equalCountAForm n ++ suffix) := by
        simpa [A, C, List.append_assoc] using ih (pre ++ [A])
      have hswap :
          GeneralGrammar.Yields EqualCountGrammar
            (pre ++ [A] ++ [C] ++ equalCountAForm n ++ suffix)
            (pre ++ [C] ++ [A] ++ equalCountAForm n ++ suffix) := by
        simpa [A, C, List.append_assoc] using
          general_yields_of_production (G := EqualCountGrammar)
            EqualCountProduces.swapAC pre (equalCountAForm n ++ suffix)
      have hall := GeneralGrammar.derives_trans htail
        (GeneralGrammar.yields_derives hswap)
      simpa [equalCountAForm, A, C, List.append_assoc] using hall

theorem equalCount_moveC_left_over_bs
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal EqualCountNT) :
    GeneralGrammar.Derives EqualCountGrammar
      (pre ++ equalCountBForm n ++ [ecN EqualCountNT.markC] ++ suffix)
      (pre ++ [ecN EqualCountNT.markC] ++ equalCountBForm n ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [equalCountBForm, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := EqualCountGrammar)
          (pre ++ [ecN EqualCountNT.markC] ++ suffix))
  | succ n ih =>
      let B := ecN EqualCountNT.markB
      let C := ecN EqualCountNT.markC
      have htail :
          GeneralGrammar.Derives EqualCountGrammar
            (pre ++ [B] ++ equalCountBForm n ++ [C] ++ suffix)
            (pre ++ [B] ++ [C] ++ equalCountBForm n ++ suffix) := by
        simpa [B, C, List.append_assoc] using ih (pre ++ [B])
      have hswap :
          GeneralGrammar.Yields EqualCountGrammar
            (pre ++ [B] ++ [C] ++ equalCountBForm n ++ suffix)
            (pre ++ [C] ++ [B] ++ equalCountBForm n ++ suffix) := by
        simpa [B, C, List.append_assoc] using
          general_yields_of_production (G := EqualCountGrammar)
            EqualCountProduces.swapBC pre (equalCountBForm n ++ suffix)
      have hall := GeneralGrammar.derives_trans htail
        (GeneralGrammar.yields_derives hswap)
      simpa [equalCountBForm, B, C, List.append_assoc] using hall

theorem equalCount_moveC_right_over_as
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal EqualCountNT) :
    GeneralGrammar.Derives EqualCountGrammar
      (pre ++ [ecN EqualCountNT.markC] ++ equalCountAForm n ++ suffix)
      (pre ++ equalCountAForm n ++ [ecN EqualCountNT.markC] ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [equalCountAForm] using
        (GeneralGrammar.Derives.refl (G := EqualCountGrammar)
          (pre ++ [ecN EqualCountNT.markC] ++ suffix))
  | succ n ih =>
      let A := ecN EqualCountNT.markA
      let C := ecN EqualCountNT.markC
      have hstep :
          GeneralGrammar.Yields EqualCountGrammar
            (pre ++ [C, A] ++ equalCountAForm n ++ suffix)
            (pre ++ [A, C] ++ equalCountAForm n ++ suffix) := by
        simpa [A, C, List.append_assoc] using
          general_yields_of_production (G := EqualCountGrammar)
            EqualCountProduces.swapCA pre (equalCountAForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives EqualCountGrammar
            (pre ++ [A, C] ++ equalCountAForm n ++ suffix)
            (pre ++ [A] ++ equalCountAForm n ++ [C] ++ suffix) := by
        simpa [A, C, List.append_assoc] using ih (pre ++ [A])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [equalCountAForm, A, C, List.append_assoc] using hall

theorem equalCount_moveB_right_over_as
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal EqualCountNT) :
    GeneralGrammar.Derives EqualCountGrammar
      (pre ++ [ecN EqualCountNT.markB] ++ equalCountAForm n ++ suffix)
      (pre ++ equalCountAForm n ++ [ecN EqualCountNT.markB] ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [equalCountAForm] using
        (GeneralGrammar.Derives.refl (G := EqualCountGrammar)
          (pre ++ [ecN EqualCountNT.markB] ++ suffix))
  | succ n ih =>
      let A := ecN EqualCountNT.markA
      let B := ecN EqualCountNT.markB
      have hstep :
          GeneralGrammar.Yields EqualCountGrammar
            (pre ++ [B, A] ++ equalCountAForm n ++ suffix)
            (pre ++ [A, B] ++ equalCountAForm n ++ suffix) := by
        simpa [A, B, List.append_assoc] using
          general_yields_of_production (G := EqualCountGrammar)
            EqualCountProduces.swapBA pre (equalCountAForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives EqualCountGrammar
            (pre ++ [A, B] ++ equalCountAForm n ++ suffix)
            (pre ++ [A] ++ equalCountAForm n ++ [B] ++ suffix) := by
        simpa [A, B, List.append_assoc] using ih (pre ++ [A])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [equalCountAForm, A, B, List.append_assoc] using hall

theorem equalCount_moveC_right_over_bs
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal EqualCountNT) :
    GeneralGrammar.Derives EqualCountGrammar
      (pre ++ [ecN EqualCountNT.markC] ++ equalCountBForm n ++ suffix)
      (pre ++ equalCountBForm n ++ [ecN EqualCountNT.markC] ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [equalCountBForm] using
        (GeneralGrammar.Derives.refl (G := EqualCountGrammar)
          (pre ++ [ecN EqualCountNT.markC] ++ suffix))
  | succ n ih =>
      let B := ecN EqualCountNT.markB
      let C := ecN EqualCountNT.markC
      have hstep :
          GeneralGrammar.Yields EqualCountGrammar
            (pre ++ [C, B] ++ equalCountBForm n ++ suffix)
            (pre ++ [B, C] ++ equalCountBForm n ++ suffix) := by
        simpa [B, C, List.append_assoc] using
          general_yields_of_production (G := EqualCountGrammar)
            EqualCountProduces.swapCB pre (equalCountBForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives EqualCountGrammar
            (pre ++ [B, C] ++ equalCountBForm n ++ suffix)
            (pre ++ [B] ++ equalCountBForm n ++ [C] ++ suffix) := by
        simpa [B, C, List.append_assoc] using ih (pre ++ [B])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [equalCountBForm, B, C, List.append_assoc] using hall

/-!
The equal-count grammar first creates marker symbols and then sorts them into a
terminal word. The move lemmas below commute markers past each other; the sort
theorem packages those local swaps into a reusable derivation.
-/

theorem equalCount_sort_repeated_markers_derives (n : Nat) :
    GeneralGrammar.Derives EqualCountGrammar
      (equalCountRepeatedMarkers n)
      (equalCountMarkerBag n n n) := by
  induction n with
  | zero =>
      exact GeneralGrammar.Derives.refl []
  | succ n ih =>
      let A := ecN EqualCountNT.markA
      let B := ecN EqualCountNT.markB
      let C := ecN EqualCountNT.markC
      have hsortTail :
          GeneralGrammar.Derives EqualCountGrammar
            (equalCountMarkerBlock ++ equalCountRepeatedMarkers n)
            (equalCountMarkerBlock ++ equalCountMarkerBag n n n) := by
        simpa [equalCountMarkerBlock, equalCountMarkerBag, A, B, C,
          List.append_assoc] using
          general_derives_context ih equalCountMarkerBlock []
      have hmoveCAs :
          GeneralGrammar.Derives EqualCountGrammar
            (equalCountMarkerBlock ++ equalCountMarkerBag n n n)
            ([A, B] ++ equalCountAForm n ++ [C] ++
              equalCountBForm n ++ equalCountCForm n) := by
        simpa [equalCountMarkerBlock, equalCountMarkerBag, A, B, C,
          List.append_assoc] using
          equalCount_moveC_right_over_as n [A, B]
            (equalCountBForm n ++ equalCountCForm n)
      have hmoveBAs :
          GeneralGrammar.Derives EqualCountGrammar
            ([A, B] ++ equalCountAForm n ++ [C] ++
              equalCountBForm n ++ equalCountCForm n)
            ([A] ++ equalCountAForm n ++ [B, C] ++
              equalCountBForm n ++ equalCountCForm n) := by
        simpa [A, B, C, List.append_assoc] using
          equalCount_moveB_right_over_as n [A]
            ([C] ++ equalCountBForm n ++ equalCountCForm n)
      have hmoveCBs :
          GeneralGrammar.Derives EqualCountGrammar
            ([A] ++ equalCountAForm n ++ [B, C] ++
              equalCountBForm n ++ equalCountCForm n)
            (equalCountMarkerBag (n + 1) (n + 1) (n + 1)) := by
        simpa [equalCountMarkerBag, equalCountAForm, equalCountBForm,
          equalCountCForm, A, B, C, List.append_assoc] using
          equalCount_moveC_right_over_bs n
            ([A] ++ equalCountAForm n ++ [B]) (equalCountCForm n)
      exact GeneralGrammar.derives_trans hsortTail
        (GeneralGrammar.derives_trans hmoveCAs
          (GeneralGrammar.derives_trans hmoveBAs hmoveCBs))

theorem equalCount_grow_repeated_markers_derives (n : Nat) :
    GeneralGrammar.Derives EqualCountGrammar [ecN EqualCountNT.start]
      ([ecN EqualCountNT.start] ++ equalCountRepeatedMarkers n) := by
  induction n with
  | zero =>
      simpa [equalCountRepeatedMarkers, Word.RepeatWord] using
        (GeneralGrammar.Derives.refl (G := EqualCountGrammar)
          [ecN EqualCountNT.start])
  | succ n ih =>
      have hstep :
          GeneralGrammar.Yields EqualCountGrammar
            ([ecN EqualCountNT.start] ++ equalCountRepeatedMarkers n)
            ([ecN EqualCountNT.start] ++ equalCountMarkerBlock ++
              equalCountRepeatedMarkers n) := by
        simpa [equalCountMarkerBlock, List.append_assoc] using
          general_yields_of_production (G := EqualCountGrammar)
            EqualCountProduces.grow [] (equalCountRepeatedMarkers n)
      have hall := GeneralGrammar.derives_trans ih
        (GeneralGrammar.yields_derives hstep)
      simpa [equalCountRepeatedMarkers, equalCountMarkerBlock,
        Word.RepeatWord, List.append_assoc] using hall

theorem equalCount_start_to_marker_bag_derives (n : Nat) :
    GeneralGrammar.Derives EqualCountGrammar [ecN EqualCountNT.start]
      (equalCountMarkerBag n n n) := by
  have hgrow := equalCount_grow_repeated_markers_derives n
  have hstop :
      GeneralGrammar.Yields EqualCountGrammar
        ([ecN EqualCountNT.start] ++ equalCountRepeatedMarkers n)
        (equalCountRepeatedMarkers n) := by
    simpa [List.append_assoc] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.stop [] (equalCountRepeatedMarkers n)
  exact GeneralGrammar.derives_trans hgrow
    (GeneralGrammar.derives_trans (GeneralGrammar.yields_derives hstop)
      (equalCount_sort_repeated_markers_derives n))

/-!
After the marker bag has been sorted, the conversion lemmas replace each marker
with its terminal symbol. This is the bridge from the grammar's bookkeeping
phase back to the visible word language.
-/

theorem equalCount_marker_bag_to_marker_word_derives
    (word : Word EqualCountTerminal)
    (aCount bCount cCount : Nat)
    (ha : Word.Count EqualCountTerminal.a word <= aCount)
    (hb : Word.Count EqualCountTerminal.b word <= bCount)
    (hc : Word.Count EqualCountTerminal.c word <= cCount) :
    GeneralGrammar.Derives EqualCountGrammar
      (equalCountMarkerBag aCount bCount cCount)
      (equalCountMarkerWord word ++
        equalCountMarkerBag
          (aCount - Word.Count EqualCountTerminal.a word)
          (bCount - Word.Count EqualCountTerminal.b word)
          (cCount - Word.Count EqualCountTerminal.c word)) := by
  induction word generalizing aCount bCount cCount with
  | nil =>
      simpa [equalCountMarkerWord, equalCountMarkerBag, Word.Count] using
        (GeneralGrammar.Derives.refl (G := EqualCountGrammar)
          (equalCountMarkerBag aCount bCount cCount))
  | cons token rest ih =>
      cases token with
      | a =>
          cases aCount with
          | zero =>
              simp [Word.Count] at ha
          | succ aRest =>
              have haRest :
                  Word.Count EqualCountTerminal.a rest <= aRest := by
                simp [Word.Count] at ha
                omega
              have hbRest :
                  Word.Count EqualCountTerminal.b rest <= bCount := by
                simpa [Word.Count] using hb
              have hcRest :
                  Word.Count EqualCountTerminal.c rest <= cCount := by
                simpa [Word.Count] using hc
              have hrest :=
                ih aRest bCount cCount haRest hbRest hcRest
              have hcontext :
                  GeneralGrammar.Derives EqualCountGrammar
                    ([ecN EqualCountNT.markA] ++
                      equalCountMarkerBag aRest bCount cCount)
                    ([ecN EqualCountNT.markA] ++
                      equalCountMarkerWord rest ++
                      equalCountMarkerBag
                        (aRest - Word.Count EqualCountTerminal.a rest)
                        (bCount - Word.Count EqualCountTerminal.b rest)
                        (cCount - Word.Count EqualCountTerminal.c rest)) := by
                simpa [List.append_assoc] using
                  general_derives_context hrest [ecN EqualCountNT.markA] []
              have hsubA :
                  aRest + 1 -
                      (1 + Word.Count EqualCountTerminal.a rest) =
                    aRest - Word.Count EqualCountTerminal.a rest := by
                omega
              have hrepA :
                  List.replicate (aRest + 1) (ecN EqualCountNT.markA) =
                    ecN EqualCountNT.markA :: equalCountAForm aRest := by
                rfl
              simpa [equalCountMarkerBag, equalCountAForm,
                equalCountMarkerWord, equalCountMarkerOfTerminal,
                Word.Count, hsubA, hrepA, List.append_assoc] using hcontext
      | b =>
          cases bCount with
          | zero =>
              simp [Word.Count] at hb
          | succ bRest =>
              have haRest :
                  Word.Count EqualCountTerminal.a rest <= aCount := by
                simpa [Word.Count] using ha
              have hbRest :
                  Word.Count EqualCountTerminal.b rest <= bRest := by
                simp [Word.Count] at hb
                omega
              have hcRest :
                  Word.Count EqualCountTerminal.c rest <= cCount := by
                simpa [Word.Count] using hc
              have hmove :
                  GeneralGrammar.Derives EqualCountGrammar
                    (equalCountMarkerBag aCount (bRest + 1) cCount)
                    ([ecN EqualCountNT.markB] ++
                      equalCountMarkerBag aCount bRest cCount) := by
                simpa [equalCountMarkerBag, equalCountBForm,
                  List.append_assoc] using
                  equalCount_moveB_left_over_as aCount []
                    (equalCountBForm bRest ++ equalCountCForm cCount)
              have hrest :=
                ih aCount bRest cCount haRest hbRest hcRest
              have hcontext :
                  GeneralGrammar.Derives EqualCountGrammar
                    ([ecN EqualCountNT.markB] ++
                      equalCountMarkerBag aCount bRest cCount)
                    ([ecN EqualCountNT.markB] ++
                      equalCountMarkerWord rest ++
                      equalCountMarkerBag
                        (aCount - Word.Count EqualCountTerminal.a rest)
                        (bRest - Word.Count EqualCountTerminal.b rest)
                        (cCount - Word.Count EqualCountTerminal.c rest)) := by
                simpa [List.append_assoc] using
                  general_derives_context hrest [ecN EqualCountNT.markB] []
              have hall := GeneralGrammar.derives_trans hmove hcontext
              have hsubB :
                  bRest + 1 -
                      (1 + Word.Count EqualCountTerminal.b rest) =
                    bRest - Word.Count EqualCountTerminal.b rest := by
                omega
              simpa [equalCountMarkerBag, equalCountBForm,
                equalCountMarkerWord, equalCountMarkerOfTerminal,
                Word.Count, hsubB, List.append_assoc] using hall
      | c =>
          cases cCount with
          | zero =>
              simp [Word.Count] at hc
          | succ cRest =>
              have haRest :
                  Word.Count EqualCountTerminal.a rest <= aCount := by
                simpa [Word.Count] using ha
              have hbRest :
                  Word.Count EqualCountTerminal.b rest <= bCount := by
                simpa [Word.Count] using hb
              have hcRest :
                  Word.Count EqualCountTerminal.c rest <= cRest := by
                simp [Word.Count] at hc
                omega
              have hmoveBs :
                  GeneralGrammar.Derives EqualCountGrammar
                    (equalCountMarkerBag aCount bCount (cRest + 1))
                    (equalCountAForm aCount ++ [ecN EqualCountNT.markC] ++
                      equalCountBForm bCount ++ equalCountCForm cRest) := by
                simpa [equalCountMarkerBag, equalCountCForm,
                  List.append_assoc] using
                  equalCount_moveC_left_over_bs bCount
                    (equalCountAForm aCount) (equalCountCForm cRest)
              have hmoveAs :
                  GeneralGrammar.Derives EqualCountGrammar
                    (equalCountAForm aCount ++ [ecN EqualCountNT.markC] ++
                      equalCountBForm bCount ++ equalCountCForm cRest)
                    ([ecN EqualCountNT.markC] ++
                      equalCountMarkerBag aCount bCount cRest) := by
                simpa [equalCountMarkerBag, List.append_assoc] using
                  equalCount_moveC_left_over_as aCount []
                    (equalCountBForm bCount ++ equalCountCForm cRest)
              have hrest :=
                ih aCount bCount cRest haRest hbRest hcRest
              have hcontext :
                  GeneralGrammar.Derives EqualCountGrammar
                    ([ecN EqualCountNT.markC] ++
                      equalCountMarkerBag aCount bCount cRest)
                    ([ecN EqualCountNT.markC] ++
                      equalCountMarkerWord rest ++
                      equalCountMarkerBag
                        (aCount - Word.Count EqualCountTerminal.a rest)
                        (bCount - Word.Count EqualCountTerminal.b rest)
                        (cRest - Word.Count EqualCountTerminal.c rest)) := by
                simpa [List.append_assoc] using
                  general_derives_context hrest [ecN EqualCountNT.markC] []
              have hall := GeneralGrammar.derives_trans hmoveBs
                (GeneralGrammar.derives_trans hmoveAs hcontext)
              have hsubC :
                  cRest + 1 -
                      (1 + Word.Count EqualCountTerminal.c rest) =
                    cRest - Word.Count EqualCountTerminal.c rest := by
                omega
              simpa [equalCountMarkerBag, equalCountCForm,
                equalCountMarkerWord, equalCountMarkerOfTerminal,
                Word.Count, hsubC, List.append_assoc] using hall

/-!
The marker-word-to-terminal-word derivation is the long constructive core of the
equal-count example. It walks through the sorted marker word and replaces each
marker with the corresponding terminal while preserving the generated shape.
-/

theorem equalCount_marker_word_to_terminal_word_derives
    (word : Word EqualCountTerminal) :
    GeneralGrammar.Derives EqualCountGrammar
      (equalCountMarkerWord word)
      (SententialForm.terminalWord word) := by
  induction word with
  | nil =>
      exact GeneralGrammar.Derives.refl []
  | cons token rest ih =>
      cases token with
      | a =>
          have hstep :
              GeneralGrammar.Yields EqualCountGrammar
                ([ecN EqualCountNT.markA] ++ equalCountMarkerWord rest)
                ([ecT EqualCountTerminal.a] ++ equalCountMarkerWord rest) := by
            simpa [List.append_assoc] using
              general_yields_of_production (G := EqualCountGrammar)
                EqualCountProduces.emitA [] (equalCountMarkerWord rest)
          have hcontext :
              GeneralGrammar.Derives EqualCountGrammar
                ([ecT EqualCountTerminal.a] ++ equalCountMarkerWord rest)
                ([ecT EqualCountTerminal.a] ++
                  SententialForm.terminalWord rest) := by
            simpa [List.append_assoc] using
              general_derives_context ih [ecT EqualCountTerminal.a] []
          have hall := GeneralGrammar.Derives.step hstep hcontext
          simpa [equalCountMarkerWord, equalCountMarkerOfTerminal,
            SententialForm.terminalWord, ecT] using hall
      | b =>
          have hstep :
              GeneralGrammar.Yields EqualCountGrammar
                ([ecN EqualCountNT.markB] ++ equalCountMarkerWord rest)
                ([ecT EqualCountTerminal.b] ++ equalCountMarkerWord rest) := by
            simpa [List.append_assoc] using
              general_yields_of_production (G := EqualCountGrammar)
                EqualCountProduces.emitB [] (equalCountMarkerWord rest)
          have hcontext :
              GeneralGrammar.Derives EqualCountGrammar
                ([ecT EqualCountTerminal.b] ++ equalCountMarkerWord rest)
                ([ecT EqualCountTerminal.b] ++
                  SententialForm.terminalWord rest) := by
            simpa [List.append_assoc] using
              general_derives_context ih [ecT EqualCountTerminal.b] []
          have hall := GeneralGrammar.Derives.step hstep hcontext
          simpa [equalCountMarkerWord, equalCountMarkerOfTerminal,
            SententialForm.terminalWord, ecT] using hall
      | c =>
          have hstep :
              GeneralGrammar.Yields EqualCountGrammar
                ([ecN EqualCountNT.markC] ++ equalCountMarkerWord rest)
                ([ecT EqualCountTerminal.c] ++ equalCountMarkerWord rest) := by
            simpa [List.append_assoc] using
              general_yields_of_production (G := EqualCountGrammar)
                EqualCountProduces.emitC [] (equalCountMarkerWord rest)
          have hcontext :
              GeneralGrammar.Derives EqualCountGrammar
                ([ecT EqualCountTerminal.c] ++ equalCountMarkerWord rest)
                ([ecT EqualCountTerminal.c] ++
                  SententialForm.terminalWord rest) := by
            simpa [List.append_assoc] using
              general_derives_context ih [ecT EqualCountTerminal.c] []
          have hall := GeneralGrammar.Derives.step hstep hcontext
          simpa [equalCountMarkerWord, equalCountMarkerOfTerminal,
            SententialForm.terminalWord, ecT] using hall

theorem equalCount_words_generated_of_equal_counts
    {word : Word EqualCountTerminal}
    (hcounts : word ∈ equalCountLanguage) :
    word ∈ GeneralGrammar.GeneratedLanguage EqualCountGrammar := by
  let n := Word.Count EqualCountTerminal.a word
  have hAB :
      Word.Count EqualCountTerminal.a word =
        Word.Count EqualCountTerminal.b word := hcounts.1
  have hBC :
      Word.Count EqualCountTerminal.b word =
        Word.Count EqualCountTerminal.c word := hcounts.2
  have hcEq :
      Word.Count EqualCountTerminal.c word =
        Word.Count EqualCountTerminal.a word :=
    (hAB.trans hBC).symm
  have hbLe : Word.Count EqualCountTerminal.b word <= n := by
    dsimp [n]
    exact Nat.le_of_eq hAB.symm
  have hcLe : Word.Count EqualCountTerminal.c word <= n := by
    dsimp [n]
    exact Nat.le_of_eq hcEq
  have hstart := equalCount_start_to_marker_bag_derives n
  have hmarkers :=
    equalCount_marker_bag_to_marker_word_derives word n n n
      (Nat.le_refl n) hbLe hcLe
  have hmarkersClean :
      GeneralGrammar.Derives EqualCountGrammar
        (equalCountMarkerBag n n n) (equalCountMarkerWord word) := by
    simpa [n, equalCountMarkerBag, equalCountAForm, equalCountBForm,
      equalCountCForm, hcEq, hAB] using hmarkers
  have hemit := equalCount_marker_word_to_terminal_word_derives word
  have hall := GeneralGrammar.derives_trans hstart
    (GeneralGrammar.derives_trans hmarkersClean hemit)
  simpa [GeneralGrammar.GeneratedLanguage, EqualCountGrammar, ecN,
    ggNonterminal] using hall

theorem equalCount_generated_language_exact
    (word : Word EqualCountTerminal) :
    word ∈ GeneralGrammar.GeneratedLanguage EqualCountGrammar <->
      word ∈ equalCountLanguage := by
  constructor
  · intro h
    exact equalCountGrammar_generated_has_equal_terminal_counts h
  · exact equalCount_words_generated_of_equal_counts

theorem equalCountLanguage_finite_production_generated :
    FiniteProductionGeneralLanguage equalCountLanguage := by
  exists EqualCountNT
  exists EqualCountGrammar
  constructor
  · exact equalCountGrammar_has_finite_productions
  · intro word
    exact equalCount_generated_language_exact word

/-!
The concrete word {lit}`baabcc` shows the unrestricted feature directly:
markers can be swapped into an arbitrary order before they are emitted as
terminals.
-/

def baabccWord : Word EqualCountTerminal :=
  [EqualCountTerminal.b, EqualCountTerminal.a, EqualCountTerminal.a,
    EqualCountTerminal.b, EqualCountTerminal.c, EqualCountTerminal.c]

theorem equalCountGrammar_generates_baabcc :
    baabccWord ∈ GeneralGrammar.GeneratedLanguage EqualCountGrammar := by
  let S := ecN EqualCountNT.start
  let A := ecN EqualCountNT.markA
  let B := ecN EqualCountNT.markB
  let C := ecN EqualCountNT.markC
  let a := ecT EqualCountTerminal.a
  let b := ecT EqualCountTerminal.b
  let c := ecT EqualCountTerminal.c
  have h1 : GeneralGrammar.Yields EqualCountGrammar [S] [S, A, B, C] := by
    simpa [S, A, B, C] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.grow [] []
  have h2 :
      GeneralGrammar.Yields EqualCountGrammar [S, A, B, C]
        [S, A, B, C, A, B, C] := by
    simpa [S, A, B, C] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.grow [] [A, B, C]
  have h3 :
      GeneralGrammar.Yields EqualCountGrammar [S, A, B, C, A, B, C]
        [A, B, C, A, B, C] := by
    simpa [S, A, B, C] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.stop [] [A, B, C, A, B, C]
  have h4 :
      GeneralGrammar.Yields EqualCountGrammar [A, B, C, A, B, C]
        [B, A, C, A, B, C] := by
    simpa [A, B, C] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.swapAB [] [C, A, B, C]
  have h5 :
      GeneralGrammar.Yields EqualCountGrammar [B, A, C, A, B, C]
        [B, A, A, C, B, C] := by
    simpa [A, B, C] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.swapCA [B, A] [B, C]
  have h6 :
      GeneralGrammar.Yields EqualCountGrammar [B, A, A, C, B, C]
        [B, A, A, B, C, C] := by
    simpa [A, B, C] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.swapCB [B, A, A] [C]
  have h7 :
      GeneralGrammar.Yields EqualCountGrammar [B, A, A, B, C, C]
        [b, A, A, B, C, C] := by
    simpa [A, B, C, b] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.emitB [] [A, A, B, C, C]
  have h8 :
      GeneralGrammar.Yields EqualCountGrammar [b, A, A, B, C, C]
        [b, a, A, B, C, C] := by
    simpa [A, B, C, a, b] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.emitA [b] [A, B, C, C]
  have h9 :
      GeneralGrammar.Yields EqualCountGrammar [b, a, A, B, C, C]
        [b, a, a, B, C, C] := by
    simpa [A, B, C, a, b] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.emitA [b, a] [B, C, C]
  have h10 :
      GeneralGrammar.Yields EqualCountGrammar [b, a, a, B, C, C]
        [b, a, a, b, C, C] := by
    simpa [A, B, C, a, b] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.emitB [b, a, a] [C, C]
  have h11 :
      GeneralGrammar.Yields EqualCountGrammar [b, a, a, b, C, C]
        [b, a, a, b, c, C] := by
    simpa [A, B, C, a, b, c] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.emitC [b, a, a, b] [C]
  have h12 :
      GeneralGrammar.Yields EqualCountGrammar [b, a, a, b, c, C]
        [b, a, a, b, c, c] := by
    simpa [A, B, C, a, b, c] using
      general_yields_of_production (G := EqualCountGrammar)
        EqualCountProduces.emitC [b, a, a, b, c] []
  have hderives :
      GeneralGrammar.Derives EqualCountGrammar [S] [b, a, a, b, c, c] :=
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
                            (GeneralGrammar.Derives.refl
                              [b, a, a, b, c, c]))))))))))))
  simpa [GeneralGrammar.GeneratedLanguage, EqualCountGrammar, baabccWord,
    SententialForm.terminalWord, S, a, b, c] using hderives


end Section06
end Chapter04
end Book
end FoC
