import FoC.Book.Chapter04.Section06.EqualCounts

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section06

/-!
# Section 4.6 equal counts over four symbols
-/

open Languages
open Grammars

/-!
# Equal Counts over Four Symbols

This is the four-symbol analogue of the previous construction. The same marker
and swapping strategy proves that equal counts of {lit}`a`, {lit}`b`, {lit}`c`, and {lit}`d` are
preserved by every generated terminal word.
-/

inductive FourCountTerminal where
  | a
  | b
  | c
  | d
deriving DecidableEq

inductive FourCountNT where
  | start
  | markA
  | markB
  | markC
  | markD
deriving DecidableEq

namespace FourCountNT

def finite : Foundation.FiniteType FourCountNT where
  elems := [start, markA, markB, markC, markD]
  complete := by
    intro A
    cases A <;> simp

end FourCountNT

def fcT (tok : FourCountTerminal) :
    Symbol FourCountTerminal FourCountNT :=
  ggTerminal tok

def fcN (A : FourCountNT) :
    Symbol FourCountTerminal FourCountNT :=
  ggNonterminal A

inductive FourCountProduces :
    SententialForm FourCountTerminal FourCountNT ->
      SententialForm FourCountTerminal FourCountNT -> Prop where
  | grow :
      FourCountProduces [fcN FourCountNT.start]
        [fcN FourCountNT.start, fcN FourCountNT.markA,
          fcN FourCountNT.markB, fcN FourCountNT.markC,
          fcN FourCountNT.markD]
  | stop :
      FourCountProduces [fcN FourCountNT.start] []
  | swapAB :
      FourCountProduces [fcN FourCountNT.markA, fcN FourCountNT.markB]
        [fcN FourCountNT.markB, fcN FourCountNT.markA]
  | swapBA :
      FourCountProduces [fcN FourCountNT.markB, fcN FourCountNT.markA]
        [fcN FourCountNT.markA, fcN FourCountNT.markB]
  | swapAC :
      FourCountProduces [fcN FourCountNT.markA, fcN FourCountNT.markC]
        [fcN FourCountNT.markC, fcN FourCountNT.markA]
  | swapCA :
      FourCountProduces [fcN FourCountNT.markC, fcN FourCountNT.markA]
        [fcN FourCountNT.markA, fcN FourCountNT.markC]
  | swapAD :
      FourCountProduces [fcN FourCountNT.markA, fcN FourCountNT.markD]
        [fcN FourCountNT.markD, fcN FourCountNT.markA]
  | swapDA :
      FourCountProduces [fcN FourCountNT.markD, fcN FourCountNT.markA]
        [fcN FourCountNT.markA, fcN FourCountNT.markD]
  | swapBC :
      FourCountProduces [fcN FourCountNT.markB, fcN FourCountNT.markC]
        [fcN FourCountNT.markC, fcN FourCountNT.markB]
  | swapCB :
      FourCountProduces [fcN FourCountNT.markC, fcN FourCountNT.markB]
        [fcN FourCountNT.markB, fcN FourCountNT.markC]
  | swapBD :
      FourCountProduces [fcN FourCountNT.markB, fcN FourCountNT.markD]
        [fcN FourCountNT.markD, fcN FourCountNT.markB]
  | swapDB :
      FourCountProduces [fcN FourCountNT.markD, fcN FourCountNT.markB]
        [fcN FourCountNT.markB, fcN FourCountNT.markD]
  | swapCD :
      FourCountProduces [fcN FourCountNT.markC, fcN FourCountNT.markD]
        [fcN FourCountNT.markD, fcN FourCountNT.markC]
  | swapDC :
      FourCountProduces [fcN FourCountNT.markD, fcN FourCountNT.markC]
        [fcN FourCountNT.markC, fcN FourCountNT.markD]
  | emitA :
      FourCountProduces [fcN FourCountNT.markA]
        [fcT FourCountTerminal.a]
  | emitB :
      FourCountProduces [fcN FourCountNT.markB]
        [fcT FourCountTerminal.b]
  | emitC :
      FourCountProduces [fcN FourCountNT.markC]
        [fcT FourCountTerminal.c]
  | emitD :
      FourCountProduces [fcN FourCountNT.markD]
        [fcT FourCountTerminal.d]

def FourCountGrammar :
    GeneralGrammar FourCountTerminal FourCountNT where
  start := FourCountNT.start
  produces := FourCountProduces
  lhsContainsNonterminal := by
    intro lhs rhs h
    cases h <;> simp [SententialForm.containsNonterminal, fcN,
      ggNonterminal]
  nonterminalsFinite := FourCountNT.finite

def FourCountProductionList :
    List (GeneralGrammar.Production FourCountTerminal FourCountNT) :=
  [{ lhs := [fcN FourCountNT.start],
     rhs := [fcN FourCountNT.start, fcN FourCountNT.markA,
       fcN FourCountNT.markB, fcN FourCountNT.markC,
       fcN FourCountNT.markD] },
   { lhs := [fcN FourCountNT.start],
     rhs := [] },
   { lhs := [fcN FourCountNT.markA, fcN FourCountNT.markB],
     rhs := [fcN FourCountNT.markB, fcN FourCountNT.markA] },
   { lhs := [fcN FourCountNT.markB, fcN FourCountNT.markA],
     rhs := [fcN FourCountNT.markA, fcN FourCountNT.markB] },
   { lhs := [fcN FourCountNT.markA, fcN FourCountNT.markC],
     rhs := [fcN FourCountNT.markC, fcN FourCountNT.markA] },
   { lhs := [fcN FourCountNT.markC, fcN FourCountNT.markA],
     rhs := [fcN FourCountNT.markA, fcN FourCountNT.markC] },
   { lhs := [fcN FourCountNT.markA, fcN FourCountNT.markD],
     rhs := [fcN FourCountNT.markD, fcN FourCountNT.markA] },
   { lhs := [fcN FourCountNT.markD, fcN FourCountNT.markA],
     rhs := [fcN FourCountNT.markA, fcN FourCountNT.markD] },
   { lhs := [fcN FourCountNT.markB, fcN FourCountNT.markC],
     rhs := [fcN FourCountNT.markC, fcN FourCountNT.markB] },
   { lhs := [fcN FourCountNT.markC, fcN FourCountNT.markB],
     rhs := [fcN FourCountNT.markB, fcN FourCountNT.markC] },
   { lhs := [fcN FourCountNT.markB, fcN FourCountNT.markD],
     rhs := [fcN FourCountNT.markD, fcN FourCountNT.markB] },
   { lhs := [fcN FourCountNT.markD, fcN FourCountNT.markB],
     rhs := [fcN FourCountNT.markB, fcN FourCountNT.markD] },
   { lhs := [fcN FourCountNT.markC, fcN FourCountNT.markD],
     rhs := [fcN FourCountNT.markD, fcN FourCountNT.markC] },
   { lhs := [fcN FourCountNT.markD, fcN FourCountNT.markC],
     rhs := [fcN FourCountNT.markC, fcN FourCountNT.markD] },
   { lhs := [fcN FourCountNT.markA],
     rhs := [fcT FourCountTerminal.a] },
   { lhs := [fcN FourCountNT.markB],
     rhs := [fcT FourCountTerminal.b] },
   { lhs := [fcN FourCountNT.markC],
     rhs := [fcT FourCountTerminal.c] },
   { lhs := [fcN FourCountNT.markD],
     rhs := [fcT FourCountTerminal.d] }]

theorem fourCountGrammar_has_finite_productions :
    GeneralGrammar.HasFiniteProductions FourCountGrammar := by
  exists FourCountProductionList
  intro lhs rhs
  constructor
  · intro h
    cases h <;> simp [FourCountProductionList]
  · intro h
    rcases h with ⟨rule, hmem, hlhs, hrhs⟩
    simp [FourCountProductionList] at hmem
    rcases hmem with
      hrule | hrule | hrule | hrule | hrule | hrule |
      hrule | hrule | hrule | hrule | hrule | hrule |
      hrule | hrule | hrule | hrule | hrule | hrule
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.grow
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.stop
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapAB
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapBA
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapAC
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapCA
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapAD
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapDA
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapBC
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapCB
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapBD
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapDB
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapCD
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.swapDC
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.emitA
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.emitB
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.emitC
    · subst rule
      cases hlhs
      cases hrhs
      exact FourCountProduces.emitD

theorem fourCountGrammar_finite_production_generated :
    FiniteProductionGeneralLanguage
      (GeneralGrammar.GeneratedLanguage FourCountGrammar) := by
  exists FourCountNT
  exists FourCountGrammar
  constructor
  · exact fourCountGrammar_has_finite_productions
  · intro w
    rfl

/-!
The four-symbol grammar is the same invariant idea with one more marker class.
The grow rule creates one marker for each of {lit}`a`, {lit}`b`, {lit}`c`, and
{lit}`d`; all swap rules preserve the four totals; emission converts markers
into terminals without changing the totals.
-/

def fourCountTotalA (sf : SententialForm FourCountTerminal FourCountNT) :
    Nat :=
  SententialCountTerminal FourCountTerminal.a sf +
    SententialCountNonterminal FourCountNT.markA sf

def fourCountTotalB (sf : SententialForm FourCountTerminal FourCountNT) :
    Nat :=
  SententialCountTerminal FourCountTerminal.b sf +
    SententialCountNonterminal FourCountNT.markB sf

def fourCountTotalC (sf : SententialForm FourCountTerminal FourCountNT) :
    Nat :=
  SententialCountTerminal FourCountTerminal.c sf +
    SententialCountNonterminal FourCountNT.markC sf

def fourCountTotalD (sf : SententialForm FourCountTerminal FourCountNT) :
    Nat :=
  SententialCountTerminal FourCountTerminal.d sf +
    SententialCountNonterminal FourCountNT.markD sf

def fourCountBalanced
    (sf : SententialForm FourCountTerminal FourCountNT) : Prop :=
  fourCountTotalA sf = fourCountTotalB sf ∧
    fourCountTotalB sf = fourCountTotalC sf ∧
    fourCountTotalC sf = fourCountTotalD sf

theorem fourCount_start_balanced :
    fourCountBalanced [fcN FourCountNT.start] := by
  simp [fourCountBalanced, fourCountTotalA, fourCountTotalB,
    fourCountTotalC, fourCountTotalD, SententialCountTerminal,
    SententialCountNonterminal, fcN, ggNonterminal]

theorem fourCount_yields_preserves_balanced
    {x y : SententialForm FourCountTerminal FourCountNT}
    (h : GeneralGrammar.Yields FourCountGrammar x y) :
    fourCountBalanced x -> fourCountBalanced y := by
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
                            simp [fourCountBalanced, fourCountTotalA,
                              fourCountTotalB, fourCountTotalC,
                              fourCountTotalD,
                              sententialCountTerminal_append,
                              sententialCountNonterminal_append,
                              SententialCountTerminal,
                              SententialCountNonterminal, fcN, fcT,
                              ggNonterminal, ggTerminal] at hbalanced ⊢ <;>
                            omega

theorem fourCount_derives_preserves_balanced
    {x y : SententialForm FourCountTerminal FourCountNT}
    (h : GeneralGrammar.Derives FourCountGrammar x y) :
    fourCountBalanced x -> fourCountBalanced y := by
  induction h with
  | refl _ =>
      intro hbalanced
      exact hbalanced
  | step hstep _ ih =>
      intro hbalanced
      exact ih (fourCount_yields_preserves_balanced hstep hbalanced)

theorem fourCountGrammar_generated_has_equal_terminal_counts
    {w : Word FourCountTerminal}
    (h : w ∈ GeneralGrammar.GeneratedLanguage FourCountGrammar) :
    Word.Count FourCountTerminal.a w = Word.Count FourCountTerminal.b w ∧
      Word.Count FourCountTerminal.b w = Word.Count FourCountTerminal.c w ∧
      Word.Count FourCountTerminal.c w = Word.Count FourCountTerminal.d w := by
  have hderives :
      GeneralGrammar.Derives FourCountGrammar [fcN FourCountNT.start]
        (SententialForm.terminalWord w) := by
    simpa [GeneralGrammar.GeneratedLanguage, FourCountGrammar, fcN,
      ggNonterminal] using h
  have hbalanced :=
    fourCount_derives_preserves_balanced hderives fourCount_start_balanced
  simpa [fourCountBalanced, fourCountTotalA, fourCountTotalB,
    fourCountTotalC, fourCountTotalD,
    sententialCountTerminal_terminalWord,
    sententialCountNonterminal_terminalWord] using hbalanced

def fourCountLanguage : Language FourCountTerminal :=
  fun w =>
    Word.Count FourCountTerminal.a w = Word.Count FourCountTerminal.b w ∧
      Word.Count FourCountTerminal.b w = Word.Count FourCountTerminal.c w ∧
      Word.Count FourCountTerminal.c w = Word.Count FourCountTerminal.d w

def fourCountAForm (n : Nat) :
    SententialForm FourCountTerminal FourCountNT :=
  List.replicate n (fcN FourCountNT.markA)

def fourCountBForm (n : Nat) :
    SententialForm FourCountTerminal FourCountNT :=
  List.replicate n (fcN FourCountNT.markB)

def fourCountCForm (n : Nat) :
    SententialForm FourCountTerminal FourCountNT :=
  List.replicate n (fcN FourCountNT.markC)

def fourCountDForm (n : Nat) :
    SententialForm FourCountTerminal FourCountNT :=
  List.replicate n (fcN FourCountNT.markD)

def fourCountMarkerBlock :
    SententialForm FourCountTerminal FourCountNT :=
  [fcN FourCountNT.markA, fcN FourCountNT.markB,
    fcN FourCountNT.markC, fcN FourCountNT.markD]

def fourCountRepeatedMarkers (n : Nat) :
    SententialForm FourCountTerminal FourCountNT :=
  Word.RepeatWord fourCountMarkerBlock n

def fourCountMarkerBag
    (aCount bCount cCount dCount : Nat) :
    SententialForm FourCountTerminal FourCountNT :=
  fourCountAForm aCount ++ fourCountBForm bCount ++
    fourCountCForm cCount ++ fourCountDForm dCount

def fourCountMarkerOfTerminal :
    FourCountTerminal -> FourCountNT
  | FourCountTerminal.a => FourCountNT.markA
  | FourCountTerminal.b => FourCountNT.markB
  | FourCountTerminal.c => FourCountNT.markC
  | FourCountTerminal.d => FourCountNT.markD

def fourCountMarkerWord (w : Word FourCountTerminal) :
    SententialForm FourCountTerminal FourCountNT :=
  w.map (fun token => fcN (fourCountMarkerOfTerminal token))

/-!
**Four-count exactness.**  The four-symbol grammar has the same two-phase
completeness proof as the three-symbol equal-count grammar: grow a balanced
marker supply, sort it into a bag, move one requested marker at a time to match
the target word, and finally emit terminals.
-/

theorem fourCount_moveB_left_over_as
    (n : Nat) (pre suffix : SententialForm FourCountTerminal FourCountNT) :
    GeneralGrammar.Derives FourCountGrammar
      (pre ++ fourCountAForm n ++ [fcN FourCountNT.markB] ++ suffix)
      (pre ++ [fcN FourCountNT.markB] ++ fourCountAForm n ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [fourCountAForm, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := FourCountGrammar)
          (pre ++ [fcN FourCountNT.markB] ++ suffix))
  | succ n ih =>
      let A := fcN FourCountNT.markA
      let B := fcN FourCountNT.markB
      have htail :
          GeneralGrammar.Derives FourCountGrammar
            (pre ++ [A] ++ fourCountAForm n ++ [B] ++ suffix)
            (pre ++ [A] ++ [B] ++ fourCountAForm n ++ suffix) := by
        simpa [A, B, List.append_assoc] using ih (pre ++ [A])
      have hswap :
          GeneralGrammar.Yields FourCountGrammar
            (pre ++ [A] ++ [B] ++ fourCountAForm n ++ suffix)
            (pre ++ [B] ++ [A] ++ fourCountAForm n ++ suffix) := by
        simpa [A, B, List.append_assoc] using
          general_yields_of_production (G := FourCountGrammar)
            FourCountProduces.swapAB pre (fourCountAForm n ++ suffix)
      have hall := GeneralGrammar.derives_trans htail
        (GeneralGrammar.yields_derives hswap)
      simpa [fourCountAForm, A, B, List.append_assoc] using hall

theorem fourCount_moveC_left_over_as
    (n : Nat) (pre suffix : SententialForm FourCountTerminal FourCountNT) :
    GeneralGrammar.Derives FourCountGrammar
      (pre ++ fourCountAForm n ++ [fcN FourCountNT.markC] ++ suffix)
      (pre ++ [fcN FourCountNT.markC] ++ fourCountAForm n ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [fourCountAForm, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := FourCountGrammar)
          (pre ++ [fcN FourCountNT.markC] ++ suffix))
  | succ n ih =>
      let A := fcN FourCountNT.markA
      let C := fcN FourCountNT.markC
      have htail :
          GeneralGrammar.Derives FourCountGrammar
            (pre ++ [A] ++ fourCountAForm n ++ [C] ++ suffix)
            (pre ++ [A] ++ [C] ++ fourCountAForm n ++ suffix) := by
        simpa [A, C, List.append_assoc] using ih (pre ++ [A])
      have hswap :
          GeneralGrammar.Yields FourCountGrammar
            (pre ++ [A] ++ [C] ++ fourCountAForm n ++ suffix)
            (pre ++ [C] ++ [A] ++ fourCountAForm n ++ suffix) := by
        simpa [A, C, List.append_assoc] using
          general_yields_of_production (G := FourCountGrammar)
            FourCountProduces.swapAC pre (fourCountAForm n ++ suffix)
      have hall := GeneralGrammar.derives_trans htail
        (GeneralGrammar.yields_derives hswap)
      simpa [fourCountAForm, A, C, List.append_assoc] using hall

theorem fourCount_moveD_left_over_as
    (n : Nat) (pre suffix : SententialForm FourCountTerminal FourCountNT) :
    GeneralGrammar.Derives FourCountGrammar
      (pre ++ fourCountAForm n ++ [fcN FourCountNT.markD] ++ suffix)
      (pre ++ [fcN FourCountNT.markD] ++ fourCountAForm n ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [fourCountAForm, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := FourCountGrammar)
          (pre ++ [fcN FourCountNT.markD] ++ suffix))
  | succ n ih =>
      let A := fcN FourCountNT.markA
      let D := fcN FourCountNT.markD
      have htail :
          GeneralGrammar.Derives FourCountGrammar
            (pre ++ [A] ++ fourCountAForm n ++ [D] ++ suffix)
            (pre ++ [A] ++ [D] ++ fourCountAForm n ++ suffix) := by
        simpa [A, D, List.append_assoc] using ih (pre ++ [A])
      have hswap :
          GeneralGrammar.Yields FourCountGrammar
            (pre ++ [A] ++ [D] ++ fourCountAForm n ++ suffix)
            (pre ++ [D] ++ [A] ++ fourCountAForm n ++ suffix) := by
        simpa [A, D, List.append_assoc] using
          general_yields_of_production (G := FourCountGrammar)
            FourCountProduces.swapAD pre (fourCountAForm n ++ suffix)
      have hall := GeneralGrammar.derives_trans htail
        (GeneralGrammar.yields_derives hswap)
      simpa [fourCountAForm, A, D, List.append_assoc] using hall

theorem fourCount_moveC_left_over_bs
    (n : Nat) (pre suffix : SententialForm FourCountTerminal FourCountNT) :
    GeneralGrammar.Derives FourCountGrammar
      (pre ++ fourCountBForm n ++ [fcN FourCountNT.markC] ++ suffix)
      (pre ++ [fcN FourCountNT.markC] ++ fourCountBForm n ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [fourCountBForm, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := FourCountGrammar)
          (pre ++ [fcN FourCountNT.markC] ++ suffix))
  | succ n ih =>
      let B := fcN FourCountNT.markB
      let C := fcN FourCountNT.markC
      have htail :
          GeneralGrammar.Derives FourCountGrammar
            (pre ++ [B] ++ fourCountBForm n ++ [C] ++ suffix)
            (pre ++ [B] ++ [C] ++ fourCountBForm n ++ suffix) := by
        simpa [B, C, List.append_assoc] using ih (pre ++ [B])
      have hswap :
          GeneralGrammar.Yields FourCountGrammar
            (pre ++ [B] ++ [C] ++ fourCountBForm n ++ suffix)
            (pre ++ [C] ++ [B] ++ fourCountBForm n ++ suffix) := by
        simpa [B, C, List.append_assoc] using
          general_yields_of_production (G := FourCountGrammar)
            FourCountProduces.swapBC pre (fourCountBForm n ++ suffix)
      have hall := GeneralGrammar.derives_trans htail
        (GeneralGrammar.yields_derives hswap)
      simpa [fourCountBForm, B, C, List.append_assoc] using hall

theorem fourCount_moveD_left_over_bs
    (n : Nat) (pre suffix : SententialForm FourCountTerminal FourCountNT) :
    GeneralGrammar.Derives FourCountGrammar
      (pre ++ fourCountBForm n ++ [fcN FourCountNT.markD] ++ suffix)
      (pre ++ [fcN FourCountNT.markD] ++ fourCountBForm n ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [fourCountBForm, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := FourCountGrammar)
          (pre ++ [fcN FourCountNT.markD] ++ suffix))
  | succ n ih =>
      let B := fcN FourCountNT.markB
      let D := fcN FourCountNT.markD
      have htail :
          GeneralGrammar.Derives FourCountGrammar
            (pre ++ [B] ++ fourCountBForm n ++ [D] ++ suffix)
            (pre ++ [B] ++ [D] ++ fourCountBForm n ++ suffix) := by
        simpa [B, D, List.append_assoc] using ih (pre ++ [B])
      have hswap :
          GeneralGrammar.Yields FourCountGrammar
            (pre ++ [B] ++ [D] ++ fourCountBForm n ++ suffix)
            (pre ++ [D] ++ [B] ++ fourCountBForm n ++ suffix) := by
        simpa [B, D, List.append_assoc] using
          general_yields_of_production (G := FourCountGrammar)
            FourCountProduces.swapBD pre (fourCountBForm n ++ suffix)
      have hall := GeneralGrammar.derives_trans htail
        (GeneralGrammar.yields_derives hswap)
      simpa [fourCountBForm, B, D, List.append_assoc] using hall

theorem fourCount_moveD_left_over_cs
    (n : Nat) (pre suffix : SententialForm FourCountTerminal FourCountNT) :
    GeneralGrammar.Derives FourCountGrammar
      (pre ++ fourCountCForm n ++ [fcN FourCountNT.markD] ++ suffix)
      (pre ++ [fcN FourCountNT.markD] ++ fourCountCForm n ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [fourCountCForm, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := FourCountGrammar)
          (pre ++ [fcN FourCountNT.markD] ++ suffix))
  | succ n ih =>
      let C := fcN FourCountNT.markC
      let D := fcN FourCountNT.markD
      have htail :
          GeneralGrammar.Derives FourCountGrammar
            (pre ++ [C] ++ fourCountCForm n ++ [D] ++ suffix)
            (pre ++ [C] ++ [D] ++ fourCountCForm n ++ suffix) := by
        simpa [C, D, List.append_assoc] using ih (pre ++ [C])
      have hswap :
          GeneralGrammar.Yields FourCountGrammar
            (pre ++ [C] ++ [D] ++ fourCountCForm n ++ suffix)
            (pre ++ [D] ++ [C] ++ fourCountCForm n ++ suffix) := by
        simpa [C, D, List.append_assoc] using
          general_yields_of_production (G := FourCountGrammar)
            FourCountProduces.swapCD pre (fourCountCForm n ++ suffix)
      have hall := GeneralGrammar.derives_trans htail
        (GeneralGrammar.yields_derives hswap)
      simpa [fourCountCForm, C, D, List.append_assoc] using hall

theorem fourCount_moveD_right_over_as
    (n : Nat) (pre suffix : SententialForm FourCountTerminal FourCountNT) :
    GeneralGrammar.Derives FourCountGrammar
      (pre ++ [fcN FourCountNT.markD] ++ fourCountAForm n ++ suffix)
      (pre ++ fourCountAForm n ++ [fcN FourCountNT.markD] ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [fourCountAForm] using
        (GeneralGrammar.Derives.refl (G := FourCountGrammar)
          (pre ++ [fcN FourCountNT.markD] ++ suffix))
  | succ n ih =>
      let A := fcN FourCountNT.markA
      let D := fcN FourCountNT.markD
      have hstep :
          GeneralGrammar.Yields FourCountGrammar
            (pre ++ [D, A] ++ fourCountAForm n ++ suffix)
            (pre ++ [A, D] ++ fourCountAForm n ++ suffix) := by
        simpa [A, D, List.append_assoc] using
          general_yields_of_production (G := FourCountGrammar)
            FourCountProduces.swapDA pre (fourCountAForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives FourCountGrammar
            (pre ++ [A, D] ++ fourCountAForm n ++ suffix)
            (pre ++ [A] ++ fourCountAForm n ++ [D] ++ suffix) := by
        simpa [A, D, List.append_assoc] using ih (pre ++ [A])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [fourCountAForm, A, D, List.append_assoc] using hall

theorem fourCount_moveC_right_over_as
    (n : Nat) (pre suffix : SententialForm FourCountTerminal FourCountNT) :
    GeneralGrammar.Derives FourCountGrammar
      (pre ++ [fcN FourCountNT.markC] ++ fourCountAForm n ++ suffix)
      (pre ++ fourCountAForm n ++ [fcN FourCountNT.markC] ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [fourCountAForm] using
        (GeneralGrammar.Derives.refl (G := FourCountGrammar)
          (pre ++ [fcN FourCountNT.markC] ++ suffix))
  | succ n ih =>
      let A := fcN FourCountNT.markA
      let C := fcN FourCountNT.markC
      have hstep :
          GeneralGrammar.Yields FourCountGrammar
            (pre ++ [C, A] ++ fourCountAForm n ++ suffix)
            (pre ++ [A, C] ++ fourCountAForm n ++ suffix) := by
        simpa [A, C, List.append_assoc] using
          general_yields_of_production (G := FourCountGrammar)
            FourCountProduces.swapCA pre (fourCountAForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives FourCountGrammar
            (pre ++ [A, C] ++ fourCountAForm n ++ suffix)
            (pre ++ [A] ++ fourCountAForm n ++ [C] ++ suffix) := by
        simpa [A, C, List.append_assoc] using ih (pre ++ [A])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [fourCountAForm, A, C, List.append_assoc] using hall

theorem fourCount_moveB_right_over_as
    (n : Nat) (pre suffix : SententialForm FourCountTerminal FourCountNT) :
    GeneralGrammar.Derives FourCountGrammar
      (pre ++ [fcN FourCountNT.markB] ++ fourCountAForm n ++ suffix)
      (pre ++ fourCountAForm n ++ [fcN FourCountNT.markB] ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [fourCountAForm] using
        (GeneralGrammar.Derives.refl (G := FourCountGrammar)
          (pre ++ [fcN FourCountNT.markB] ++ suffix))
  | succ n ih =>
      let A := fcN FourCountNT.markA
      let B := fcN FourCountNT.markB
      have hstep :
          GeneralGrammar.Yields FourCountGrammar
            (pre ++ [B, A] ++ fourCountAForm n ++ suffix)
            (pre ++ [A, B] ++ fourCountAForm n ++ suffix) := by
        simpa [A, B, List.append_assoc] using
          general_yields_of_production (G := FourCountGrammar)
            FourCountProduces.swapBA pre (fourCountAForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives FourCountGrammar
            (pre ++ [A, B] ++ fourCountAForm n ++ suffix)
            (pre ++ [A] ++ fourCountAForm n ++ [B] ++ suffix) := by
        simpa [A, B, List.append_assoc] using ih (pre ++ [A])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [fourCountAForm, A, B, List.append_assoc] using hall

theorem fourCount_moveD_right_over_bs
    (n : Nat) (pre suffix : SententialForm FourCountTerminal FourCountNT) :
    GeneralGrammar.Derives FourCountGrammar
      (pre ++ [fcN FourCountNT.markD] ++ fourCountBForm n ++ suffix)
      (pre ++ fourCountBForm n ++ [fcN FourCountNT.markD] ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [fourCountBForm] using
        (GeneralGrammar.Derives.refl (G := FourCountGrammar)
          (pre ++ [fcN FourCountNT.markD] ++ suffix))
  | succ n ih =>
      let B := fcN FourCountNT.markB
      let D := fcN FourCountNT.markD
      have hstep :
          GeneralGrammar.Yields FourCountGrammar
            (pre ++ [D, B] ++ fourCountBForm n ++ suffix)
            (pre ++ [B, D] ++ fourCountBForm n ++ suffix) := by
        simpa [B, D, List.append_assoc] using
          general_yields_of_production (G := FourCountGrammar)
            FourCountProduces.swapDB pre (fourCountBForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives FourCountGrammar
            (pre ++ [B, D] ++ fourCountBForm n ++ suffix)
            (pre ++ [B] ++ fourCountBForm n ++ [D] ++ suffix) := by
        simpa [B, D, List.append_assoc] using ih (pre ++ [B])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [fourCountBForm, B, D, List.append_assoc] using hall

theorem fourCount_moveC_right_over_bs
    (n : Nat) (pre suffix : SententialForm FourCountTerminal FourCountNT) :
    GeneralGrammar.Derives FourCountGrammar
      (pre ++ [fcN FourCountNT.markC] ++ fourCountBForm n ++ suffix)
      (pre ++ fourCountBForm n ++ [fcN FourCountNT.markC] ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [fourCountBForm] using
        (GeneralGrammar.Derives.refl (G := FourCountGrammar)
          (pre ++ [fcN FourCountNT.markC] ++ suffix))
  | succ n ih =>
      let B := fcN FourCountNT.markB
      let C := fcN FourCountNT.markC
      have hstep :
          GeneralGrammar.Yields FourCountGrammar
            (pre ++ [C, B] ++ fourCountBForm n ++ suffix)
            (pre ++ [B, C] ++ fourCountBForm n ++ suffix) := by
        simpa [B, C, List.append_assoc] using
          general_yields_of_production (G := FourCountGrammar)
            FourCountProduces.swapCB pre (fourCountBForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives FourCountGrammar
            (pre ++ [B, C] ++ fourCountBForm n ++ suffix)
            (pre ++ [B] ++ fourCountBForm n ++ [C] ++ suffix) := by
        simpa [B, C, List.append_assoc] using ih (pre ++ [B])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [fourCountBForm, B, C, List.append_assoc] using hall

theorem fourCount_moveD_right_over_cs
    (n : Nat) (pre suffix : SententialForm FourCountTerminal FourCountNT) :
    GeneralGrammar.Derives FourCountGrammar
      (pre ++ [fcN FourCountNT.markD] ++ fourCountCForm n ++ suffix)
      (pre ++ fourCountCForm n ++ [fcN FourCountNT.markD] ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [fourCountCForm] using
        (GeneralGrammar.Derives.refl (G := FourCountGrammar)
          (pre ++ [fcN FourCountNT.markD] ++ suffix))
  | succ n ih =>
      let C := fcN FourCountNT.markC
      let D := fcN FourCountNT.markD
      have hstep :
          GeneralGrammar.Yields FourCountGrammar
            (pre ++ [D, C] ++ fourCountCForm n ++ suffix)
            (pre ++ [C, D] ++ fourCountCForm n ++ suffix) := by
        simpa [C, D, List.append_assoc] using
          general_yields_of_production (G := FourCountGrammar)
            FourCountProduces.swapDC pre (fourCountCForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives FourCountGrammar
            (pre ++ [C, D] ++ fourCountCForm n ++ suffix)
            (pre ++ [C] ++ fourCountCForm n ++ [D] ++ suffix) := by
        simpa [C, D, List.append_assoc] using ih (pre ++ [C])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [fourCountCForm, C, D, List.append_assoc] using hall

theorem fourCount_sort_repeated_markers_derives (n : Nat) :
    GeneralGrammar.Derives FourCountGrammar
      (fourCountRepeatedMarkers n)
      (fourCountMarkerBag n n n n) := by
  induction n with
  | zero =>
      exact GeneralGrammar.Derives.refl []
  | succ n ih =>
      let A := fcN FourCountNT.markA
      let B := fcN FourCountNT.markB
      let C := fcN FourCountNT.markC
      let D := fcN FourCountNT.markD
      have hsortTail :
          GeneralGrammar.Derives FourCountGrammar
            (fourCountMarkerBlock ++ fourCountRepeatedMarkers n)
            (fourCountMarkerBlock ++ fourCountMarkerBag n n n n) := by
        simpa [fourCountMarkerBlock, fourCountMarkerBag, A, B, C, D,
          List.append_assoc] using
          general_derives_context ih fourCountMarkerBlock []
      have hmoveDAs :
          GeneralGrammar.Derives FourCountGrammar
            (fourCountMarkerBlock ++ fourCountMarkerBag n n n n)
            ([A, B, C] ++ fourCountAForm n ++ [D] ++
              fourCountBForm n ++ fourCountCForm n ++
              fourCountDForm n) := by
        simpa [fourCountMarkerBlock, fourCountMarkerBag, A, B, C, D,
          List.append_assoc] using
          fourCount_moveD_right_over_as n [A, B, C]
            (fourCountBForm n ++ fourCountCForm n ++ fourCountDForm n)
      have hmoveCAs :
          GeneralGrammar.Derives FourCountGrammar
            ([A, B, C] ++ fourCountAForm n ++ [D] ++
              fourCountBForm n ++ fourCountCForm n ++ fourCountDForm n)
            ([A, B] ++ fourCountAForm n ++ [C, D] ++
              fourCountBForm n ++ fourCountCForm n ++ fourCountDForm n) := by
        simpa [A, B, C, D, List.append_assoc] using
          fourCount_moveC_right_over_as n [A, B]
            ([D] ++ fourCountBForm n ++ fourCountCForm n ++
              fourCountDForm n)
      have hmoveBAs :
          GeneralGrammar.Derives FourCountGrammar
            ([A, B] ++ fourCountAForm n ++ [C, D] ++
              fourCountBForm n ++ fourCountCForm n ++ fourCountDForm n)
            ([A] ++ fourCountAForm n ++ [B, C, D] ++
              fourCountBForm n ++ fourCountCForm n ++ fourCountDForm n) := by
        simpa [A, B, C, D, List.append_assoc] using
          fourCount_moveB_right_over_as n [A]
            ([C, D] ++ fourCountBForm n ++ fourCountCForm n ++
              fourCountDForm n)
      have hmoveDBs :
          GeneralGrammar.Derives FourCountGrammar
            ([A] ++ fourCountAForm n ++ [B, C, D] ++
              fourCountBForm n ++ fourCountCForm n ++ fourCountDForm n)
            ([A] ++ fourCountAForm n ++ [B, C] ++
              fourCountBForm n ++ [D] ++ fourCountCForm n ++
              fourCountDForm n) := by
        simpa [A, B, C, D, List.append_assoc] using
          fourCount_moveD_right_over_bs n
            ([A] ++ fourCountAForm n ++ [B, C])
            (fourCountCForm n ++ fourCountDForm n)
      have hmoveCBs :
          GeneralGrammar.Derives FourCountGrammar
            ([A] ++ fourCountAForm n ++ [B, C] ++
              fourCountBForm n ++ [D] ++ fourCountCForm n ++
              fourCountDForm n)
            ([A] ++ fourCountAForm n ++ [B] ++
              fourCountBForm n ++ [C, D] ++ fourCountCForm n ++
              fourCountDForm n) := by
        simpa [A, B, C, D, List.append_assoc] using
          fourCount_moveC_right_over_bs n
            ([A] ++ fourCountAForm n ++ [B])
            ([D] ++ fourCountCForm n ++ fourCountDForm n)
      have hmoveDCs :
          GeneralGrammar.Derives FourCountGrammar
            ([A] ++ fourCountAForm n ++ [B] ++
              fourCountBForm n ++ [C, D] ++ fourCountCForm n ++
              fourCountDForm n)
            (fourCountMarkerBag (n + 1) (n + 1) (n + 1) (n + 1)) := by
        simpa [fourCountMarkerBag, fourCountAForm, fourCountBForm,
          fourCountCForm, fourCountDForm, A, B, C, D,
          List.append_assoc] using
          fourCount_moveD_right_over_cs n
            ([A] ++ fourCountAForm n ++ [B] ++ fourCountBForm n ++
              [C])
            (fourCountDForm n)
      exact GeneralGrammar.derives_trans hsortTail
        (GeneralGrammar.derives_trans hmoveDAs
          (GeneralGrammar.derives_trans hmoveCAs
            (GeneralGrammar.derives_trans hmoveBAs
              (GeneralGrammar.derives_trans hmoveDBs
                (GeneralGrammar.derives_trans hmoveCBs hmoveDCs)))))

theorem fourCount_grow_repeated_markers_derives (n : Nat) :
    GeneralGrammar.Derives FourCountGrammar [fcN FourCountNT.start]
      ([fcN FourCountNT.start] ++ fourCountRepeatedMarkers n) := by
  induction n with
  | zero =>
      simpa [fourCountRepeatedMarkers, Word.RepeatWord] using
        (GeneralGrammar.Derives.refl (G := FourCountGrammar)
          [fcN FourCountNT.start])
  | succ n ih =>
      have hstep :
          GeneralGrammar.Yields FourCountGrammar
            ([fcN FourCountNT.start] ++ fourCountRepeatedMarkers n)
            ([fcN FourCountNT.start] ++ fourCountMarkerBlock ++
              fourCountRepeatedMarkers n) := by
        simpa [fourCountMarkerBlock, List.append_assoc] using
          general_yields_of_production (G := FourCountGrammar)
            FourCountProduces.grow [] (fourCountRepeatedMarkers n)
      have hall := GeneralGrammar.derives_trans ih
        (GeneralGrammar.yields_derives hstep)
      simpa [fourCountRepeatedMarkers, fourCountMarkerBlock,
        Word.RepeatWord, List.append_assoc] using hall

theorem fourCount_start_to_marker_bag_derives (n : Nat) :
    GeneralGrammar.Derives FourCountGrammar [fcN FourCountNT.start]
      (fourCountMarkerBag n n n n) := by
  have hgrow := fourCount_grow_repeated_markers_derives n
  have hstop :
      GeneralGrammar.Yields FourCountGrammar
        ([fcN FourCountNT.start] ++ fourCountRepeatedMarkers n)
        (fourCountRepeatedMarkers n) := by
    simpa [List.append_assoc] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.stop [] (fourCountRepeatedMarkers n)
  exact GeneralGrammar.derives_trans hgrow
    (GeneralGrammar.derives_trans (GeneralGrammar.yields_derives hstop)
      (fourCount_sort_repeated_markers_derives n))

theorem fourCount_marker_bag_to_marker_word_derives
    (word : Word FourCountTerminal)
    (aCount bCount cCount dCount : Nat)
    (ha : Word.Count FourCountTerminal.a word <= aCount)
    (hb : Word.Count FourCountTerminal.b word <= bCount)
    (hc : Word.Count FourCountTerminal.c word <= cCount)
    (hd : Word.Count FourCountTerminal.d word <= dCount) :
    GeneralGrammar.Derives FourCountGrammar
      (fourCountMarkerBag aCount bCount cCount dCount)
      (fourCountMarkerWord word ++
        fourCountMarkerBag
          (aCount - Word.Count FourCountTerminal.a word)
          (bCount - Word.Count FourCountTerminal.b word)
          (cCount - Word.Count FourCountTerminal.c word)
          (dCount - Word.Count FourCountTerminal.d word)) := by
  induction word generalizing aCount bCount cCount dCount with
  | nil =>
      simpa [fourCountMarkerWord, fourCountMarkerBag, Word.Count] using
        (GeneralGrammar.Derives.refl (G := FourCountGrammar)
          (fourCountMarkerBag aCount bCount cCount dCount))
  | cons token rest ih =>
      cases token with
      | a =>
          cases aCount with
          | zero =>
              simp [Word.Count] at ha
          | succ aRest =>
              have haRest :
                  Word.Count FourCountTerminal.a rest <= aRest := by
                simp [Word.Count] at ha
                omega
              have hbRest :
                  Word.Count FourCountTerminal.b rest <= bCount := by
                simpa [Word.Count] using hb
              have hcRest :
                  Word.Count FourCountTerminal.c rest <= cCount := by
                simpa [Word.Count] using hc
              have hdRest :
                  Word.Count FourCountTerminal.d rest <= dCount := by
                simpa [Word.Count] using hd
              have hrest :=
                ih aRest bCount cCount dCount haRest hbRest hcRest hdRest
              have hcontext :
                  GeneralGrammar.Derives FourCountGrammar
                    ([fcN FourCountNT.markA] ++
                      fourCountMarkerBag aRest bCount cCount dCount)
                    ([fcN FourCountNT.markA] ++
                      fourCountMarkerWord rest ++
                      fourCountMarkerBag
                        (aRest - Word.Count FourCountTerminal.a rest)
                        (bCount - Word.Count FourCountTerminal.b rest)
                        (cCount - Word.Count FourCountTerminal.c rest)
                        (dCount - Word.Count FourCountTerminal.d rest)) := by
                simpa [List.append_assoc] using
                  general_derives_context hrest [fcN FourCountNT.markA] []
              have hsubA :
                  aRest + 1 -
                      (1 + Word.Count FourCountTerminal.a rest) =
                    aRest - Word.Count FourCountTerminal.a rest := by
                omega
              have hrepA :
                  List.replicate (aRest + 1) (fcN FourCountNT.markA) =
                    fcN FourCountNT.markA :: fourCountAForm aRest := by
                rfl
              simpa [fourCountMarkerBag, fourCountAForm,
                fourCountMarkerWord, fourCountMarkerOfTerminal,
                Word.Count, hsubA, hrepA, List.append_assoc] using hcontext
      | b =>
          cases bCount with
          | zero =>
              simp [Word.Count] at hb
          | succ bRest =>
              have haRest :
                  Word.Count FourCountTerminal.a rest <= aCount := by
                simpa [Word.Count] using ha
              have hbRest :
                  Word.Count FourCountTerminal.b rest <= bRest := by
                simp [Word.Count] at hb
                omega
              have hcRest :
                  Word.Count FourCountTerminal.c rest <= cCount := by
                simpa [Word.Count] using hc
              have hdRest :
                  Word.Count FourCountTerminal.d rest <= dCount := by
                simpa [Word.Count] using hd
              have hmove :
                  GeneralGrammar.Derives FourCountGrammar
                    (fourCountMarkerBag aCount (bRest + 1) cCount dCount)
                    ([fcN FourCountNT.markB] ++
                      fourCountMarkerBag aCount bRest cCount dCount) := by
                simpa [fourCountMarkerBag, fourCountBForm,
                  List.append_assoc] using
                  fourCount_moveB_left_over_as aCount []
                    (fourCountBForm bRest ++ fourCountCForm cCount ++
                      fourCountDForm dCount)
              have hrest :=
                ih aCount bRest cCount dCount haRest hbRest hcRest hdRest
              have hcontext :
                  GeneralGrammar.Derives FourCountGrammar
                    ([fcN FourCountNT.markB] ++
                      fourCountMarkerBag aCount bRest cCount dCount)
                    ([fcN FourCountNT.markB] ++
                      fourCountMarkerWord rest ++
                      fourCountMarkerBag
                        (aCount - Word.Count FourCountTerminal.a rest)
                        (bRest - Word.Count FourCountTerminal.b rest)
                        (cCount - Word.Count FourCountTerminal.c rest)
                        (dCount - Word.Count FourCountTerminal.d rest)) := by
                simpa [List.append_assoc] using
                  general_derives_context hrest [fcN FourCountNT.markB] []
              have hall := GeneralGrammar.derives_trans hmove hcontext
              have hsubB :
                  bRest + 1 -
                      (1 + Word.Count FourCountTerminal.b rest) =
                    bRest - Word.Count FourCountTerminal.b rest := by
                omega
              simpa [fourCountMarkerBag, fourCountBForm,
                fourCountMarkerWord, fourCountMarkerOfTerminal,
                Word.Count, hsubB, List.append_assoc] using hall
      | c =>
          cases cCount with
          | zero =>
              simp [Word.Count] at hc
          | succ cRest =>
              have haRest :
                  Word.Count FourCountTerminal.a rest <= aCount := by
                simpa [Word.Count] using ha
              have hbRest :
                  Word.Count FourCountTerminal.b rest <= bCount := by
                simpa [Word.Count] using hb
              have hcRest :
                  Word.Count FourCountTerminal.c rest <= cRest := by
                simp [Word.Count] at hc
                omega
              have hdRest :
                  Word.Count FourCountTerminal.d rest <= dCount := by
                simpa [Word.Count] using hd
              have hmoveBs :
                  GeneralGrammar.Derives FourCountGrammar
                    (fourCountMarkerBag aCount bCount (cRest + 1) dCount)
                    (fourCountAForm aCount ++ [fcN FourCountNT.markC] ++
                      fourCountBForm bCount ++ fourCountCForm cRest ++
                      fourCountDForm dCount) := by
                simpa [fourCountMarkerBag, fourCountCForm,
                  List.append_assoc] using
                  fourCount_moveC_left_over_bs bCount
                    (fourCountAForm aCount)
                    (fourCountCForm cRest ++ fourCountDForm dCount)
              have hmoveAs :
                  GeneralGrammar.Derives FourCountGrammar
                    (fourCountAForm aCount ++ [fcN FourCountNT.markC] ++
                      fourCountBForm bCount ++ fourCountCForm cRest ++
                      fourCountDForm dCount)
                    ([fcN FourCountNT.markC] ++
                      fourCountMarkerBag aCount bCount cRest dCount) := by
                simpa [fourCountMarkerBag, List.append_assoc] using
                  fourCount_moveC_left_over_as aCount []
                    (fourCountBForm bCount ++ fourCountCForm cRest ++
                      fourCountDForm dCount)
              have hrest :=
                ih aCount bCount cRest dCount haRest hbRest hcRest hdRest
              have hcontext :
                  GeneralGrammar.Derives FourCountGrammar
                    ([fcN FourCountNT.markC] ++
                      fourCountMarkerBag aCount bCount cRest dCount)
                    ([fcN FourCountNT.markC] ++
                      fourCountMarkerWord rest ++
                      fourCountMarkerBag
                        (aCount - Word.Count FourCountTerminal.a rest)
                        (bCount - Word.Count FourCountTerminal.b rest)
                        (cRest - Word.Count FourCountTerminal.c rest)
                        (dCount - Word.Count FourCountTerminal.d rest)) := by
                simpa [List.append_assoc] using
                  general_derives_context hrest [fcN FourCountNT.markC] []
              have hall := GeneralGrammar.derives_trans hmoveBs
                (GeneralGrammar.derives_trans hmoveAs hcontext)
              have hsubC :
                  cRest + 1 -
                      (1 + Word.Count FourCountTerminal.c rest) =
                    cRest - Word.Count FourCountTerminal.c rest := by
                omega
              simpa [fourCountMarkerBag, fourCountCForm,
                fourCountMarkerWord, fourCountMarkerOfTerminal,
                Word.Count, hsubC, List.append_assoc] using hall
      | d =>
          cases dCount with
          | zero =>
              simp [Word.Count] at hd
          | succ dRest =>
              have haRest :
                  Word.Count FourCountTerminal.a rest <= aCount := by
                simpa [Word.Count] using ha
              have hbRest :
                  Word.Count FourCountTerminal.b rest <= bCount := by
                simpa [Word.Count] using hb
              have hcRest :
                  Word.Count FourCountTerminal.c rest <= cCount := by
                simpa [Word.Count] using hc
              have hdRest :
                  Word.Count FourCountTerminal.d rest <= dRest := by
                simp [Word.Count] at hd
                omega
              have hmoveCs :
                  GeneralGrammar.Derives FourCountGrammar
                    (fourCountMarkerBag aCount bCount cCount (dRest + 1))
                    (fourCountAForm aCount ++ fourCountBForm bCount ++
                      [fcN FourCountNT.markD] ++ fourCountCForm cCount ++
                      fourCountDForm dRest) := by
                simpa [fourCountMarkerBag, fourCountDForm,
                  List.append_assoc] using
                  fourCount_moveD_left_over_cs cCount
                    (fourCountAForm aCount ++ fourCountBForm bCount)
                    (fourCountDForm dRest)
              have hmoveBs :
                  GeneralGrammar.Derives FourCountGrammar
                    (fourCountAForm aCount ++ fourCountBForm bCount ++
                      [fcN FourCountNT.markD] ++ fourCountCForm cCount ++
                      fourCountDForm dRest)
                    (fourCountAForm aCount ++ [fcN FourCountNT.markD] ++
                      fourCountBForm bCount ++ fourCountCForm cCount ++
                      fourCountDForm dRest) := by
                simpa [fourCountMarkerBag, List.append_assoc] using
                  fourCount_moveD_left_over_bs bCount
                    (fourCountAForm aCount)
                    (fourCountCForm cCount ++ fourCountDForm dRest)
              have hmoveAs :
                  GeneralGrammar.Derives FourCountGrammar
                    (fourCountAForm aCount ++ [fcN FourCountNT.markD] ++
                      fourCountBForm bCount ++ fourCountCForm cCount ++
                      fourCountDForm dRest)
                    ([fcN FourCountNT.markD] ++
                      fourCountMarkerBag aCount bCount cCount dRest) := by
                simpa [fourCountMarkerBag, List.append_assoc] using
                  fourCount_moveD_left_over_as aCount []
                    (fourCountBForm bCount ++ fourCountCForm cCount ++
                      fourCountDForm dRest)
              have hrest :=
                ih aCount bCount cCount dRest haRest hbRest hcRest hdRest
              have hcontext :
                  GeneralGrammar.Derives FourCountGrammar
                    ([fcN FourCountNT.markD] ++
                      fourCountMarkerBag aCount bCount cCount dRest)
                    ([fcN FourCountNT.markD] ++
                      fourCountMarkerWord rest ++
                      fourCountMarkerBag
                        (aCount - Word.Count FourCountTerminal.a rest)
                        (bCount - Word.Count FourCountTerminal.b rest)
                        (cCount - Word.Count FourCountTerminal.c rest)
                        (dRest - Word.Count FourCountTerminal.d rest)) := by
                simpa [List.append_assoc] using
                  general_derives_context hrest [fcN FourCountNT.markD] []
              have hall := GeneralGrammar.derives_trans hmoveCs
                (GeneralGrammar.derives_trans hmoveBs
                  (GeneralGrammar.derives_trans hmoveAs hcontext))
              have hsubD :
                  dRest + 1 -
                      (1 + Word.Count FourCountTerminal.d rest) =
                    dRest - Word.Count FourCountTerminal.d rest := by
                omega
              simpa [fourCountMarkerBag, fourCountDForm,
                fourCountMarkerWord, fourCountMarkerOfTerminal,
                Word.Count, hsubD, List.append_assoc] using hall

theorem fourCount_marker_word_to_terminal_word_derives
    (word : Word FourCountTerminal) :
    GeneralGrammar.Derives FourCountGrammar
      (fourCountMarkerWord word)
      (SententialForm.terminalWord word) := by
  induction word with
  | nil =>
      exact GeneralGrammar.Derives.refl []
  | cons token rest ih =>
      cases token with
      | a =>
          have hstep :
              GeneralGrammar.Yields FourCountGrammar
                ([fcN FourCountNT.markA] ++ fourCountMarkerWord rest)
                ([fcT FourCountTerminal.a] ++ fourCountMarkerWord rest) := by
            simpa [List.append_assoc] using
              general_yields_of_production (G := FourCountGrammar)
                FourCountProduces.emitA [] (fourCountMarkerWord rest)
          have hcontext :
              GeneralGrammar.Derives FourCountGrammar
                ([fcT FourCountTerminal.a] ++ fourCountMarkerWord rest)
                ([fcT FourCountTerminal.a] ++
                  SententialForm.terminalWord rest) := by
            simpa [List.append_assoc] using
              general_derives_context ih [fcT FourCountTerminal.a] []
          have hall := GeneralGrammar.Derives.step hstep hcontext
          simpa [fourCountMarkerWord, fourCountMarkerOfTerminal,
            SententialForm.terminalWord, fcT] using hall
      | b =>
          have hstep :
              GeneralGrammar.Yields FourCountGrammar
                ([fcN FourCountNT.markB] ++ fourCountMarkerWord rest)
                ([fcT FourCountTerminal.b] ++ fourCountMarkerWord rest) := by
            simpa [List.append_assoc] using
              general_yields_of_production (G := FourCountGrammar)
                FourCountProduces.emitB [] (fourCountMarkerWord rest)
          have hcontext :
              GeneralGrammar.Derives FourCountGrammar
                ([fcT FourCountTerminal.b] ++ fourCountMarkerWord rest)
                ([fcT FourCountTerminal.b] ++
                  SententialForm.terminalWord rest) := by
            simpa [List.append_assoc] using
              general_derives_context ih [fcT FourCountTerminal.b] []
          have hall := GeneralGrammar.Derives.step hstep hcontext
          simpa [fourCountMarkerWord, fourCountMarkerOfTerminal,
            SententialForm.terminalWord, fcT] using hall
      | c =>
          have hstep :
              GeneralGrammar.Yields FourCountGrammar
                ([fcN FourCountNT.markC] ++ fourCountMarkerWord rest)
                ([fcT FourCountTerminal.c] ++ fourCountMarkerWord rest) := by
            simpa [List.append_assoc] using
              general_yields_of_production (G := FourCountGrammar)
                FourCountProduces.emitC [] (fourCountMarkerWord rest)
          have hcontext :
              GeneralGrammar.Derives FourCountGrammar
                ([fcT FourCountTerminal.c] ++ fourCountMarkerWord rest)
                ([fcT FourCountTerminal.c] ++
                  SententialForm.terminalWord rest) := by
            simpa [List.append_assoc] using
              general_derives_context ih [fcT FourCountTerminal.c] []
          have hall := GeneralGrammar.Derives.step hstep hcontext
          simpa [fourCountMarkerWord, fourCountMarkerOfTerminal,
            SententialForm.terminalWord, fcT] using hall
      | d =>
          have hstep :
              GeneralGrammar.Yields FourCountGrammar
                ([fcN FourCountNT.markD] ++ fourCountMarkerWord rest)
                ([fcT FourCountTerminal.d] ++ fourCountMarkerWord rest) := by
            simpa [List.append_assoc] using
              general_yields_of_production (G := FourCountGrammar)
                FourCountProduces.emitD [] (fourCountMarkerWord rest)
          have hcontext :
              GeneralGrammar.Derives FourCountGrammar
                ([fcT FourCountTerminal.d] ++ fourCountMarkerWord rest)
                ([fcT FourCountTerminal.d] ++
                  SententialForm.terminalWord rest) := by
            simpa [List.append_assoc] using
              general_derives_context ih [fcT FourCountTerminal.d] []
          have hall := GeneralGrammar.Derives.step hstep hcontext
          simpa [fourCountMarkerWord, fourCountMarkerOfTerminal,
            SententialForm.terminalWord, fcT] using hall

theorem fourCount_words_generated_of_equal_counts
    {word : Word FourCountTerminal}
    (hcounts : word ∈ fourCountLanguage) :
    word ∈ GeneralGrammar.GeneratedLanguage FourCountGrammar := by
  let n := Word.Count FourCountTerminal.a word
  have hAB :
      Word.Count FourCountTerminal.a word =
        Word.Count FourCountTerminal.b word := hcounts.1
  have hBC :
      Word.Count FourCountTerminal.b word =
        Word.Count FourCountTerminal.c word := hcounts.2.1
  have hCD :
      Word.Count FourCountTerminal.c word =
        Word.Count FourCountTerminal.d word := hcounts.2.2
  have hcEq :
      Word.Count FourCountTerminal.c word =
        Word.Count FourCountTerminal.a word :=
    (hAB.trans hBC).symm
  have hdEq :
      Word.Count FourCountTerminal.d word =
        Word.Count FourCountTerminal.a word :=
    (hAB.trans (hBC.trans hCD)).symm
  have hbLe : Word.Count FourCountTerminal.b word <= n := by
    dsimp [n]
    exact Nat.le_of_eq hAB.symm
  have hcLe : Word.Count FourCountTerminal.c word <= n := by
    dsimp [n]
    exact Nat.le_of_eq hcEq
  have hdLe : Word.Count FourCountTerminal.d word <= n := by
    dsimp [n]
    exact Nat.le_of_eq hdEq
  have hstart := fourCount_start_to_marker_bag_derives n
  have hmarkers :=
    fourCount_marker_bag_to_marker_word_derives word n n n n
      (Nat.le_refl n) hbLe hcLe hdLe
  have hmarkersClean :
      GeneralGrammar.Derives FourCountGrammar
        (fourCountMarkerBag n n n n) (fourCountMarkerWord word) := by
    simpa [n, fourCountMarkerBag, fourCountAForm, fourCountBForm,
      fourCountCForm, fourCountDForm, hAB, hcEq, hdEq] using hmarkers
  have hemit := fourCount_marker_word_to_terminal_word_derives word
  have hall := GeneralGrammar.derives_trans hstart
    (GeneralGrammar.derives_trans hmarkersClean hemit)
  simpa [GeneralGrammar.GeneratedLanguage, FourCountGrammar, fcN,
    ggNonterminal] using hall

theorem fourCount_generated_language_exact
    (word : Word FourCountTerminal) :
    word ∈ GeneralGrammar.GeneratedLanguage FourCountGrammar <->
      word ∈ fourCountLanguage := by
  constructor
  · intro h
    exact fourCountGrammar_generated_has_equal_terminal_counts h
  · exact fourCount_words_generated_of_equal_counts

theorem fourCountLanguage_finite_production_generated :
    FiniteProductionGeneralLanguage fourCountLanguage := by
  exists FourCountNT
  exists FourCountGrammar
  constructor
  · exact fourCountGrammar_has_finite_productions
  · intro word
    exact fourCount_generated_language_exact word

/-!
The concrete word {lit}`dacb` shows that the grammar is not enforcing order. It
only enforces equal counts.
-/

def dacbWord : Word FourCountTerminal :=
  [FourCountTerminal.d, FourCountTerminal.a, FourCountTerminal.c,
    FourCountTerminal.b]

theorem fourCountGrammar_generates_dacb :
    dacbWord ∈ GeneralGrammar.GeneratedLanguage FourCountGrammar := by
  let S := fcN FourCountNT.start
  let A := fcN FourCountNT.markA
  let B := fcN FourCountNT.markB
  let C := fcN FourCountNT.markC
  let D := fcN FourCountNT.markD
  let a := fcT FourCountTerminal.a
  let b := fcT FourCountTerminal.b
  let c := fcT FourCountTerminal.c
  let d := fcT FourCountTerminal.d
  have h1 : GeneralGrammar.Yields FourCountGrammar [S] [S, A, B, C, D] := by
    simpa [S, A, B, C, D] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.grow [] []
  have h2 :
      GeneralGrammar.Yields FourCountGrammar [S, A, B, C, D]
        [A, B, C, D] := by
    simpa [S, A, B, C, D] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.stop [] [A, B, C, D]
  have h3 :
      GeneralGrammar.Yields FourCountGrammar [A, B, C, D]
        [A, B, D, C] := by
    simpa [A, B, C, D] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.swapCD [A, B] []
  have h4 :
      GeneralGrammar.Yields FourCountGrammar [A, B, D, C]
        [A, D, B, C] := by
    simpa [A, B, C, D] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.swapBD [A] [C]
  have h5 :
      GeneralGrammar.Yields FourCountGrammar [A, D, B, C]
        [D, A, B, C] := by
    simpa [A, B, C, D] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.swapAD [] [B, C]
  have h6 :
      GeneralGrammar.Yields FourCountGrammar [D, A, B, C]
        [D, A, C, B] := by
    simpa [A, B, C, D] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.swapBC [D, A] []
  have h7 :
      GeneralGrammar.Yields FourCountGrammar [D, A, C, B]
        [d, A, C, B] := by
    simpa [A, B, C, D, d] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.emitD [] [A, C, B]
  have h8 :
      GeneralGrammar.Yields FourCountGrammar [d, A, C, B]
        [d, a, C, B] := by
    simpa [A, B, C, a, d] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.emitA [d] [C, B]
  have h9 :
      GeneralGrammar.Yields FourCountGrammar [d, a, C, B]
        [d, a, c, B] := by
    simpa [B, C, a, c, d] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.emitC [d, a] [B]
  have h10 :
      GeneralGrammar.Yields FourCountGrammar [d, a, c, B]
        [d, a, c, b] := by
    simpa [B, a, b, c, d] using
      general_yields_of_production (G := FourCountGrammar)
        FourCountProduces.emitB [d, a, c] []
  have hderives :
      GeneralGrammar.Derives FourCountGrammar [S] [d, a, c, b] :=
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
                        (GeneralGrammar.Derives.refl [d, a, c, b]))))))))))
  simpa [GeneralGrammar.GeneratedLanguage, FourCountGrammar, dacbWord,
    SententialForm.terminalWord, S, a, b, c, d] using hderives


end Section06
end Chapter04
end Book
end FoC
