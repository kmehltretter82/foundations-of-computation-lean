import FoC.Book.Chapter04.Section06.FourCounts

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section06

/-!
# Section 4.6 ordered three-block counts
-/

open Languages
open Grammars

/-!
# Ordered {lit}`a^n b^n c^n`

The ordered construction first creates equal markers, then uses swapping and
phase nonterminals to force all {lit}`a`s before all {lit}`b`s before all {lit}`c`s. The
exactness theorem states that the generated language is exactly the ordered
block language.
-/

inductive OrderedABCNT where
  | start
  | markA
  | markB
  | markC
  | x
  | y
  | z
deriving DecidableEq

namespace OrderedABCNT

def finite : Foundation.FiniteType OrderedABCNT where
  elems := [start, markA, markB, markC, x, y, z]
  complete := by
    intro A
    cases A <;> simp

end OrderedABCNT

def orderedN (A : OrderedABCNT) :
    Symbol EqualCountTerminal OrderedABCNT :=
  ggNonterminal A

def orderedT (tok : EqualCountTerminal) :
    Symbol EqualCountTerminal OrderedABCNT :=
  ggTerminal tok

inductive OrderedABCProduces :
    SententialForm EqualCountTerminal OrderedABCNT ->
      SententialForm EqualCountTerminal OrderedABCNT -> Prop where
  | grow :
      OrderedABCProduces [orderedN OrderedABCNT.start]
        [orderedN OrderedABCNT.start, orderedN OrderedABCNT.markA,
          orderedN OrderedABCNT.markB, orderedN OrderedABCNT.markC]
  | startX :
      OrderedABCProduces [orderedN OrderedABCNT.start] [orderedN OrderedABCNT.x]
  | swapBA :
      OrderedABCProduces [orderedN OrderedABCNT.markB, orderedN OrderedABCNT.markA]
        [orderedN OrderedABCNT.markA, orderedN OrderedABCNT.markB]
  | swapCA :
      OrderedABCProduces [orderedN OrderedABCNT.markC, orderedN OrderedABCNT.markA]
        [orderedN OrderedABCNT.markA, orderedN OrderedABCNT.markC]
  | swapCB :
      OrderedABCProduces [orderedN OrderedABCNT.markC, orderedN OrderedABCNT.markB]
        [orderedN OrderedABCNT.markB, orderedN OrderedABCNT.markC]
  | convertXA :
      OrderedABCProduces [orderedN OrderedABCNT.x, orderedN OrderedABCNT.markA]
        [orderedT EqualCountTerminal.a, orderedN OrderedABCNT.x]
  | xToY :
      OrderedABCProduces [orderedN OrderedABCNT.x] [orderedN OrderedABCNT.y]
  | convertYB :
      OrderedABCProduces [orderedN OrderedABCNT.y, orderedN OrderedABCNT.markB]
        [orderedT EqualCountTerminal.b, orderedN OrderedABCNT.y]
  | yToZ :
      OrderedABCProduces [orderedN OrderedABCNT.y] [orderedN OrderedABCNT.z]
  | convertZC :
      OrderedABCProduces [orderedN OrderedABCNT.z, orderedN OrderedABCNT.markC]
        [orderedT EqualCountTerminal.c, orderedN OrderedABCNT.z]
  | finish :
      OrderedABCProduces [orderedN OrderedABCNT.z] []

def OrderedABCGrammar :
    GeneralGrammar EqualCountTerminal OrderedABCNT where
  start := OrderedABCNT.start
  produces := OrderedABCProduces
  lhsContainsNonterminal := by
    intro lhs rhs h
    cases h <;> simp [SententialForm.containsNonterminal, orderedN,
      ggNonterminal]
  nonterminalsFinite := OrderedABCNT.finite

def OrderedABCProductionList :
    List (GeneralGrammar.Production EqualCountTerminal OrderedABCNT) :=
  [{ lhs := [orderedN OrderedABCNT.start],
     rhs := [orderedN OrderedABCNT.start, orderedN OrderedABCNT.markA,
       orderedN OrderedABCNT.markB, orderedN OrderedABCNT.markC] },
   { lhs := [orderedN OrderedABCNT.start],
     rhs := [orderedN OrderedABCNT.x] },
   { lhs := [orderedN OrderedABCNT.markB, orderedN OrderedABCNT.markA],
     rhs := [orderedN OrderedABCNT.markA, orderedN OrderedABCNT.markB] },
   { lhs := [orderedN OrderedABCNT.markC, orderedN OrderedABCNT.markA],
     rhs := [orderedN OrderedABCNT.markA, orderedN OrderedABCNT.markC] },
   { lhs := [orderedN OrderedABCNT.markC, orderedN OrderedABCNT.markB],
     rhs := [orderedN OrderedABCNT.markB, orderedN OrderedABCNT.markC] },
   { lhs := [orderedN OrderedABCNT.x, orderedN OrderedABCNT.markA],
     rhs := [orderedT EqualCountTerminal.a, orderedN OrderedABCNT.x] },
   { lhs := [orderedN OrderedABCNT.x],
     rhs := [orderedN OrderedABCNT.y] },
   { lhs := [orderedN OrderedABCNT.y, orderedN OrderedABCNT.markB],
     rhs := [orderedT EqualCountTerminal.b, orderedN OrderedABCNT.y] },
   { lhs := [orderedN OrderedABCNT.y],
     rhs := [orderedN OrderedABCNT.z] },
   { lhs := [orderedN OrderedABCNT.z, orderedN OrderedABCNT.markC],
     rhs := [orderedT EqualCountTerminal.c, orderedN OrderedABCNT.z] },
   { lhs := [orderedN OrderedABCNT.z],
     rhs := [] }]

theorem orderedABCGrammar_has_finite_productions :
    GeneralGrammar.HasFiniteProductions OrderedABCGrammar := by
  exists OrderedABCProductionList
  intro lhs rhs
  constructor
  · intro h
    cases h <;> simp [OrderedABCProductionList]
  · intro h
    rcases h with ⟨rule, hmem, hlhs, hrhs⟩
    simp [OrderedABCProductionList] at hmem
    rcases hmem with
      hrule | hrule | hrule | hrule | hrule | hrule |
      hrule | hrule | hrule | hrule | hrule
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.grow
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.startX
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.swapBA
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.swapCA
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.swapCB
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.convertXA
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.xToY
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.convertYB
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.yToZ
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.convertZC
    · subst rule
      cases hlhs
      cases hrhs
      exact OrderedABCProduces.finish

theorem orderedABCGrammar_finite_production_generated :
    FiniteProductionGeneralLanguage
      (GeneralGrammar.GeneratedLanguage OrderedABCGrammar) := by
  exists OrderedABCNT
  exists OrderedABCGrammar
  constructor
  · exact orderedABCGrammar_has_finite_productions
  · intro w
    rfl

/-!
The ordered grammar still grows one marker of each kind, but the cleanup rules
force the marker blocks into {lit}`A* B* C*` order before terminals are emitted.
The invariant below proves equal counts; a later shape proof proves that the
terminal order is also correct.
-/

def orderedABCTotalA (sf : SententialForm EqualCountTerminal OrderedABCNT) :
    Nat :=
  SententialCountTerminal EqualCountTerminal.a sf +
    SententialCountNonterminal OrderedABCNT.markA sf

def orderedABCTotalB (sf : SententialForm EqualCountTerminal OrderedABCNT) :
    Nat :=
  SententialCountTerminal EqualCountTerminal.b sf +
    SententialCountNonterminal OrderedABCNT.markB sf

def orderedABCTotalC (sf : SententialForm EqualCountTerminal OrderedABCNT) :
    Nat :=
  SententialCountTerminal EqualCountTerminal.c sf +
    SententialCountNonterminal OrderedABCNT.markC sf

def orderedABCBalanced
    (sf : SententialForm EqualCountTerminal OrderedABCNT) : Prop :=
  orderedABCTotalA sf = orderedABCTotalB sf ∧
    orderedABCTotalB sf = orderedABCTotalC sf

theorem orderedABC_start_balanced :
    orderedABCBalanced [orderedN OrderedABCNT.start] := by
  simp [orderedABCBalanced, orderedABCTotalA, orderedABCTotalB,
    orderedABCTotalC, SententialCountTerminal, SententialCountNonterminal,
    orderedN, ggNonterminal]

theorem orderedABC_yields_preserves_balanced
    {x y : SententialForm EqualCountTerminal OrderedABCNT}
    (h : GeneralGrammar.Yields OrderedABCGrammar x y) :
    orderedABCBalanced x -> orderedABCBalanced y := by
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
                            simp [orderedABCBalanced, orderedABCTotalA,
                              orderedABCTotalB, orderedABCTotalC,
                              sententialCountTerminal_append,
                              sententialCountNonterminal_append,
                              SententialCountTerminal,
                              SententialCountNonterminal, orderedN,
                              orderedT, ggNonterminal, ggTerminal] at hbalanced ⊢ <;>
                            omega

theorem orderedABC_derives_preserves_balanced
    {x y : SententialForm EqualCountTerminal OrderedABCNT}
    (h : GeneralGrammar.Derives OrderedABCGrammar x y) :
    orderedABCBalanced x -> orderedABCBalanced y := by
  induction h with
  | refl _ =>
      intro hbalanced
      exact hbalanced
  | step hstep _ ih =>
      intro hbalanced
      exact ih (orderedABC_yields_preserves_balanced hstep hbalanced)

theorem orderedABCGrammar_generated_has_equal_terminal_counts
    {word : Word EqualCountTerminal}
    (h : word ∈ GeneralGrammar.GeneratedLanguage OrderedABCGrammar) :
    Word.Count EqualCountTerminal.a word =
        Word.Count EqualCountTerminal.b word ∧
      Word.Count EqualCountTerminal.b word =
        Word.Count EqualCountTerminal.c word := by
  have hderives :
      GeneralGrammar.Derives OrderedABCGrammar [orderedN OrderedABCNT.start]
        (SententialForm.terminalWord word) := by
    simpa [GeneralGrammar.GeneratedLanguage, OrderedABCGrammar, orderedN,
      ggNonterminal] using h
  have hbalanced :=
    orderedABC_derives_preserves_balanced hderives
      orderedABC_start_balanced
  simpa [orderedABCBalanced, orderedABCTotalA, orderedABCTotalB,
    orderedABCTotalC, sententialCountTerminal_terminalWord,
    sententialCountNonterminal_terminalWord] using hbalanced

def orderedABCBlockWord (n : Nat) : Word EqualCountTerminal :=
  Word.Concat (Word.RepeatSymbol EqualCountTerminal.a n)
    (Word.Concat (Word.RepeatSymbol EqualCountTerminal.b n)
      (Word.RepeatSymbol EqualCountTerminal.c n))

def orderedABCLanguage : Language EqualCountTerminal :=
  fun word => exists n, word = orderedABCBlockWord n

def orderedABCAForm (n : Nat) :
    SententialForm EqualCountTerminal OrderedABCNT :=
  List.replicate n (orderedN OrderedABCNT.markA)

def orderedABCBForm (n : Nat) :
    SententialForm EqualCountTerminal OrderedABCNT :=
  List.replicate n (orderedN OrderedABCNT.markB)

def orderedABCCForm (n : Nat) :
    SententialForm EqualCountTerminal OrderedABCNT :=
  List.replicate n (orderedN OrderedABCNT.markC)

def orderedABCMarkerBlock :
    SententialForm EqualCountTerminal OrderedABCNT :=
  [orderedN OrderedABCNT.markA, orderedN OrderedABCNT.markB,
    orderedN OrderedABCNT.markC]

def orderedABCRepeatedMarkers (n : Nat) :
    SententialForm EqualCountTerminal OrderedABCNT :=
  Word.RepeatWord orderedABCMarkerBlock n

def orderedABCSortedMarkers (n : Nat) :
    SententialForm EqualCountTerminal OrderedABCNT :=
  orderedABCAForm n ++ orderedABCBForm n ++ orderedABCCForm n

/-!
The generation proof is a pipeline: sort the generated markers, convert all
{lit}`X` markers to {lit}`a`s, convert all {lit}`Y` markers to {lit}`b`s, and
convert all {lit}`Z` markers to {lit}`c`s.
-/

theorem orderedABC_moveC_right_over_as
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal OrderedABCNT) :
    GeneralGrammar.Derives OrderedABCGrammar
      (pre ++ [orderedN OrderedABCNT.markC] ++
        orderedABCAForm n ++ suffix)
      (pre ++ orderedABCAForm n ++ [orderedN OrderedABCNT.markC] ++
        suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [orderedABCAForm] using
        (GeneralGrammar.Derives.refl (G := OrderedABCGrammar)
          (pre ++ [orderedN OrderedABCNT.markC] ++ suffix))
  | succ n ih =>
      let A := orderedN OrderedABCNT.markA
      let C := orderedN OrderedABCNT.markC
      have hstep :
          GeneralGrammar.Yields OrderedABCGrammar
            (pre ++ [C, A] ++ orderedABCAForm n ++ suffix)
            (pre ++ [A, C] ++ orderedABCAForm n ++ suffix) := by
        simpa [A, C, List.append_assoc] using
          general_yields_of_production (G := OrderedABCGrammar)
            OrderedABCProduces.swapCA pre
            (orderedABCAForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives OrderedABCGrammar
            (pre ++ [A, C] ++ orderedABCAForm n ++ suffix)
            (pre ++ [A] ++ orderedABCAForm n ++ [C] ++ suffix) := by
        simpa [A, C, List.append_assoc] using ih (pre ++ [A])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [orderedABCAForm, A, C, List.append_assoc] using hall

theorem orderedABC_moveB_right_over_as
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal OrderedABCNT) :
    GeneralGrammar.Derives OrderedABCGrammar
      (pre ++ [orderedN OrderedABCNT.markB] ++
        orderedABCAForm n ++ suffix)
      (pre ++ orderedABCAForm n ++ [orderedN OrderedABCNT.markB] ++
        suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [orderedABCAForm] using
        (GeneralGrammar.Derives.refl (G := OrderedABCGrammar)
          (pre ++ [orderedN OrderedABCNT.markB] ++ suffix))
  | succ n ih =>
      let A := orderedN OrderedABCNT.markA
      let B := orderedN OrderedABCNT.markB
      have hstep :
          GeneralGrammar.Yields OrderedABCGrammar
            (pre ++ [B, A] ++ orderedABCAForm n ++ suffix)
            (pre ++ [A, B] ++ orderedABCAForm n ++ suffix) := by
        simpa [A, B, List.append_assoc] using
          general_yields_of_production (G := OrderedABCGrammar)
            OrderedABCProduces.swapBA pre
            (orderedABCAForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives OrderedABCGrammar
            (pre ++ [A, B] ++ orderedABCAForm n ++ suffix)
            (pre ++ [A] ++ orderedABCAForm n ++ [B] ++ suffix) := by
        simpa [A, B, List.append_assoc] using ih (pre ++ [A])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [orderedABCAForm, A, B, List.append_assoc] using hall

theorem orderedABC_moveC_right_over_bs
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal OrderedABCNT) :
    GeneralGrammar.Derives OrderedABCGrammar
      (pre ++ [orderedN OrderedABCNT.markC] ++
        orderedABCBForm n ++ suffix)
      (pre ++ orderedABCBForm n ++ [orderedN OrderedABCNT.markC] ++
        suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [orderedABCBForm] using
        (GeneralGrammar.Derives.refl (G := OrderedABCGrammar)
          (pre ++ [orderedN OrderedABCNT.markC] ++ suffix))
  | succ n ih =>
      let B := orderedN OrderedABCNT.markB
      let C := orderedN OrderedABCNT.markC
      have hstep :
          GeneralGrammar.Yields OrderedABCGrammar
            (pre ++ [C, B] ++ orderedABCBForm n ++ suffix)
            (pre ++ [B, C] ++ orderedABCBForm n ++ suffix) := by
        simpa [B, C, List.append_assoc] using
          general_yields_of_production (G := OrderedABCGrammar)
            OrderedABCProduces.swapCB pre
            (orderedABCBForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives OrderedABCGrammar
            (pre ++ [B, C] ++ orderedABCBForm n ++ suffix)
            (pre ++ [B] ++ orderedABCBForm n ++ [C] ++ suffix) := by
        simpa [B, C, List.append_assoc] using ih (pre ++ [B])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [orderedABCBForm, B, C, List.append_assoc] using hall

/-!
The ordered {lit}`a^n b^n c^n` construction repeats the marker strategy, but the
target word must be sorted by terminal block. The next derivations move markers
into the ordered arrangement before converting them to terminals.
-/

theorem orderedABC_sort_markers_derives (n : Nat) :
    GeneralGrammar.Derives OrderedABCGrammar
      (orderedABCRepeatedMarkers n) (orderedABCSortedMarkers n) := by
  induction n with
  | zero =>
      exact GeneralGrammar.Derives.refl []
  | succ n ih =>
      let A := orderedN OrderedABCNT.markA
      let B := orderedN OrderedABCNT.markB
      let C := orderedN OrderedABCNT.markC
      have hsortTail :
          GeneralGrammar.Derives OrderedABCGrammar
            (orderedABCMarkerBlock ++ orderedABCRepeatedMarkers n)
            (orderedABCMarkerBlock ++ orderedABCSortedMarkers n) := by
        simpa [orderedABCMarkerBlock, A, B, C, List.append_assoc] using
          general_derives_context ih orderedABCMarkerBlock []
      have hmoveCAs :
          GeneralGrammar.Derives OrderedABCGrammar
            (orderedABCMarkerBlock ++ orderedABCSortedMarkers n)
            ([A, B] ++ orderedABCAForm n ++ [C] ++
              orderedABCBForm n ++ orderedABCCForm n) := by
        simpa [orderedABCMarkerBlock, orderedABCSortedMarkers, A, B, C,
          List.append_assoc] using
          orderedABC_moveC_right_over_as n [A, B]
            (orderedABCBForm n ++ orderedABCCForm n)
      have hmoveBAs :
          GeneralGrammar.Derives OrderedABCGrammar
            ([A, B] ++ orderedABCAForm n ++ [C] ++
              orderedABCBForm n ++ orderedABCCForm n)
            ([A] ++ orderedABCAForm n ++ [B, C] ++
              orderedABCBForm n ++ orderedABCCForm n) := by
        simpa [A, B, C, List.append_assoc] using
          orderedABC_moveB_right_over_as n [A]
            ([C] ++ orderedABCBForm n ++ orderedABCCForm n)
      have hmoveCBs :
          GeneralGrammar.Derives OrderedABCGrammar
            ([A] ++ orderedABCAForm n ++ [B, C] ++
              orderedABCBForm n ++ orderedABCCForm n)
            (orderedABCSortedMarkers (n + 1)) := by
        simpa [orderedABCSortedMarkers, orderedABCAForm, orderedABCBForm,
          orderedABCCForm, A, B, C, List.append_assoc] using
          orderedABC_moveC_right_over_bs n
            ([A] ++ orderedABCAForm n ++ [B]) (orderedABCCForm n)
      exact GeneralGrammar.derives_trans hsortTail
        (GeneralGrammar.derives_trans hmoveCAs
          (GeneralGrammar.derives_trans hmoveBAs hmoveCBs))

theorem orderedABC_grow_repeated_markers_derives (n : Nat) :
    GeneralGrammar.Derives OrderedABCGrammar [orderedN OrderedABCNT.start]
      ([orderedN OrderedABCNT.start] ++ orderedABCRepeatedMarkers n) := by
  induction n with
  | zero =>
      simpa [orderedABCRepeatedMarkers, Word.RepeatWord] using
        (GeneralGrammar.Derives.refl (G := OrderedABCGrammar)
          [orderedN OrderedABCNT.start])
  | succ n ih =>
      have hstep :
          GeneralGrammar.Yields OrderedABCGrammar
            ([orderedN OrderedABCNT.start] ++ orderedABCRepeatedMarkers n)
            ([orderedN OrderedABCNT.start] ++ orderedABCMarkerBlock ++
              orderedABCRepeatedMarkers n) := by
        simpa [orderedABCMarkerBlock, List.append_assoc] using
          general_yields_of_production (G := OrderedABCGrammar)
            OrderedABCProduces.grow [] (orderedABCRepeatedMarkers n)
      have hall := GeneralGrammar.derives_trans ih
        (GeneralGrammar.yields_derives hstep)
      simpa [orderedABCRepeatedMarkers, orderedABCMarkerBlock,
        Word.RepeatWord, List.append_assoc] using hall

theorem orderedABC_start_to_repeated_markers_derives (n : Nat) :
    GeneralGrammar.Derives OrderedABCGrammar [orderedN OrderedABCNT.start]
      ([orderedN OrderedABCNT.x] ++ orderedABCRepeatedMarkers n) := by
  have hgrow := orderedABC_grow_repeated_markers_derives n
  have hstep :
      GeneralGrammar.Yields OrderedABCGrammar
        ([orderedN OrderedABCNT.start] ++ orderedABCRepeatedMarkers n)
        ([orderedN OrderedABCNT.x] ++ orderedABCRepeatedMarkers n) := by
    simpa [List.append_assoc] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.startX [] (orderedABCRepeatedMarkers n)
  exact GeneralGrammar.derives_trans hgrow
    (GeneralGrammar.yields_derives hstep)

/-!
Once the ordered marker block is assembled, the conversion phase proceeds one
region at a time: X markers become a's, Y markers become b's, and Z markers
become c's.
-/

theorem orderedABC_convert_x_as_derives
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal OrderedABCNT) :
    GeneralGrammar.Derives OrderedABCGrammar
      (pre ++ [orderedN OrderedABCNT.x] ++ orderedABCAForm n ++ suffix)
      (pre ++
        SententialForm.terminalWord
          (Word.RepeatSymbol EqualCountTerminal.a n) ++
        [orderedN OrderedABCNT.x] ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [orderedABCAForm, Word.RepeatSymbol,
        SententialForm.terminalWord, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := OrderedABCGrammar)
          (pre ++ [orderedN OrderedABCNT.x] ++ suffix))
  | succ n ih =>
      let X := orderedN OrderedABCNT.x
      let A := orderedN OrderedABCNT.markA
      let a := orderedT EqualCountTerminal.a
      have hstep :
          GeneralGrammar.Yields OrderedABCGrammar
            (pre ++ [X, A] ++ orderedABCAForm n ++ suffix)
            (pre ++ [a, X] ++ orderedABCAForm n ++ suffix) := by
        simpa [X, A, a, List.append_assoc] using
          general_yields_of_production (G := OrderedABCGrammar)
            OrderedABCProduces.convertXA pre (orderedABCAForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives OrderedABCGrammar
            (pre ++ [a, X] ++ orderedABCAForm n ++ suffix)
            (pre ++ [a] ++
              SententialForm.terminalWord
                (Word.RepeatSymbol EqualCountTerminal.a n) ++
              [X] ++ suffix) := by
        simpa [X, a, List.append_assoc] using ih (pre ++ [a])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [orderedABCAForm, X, A, a, Word.RepeatSymbol,
        SententialForm.terminalWord, List.append_assoc] using hall

theorem orderedABC_convert_y_bs_derives
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal OrderedABCNT) :
    GeneralGrammar.Derives OrderedABCGrammar
      (pre ++ [orderedN OrderedABCNT.y] ++ orderedABCBForm n ++ suffix)
      (pre ++
        SententialForm.terminalWord
          (Word.RepeatSymbol EqualCountTerminal.b n) ++
        [orderedN OrderedABCNT.y] ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [orderedABCBForm, Word.RepeatSymbol,
        SententialForm.terminalWord, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := OrderedABCGrammar)
          (pre ++ [orderedN OrderedABCNT.y] ++ suffix))
  | succ n ih =>
      let Y := orderedN OrderedABCNT.y
      let B := orderedN OrderedABCNT.markB
      let b := orderedT EqualCountTerminal.b
      have hstep :
          GeneralGrammar.Yields OrderedABCGrammar
            (pre ++ [Y, B] ++ orderedABCBForm n ++ suffix)
            (pre ++ [b, Y] ++ orderedABCBForm n ++ suffix) := by
        simpa [Y, B, b, List.append_assoc] using
          general_yields_of_production (G := OrderedABCGrammar)
            OrderedABCProduces.convertYB pre (orderedABCBForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives OrderedABCGrammar
            (pre ++ [b, Y] ++ orderedABCBForm n ++ suffix)
            (pre ++ [b] ++
              SententialForm.terminalWord
                (Word.RepeatSymbol EqualCountTerminal.b n) ++
              [Y] ++ suffix) := by
        simpa [Y, b, List.append_assoc] using ih (pre ++ [b])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [orderedABCBForm, Y, B, b, Word.RepeatSymbol,
        SententialForm.terminalWord, List.append_assoc] using hall

theorem orderedABC_convert_z_cs_derives
    (n : Nat) (pre suffix : SententialForm EqualCountTerminal OrderedABCNT) :
    GeneralGrammar.Derives OrderedABCGrammar
      (pre ++ [orderedN OrderedABCNT.z] ++ orderedABCCForm n ++ suffix)
      (pre ++
        SententialForm.terminalWord
          (Word.RepeatSymbol EqualCountTerminal.c n) ++
        [orderedN OrderedABCNT.z] ++ suffix) := by
  induction n generalizing pre with
  | zero =>
      simpa [orderedABCCForm, Word.RepeatSymbol,
        SententialForm.terminalWord, List.append_assoc] using
        (GeneralGrammar.Derives.refl (G := OrderedABCGrammar)
          (pre ++ [orderedN OrderedABCNT.z] ++ suffix))
  | succ n ih =>
      let Z := orderedN OrderedABCNT.z
      let C := orderedN OrderedABCNT.markC
      let c := orderedT EqualCountTerminal.c
      have hstep :
          GeneralGrammar.Yields OrderedABCGrammar
            (pre ++ [Z, C] ++ orderedABCCForm n ++ suffix)
            (pre ++ [c, Z] ++ orderedABCCForm n ++ suffix) := by
        simpa [Z, C, c, List.append_assoc] using
          general_yields_of_production (G := OrderedABCGrammar)
            OrderedABCProduces.convertZC pre (orderedABCCForm n ++ suffix)
      have hrest :
          GeneralGrammar.Derives OrderedABCGrammar
            (pre ++ [c, Z] ++ orderedABCCForm n ++ suffix)
            (pre ++ [c] ++
              SententialForm.terminalWord
                (Word.RepeatSymbol EqualCountTerminal.c n) ++
              [Z] ++ suffix) := by
        simpa [Z, c, List.append_assoc] using ih (pre ++ [c])
      have hall := GeneralGrammar.Derives.step hstep hrest
      simpa [orderedABCCForm, Z, C, c, Word.RepeatSymbol,
        SententialForm.terminalWord, List.append_assoc] using hall

/-!
The sorted-marker-to-word theorem is the terminal conversion step for the
ordered three-block grammar. It consumes the entire sorted marker form and
produces the concrete block word.
-/

theorem orderedABC_sorted_markers_to_word_derives (n : Nat) :
    GeneralGrammar.Derives OrderedABCGrammar
      ([orderedN OrderedABCNT.x] ++ orderedABCSortedMarkers n)
      (SententialForm.terminalWord (orderedABCBlockWord n)) := by
  let X := orderedN OrderedABCNT.x
  let Y := orderedN OrderedABCNT.y
  let Z := orderedN OrderedABCNT.z
  let aWord : SententialForm EqualCountTerminal OrderedABCNT :=
    SententialForm.terminalWord (Word.RepeatSymbol EqualCountTerminal.a n)
  let bWord : SententialForm EqualCountTerminal OrderedABCNT :=
    SententialForm.terminalWord (Word.RepeatSymbol EqualCountTerminal.b n)
  let cWord : SententialForm EqualCountTerminal OrderedABCNT :=
    SententialForm.terminalWord (Word.RepeatSymbol EqualCountTerminal.c n)
  have hAs :
      GeneralGrammar.Derives OrderedABCGrammar
        ([X] ++ orderedABCSortedMarkers n)
        (aWord ++ [X] ++ orderedABCBForm n ++ orderedABCCForm n) := by
    simpa [orderedABCSortedMarkers, X, aWord, List.append_assoc] using
      orderedABC_convert_x_as_derives n []
        (orderedABCBForm n ++ orderedABCCForm n)
  have hXToY :
      GeneralGrammar.Derives OrderedABCGrammar
        (aWord ++ [X] ++ orderedABCBForm n ++ orderedABCCForm n)
        (aWord ++ [Y] ++ orderedABCBForm n ++ orderedABCCForm n) := by
    have hstep :
        GeneralGrammar.Yields OrderedABCGrammar
          (aWord ++ [X] ++ orderedABCBForm n ++ orderedABCCForm n)
          (aWord ++ [Y] ++ orderedABCBForm n ++ orderedABCCForm n) := by
      simpa [X, Y, List.append_assoc] using
        general_yields_of_production (G := OrderedABCGrammar)
          OrderedABCProduces.xToY aWord
          (orderedABCBForm n ++ orderedABCCForm n)
    exact GeneralGrammar.yields_derives hstep
  have hBs :
      GeneralGrammar.Derives OrderedABCGrammar
        (aWord ++ [Y] ++ orderedABCBForm n ++ orderedABCCForm n)
        (aWord ++ bWord ++ [Y] ++ orderedABCCForm n) := by
    simpa [Y, bWord, List.append_assoc] using
      orderedABC_convert_y_bs_derives n aWord (orderedABCCForm n)
  have hYToZ :
      GeneralGrammar.Derives OrderedABCGrammar
        (aWord ++ bWord ++ [Y] ++ orderedABCCForm n)
        (aWord ++ bWord ++ [Z] ++ orderedABCCForm n) := by
    have hstep :
        GeneralGrammar.Yields OrderedABCGrammar
          (aWord ++ bWord ++ [Y] ++ orderedABCCForm n)
          (aWord ++ bWord ++ [Z] ++ orderedABCCForm n) := by
      simpa [Y, Z, List.append_assoc] using
        general_yields_of_production (G := OrderedABCGrammar)
          OrderedABCProduces.yToZ (aWord ++ bWord) (orderedABCCForm n)
    exact GeneralGrammar.yields_derives hstep
  have hCs :
      GeneralGrammar.Derives OrderedABCGrammar
        (aWord ++ bWord ++ [Z] ++ orderedABCCForm n)
        (aWord ++ bWord ++ cWord ++ [Z]) := by
    simpa [Z, cWord, List.append_assoc] using
      orderedABC_convert_z_cs_derives n (aWord ++ bWord) []
  have hFinish :
      GeneralGrammar.Derives OrderedABCGrammar
        (aWord ++ bWord ++ cWord ++ [Z])
        (aWord ++ bWord ++ cWord) := by
    have hstep :
        GeneralGrammar.Yields OrderedABCGrammar
          (aWord ++ bWord ++ cWord ++ [Z])
          (aWord ++ bWord ++ cWord) := by
      simpa [Z, List.append_assoc] using
        general_yields_of_production (G := OrderedABCGrammar)
          OrderedABCProduces.finish (aWord ++ bWord ++ cWord) []
    exact GeneralGrammar.yields_derives hstep
  have hall := GeneralGrammar.derives_trans hAs
    (GeneralGrammar.derives_trans hXToY
      (GeneralGrammar.derives_trans hBs
        (GeneralGrammar.derives_trans hYToZ
          (GeneralGrammar.derives_trans hCs hFinish))))
  rw [orderedABCBlockWord, SententialForm.terminalWord_append,
    SententialForm.terminalWord_append]
  simpa [aWord, bWord, cWord, Word.Concat, List.append_assoc] using hall

theorem orderedABC_words_generated (n : Nat) :
    orderedABCBlockWord n ∈
      GeneralGrammar.GeneratedLanguage OrderedABCGrammar := by
  have hstart := orderedABC_start_to_repeated_markers_derives n
  have hsort :
      GeneralGrammar.Derives OrderedABCGrammar
        ([orderedN OrderedABCNT.x] ++ orderedABCRepeatedMarkers n)
        ([orderedN OrderedABCNT.x] ++ orderedABCSortedMarkers n) := by
    simpa [List.append_assoc] using
      general_derives_context (orderedABC_sort_markers_derives n)
        [orderedN OrderedABCNT.x] []
  have hconvert := orderedABC_sorted_markers_to_word_derives n
  have hall := GeneralGrammar.derives_trans hstart
    (GeneralGrammar.derives_trans hsort hconvert)
  simpa [GeneralGrammar.GeneratedLanguage, OrderedABCGrammar, orderedN,
    ggNonterminal] using hall

theorem orderedABC_language_subset_generated {word : Word EqualCountTerminal}
    (h : word ∈ orderedABCLanguage) :
    word ∈ GeneralGrammar.GeneratedLanguage OrderedABCGrammar := by
  rcases h with ⟨n, hword⟩
  rw [hword]
  exact orderedABC_words_generated n

def orderedABCShapeWord (aCount bCount cCount : Nat) :
    Word EqualCountTerminal :=
  Word.Concat (Word.RepeatSymbol EqualCountTerminal.a aCount)
    (Word.Concat (Word.RepeatSymbol EqualCountTerminal.b bCount)
      (Word.RepeatSymbol EqualCountTerminal.c cCount))

def orderedABCBCShapeWord (bCount cCount : Nat) :
    Word EqualCountTerminal :=
  Word.Concat (Word.RepeatSymbol EqualCountTerminal.b bCount)
    (Word.RepeatSymbol EqualCountTerminal.c cCount)

def orderedABCCShapeWord (cCount : Nat) : Word EqualCountTerminal :=
  Word.RepeatSymbol EqualCountTerminal.c cCount

def orderedABCShapeLanguage : Language EqualCountTerminal :=
  fun word => exists aCount bCount cCount,
    word = orderedABCShapeWord aCount bCount cCount

def orderedABCBCShapeLanguage : Language EqualCountTerminal :=
  fun word => exists bCount cCount,
    word = orderedABCBCShapeWord bCount cCount

def orderedABCCShapeLanguage : Language EqualCountTerminal :=
  fun word => exists cCount, word = orderedABCCShapeWord cCount

def orderedABCSymbolLanguage :
    Symbol EqualCountTerminal OrderedABCNT -> Language EqualCountTerminal
  | Symbol.terminal token => Language.Singleton (Word.Symbol token)
  | Symbol.nonterminal OrderedABCNT.start => orderedABCShapeLanguage
  | Symbol.nonterminal OrderedABCNT.markA => Language.Singleton Word.Empty
  | Symbol.nonterminal OrderedABCNT.markB => Language.Singleton Word.Empty
  | Symbol.nonterminal OrderedABCNT.markC => Language.Singleton Word.Empty
  | Symbol.nonterminal OrderedABCNT.x => orderedABCShapeLanguage
  | Symbol.nonterminal OrderedABCNT.y => orderedABCBCShapeLanguage
  | Symbol.nonterminal OrderedABCNT.z => orderedABCCShapeLanguage

/-!
The soundness proof uses shape languages. They track not just the counts, but
also the phase of the ordered block: full {lit}`a* b* c*`, then {lit}`b* c*`,
then {lit}`c*`.
-/

theorem orderedABCShape_cons_a {word : Word EqualCountTerminal}
    (h : word ∈ orderedABCShapeLanguage) :
    Word.Concat [EqualCountTerminal.a] word ∈ orderedABCShapeLanguage := by
  rcases h with ⟨aCount, bCount, cCount, hword⟩
  exists Nat.succ aCount
  exists bCount
  exists cCount
  rw [hword]
  change EqualCountTerminal.a ::
      orderedABCShapeWord aCount bCount cCount =
    orderedABCShapeWord (Nat.succ aCount) bCount cCount
  rfl

theorem orderedABCBCShape_cons_b {word : Word EqualCountTerminal}
    (h : word ∈ orderedABCBCShapeLanguage) :
    Word.Concat [EqualCountTerminal.b] word ∈ orderedABCBCShapeLanguage := by
  rcases h with ⟨bCount, cCount, hword⟩
  exists Nat.succ bCount
  exists cCount
  rw [hword]
  change EqualCountTerminal.b :: orderedABCBCShapeWord bCount cCount =
    orderedABCBCShapeWord (Nat.succ bCount) cCount
  rfl

theorem orderedABCCShape_cons_c {word : Word EqualCountTerminal}
    (h : word ∈ orderedABCCShapeLanguage) :
    Word.Concat [EqualCountTerminal.c] word ∈ orderedABCCShapeLanguage := by
  rcases h with ⟨cCount, hword⟩
  exists Nat.succ cCount
  rw [hword]
  change EqualCountTerminal.c :: orderedABCCShapeWord cCount =
    orderedABCCShapeWord (Nat.succ cCount)
  rfl

theorem orderedABCBCShape_subset_shape {word : Word EqualCountTerminal}
    (h : word ∈ orderedABCBCShapeLanguage) :
    word ∈ orderedABCShapeLanguage := by
  rcases h with ⟨bCount, cCount, hword⟩
  exists 0
  exists bCount
  exists cCount

theorem orderedABCCShape_subset_bcShape {word : Word EqualCountTerminal}
    (h : word ∈ orderedABCCShapeLanguage) :
    word ∈ orderedABCBCShapeLanguage := by
  rcases h with ⟨cCount, hword⟩
  exists 0
  exists cCount

theorem orderedABCCShape_empty :
    Word.Empty ∈ orderedABCCShapeLanguage := by
  exists 0

theorem orderedABCShapeWord_count_a (aCount bCount cCount : Nat) :
    Word.Count EqualCountTerminal.a
      (orderedABCShapeWord aCount bCount cCount) = aCount := by
  simp [orderedABCShapeWord, word_count_concat,
    word_count_repeat_same, word_count_repeat_of_ne]

theorem orderedABCShapeWord_count_b (aCount bCount cCount : Nat) :
    Word.Count EqualCountTerminal.b
      (orderedABCShapeWord aCount bCount cCount) = bCount := by
  simp [orderedABCShapeWord, word_count_concat,
    word_count_repeat_same, word_count_repeat_of_ne]

theorem orderedABCShapeWord_count_c (aCount bCount cCount : Nat) :
    Word.Count EqualCountTerminal.c
      (orderedABCShapeWord aCount bCount cCount) = cCount := by
  simp [orderedABCShapeWord, word_count_concat,
    word_count_repeat_same, word_count_repeat_of_ne]

theorem orderedABCBlockWord_eq_shape (n : Nat) :
    orderedABCBlockWord n = orderedABCShapeWord n n n := by
  rfl

/-!
The shape lemmas separate ordering from counting. They show that any generated
ordered word has the correct block structure and equal counts, which gives the
semantic reverse direction for the grammar.
-/

theorem orderedABCShape_equal_counts_language
    {word : Word EqualCountTerminal}
    (hshape : word ∈ orderedABCShapeLanguage)
    (hcounts :
      Word.Count EqualCountTerminal.a word =
          Word.Count EqualCountTerminal.b word ∧
        Word.Count EqualCountTerminal.b word =
          Word.Count EqualCountTerminal.c word) :
    word ∈ orderedABCLanguage := by
  rcases hshape with ⟨aCount, bCount, cCount, hword⟩
  have ha :
      Word.Count EqualCountTerminal.a word = aCount := by
    rw [hword]
    exact orderedABCShapeWord_count_a aCount bCount cCount
  have hb :
      Word.Count EqualCountTerminal.b word = bCount := by
    rw [hword]
    exact orderedABCShapeWord_count_b aCount bCount cCount
  have hc :
      Word.Count EqualCountTerminal.c word = cCount := by
    rw [hword]
    exact orderedABCShapeWord_count_c aCount bCount cCount
  have hab : aCount = bCount := by
    omega
  have hbc : bCount = cCount := by
    omega
  exists aCount
  rw [hword, orderedABCBlockWord_eq_shape, hab, hbc]

theorem orderedABC_production_shape_sound
    {lhs rhs : SententialForm EqualCountTerminal OrderedABCNT}
    (hprod : OrderedABCGrammar.produces lhs rhs) :
    forall word, word ∈ CFG.FormLanguage orderedABCSymbolLanguage rhs ->
      word ∈ CFG.FormLanguage orderedABCSymbolLanguage lhs := by
  intro word hw
  let eps : Language EqualCountTerminal :=
    Language.Singleton (Word.Empty : Word EqualCountTerminal)
  have hepsOnly : forall suffix, suffix ∈ eps -> suffix = Word.Empty := by
    intro suffix hsuffix
    exact hsuffix
  have hepsMem : (Word.Empty : Word EqualCountTerminal) ∈ eps := rfl
  have heps2Only :
      forall suffix, suffix ∈ Language.Concat eps eps ->
        suffix = Word.Empty :=
    language_concat_empty_only hepsOnly hepsOnly
  have heps2Mem :
      (Word.Empty : Word EqualCountTerminal) ∈ Language.Concat eps eps :=
    language_concat_empty_mem hepsMem hepsMem
  have heps3Only :
      forall suffix, suffix ∈ Language.Concat eps (Language.Concat eps eps) ->
        suffix = Word.Empty :=
    language_concat_empty_only hepsOnly heps2Only
  have heps4Only :
      forall suffix,
        suffix ∈
          Language.Concat eps
            (Language.Concat eps (Language.Concat eps eps)) ->
        suffix = Word.Empty :=
    language_concat_empty_only hepsOnly heps3Only
  cases hprod
  · simp [CFG.FormLanguage, orderedABCSymbolLanguage, orderedN,
      ggNonterminal] at hw ⊢
    have hshape :=
      language_concat_right_empty_only_mem heps4Only hw
    exact language_concat_right_empty_mem hepsMem hshape
  · simpa [OrderedABCGrammar, CFG.FormLanguage, orderedABCSymbolLanguage,
      orderedN, orderedT, ggNonterminal, ggTerminal] using hw
  · simpa [OrderedABCGrammar, CFG.FormLanguage, orderedABCSymbolLanguage,
      orderedN, orderedT, ggNonterminal, ggTerminal] using hw
  · simpa [OrderedABCGrammar, CFG.FormLanguage, orderedABCSymbolLanguage,
      orderedN, orderedT, ggNonterminal, ggTerminal] using hw
  · simpa [OrderedABCGrammar, CFG.FormLanguage, orderedABCSymbolLanguage,
      orderedN, orderedT, ggNonterminal, ggTerminal] using hw
  · simp [CFG.FormLanguage, orderedABCSymbolLanguage,
      orderedN, orderedT, ggNonterminal, ggTerminal] at hw ⊢
    rcases hw with ⟨pref, suffix, hpref, hsuffix, hword⟩
    have hsuffixShape :
        suffix ∈ orderedABCShapeLanguage :=
      language_concat_right_empty_only_mem hepsOnly hsuffix
    have hshape : word ∈ orderedABCShapeLanguage := by
      rw [hword, hpref]
      simpa [Word.Symbol] using orderedABCShape_cons_a hsuffixShape
    exact language_concat_right_empty_mem heps2Mem hshape
  · simp [CFG.FormLanguage, orderedABCSymbolLanguage, orderedN,
      ggNonterminal] at hw ⊢
    have htail :=
      language_concat_right_empty_only_mem hepsOnly hw
    exact language_concat_right_empty_mem hepsMem
      (orderedABCBCShape_subset_shape htail)
  · simp [CFG.FormLanguage, orderedABCSymbolLanguage,
      orderedN, orderedT, ggNonterminal, ggTerminal] at hw ⊢
    rcases hw with ⟨pref, suffix, hpref, hsuffix, hword⟩
    have hsuffixShape :
        suffix ∈ orderedABCBCShapeLanguage :=
      language_concat_right_empty_only_mem hepsOnly hsuffix
    have hshape : word ∈ orderedABCBCShapeLanguage := by
      rw [hword, hpref]
      simpa [Word.Symbol] using orderedABCBCShape_cons_b hsuffixShape
    exact language_concat_right_empty_mem heps2Mem hshape
  · simp [CFG.FormLanguage, orderedABCSymbolLanguage, orderedN,
      ggNonterminal] at hw ⊢
    have htail :=
      language_concat_right_empty_only_mem hepsOnly hw
    exact language_concat_right_empty_mem hepsMem
      (orderedABCCShape_subset_bcShape htail)
  · simp [CFG.FormLanguage, orderedABCSymbolLanguage,
      orderedN, orderedT, ggNonterminal, ggTerminal] at hw ⊢
    rcases hw with ⟨pref, suffix, hpref, hsuffix, hword⟩
    have hsuffixShape :
        suffix ∈ orderedABCCShapeLanguage :=
      language_concat_right_empty_only_mem hepsOnly hsuffix
    have hshape : word ∈ orderedABCCShapeLanguage := by
      rw [hword, hpref]
      simpa [Word.Symbol] using orderedABCCShape_cons_c hsuffixShape
    exact language_concat_right_empty_mem heps2Mem hshape
  · simp [CFG.FormLanguage, orderedABCSymbolLanguage, orderedN,
      ggNonterminal] at hw ⊢
    rw [hw]
    exact language_concat_right_empty_mem hepsMem orderedABCCShape_empty

theorem orderedABCGrammar_generated_has_ordered_shape
    {word : Word EqualCountTerminal}
    (h : word ∈ GeneralGrammar.GeneratedLanguage OrderedABCGrammar) :
    word ∈ orderedABCShapeLanguage := by
  have hderives :
      GeneralGrammar.Derives OrderedABCGrammar [orderedN OrderedABCNT.start]
        (SententialForm.terminalWord word) := by
    simpa [GeneralGrammar.GeneratedLanguage, OrderedABCGrammar, orderedN,
      ggNonterminal] using h
  have hs := general_derives_sound_for_symbol_language
    orderedABCSymbolLanguage (by intro token; rfl)
    (by
      intro lhs rhs hprod word hw
      exact orderedABC_production_shape_sound hprod word hw)
    hderives
  simp [CFG.FormLanguage, orderedABCSymbolLanguage, orderedN, ggNonterminal]
    at hs
  exact language_concat_right_empty_only_mem
    (fun suffix hsuffix => hsuffix) hs

theorem orderedABC_generated_only_language
    {word : Word EqualCountTerminal}
    (h : word ∈ GeneralGrammar.GeneratedLanguage OrderedABCGrammar) :
    word ∈ orderedABCLanguage := by
  exact orderedABCShape_equal_counts_language
    (orderedABCGrammar_generated_has_ordered_shape h)
    (orderedABCGrammar_generated_has_equal_terminal_counts h)

theorem orderedABC_generated_language_exact
    (word : Word EqualCountTerminal) :
    word ∈ GeneralGrammar.GeneratedLanguage OrderedABCGrammar <->
      word ∈ orderedABCLanguage := by
  constructor
  · exact orderedABC_generated_only_language
  · exact orderedABC_language_subset_generated

theorem orderedABCLanguage_finite_production_generated :
    FiniteProductionGeneralLanguage orderedABCLanguage := by
  exists OrderedABCNT
  exists OrderedABCGrammar
  constructor
  · exact orderedABCGrammar_has_finite_productions
  · intro word
    exact orderedABC_generated_language_exact word

def aabbccWord : Word EqualCountTerminal :=
  [EqualCountTerminal.a, EqualCountTerminal.a, EqualCountTerminal.b,
    EqualCountTerminal.b, EqualCountTerminal.c, EqualCountTerminal.c]

/-!
The concrete {lit}`aabbcc` derivation is a compact worked example of the ordered
grammar: start, grow two marker rows, sort them, and convert them into terminals.
-/

theorem orderedABCGrammar_generates_aabbcc :
    aabbccWord ∈ GeneralGrammar.GeneratedLanguage OrderedABCGrammar := by
  let S := orderedN OrderedABCNT.start
  let A := orderedN OrderedABCNT.markA
  let B := orderedN OrderedABCNT.markB
  let C := orderedN OrderedABCNT.markC
  let X := orderedN OrderedABCNT.x
  let Y := orderedN OrderedABCNT.y
  let Z := orderedN OrderedABCNT.z
  let a := orderedT EqualCountTerminal.a
  let b := orderedT EqualCountTerminal.b
  let c := orderedT EqualCountTerminal.c
  have h1 : GeneralGrammar.Yields OrderedABCGrammar [S] [S, A, B, C] := by
    simpa [S, A, B, C] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.grow [] []
  have h2 :
      GeneralGrammar.Yields OrderedABCGrammar [S, A, B, C]
        [S, A, B, C, A, B, C] := by
    simpa [S, A, B, C] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.grow [] [A, B, C]
  have h3 :
      GeneralGrammar.Yields OrderedABCGrammar [S, A, B, C, A, B, C]
        [X, A, B, C, A, B, C] := by
    simpa [S, A, B, C, X] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.startX [] [A, B, C, A, B, C]
  have h4 :
      GeneralGrammar.Yields OrderedABCGrammar [X, A, B, C, A, B, C]
        [X, A, B, A, C, B, C] := by
    simpa [X, A, B, C] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.swapCA [X, A, B] [B, C]
  have h5 :
      GeneralGrammar.Yields OrderedABCGrammar [X, A, B, A, C, B, C]
        [X, A, A, B, C, B, C] := by
    simpa [X, A, B, C] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.swapBA [X, A] [C, B, C]
  have h6 :
      GeneralGrammar.Yields OrderedABCGrammar [X, A, A, B, C, B, C]
        [X, A, A, B, B, C, C] := by
    simpa [X, A, B, C] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.swapCB [X, A, A, B] [C]
  have h7 :
      GeneralGrammar.Yields OrderedABCGrammar [X, A, A, B, B, C, C]
        [a, X, A, B, B, C, C] := by
    simpa [X, A, B, C, a] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.convertXA [] [A, B, B, C, C]
  have h8 :
      GeneralGrammar.Yields OrderedABCGrammar [a, X, A, B, B, C, C]
        [a, a, X, B, B, C, C] := by
    simpa [X, A, B, C, a] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.convertXA [a] [B, B, C, C]
  have h9 :
      GeneralGrammar.Yields OrderedABCGrammar [a, a, X, B, B, C, C]
        [a, a, Y, B, B, C, C] := by
    simpa [X, Y, B, C, a] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.xToY [a, a] [B, B, C, C]
  have h10 :
      GeneralGrammar.Yields OrderedABCGrammar [a, a, Y, B, B, C, C]
        [a, a, b, Y, B, C, C] := by
    simpa [Y, B, C, a, b] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.convertYB [a, a] [B, C, C]
  have h11 :
      GeneralGrammar.Yields OrderedABCGrammar [a, a, b, Y, B, C, C]
        [a, a, b, b, Y, C, C] := by
    simpa [Y, B, C, a, b] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.convertYB [a, a, b] [C, C]
  have h12 :
      GeneralGrammar.Yields OrderedABCGrammar [a, a, b, b, Y, C, C]
        [a, a, b, b, Z, C, C] := by
    simpa [Y, Z, C, a, b] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.yToZ [a, a, b, b] [C, C]
  have h13 :
      GeneralGrammar.Yields OrderedABCGrammar [a, a, b, b, Z, C, C]
        [a, a, b, b, c, Z, C] := by
    simpa [Z, C, a, b, c] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.convertZC [a, a, b, b] [C]
  have h14 :
      GeneralGrammar.Yields OrderedABCGrammar [a, a, b, b, c, Z, C]
        [a, a, b, b, c, c, Z] := by
    simpa [Z, C, a, b, c] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.convertZC [a, a, b, b, c] []
  have h15 :
      GeneralGrammar.Yields OrderedABCGrammar [a, a, b, b, c, c, Z]
        [a, a, b, b, c, c] := by
    simpa [Z, a, b, c] using
      general_yields_of_production (G := OrderedABCGrammar)
        OrderedABCProduces.finish [a, a, b, b, c, c] []
  have hderives :
      GeneralGrammar.Derives OrderedABCGrammar [S] [a, a, b, b, c, c] :=
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
                                  (GeneralGrammar.Derives.refl
                                    [a, a, b, b, c, c])))))))))))))))
  simpa [GeneralGrammar.GeneratedLanguage, OrderedABCGrammar, aabbccWord,
    SententialForm.terminalWord, S, a, b, c] using hderives


end Section06
end Chapter04
end Book
end FoC
