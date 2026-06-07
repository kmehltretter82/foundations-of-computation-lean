import FoC.Computability.Enumerable

set_option doc.verso true

/-!
# Undecidability

## Diagonal and halting vocabularies

The final section of Chapter 5 uses diagonal languages, halting-problem style
predicates, reductions, and noncomputability statements.  This module keeps that
vocabulary separate from the concrete Turing-machine model.

## Book coordinates

Used by:
- Chapter 5, Section 5.3: limits of computation, diagonal languages, and
  halting-problem style statements.
-/

namespace FoC
namespace Computability

open Languages

/-!
# Negative computability predicates

The chapter-facing undecidability statements use explicit negations of
computability, acceptability, and decidability.
-/

def NonComputableFunction (f : Word input -> Word output) : Prop :=
  ¬ TuringComputable f

def NonAcceptableLanguage (L : Language alpha) : Prop :=
  ¬ TuringAcceptable L

def UndecidableLanguage (L : Language alpha) : Prop :=
  ¬ TuringDecidable L

def DecidableReduction (L : Language input) (K : Language output) : Prop :=
  TuringDecidable K -> TuringDecidable L

def AcceptableReduction (L : Language input) (K : Language output) : Prop :=
  TuringAcceptable K -> TuringAcceptable L

/-!
# Diagonal languages

Diagonal languages are parameterized by an abstract decoding relation so the
formal statements can separate the logical argument from any concrete machine
encoding.
-/

def DiagonalLanguage (acceptsSelf : Word code -> Prop) : Language code :=
  fun w => ¬ acceptsSelf w

def DecoderRecognizes
    (decodeAccepts : Word code -> Word code -> Prop)
    (machine : Word code) (L : Language code) : Prop :=
  forall input : Word code, decodeAccepts machine input <-> input ∈ L

def SelfDiagonalLanguage
    (decodeAccepts : Word code -> Word code -> Prop) : Language code :=
  DiagonalLanguage (fun w => decodeAccepts w w)

def DecoderUniversalForAcceptableLanguages
    (decodeAccepts : Word code -> Word code -> Prop) : Prop :=
  forall L : Language code, TuringAcceptable L ->
    exists machine : Word code, DecoderRecognizes decodeAccepts machine L

def DecoderUniversalForAllLanguages
    (decodeAccepts : Word code -> Word code -> Prop) : Prop :=
  forall L : Language code,
    exists machine : Word code, DecoderRecognizes decodeAccepts machine L

/-!
# Halting-problem vocabularies

The halting-problem predicates are stated both with concatenated encodings and
with an explicit pair encoder.
-/

def HaltingProblem (haltsOnCodeInput : Word code -> Word code -> Prop) :
    Language code :=
  fun encodedPair => exists machine input : Word code,
    encodedPair = Languages.Word.Concat machine input ∧ haltsOnCodeInput machine input

def PairHaltingProblem
    (encodePair : Word code -> Word code -> Word pairSymbol)
    (haltsOnCodeInput : Word code -> Word code -> Prop) :
    Language pairSymbol :=
  fun encodedPair => exists machine input : Word code,
    encodedPair = encodePair machine input ∧ haltsOnCodeInput machine input

def SelfHaltingLanguage
    (haltsOnCodeInput : Word code -> Word code -> Prop) : Language code :=
  fun machine => haltsOnCodeInput machine machine

def SelfHaltingPairLanguage
    (encodePair : Word code -> Word code -> Word pairSymbol)
    (haltsOnCodeInput : Word code -> Word code -> Prop) :
    Language pairSymbol :=
  fun encodedPair => exists machine : Word code,
    encodedPair = encodePair machine machine ∧
      haltsOnCodeInput machine machine

def DiagonalPairDecidablePreimagePrinciple
    (encodePair : Word code -> Word code -> Word pairSymbol) : Prop :=
  forall haltsOnCodeInput : Word code -> Word code -> Prop,
    TuringDecidable (PairHaltingProblem encodePair haltsOnCodeInput) ->
      TuringDecidable (SelfHaltingLanguage haltsOnCodeInput)

def WordPreimageLanguage
    (map : Word input -> Word output)
    (L : Language output) : Language input :=
  fun w => map w ∈ L

def DecidablePreimagePrinciple
    (map : Word input -> Word output) : Prop :=
  forall L : Language output,
    TuringDecidable L -> TuringDecidable (WordPreimageLanguage map L)

def ComputableMapDecidablePreimagePrinciple
    (input : Type u) (output : Type v) : Prop :=
  forall map : Word input -> Word output,
    TuringComputable map -> DecidablePreimagePrinciple map

theorem decidablePreimagePrinciple_vacuous_exact_output
    (map : Word input -> Word output) :
    DecidablePreimagePrinciple map := by
  intro L hdecidable
  exact False.elim (not_turingDecidable_exact_output L hdecidable)

def PairEncodingInjective
    (encodePair : Word code -> Word code -> Word pairSymbol) : Prop :=
  forall a b c d : Word code,
    encodePair a b = encodePair c d -> a = c ∧ b = d

def DiagonalPairMap
    (encodePair : Word code -> Word code -> Word pairSymbol) :
    Word code -> Word pairSymbol :=
  fun machine => encodePair machine machine

def UniversalMachineSpec
    (universal : TuringMachine symbol state)
  (decodeAccepts : Word symbol -> Word symbol -> Prop) : Prop :=
  forall machine input : Word symbol,
    TuringMachine.HaltsOnInput universal (Languages.Word.Concat machine input) <->
      decodeAccepts machine input

theorem decidablePreimagePrinciple_of_computableMapPrinciple
    {map : Word input -> Word output}
    (hpreimage : ComputableMapDecidablePreimagePrinciple input output)
    (hcomputable : TuringComputable map) :
    DecidablePreimagePrinciple map :=
  hpreimage map hcomputable

/-!
# Undecidability transport

Undecidability is stable under language equality, complement, and decidable
reductions.
-/

theorem undecidable_of_not_decidable {L : Language alpha}
    (h : ¬ TuringDecidable L) : UndecidableLanguage L :=
  h

theorem undecidable_of_equal {L K : Language alpha}
    (h : UndecidableLanguage L) (hEq : Language.Equal L K) :
    UndecidableLanguage K := by
  intro hK
  exact h (turing_decidable_of_equal hK (Language.equal_symm hEq))

theorem undecidable_complement {L : Language alpha}
    (h : UndecidableLanguage L) : UndecidableLanguage (Language.Compl L) := by
  intro hcomp
  exact h (turing_decidable_of_complement hcomp)

theorem undecidable_of_complement {L : Language alpha}
    (h : UndecidableLanguage (Language.Compl L)) : UndecidableLanguage L := by
  intro hL
  exact h (turing_decidable_complement hL)

theorem undecidable_complement_iff {L : Language alpha} :
    UndecidableLanguage (Language.Compl L) <-> UndecidableLanguage L := by
  constructor
  · exact undecidable_of_complement
  · exact undecidable_complement

theorem decidableReduction_refl (L : Language alpha) :
    DecidableReduction L L :=
  fun hL => hL

theorem decidableReduction_trans
    {L : Language alpha} {K : Language beta} {H : Language gamma}
    (hLK : DecidableReduction L K)
    (hKH : DecidableReduction K H) :
    DecidableReduction L H :=
  fun hH => hLK (hKH hH)

theorem decidableReduction_of_equal_left
    {L L' : Language alpha} {K : Language beta}
    (hEq : Language.Equal L L')
    (h : DecidableReduction L K) :
    DecidableReduction L' K :=
  fun hK => turing_decidable_of_equal (h hK) hEq

theorem decidableReduction_of_equal_right
    {L : Language alpha} {K K' : Language beta}
    (hEq : Language.Equal K K')
    (h : DecidableReduction L K) :
    DecidableReduction L K' :=
  fun hK' => h (turing_decidable_of_equal hK' (Language.equal_symm hEq))

theorem decidableReduction_complement
    {L : Language alpha} {K : Language beta}
    (h : DecidableReduction L K) :
    DecidableReduction (Language.Compl L) (Language.Compl K) :=
  fun hK =>
    turing_decidable_complement
      (h (turing_decidable_of_complement hK))

theorem undecidable_of_decidableReduction
    {L : Language alpha} {K : Language beta}
    (hred : DecidableReduction L K)
    (hL : UndecidableLanguage L) :
    UndecidableLanguage K := by
  intro hK
  exact hL (hred hK)

/-!
# Nonacceptability and acceptable reductions

The corresponding facts for acceptability support diagonal non-recognizability
arguments.
-/

theorem not_acceptable_of_diagonal_contradiction {L : Language alpha}
    (h : TuringAcceptable L -> False) : NonAcceptableLanguage L := by
  intro hL
  exact h hL

theorem not_acceptable_of_equal {L K : Language alpha}
    (h : NonAcceptableLanguage L) (hEq : Language.Equal L K) :
    NonAcceptableLanguage K := by
  intro hK
  exact h (turing_acceptable_of_equal hK (Language.equal_symm hEq))

theorem acceptableReduction_refl (L : Language alpha) :
    AcceptableReduction L L :=
  fun hL => hL

theorem acceptableReduction_trans
    {L : Language alpha} {K : Language beta} {H : Language gamma}
    (hLK : AcceptableReduction L K)
    (hKH : AcceptableReduction K H) :
    AcceptableReduction L H :=
  fun hH => hLK (hKH hH)

theorem acceptableReduction_of_equal_left
    {L L' : Language alpha} {K : Language beta}
    (hEq : Language.Equal L L')
    (h : AcceptableReduction L K) :
    AcceptableReduction L' K :=
  fun hK => turing_acceptable_of_equal (h hK) hEq

theorem acceptableReduction_of_equal_right
    {L : Language alpha} {K K' : Language beta}
    (hEq : Language.Equal K K')
    (h : AcceptableReduction L K) :
    AcceptableReduction L K' :=
  fun hK' => h (turing_acceptable_of_equal hK' (Language.equal_symm hEq))

theorem not_acceptable_of_acceptableReduction
    {L : Language alpha} {K : Language beta}
    (hred : AcceptableReduction L K)
    (hL : NonAcceptableLanguage L) :
    NonAcceptableLanguage K := by
  intro hK
  exact hL (hred hK)

theorem nonComputableFunction_of_pointwise_equal
    {f g : Word input -> Word output}
    (h : NonComputableFunction f) (hfg : forall w, f w = g w) :
    NonComputableFunction g := by
  intro hg
  exact h (turingComputable_of_pointwise_equal hg (fun w => Eq.symm (hfg w)))

/-!
# Diagonal contradiction

The central diagonal argument says no decoder row can recognize its own
self-diagonal language, which yields nonacceptability under a universal decoder
assumption.
-/

theorem decoderRecognizes_of_equal
    {decodeAccepts : Word code -> Word code -> Prop}
    {machine : Word code} {L K : Language code}
    (h : DecoderRecognizes decodeAccepts machine L)
    (hEq : Language.Equal L K) :
    DecoderRecognizes decodeAccepts machine K := by
  intro input
  exact Iff.trans (h input) (hEq input)

theorem diagonal_not_self_recognized (acceptsSelf : Word code -> Prop) :
    ¬ forall w : Word code, acceptsSelf w <-> w ∈ DiagonalLanguage acceptsSelf := by
  intro h
  have hdiag := h (Word.Empty : Word code)
  by_cases hself : acceptsSelf (Word.Empty : Word code)
  · exact (hdiag.mp hself) hself
  · exact hself (hdiag.mpr hself)

theorem decoder_cannot_recognize_self_diagonal
    (decodeAccepts : Word code -> Word code -> Prop) :
    ¬ exists machine : Word code,
      DecoderRecognizes decodeAccepts machine
        (SelfDiagonalLanguage decodeAccepts) := by
  intro h
  cases h with
  | intro machine hmachine =>
      have hdiag := hmachine machine
      have hnot : ¬ decodeAccepts machine machine := by
        intro haccept
        exact (hdiag.mp haccept) haccept
      exact hnot (hdiag.mpr hnot)

theorem decoder_row_not_self_diagonal
    (decodeAccepts : Word code -> Word code -> Prop)
    (machine : Word code) :
    ¬ DecoderRecognizes decodeAccepts machine
      (SelfDiagonalLanguage decodeAccepts) := by
  intro hmachine
  exact decoder_cannot_recognize_self_diagonal decodeAccepts
    (Exists.intro machine hmachine)

theorem self_diagonal_missing_from_decoder_rows
    (decodeAccepts : Word code -> Word code -> Prop) :
    exists L : Language code,
      ¬ exists machine : Word code,
        DecoderRecognizes decodeAccepts machine L :=
  Exists.intro (SelfDiagonalLanguage decodeAccepts)
    (decoder_cannot_recognize_self_diagonal decodeAccepts)

theorem decoder_not_universal_for_all_languages
    (decodeAccepts : Word code -> Word code -> Prop) :
    ¬ DecoderUniversalForAllLanguages decodeAccepts := by
  intro huniv
  exact decoder_cannot_recognize_self_diagonal decodeAccepts
    (huniv (SelfDiagonalLanguage decodeAccepts))

theorem self_diagonal_not_acceptable_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (huniv : DecoderUniversalForAcceptableLanguages decodeAccepts) :
    NonAcceptableLanguage (SelfDiagonalLanguage decodeAccepts) := by
  intro hacceptable
  exact decoder_cannot_recognize_self_diagonal decodeAccepts
    (huniv (SelfDiagonalLanguage decodeAccepts) hacceptable)

theorem exists_nonacceptable_language_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (huniv : DecoderUniversalForAcceptableLanguages decodeAccepts) :
    exists L : Language code, NonAcceptableLanguage L :=
  Exists.intro (SelfDiagonalLanguage decodeAccepts)
    (self_diagonal_not_acceptable_if_decoder_universal huniv)

theorem selfDiagonal_equal_compl_selfHalting
    (haltsOnCodeInput : Word code -> Word code -> Prop) :
    Language.Equal (SelfDiagonalLanguage haltsOnCodeInput)
      (Language.Compl (SelfHaltingLanguage haltsOnCodeInput)) :=
  Language.equal_refl (SelfDiagonalLanguage haltsOnCodeInput)

theorem compl_selfHalting_not_acceptable_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (huniv : DecoderUniversalForAcceptableLanguages decodeAccepts) :
    NonAcceptableLanguage
      (Language.Compl (SelfHaltingLanguage decodeAccepts)) :=
  not_acceptable_of_equal
    (self_diagonal_not_acceptable_if_decoder_universal huniv)
    (selfDiagonal_equal_compl_selfHalting decodeAccepts)

theorem compl_selfHalting_not_recursivelyEnumerable_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (huniv : DecoderUniversalForAcceptableLanguages decodeAccepts) :
    ¬ RecursivelyEnumerable
      (Language.Compl (SelfHaltingLanguage decodeAccepts)) :=
  compl_selfHalting_not_acceptable_if_decoder_universal huniv

theorem selfHalting_not_recursive_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptablePrinciple code)
    (huniv : DecoderUniversalForAcceptableLanguages decodeAccepts) :
    ¬ Recursive (SelfHaltingLanguage decodeAccepts) := by
  intro hrecursive
  exact compl_selfHalting_not_recursivelyEnumerable_if_decoder_universal
    huniv
    (haccept (Language.Compl (SelfHaltingLanguage decodeAccepts))
      (turing_decidable_complement hrecursive))

theorem selfHalting_undecidable_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptablePrinciple code)
    (huniv : DecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableLanguage (SelfHaltingLanguage decodeAccepts) :=
  selfHalting_not_recursive_if_decoder_universal haccept huniv

theorem selfHalting_re_not_recursive_and_compl_not_re_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptablePrinciple code)
    (huniv : DecoderUniversalForAcceptableLanguages decodeAccepts)
    (hself : RecursivelyEnumerable (SelfHaltingLanguage decodeAccepts)) :
    RecursivelyEnumerable (SelfHaltingLanguage decodeAccepts) ∧
      ¬ Recursive (SelfHaltingLanguage decodeAccepts) ∧
        ¬ RecursivelyEnumerable
          (Language.Compl (SelfHaltingLanguage decodeAccepts)) := by
  constructor
  · exact hself
  constructor
  · exact selfHalting_not_recursive_if_decoder_universal haccept huniv
  · exact compl_selfHalting_not_recursivelyEnumerable_if_decoder_universal huniv

/-!
# Halting problem reductions

The remaining lemmas relate self-halting, pair-halting, and concatenated
halting encodings by membership equivalences and preimage reductions.
-/

theorem haltingProblem_mem
    (haltsOnCodeInput : Word code -> Word code -> Prop)
    (encodedPair : Word code) :
    encodedPair ∈ HaltingProblem haltsOnCodeInput <->
      exists machine input : Word code,
        encodedPair = Languages.Word.Concat machine input ∧
          haltsOnCodeInput machine input :=
  Iff.rfl

theorem pairHaltingProblem_mem
    (encodePair : Word code -> Word code -> Word pairSymbol)
    (haltsOnCodeInput : Word code -> Word code -> Prop)
    (encodedPair : Word pairSymbol) :
    encodedPair ∈ PairHaltingProblem encodePair haltsOnCodeInput <->
      exists machine input : Word code,
        encodedPair = encodePair machine input ∧
          haltsOnCodeInput machine input :=
  Iff.rfl

theorem haltingProblem_equal_pairHaltingProblem_concat
    (haltsOnCodeInput : Word code -> Word code -> Prop) :
    Language.Equal (HaltingProblem haltsOnCodeInput)
      (PairHaltingProblem
        (fun machine input : Word code => Languages.Word.Concat machine input)
        haltsOnCodeInput) :=
  Language.equal_refl (HaltingProblem haltsOnCodeInput)

theorem haltingProblem_contains_encoded_halting_pair
    (haltsOnCodeInput : Word code -> Word code -> Prop)
    {machine input : Word code}
    (hhalts : haltsOnCodeInput machine input) :
    Languages.Word.Concat machine input ∈ HaltingProblem haltsOnCodeInput :=
  Exists.intro machine
    (Exists.intro input (And.intro rfl hhalts))

theorem pairHaltingProblem_contains_encoded_halting_pair
    (encodePair : Word code -> Word code -> Word pairSymbol)
    (haltsOnCodeInput : Word code -> Word code -> Prop)
    {machine input : Word code}
    (hhalts : haltsOnCodeInput machine input) :
    encodePair machine input ∈
      PairHaltingProblem encodePair haltsOnCodeInput :=
  Exists.intro machine
    (Exists.intro input (And.intro rfl hhalts))

theorem haltingProblem_pair_elim
    {haltsOnCodeInput : Word code -> Word code -> Prop}
    {encodedPair : Word code}
    (h : encodedPair ∈ HaltingProblem haltsOnCodeInput) :
    exists machine input : Word code,
      encodedPair = Languages.Word.Concat machine input ∧
        haltsOnCodeInput machine input :=
  h

theorem pairHaltingProblem_pair_elim
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {haltsOnCodeInput : Word code -> Word code -> Prop}
    {encodedPair : Word pairSymbol}
    (h : encodedPair ∈ PairHaltingProblem encodePair haltsOnCodeInput) :
    exists machine input : Word code,
      encodedPair = encodePair machine input ∧
        haltsOnCodeInput machine input :=
  h

theorem selfHaltingPairLanguage_mem
    (encodePair : Word code -> Word code -> Word pairSymbol)
    (haltsOnCodeInput : Word code -> Word code -> Prop)
    (encodedPair : Word pairSymbol) :
    encodedPair ∈
        SelfHaltingPairLanguage encodePair haltsOnCodeInput <->
      exists machine : Word code,
        encodedPair = encodePair machine machine ∧
          haltsOnCodeInput machine machine :=
  Iff.rfl

theorem selfHaltingPairLanguage_subset_pairHaltingProblem
    (encodePair : Word code -> Word code -> Word pairSymbol)
    (haltsOnCodeInput : Word code -> Word code -> Prop) :
    Language.Subset
      (SelfHaltingPairLanguage encodePair haltsOnCodeInput)
      (PairHaltingProblem encodePair haltsOnCodeInput) := by
  intro encodedPair hself
  cases hself with
  | intro machine hmachine =>
      exact Exists.intro machine (Exists.intro machine hmachine)

theorem wordPreimageLanguage_mem
    (map : Word input -> Word output)
    (L : Language output)
    (w : Word input) :
    w ∈ WordPreimageLanguage map L <-> map w ∈ L :=
  Iff.rfl

theorem diagonalPairMap_preimage_pairHalting_equal_selfHalting
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {haltsOnCodeInput : Word code -> Word code -> Prop}
    (hinj : PairEncodingInjective encodePair) :
    Language.Equal
      (WordPreimageLanguage
        (DiagonalPairMap encodePair)
        (PairHaltingProblem encodePair haltsOnCodeInput))
      (SelfHaltingLanguage haltsOnCodeInput) := by
  intro machine
  constructor
  · intro hpre
    cases hpre with
    | intro decodedMachine hmachine =>
        cases hmachine with
        | intro input hinput =>
            have hcoords :=
              hinj machine machine decodedMachine input hinput.left
            have hdecoded : decodedMachine = machine := hcoords.left.symm
            have hinputEq : input = machine := hcoords.right.symm
            rw [hdecoded, hinputEq] at hinput
            exact hinput.right
  · intro hself
    exact Exists.intro machine
      (Exists.intro machine (And.intro rfl hself))

theorem diagonalPairDecidablePreimagePrinciple_of_preimage
    {encodePair : Word code -> Word code -> Word pairSymbol}
    (hinj : PairEncodingInjective encodePair)
    (hpreimage :
      DecidablePreimagePrinciple (DiagonalPairMap encodePair)) :
    DiagonalPairDecidablePreimagePrinciple encodePair := by
  intro haltsOnCodeInput hpair
  exact turing_decidable_of_equal
    (hpreimage (PairHaltingProblem encodePair haltsOnCodeInput) hpair)
    (diagonalPairMap_preimage_pairHalting_equal_selfHalting
      (encodePair := encodePair)
      (haltsOnCodeInput := haltsOnCodeInput)
      hinj)

theorem diagonalPairDecidablePreimagePrinciple_of_computableMapPrinciple
    {encodePair : Word code -> Word code -> Word pairSymbol}
    (hinj : PairEncodingInjective encodePair)
    (hpreimage : ComputableMapDecidablePreimagePrinciple code pairSymbol)
    (hcomputable : TuringComputable (DiagonalPairMap encodePair)) :
    DiagonalPairDecidablePreimagePrinciple encodePair :=
  diagonalPairDecidablePreimagePrinciple_of_preimage
    hinj
    (decidablePreimagePrinciple_of_computableMapPrinciple
      hpreimage hcomputable)

theorem haltingProblem_of_pointwise_iff
    {halts1 halts2 : Word code -> Word code -> Prop}
    (hiff : forall machine input : Word code,
      halts1 machine input <-> halts2 machine input) :
    Language.Equal (HaltingProblem halts1) (HaltingProblem halts2) := by
  intro encodedPair
  constructor
  · intro h
    cases h with
    | intro machine hmachine =>
        cases hmachine with
        | intro input hinput =>
            exists machine
            exists input
            exact And.intro hinput.left
              ((hiff machine input).mp hinput.right)
  · intro h
    cases h with
    | intro machine hmachine =>
        cases hmachine with
        | intro input hinput =>
            exists machine
            exists input
            exact And.intro hinput.left
              ((hiff machine input).mpr hinput.right)

theorem pairHaltingProblem_of_pointwise_iff
    (encodePair : Word code -> Word code -> Word pairSymbol)
    {halts1 halts2 : Word code -> Word code -> Prop}
    (hiff : forall machine input : Word code,
      halts1 machine input <-> halts2 machine input) :
    Language.Equal (PairHaltingProblem encodePair halts1)
      (PairHaltingProblem encodePair halts2) := by
  intro encodedPair
  constructor
  · intro h
    cases h with
    | intro machine hmachine =>
        cases hmachine with
        | intro input hinput =>
            exists machine
            exists input
            exact And.intro hinput.left
              ((hiff machine input).mp hinput.right)
  · intro h
    cases h with
    | intro machine hmachine =>
        cases hmachine with
        | intro input hinput =>
            exists machine
            exists input
            exact And.intro hinput.left
              ((hiff machine input).mpr hinput.right)

theorem pairHalting_undecidable_if_selfHalting_undecidable
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {haltsOnCodeInput : Word code -> Word code -> Prop}
    (hdiag :
      DiagonalPairDecidablePreimagePrinciple encodePair)
    (hself :
      UndecidableLanguage (SelfHaltingLanguage haltsOnCodeInput)) :
    UndecidableLanguage
      (PairHaltingProblem encodePair haltsOnCodeInput) := by
  intro hpair
  exact hself (hdiag haltsOnCodeInput hpair)

theorem pairHalting_undecidable_if_selfHalting_undecidable_of_preimage
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {haltsOnCodeInput : Word code -> Word code -> Prop}
    (hinj : PairEncodingInjective encodePair)
    (hpreimage :
      DecidablePreimagePrinciple (DiagonalPairMap encodePair))
    (hself :
      UndecidableLanguage (SelfHaltingLanguage haltsOnCodeInput)) :
    UndecidableLanguage
      (PairHaltingProblem encodePair haltsOnCodeInput) :=
  pairHalting_undecidable_if_selfHalting_undecidable
    (diagonalPairDecidablePreimagePrinciple_of_preimage
      hinj hpreimage)
    hself

theorem pairHalting_undecidable_if_decoder_universal
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptablePrinciple code)
    (hdiag :
      DiagonalPairDecidablePreimagePrinciple encodePair)
    (huniv : DecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableLanguage
      (PairHaltingProblem encodePair decodeAccepts) :=
  pairHalting_undecidable_if_selfHalting_undecidable
    hdiag
    (selfHalting_undecidable_if_decoder_universal haccept huniv)

theorem pairHalting_undecidable_if_decoder_universal_of_preimage
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptablePrinciple code)
    (hinj : PairEncodingInjective encodePair)
    (hpreimage :
      DecidablePreimagePrinciple (DiagonalPairMap encodePair))
    (huniv : DecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableLanguage
      (PairHaltingProblem encodePair decodeAccepts) :=
  pairHalting_undecidable_if_selfHalting_undecidable_of_preimage
    hinj hpreimage
    (selfHalting_undecidable_if_decoder_universal haccept huniv)

theorem universalMachineSpec_pair_halts
    {universal : TuringMachine symbol state}
    {decodeAccepts : Word symbol -> Word symbol -> Prop}
    (hspec : UniversalMachineSpec universal decodeAccepts)
    {machine input : Word symbol}
    (hdecode : decodeAccepts machine input) :
    TuringMachine.HaltsOnInput universal
      (Languages.Word.Concat machine input) :=
  (hspec machine input).mpr hdecode

theorem universalMachineSpec_pair_decode
    {universal : TuringMachine symbol state}
    {decodeAccepts : Word symbol -> Word symbol -> Prop}
    (hspec : UniversalMachineSpec universal decodeAccepts)
    {machine input : Word symbol}
    (hhalts : TuringMachine.HaltsOnInput universal
      (Languages.Word.Concat machine input)) :
    decodeAccepts machine input :=
  (hspec machine input).mp hhalts

end Computability
end FoC
