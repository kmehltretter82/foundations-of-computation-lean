import FoC.Computability.Enumerable

namespace FoC
namespace Computability

/-!
Undecidability vocabulary.

Used by:
- Chapter 5, Section 5.3: limits of computation, diagonal languages, and
  halting-problem style statements.
-/

open Languages

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

def HaltingProblem (haltsOnCodeInput : Word code -> Word code -> Prop) :
    Language code :=
  fun encodedPair => exists machine input : Word code,
    encodedPair = Languages.Word.Concat machine input ∧ haltsOnCodeInput machine input

def UniversalMachineSpec
    (universal : TuringMachine symbol state)
  (decodeAccepts : Word symbol -> Word symbol -> Prop) : Prop :=
  forall machine input : Word symbol,
    TuringMachine.HaltsOnInput universal (Languages.Word.Concat machine input) <->
      decodeAccepts machine input

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

theorem haltingProblem_contains_encoded_halting_pair
    (haltsOnCodeInput : Word code -> Word code -> Prop)
    {machine input : Word code}
    (hhalts : haltsOnCodeInput machine input) :
    Languages.Word.Concat machine input ∈ HaltingProblem haltsOnCodeInput :=
  Exists.intro machine
    (Exists.intro input (And.intro rfl hhalts))

end Computability
end FoC
