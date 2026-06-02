import FoC.Computability.Undecidable

namespace FoC
namespace Book
namespace Chapter05
namespace Section03

/-!
Book: Chapter 5, Section 5.3, The Limits of Computation.
-/

open Languages
open Computability

-- Book: Chapter 5, Section 5.3, non-computable string functions.
def NonComputableStringFunction (f : Word input -> Word output) : Prop :=
  NonComputableFunction f

-- Book: Chapter 5, Section 5.3, non-acceptable languages.
def NonTuringAcceptableLanguage (L : Language alpha) : Prop :=
  NonAcceptableLanguage L

-- Book: Chapter 5, Section 5.3, undecidable languages.
def UndecidableTuringLanguage (L : Language alpha) : Prop :=
  UndecidableLanguage L

-- Book: Chapter 5, Section 5.3, abstract reductions preserving
-- decidability.
def TuringDecidableReduction
    (L : Language input) (K : Language output) : Prop :=
  DecidableReduction L K

-- Book: Chapter 5, Section 5.3, abstract reductions preserving
-- acceptability.
def TuringAcceptableReduction
    (L : Language input) (K : Language output) : Prop :=
  AcceptableReduction L K

-- Book: Chapter 5, Section 5.3, diagonal language vocabulary.
def TuringDiagonalLanguage (acceptsSelf : Word code -> Prop) : Language code :=
  DiagonalLanguage acceptsSelf

-- Book: Chapter 5, Section 5.3, a decoded machine row recognizes a language.
def TuringDecoderRecognizes
    (decodeAccepts : Word code -> Word code -> Prop)
    (machine : Word code) (L : Language code) : Prop :=
  DecoderRecognizes decodeAccepts machine L

-- Book: Chapter 5, Section 5.3, the diagonal language associated with a
-- decoder table.
def TuringSelfDiagonalLanguage
    (decodeAccepts : Word code -> Word code -> Prop) : Language code :=
  SelfDiagonalLanguage decodeAccepts

-- Book: Chapter 5, Section 5.3, statement shape for a decoder table that has
-- a row for every Turing-acceptable language.
def TuringDecoderUniversalForAcceptableLanguages
    (decodeAccepts : Word code -> Word code -> Prop) : Prop :=
  DecoderUniversalForAcceptableLanguages decodeAccepts

-- Book: Chapter 5, Section 5.3, statement shape for a decoder table that has
-- a row for every language.
def TuringDecoderUniversalForAllLanguages
    (decodeAccepts : Word code -> Word code -> Prop) : Prop :=
  DecoderUniversalForAllLanguages decodeAccepts

-- Book: Chapter 5, Section 5.3, halting-problem vocabulary.
def TuringHaltingProblem (haltsOnCodeInput : Word code -> Word code -> Prop) :
    Language code :=
  HaltingProblem haltsOnCodeInput

-- Book: Chapter 5, Section 5.3, universal-machine specification shape.
def UniversalTuringMachineSpec
    (universal : TuringMachine symbol state)
    (decodeAccepts : Word symbol -> Word symbol -> Prop) : Prop :=
  UniversalMachineSpec universal decodeAccepts

-- Book: Chapter 5, Section 5.3, proof wrapper for undecidability by negating decidability.
theorem undecidable_of_not_decidable {L : Language alpha}
    (h : ¬ TuringDecidable L) : UndecidableTuringLanguage L :=
  Computability.undecidable_of_not_decidable h

-- Book: Chapter 5, Section 5.3, undecidability is extensional.
theorem undecidable_language_of_equal {L K : Language alpha}
    (h : UndecidableTuringLanguage L) (hEq : Language.Equal L K) :
    UndecidableTuringLanguage K :=
  Computability.undecidable_of_equal h hEq

-- Book: Chapter 5, Section 5.3, undecidability passes to complements.
theorem undecidable_language_complement {L : Language alpha}
    (h : UndecidableTuringLanguage L) :
    UndecidableTuringLanguage (Language.Compl L) :=
  Computability.undecidable_complement h

-- Book: Chapter 5, Section 5.3, if the complement is undecidable, then so is
-- the original language.
theorem undecidable_language_of_undecidable_complement {L : Language alpha}
    (h : UndecidableTuringLanguage (Language.Compl L)) :
    UndecidableTuringLanguage L :=
  Computability.undecidable_of_complement h

-- Book: Chapter 5, Section 5.3, undecidability is equivalent for a language
-- and its complement.
theorem undecidable_language_complement_iff {L : Language alpha} :
    UndecidableTuringLanguage (Language.Compl L) <-> UndecidableTuringLanguage L :=
  Computability.undecidable_complement_iff

-- Book: Chapter 5, Section 5.3, decidable reductions are reflexive.
theorem decidable_reduction_refl (L : Language alpha) :
    TuringDecidableReduction L L :=
  Computability.decidableReduction_refl L

-- Book: Chapter 5, Section 5.3, decidable reductions compose.
theorem decidable_reduction_trans
    {L : Language alpha} {K : Language beta} {H : Language gamma}
    (hLK : TuringDecidableReduction L K)
    (hKH : TuringDecidableReduction K H) :
    TuringDecidableReduction L H :=
  Computability.decidableReduction_trans hLK hKH

-- Book: Chapter 5, Section 5.3, undecidability transfers forward along a
-- decidable reduction.
theorem undecidable_of_decidable_reduction
    {L : Language alpha} {K : Language beta}
    (hred : TuringDecidableReduction L K)
    (hL : UndecidableTuringLanguage L) :
    UndecidableTuringLanguage K :=
  Computability.undecidable_of_decidableReduction hred hL

-- Book: Chapter 5, Section 5.3, complementing both languages preserves an
-- abstract decidable reduction.
theorem decidable_reduction_complement
    {L : Language alpha} {K : Language beta}
    (h : TuringDecidableReduction L K) :
    TuringDecidableReduction (Language.Compl L) (Language.Compl K) :=
  Computability.decidableReduction_complement h

-- Book: Chapter 5, Section 5.3, proof wrapper for non-acceptability by contradiction.
theorem not_acceptable_of_contradiction {L : Language alpha}
    (h : TuringAcceptable L -> False) : NonTuringAcceptableLanguage L :=
  Computability.not_acceptable_of_diagonal_contradiction h

-- Book: Chapter 5, Section 5.3, non-acceptability is extensional.
theorem non_acceptable_language_of_equal {L K : Language alpha}
    (h : NonTuringAcceptableLanguage L) (hEq : Language.Equal L K) :
    NonTuringAcceptableLanguage K :=
  Computability.not_acceptable_of_equal h hEq

-- Book: Chapter 5, Section 5.3, acceptable reductions are reflexive.
theorem acceptable_reduction_refl (L : Language alpha) :
    TuringAcceptableReduction L L :=
  Computability.acceptableReduction_refl L

-- Book: Chapter 5, Section 5.3, acceptable reductions compose.
theorem acceptable_reduction_trans
    {L : Language alpha} {K : Language beta} {H : Language gamma}
    (hLK : TuringAcceptableReduction L K)
    (hKH : TuringAcceptableReduction K H) :
    TuringAcceptableReduction L H :=
  Computability.acceptableReduction_trans hLK hKH

-- Book: Chapter 5, Section 5.3, non-acceptability transfers forward along an
-- acceptable reduction.
theorem non_acceptable_of_acceptable_reduction
    {L : Language alpha} {K : Language beta}
    (hred : TuringAcceptableReduction L K)
    (hL : NonTuringAcceptableLanguage L) :
    NonTuringAcceptableLanguage K :=
  Computability.not_acceptable_of_acceptableReduction hred hL

-- Book: Chapter 5, Section 5.3, non-computability is extensional for
-- pointwise equal string functions.
theorem non_computable_function_of_pointwise_equal
    {f g : Word input -> Word output}
    (h : NonComputableStringFunction f) (hfg : forall w, f w = g w) :
    NonComputableStringFunction g :=
  Computability.nonComputableFunction_of_pointwise_equal h hfg

-- Book: Chapter 5, Section 5.3, decoded-row recognition is extensional in
-- the recognized language.
theorem decoder_recognizes_of_equal
    {decodeAccepts : Word code -> Word code -> Prop}
    {machine : Word code} {L K : Language code}
    (h : TuringDecoderRecognizes decodeAccepts machine L)
    (hEq : Language.Equal L K) :
    TuringDecoderRecognizes decodeAccepts machine K :=
  Computability.decoderRecognizes_of_equal h hEq

-- Book: Chapter 5, Section 5.3, abstract diagonal contradiction core.
theorem diagonal_language_not_self_recognized (acceptsSelf : Word code -> Prop) :
    ¬ forall w : Word code,
      acceptsSelf w <-> w ∈ TuringDiagonalLanguage acceptsSelf :=
  Computability.diagonal_not_self_recognized acceptsSelf

-- Book: Chapter 5, Section 5.3, no decoded row recognizes the decoder's own
-- diagonal language.
theorem decoder_cannot_recognize_self_diagonal
    (decodeAccepts : Word code -> Word code -> Prop) :
    ¬ exists machine : Word code,
      TuringDecoderRecognizes decodeAccepts machine
        (TuringSelfDiagonalLanguage decodeAccepts) :=
  Computability.decoder_cannot_recognize_self_diagonal decodeAccepts

-- Book: Chapter 5, Section 5.3, no individual decoded row recognizes the
-- decoder's own diagonal language.
theorem decoder_row_not_self_diagonal
    (decodeAccepts : Word code -> Word code -> Prop)
    (machine : Word code) :
    ¬ TuringDecoderRecognizes decodeAccepts machine
      (TuringSelfDiagonalLanguage decodeAccepts) :=
  Computability.decoder_row_not_self_diagonal decodeAccepts machine

-- Book: Chapter 5, Section 5.3, the decoder's own diagonal language is a
-- concrete language missing from its rows.
theorem self_diagonal_missing_from_decoder_rows
    (decodeAccepts : Word code -> Word code -> Prop) :
    exists L : Language code,
      ¬ exists machine : Word code,
        TuringDecoderRecognizes decodeAccepts machine L :=
  Computability.self_diagonal_missing_from_decoder_rows decodeAccepts

-- Book: Chapter 5, Section 5.3, no decoder table can contain a row for every
-- language.
theorem decoder_not_universal_for_all_languages
    (decodeAccepts : Word code -> Word code -> Prop) :
    ¬ TuringDecoderUniversalForAllLanguages decodeAccepts :=
  Computability.decoder_not_universal_for_all_languages decodeAccepts

-- Book: Chapter 5, Section 5.3, if a decoder table had a row for every
-- acceptable language, then its own diagonal language would be non-acceptable.
theorem self_diagonal_not_acceptable_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    NonTuringAcceptableLanguage
      (TuringSelfDiagonalLanguage decodeAccepts) :=
  Computability.self_diagonal_not_acceptable_if_decoder_universal huniv

-- Book: Chapter 5, Section 5.3, a decoder table universal for acceptable
-- languages yields an explicit non-acceptable language.
theorem exists_nonacceptable_language_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    exists L : Language code, NonTuringAcceptableLanguage L :=
  Computability.exists_nonacceptable_language_if_decoder_universal huniv

-- Book: Chapter 5, Section 5.3, a halting pair belongs to the abstract
-- halting-problem language.
theorem halting_problem_contains_encoded_halting_pair
    (haltsOnCodeInput : Word code -> Word code -> Prop)
    {machine input : Word code}
    (hhalts : haltsOnCodeInput machine input) :
    Languages.Word.Concat machine input ∈
      TuringHaltingProblem haltsOnCodeInput :=
  Computability.haltingProblem_contains_encoded_halting_pair
    haltsOnCodeInput hhalts

/-!
The section's universal-machine and diagonalization theorems require a concrete
encoding of machines as strings.  This module records the formal statement
vocabulary without adding an unproved universal-machine assumption.
-/

end Section03
end Chapter05
end Book
end FoC
