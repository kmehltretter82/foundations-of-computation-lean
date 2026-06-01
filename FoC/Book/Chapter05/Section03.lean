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

-- Book: Chapter 5, Section 5.3, diagonal language vocabulary.
def TuringDiagonalLanguage (acceptsSelf : Word code -> Prop) : Language code :=
  DiagonalLanguage acceptsSelf

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

-- Book: Chapter 5, Section 5.3, proof wrapper for non-acceptability by contradiction.
theorem not_acceptable_of_contradiction {L : Language alpha}
    (h : TuringAcceptable L -> False) : NonTuringAcceptableLanguage L :=
  Computability.not_acceptable_of_diagonal_contradiction h

-- Book: Chapter 5, Section 5.3, non-acceptability is extensional.
theorem non_acceptable_language_of_equal {L K : Language alpha}
    (h : NonTuringAcceptableLanguage L) (hEq : Language.Equal L K) :
    NonTuringAcceptableLanguage K :=
  Computability.not_acceptable_of_equal h hEq

-- Book: Chapter 5, Section 5.3, non-computability is extensional for
-- pointwise equal string functions.
theorem non_computable_function_of_pointwise_equal
    {f g : Word input -> Word output}
    (h : NonComputableStringFunction f) (hfg : forall w, f w = g w) :
    NonComputableStringFunction g :=
  Computability.nonComputableFunction_of_pointwise_equal h hfg

-- Book: Chapter 5, Section 5.3, abstract diagonal contradiction core.
theorem diagonal_language_not_self_recognized (acceptsSelf : Word code -> Prop) :
    ¬ forall w : Word code,
      acceptsSelf w <-> w ∈ TuringDiagonalLanguage acceptsSelf :=
  Computability.diagonal_not_self_recognized acceptsSelf

/-!
The section's universal-machine and diagonalization theorems require a concrete
encoding of machines as strings.  This module records the formal statement
vocabulary without adding an unproved universal-machine assumption.
-/

end Section03
end Chapter05
end Book
end FoC
