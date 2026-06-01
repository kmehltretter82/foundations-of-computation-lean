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

-- Book: Chapter 5, Section 5.3, proof wrapper for non-acceptability by contradiction.
theorem not_acceptable_of_contradiction {L : Language alpha}
    (h : TuringAcceptable L -> False) : NonTuringAcceptableLanguage L :=
  Computability.not_acceptable_of_diagonal_contradiction h

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
