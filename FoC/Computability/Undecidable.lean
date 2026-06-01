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

def DiagonalLanguage (acceptsSelf : Word code -> Prop) : Language code :=
  fun w => ¬ acceptsSelf w

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

theorem not_acceptable_of_diagonal_contradiction {L : Language alpha}
    (h : TuringAcceptable L -> False) : NonAcceptableLanguage L := by
  intro hL
  exact h hL

end Computability
end FoC
