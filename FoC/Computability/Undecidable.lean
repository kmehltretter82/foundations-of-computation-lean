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

theorem not_acceptable_of_diagonal_contradiction {L : Language alpha}
    (h : TuringAcceptable L -> False) : NonAcceptableLanguage L := by
  intro hL
  exact h hL

theorem not_acceptable_of_equal {L K : Language alpha}
    (h : NonAcceptableLanguage L) (hEq : Language.Equal L K) :
    NonAcceptableLanguage K := by
  intro hK
  exact h (turing_acceptable_of_equal hK (Language.equal_symm hEq))

theorem nonComputableFunction_of_pointwise_equal
    {f g : Word input -> Word output}
    (h : NonComputableFunction f) (hfg : forall w, f w = g w) :
    NonComputableFunction g := by
  intro hg
  exact h (turingComputable_of_pointwise_equal hg (fun w => Eq.symm (hfg w)))

theorem diagonal_not_self_recognized (acceptsSelf : Word code -> Prop) :
    ¬ forall w : Word code, acceptsSelf w <-> w ∈ DiagonalLanguage acceptsSelf := by
  intro h
  have hdiag := h (Word.Empty : Word code)
  by_cases hself : acceptsSelf (Word.Empty : Word code)
  · exact (hdiag.mp hself) hself
  · exact hself (hdiag.mpr hself)

end Computability
end FoC
