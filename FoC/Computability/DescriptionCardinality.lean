import FoC.Computability.DescriptionCodeValidity
import FoC.Computability.DescriptionCodeLanguages
import FoC.Foundation.CountableImage
import FoC.Languages.WordCountable

set_option doc.verso true

/-!
# Cardinality of finite-description languages

This module counts the exact class used by the repaired Chapter 5 theorem:
complete codes of well-formed finite
{name (full := FoC.Computability.MachineDescription)}`MachineDescription`s and the code
languages recognized by those descriptions.  It does not make a claim about
the unrestricted semantic {lit}`TuringAcceptable` class.
-/

namespace FoC
namespace Computability
namespace DescriptionCardinality

open Foundation
open Languages

/-- Complete words that decode to well-formed finite descriptions. -/
def ValidDescriptionCodes : FSet (Word MachineCodeSymbol) :=
  fun code => MachineDescription.DescriptionCodeValid code

/-- The set of well-formed finite transition-table descriptions. -/
def WellFormedDescriptions : FSet MachineDescription :=
  fun D => D.WellFormed

/-- The exact image of well-formed finite descriptions under their canonical
encoded-input language semantics. -/
def FiniteDescriptionRecognizedLanguages :
    FSet (Language MachineCodeSymbol) :=
  Fn.Image MachineDescription.EncodedInputLanguage WellFormedDescriptions

/-- All raw finite descriptions form a countable type, witnessed by their
injective canonical code words. -/
theorem machineDescriptions_countable :
    FSet.Countable (FSet.Univ : FSet MachineDescription) := by
  rcases Word.encodableByNat MachineCodeSymbol.finite with
    ⟨encodeWord, hencodeWord⟩
  apply Countability.countable_univ_of_encodableByNat
  refine ⟨fun D => encodeWord (MachineDescription.encodeDescription D), ?_⟩
  intro D E hcode
  have hencoded : MachineDescription.encodeDescription D =
      MachineDescription.encodeDescription E := hencodeWord hcode
  have hdecoded : some D = some E := by
    simpa only [MachineDescription.decodeDescription_encodeDescription] using
      congrArg MachineDescription.decodeDescription hencoded
  exact Option.some.inj hdecoded

/-- Valid complete finite-description codes are countable. -/
theorem validDescriptionCodes_countable :
    FSet.Countable ValidDescriptionCodes :=
  FSet.countable_subset_classical
    (fun _code _hvalid => True.intro)
    (Word.univ_countable MachineCodeSymbol.finite)

/-- Well-formed finite descriptions are a countable subset of all raw finite
descriptions. -/
theorem wellFormedDescriptions_countable :
    FSet.Countable WellFormedDescriptions :=
  FSet.countable_subset_classical
    (fun _D _hwell => True.intro)
    machineDescriptions_countable

/-- Languages recognized by well-formed finite descriptions form a countable
image. -/
theorem finiteDescriptionRecognizedLanguages_countable :
    FSet.Countable FiniteDescriptionRecognizedLanguages :=
  FSet.countable_image wellFormedDescriptions_countable
    MachineDescription.EncodedInputLanguage

/-- Membership in the counted image is exactly finite-description code-language
recognizability. -/
theorem mem_finiteDescriptionRecognizedLanguages_iff
    (L : Language MachineCodeSymbol) :
    L ∈ FiniteDescriptionRecognizedLanguages <->
      DescriptionRecognizableCodeLanguage L := by
  constructor
  · rintro ⟨D, hwell, rfl⟩
    exact ⟨D, hwell, fun _input => Iff.rfl⟩
  · rintro ⟨D, hwell, hlanguage⟩
    refine ⟨D, hwell, ?_⟩
    funext input
    exact propext (hlanguage input)

/-- An uncountable universe of code languages contains a language outside the
countable finite-description image. -/
theorem exists_language_not_descriptionRecognizable_of_uncountable
    (huncountable :
      FSet.Uncountable (FSet.Univ : FSet (Language MachineCodeSymbol))) :
    exists L : Language MachineCodeSymbol,
      ¬ DescriptionRecognizableCodeLanguage L := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hall : forall L : Language MachineCodeSymbol,
      DescriptionRecognizableCodeLanguage L := by
    intro L
    apply Classical.byContradiction
    intro hnot
    exact hnone ⟨L, hnot⟩
  have hequal : FSet.Equal FiniteDescriptionRecognizedLanguages
      (FSet.Univ : FSet (Language MachineCodeSymbol)) := by
    intro L
    constructor
    · intro _hrecognized
      exact True.intro
    · intro _huniv
      exact (mem_finiteDescriptionRecognizedLanguages_iff L).2 (hall L)
  have hcountable :
      FSet.Countable (FSet.Univ : FSet (Language MachineCodeSymbol)) :=
    FSet.countable_of_equal hequal
      finiteDescriptionRecognizedLanguages_countable
  exact huncountable hcountable

/-- There is a language over the concrete finite code alphabet that no
well-formed finite description recognizes. -/
theorem exists_language_not_descriptionRecognizable :
    exists L : Language MachineCodeSymbol,
      ¬ DescriptionRecognizableCodeLanguage L := by
  apply exists_language_not_descriptionRecognizable_of_uncountable
  · change FSet.Uncountable
      (FSet.Univ : FSet (FSet (Word MachineCodeSymbol)))
    exact FSet.univ_fset_uncountable_of_countablyInfinite
      (Word.univ_countablyInfinite MachineCodeSymbol.finite
        MachineCodeSymbol.header)

end DescriptionCardinality
end Computability
end FoC
