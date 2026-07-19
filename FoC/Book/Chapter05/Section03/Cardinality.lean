import FoC.Book.Chapter05.Section03.BasicPart1
import FoC.Book.Chapter03.Section01
import FoC.Computability.DescriptionCardinality

set_option doc.verso true

/-!
# Section 5.3: Cardinality of finite-machine languages

The exact finite-description class used by this section is countable, while
the collection of all languages over the finite machine-code alphabet is
uncountable.  Hence some language has no well-formed finite-description
recognizer.

## Enumeration fidelity

This formalization chooses the **direct-code endpoint** from the Section 5.3
improvement plan.  The canonical theorem ranges over complete finite
description codes directly.  It does not define a duplicate-free unary
enumeration {lit}`T_n`, does not construct the printed machine {lit}`G`, and
does not claim a proved equivalence with that presentation.  A literal
{lit}`T_n`/{lit}`G` endpoint would require its own finite-machine campaign.
-/

namespace FoC
namespace Book
namespace Chapter05
namespace Section03

open Languages
open Computability

/-- Complete valid finite-description codes form a countable set. -/
theorem concrete_valid_description_codes_countable :
    Foundation.FSet.Countable
      DescriptionCardinality.ValidDescriptionCodes :=
  DescriptionCardinality.validDescriptionCodes_countable

/-- The exact image of languages recognized by well-formed finite descriptions
is countable. -/
theorem concrete_finite_description_languages_countable :
    Foundation.FSet.Countable
      DescriptionCardinality.FiniteDescriptionRecognizedLanguages :=
  DescriptionCardinality.finiteDescriptionRecognizedLanguages_countable

/-- Chapter 3's Cantor theorem instantiated at the finite machine-code
alphabet. -/
theorem concrete_code_languages_uncountable :
    Foundation.FSet.Uncountable
      (Foundation.FSet.Univ :
        Foundation.FSet (Language ConcreteMachineCodeSymbol)) :=
  Chapter03.Section01.languages_over_finite_nonempty_alphabet_uncountable
    MachineCodeSymbol.finite MachineCodeSymbol.header

/-- Some language over the concrete finite code alphabet is not recognized by
any well-formed finite description. -/
theorem exists_concrete_language_not_recognizable_by_finite_description :
    exists L : Language ConcreteMachineCodeSymbol,
      ¬ RecognizableCodeLanguage L := by
  change exists L : Language MachineCodeSymbol,
    ¬ DescriptionRecognizableCodeLanguage L
  exact
    DescriptionCardinality.exists_language_not_descriptionRecognizable_of_uncountable
      concrete_code_languages_uncountable

end Section03
end Chapter05
end Book
end FoC
