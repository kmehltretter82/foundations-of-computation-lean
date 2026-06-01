import FoC.Computability.Enumerable
import FoC.Grammars.GeneralGrammar

namespace FoC
namespace Book
namespace Chapter05
namespace Section02

/-!
Book: Chapter 5, Section 5.2, Computability.
-/

open Languages
open Computability
open Grammars

-- Book: Chapter 5, Section 5.2, recursively enumerable languages.
def RecursivelyEnumerableLanguage (L : Language alpha) : Prop :=
  RecursivelyEnumerable L

-- Book: Chapter 5, Section 5.2, recursive languages.
def RecursiveLanguage (L : Language alpha) : Prop :=
  Recursive L

-- Book: Chapter 5, Section 5.2, recursive languages are closed under complement.
theorem recursive_language_complement {L : Language alpha}
    (h : RecursiveLanguage L) : RecursiveLanguage (Language.Compl L) :=
  Computability.recursive_complement h

-- Book: Chapter 5, Section 5.2, if the complement is recursive, then so is
-- the original language.
theorem recursive_language_of_recursive_complement {L : Language alpha}
    (h : RecursiveLanguage (Language.Compl L)) : RecursiveLanguage L :=
  Computability.recursive_of_complement h

-- Book: Chapter 5, Section 5.2, recursiveness is equivalent for a language
-- and its complement.
theorem recursive_language_complement_iff {L : Language alpha} :
    RecursiveLanguage (Language.Compl L) <-> RecursiveLanguage L :=
  Computability.recursive_complement_iff

-- Book: Chapter 5, Section 5.2, recursive languages are extensional.
theorem recursive_language_of_equal {L K : Language alpha}
    (h : RecursiveLanguage L) (hEq : Language.Equal L K) :
    RecursiveLanguage K :=
  Computability.recursive_of_equal h hEq

-- Book: Chapter 5, Section 5.2, recursively enumerable languages are
-- extensional.
theorem recursively_enumerable_language_of_equal {L K : Language alpha}
    (h : RecursivelyEnumerableLanguage L) (hEq : Language.Equal L K) :
    RecursivelyEnumerableLanguage K :=
  Computability.recursivelyEnumerable_of_equal h hEq

-- Book: Chapter 5, Section 5.2, languages listed by a stream of words.
def LanguageListedBy (stream : Nat -> Word alpha) (L : Language alpha) : Prop :=
  ListedBy stream L

-- Book: Chapter 5, Section 5.2, listed languages are extensional.
theorem listed_language_of_equal {stream : Nat -> Word alpha}
    {L K : Language alpha}
    (h : LanguageListedBy stream L) (hEq : Language.Equal L K) :
    LanguageListedBy stream K :=
  listedBy_of_equal h hEq

-- Book: Chapter 5, Section 5.2, every listed word belongs to the listed language.
theorem listed_word_in_language {stream : Nat -> Word alpha} {L : Language alpha}
    (h : LanguageListedBy stream L) (n : Nat) :
    stream n ∈ L :=
  listed_word_mem h n

-- Book: Chapter 5, Section 5.2, language-listability vocabulary.
def LanguageListable (L : Language alpha) : Prop :=
  Listable L

-- Book: Chapter 5, Section 5.2, listability is extensional.
theorem listable_language_of_equal {L K : Language alpha}
    (h : LanguageListable L) (hEq : Language.Equal L K) :
    LanguageListable K :=
  listable_of_equal h hEq

-- Book: Chapter 5, Section 5.2, languages as ranges of functions.
def FunctionRangeLanguage (f : Word input -> Word output) : Language output :=
  RangeLanguage f

-- Book: Chapter 5, Section 5.2, a function value is in its range language.
theorem function_value_in_range (f : Word input -> Word output) (x : Word input) :
    f x ∈ FunctionRangeLanguage f :=
  range_mem x

-- Book: Chapter 5, Section 5.2, pointwise equal functions have the same range.
theorem function_range_equal_of_pointwise
    {f g : Word input -> Word output}
    (hfg : forall x, f x = g x) :
    Language.Equal (FunctionRangeLanguage f) (FunctionRangeLanguage g) :=
  rangeLanguage_equal_of_pointwise hfg

-- Book: Chapter 5, Section 5.2, computable-function range descriptions are
-- extensional.
theorem computable_range_language_of_equal {L K : Language output}
    (h : RangeOfComputableFunction L) (hEq : Language.Equal L K) :
    RangeOfComputableFunction K :=
  rangeOfComputableFunction_of_equal h hEq

-- Book: Chapter 5, Section 5.2, equivalence vocabulary for RE languages.
def AcceptableListingEquivalenceStatement (L : Language alpha) : Prop :=
  AcceptableListingEquivalence L

-- Book: Chapter 5, Section 5.2, equivalence vocabulary for computable ranges.
def AcceptableRangeEquivalenceStatement (L : Language alpha) : Prop :=
  AcceptableRangeEquivalence L

-- Book: Chapter 5, Section 5.2, general grammar generated languages.
def GeneralGrammarGeneratedLanguage (G : GeneralGrammar terminal nonterminal) :
    Language terminal :=
  GeneralGrammar.GeneratedLanguage G

-- Book: Chapter 5, Section 5.2, grammar/RE-language equivalence statement.
def GeneralGrammarAcceptabilityEquivalence (L : Language terminal) : Prop :=
  GeneralGrammar.Generated L <-> RecursivelyEnumerable L

/-!
The theorem equating general grammars with recursively enumerable languages is
recorded as an explicit statement shape.  The construction proof is deferred
until the formalization has enough machine-encoding and simulation
infrastructure.
-/

end Section02
end Chapter05
end Book
end FoC
