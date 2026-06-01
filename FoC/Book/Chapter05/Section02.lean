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

-- Book: Chapter 5, Section 5.2, languages listed by a stream of words.
def LanguageListedBy (stream : Nat -> Word alpha) (L : Language alpha) : Prop :=
  ListedBy stream L

-- Book: Chapter 5, Section 5.2, every listed word belongs to the listed language.
theorem listed_word_in_language {stream : Nat -> Word alpha} {L : Language alpha}
    (h : LanguageListedBy stream L) (n : Nat) :
    stream n ∈ L :=
  listed_word_mem h n

-- Book: Chapter 5, Section 5.2, languages as ranges of functions.
def FunctionRangeLanguage (f : Word input -> Word output) : Language output :=
  RangeLanguage f

-- Book: Chapter 5, Section 5.2, a function value is in its range language.
theorem function_value_in_range (f : Word input -> Word output) (x : Word input) :
    f x ∈ FunctionRangeLanguage f :=
  range_mem x

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
