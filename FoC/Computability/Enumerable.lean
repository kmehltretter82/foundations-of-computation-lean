import FoC.Computability.Recognizable

namespace FoC
namespace Computability

/-!
Enumeration vocabulary for recursively enumerable languages.

Used by:
- Chapter 5, Section 5.2: equivalent descriptions of recursively enumerable
  languages by accepting machines, listing machines, and ranges of computable
  functions.
-/

open Languages

def ListedBy (stream : Nat -> Word alpha) (L : Language alpha) : Prop :=
  Language.Equal (fun w => exists n : Nat, stream n = w) L

def Listable (L : Language alpha) : Prop :=
  exists stream : Nat -> Word alpha, ListedBy stream L

def RangeLanguage (f : Word input -> Word output) : Language output :=
  fun w => exists x : Word input, f x = w

def RangeOfComputableFunction (L : Language output) : Prop :=
  exists input : Type, exists f : Word input -> Word output,
    TuringComputable f ∧ Language.Equal (RangeLanguage f) L

def AcceptableListingEquivalence (L : Language alpha) : Prop :=
  TuringAcceptable L <-> Listable L

def AcceptableRangeEquivalence (L : Language alpha) : Prop :=
  TuringAcceptable L <-> RangeOfComputableFunction L

theorem listedBy_mem {stream : Nat -> Word alpha} {L : Language alpha}
    (h : ListedBy stream L) (w : Word alpha) :
    (exists n : Nat, stream n = w) <-> w ∈ L :=
  h w

theorem listed_word_mem {stream : Nat -> Word alpha} {L : Language alpha}
    (h : ListedBy stream L) (n : Nat) :
    stream n ∈ L :=
  (h (stream n)).mp (Exists.intro n rfl)

theorem range_mem {f : Word input -> Word output} (x : Word input) :
    f x ∈ RangeLanguage f :=
  Exists.intro x rfl

end Computability
end FoC
