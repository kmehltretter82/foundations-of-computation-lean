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

def UnaryInputWord (n : Nat) : Word Unit :=
  Word.RepeatSymbol () n

def ListingAsUnaryFunction (stream : Nat -> Word output) :
    Word Unit -> Word output :=
  fun w => stream (Word.Length w)

def AcceptableListingEquivalence (L : Language alpha) : Prop :=
  TuringAcceptable L <-> Listable L

def AcceptableRangeEquivalence (L : Language alpha) : Prop :=
  TuringAcceptable L <-> RangeOfComputableFunction L

theorem listedBy_mem {stream : Nat -> Word alpha} {L : Language alpha}
    (h : ListedBy stream L) (w : Word alpha) :
    (exists n : Nat, stream n = w) <-> w ∈ L :=
  h w

theorem listedBy_of_equal {stream : Nat -> Word alpha} {L K : Language alpha}
    (h : ListedBy stream L) (hEq : Language.Equal L K) :
    ListedBy stream K :=
  Language.equal_trans h hEq

theorem listable_of_equal {L K : Language alpha}
    (h : Listable L) (hEq : Language.Equal L K) :
    Listable K := by
  cases h with
  | intro stream hstream =>
      exists stream
      exact listedBy_of_equal hstream hEq

theorem listed_word_mem {stream : Nat -> Word alpha} {L : Language alpha}
    (h : ListedBy stream L) (n : Nat) :
    stream n ∈ L :=
  (h (stream n)).mp (Exists.intro n rfl)

theorem range_mem {f : Word input -> Word output} (x : Word input) :
    f x ∈ RangeLanguage f :=
  Exists.intro x rfl

theorem unaryInputWord_length (n : Nat) :
    Word.Length (UnaryInputWord n) = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change (List.replicate n ()).length = n at ih
      change (List.replicate n ()).length + 1 = n + 1
      rw [ih]

theorem unit_word_eq_unaryInputWord_length (w : Word Unit) :
    w = UnaryInputWord (Word.Length w) := by
  induction w with
  | nil =>
      rfl
  | cons a rest ih =>
      cases a
      change () :: rest = () :: UnaryInputWord (Word.Length rest)
      exact congrArg (fun tail : Word Unit => () :: tail) ih

theorem unaryFunctionRange_listedBy
    (f : Word Unit -> Word output) :
    ListedBy (fun n => f (UnaryInputWord n)) (RangeLanguage f) := by
  intro w
  constructor
  · intro hw
    cases hw with
    | intro n hn =>
        exact Exists.intro (UnaryInputWord n) hn
  · intro hw
    cases hw with
    | intro x hx =>
        exists Word.Length x
        change f (UnaryInputWord (Word.Length x)) = w
        exact Eq.trans
          (congrArg f (unit_word_eq_unaryInputWord_length x).symm) hx

theorem unaryFunctionRange_listable
    (f : Word Unit -> Word output) :
    Listable (RangeLanguage f) :=
  Exists.intro (fun n => f (UnaryInputWord n))
    (unaryFunctionRange_listedBy f)

theorem listedBy_rangeLanguage_listingAsUnaryFunction
    {stream : Nat -> Word output} {L : Language output}
    (h : ListedBy stream L) :
    Language.Equal (RangeLanguage (ListingAsUnaryFunction stream)) L := by
  intro w
  constructor
  · intro hw
    cases hw with
    | intro x hx =>
        exact (h w).mp (Exists.intro (Word.Length x) hx)
  · intro hw
    cases (h w).mpr hw with
    | intro n hn =>
        exists UnaryInputWord n
        change stream (Word.Length (UnaryInputWord n)) = w
        exact Eq.trans (congrArg stream (unaryInputWord_length n)) hn

theorem listable_has_unary_range_function {L : Language output}
    (h : Listable L) :
    exists f : Word Unit -> Word output,
      Language.Equal (RangeLanguage f) L := by
  cases h with
  | intro stream hstream =>
      exists ListingAsUnaryFunction stream
      exact listedBy_rangeLanguage_listingAsUnaryFunction hstream

theorem rangeLanguage_equal_of_pointwise
    {f g : Word input -> Word output}
    (hfg : forall x, f x = g x) :
    Language.Equal (RangeLanguage f) (RangeLanguage g) := by
  intro w
  constructor
  · intro hw
    cases hw with
    | intro x hx =>
        exists x
        rw [← hfg x]
        exact hx
  · intro hw
    cases hw with
    | intro x hx =>
        exists x
        rw [hfg x]
        exact hx

theorem rangeOfComputableFunction_of_equal {L K : Language output}
    (h : RangeOfComputableFunction L) (hEq : Language.Equal L K) :
    RangeOfComputableFunction K := by
  cases h with
  | intro input hinput =>
      cases hinput with
      | intro f hf =>
          exists input
          exists f
          constructor
          · exact hf.left
          · exact Language.equal_trans hf.right hEq

end Computability
end FoC
