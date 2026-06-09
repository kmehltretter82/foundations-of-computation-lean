import FoC.Foundation.Countable
import FoC.Computability.Recognizable

set_option doc.verso true

/-!
# Enumerable languages

## Listings and ranges

Recursively enumerable languages can be viewed through machines, listings, or
ranges of computable functions.  This module records those equivalent-looking
forms as reusable predicates and bridges.

## Book coordinates

Used by:
- Chapter 5, Section 5.2: equivalent descriptions of recursively enumerable
  languages by accepting machines, listing machines, and ranges of computable
  functions.
-/

namespace FoC
namespace Computability

open Languages

/-!
# Listings

A listing is a stream of words whose range is extensionally equal to the
language.
-/

def ListedBy (stream : Nat -> Word alpha) (L : Language alpha) : Prop :=
  Language.Equal (fun w => exists n : Nat, stream n = w) L

def Listable (L : Language alpha) : Prop :=
  exists stream : Nat -> Word alpha, ListedBy stream L

def PartiallyListedBy (stream : Nat -> Option (Word alpha))
    (L : Language alpha) : Prop :=
  Language.Equal (fun w => exists n : Nat, stream n = some w) L

def PartiallyListable (L : Language alpha) : Prop :=
  exists stream : Nat -> Option (Word alpha), PartiallyListedBy stream L

/-!
# Ranges of functions

Enumerable languages can also be described as ranges of string functions, with
or without an explicit computability requirement.
-/

def RangeLanguage (f : Word input -> Word output) : Language output :=
  fun w => exists x : Word input, f x = w

def PartialRangeLanguage
    (f : Word input -> Option (Word output)) : Language output :=
  fun w => exists x : Word input, f x = some w

def RangeOfComputableFunction (L : Language output) : Prop :=
  exists input : Type, exists f : Word input -> Word output,
    TuringComputable f ∧ Language.Equal (RangeLanguage f) L

def RangeOfUnaryFunction (L : Language output) : Prop :=
  exists f : Word Unit -> Word output, Language.Equal (RangeLanguage f) L

def PartialRangeOfUnaryFunction (L : Language output) : Prop :=
  exists f : Word Unit -> Option (Word output),
    Language.Equal (PartialRangeLanguage f) L

def UnaryInputWord (n : Nat) : Word Unit :=
  Word.RepeatSymbol () n

def ListingAsUnaryFunction (stream : Nat -> Word output) :
    Word Unit -> Word output :=
  fun w => stream (Word.Length w)

def PartialListingAsUnaryFunction (stream : Nat -> Option (Word output)) :
    Word Unit -> Option (Word output) :=
  fun w => stream (Word.Length w)

def WordStreamCovers (stream : Nat -> Option (Word alpha)) : Prop :=
  forall w : Word alpha, exists n : Nat, stream n = some w

noncomputable def CodeCandidates (code : alpha -> Nat) :
    Nat -> Option alpha :=
  by
    classical
    exact fun n =>
      if h : exists x : alpha, code x = n then
        some (Classical.choose h)
      else
        none

theorem codeCandidates_of_code
    {code : alpha -> Nat}
    (hcode : Foundation.Fn.Injective code)
    (x : alpha) :
    CodeCandidates code (code x) = some x := by
  classical
  unfold CodeCandidates
  have hExists : exists y : alpha, code y = code x := ⟨x, rfl⟩
  rw [dif_pos hExists]
  have hchosen : code (Classical.choose hExists) = code x :=
    Classical.choose_spec hExists
  have hchoice : Classical.choose hExists = x := hcode hchosen
  rw [hchoice]

theorem codeCandidates_covers
    {code : alpha -> Nat}
    (hcode : Foundation.Fn.Injective code) :
    forall x : alpha, exists n : Nat, CodeCandidates code n = some x := by
  intro x
  exact ⟨code x, codeCandidates_of_code hcode x⟩

noncomputable def PairCodeDecode (n : Nat) :
    Option (Nat × Nat) :=
  by
    classical
    exact
      if h : exists left : Nat, exists right : Nat,
          Foundation.Countability.PairCode left right = n then
        let left := Classical.choose h
        let hright := Classical.choose_spec h
        let right := Classical.choose hright
        some (left, right)
      else
        none

theorem pairCodeDecode_pairCode (left right : Nat) :
    PairCodeDecode
        (Foundation.Countability.PairCode left right) =
      some (left, right) := by
  classical
  unfold PairCodeDecode
  have hExists : exists left' : Nat, exists right' : Nat,
      Foundation.Countability.PairCode left' right' =
        Foundation.Countability.PairCode left right :=
    ⟨left, right, rfl⟩
  rw [dif_pos hExists]
  let left' := Classical.choose hExists
  let hright := Classical.choose_spec hExists
  let right' := Classical.choose hright
  have hpair :
      Foundation.Countability.PairCode left' right' =
        Foundation.Countability.PairCode left right := by
    simpa [left', right', hright] using Classical.choose_spec hright
  rcases Foundation.Countability.pairCode_injective_left hpair with
    ⟨hleft, hright'⟩
  change some (left', right') = some (left, right)
  rw [hleft, hright']

noncomputable def BoundedTraceListing
    (candidates : Nat -> Option (Word alpha))
    (trace : Word alpha -> Nat -> Prop) :
    Nat -> Option (Word alpha) :=
  by
    classical
    exact fun n =>
      match PairCodeDecode n with
      | none => none
      | some (candidateIndex, stage) =>
          match candidates candidateIndex with
          | none => none
          | some w => if trace w stage then some w else none

theorem boundedTraceListing_pairCode_of_trace
    (candidates : Nat -> Option (Word alpha))
    (trace : Word alpha -> Nat -> Prop)
    {candidateIndex stage : Nat} {w : Word alpha}
    (hcandidate : candidates candidateIndex = some w)
    (htrace : trace w stage) :
    BoundedTraceListing candidates trace
        (Foundation.Countability.PairCode candidateIndex stage) =
      some w := by
  classical
  simp [BoundedTraceListing, pairCodeDecode_pairCode,
    hcandidate, htrace]

theorem boundedTraceListing_trace_of_some
    {candidates : Nat -> Option (Word alpha)}
    {trace : Word alpha -> Nat -> Prop}
    {n : Nat} {w : Word alpha}
    (h : BoundedTraceListing candidates trace n = some w) :
    exists stage : Nat, trace w stage := by
  classical
  unfold BoundedTraceListing at h
  cases hpair : PairCodeDecode n with
  | none =>
      simp [hpair] at h
  | some pair =>
      cases pair with
      | mk candidateIndex stage =>
          cases hcandidate : candidates candidateIndex with
          | none =>
              simp [hpair, hcandidate] at h
          | some listed =>
              by_cases htrace : trace listed stage
              · simp [hpair, hcandidate, htrace] at h
                cases h
                exact ⟨stage, htrace⟩
              · simp [hpair, hcandidate, htrace] at h

theorem acceptanceTrace_boundedTraceListing_partiallyListedBy
    {candidates : Nat -> Option (Word alpha)}
    {trace : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (hcovers : WordStreamCovers candidates)
    (htrace : AcceptanceTrace trace L) :
    PartiallyListedBy (BoundedTraceListing candidates trace) L := by
  intro w
  constructor
  · intro hlisted
    rcases hlisted with ⟨n, hn⟩
    rcases boundedTraceListing_trace_of_some hn with ⟨stage, hstage⟩
    exact acceptanceTrace_sound htrace hstage
  · intro hw
    rcases hcovers w with ⟨candidateIndex, hcandidate⟩
    rcases acceptanceTrace_complete htrace hw with ⟨stage, hstage⟩
    exists Foundation.Countability.PairCode candidateIndex stage
    exact boundedTraceListing_pairCode_of_trace
      candidates trace hcandidate hstage

theorem acceptanceTrace_partiallyListable_of_word_stream
    {candidates : Nat -> Option (Word alpha)}
    {trace : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (hcovers : WordStreamCovers candidates)
    (htrace : AcceptanceTrace trace L) :
    PartiallyListable L :=
  ⟨BoundedTraceListing candidates trace,
    acceptanceTrace_boundedTraceListing_partiallyListedBy hcovers htrace⟩

theorem acceptanceTrace_partiallyListable_of_word_code
    {code : Word alpha -> Nat}
    (hcode : Foundation.Fn.Injective code)
    {trace : Word alpha -> Nat -> Prop}
    {L : Language alpha}
    (htrace : AcceptanceTrace trace L) :
    PartiallyListable L :=
  acceptanceTrace_partiallyListable_of_word_stream
    (candidates := CodeCandidates code)
    (codeCandidates_covers hcode)
    htrace

/-!
# Equivalence predicates

These proposition-level predicates name the standard equivalences discussed in
the textbook.
-/

def AcceptableListingEquivalence (L : Language alpha) : Prop :=
  TuringAcceptable L <-> Listable L

def AcceptableRangeEquivalence (L : Language alpha) : Prop :=
  TuringAcceptable L <-> RangeOfComputableFunction L

/-!
# Listing laws

The first lemmas expose membership in a listed language and preserve listability
under language equality.
-/

theorem listedBy_mem {stream : Nat -> Word alpha} {L : Language alpha}
    (h : ListedBy stream L) (w : Word alpha) :
    (exists n : Nat, stream n = w) <-> w ∈ L :=
  h w

theorem partiallyListedBy_mem
    {stream : Nat -> Option (Word alpha)} {L : Language alpha}
    (h : PartiallyListedBy stream L) (w : Word alpha) :
    (exists n : Nat, stream n = some w) <-> w ∈ L :=
  h w

theorem listedBy_acceptanceTrace
    {stream : Nat -> Word alpha} {L : Language alpha}
    (h : ListedBy stream L) :
    AcceptanceTrace (fun w n => stream n = w) L :=
  h

theorem partiallyListedBy_acceptanceTrace
    {stream : Nat -> Option (Word alpha)} {L : Language alpha}
    (h : PartiallyListedBy stream L) :
    AcceptanceTrace (fun w n => stream n = some w) L :=
  h

theorem listedBy_of_equal {stream : Nat -> Word alpha} {L K : Language alpha}
    (h : ListedBy stream L) (hEq : Language.Equal L K) :
    ListedBy stream K :=
  Language.equal_trans h hEq

theorem partiallyListedBy_of_equal
    {stream : Nat -> Option (Word alpha)} {L K : Language alpha}
    (h : PartiallyListedBy stream L) (hEq : Language.Equal L K) :
    PartiallyListedBy stream K :=
  Language.equal_trans h hEq

theorem listable_of_equal {L K : Language alpha}
    (h : Listable L) (hEq : Language.Equal L K) :
    Listable K := by
  cases h with
  | intro stream hstream =>
      exists stream
      exact listedBy_of_equal hstream hEq

theorem partiallyListable_of_equal {L K : Language alpha}
    (h : PartiallyListable L) (hEq : Language.Equal L K) :
    PartiallyListable K := by
  cases h with
  | intro stream hstream =>
      exists stream
      exact partiallyListedBy_of_equal hstream hEq

theorem listed_word_mem {stream : Nat -> Word alpha} {L : Language alpha}
    (h : ListedBy stream L) (n : Nat) :
    stream n ∈ L :=
  (h (stream n)).mp (Exists.intro n rfl)

theorem partially_listed_word_mem
    {stream : Nat -> Option (Word alpha)} {L : Language alpha}
    (h : PartiallyListedBy stream L) {n : Nat} {w : Word alpha}
    (hn : stream n = some w) :
    w ∈ L :=
  (h w).mp (Exists.intro n hn)

theorem empty_partiallyListable :
    PartiallyListable (Language.Empty : Language alpha) := by
  exists fun _ : Nat => none
  intro w
  constructor
  · intro hw
    cases hw with
    | intro _ hn =>
        cases hn
  · intro hw
    cases hw

theorem range_mem {f : Word input -> Word output} (x : Word input) :
    f x ∈ RangeLanguage f :=
  Exists.intro x rfl

theorem partial_range_mem
    {f : Word input -> Option (Word output)}
    {x : Word input} {w : Word output}
    (hx : f x = some w) :
    w ∈ PartialRangeLanguage f :=
  Exists.intro x hx

/-!
# Unary range conversion

Unary input words encode natural indices, turning any listing stream into a
unary-input range function and conversely.
-/

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

theorem partialUnaryFunctionRange_partiallyListedBy
    (f : Word Unit -> Option (Word output)) :
    PartiallyListedBy
      (fun n => f (UnaryInputWord n))
      (PartialRangeLanguage f) := by
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
        change f (UnaryInputWord (Word.Length x)) = some w
        exact Eq.trans
          (congrArg f (unit_word_eq_unaryInputWord_length x).symm) hx

theorem partialUnaryFunctionRange_partiallyListable
    (f : Word Unit -> Option (Word output)) :
    PartiallyListable (PartialRangeLanguage f) :=
  Exists.intro (fun n => f (UnaryInputWord n))
    (partialUnaryFunctionRange_partiallyListedBy f)

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

theorem partiallyListedBy_partialRangeLanguage_partialListingAsUnaryFunction
    {stream : Nat -> Option (Word output)} {L : Language output}
    (h : PartiallyListedBy stream L) :
    Language.Equal
      (PartialRangeLanguage (PartialListingAsUnaryFunction stream)) L := by
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
        change stream (Word.Length (UnaryInputWord n)) = some w
        exact Eq.trans (congrArg stream (unaryInputWord_length n)) hn

theorem listable_has_unary_range_function {L : Language output}
    (h : Listable L) :
    exists f : Word Unit -> Word output,
      Language.Equal (RangeLanguage f) L := by
  cases h with
  | intro stream hstream =>
      exists ListingAsUnaryFunction stream
      exact listedBy_rangeLanguage_listingAsUnaryFunction hstream

theorem listable_rangeOfUnaryFunction {L : Language output}
    (h : Listable L) :
    RangeOfUnaryFunction L :=
  listable_has_unary_range_function h

theorem partiallyListable_has_partial_unary_range_function
    {L : Language output}
    (h : PartiallyListable L) :
    exists f : Word Unit -> Option (Word output),
      Language.Equal (PartialRangeLanguage f) L := by
  cases h with
  | intro stream hstream =>
      exists PartialListingAsUnaryFunction stream
      exact partiallyListedBy_partialRangeLanguage_partialListingAsUnaryFunction
        hstream

theorem partiallyListable_partialRangeOfUnaryFunction
    {L : Language output}
    (h : PartiallyListable L) :
    PartialRangeOfUnaryFunction L :=
  partiallyListable_has_partial_unary_range_function h

theorem acceptanceTrace_partialRangeOfUnaryFunction_of_word_stream
    {candidates : Nat -> Option (Word output)}
    {trace : Word output -> Nat -> Prop}
    {L : Language output}
    (hcovers : WordStreamCovers candidates)
    (htrace : AcceptanceTrace trace L) :
    PartialRangeOfUnaryFunction L :=
  partiallyListable_partialRangeOfUnaryFunction
    (acceptanceTrace_partiallyListable_of_word_stream hcovers htrace)

theorem acceptanceTrace_partialRangeOfUnaryFunction_of_word_code
    {code : Word output -> Nat}
    (hcode : Foundation.Fn.Injective code)
    {trace : Word output -> Nat -> Prop}
    {L : Language output}
    (htrace : AcceptanceTrace trace L) :
    PartialRangeOfUnaryFunction L :=
  acceptanceTrace_partialRangeOfUnaryFunction_of_word_stream
    (candidates := CodeCandidates code)
    (codeCandidates_covers hcode)
    htrace

theorem rangeOfUnaryFunction_listable {L : Language output}
    (h : RangeOfUnaryFunction L) :
    Listable L := by
  cases h with
  | intro f hf =>
      exact listable_of_equal
        (unaryFunctionRange_listable f) hf

theorem listable_iff_rangeOfUnaryFunction (L : Language output) :
    Listable L <-> RangeOfUnaryFunction L := by
  constructor
  · exact listable_rangeOfUnaryFunction
  · exact rangeOfUnaryFunction_listable

theorem partialRangeOfUnaryFunction_partiallyListable
    {L : Language output}
    (h : PartialRangeOfUnaryFunction L) :
    PartiallyListable L := by
  cases h with
  | intro f hf =>
      exact partiallyListable_of_equal
        (partialUnaryFunctionRange_partiallyListable f) hf

theorem partialRangeOfUnaryFunction_acceptanceTrace
    {L : Language output}
    (h : PartialRangeOfUnaryFunction L) :
    exists trace : Word output -> Nat -> Prop,
      AcceptanceTrace trace L := by
  rcases partialRangeOfUnaryFunction_partiallyListable h with
    ⟨stream, hstream⟩
  exact ⟨fun w n => stream n = some w,
    partiallyListedBy_acceptanceTrace hstream⟩

theorem partiallyListable_iff_partialRangeOfUnaryFunction
    (L : Language output) :
    PartiallyListable L <-> PartialRangeOfUnaryFunction L := by
  constructor
  · exact partiallyListable_partialRangeOfUnaryFunction
  · exact partialRangeOfUnaryFunction_partiallyListable

/-!
# Extensional range laws

Range predicates are invariant under pointwise equal functions and language
equality.
-/

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

theorem partialRangeLanguage_equal_of_pointwise
    {f g : Word input -> Option (Word output)}
    (hfg : forall x, f x = g x) :
    Language.Equal (PartialRangeLanguage f) (PartialRangeLanguage g) := by
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

theorem rangeOfUnaryFunction_of_equal {L K : Language output}
    (h : RangeOfUnaryFunction L) (hEq : Language.Equal L K) :
    RangeOfUnaryFunction K := by
  cases h with
  | intro f hf =>
      exists f
      exact Language.equal_trans hf hEq

theorem partialRangeOfUnaryFunction_of_equal {L K : Language output}
    (h : PartialRangeOfUnaryFunction L) (hEq : Language.Equal L K) :
    PartialRangeOfUnaryFunction K := by
  cases h with
  | intro f hf =>
      exists f
      exact Language.equal_trans hf hEq

end Computability
end FoC
