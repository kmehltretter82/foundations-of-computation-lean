import FoC.Book.Chapter04.Section04.Range12

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section04

open Languages
open Grammars

/-!
# The Half-Range Variant

This machine recognizes the complementary block-range pattern `m <= n <= 2m`.
It nondeterministically groups some {lit}`a`s in pairs before switching to the
{lit}`b`-popping phase.
-/

inductive HalfRangePDAState where
  | ready
  | needSecond
  | pop
deriving DecidableEq

namespace HalfRangePDAState

def finite : Foundation.FiniteType HalfRangePDAState where
  elems := [ready, needSecond, pop]
  complete := by
    intro q
    cases q <;> simp

end HalfRangePDAState

inductive HalfRangePDATransition :
    HalfRangePDAState -> Option Section01.AB -> Word AnBnPDAStack ->
      HalfRangePDAState -> Word AnBnPDAStack -> Prop where
  | oneA :
      HalfRangePDATransition HalfRangePDAState.ready (some Section01.AB.a) []
        HalfRangePDAState.ready [AnBnPDAStack.marker]
  | firstOfPair :
      HalfRangePDATransition HalfRangePDAState.ready (some Section01.AB.a) []
        HalfRangePDAState.needSecond []
  | secondOfPair :
      HalfRangePDATransition HalfRangePDAState.needSecond (some Section01.AB.a) []
        HalfRangePDAState.ready [AnBnPDAStack.marker]
  | startPop :
      HalfRangePDATransition HalfRangePDAState.ready none []
        HalfRangePDAState.pop []
  | popB :
      HalfRangePDATransition HalfRangePDAState.pop (some Section01.AB.b)
        [AnBnPDAStack.marker] HalfRangePDAState.pop []

def HalfRangePDA : PDA Section01.AB AnBnPDAStack HalfRangePDAState where
  start := HalfRangePDAState.ready
  transition := HalfRangePDATransition
  accept := fun q => q = HalfRangePDAState.pop
  statesFinite := HalfRangePDAState.finite

def HalfRangeLanguage : Language Section01.AB :=
  fun w => exists n m, m <= n ∧ n <= 2 * m ∧ w = AnBmWord n m

def halfRangeExampleWord : Word Section01.AB :=
  AnBmWord 3 2

/-!
The example word demonstrates the intended behavior before the general proof:
read three {lit}`a`s, push two markers by grouping one pair and one single,
then pop those two markers while reading two {lit}`b`s.
-/

theorem halfRangePDA_accepts_three_a_two_b :
    PDA.Accepts HalfRangePDA halfRangeExampleWord := by
  exists HalfRangePDAState.pop
  constructor
  · rfl
  · unfold halfRangeExampleWord AnBmWord PDA.initial
    let c0 : PDA.Configuration Section01.AB AnBnPDAStack HalfRangePDAState :=
      { state := HalfRangePDAState.ready,
        unread := [Section01.AB.a, Section01.AB.a, Section01.AB.a,
          Section01.AB.b, Section01.AB.b],
        stack := [] }
    let c1 : PDA.Configuration Section01.AB AnBnPDAStack HalfRangePDAState :=
      { state := HalfRangePDAState.needSecond,
        unread := [Section01.AB.a, Section01.AB.a, Section01.AB.b, Section01.AB.b],
        stack := [] }
    let c2 : PDA.Configuration Section01.AB AnBnPDAStack HalfRangePDAState :=
      { state := HalfRangePDAState.ready,
        unread := [Section01.AB.a, Section01.AB.b, Section01.AB.b],
        stack := [AnBnPDAStack.marker] }
    let c3 : PDA.Configuration Section01.AB AnBnPDAStack HalfRangePDAState :=
      { state := HalfRangePDAState.ready,
        unread := [Section01.AB.b, Section01.AB.b],
        stack := [AnBnPDAStack.marker, AnBnPDAStack.marker] }
    let c4 : PDA.Configuration Section01.AB AnBnPDAStack HalfRangePDAState :=
      { state := HalfRangePDAState.pop,
        unread := [Section01.AB.b, Section01.AB.b],
        stack := [AnBnPDAStack.marker, AnBnPDAStack.marker] }
    let c5 : PDA.Configuration Section01.AB AnBnPDAStack HalfRangePDAState :=
      { state := HalfRangePDAState.pop,
        unread := [Section01.AB.b],
        stack := [AnBnPDAStack.marker] }
    let c6 : PDA.Configuration Section01.AB AnBnPDAStack HalfRangePDAState :=
      { state := HalfRangePDAState.pop,
        unread := [],
        stack := [] }
    have h01 : PDA.Step HalfRangePDA c0 c1 := by
      exact PDA.Step.read (M := HalfRangePDA)
        (unread := [Section01.AB.a, Section01.AB.a,
          Section01.AB.b, Section01.AB.b])
        (restStack := []) HalfRangePDATransition.firstOfPair
    have h12 : PDA.Step HalfRangePDA c1 c2 := by
      exact PDA.Step.read (M := HalfRangePDA)
        (unread := [Section01.AB.a, Section01.AB.b, Section01.AB.b])
        (restStack := []) HalfRangePDATransition.secondOfPair
    have h23 : PDA.Step HalfRangePDA c2 c3 := by
      exact PDA.Step.read (M := HalfRangePDA)
        (unread := [Section01.AB.b, Section01.AB.b])
        (restStack := [AnBnPDAStack.marker]) HalfRangePDATransition.oneA
    have h34 : PDA.Step HalfRangePDA c3 c4 := by
      exact PDA.Step.epsilon (M := HalfRangePDA)
        (unread := [Section01.AB.b, Section01.AB.b])
        (restStack := [AnBnPDAStack.marker, AnBnPDAStack.marker])
        HalfRangePDATransition.startPop
    have h45 : PDA.Step HalfRangePDA c4 c5 := by
      exact PDA.Step.read (M := HalfRangePDA)
        (unread := [Section01.AB.b])
        (restStack := [AnBnPDAStack.marker]) HalfRangePDATransition.popB
    have h56 : PDA.Step HalfRangePDA c5 c6 := by
      exact PDA.Step.read (M := HalfRangePDA)
        (unread := [])
        (restStack := []) HalfRangePDATransition.popB
    change PDA.Computes HalfRangePDA c0 c6
    exact PDA.Computes.step h01
      (PDA.Computes.step h12
        (PDA.Computes.step h23
          (PDA.Computes.step h34
            (PDA.Computes.step h45
      (PDA.Computes.step h56 (PDA.Computes.refl c6))))))

/-!
The general acceptance proof separates two ways of creating markers. A single
{lit}`a` may push one marker, while a pair of {lit}`a`s may also push one marker.
Combining those computations recognizes exactly the range
{lit}`m <= n <= 2 * m`.
-/

theorem halfRangePDA_push_singles (n : Nat) (rest : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Computes HalfRangePDA
      { state := HalfRangePDAState.ready,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
        stack := stack }
      { state := HalfRangePDAState.ready,
        unread := rest,
        stack := Word.Concat (AnBnPDAStackWord n) stack } := by
  induction n generalizing stack with
  | zero =>
      simp [Word.Concat, Word.RepeatSymbol, AnBnPDAStackWord]
      exact PDA.Computes.refl _
  | succ n ih =>
      have hstep : PDA.Step HalfRangePDA
          { state := HalfRangePDAState.ready,
            unread := Section01.AB.a ::
              Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
            stack := stack }
          { state := HalfRangePDAState.ready,
            unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
            stack := AnBnPDAStack.marker :: stack } := by
        exact PDA.Step.read (M := HalfRangePDA)
          (unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest)
          (restStack := stack) HalfRangePDATransition.oneA
      have hrest := ih (AnBnPDAStack.marker :: stack)
      have htarget :
          Word.Concat (AnBnPDAStackWord n)
              (AnBnPDAStack.marker :: stack) =
            Word.Concat (AnBnPDAStackWord (n + 1)) stack := by
        simp [AnBnPDAStackWord, Word.Concat, Word.RepeatSymbol,
          Section01.replicate_succ_eq_append AnBnPDAStack.marker n,
          List.append_assoc]
      exact PDA.Computes.step hstep (by
        simpa [htarget] using hrest)

theorem halfRangePDA_push_pairs (pairs : Nat) (rest : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Computes HalfRangePDA
      { state := HalfRangePDAState.ready,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs)) rest,
        stack := stack }
      { state := HalfRangePDAState.ready,
        unread := rest,
        stack := Word.Concat (AnBnPDAStackWord pairs) stack } := by
  induction pairs generalizing stack with
  | zero =>
      simp [Word.Concat, Word.RepeatSymbol, AnBnPDAStackWord]
      exact PDA.Computes.refl _
  | succ pairs ih =>
      have hfirst : PDA.Step HalfRangePDA
          { state := HalfRangePDAState.ready,
            unread := Section01.AB.a :: Section01.AB.a ::
              Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs)) rest,
            stack := stack }
          { state := HalfRangePDAState.needSecond,
            unread := Section01.AB.a ::
              Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs)) rest,
            stack := stack } := by
        exact PDA.Step.read (M := HalfRangePDA)
          (unread := Section01.AB.a ::
            Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs)) rest)
          (restStack := stack) HalfRangePDATransition.firstOfPair
      have hsecond : PDA.Step HalfRangePDA
          { state := HalfRangePDAState.needSecond,
            unread := Section01.AB.a ::
              Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs)) rest,
            stack := stack }
          { state := HalfRangePDAState.ready,
            unread := Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs)) rest,
            stack := AnBnPDAStack.marker :: stack } := by
        exact PDA.Step.read (M := HalfRangePDA)
          (unread := Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs)) rest)
          (restStack := stack) HalfRangePDATransition.secondOfPair
      have hrest := ih (AnBnPDAStack.marker :: stack)
      have htarget :
          Word.Concat (AnBnPDAStackWord pairs)
              (AnBnPDAStack.marker :: stack) =
            Word.Concat (AnBnPDAStackWord (pairs + 1)) stack := by
        simp [AnBnPDAStackWord, Word.Concat, Word.RepeatSymbol,
          Section01.replicate_succ_eq_append AnBnPDAStack.marker pairs,
          List.append_assoc]
      have htail : PDA.Computes HalfRangePDA
          { state := HalfRangePDAState.ready,
            unread := Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs)) rest,
            stack := AnBnPDAStack.marker :: stack }
          { state := HalfRangePDAState.ready, unread := rest,
            stack := Word.Concat (AnBnPDAStackWord (pairs + 1)) stack } := by
        simpa [htarget] using hrest
      have hprefix :
          Word.RepeatSymbol Section01.AB.a (2 * (pairs + 1)) =
            Section01.AB.a :: Section01.AB.a ::
              Word.RepeatSymbol Section01.AB.a (2 * pairs) := by
        simp [Word.RepeatSymbol]
        rw [show 2 * (pairs + 1) = 2 * pairs + 1 + 1 by omega]
        rw [List.replicate_succ]
        rw [List.replicate_succ]
      rw [hprefix]
      exact PDA.Computes.step hfirst
        (PDA.Computes.step hsecond htail)

theorem halfRangePDA_push_as_with_pairs (pairs singles : Nat)
    (rest : Word Section01.AB) (stack : Word AnBnPDAStack) :
    PDA.Computes HalfRangePDA
      { state := HalfRangePDAState.ready,
        unread :=
          Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs + singles)) rest,
        stack := stack }
      { state := HalfRangePDAState.ready,
        unread := rest,
        stack := Word.Concat (AnBnPDAStackWord (pairs + singles)) stack } := by
  have hpairs :=
    halfRangePDA_push_pairs pairs
      (Word.Concat (Word.RepeatSymbol Section01.AB.a singles) rest) stack
  have hsingles :=
    halfRangePDA_push_singles singles rest
      (Word.Concat (AnBnPDAStackWord pairs) stack)
  have hpairs' : PDA.Computes HalfRangePDA
      { state := HalfRangePDAState.ready,
        unread :=
          Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs + singles)) rest,
        stack := stack }
      { state := HalfRangePDAState.ready,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.a singles) rest,
        stack := Word.Concat (AnBnPDAStackWord pairs) stack } := by
    have hrepeat :
        Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs))
            (Word.Concat (Word.RepeatSymbol Section01.AB.a singles) rest) =
          Word.Concat (Word.RepeatSymbol Section01.AB.a (2 * pairs + singles)) rest := by
      simp [Word.Concat, Word.RepeatSymbol]
      rw [← List.append_assoc, List.replicate_append_replicate]
    simpa [hrepeat] using hpairs
  have hsingles' : PDA.Computes HalfRangePDA
      { state := HalfRangePDAState.ready,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.a singles) rest,
        stack := Word.Concat (AnBnPDAStackWord pairs) stack }
      { state := HalfRangePDAState.ready,
        unread := rest,
        stack := Word.Concat (AnBnPDAStackWord (pairs + singles)) stack } := by
    have hstack :
        Word.Concat (AnBnPDAStackWord singles)
            (Word.Concat (AnBnPDAStackWord pairs) stack) =
          Word.Concat (AnBnPDAStackWord (pairs + singles)) stack := by
      simp [AnBnPDAStackWord, Word.Concat, Word.RepeatSymbol]
      rw [← List.append_assoc, List.replicate_append_replicate, Nat.add_comm]
    simpa [hstack] using hsingles
  exact PDA.computes_trans hpairs' hsingles'

theorem halfRangePDA_switch_to_pop (unread : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Step HalfRangePDA
      { state := HalfRangePDAState.ready, unread := unread, stack := stack }
      { state := HalfRangePDAState.pop, unread := unread, stack := stack } := by
  simpa [Word.Concat] using
    (PDA.Step.epsilon (M := HalfRangePDA) (unread := unread)
      (restStack := stack) HalfRangePDATransition.startPop)

theorem halfRangePDA_pop_bs (m : Nat) (rest : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Computes HalfRangePDA
      { state := HalfRangePDAState.pop,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.b m) rest,
        stack := Word.Concat (AnBnPDAStackWord m) stack }
      { state := HalfRangePDAState.pop, unread := rest, stack := stack } := by
  induction m generalizing stack with
  | zero =>
      simp [Word.Concat, Word.RepeatSymbol, AnBnPDAStackWord]
      exact PDA.Computes.refl _
  | succ m ih =>
      have hstep : PDA.Step HalfRangePDA
          { state := HalfRangePDAState.pop,
            unread := Section01.AB.b ::
              Word.Concat (Word.RepeatSymbol Section01.AB.b m) rest,
            stack := AnBnPDAStack.marker ::
              Word.Concat (AnBnPDAStackWord m) stack }
          { state := HalfRangePDAState.pop,
            unread := Word.Concat (Word.RepeatSymbol Section01.AB.b m) rest,
            stack := Word.Concat (AnBnPDAStackWord m) stack } := by
        exact PDA.Step.read (M := HalfRangePDA)
          (unread := Word.Concat (Word.RepeatSymbol Section01.AB.b m) rest)
          (restStack := Word.Concat (AnBnPDAStackWord m) stack)
          HalfRangePDATransition.popB
      exact PDA.Computes.step hstep (ih stack)

theorem halfRangePDA_accepts_range_words {n m : Nat}
    (hLower : m <= n) (hUpper : n <= 2 * m) :
    PDA.Accepts HalfRangePDA (AnBmWord n m) := by
  let pairs := n - m
  let singles := 2 * m - n
  have hn : n = 2 * pairs + singles := by
    simp [pairs, singles]
    omega
  have hm : m = pairs + singles := by
    simp [pairs, singles]
    omega
  exists HalfRangePDAState.pop
  constructor
  · rfl
  · unfold PDA.initial AnBmWord
    have hpush :=
      halfRangePDA_push_as_with_pairs pairs singles
        (Word.RepeatSymbol Section01.AB.b m) ([] : Word AnBnPDAStack)
    have hpush' : PDA.Computes HalfRangePDA
        { state := HalfRangePDAState.ready,
          unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n)
            (Word.RepeatSymbol Section01.AB.b m),
          stack := [] }
        { state := HalfRangePDAState.ready,
          unread := Word.RepeatSymbol Section01.AB.b m,
          stack := Word.Concat (AnBnPDAStackWord m) [] } := by
      rw [hn]
      have hstack :
          Word.Concat (AnBnPDAStackWord (pairs + singles)) [] =
            Word.Concat (AnBnPDAStackWord m) [] := by
        rw [← hm]
      simpa [hstack] using hpush
    have hswitch : PDA.Computes HalfRangePDA
        { state := HalfRangePDAState.ready,
          unread := Word.RepeatSymbol Section01.AB.b m,
          stack := Word.Concat (AnBnPDAStackWord m) [] }
        { state := HalfRangePDAState.pop,
          unread := Word.RepeatSymbol Section01.AB.b m,
          stack := Word.Concat (AnBnPDAStackWord m) [] } := by
      exact PDA.computes_of_step
        (halfRangePDA_switch_to_pop (Word.RepeatSymbol Section01.AB.b m)
          (Word.Concat (AnBnPDAStackWord m) []))
    have hpop : PDA.Computes HalfRangePDA
        { state := HalfRangePDAState.pop,
          unread := Word.RepeatSymbol Section01.AB.b m,
          stack := Word.Concat (AnBnPDAStackWord m) [] }
        { state := HalfRangePDAState.pop, unread := [], stack := [] } := by
      simpa [Word.Concat] using halfRangePDA_pop_bs m [] []
    exact PDA.computes_trans hpush'
      (PDA.computes_trans hswitch hpop)

/-!
The converse proof uses tail predicates to describe what remains possible from
each state. They rule out malformed endings, for example stopping in the middle
of an {lit}`a` pair or trying to pop more markers than were pushed.
-/

def HalfRangeReadyTail (unread : Word Section01.AB)
    (stack : Word AnBnPDAStack) : Prop :=
  exists n m,
    m <= n ∧ n <= 2 * m ∧
      unread =
        Word.Concat (Word.RepeatSymbol Section01.AB.a n)
          (Word.RepeatSymbol Section01.AB.b (Word.Length stack + m))

def HalfRangeNeedSecondTail (unread : Word Section01.AB)
    (stack : Word AnBnPDAStack) : Prop :=
  exists n m,
    m <= n ∧ n < 2 * m ∧
      unread =
        Word.Concat (Word.RepeatSymbol Section01.AB.a n)
          (Word.RepeatSymbol Section01.AB.b (Word.Length stack + m))

def HalfRangeAcceptedTail :
    HalfRangePDAState -> Word Section01.AB -> Word AnBnPDAStack -> Prop
  | HalfRangePDAState.pop, unread, stack =>
      unread = Word.RepeatSymbol Section01.AB.b (Word.Length stack)
  | HalfRangePDAState.ready, unread, stack =>
      HalfRangeReadyTail unread stack
  | HalfRangePDAState.needSecond, unread, stack =>
      HalfRangeNeedSecondTail unread stack

theorem halfRangePDA_computes_final_shape_config
    {c d : PDA.Configuration Section01.AB AnBnPDAStack HalfRangePDAState}
    (h : PDA.Computes HalfRangePDA c d)
    (hfinal :
      d = { state := HalfRangePDAState.pop, unread := [], stack := [] }) :
    HalfRangeAcceptedTail c.state c.unread c.stack := by
  induction h with
  | refl c =>
      rw [hfinal]
      simp [HalfRangeAcceptedTail, Word.Length, Word.RepeatSymbol]
  | step hstep hrest ih =>
      cases hstep with
      | read htrans =>
          cases htrans with
          | oneA =>
              cases ih hfinal with
              | intro n hn =>
                  cases hn with
                  | intro m hm =>
                      exists n + 1
                      exists m + 1
                      constructor
                      · omega
                      constructor
                      · omega
                      · simp [Word.Length, Word.Concat, Word.RepeatSymbol] at hm ⊢
                        rw [hm.right.right]
                        simp [Section01.replicate_succ_eq_cons,
                          Nat.add_comm, Nat.add_left_comm]
          | firstOfPair =>
              cases ih hfinal with
              | intro n hn =>
                  cases hn with
                  | intro m hm =>
                      exists n + 1
                      exists m
                      constructor
                      · omega
                      constructor
                      · omega
                      · simp [Word.Length, Word.Concat, Word.RepeatSymbol] at hm ⊢
                        rw [hm.right.right]
                        simp [Section01.replicate_succ_eq_cons]
          | secondOfPair =>
              cases ih hfinal with
              | intro n hn =>
                  cases hn with
                  | intro m hm =>
                      exists n + 1
                      exists m + 1
                      constructor
                      · omega
                      constructor
                      · omega
                      · simp [Word.Length, Word.Concat, Word.RepeatSymbol] at hm ⊢
                        rw [hm.right.right]
                        simp [Section01.replicate_succ_eq_cons,
                          Nat.add_comm, Nat.add_left_comm]
          | popB =>
              have htail := ih hfinal
              simp [HalfRangeAcceptedTail, Word.Concat, Word.Length,
                Word.RepeatSymbol] at htail ⊢
              rw [htail]
              rw [List.replicate_succ]
      | epsilon htrans =>
          cases htrans with
          | startPop =>
              have hpop := ih hfinal
              exact ⟨0, 0, by omega, by omega,
                by
                  simpa [HalfRangeAcceptedTail, HalfRangeReadyTail,
                    Word.Concat, Word.RepeatSymbol, Word.Length] using hpop⟩

theorem halfRangePDA_accepts_only_range_words {w : Word Section01.AB}
    (h : PDA.Accepts HalfRangePDA w) :
    w ∈ HalfRangeLanguage := by
  cases h with
  | intro q hq =>
      cases hq.left
      have hshape := halfRangePDA_computes_final_shape_config hq.right rfl
      cases hshape with
      | intro n hn =>
          cases hn with
          | intro m hm =>
              exists n
              exists m
              constructor
              · exact hm.left
              constructor
              · exact hm.right.left
              · simpa [PDA.initial, HalfRangeAcceptedTail, HalfRangeReadyTail,
                  HalfRangeLanguage, AnBmWord, Word.Length, Word.Concat]
                  using hm.right.right

theorem halfRangePDA_accepted_language_exact (w : Word Section01.AB) :
    w ∈ PDA.AcceptedLanguage HalfRangePDA <-> w ∈ HalfRangeLanguage := by
  constructor
  · exact halfRangePDA_accepts_only_range_words
  · intro hw
    cases hw with
    | intro n hn =>
        cases hn with
        | intro m hm =>
            rw [hm.right.right]
            exact halfRangePDA_accepts_range_words hm.left hm.right.left

end Section04
end Chapter04
end Book
end FoC
