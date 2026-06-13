import FoC.Book.Chapter04.Section04.AnBn

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section04

open Languages
open Grammars

/-!
# The Range {lit}`n <= m <= 2n`

The next PDA recognizes block words {lit}`a^n b^m` where each {lit}`a` contributes one
or two stack markers. Popping one marker per {lit}`b` allows exactly the range
between {lit}`n` and `2n`.
-/

inductive Range12PDAState where
  | push
  | pop
deriving DecidableEq

namespace Range12PDAState

def finite : Foundation.FiniteType Range12PDAState where
  elems := [push, pop]
  complete := by
    intro q
    cases q <;> simp

end Range12PDAState

inductive Range12PDATransition :
    Range12PDAState -> Option Section01.AB -> Word AnBnPDAStack ->
      Range12PDAState -> Word AnBnPDAStack -> Prop where
  | pushOne :
      Range12PDATransition Range12PDAState.push (some Section01.AB.a) []
        Range12PDAState.push [AnBnPDAStack.marker]
  | pushTwo :
      Range12PDATransition Range12PDAState.push (some Section01.AB.a) []
        Range12PDAState.push [AnBnPDAStack.marker, AnBnPDAStack.marker]
  | startPop :
      Range12PDATransition Range12PDAState.push none []
        Range12PDAState.pop []
  | popB :
      Range12PDATransition Range12PDAState.pop (some Section01.AB.b)
        [AnBnPDAStack.marker] Range12PDAState.pop []

def Range12PDA : PDA Section01.AB AnBnPDAStack Range12PDAState where
  start := Range12PDAState.push
  transition := Range12PDATransition
  accept := fun q => q = Range12PDAState.pop
  statesFinite := Range12PDAState.finite

def AnBmWord (n m : Nat) : Word Section01.AB :=
  Word.Concat (Word.RepeatSymbol Section01.AB.a n)
    (Word.RepeatSymbol Section01.AB.b m)

def Range12Language : Language Section01.AB :=
  fun w => exists n m, n <= m ∧ m <= 2 * n ∧ w = AnBmWord n m

/-!
For the forward direction, choose nondeterministically whether each {lit}`a`
pushes one or two markers. The variable {lit}`extra` counts how many of the
{lit}`a`s used the two-marker transition, so the stack has {lit}`n + extra`
markers before the {lit}`b` phase.
-/

theorem range12PDA_push_as_with_extra (n extra : Nat) (hextra : extra <= n)
    (rest : Word Section01.AB) (stack : Word AnBnPDAStack) :
    PDA.Computes Range12PDA
      { state := Range12PDAState.push,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
        stack := stack }
      { state := Range12PDAState.push,
        unread := rest,
        stack :=
          Word.Concat (AnBnPDAStackWord (n + extra)) stack } := by
  induction n generalizing extra stack with
  | zero =>
      have hextraZero : extra = 0 := by omega
      subst extra
      simp [Word.Concat, Word.RepeatSymbol, AnBnPDAStackWord]
      exact PDA.Computes.refl _
  | succ n ih =>
      cases extra with
      | zero =>
          have hstep : PDA.Step Range12PDA
              { state := Range12PDAState.push,
                unread := Section01.AB.a ::
                  Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
                stack := stack }
              { state := Range12PDAState.push,
                unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
                stack := AnBnPDAStack.marker :: stack } := by
            exact PDA.Step.read (M := Range12PDA)
              (unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest)
              (restStack := stack) Range12PDATransition.pushOne
          have hrest := ih 0 (by omega) (AnBnPDAStack.marker :: stack)
          have htarget :
              Word.Concat (AnBnPDAStackWord n)
                  (AnBnPDAStack.marker :: stack) =
                Word.Concat (AnBnPDAStackWord (n + 1)) stack := by
            simp [AnBnPDAStackWord, Word.Concat, Word.RepeatSymbol,
              Section01.replicate_succ_eq_append AnBnPDAStack.marker n,
              List.append_assoc]
          exact PDA.Computes.step hstep (by
            simpa [htarget] using hrest)
      | succ extra =>
          have hstep : PDA.Step Range12PDA
              { state := Range12PDAState.push,
                unread := Section01.AB.a ::
                  Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
                stack := stack }
              { state := Range12PDAState.push,
                unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
                stack := AnBnPDAStack.marker :: AnBnPDAStack.marker :: stack } := by
            exact PDA.Step.read (M := Range12PDA)
              (unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest)
              (restStack := stack) Range12PDATransition.pushTwo
          have hrest := ih extra (by omega)
            (AnBnPDAStack.marker :: AnBnPDAStack.marker :: stack)
          have htarget :
              Word.Concat (AnBnPDAStackWord (n + extra))
                  (AnBnPDAStack.marker :: AnBnPDAStack.marker :: stack) =
                Word.Concat (AnBnPDAStackWord (n + 1 + (extra + 1))) stack := by
            have hnat : n + extra + 2 = n + 1 + (extra + 1) := by omega
            simp [AnBnPDAStackWord, Word.Concat, Word.RepeatSymbol]
            rw [← hnat]
            rw [Section01.replicate_succ_eq_append AnBnPDAStack.marker
              (n + extra + 1)]
            rw [Section01.replicate_succ_eq_append AnBnPDAStack.marker
              (n + extra)]
            simp [List.append_assoc]
          exact PDA.Computes.step hstep (by
            simpa [htarget] using hrest)

theorem range12PDA_switch_to_pop (unread : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Step Range12PDA
      { state := Range12PDAState.push, unread := unread, stack := stack }
      { state := Range12PDAState.pop, unread := unread, stack := stack } := by
  simpa [Word.Concat] using
    (PDA.Step.epsilon (M := Range12PDA) (unread := unread)
      (restStack := stack) Range12PDATransition.startPop)

theorem range12PDA_pop_bs (m : Nat) (rest : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Computes Range12PDA
      { state := Range12PDAState.pop,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.b m) rest,
        stack := Word.Concat (AnBnPDAStackWord m) stack }
      { state := Range12PDAState.pop, unread := rest, stack := stack } := by
  induction m generalizing stack with
  | zero =>
      simp [Word.Concat, Word.RepeatSymbol, AnBnPDAStackWord]
      exact PDA.Computes.refl _
  | succ m ih =>
      have hstep : PDA.Step Range12PDA
          { state := Range12PDAState.pop,
            unread := Section01.AB.b ::
              Word.Concat (Word.RepeatSymbol Section01.AB.b m) rest,
            stack := AnBnPDAStack.marker ::
              Word.Concat (AnBnPDAStackWord m) stack }
          { state := Range12PDAState.pop,
            unread := Word.Concat (Word.RepeatSymbol Section01.AB.b m) rest,
            stack := Word.Concat (AnBnPDAStackWord m) stack } := by
        exact PDA.Step.read (M := Range12PDA)
          (unread := Word.Concat (Word.RepeatSymbol Section01.AB.b m) rest)
          (restStack := Word.Concat (AnBnPDAStackWord m) stack)
          Range12PDATransition.popB
      exact PDA.Computes.step hstep (ih stack)

theorem range12PDA_accepts_range_words {n m : Nat}
    (hLower : n <= m) (hUpper : m <= 2 * n) :
    PDA.Accepts Range12PDA (AnBmWord n m) := by
  let extra := m - n
  have hm : m = n + extra := by
    simp [extra]
    omega
  have hextra : extra <= n := by
    simp [extra]
    omega
  exists Range12PDAState.pop
  constructor
  · rfl
  · unfold PDA.initial AnBmWord
    have hpush :=
      range12PDA_push_as_with_extra n extra hextra
        (Word.RepeatSymbol Section01.AB.b m) ([] : Word AnBnPDAStack)
    have hswitch : PDA.Computes Range12PDA
        { state := Range12PDAState.push,
          unread := Word.RepeatSymbol Section01.AB.b m,
          stack := Word.Concat (AnBnPDAStackWord (n + extra)) [] }
        { state := Range12PDAState.pop,
          unread := Word.RepeatSymbol Section01.AB.b m,
          stack := Word.Concat (AnBnPDAStackWord (n + extra)) [] } := by
      exact PDA.computes_of_step
        (range12PDA_switch_to_pop (Word.RepeatSymbol Section01.AB.b m)
          (Word.Concat (AnBnPDAStackWord (n + extra)) []))
    have hpop : PDA.Computes Range12PDA
        { state := Range12PDAState.pop,
          unread := Word.RepeatSymbol Section01.AB.b m,
          stack := Word.Concat (AnBnPDAStackWord (n + extra)) [] }
        { state := Range12PDAState.pop, unread := [], stack := [] } := by
      rw [hm]
      simpa [Word.Concat] using range12PDA_pop_bs (n + extra) [] []
    exact PDA.computes_trans hpush
      (PDA.computes_trans hswitch hpop)

/-!
For the reverse direction, the proof reads the computation backwards by state.
In the pop state, only {lit}`b`s can be consumed. In the push state, each
{lit}`a` accounts for either one or two future {lit}`b`s.
-/

theorem range12PDA_pop_accepts_only_config
    {c d : PDA.Configuration Section01.AB AnBnPDAStack Range12PDAState}
    (h : PDA.Computes Range12PDA c d)
    (hstate : c.state = Range12PDAState.pop)
    (hfinal :
      d = { state := Range12PDAState.pop, unread := [], stack := [] }) :
    c.unread = Word.RepeatSymbol Section01.AB.b (Word.Length c.stack) := by
  induction h with
  | refl c =>
      rw [hfinal]
      rfl
  | step hstep hrest ih =>
      cases hstep with
      | read htrans =>
          cases hstate
          cases htrans
          have htail := ih rfl hfinal
          simp [Word.Length, Word.RepeatSymbol, Word.Concat] at htail ⊢
          rw [htail]
          rw [Section01.replicate_succ_eq_cons Section01.AB.b]
      | epsilon htrans =>
          cases hstate
          cases htrans

theorem range12PDA_push_accepts_only_config
    {c d : PDA.Configuration Section01.AB AnBnPDAStack Range12PDAState}
    (h : PDA.Computes Range12PDA c d)
    (hstate : c.state = Range12PDAState.push)
    (hfinal :
      d = { state := Range12PDAState.pop, unread := [], stack := [] }) :
    exists n k,
      n <= k ∧ k <= 2 * n ∧
      c.unread =
        Word.Concat (Word.RepeatSymbol Section01.AB.a n)
          (Word.RepeatSymbol Section01.AB.b (Word.Length c.stack + k)) := by
  induction h with
  | refl c =>
      rw [hfinal] at hstate
      cases hstate
  | step hstep hrest ih =>
      cases hstep with
      | read htrans =>
          cases hstate
          cases htrans
          · cases ih rfl hfinal with
            | intro n hn =>
                cases hn with
                | intro k hk =>
                    exists n + 1
                    exists k + 1
                    constructor
                    · omega
                    constructor
                    · omega
                    · simp [Word.Concat, Word.RepeatSymbol, Word.Length] at hk ⊢
                      rw [hk.right.right]
                      simp [Section01.replicate_succ_eq_cons,
                        Nat.add_comm, Nat.add_left_comm]
          · cases ih rfl hfinal with
            | intro n hn =>
                cases hn with
                | intro k hk =>
                    exists n + 1
                    exists k + 2
                    constructor
                    · omega
                    constructor
                    · omega
                    · simp [Word.Concat, Word.RepeatSymbol, Word.Length] at hk ⊢
                      rw [hk.right.right]
                      simp [Section01.replicate_succ_eq_cons,
                        Nat.add_comm, Nat.add_left_comm]
      | epsilon htrans =>
          cases hstate
          cases htrans
          exists 0
          exists 0
          constructor
          · omega
          constructor
          · omega
          · have hpop := range12PDA_pop_accepts_only_config hrest rfl hfinal
            simpa [Word.Concat, Word.RepeatSymbol, Word.Length] using hpop

theorem range12PDA_accepts_only_range_words {w : Word Section01.AB}
    (h : PDA.Accepts Range12PDA w) :
    w ∈ Range12Language := by
  cases h with
  | intro q hq =>
      cases hq.left
      have hshape := range12PDA_push_accepts_only_config hq.right rfl rfl
      cases hshape with
      | intro n hn =>
          cases hn with
          | intro k hk =>
              exists n
              exists k
              constructor
              · exact hk.left
              constructor
              · exact hk.right.left
              · simpa [PDA.initial, AnBmWord, Word.Length, Word.Concat]
                  using hk.right.right

theorem range12PDA_accepted_language_exact (w : Word Section01.AB) :
    w ∈ PDA.AcceptedLanguage Range12PDA <-> w ∈ Range12Language := by
  constructor
  · exact range12PDA_accepts_only_range_words
  · intro hw
    cases hw with
    | intro n hn =>
        cases hn with
        | intro m hm =>
            rw [hm.right.right]
            exact range12PDA_accepts_range_words hm.left hm.right.left

end Section04
end Chapter04
end Book
end FoC
