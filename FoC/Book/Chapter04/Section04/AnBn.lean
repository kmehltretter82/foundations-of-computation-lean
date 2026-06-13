import FoC.Book.Chapter04.Section04.Conversions

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section04

open Languages
open Grammars

/-!
# Concrete PDA Examples

The remainder of the page proves exact languages for concrete machines. Each
example defines a small finite state type, a transition relation, and then two
directions of correctness: accepted computations have the intended word shape,
and every word of the intended shape has an accepting computation.
-/

/-!
# The {lit}`a^n b^n` PDA

This standard PDA pushes one marker for each {lit}`a`, then pops one marker for
each {lit}`b`. Acceptance requires the input and stack to be empty, so the counts
must match.
-/

inductive AnBnPDAStack where
  | marker
deriving DecidableEq

inductive AnBnPDAState where
  | push
  | pop
  | accept
deriving DecidableEq

namespace AnBnPDAState

def finite : Foundation.FiniteType AnBnPDAState where
  elems := [push, pop, accept]
  complete := by
    intro q
    cases q <;> simp

end AnBnPDAState

inductive AnBnPDATransition :
    AnBnPDAState -> Option Section01.AB -> Word AnBnPDAStack ->
      AnBnPDAState -> Word AnBnPDAStack -> Prop where
  | pushA :
      AnBnPDATransition AnBnPDAState.push (some Section01.AB.a) []
        AnBnPDAState.push [AnBnPDAStack.marker]
  | startPop :
      AnBnPDATransition AnBnPDAState.push none []
        AnBnPDAState.pop []
  | popB :
      AnBnPDATransition AnBnPDAState.pop (some Section01.AB.b)
        [AnBnPDAStack.marker] AnBnPDAState.pop []
  | finish :
      AnBnPDATransition AnBnPDAState.pop none []
        AnBnPDAState.accept []

def AnBnPDA : PDA Section01.AB AnBnPDAStack AnBnPDAState where
  start := AnBnPDAState.push
  transition := AnBnPDATransition
  accept := fun q => q = AnBnPDAState.accept
  statesFinite := AnBnPDAState.finite

def AnBnPDAStackWord (n : Nat) : Word AnBnPDAStack :=
  Word.RepeatSymbol AnBnPDAStack.marker n

theorem anbnPDAStackWord_succ (n : Nat) :
    AnBnPDAStack.marker :: AnBnPDAStackWord n =
      AnBnPDAStackWord (n + 1) :=
  rfl

/-!
The acceptance direction is constructive. The lemmas below show how to run the
machine: push one marker for each {lit}`a`, switch to popping, pop one marker
for each {lit}`b`, and finally accept when both the input and stack are empty.
-/

theorem anbnPDA_push_as (n : Nat) (rest : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Computes AnBnPDA
      { state := AnBnPDAState.push,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
        stack := stack }
      { state := AnBnPDAState.push,
        unread := rest,
        stack := Word.Concat (AnBnPDAStackWord n) stack } := by
  induction n generalizing stack with
  | zero =>
      simp [Word.Concat, Word.RepeatSymbol, AnBnPDAStackWord]
      exact PDA.Computes.refl _
  | succ n ih =>
      have hstep : PDA.Step AnBnPDA
          { state := AnBnPDAState.push,
            unread := Section01.AB.a ::
              Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
            stack := stack }
          { state := AnBnPDAState.push,
            unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
            stack := AnBnPDAStack.marker :: stack } := by
        exact PDA.Step.read (M := AnBnPDA)
          (unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest)
          (restStack := stack) AnBnPDATransition.pushA
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

theorem anbnPDA_switch_to_pop (unread : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Step AnBnPDA
      { state := AnBnPDAState.push, unread := unread, stack := stack }
      { state := AnBnPDAState.pop, unread := unread, stack := stack } := by
  simpa [Word.Concat] using
    (PDA.Step.epsilon (M := AnBnPDA) (unread := unread)
      (restStack := stack) AnBnPDATransition.startPop)

theorem anbnPDA_pop_bs (n : Nat) (rest : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Computes AnBnPDA
      { state := AnBnPDAState.pop,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.b n) rest,
        stack := Word.Concat (AnBnPDAStackWord n) stack }
      { state := AnBnPDAState.pop, unread := rest, stack := stack } := by
  induction n generalizing stack with
  | zero =>
      simp [Word.Concat, Word.RepeatSymbol, AnBnPDAStackWord]
      exact PDA.Computes.refl _
  | succ n ih =>
      have hstep : PDA.Step AnBnPDA
          { state := AnBnPDAState.pop,
            unread := Section01.AB.b ::
              Word.Concat (Word.RepeatSymbol Section01.AB.b n) rest,
            stack := AnBnPDAStack.marker ::
              Word.Concat (AnBnPDAStackWord n) stack }
          { state := AnBnPDAState.pop,
            unread := Word.Concat (Word.RepeatSymbol Section01.AB.b n) rest,
            stack := Word.Concat (AnBnPDAStackWord n) stack } := by
        exact PDA.Step.read (M := AnBnPDA)
          (unread := Word.Concat (Word.RepeatSymbol Section01.AB.b n) rest)
          (restStack := Word.Concat (AnBnPDAStackWord n) stack)
          AnBnPDATransition.popB
      exact PDA.Computes.step hstep (ih stack)

theorem anbnPDA_finish :
    PDA.Step AnBnPDA
      { state := AnBnPDAState.pop, unread := [], stack := [] }
      { state := AnBnPDAState.accept, unread := [], stack := [] } := by
  simpa [Word.Concat] using
    (PDA.Step.epsilon (M := AnBnPDA)
      (unread := ([] : Word Section01.AB))
      (restStack := ([] : Word AnBnPDAStack))
      AnBnPDATransition.finish)

theorem anbnPDA_accepts_anbn_words (n : Nat) :
    PDA.Accepts AnBnPDA (Section01.AnBnWord n) := by
  exists AnBnPDAState.accept
  constructor
  · rfl
  · unfold Section01.AnBnWord PDA.initial
    have hpush :=
      anbnPDA_push_as n (Word.RepeatSymbol Section01.AB.b n)
        ([] : Word AnBnPDAStack)
    have hswitch : PDA.Computes AnBnPDA
        { state := AnBnPDAState.push,
          unread := Word.RepeatSymbol Section01.AB.b n,
          stack := Word.Concat (AnBnPDAStackWord n) [] }
        { state := AnBnPDAState.pop,
          unread := Word.RepeatSymbol Section01.AB.b n,
          stack := Word.Concat (AnBnPDAStackWord n) [] } := by
      simpa [Word.Concat] using PDA.computes_of_step
        (anbnPDA_switch_to_pop (Word.RepeatSymbol Section01.AB.b n)
          (AnBnPDAStackWord n))
    have hpop : PDA.Computes AnBnPDA
        { state := AnBnPDAState.pop,
          unread := Word.RepeatSymbol Section01.AB.b n,
          stack := Word.Concat (AnBnPDAStackWord n) [] }
        { state := AnBnPDAState.pop, unread := [], stack := [] } := by
      simpa [Word.Concat] using anbnPDA_pop_bs n [] []
    have hfinish := PDA.computes_of_step anbnPDA_finish
    exact PDA.computes_trans hpush
      (PDA.computes_trans hswitch
        (PDA.computes_trans hpop hfinish))

/-!
The converse direction is a shape argument. Starting in the push state, any
accepting computation must read some number of {lit}`a`s, switch once, and then
read exactly as many {lit}`b`s as there are stack markers.
-/

theorem anbnPDA_accept_state_no_steps
    {w : Word Section01.AB} {stack : Word AnBnPDAStack}
    {c : PDA.Configuration Section01.AB AnBnPDAStack AnBnPDAState} :
    ¬ PDA.Step AnBnPDA
      { state := AnBnPDAState.accept, unread := w, stack := stack } c := by
  intro h
  cases h with
  | read htrans =>
      cases htrans
  | epsilon htrans =>
      cases htrans

theorem anbnPDA_accept_computes_final_config
    {c d : PDA.Configuration Section01.AB AnBnPDAStack AnBnPDAState}
    (h : PDA.Computes AnBnPDA c d)
    (hstate : c.state = AnBnPDAState.accept)
    (hfinal :
      d = { state := AnBnPDAState.accept, unread := [], stack := [] }) :
    c.unread = [] ∧ c.stack = [] := by
  induction h with
  | refl c =>
      rw [hfinal]
      exact And.intro rfl rfl
  | step hstep _ _ =>
      cases hstep with
      | read htrans =>
          cases hstate
          cases htrans
      | epsilon htrans =>
          cases hstate
          cases htrans

theorem anbnPDA_accept_computes_final
    {w : Word Section01.AB} {stack : Word AnBnPDAStack}
    (h : PDA.Computes AnBnPDA
      { state := AnBnPDAState.accept, unread := w, stack := stack }
      { state := AnBnPDAState.accept, unread := [], stack := [] }) :
    w = [] ∧ stack = [] :=
  anbnPDA_accept_computes_final_config h rfl rfl

theorem anbnPDA_pop_accepts_only_config
    {c d : PDA.Configuration Section01.AB AnBnPDAStack AnBnPDAState}
    (h : PDA.Computes AnBnPDA c d)
    (hstate : c.state = AnBnPDAState.pop)
    (hfinal :
      d = { state := AnBnPDAState.accept, unread := [], stack := [] }) :
    c.unread = Word.RepeatSymbol Section01.AB.b (Word.Length c.stack) := by
  induction h with
  | refl c =>
      rw [hfinal] at hstate
      cases hstate
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
          have hfinalSource :=
            anbnPDA_accept_computes_final_config hrest rfl hfinal
          rw [hfinalSource.left, hfinalSource.right]
          rfl

theorem anbnPDA_pop_accepts_only
    {w : Word Section01.AB} {stack : Word AnBnPDAStack}
    (h : PDA.Computes AnBnPDA
      { state := AnBnPDAState.pop, unread := w, stack := stack }
      { state := AnBnPDAState.accept, unread := [], stack := [] }) :
    w = Word.RepeatSymbol Section01.AB.b (Word.Length stack) :=
  anbnPDA_pop_accepts_only_config h rfl rfl

theorem anbnPDA_push_accepts_only_config
    {c d : PDA.Configuration Section01.AB AnBnPDAStack AnBnPDAState}
    (h : PDA.Computes AnBnPDA c d)
    (hstate : c.state = AnBnPDAState.push)
    (hfinal :
      d = { state := AnBnPDAState.accept, unread := [], stack := [] }) :
    exists n,
      c.unread =
        Word.Concat (Word.RepeatSymbol Section01.AB.a n)
          (Word.RepeatSymbol Section01.AB.b (Word.Length c.stack + n)) := by
  induction h with
  | refl c =>
      rw [hfinal] at hstate
      cases hstate
  | step hstep hrest ih =>
      cases hstep with
      | read htrans =>
          cases hstate
          cases htrans
          cases ih rfl hfinal with
          | intro n hn =>
              exists n + 1
              simp [Word.Concat, Word.RepeatSymbol, Word.Length] at hn ⊢
              rw [hn]
              simp [Section01.replicate_succ_eq_cons, Nat.add_comm, Nat.add_left_comm]
      | epsilon htrans =>
          cases hstate
          cases htrans
          exists 0
          have hpop := anbnPDA_pop_accepts_only_config hrest rfl hfinal
          simpa [Word.Concat, Word.RepeatSymbol, Word.Length] using hpop

theorem anbnPDA_push_accepts_only
    {w : Word Section01.AB} {stack : Word AnBnPDAStack}
    (h : PDA.Computes AnBnPDA
      { state := AnBnPDAState.push, unread := w, stack := stack }
      { state := AnBnPDAState.accept, unread := [], stack := [] }) :
    exists n,
      w =
        Word.Concat (Word.RepeatSymbol Section01.AB.a n)
          (Word.RepeatSymbol Section01.AB.b (Word.Length stack + n)) :=
  anbnPDA_push_accepts_only_config h rfl rfl

theorem anbnPDA_accepts_only_anbn_words {w : Word Section01.AB}
    (h : PDA.Accepts AnBnPDA w) :
    exists n, w = Section01.AnBnWord n := by
  cases h with
  | intro q hq =>
      cases hq.left
      have hshape := anbnPDA_push_accepts_only hq.right
      cases hshape with
      | intro n hn =>
          exists n
          simpa [Section01.AnBnWord, Word.Length, Word.Concat,
            Word.RepeatSymbol] using hn

theorem anbnPDA_accepted_language_exact (w : Word Section01.AB) :
    w ∈ PDA.AcceptedLanguage AnBnPDA <->
      exists n, w = Section01.AnBnWord n := by
  constructor
  · exact anbnPDA_accepts_only_anbn_words
  · intro h
    cases h with
    | intro n hn =>
        rw [hn]
        exact anbnPDA_accepts_anbn_words n


end Section04
end Chapter04
end Book
end FoC
