import FoC.Book.Chapter04.Section04.HalfRange

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section04

open Languages
open Grammars

/-!
# A Deterministic {lit}`a^n b^n` PDA

This variant removes epsilon guessing: the first {lit}`b` deterministically switches
from pushing to popping. It illustrates the deterministic vocabulary introduced
earlier in the section.
-/

inductive DetAnBnPDAState where
  | read
  | pop
deriving DecidableEq

namespace DetAnBnPDAState

def finite : Foundation.FiniteType DetAnBnPDAState where
  elems := [read, pop]
  complete := by
    intro q
    cases q <;> simp

end DetAnBnPDAState

inductive DetAnBnPDATransition :
    DetAnBnPDAState -> Option Section01.AB -> Word AnBnPDAStack ->
      DetAnBnPDAState -> Word AnBnPDAStack -> Prop where
  | readA :
      DetAnBnPDATransition DetAnBnPDAState.read (some Section01.AB.a) []
        DetAnBnPDAState.read [AnBnPDAStack.marker]
  | firstB :
      DetAnBnPDATransition DetAnBnPDAState.read (some Section01.AB.b)
        [AnBnPDAStack.marker] DetAnBnPDAState.pop []
  | popB :
      DetAnBnPDATransition DetAnBnPDAState.pop (some Section01.AB.b)
        [AnBnPDAStack.marker] DetAnBnPDAState.pop []

def DetAnBnPDA : PDA Section01.AB AnBnPDAStack DetAnBnPDAState where
  start := DetAnBnPDAState.read
  transition := DetAnBnPDATransition
  accept := fun q => q = DetAnBnPDAState.read ∨ q = DetAnBnPDAState.pop
  statesFinite := DetAnBnPDAState.finite

/-!
The deterministic machine has no epsilon choice for when to switch. It keeps
reading {lit}`a`s until it sees the first {lit}`b`; that first {lit}`b` both
changes state and pops one marker. Because the transition relation has no
alternative in a given situation, the language proof also establishes the
deterministic behavior expected in the textbook discussion.
-/

theorem detAnBnPDA_push_as (n : Nat) (rest : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Computes DetAnBnPDA
      { state := DetAnBnPDAState.read,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
        stack := stack }
      { state := DetAnBnPDAState.read,
        unread := rest,
        stack := Word.Concat (AnBnPDAStackWord n) stack } := by
  induction n generalizing stack with
  | zero =>
      simp [Word.Concat, Word.RepeatSymbol, AnBnPDAStackWord]
      exact PDA.Computes.refl _
  | succ n ih =>
      have hstep : PDA.Step DetAnBnPDA
          { state := DetAnBnPDAState.read,
            unread := Section01.AB.a ::
              Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
            stack := stack }
          { state := DetAnBnPDAState.read,
            unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest,
            stack := AnBnPDAStack.marker :: stack } := by
        exact PDA.Step.read (M := DetAnBnPDA)
          (unread := Word.Concat (Word.RepeatSymbol Section01.AB.a n) rest)
          (restStack := stack) DetAnBnPDATransition.readA
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

theorem detAnBnPDA_first_b (rest : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Step DetAnBnPDA
      { state := DetAnBnPDAState.read,
        unread := Section01.AB.b :: rest,
        stack := AnBnPDAStack.marker :: stack }
      { state := DetAnBnPDAState.pop, unread := rest, stack := stack } := by
  simpa [Word.Concat] using
    (PDA.Step.read (M := DetAnBnPDA) (unread := rest)
      (restStack := stack) DetAnBnPDATransition.firstB)

theorem detAnBnPDA_pop_bs (n : Nat) (rest : Word Section01.AB)
    (stack : Word AnBnPDAStack) :
    PDA.Computes DetAnBnPDA
      { state := DetAnBnPDAState.pop,
        unread := Word.Concat (Word.RepeatSymbol Section01.AB.b n) rest,
        stack := Word.Concat (AnBnPDAStackWord n) stack }
      { state := DetAnBnPDAState.pop, unread := rest, stack := stack } := by
  induction n generalizing stack with
  | zero =>
      simp [Word.Concat, Word.RepeatSymbol, AnBnPDAStackWord]
      exact PDA.Computes.refl _
  | succ n ih =>
      have hstep : PDA.Step DetAnBnPDA
          { state := DetAnBnPDAState.pop,
            unread := Section01.AB.b ::
              Word.Concat (Word.RepeatSymbol Section01.AB.b n) rest,
            stack := AnBnPDAStack.marker ::
              Word.Concat (AnBnPDAStackWord n) stack }
          { state := DetAnBnPDAState.pop,
            unread := Word.Concat (Word.RepeatSymbol Section01.AB.b n) rest,
            stack := Word.Concat (AnBnPDAStackWord n) stack } := by
        exact PDA.Step.read (M := DetAnBnPDA)
          (unread := Word.Concat (Word.RepeatSymbol Section01.AB.b n) rest)
          (restStack := Word.Concat (AnBnPDAStackWord n) stack)
          DetAnBnPDATransition.popB
      exact PDA.Computes.step hstep (ih stack)

theorem detAnBnPDA_accepts_anbn_words (n : Nat) :
    PDA.Accepts DetAnBnPDA (Section01.AnBnWord n) := by
  cases n with
  | zero =>
      exists DetAnBnPDAState.read
      constructor
      · exact Or.inl rfl
      · simp [Section01.AnBnWord, PDA.initial, Word.Concat, Word.RepeatSymbol]
        exact PDA.Computes.refl _
  | succ n =>
      exists DetAnBnPDAState.pop
      constructor
      · exact Or.inr rfl
      · unfold Section01.AnBnWord PDA.initial
        have hpush :=
          detAnBnPDA_push_as (n + 1)
            (Word.RepeatSymbol Section01.AB.b (n + 1))
            ([] : Word AnBnPDAStack)
        have hfirst : PDA.Computes DetAnBnPDA
            { state := DetAnBnPDAState.read,
              unread := Section01.AB.b :: Word.RepeatSymbol Section01.AB.b n,
              stack := Word.Concat (AnBnPDAStackWord (n + 1)) [] }
            { state := DetAnBnPDAState.pop,
              unread := Word.RepeatSymbol Section01.AB.b n,
              stack := Word.Concat (AnBnPDAStackWord n) [] } := by
          simpa [AnBnPDAStackWord, Word.Concat, Word.RepeatSymbol] using
            PDA.computes_of_step (detAnBnPDA_first_b
              (Word.RepeatSymbol Section01.AB.b n)
              (Word.Concat (AnBnPDAStackWord n) []))
        have hpop : PDA.Computes DetAnBnPDA
            { state := DetAnBnPDAState.pop,
              unread := Word.RepeatSymbol Section01.AB.b n,
              stack := Word.Concat (AnBnPDAStackWord n) [] }
            { state := DetAnBnPDAState.pop, unread := [], stack := [] } := by
          simpa [Word.Concat] using detAnBnPDA_pop_bs n [] []
        exact PDA.computes_trans hpush
          (PDA.computes_trans hfirst hpop)

/-!
As with the nondeterministic version, the reverse direction is a state-by-state
shape proof. The read state can only consume {lit}`a`s or the first {lit}`b`;
the pop state can only consume the remaining {lit}`b`s while removing markers.
-/

def DetAnBnReadFinalTail :
    DetAnBnPDAState -> Word Section01.AB -> Word AnBnPDAStack -> Prop
  | DetAnBnPDAState.read, unread, stack => unread = [] ∧ stack = []
  | DetAnBnPDAState.pop, _, _ => False

def DetAnBnPopFinalTail :
    DetAnBnPDAState -> Word Section01.AB -> Word AnBnPDAStack -> Prop
  | DetAnBnPDAState.pop, unread, stack =>
      unread = Word.RepeatSymbol Section01.AB.b (Word.Length stack)
  | DetAnBnPDAState.read, unread, stack =>
      exists n,
        unread =
          Word.Concat (Word.RepeatSymbol Section01.AB.a n)
            (Word.RepeatSymbol Section01.AB.b (Word.Length stack + n))

theorem detAnBnPDA_computes_read_final_shape_config
    {c d : PDA.Configuration Section01.AB AnBnPDAStack DetAnBnPDAState}
    (h : PDA.Computes DetAnBnPDA c d)
    (hfinal :
      d = { state := DetAnBnPDAState.read, unread := [], stack := [] }) :
    DetAnBnReadFinalTail c.state c.unread c.stack := by
  induction h with
  | refl c =>
      rw [hfinal]
      simp [DetAnBnReadFinalTail]
  | step hstep hrest ih =>
      cases hstep with
      | read htrans =>
          cases htrans with
          | readA =>
              have htail := ih hfinal
              cases htail.right
          | firstB =>
              exact False.elim (ih hfinal)
          | popB =>
              exact False.elim (ih hfinal)
      | epsilon htrans =>
          cases htrans

theorem detAnBnPDA_computes_pop_final_shape_config
    {c d : PDA.Configuration Section01.AB AnBnPDAStack DetAnBnPDAState}
    (h : PDA.Computes DetAnBnPDA c d)
    (hfinal :
      d = { state := DetAnBnPDAState.pop, unread := [], stack := [] }) :
    DetAnBnPopFinalTail c.state c.unread c.stack := by
  induction h with
  | refl c =>
      rw [hfinal]
      simp [DetAnBnPopFinalTail, Word.Length, Word.RepeatSymbol]
  | step hstep hrest ih =>
      cases hstep with
      | read htrans =>
          cases htrans with
          | readA =>
              cases ih hfinal with
              | intro n hn =>
                  exists n + 1
                  simp [Word.Length, Word.Concat, Word.RepeatSymbol] at hn ⊢
                  rw [hn]
                  simp [Section01.replicate_succ_eq_cons,
                    Nat.add_comm, Nat.add_left_comm]
          | firstB =>
              have htail := ih hfinal
              exists 0
              simp [DetAnBnPopFinalTail, Word.Length, Word.Concat,
                Word.RepeatSymbol] at htail ⊢
              rw [htail]
              rw [List.replicate_succ]
          | popB =>
              have htail := ih hfinal
              simp [DetAnBnPopFinalTail, Word.Concat, Word.Length,
                Word.RepeatSymbol] at htail ⊢
              rw [htail]
              rw [List.replicate_succ]
      | epsilon htrans =>
          cases htrans

theorem detAnBnPDA_accepts_only_anbn_words {w : Word Section01.AB}
    (h : PDA.Accepts DetAnBnPDA w) :
    exists n, w = Section01.AnBnWord n := by
  cases h with
  | intro q hq =>
      cases hq.left with
      | inl hread =>
          subst q
          have hshape :=
            detAnBnPDA_computes_read_final_shape_config hq.right rfl
          exists 0
          simpa [PDA.initial, DetAnBnReadFinalTail, Section01.AnBnWord,
            Word.Concat, Word.RepeatSymbol] using hshape.left
      | inr hpop =>
          subst q
          have hshape :=
            detAnBnPDA_computes_pop_final_shape_config hq.right rfl
          cases hshape with
          | intro n hn =>
              exists n
              simpa [PDA.initial, DetAnBnPopFinalTail, Section01.AnBnWord,
                Word.Length, Word.Concat] using hn

theorem detAnBnPDA_accepted_language_exact (w : Word Section01.AB) :
    w ∈ PDA.AcceptedLanguage DetAnBnPDA <->
      exists n, w = Section01.AnBnWord n := by
  constructor
  · exact detAnBnPDA_accepts_only_anbn_words
  · intro h
    cases h with
        | intro n hn =>
            rw [hn]
            exact detAnBnPDA_accepts_anbn_words n

def AnBnBlockLanguage : Language Section01.AB :=
  fun w => exists n, w = Section01.AnBnWord n

theorem detAnBnPDA_deterministic :
    DeterministicPDA DetAnBnPDA := by
  intro c d e hd he
  rcases PDA.step_cases hd with hreadD | hepsD
  · rcases hreadD with
      ⟨qD, rD, aD, unreadD, popD, pushD, restD,
        htransD, hcD, hdD⟩
    rcases PDA.step_cases he with hreadE | hepsE
    · rcases hreadE with
        ⟨qE, rE, aE, unreadE, popE, pushE, restE,
          htransE, hcE, heE⟩
      subst d
      subst e
      subst c
      cases htransD <;> cases htransE <;> cases hcE <;> rfl
    · rcases hepsE with
        ⟨qE, rE, unreadE, popE, pushE, restE,
          htransE, hcE, heE⟩
      cases htransE
  · rcases hepsD with
      ⟨qD, rD, unreadD, popD, pushD, restD,
        htransD, hcD, hdD⟩
    cases htransD

theorem anbn_block_language_deterministic_pda_recognizable :
    DeterministicPDARecognizable AnBnBlockLanguage := by
  exists AnBnPDAStack
  exists DetAnBnPDAState
  exists DetAnBnPDA
  constructor
  · exact detAnBnPDA_deterministic
  · intro w
    exact detAnBnPDA_accepted_language_exact w

end Section04
end Chapter04
end Book
end FoC
