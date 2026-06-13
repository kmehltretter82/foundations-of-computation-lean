import FoC.Book.Chapter04.Section04.DeterministicAnBn

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter04
namespace Section04

open Languages
open Grammars

/-!
# Copy Across a Center Marker

The final example recognizes words of the form `w c reverse(w)`. The stack
stores the first half, the center marker switches modes, and the second half
must pop matching symbols in reverse order.
-/

inductive CopyInput where
  | a
  | b
  | c
deriving DecidableEq

inductive CopyPDAState where
  | push
  | pop
deriving DecidableEq

namespace CopyPDAState

def finite : Foundation.FiniteType CopyPDAState where
  elems := [push, pop]
  complete := by
    intro q
    cases q <;> simp

end CopyPDAState

def copyInputOfAB : Section01.AB -> CopyInput
  | Section01.AB.a => CopyInput.a
  | Section01.AB.b => CopyInput.b

def copyInputWord (w : Word Section01.AB) : Word CopyInput :=
  w.map copyInputOfAB

def copyCenteredWord (w : Word Section01.AB) : Word CopyInput :=
  Word.Concat (copyInputWord w)
    (CopyInput.c :: copyInputWord (Word.Reverse w))

inductive CopyPDATransition :
    CopyPDAState -> Option CopyInput -> Word Section01.AB ->
      CopyPDAState -> Word Section01.AB -> Prop where
  | pushA :
      CopyPDATransition CopyPDAState.push (some CopyInput.a) []
        CopyPDAState.push [Section01.AB.a]
  | pushB :
      CopyPDATransition CopyPDAState.push (some CopyInput.b) []
        CopyPDAState.push [Section01.AB.b]
  | readCenter :
      CopyPDATransition CopyPDAState.push (some CopyInput.c) []
        CopyPDAState.pop []
  | popA :
      CopyPDATransition CopyPDAState.pop (some CopyInput.a)
        [Section01.AB.a] CopyPDAState.pop []
  | popB :
      CopyPDATransition CopyPDAState.pop (some CopyInput.b)
        [Section01.AB.b] CopyPDAState.pop []

def CopyPDA : PDA CopyInput Section01.AB CopyPDAState where
  start := CopyPDAState.push
  transition := CopyPDATransition
  accept := fun q => q = CopyPDAState.pop
  statesFinite := CopyPDAState.finite

/-!
The copy PDA uses the stack as a reverse buffer. Before the center marker, it
pushes each {lit}`a` or {lit}`b`. After the center marker, it must read the
matching symbols while popping them, so the second half is the reverse of the
first half.
-/

theorem copyPDA_push_word (w : Word Section01.AB) (rest : Word CopyInput)
    (stack : Word Section01.AB) :
    PDA.Computes CopyPDA
      { state := CopyPDAState.push,
        unread := Word.Concat (copyInputWord w) rest,
        stack := stack }
      { state := CopyPDAState.push,
        unread := rest,
        stack := Word.Concat (Word.Reverse w) stack } := by
  induction w generalizing stack with
  | nil =>
      simp [copyInputWord, Word.Concat, Word.Reverse]
      exact PDA.Computes.refl _
  | cons sym tail ih =>
      cases sym
      · have hstep : PDA.Step CopyPDA
            { state := CopyPDAState.push,
              unread := CopyInput.a :: Word.Concat (copyInputWord tail) rest,
              stack := stack }
            { state := CopyPDAState.push,
              unread := Word.Concat (copyInputWord tail) rest,
              stack := Section01.AB.a :: stack } := by
          exact PDA.Step.read (M := CopyPDA)
            (unread := Word.Concat (copyInputWord tail) rest)
            (restStack := stack) CopyPDATransition.pushA
        have hrest := ih (Section01.AB.a :: stack)
        exact PDA.Computes.step hstep (by
          simpa [copyInputWord, copyInputOfAB, Word.Concat, Word.Reverse,
            List.map_reverse, List.append_assoc] using hrest)
      · have hstep : PDA.Step CopyPDA
            { state := CopyPDAState.push,
              unread := CopyInput.b :: Word.Concat (copyInputWord tail) rest,
              stack := stack }
            { state := CopyPDAState.push,
              unread := Word.Concat (copyInputWord tail) rest,
              stack := Section01.AB.b :: stack } := by
          exact PDA.Step.read (M := CopyPDA)
            (unread := Word.Concat (copyInputWord tail) rest)
            (restStack := stack) CopyPDATransition.pushB
        have hrest := ih (Section01.AB.b :: stack)
        exact PDA.Computes.step hstep (by
          simpa [copyInputWord, copyInputOfAB, Word.Concat, Word.Reverse,
            List.map_reverse, List.append_assoc] using hrest)

theorem copyPDA_read_center (rest : Word CopyInput)
    (stack : Word Section01.AB) :
    PDA.Step CopyPDA
      { state := CopyPDAState.push,
        unread := CopyInput.c :: rest,
        stack := stack }
      { state := CopyPDAState.pop, unread := rest, stack := stack } := by
  simpa [Word.Concat] using
    (PDA.Step.read (M := CopyPDA) (unread := rest)
      (restStack := stack) CopyPDATransition.readCenter)

theorem copyPDA_pop_word (w : Word Section01.AB) (rest : Word CopyInput)
    (stack : Word Section01.AB) :
    PDA.Computes CopyPDA
      { state := CopyPDAState.pop,
        unread := Word.Concat (copyInputWord w) rest,
        stack := Word.Concat w stack }
      { state := CopyPDAState.pop, unread := rest, stack := stack } := by
  induction w generalizing stack with
  | nil =>
      simp [copyInputWord, Word.Concat]
      exact PDA.Computes.refl _
  | cons sym tail ih =>
      cases sym
      · have hstep : PDA.Step CopyPDA
            { state := CopyPDAState.pop,
              unread := CopyInput.a :: Word.Concat (copyInputWord tail) rest,
              stack := Section01.AB.a :: Word.Concat tail stack }
            { state := CopyPDAState.pop,
              unread := Word.Concat (copyInputWord tail) rest,
              stack := Word.Concat tail stack } := by
          exact PDA.Step.read (M := CopyPDA)
            (unread := Word.Concat (copyInputWord tail) rest)
            (restStack := Word.Concat tail stack) CopyPDATransition.popA
        exact PDA.Computes.step hstep (ih stack)
      · have hstep : PDA.Step CopyPDA
            { state := CopyPDAState.pop,
              unread := CopyInput.b :: Word.Concat (copyInputWord tail) rest,
              stack := Section01.AB.b :: Word.Concat tail stack }
            { state := CopyPDAState.pop,
              unread := Word.Concat (copyInputWord tail) rest,
              stack := Word.Concat tail stack } := by
          exact PDA.Step.read (M := CopyPDA)
            (unread := Word.Concat (copyInputWord tail) rest)
            (restStack := Word.Concat tail stack) CopyPDATransition.popB
        exact PDA.Computes.step hstep (ih stack)

theorem copyPDA_accepts_centered_reverse (w : Word Section01.AB) :
    PDA.Accepts CopyPDA (copyCenteredWord w) := by
  exists CopyPDAState.pop
  constructor
  · rfl
  · unfold PDA.initial copyCenteredWord
    have hpush :=
      copyPDA_push_word w
        (CopyInput.c :: copyInputWord (Word.Reverse w))
        ([] : Word Section01.AB)
    have hcenter : PDA.Computes CopyPDA
        { state := CopyPDAState.push,
          unread := CopyInput.c :: copyInputWord (Word.Reverse w),
          stack := Word.Concat (Word.Reverse w) [] }
        { state := CopyPDAState.pop,
          unread := copyInputWord (Word.Reverse w),
          stack := Word.Concat (Word.Reverse w) [] } := by
      exact PDA.computes_of_step
        (copyPDA_read_center (copyInputWord (Word.Reverse w))
          (Word.Concat (Word.Reverse w) []))
    have hpop : PDA.Computes CopyPDA
        { state := CopyPDAState.pop,
          unread := copyInputWord (Word.Reverse w),
          stack := Word.Concat (Word.Reverse w) [] }
        { state := CopyPDAState.pop, unread := [], stack := [] } := by
      simpa [Word.Concat] using copyPDA_pop_word (Word.Reverse w) [] []
    exact PDA.computes_trans hpush
      (PDA.computes_trans hcenter hpop)

/-!
The converse proof again uses a tail predicate: once the machine has crossed
the center marker, every remaining input symbol must match the current stack
top. That forces accepted words to have the form {lit}`w c reverse(w)`.
-/

def CopyCenteredLanguage : Language CopyInput :=
  fun input => exists w : Word Section01.AB, input = copyCenteredWord w

def CopyAcceptedTail :
    CopyPDAState -> Word CopyInput -> Word Section01.AB -> Prop
  | CopyPDAState.pop, unread, stack =>
      unread = copyInputWord stack
  | CopyPDAState.push, unread, stack =>
      exists w : Word Section01.AB,
        unread =
          Word.Concat (copyInputWord w)
            (CopyInput.c ::
              copyInputWord (Word.Concat (Word.Reverse w) stack))

theorem copyPDA_computes_final_shape_config
    {c d : PDA.Configuration CopyInput Section01.AB CopyPDAState}
    (h : PDA.Computes CopyPDA c d)
    (hfinal :
      d = { state := CopyPDAState.pop, unread := [], stack := [] }) :
    CopyAcceptedTail c.state c.unread c.stack := by
  induction h with
  | refl c =>
      rw [hfinal]
      simp [CopyAcceptedTail, copyInputWord]
  | step hstep hrest ih =>
      cases hstep with
      | read htrans =>
          cases htrans with
          | pushA =>
              cases ih hfinal with
              | intro w hw =>
                  exists Section01.AB.a :: w
                  simp [copyInputWord, copyInputOfAB,
                    Word.Concat, Word.Reverse, List.map_reverse,
                    List.append_assoc] at hw ⊢
                  rw [hw]
          | pushB =>
              cases ih hfinal with
              | intro w hw =>
                  exists Section01.AB.b :: w
                  simp [copyInputWord, copyInputOfAB,
                    Word.Concat, Word.Reverse, List.map_reverse,
                    List.append_assoc] at hw ⊢
                  rw [hw]
          | readCenter =>
              have htail := ih hfinal
              exists []
              simp [CopyAcceptedTail, copyInputWord, Word.Concat, Word.Reverse] at htail ⊢
              rw [htail]
          | popA =>
              have htail := ih hfinal
              simp [CopyAcceptedTail, copyInputWord, copyInputOfAB,
                Word.Concat] at htail ⊢
              rw [htail]
          | popB =>
              have htail := ih hfinal
              simp [CopyAcceptedTail, copyInputWord, copyInputOfAB,
                Word.Concat] at htail ⊢
              rw [htail]
      | epsilon htrans =>
          cases htrans

theorem copyPDA_accepts_only_centered_reverse {input : Word CopyInput}
    (h : PDA.Accepts CopyPDA input) :
    input ∈ CopyCenteredLanguage := by
  cases h with
  | intro q hq =>
      cases hq.left
      have hshape := copyPDA_computes_final_shape_config hq.right rfl
      cases hshape with
      | intro w hw =>
          exists w
          simpa [PDA.initial, CopyAcceptedTail, CopyCenteredLanguage,
            copyCenteredWord, Word.Concat] using hw

theorem copyPDA_accepted_language_exact (input : Word CopyInput) :
    input ∈ PDA.AcceptedLanguage CopyPDA <->
      input ∈ CopyCenteredLanguage := by
  constructor
  · exact copyPDA_accepts_only_centered_reverse
  · intro h
    cases h with
    | intro w hw =>
        rw [hw]
        exact copyPDA_accepts_centered_reverse w

theorem copyPDA_deterministic :
    DeterministicPDA CopyPDA := by
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

theorem copy_centered_language_deterministic_pda_recognizable :
    DeterministicPDARecognizable CopyCenteredLanguage := by
  exists Section01.AB
  exists CopyPDAState
  exists CopyPDA
  constructor
  · exact copyPDA_deterministic
  · intro input
    exact copyPDA_accepted_language_exact input

end Section04
end Chapter04
end Book
end FoC
