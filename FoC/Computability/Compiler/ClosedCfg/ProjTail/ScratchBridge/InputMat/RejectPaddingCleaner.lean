import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.Shapes

set_option maxRecDepth 10000

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat
namespace RejectPaddingCleaner

def scanWord : Nat := 0
def scanGap : Nat := 1
def eraseSecond : Nat := 2
def eraseThird : Nat := 3
def eraseFourth : Nat := 4
def returnGap : Nat := 5
def halt : Nat := 6

/--
Erase the four visible reject-hit cells behind the source boundary, then
return to that boundary.  The machine deliberately ignores the length of the
blank gap: on this branch the four-cell hit code is its first visible suffix.
-/
def description : MachineDescription where
  stateCount := 7
  start := scanWord
  halt := halt
  transitions :=
    [ transition scanWord (some false) (some false) Direction.right scanWord
    , transition scanWord (some true) (some true) Direction.right scanWord
    , transition scanWord none none Direction.right scanGap
    , transition scanGap none none Direction.right scanGap
    , transition scanGap (some false) none Direction.right eraseSecond
    , transition scanGap (some true) none Direction.right eraseSecond
    , transition eraseSecond (some false) none Direction.right eraseThird
    , transition eraseSecond (some true) none Direction.right eraseThird
    , transition eraseThird (some false) none Direction.right eraseFourth
    , transition eraseThird (some true) none Direction.right eraseFourth
    , transition eraseFourth (some false) none Direction.left returnGap
    , transition eraseFourth (some true) none Direction.left returnGap
    , transition returnGap none none Direction.left returnGap
    , transition returnGap (some false) (some false) Direction.right halt
    , transition returnGap (some true) (some true) Direction.right halt ]

theorem description_subroutineReady : description.SubroutineReady := by
  exact machineDescription_subroutineReady_of_transition_checks
    description (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)

def scanSourceTape
    (left : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) : Tape Bool :=
  tapeAtCells left
    (List.append (bits.map some) (none :: padding))

theorem scanWord_step
    (left : List (Option Bool)) (bit : Bool) (rest : Word Bool)
    (padding : List (Option Bool)) :
    description.runConfig 1
        { state := scanWord
          tape := scanSourceTape left (bit :: rest) padding } =
      { state := scanWord
        tape := scanSourceTape (some bit :: left) rest padding } := by
  cases bit <;> cases rest <;> cases padding <;>
    simp [description, scanWord, scanGap, eraseSecond, eraseThird,
      eraseFourth, returnGap, halt, scanSourceTape, runConfig,
      stepConfig, lookupTransition, Matches, transition, Tape.read,
      Tape.write, Tape.move, Tape.moveRight, tapeAtCells]

theorem scanWord_run
    (left : List (Option Bool)) (bits : Word Bool)
    (padding : List (Option Bool)) :
    description.runConfig bits.length
        { state := scanWord
          tape := scanSourceTape left bits padding } =
      { state := scanWord
        tape :=
          tapeAtCells
            (List.append (bits.reverse.map some) left)
            (none :: padding) } := by
  induction bits generalizing left with
  | nil =>
      simp [runConfig, scanSourceTape]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by simp; lia]
      rw [runConfig_add]
      rw [scanWord_step]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

theorem scanBoundary_step
    (left padding : List (Option Bool)) :
    description.runConfig 1
        { state := scanWord
          tape := tapeAtCells left (none :: padding) } =
      { state := scanGap
        tape := tapeAtCells (none :: left) padding } := by
  cases left <;> cases padding <;>
    simp [description, scanWord, scanGap, eraseSecond, eraseThird,
      eraseFourth, returnGap, halt, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveRight, tapeAtCells]

theorem scanGap_step_blank
    (left padding : List (Option Bool)) :
    description.runConfig 1
        { state := scanGap
          tape := tapeAtCells left (none :: padding) } =
      { state := scanGap
        tape := tapeAtCells (none :: left) padding } := by
  cases left <;> cases padding <;>
    simp [description, scanWord, scanGap, eraseSecond, eraseThird,
      eraseFourth, returnGap, halt, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveRight, tapeAtCells]

theorem replicate_none_append_cons
    (n : Nat) (left : List (Option Bool)) :
    List.append (List.replicate n (none : Option Bool)) (none :: left) =
      none :: List.append (List.replicate n (none : Option Bool)) left := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ]
      exact congrArg (List.cons none) ih

theorem scanGap_run_blanks
    (left : List (Option Bool)) (n : Nat)
    (first : Bool) (rest : List (Option Bool)) :
    description.runConfig n
        { state := scanGap
          tape :=
            tapeAtCells left
              (List.append
                (List.replicate n (none : Option Bool))
                (some first :: rest)) } =
      { state := scanGap
        tape :=
          tapeAtCells
            (List.append
              (List.replicate n (none : Option Bool)) left)
            (some first :: rest) } := by
  induction n generalizing left with
  | zero =>
      simp [runConfig]
  | succ n ih =>
      rw [List.replicate_succ]
      rw [show n + 1 = 1 + n by lia]
      rw [runConfig_add]
      change
        description.runConfig n
            (description.runConfig 1
              { state := scanGap
                tape := tapeAtCells left
                  (none ::
                    List.append (List.replicate n (none : Option Bool))
                      (some first :: rest)) }) = _
      rw [scanGap_step_blank]
      rw [ih (none :: left)]
      rw [replicate_none_append_cons]
      rfl

theorem eraseFour_run
    (left : List (Option Bool))
    (bit0 bit1 bit2 bit3 : Bool)
    (right : List (Option Bool)) :
    description.runConfig 4
        { state := scanGap
          tape := tapeAtCells left
            (some bit0 :: some bit1 :: some bit2 :: some bit3 :: right) } =
      { state := returnGap
        tape := tapeAtCells
          (none :: none :: left) (none :: none :: right) } := by
  cases bit0 <;> cases bit1 <;> cases bit2 <;> cases bit3 <;>
    cases left <;> cases right <;>
      simp [description, scanWord, scanGap, eraseSecond, eraseThird,
        eraseFourth, returnGap, halt, runConfig, stepConfig,
        lookupTransition, Matches, transition, Tape.read, Tape.write,
        Tape.move, Tape.moveLeft, Tape.moveRight, tapeAtCells]

theorem returnGap_step_blank
    (left right : List (Option Bool)) :
    description.runConfig 1
        { state := returnGap
          tape := tapeAtCells left (none :: right) } =
      { state := returnGap
        tape := Tape.move Direction.left (tapeAtCells left (none :: right)) } := by
  cases left <;> cases right <;>
    simp [description, scanWord, scanGap, eraseSecond, eraseThird,
      eraseFourth, returnGap, halt, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, tapeAtCells]

theorem returnGap_run_blanks
    (left : List (Option Bool)) (last : Bool)
    (n : Nat) (right : List (Option Bool)) :
    description.runConfig (n + 1)
        { state := returnGap
          tape :=
            tapeAtCells
              (List.append
                (List.replicate n (none : Option Bool))
                (some last :: left))
              (none :: right) } =
      { state := returnGap
        tape :=
          tapeAtCells left
            (some last ::
              List.append
                (List.replicate (n + 1) (none : Option Bool)) right) } := by
  induction n generalizing right with
  | zero =>
      rw [Nat.zero_add]
      change
        description.runConfig 1
            { state := returnGap
              tape := tapeAtCells (some last :: left) (none :: right) } = _
      rw [returnGap_step_blank]
      simp [Tape.move, Tape.moveLeft, tapeAtCells]
  | succ n ih =>
      rw [List.replicate_succ]
      rw [show n + 1 + 1 = 1 + (n + 1) by lia]
      rw [runConfig_add]
      change
        description.runConfig (n + 1)
            (description.runConfig 1
              { state := returnGap
                tape :=
                  tapeAtCells
                    (none ::
                      List.append
                        (List.replicate n (none : Option Bool))
                        (some last :: left))
                    (none :: right) }) = _
      rw [returnGap_step_blank]
      change
        description.runConfig (n + 1)
            { state := returnGap
              tape :=
                tapeAtCells
                  (List.append
                    (List.replicate n (none : Option Bool))
                    (some last :: left))
                  (none :: none :: right) } = _
      rw [ih (none :: right)]
      congr 3
      rw [replicate_none_append_cons]
      rw [show 1 + (n + 1) = (n + 1) + 1 by lia,
        List.replicate_succ, List.replicate_succ]
      rfl

theorem returnGap_finish
    (left : List (Option Bool)) (last : Bool)
    (right : List (Option Bool)) :
    description.runConfig 1
        { state := returnGap
          tape := tapeAtCells left (some last :: right) } =
      { state := halt
        tape := tapeAtCells (some last :: left) right } := by
  cases last <;> cases left <;> cases right <;>
    simp [description, scanWord, scanGap, eraseSecond, eraseThird,
      eraseFourth, returnGap, halt, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveRight, tapeAtCells]

theorem description_run
    (pref : Word Bool) (last : Bool) (gap : Nat)
    (bit0 bit1 bit2 bit3 : Bool) :
    description.runConfig
        ((List.append pref [last]).length + 2 * gap + 10)
        { state := description.start
          tape :=
            rightEdgeRewindTargetTape
              (List.append pref [last])
              (List.append
                (List.replicate gap (none : Option Bool))
                [some bit0, some bit1, some bit2, some bit3, none, none]) } =
      { state := description.halt
        tape :=
          tapeAtCells
            (List.append
              ((List.append pref [last]).reverse.map some) [none])
            (none ::
              List.replicate (gap + 6) (none : Option Bool)) } := by
  rw [show
      (List.append pref [last]).length + 2 * gap + 10 =
        (List.append pref [last]).length +
          (1 + (gap + (4 + ((gap + 4) + 1)))) by
    simp
    lia]
  rw [runConfig_add]
  change
    description.runConfig (1 + (gap + (4 + (gap + 4 + 1))))
        (description.runConfig (List.append pref [last]).length
          { state := scanWord
            tape :=
              scanSourceTape [none] (List.append pref [last])
                (List.append
                  (List.replicate gap (none : Option Bool))
                  [some bit0, some bit1, some bit2, some bit3,
                    none, none]) }) = _
  rw [scanWord_run]
  rw [runConfig_add]
  rw [scanBoundary_step]
  rw [runConfig_add]
  change
    description.runConfig (4 + (gap + 4 + 1))
        (description.runConfig gap
          { state := scanGap
            tape :=
              tapeAtCells
                (none ::
                  List.append
                    ((List.append pref [last]).reverse.map some) [none])
                (List.append
                  (List.replicate gap (none : Option Bool))
                  [some bit0, some bit1, some bit2, some bit3,
                    none, none]) }) = _
  rw [scanGap_run_blanks]
  rw [runConfig_add]
  change
    description.runConfig (gap + 4 + 1)
        (description.runConfig 4
          { state := scanGap
            tape :=
              tapeAtCells
                (List.append
                  (List.replicate gap (none : Option Bool))
                  (none ::
                    List.append
                      ((List.append pref [last]).reverse.map some) [none]))
                (some bit0 :: some bit1 :: some bit2 :: some bit3 ::
                  [none, none]) }) = _
  rw [eraseFour_run]
  rw [runConfig_add]
  change
    description.runConfig 1
        (description.runConfig (gap + 4)
          { state := returnGap
            tape :=
              tapeAtCells
                (none :: none ::
                  List.append
                    (List.replicate gap (none : Option Bool))
                    (none ::
                      List.append
                        ((List.append pref [last]).reverse.map some)
                        [none]))
                [none, none, none, none] }) = _
  have hleft :
      none :: none ::
          List.append
            (List.replicate gap (none : Option Bool))
            (none ::
              List.append
                ((List.append pref [last]).reverse.map some) [none]) =
        List.append
          (List.replicate (gap + 3) (none : Option Bool))
          (some last ::
            List.append (pref.reverse.map some) [none]) := by
    rw [show (List.append pref [last]).reverse =
        last :: pref.reverse by simp]
    simp only [List.map_cons]
    rw [replicate_none_append_cons]
    rw [show gap + 3 = ((gap + 1) + 1) + 1 by lia]
    rw [List.replicate_succ, List.replicate_succ, List.replicate_succ]
    rfl
  rw [hleft]
  rw [show gap + 4 = (gap + 3) + 1 by lia]
  rw [returnGap_run_blanks]
  rw [returnGap_finish]
  congr 3
  · simp [List.reverse_append]
  · change
      List.append
          (List.replicate (gap + 4) (none : Option Bool))
          (List.replicate 3 (none : Option Bool)) =
        List.replicate (gap + 7) (none : Option Bool)
    rw [replicate_none_append_replicate_none]

theorem description_haltsFromTape
    (pref : Word Bool) (last : Bool) (gap : Nat)
    (bit0 bit1 bit2 bit3 : Bool) :
    description.HaltsFromTape
      (rightEdgeRewindTargetTape
        (List.append pref [last])
        (List.append
          (List.replicate gap (none : Option Bool))
          [some bit0, some bit1, some bit2, some bit3, none, none]))
      (tapeAtCells
        (List.append
          ((List.append pref [last]).reverse.map some) [none])
        (none :: List.replicate (gap + 6) (none : Option Bool))) := by
  refine
    ⟨(List.append pref [last]).length + 2 * gap + 10, ?_⟩
  constructor <;> rw [description_run]

def cleanedBoundaryTape
    (pref : Word Bool) (last : Bool) (gap : Nat) : Tape Bool :=
  tapeAtCells
    (List.append ((List.append pref [last]).reverse.map some) [none])
    (none :: List.replicate (gap + 6) (none : Option Bool))

def cleanedLastBitTape
    (pref : Word Bool) (last : Bool) (gap : Nat) : Tape Bool :=
  tapeAtCells
    (List.append (pref.reverse.map some) [none])
    (some last :: none ::
      List.replicate (gap + 6) (none : Option Bool))

theorem cleanedBoundaryTape_move_left
    (pref : Word Bool) (last : Bool) (gap : Nat) :
    Tape.move Direction.left (cleanedBoundaryTape pref last gap) =
      cleanedLastBitTape pref last gap := by
  simp [cleanedBoundaryTape, cleanedLastBitTape, List.reverse_append,
    Tape.move, Tape.moveLeft, tapeAtCells]

theorem cleanedBoundaryTape_bridge
    (pref : Word Bool) (last : Bool) (gap : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right (cleanedBoundaryTape pref last gap)) =
      cleanedBoundaryTape pref last gap := by
  unfold cleanedBoundaryTape
  rw [show gap + 6 = (gap + 5) + 1 by lia, List.replicate_succ]
  simp [Tape.move, Tape.moveLeft, Tape.moveRight,
    tapeAtCells, List.reverse_append]

theorem cleanedLastBitTape_bridge
    (pref : Word Bool) (last : Bool) (gap : Nat) :
    Tape.move Direction.left
        (Tape.move Direction.right (cleanedLastBitTape pref last gap)) =
      cleanedLastBitTape pref last gap := by
  cases pref <;> cases last <;> cases gap <;>
    simp [cleanedLastBitTape, Tape.move, Tape.moveLeft, Tape.moveRight,
      tapeAtCells]

def cleanAndRewindDescription : MachineDescription :=
  canonicalSeqDescription
    (canonicalSeqDescription description leftMoveOnceDescription)
    rightEdgeRewindDescription

theorem cleanAndRewindDescription_subroutineReady :
    cleanAndRewindDescription.SubroutineReady := by
  exact
    canonicalSeqDescription_subroutineReady
      (canonicalSeqDescription_subroutineReady
        description_subroutineReady
        leftMoveOnceDescription_subroutineReady)
      rightEdgeRewindDescription_subroutineReady

theorem cleanerThenLeftMove_haltsFromTape
    (pref : Word Bool) (last : Bool) (gap : Nat)
    (bit0 bit1 bit2 bit3 : Bool) :
    (canonicalSeqDescription description leftMoveOnceDescription).HaltsFromTape
      (rightEdgeRewindTargetTape
        (List.append pref [last])
        (List.append
          (List.replicate gap (none : Option Bool))
          [some bit0, some bit1, some bit2, some bit3, none, none]))
      (cleanedLastBitTape pref last gap) := by
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      description_subroutineReady
      leftMoveOnceDescription_subroutineReady
      (by
        simpa [cleanedBoundaryTape] using
          description_haltsFromTape pref last gap bit0 bit1 bit2 bit3)
      (cleanedBoundaryTape_bridge pref last gap)
      (by
        rw [← cleanedBoundaryTape_move_left]
        exact
          leftMoveOnceDescription_haltsFromTape
            (cleanedBoundaryTape pref last gap))

theorem cleanAndRewindDescription_haltsFromTape
    (pref : Word Bool) (last : Bool) (gap : Nat)
    (bit0 bit1 bit2 bit3 : Bool) :
    cleanAndRewindDescription.HaltsFromTape
      (rightEdgeRewindTargetTape
        (List.append pref [last])
        (List.append
          (List.replicate gap (none : Option Bool))
          [some bit0, some bit1, some bit2, some bit3, none, none]))
      (rightEdgeRewindTargetTape
        (List.append pref [last])
        (List.replicate (gap + 6) (none : Option Bool))) := by
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      (canonicalSeqDescription_subroutineReady
        description_subroutineReady
        leftMoveOnceDescription_subroutineReady)
      rightEdgeRewindDescription_subroutineReady
      (cleanerThenLeftMove_haltsFromTape
        pref last gap bit0 bit1 bit2 bit3)
      (cleanedLastBitTape_bridge pref last gap)
      (by
        simpa [cleanedLastBitTape] using
          rightEdgeRewindDescription_haltsFrom_lastBitBoundary
            pref.reverse last
            (List.replicate (gap + 6) (none : Option Bool)))

theorem exists_eq_append_last_of_ne_nil
    (word : Word Bool) (hword : word ≠ []) :
    exists pref : Word Bool, exists last : Bool,
      word = List.append pref [last] := by
  induction word with
  | nil => exact (hword rfl).elim
  | cons first rest ih =>
      cases rest with
      | nil => exact ⟨[], first, rfl⟩
      | cons second tail =>
          rcases ih (by simp) with ⟨pref, last, hrest⟩
          exact ⟨first :: pref, last, by simp [hrest]⟩

theorem cleanAndRewindDescription_haltsFromTape_nonempty
    (word : Word Bool) (hword : word ≠ []) (gap : Nat)
    (bit0 bit1 bit2 bit3 : Bool) :
    cleanAndRewindDescription.HaltsFromTape
      (rightEdgeRewindTargetTape word
        (List.append
          (List.replicate gap (none : Option Bool))
          [some bit0, some bit1, some bit2, some bit3, none, none]))
      (rightEdgeRewindTargetTape word
        (List.replicate (gap + 6) (none : Option Bool))) := by
  rcases exists_eq_append_last_of_ne_nil word hword with
    ⟨pref, last, rfl⟩
  exact
    cleanAndRewindDescription_haltsFromTape
      pref last gap bit0 bit1 bit2 bit3

theorem rightEdgeRewindTargetTape_replicate_equiv_input_cons
    (first : Bool) (rest : Word Bool) (padding : Nat) :
    Tape.Equiv
      (rightEdgeRewindTargetTape (first :: rest)
        (List.replicate padding (none : Option Bool)))
      (Tape.input (first :: rest)) := by
  simp only [Tape.Equiv, rightEdgeRewindTargetTape, tapeAtCells, Tape.input]
  constructor
  · rfl
  · constructor
    · rfl
    · simpa [List.replicate_succ, List.append_assoc] using
        FoC.Computability.dropTrailingNone_append_replicate_none
          (rest.map some) (padding + 1)

theorem exists_four_bits_of_length_eq_four
    (bits : Word Bool) (hlength : bits.length = 4) :
    exists bit0 bit1 bit2 bit3 : Bool,
      bits = [bit0, bit1, bit2, bit3] := by
  cases bits with
  | nil => simp at hlength
  | cons bit0 rest0 =>
      cases rest0 with
      | nil => simp at hlength
      | cons bit1 rest1 =>
          cases rest1 with
          | nil => simp at hlength
          | cons bit2 rest2 =>
              cases rest2 with
              | nil => simp at hlength
              | cons bit3 rest3 =>
                  cases rest3 with
                  | nil => exact ⟨bit0, bit1, bit2, bit3, rfl⟩
                  | cons bit4 rest4 => simp at hlength

theorem sourceWord_ne_nil
    (useAccept : Bool) (L : DovetailLayout) :
    sourceWord useAccept L ≠ [] := by
  rw [sourceWord_cons]
  simp

theorem cleanAndRewindDescription_haltsFrom_rejectPadding
    (L : DovetailLayout) (deletedTail : Word Bool) :
    cleanAndRewindDescription.HaltsFromTapeEquiv
      (rightEdgeRewindTargetTape
        (sourceWord false L)
        (countWindowPostFieldDecodedPrefixStructuredSourcePadding
          false L deletedTail))
      (Tape.input (sourceWord false L)) := by
  rcases
      exists_four_bits_of_length_eq_four
        (selectedProjectionPaddedTailCleanupSelectedHitBits false L)
        (selectedHitBits_length false L) with
    ⟨bit0, bit1, bit2, bit3, hbits⟩
  let actual :=
    rightEdgeRewindTargetTape
      (sourceWord false L)
      (List.replicate (deletedTail.length + 4 + 6)
        (none : Option Bool))
  refine ⟨actual, ?_, ?_⟩
  · rw [sourcePadding_reject_closedForm, hbits]
    exact
      cleanAndRewindDescription_haltsFromTape_nonempty
        (sourceWord false L) (sourceWord_ne_nil false L)
        (deletedTail.length + 4) bit0 bit1 bit2 bit3
  · rw [sourceWord_cons]
    exact
      rightEdgeRewindTargetTape_replicate_equiv_input_cons
        false
        (List.append [false, false, false]
          (List.append
            (boolWordRawBitsDecoderEncodedFieldBits (ParsedLayoutBits L))
            (false ::
              countWindowPostFieldDecodedPrefixStructuredSuffixTail false L)))
        (deletedTail.length + 4 + 6)

def CountWindowRejectDetachedHitCleanerSpec
    (cleaner : MachineDescription) : Prop :=
  cleaner.SubroutineReady ∧
    forall input :
      CountWindowPostFieldDecodedPrefixStructuredInputMaterializerInput false,
      cleaner.HaltsFromTapeEquiv
        (countWindowPostFieldDecodedPrefixStructuredBoolWordMaterializerSource
          false input)
        (Tape.input (sourceWord false input.L))

theorem cleanAndRewindDescription_rejectDetachedHitCleanerSpec :
    CountWindowRejectDetachedHitCleanerSpec cleanAndRewindDescription := by
  refine ⟨cleanAndRewindDescription_subroutineReady, ?_⟩
  intro input
  change
    cleanAndRewindDescription.HaltsFromTapeEquiv
      (rightEdgeRewindTargetTape
        (sourceWord false input.L)
        (countWindowPostFieldDecodedPrefixStructuredSourcePadding
          false input.L input.deletedTail))
      (Tape.input (sourceWord false input.L))
  exact
    cleanAndRewindDescription_haltsFrom_rejectPadding
      input.L input.deletedTail

end RejectPaddingCleaner
end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
