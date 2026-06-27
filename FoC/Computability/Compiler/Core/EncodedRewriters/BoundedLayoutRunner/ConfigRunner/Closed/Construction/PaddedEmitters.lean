import FoC.Computability.Compiler.Core.EncodedRewriters.RightShifted
import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.Spec
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.Parser.Basic
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.PhaseAdapters

set_option doc.verso true

/-!
# Padded emitter tape adapters

This module collects reusable padded-output tape shapes for finite emitters.
The adapters keep exact output content equivalent to the canonical output while
leaving enough trailing blank cells for downstream scanners that need scratch
space.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

def inputWithTrailingBlankPadding
    (w : Word Bool) (padding : Nat) : Tape Bool :=
  match w with
  | [] =>
      { left := []
        head := none
        right := List.replicate padding none }
  | bit :: rest =>
      { left := []
        head := some bit
        right := rest.map some ++ List.replicate padding none }

def inputWithTrailingBlankPaddingCells
    (w : Word Bool) (padding : Nat) : List (Option Bool) :=
  match w with
  | [] => none :: List.replicate padding none
  | bit :: rest =>
      (bit :: rest).map some ++ List.replicate padding none

theorem inputWithTrailingBlankPadding_eq_tapeAtCells
    (w : Word Bool) (padding : Nat) :
    inputWithTrailingBlankPadding w padding =
      DovetailInitialLayoutInitializer.tapeAtCells []
        (inputWithTrailingBlankPaddingCells w padding) := by
  cases w with
  | nil =>
      simp [inputWithTrailingBlankPadding,
        inputWithTrailingBlankPaddingCells,
        DovetailInitialLayoutInitializer.tapeAtCells]
  | cons bit rest =>
      simp [inputWithTrailingBlankPadding,
        inputWithTrailingBlankPaddingCells,
        DovetailInitialLayoutInitializer.tapeAtCells]

theorem inputWithTrailingBlankPadding_move_right_eq_tapeAtCells
    (w : Word Bool) (padding : Nat) :
    Tape.move Direction.right
        (inputWithTrailingBlankPadding w padding) =
      match inputWithTrailingBlankPaddingCells w padding with
      | [] => DovetailInitialLayoutInitializer.tapeAtCells [] []
      | cell :: rest =>
          DovetailInitialLayoutInitializer.tapeAtCells [cell] rest := by
  cases w with
  | nil =>
      cases padding with
      | zero =>
          simp [inputWithTrailingBlankPadding,
            inputWithTrailingBlankPaddingCells,
            DovetailInitialLayoutInitializer.tapeAtCells,
            Tape.move, Tape.moveRight]
      | succ padding =>
          simp [inputWithTrailingBlankPadding,
            inputWithTrailingBlankPaddingCells,
            DovetailInitialLayoutInitializer.tapeAtCells,
            Tape.move, Tape.moveRight, List.replicate_succ]
  | cons bit rest =>
      cases rest with
      | nil =>
          cases padding with
          | zero =>
              simp [inputWithTrailingBlankPadding,
                inputWithTrailingBlankPaddingCells,
                DovetailInitialLayoutInitializer.tapeAtCells,
                Tape.move, Tape.moveRight]
          | succ padding =>
              simp [inputWithTrailingBlankPadding,
                inputWithTrailingBlankPaddingCells,
                DovetailInitialLayoutInitializer.tapeAtCells,
                Tape.move, Tape.moveRight, List.replicate_succ]
      | cons bit' rest =>
          simp [inputWithTrailingBlankPadding,
            inputWithTrailingBlankPaddingCells,
            DovetailInitialLayoutInitializer.tapeAtCells,
            Tape.move, Tape.moveRight]

theorem dropTrailingNone_replicate_none
    (padding : Nat) :
    Tape.dropTrailingNone
        (List.replicate padding (none : Option Bool)) = [] := by
  induction padding with
  | zero =>
      rfl
  | succ padding ih =>
      simp [List.replicate, Tape.dropTrailingNone, ih]

theorem dropTrailingNone_append_replicate_none
    (xs : List (Option Bool)) (padding : Nat) :
    Tape.dropTrailingNone
        (xs ++ List.replicate padding (none : Option Bool)) =
      Tape.dropTrailingNone xs := by
  induction padding generalizing xs with
  | zero =>
      simp
  | succ padding ih =>
      calc
        Tape.dropTrailingNone
            (xs ++ List.replicate (padding + 1) (none : Option Bool)) =
          Tape.dropTrailingNone
            ((xs ++ [none]) ++
              List.replicate padding (none : Option Bool)) := by
            simp [List.replicate_succ, List.append_assoc]
        _ = Tape.dropTrailingNone (xs ++ [none]) :=
          ih (xs ++ [none])
        _ = Tape.dropTrailingNone xs :=
          dropTrailingNone_append_none xs

theorem inputWithTrailingBlankPadding_equiv_input
    (w : Word Bool) (padding : Nat) :
    Tape.Equiv (inputWithTrailingBlankPadding w padding)
      (Tape.input w) := by
  cases w with
  | nil =>
      constructor
      · rfl
      · constructor
        · rfl
        · exact dropTrailingNone_replicate_none padding
  | cons bit rest =>
      constructor
      · rfl
      · constructor
        · rfl
        · exact dropTrailingNone_append_replicate_none
            (rest.map some) padding

theorem inputWithTrailingBlankPadding_normalizedOutput
    (w : Word Bool) (padding : Nat) :
    Tape.normalizedOutput
        (inputWithTrailingBlankPadding w padding) = w := by
  have hequiv :=
    inputWithTrailingBlankPadding_equiv_input w padding
  rw [Tape.Equiv.normalizedOutput_eq hequiv]
  simpa [Tape.output] using Tape.normalizedOutput_output w

theorem inputWithTrailingBlankPadding_contextLength_ge_input
    (outputBits inputBits : Word Bool) :
    Tape.contextLength (Tape.input inputBits) <=
      Tape.contextLength
        (inputWithTrailingBlankPadding outputBits inputBits.length) := by
  cases outputBits <;> cases inputBits <;>
    simp [inputWithTrailingBlankPadding, Tape.input, Tape.blank,
      Tape.contextLength] <;>
    omega

theorem inputWithTrailingBlankPadding_move_right_contextLength_ge_pred
    (w : Word Bool) (padding : Nat) :
    w.length + padding - 1 <=
      Tape.contextLength
        (Tape.move Direction.right
          (inputWithTrailingBlankPadding w padding)) := by
  cases w with
  | nil =>
      cases padding with
      | zero =>
          simp [inputWithTrailingBlankPadding, Tape.contextLength,
            Tape.move, Tape.moveRight]
      | succ padding =>
          simp [inputWithTrailingBlankPadding, Tape.contextLength,
            Tape.move, Tape.moveRight, List.replicate_succ]
  | cons bit rest =>
      cases rest with
      | nil =>
          cases padding with
          | zero =>
              simp [inputWithTrailingBlankPadding, Tape.contextLength,
                Tape.move, Tape.moveRight]
          | succ padding =>
              simp [inputWithTrailingBlankPadding, Tape.contextLength,
                Tape.move, Tape.moveRight, List.replicate_succ]
              omega
      | cons bit' rest =>
          simp [inputWithTrailingBlankPadding, Tape.contextLength,
            Tape.move, Tape.moveRight]
          omega

theorem inputWithTrailingBlankPadding_move_right_normalizedOutput
    (w : Word Bool) (padding : Nat) :
    Tape.normalizedOutput
        (Tape.move Direction.right
          (inputWithTrailingBlankPadding w padding)) = w := by
  have hequiv :
      Tape.Equiv
        (Tape.move Direction.right
          (inputWithTrailingBlankPadding w padding))
        (Tape.move Direction.right (Tape.input w)) :=
    Tape.Equiv.move
      (inputWithTrailingBlankPadding_equiv_input w padding)
      Direction.right
  rw [Tape.Equiv.normalizedOutput_eq hequiv]
  exact tape_normalizedOutput_move_right_input w

def ScratchPaddedOutputTape
    {ι : Type}
    (outputBits : ι -> Word Bool)
    (scratchWidth : ι -> Nat)
    (i : ι) : Tape Bool :=
  inputWithTrailingBlankPadding (outputBits i) (scratchWidth i)

def RightScratchPaddedOutputTape
    {ι : Type}
    (outputBits : ι -> Word Bool)
    (scratchWidth : ι -> Nat)
    (i : ι) : Tape Bool :=
  Tape.move Direction.right
    (ScratchPaddedOutputTape outputBits scratchWidth i)

theorem ScratchPaddedOutputTape_equiv_input
    {ι : Type}
    (outputBits : ι -> Word Bool)
    (scratchWidth : ι -> Nat)
    (i : ι) :
    Tape.Equiv
      (ScratchPaddedOutputTape outputBits scratchWidth i)
      (Tape.input (outputBits i)) :=
  inputWithTrailingBlankPadding_equiv_input
    (outputBits i) (scratchWidth i)

theorem RightScratchPaddedOutputTape_equiv_right_input
    {ι : Type}
    (outputBits : ι -> Word Bool)
    (scratchWidth : ι -> Nat)
    (i : ι) :
    Tape.Equiv
      (RightScratchPaddedOutputTape outputBits scratchWidth i)
      (Tape.move Direction.right (Tape.input (outputBits i))) :=
  Tape.Equiv.move
    (ScratchPaddedOutputTape_equiv_input outputBits scratchWidth i)
    Direction.right

theorem ScratchPaddedOutputTape_normalizedOutput
    {ι : Type}
    (outputBits : ι -> Word Bool)
    (scratchWidth : ι -> Nat)
    (i : ι) :
    Tape.normalizedOutput
        (ScratchPaddedOutputTape outputBits scratchWidth i) =
      outputBits i :=
  inputWithTrailingBlankPadding_normalizedOutput
    (outputBits i) (scratchWidth i)

theorem RightScratchPaddedOutputTape_normalizedOutput
    {ι : Type}
    (outputBits : ι -> Word Bool)
    (scratchWidth : ι -> Nat)
    (i : ι) :
    Tape.normalizedOutput
        (RightScratchPaddedOutputTape outputBits scratchWidth i) =
      outputBits i :=
  inputWithTrailingBlankPadding_move_right_normalizedOutput
    (outputBits i) (scratchWidth i)

def ScratchPaddedEmitterSpec
    {ι : Type}
    (inputTape : ι -> Tape Bool)
    (outputBits : ι -> Word Bool)
    (scratchWidth : ι -> Nat)
    (canonicalOutputTape : ι -> Tape Bool)
    (emitter : MachineDescription) : Prop :=
  PaddedEquivEmitterSpec inputTape
    (ScratchPaddedOutputTape outputBits scratchWidth)
    canonicalOutputTape emitter

def RightScratchPaddedEmitterSpec
    {ι : Type}
    (inputTape : ι -> Tape Bool)
    (outputBits : ι -> Word Bool)
    (scratchWidth : ι -> Nat)
    (canonicalOutputTape : ι -> Tape Bool)
    (emitter : MachineDescription) : Prop :=
  PaddedEquivEmitterSpec inputTape
    (RightScratchPaddedOutputTape outputBits scratchWidth)
    canonicalOutputTape emitter

theorem tape_contextLength_le_move_right
    (T : Tape Bool) :
    Tape.contextLength T <=
      Tape.contextLength (Tape.move Direction.right T) := by
  cases T with
  | mk left head right =>
      cases right <;>
        simp [Tape.contextLength, Tape.move, Tape.moveRight] <;>
        omega

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
