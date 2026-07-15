import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.SimulatorHitExtractor
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.SuccessOnlyRecognizer
import FoC.Computability.Compiler.Structured.Lowering.TypedStateRuns

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

namespace U12HitBranch

inductive State where
  | inspect
  | branch
  | eraseSuccess
  | eraseFailure
  | failureExit
  | successHalt
deriving DecidableEq, Repr

private def step (a2 : TapeAction) (target : State) :=
  some (TypedStep.mk target keepS keepS a2)

def next (b : Bool) :
    State -> Option Bool -> Option Bool -> Option Bool ->
      Option (TypedStep State)
  | .inspect => fun _ _ _ => step keepL .branch
  | .branch => fun _ _ r2 =>
      match r2 with
      | some false => step eraseL .eraseSuccess
      | some true => step eraseL .eraseFailure
      | none => none
  | .eraseSuccess => fun _ _ r2 =>
      match r2 with
      | some _ => step eraseL .eraseSuccess
      | none => step (writeBitR b) .successHalt
  | .eraseFailure => fun _ _ r2 =>
      match r2 with
      | some _ => step eraseL .eraseFailure
      | none => step keepS .failureExit
  | .failureExit => fun _ _ _ => none
  | .successHalt => fun _ _ _ => none

def states : List State :=
  [.inspect, .branch, .eraseSuccess, .eraseFailure,
    .failureExit, .successHalt]

theorem next_target_mem (b : Bool) :
    forall s : State, s ∈ states ->
      forall r0 r1 r2 st, next b s r0 r1 r2 = some st ->
        st.target ∈ states := by
  intro s hs r0 r1 r2 st hnext
  cases s <;> simp only [next] at hnext
  all_goals repeat' first | split at hnext | simp only [step] at hnext
  all_goals try cases hnext
  all_goals simp [states]

def table (b : Bool) : TypedStateTable State :=
  TypedStateTable.ofList states .inspect .successHalt (next b)
    (by simp [states]) (by simp [states])
    (by intros; rfl) (next_target_mem b)

@[simp] theorem table_next_apply (b : Bool)
    (s : State) (r0 r1 r2 : Option Bool) :
    (table b).next s r0 r1 r2 = next b s r0 r1 r2 := rfl

def eraseLeftTape (bits : List Bool)
    (padding right : List (Option Bool)) : Tape Bool :=
  match bits with
  | [] => tapeAtCells padding (none :: right)
  | bit :: rest =>
      tapeAtCells
        (List.append (rest.map some) (none :: padding))
        (some bit :: right)

theorem replicate_succ_eq_append (n : Nat) (a : Option Bool) :
    List.replicate (n + 1) a = List.append (List.replicate n a) [a] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change
        a :: List.replicate (n + 1) a =
          a :: (List.replicate n a ++ [a])
      exact congrArg (List.cons a) ih

def hitOutputTape (hit : Bool) (padding : Nat) : Tape Bool :=
  tapeAtCells
    (List.append
      ((FoC.Computability.BoundedFuelPairSearch.singletonBoolWordBits hit).reverse.map some)
      (List.replicate (padding + 1) none)) []

def reversedHitTail (hit : Bool) : List Bool :=
  (FoC.Computability.BoundedFuelPairSearch.singletonBoolWordBits hit).reverse.tail

theorem reversedHitBits_true :
    (FoC.Computability.BoundedFuelPairSearch.singletonBoolWordBits true).reverse =
      false :: reversedHitTail true := rfl

theorem reversedHitBits_false :
    (FoC.Computability.BoundedFuelPairSearch.singletonBoolWordBits false).reverse =
      true :: reversedHitTail false := rfl

def successTape (b : Bool) (padding : List (Option Bool))
    (right : List (Option Bool)) : Tape Bool :=
  (writeBitR b).apply (eraseLeftTape [] padding right)

def successBranchTape (b : Bool) (padding : Nat) : Tape Bool :=
  successTape b (List.replicate padding none)
    (List.append
      (List.replicate (reversedHitTail true).length none)
      [none, none])

def failureBranchTape (padding : Nat) : Tape Bool :=
  eraseLeftTape [] (List.replicate padding none)
    (List.append
      (List.replicate (reversedHitTail false).length none)
      [none, none])

theorem successBranchTape_equiv (b : Bool) (padding : Nat) :
    Tape.Equiv (successBranchTape b padding)
      (Tape.move Direction.right (Tape.input [b])) := by
  simp [successBranchTape, successTape, eraseLeftTape,
    reversedHitTail,
    FoC.Computability.BoundedFuelPairSearch.singletonBoolWordBits,
    writeBitR, writeR, TapeAction.apply, HeadMove.apply,
    Tape.move, Tape.moveRight, Tape.write, Tape.input,
    tapeAtCells, Tape.Equiv, Tape.dropTrailingNone,
    FoC.Computability.dropTrailingNone_replicate_none]

theorem failureBranchTape_equiv_blank (padding : Nat) :
    Tape.Equiv (failureBranchTape padding) Tape.blank := by
  simp [failureBranchTape, eraseLeftTape, Tape.blank,
    reversedHitTail,
    FoC.Computability.BoundedFuelPairSearch.singletonBoolWordBits,
    tapeAtCells, Tape.Equiv, Tape.dropTrailingNone,
    FoC.Computability.dropTrailingNone_replicate_none]

def simulatorHitPadding (L : SimulatorLayout) : Nat :=
  0 + 4 *
    (FoC.Computability.BoundedFuelPairSearch.SimulatorHitSentinelCode L).length

theorem simulatorHitEmitterTargetTape_eq_hitOutputTape
    (L : SimulatorLayout) :
    FoC.Computability.BoundedFuelPairSearch.SimulatorHitEmitterTargetTape L =
      hitOutputTape L.hit (simulatorHitPadding L) := by
  simp [FoC.Computability.BoundedFuelPairSearch.SimulatorHitEmitterTargetTape,
    FoC.Computability.BoundedFuelPairSearch.hitSentinelBoundaryOutputBits,
    FoC.Computability.BoundedFuelPairSearch.encode_singleton_boolWord_eq_bits,
    EncRewriters.TotalOutputEmitter.finalTape,
    hitOutputTape, simulatorHitPadding, tapeAtCells]

end U12HitBranch
end Computability
end FoC
