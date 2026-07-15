import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Frame.Fuel

set_option doc.verso true

/-!
# Positioned right-field locator

Finite cursor motion from the protected frame head to the serialized right
payload and count boundaries.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace Edits
namespace PositionedRightLocator

open SerializedFieldComposer

inductive Boundary where
  | rightCountTicks
  | rightPayload
deriving DecidableEq

inductive Control where
  | head (count : Fin 10)
  | rightCount
  | returnToCountDone
  | gate
deriving DecidableEq

namespace Control

def elems : List Control :=
  (List.finRange 10).map Control.head ++
    [.rightCount, .returnToCountDone, .gate]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | head count => simp [elems, List.mem_finRange]
    | rightCount => simp [elems]
    | returnToCountDone => simp [elems]
    | gate => simp [elems]

end Control

def transition (boundary : Boundary) :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .head count, some MachineCodeSymbol.tick =>
      match HeadLocator.incrementHeadCount count with
      | none => none
      | some next =>
          some (some MachineCodeSymbol.tick, Direction.right, .head next)
  | .head _, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .rightCount)
  | .rightCount, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .rightCount)
  | .rightCount, some MachineCodeSymbol.done =>
      match boundary with
      | .rightCountTicks =>
          some (some MachineCodeSymbol.done, Direction.right,
            .returnToCountDone)
      | .rightPayload =>
          some (some MachineCodeSymbol.done, Direction.right, .gate)
  | .returnToCountDone, read =>
      some (read, Direction.left, .gate)
  | _, _ => none

def machine (boundary : Boundary) :
    TuringMachine MachineCodeSymbol Control where
  start := .head ⟨0, by decide⟩
  halt := .gate
  transition := transition boundary
  statesFinite := Control.finite

def config (control : Control)
    (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := control
  tape := SerializedShift.cursorTape leftRev rest

def sourceConfig (leftRev : Word MachineCodeSymbol)
    (head : Option MachineCodeSymbol) (rightCount : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config (.head ⟨0, by decide⟩) leftRev
    (List.append (optionalCellWord head)
      (MachineDescription.encodeNatAppend rightCount suffix))

def afterHeadLeftRev (leftRev : Word MachineCodeSymbol)
    (head : Option MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (optionalCellWord head).reverse leftRev

def rightPayloadGateConfig (leftRev : Word MachineCodeSymbol)
    (head : Option MachineCodeSymbol) (rightCount : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .gate
    (List.append (MachineDescription.encodeNat rightCount).reverse
      (afterHeadLeftRev leftRev head)) suffix

def headSteps (head : Option MachineCodeSymbol) : Nat :=
  optionalCodeSymbolTag head + 1

def rightCountStartConfig (leftRev : Word MachineCodeSymbol)
    (head : Option MachineCodeSymbol) (rightCount : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .rightCount (afterHeadLeftRev leftRev head)
    (MachineDescription.encodeNatAppend rightCount suffix)

theorem head_run_rightPayload_prefix_exact
    (leftRev : Word MachineCodeSymbol)
    (head : Option MachineCodeSymbol) (rightCount : Nat)
    (suffix : Word MachineCodeSymbol) :
    (machine .rightPayload).runConfigExact? (headSteps head)
        (sourceConfig leftRev head rightCount suffix) =
      some (rightCountStartConfig leftRev head rightCount suffix) := by
  cases head with
  | none => cases rightCount <;> cases suffix <;> rfl
  | some symbol =>
      cases symbol <;> cases rightCount <;> cases suffix <;> rfl

theorem head_run_rightCountTicks_prefix_exact
    (leftRev : Word MachineCodeSymbol)
    (head : Option MachineCodeSymbol) (rightCount : Nat)
    (suffix : Word MachineCodeSymbol) :
    (machine .rightCountTicks).runConfigExact? (headSteps head)
        (sourceConfig leftRev head rightCount suffix) =
      some (rightCountStartConfig leftRev head rightCount suffix) := by
  cases head with
  | none => cases rightCount <;> cases suffix <;> rfl
  | some symbol =>
      cases symbol <;> cases rightCount <;> cases suffix <;> rfl

theorem rightCount_tick_step
    (boundary : Boundary) (leftRev suffix : Word MachineCodeSymbol) :
    (machine boundary).stepConfig
        (config .rightCount leftRev
          (MachineCodeSymbol.tick :: suffix)) =
      some
        (config .rightCount (MachineCodeSymbol.tick :: leftRev) suffix) := by
  cases boundary <;> cases suffix <;> rfl

theorem rightCount_done_step
    (leftRev suffix : Word MachineCodeSymbol) :
    (machine .rightPayload).stepConfig
        (config .rightCount leftRev
          (MachineCodeSymbol.done :: suffix)) =
      some
        (config .gate (MachineCodeSymbol.done :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem rightCount_run_exact
    (count : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    (machine .rightPayload).runConfigExact? (count + 1)
        (config .rightCount leftRev
          (MachineDescription.encodeNatAppend count suffix)) =
      some
        (config .gate
          (List.append (MachineDescription.encodeNat count).reverse
            leftRev) suffix) := by
  induction count generalizing leftRev with
  | zero => exact rightCount_done_step leftRev suffix
  | succ count ih =>
      change
        (machine .rightPayload).runConfigExact? ((count + 1) + 1)
            (config .rightCount leftRev
              (MachineCodeSymbol.tick ::
                MachineDescription.encodeNatAppend count suffix)) = _
      rw [TuringMachine.runConfigExact?]
      rw [rightCount_tick_step .rightPayload]
      simp only
      rw [ih]
      simp [MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc]

def roundTripTape (T : Tape MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.left (Tape.move Direction.right T)

theorem roundTripTape_equiv (T : Tape MachineCodeSymbol) :
    Tape.Equiv (roundTripTape T) T :=
  Machine.moveLeft_moveRight_equiv_self T

def countTicksLeftRev (count : Nat)
    (leftRev : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (HeadLocator.ticks count).reverse leftRev

def rightCountTicksGateConfig
    (count : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .gate
  tape := roundTripTape
    (SerializedShift.cursorTape (countTicksLeftRev count leftRev)
      (MachineCodeSymbol.done :: suffix))

theorem rightCount_done_bounce_exact
    (leftRev suffix : Word MachineCodeSymbol) :
    (machine .rightCountTicks).runConfigExact? 2
        (config .rightCount leftRev
          (MachineCodeSymbol.done :: suffix)) =
      some (rightCountTicksGateConfig 0 leftRev suffix) := by
  cases suffix <;> rfl

theorem rightCountTicks_run_exact
    (count : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    (machine .rightCountTicks).runConfigExact? (count + 2)
        (config .rightCount leftRev
          (MachineDescription.encodeNatAppend count suffix)) =
      some (rightCountTicksGateConfig count leftRev suffix) := by
  induction count generalizing leftRev with
  | zero => exact rightCount_done_bounce_exact leftRev suffix
  | succ count ih =>
      change
        (machine .rightCountTicks).runConfigExact? ((count + 2) + 1)
            (config .rightCount leftRev
              (MachineCodeSymbol.tick ::
                MachineDescription.encodeNatAppend count suffix)) = _
      rw [TuringMachine.runConfigExact?]
      rw [rightCount_tick_step .rightCountTicks]
      simp only
      rw [ih]
      simp [rightCountTicksGateConfig, countTicksLeftRev,
        HeadLocator.ticks, roundTripTape, List.reverse_cons,
        List.append_assoc]

def rightPayloadSteps (head : Option MachineCodeSymbol)
    (rightCount : Nat) : Nat :=
  headSteps head + (rightCount + 1)

theorem runConfigExact?_add (boundary : Boundary)
    (first second : Nat)
    (c : TuringMachine.Configuration MachineCodeSymbol Control) :
    (machine boundary).runConfigExact? (first + second) c =
      match (machine boundary).runConfigExact? first c with
      | none => none
      | some middle =>
          (machine boundary).runConfigExact? second middle := by
  induction first generalizing c with
  | zero => simp only [Nat.zero_add, TuringMachine.runConfigExact?]
  | succ first ih =>
      rw [Nat.succ_add]
      rw [TuringMachine.runConfigExact?]
      rw [TuringMachine.runConfigExact?]
      cases hstep : (machine boundary).stepConfig c with
      | none => rfl
      | some next =>
          simp only
          exact ih next

def rightCountTicksSteps (head : Option MachineCodeSymbol)
    (rightCount : Nat) : Nat :=
  headSteps head + (rightCount + 2)

theorem run_rightCountTicks_exact
    (leftRev : Word MachineCodeSymbol)
    (head : Option MachineCodeSymbol) (rightCount : Nat)
    (suffix : Word MachineCodeSymbol) :
    (machine .rightCountTicks).runConfigExact?
        (rightCountTicksSteps head rightCount)
        (sourceConfig leftRev head rightCount suffix) =
      some
        (rightCountTicksGateConfig rightCount
          (afterHeadLeftRev leftRev head) suffix) := by
  unfold rightCountTicksSteps
  rw [runConfigExact?_add]
  rw [head_run_rightCountTicks_prefix_exact]
  simp only
  exact rightCountTicks_run_exact rightCount
    (afterHeadLeftRev leftRev head) suffix

theorem run_rightPayload_exact
    (leftRev : Word MachineCodeSymbol)
    (head : Option MachineCodeSymbol) (rightCount : Nat)
    (suffix : Word MachineCodeSymbol) :
    (machine .rightPayload).runConfigExact?
        (rightPayloadSteps head rightCount)
        (sourceConfig leftRev head rightCount suffix) =
      some (rightPayloadGateConfig leftRev head rightCount suffix) := by
  unfold rightPayloadSteps
  rw [runConfigExact?_add]
  rw [head_run_rightPayload_prefix_exact]
  simp only
  exact rightCount_run_exact rightCount
    (afterHeadLeftRev leftRev head) suffix

theorem canonical_rightPayload_exact {stateCount : Nat}
    (L : Layout stateCount) (callerData : Word MachineCodeSymbol) :
    (machine .rightPayload).runConfigExact?
        (rightPayloadSteps L.head L.right.length)
        (sourceConfig (headPrefix L).reverse L.head L.right.length
          (RightPrepend.rightPayloadSuffix L callerData)) =
      some
        (config .gate (RightPrepend.rightPayloadPrefix L).reverse
          (RightPrepend.rightPayloadSuffix L callerData)) := by
  simpa [rightPayloadGateConfig, afterHeadLeftRev,
    RightPrepend.rightPayloadPrefix, RightPrepend.rightCountPrefix,
    List.reverse_append, List.append_assoc] using
      run_rightPayload_exact (headPrefix L).reverse L.head
        L.right.length (RightPrepend.rightPayloadSuffix L callerData)

theorem canonical_rightCountTicks_exact {stateCount : Nat}
    (L : Layout stateCount) (write : Option MachineCodeSymbol)
    (callerData : Word MachineCodeSymbol) :
    (machine .rightCountTicks).runConfigExact?
        (rightCountTicksSteps L.head L.right.length)
        (sourceConfig (headPrefix L).reverse L.head L.right.length
          (List.append (optionalCellWord write)
            (RightPrepend.rightPayloadSuffix L callerData))) =
      some
        { state := Control.gate
          tape := roundTripTape
            (SerializedShift.cursorTape
              (RightPrepend.rightCountTicksPrefix L).reverse
              (RightPrepend.afterCountDoneSuffix
                L write callerData)) } := by
  simpa [rightCountTicksGateConfig, countTicksLeftRev,
    afterHeadLeftRev, RightPrepend.rightCountTicksPrefix,
    RightPrepend.rightCountPrefix,
    RightPrepend.afterCountDoneSuffix,
    List.reverse_append, List.append_assoc] using
      run_rightCountTicks_exact (headPrefix L).reverse L.head
        L.right.length
        (List.append (optionalCellWord write)
          (RightPrepend.rightPayloadSuffix L callerData))

end PositionedRightLocator
end Edits
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
