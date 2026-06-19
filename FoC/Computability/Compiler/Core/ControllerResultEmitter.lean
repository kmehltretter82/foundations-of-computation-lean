import FoC.Computability.Compiler.Core.ControllerStageInputProjection

set_option doc.verso true

/-!
# Controller result-emitter machine
-/

namespace FoC
namespace Computability

open Languages

private inductive ControllerResultEmitterBoundary where
  | other
  | tick
  | tickDone
  | falseResult
  | trueResult
deriving DecidableEq

namespace ControllerResultEmitterBoundary

private def toNat : ControllerResultEmitterBoundary -> Nat
  | other => 0
  | tick => 1
  | tickDone => 2
  | falseResult => 3
  | trueResult => 4

private def update
    (state : ControllerResultEmitterBoundary)
    (symbol : MachineCodeSymbol) :
    ControllerResultEmitterBoundary :=
  match symbol with
  | MachineCodeSymbol.tick => tick
  | MachineCodeSymbol.done =>
      match state with
      | tick => tickDone
      | _ => other
  | MachineCodeSymbol.zero =>
      match state with
      | tickDone => falseResult
      | _ => other
  | MachineCodeSymbol.one =>
      match state with
      | tickDone => trueResult
      | _ => other
  | _ => other

private def output : ControllerResultEmitterBoundary -> Word Bool
  | falseResult => [false]
  | trueResult => [true]
  | _ => []

end ControllerResultEmitterBoundary

private def controllerResultEmitterBitValue : Bool -> Nat
  | false => 0
  | true => 1

private def controllerResultEmitterCodeOfBits
    (bit0 bit1 bit2 bit3 : Bool) : Nat :=
  (((controllerResultEmitterBitValue bit0) * 2 +
      controllerResultEmitterBitValue bit1) * 2 +
      controllerResultEmitterBitValue bit2) * 2 +
    controllerResultEmitterBitValue bit3

private def controllerResultEmitterSymbolCode : MachineCodeSymbol -> Nat
  | MachineCodeSymbol.header => 0
  | MachineCodeSymbol.transition => 1
  | MachineCodeSymbol.tick => 2
  | MachineCodeSymbol.done => 3
  | MachineCodeSymbol.blank => 4
  | MachineCodeSymbol.zero => 5
  | MachineCodeSymbol.one => 6
  | MachineCodeSymbol.moveLeft => 7
  | MachineCodeSymbol.moveRight => 8

private def controllerResultEmitterBoundaryOfNat
    (n : Nat) : ControllerResultEmitterBoundary :=
  match n with
  | 1 => ControllerResultEmitterBoundary.tick
  | 2 => ControllerResultEmitterBoundary.tickDone
  | 3 => ControllerResultEmitterBoundary.falseResult
  | 4 => ControllerResultEmitterBoundary.trueResult
  | _ => ControllerResultEmitterBoundary.other

private def controllerResultEmitterUpdateCode
    (boundary : Nat) (code : Nat) : Nat :=
  match code with
  | 2 => ControllerResultEmitterBoundary.tick.toNat
  | 3 =>
      match controllerResultEmitterBoundaryOfNat boundary with
      | ControllerResultEmitterBoundary.tick =>
          ControllerResultEmitterBoundary.tickDone.toNat
      | _ => ControllerResultEmitterBoundary.other.toNat
  | 5 =>
      match controllerResultEmitterBoundaryOfNat boundary with
      | ControllerResultEmitterBoundary.tickDone =>
          ControllerResultEmitterBoundary.falseResult.toNat
      | _ => ControllerResultEmitterBoundary.other.toNat
  | 6 =>
      match controllerResultEmitterBoundaryOfNat boundary with
      | ControllerResultEmitterBoundary.tickDone =>
          ControllerResultEmitterBoundary.trueResult.toNat
      | _ => ControllerResultEmitterBoundary.other.toNat
  | _ => ControllerResultEmitterBoundary.other.toNat

private def controllerResultEmitterState
    (boundary len bits : Nat) : Nat :=
  boundary * 16 + ((2 ^ len) - 1 + bits)

private def controllerResultEmitterHalt : Nat := 80

private def controllerResultEmitterNext
    (state : Nat) (bit : Bool) : Nat :=
  let boundary := state / 16
  let slot := state % 16
  if slot = 0 then
    controllerResultEmitterState boundary 1
      (controllerResultEmitterBitValue bit)
  else if slot < 3 then
    controllerResultEmitterState boundary 2
      ((slot - 1) * 2 + controllerResultEmitterBitValue bit)
  else if slot < 7 then
    controllerResultEmitterState boundary 3
      ((slot - 3) * 2 + controllerResultEmitterBitValue bit)
  else
    controllerResultEmitterState
      (controllerResultEmitterUpdateCode boundary
        ((slot - 7) * 2 + controllerResultEmitterBitValue bit))
      0 0

private def controllerResultEmitterPrefixTransitions
    (boundary : Nat) : List TransitionDescription :=
  [ MachineDescription.transition
      (controllerResultEmitterState boundary 0 0)
      (some false) none Direction.right
      (controllerResultEmitterState boundary 1 0)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 0 0)
      (some true) none Direction.right
      (controllerResultEmitterState boundary 1 1)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 1 0)
      (some false) none Direction.right
      (controllerResultEmitterState boundary 2 0)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 1 0)
      (some true) none Direction.right
      (controllerResultEmitterState boundary 2 1)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 1 1)
      (some false) none Direction.right
      (controllerResultEmitterState boundary 2 2)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 1 1)
      (some true) none Direction.right
      (controllerResultEmitterState boundary 2 3)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 2 0)
      (some false) none Direction.right
      (controllerResultEmitterState boundary 3 0)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 2 0)
      (some true) none Direction.right
      (controllerResultEmitterState boundary 3 1)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 2 1)
      (some false) none Direction.right
      (controllerResultEmitterState boundary 3 2)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 2 1)
      (some true) none Direction.right
      (controllerResultEmitterState boundary 3 3)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 2 2)
      (some false) none Direction.right
      (controllerResultEmitterState boundary 3 4)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 2 2)
      (some true) none Direction.right
      (controllerResultEmitterState boundary 3 5)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 2 3)
      (some false) none Direction.right
      (controllerResultEmitterState boundary 3 6)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 2 3)
      (some true) none Direction.right
      (controllerResultEmitterState boundary 3 7)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 3 0)
      (some false) none Direction.right
      (controllerResultEmitterState
        (controllerResultEmitterUpdateCode boundary 0) 0 0)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 3 0)
      (some true) none Direction.right
      (controllerResultEmitterState
        (controllerResultEmitterUpdateCode boundary 1) 0 0)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 3 1)
      (some false) none Direction.right
      (controllerResultEmitterState
        (controllerResultEmitterUpdateCode boundary 2) 0 0)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 3 1)
      (some true) none Direction.right
      (controllerResultEmitterState
        (controllerResultEmitterUpdateCode boundary 3) 0 0)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 3 2)
      (some false) none Direction.right
      (controllerResultEmitterState
        (controllerResultEmitterUpdateCode boundary 4) 0 0)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 3 2)
      (some true) none Direction.right
      (controllerResultEmitterState
        (controllerResultEmitterUpdateCode boundary 5) 0 0)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 3 3)
      (some false) none Direction.right
      (controllerResultEmitterState
        (controllerResultEmitterUpdateCode boundary 6) 0 0)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 3 3)
      (some true) none Direction.right
      (controllerResultEmitterState
        (controllerResultEmitterUpdateCode boundary 7) 0 0)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 3 4)
      (some false) none Direction.right
      (controllerResultEmitterState
        (controllerResultEmitterUpdateCode boundary 8) 0 0)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 3 4)
      (some true) none Direction.right
      (controllerResultEmitterState
        (controllerResultEmitterUpdateCode boundary 9) 0 0)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 3 5)
      (some false) none Direction.right
      (controllerResultEmitterState
        (controllerResultEmitterUpdateCode boundary 10) 0 0)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 3 5)
      (some true) none Direction.right
      (controllerResultEmitterState
        (controllerResultEmitterUpdateCode boundary 11) 0 0)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 3 6)
      (some false) none Direction.right
      (controllerResultEmitterState
        (controllerResultEmitterUpdateCode boundary 12) 0 0)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 3 6)
      (some true) none Direction.right
      (controllerResultEmitterState
        (controllerResultEmitterUpdateCode boundary 13) 0 0)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 3 7)
      (some false) none Direction.right
      (controllerResultEmitterState
        (controllerResultEmitterUpdateCode boundary 14) 0 0)
  , MachineDescription.transition
      (controllerResultEmitterState boundary 3 7)
      (some true) none Direction.right
      (controllerResultEmitterState
        (controllerResultEmitterUpdateCode boundary 15) 0 0)
  ]

private def controllerResultEmitterBitTransitions :
    List TransitionDescription :=
  controllerResultEmitterPrefixTransitions
      ControllerResultEmitterBoundary.other.toNat ++
    controllerResultEmitterPrefixTransitions
      ControllerResultEmitterBoundary.tick.toNat ++
    controllerResultEmitterPrefixTransitions
      ControllerResultEmitterBoundary.tickDone.toNat ++
    controllerResultEmitterPrefixTransitions
      ControllerResultEmitterBoundary.falseResult.toNat ++
    controllerResultEmitterPrefixTransitions
      ControllerResultEmitterBoundary.trueResult.toNat

private def controllerResultEmitterBlankTransitions :
    List TransitionDescription :=
  [ MachineDescription.transition
      (controllerResultEmitterState
        ControllerResultEmitterBoundary.other.toNat 0 0)
      none none Direction.right controllerResultEmitterHalt
  , MachineDescription.transition
      (controllerResultEmitterState
        ControllerResultEmitterBoundary.tick.toNat 0 0)
      none none Direction.right controllerResultEmitterHalt
  , MachineDescription.transition
      (controllerResultEmitterState
        ControllerResultEmitterBoundary.tickDone.toNat 0 0)
      none none Direction.right controllerResultEmitterHalt
  , MachineDescription.transition
      (controllerResultEmitterState
        ControllerResultEmitterBoundary.falseResult.toNat 0 0)
      none (some false) Direction.right controllerResultEmitterHalt
  , MachineDescription.transition
      (controllerResultEmitterState
        ControllerResultEmitterBoundary.trueResult.toNat 0 0)
      none (some true) Direction.right controllerResultEmitterHalt
  ]

def DovetailControllerResultEmitterDescription :
    MachineDescription where
  stateCount := controllerResultEmitterHalt + 1
  start :=
    controllerResultEmitterState
      ControllerResultEmitterBoundary.other.toNat 0 0
  halt := controllerResultEmitterHalt
  transitions :=
    controllerResultEmitterBitTransitions ++
      controllerResultEmitterBlankTransitions

theorem dovetailControllerResultEmitterDescription_wellFormed :
    DovetailControllerResultEmitterDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := DovetailControllerResultEmitterDescription.transitions)
      (stateCount := DovetailControllerResultEmitterDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := DovetailControllerResultEmitterDescription.transitions)
      (by
        native_decide) t u ht hu hkey

theorem dovetailControllerResultEmitterDescription_haltTransitionFree :
    DovetailControllerResultEmitterDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := DovetailControllerResultEmitterDescription.transitions)
    (state := DovetailControllerResultEmitterDescription.halt)
    (by
      native_decide) t ht

theorem dovetailControllerResultEmitterDescription_subroutineReady :
    DovetailControllerResultEmitterDescription.SubroutineReady :=
  ⟨dovetailControllerResultEmitterDescription_wellFormed,
    dovetailControllerResultEmitterDescription_haltTransitionFree⟩

private theorem dovetailControllerResultEmitterDescription_run_first_bit
    (boundary : ControllerResultEmitterBoundary)
    (bit : Bool) (erased : Nat) (suffix : Word Bool) :
    DovetailControllerResultEmitterDescription.runConfig 1
        { state := controllerResultEmitterState boundary.toNat 0 0
          tape := MachineDescription.eraseRightTape erased (bit :: suffix) } =
      { state :=
          controllerResultEmitterState boundary.toNat 1
            (controllerResultEmitterBitValue bit)
        tape := MachineDescription.eraseRightTape (erased + 1) suffix } := by
  cases boundary <;> cases bit <;> cases suffix <;> rfl

private theorem dovetailControllerResultEmitterDescription_run_second_bit
    (boundary : ControllerResultEmitterBoundary)
    (bit0 bit1 : Bool) (erased : Nat) (suffix : Word Bool) :
    DovetailControllerResultEmitterDescription.runConfig 1
        { state :=
            controllerResultEmitterState boundary.toNat 1
              (controllerResultEmitterBitValue bit0)
          tape := MachineDescription.eraseRightTape erased (bit1 :: suffix) } =
      { state :=
          controllerResultEmitterState boundary.toNat 2
            (controllerResultEmitterBitValue bit0 * 2 +
              controllerResultEmitterBitValue bit1)
        tape := MachineDescription.eraseRightTape (erased + 1) suffix } := by
  cases boundary <;> cases bit0 <;> cases bit1 <;> cases suffix <;> rfl

private theorem dovetailControllerResultEmitterDescription_run_third_bit
    (boundary : ControllerResultEmitterBoundary)
    (bit0 bit1 bit2 : Bool) (erased : Nat) (suffix : Word Bool) :
    DovetailControllerResultEmitterDescription.runConfig 1
        { state :=
            controllerResultEmitterState boundary.toNat 2
              (controllerResultEmitterBitValue bit0 * 2 +
                controllerResultEmitterBitValue bit1)
          tape := MachineDescription.eraseRightTape erased (bit2 :: suffix) } =
      { state :=
          controllerResultEmitterState boundary.toNat 3
            ((controllerResultEmitterBitValue bit0 * 2 +
                controllerResultEmitterBitValue bit1) * 2 +
              controllerResultEmitterBitValue bit2)
        tape := MachineDescription.eraseRightTape (erased + 1) suffix } := by
  cases boundary <;> cases bit0 <;> cases bit1 <;> cases bit2 <;>
    cases suffix <;> rfl

private theorem dovetailControllerResultEmitterDescription_run_fourth_bit
    (boundary : ControllerResultEmitterBoundary)
    (bit0 bit1 bit2 bit3 : Bool) (erased : Nat) (suffix : Word Bool) :
    DovetailControllerResultEmitterDescription.runConfig 1
        { state :=
            controllerResultEmitterState boundary.toNat 3
              ((controllerResultEmitterBitValue bit0 * 2 +
                  controllerResultEmitterBitValue bit1) * 2 +
                controllerResultEmitterBitValue bit2)
          tape := MachineDescription.eraseRightTape erased (bit3 :: suffix) } =
      { state :=
          controllerResultEmitterState
            (controllerResultEmitterUpdateCode boundary.toNat
              (controllerResultEmitterCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := MachineDescription.eraseRightTape (erased + 1) suffix } := by
  cases boundary <;> cases bit0 <;> cases bit1 <;> cases bit2 <;>
    cases bit3 <;> cases suffix <;> rfl

private theorem dovetailControllerResultEmitterDescription_run_bits
    (boundary : ControllerResultEmitterBoundary)
    (bit0 bit1 bit2 bit3 : Bool)
    (erased : Nat) (suffix : Word Bool) :
    DovetailControllerResultEmitterDescription.runConfig 4
        { state := controllerResultEmitterState boundary.toNat 0 0
          tape :=
            MachineDescription.eraseRightTape erased
              (List.append [bit0, bit1, bit2, bit3] suffix) } =
      { state :=
          controllerResultEmitterState
            (controllerResultEmitterUpdateCode boundary.toNat
              (controllerResultEmitterCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := MachineDescription.eraseRightTape (erased + 4) suffix } := by
  rw [show 4 = 1 + 3 by decide, MachineDescription.runConfig_add]
  change
    DovetailControllerResultEmitterDescription.runConfig 3
        (DovetailControllerResultEmitterDescription.runConfig 1
          { state := controllerResultEmitterState boundary.toNat 0 0
            tape :=
              MachineDescription.eraseRightTape erased
                (bit0 :: bit1 :: bit2 :: bit3 :: suffix) }) =
      { state :=
          controllerResultEmitterState
            (controllerResultEmitterUpdateCode boundary.toNat
              (controllerResultEmitterCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := MachineDescription.eraseRightTape (erased + 4) suffix }
  rw [dovetailControllerResultEmitterDescription_run_first_bit]
  rw [show 3 = 1 + 2 by decide, MachineDescription.runConfig_add]
  change
    DovetailControllerResultEmitterDescription.runConfig 2
        (DovetailControllerResultEmitterDescription.runConfig 1
          { state :=
              controllerResultEmitterState boundary.toNat 1
                (controllerResultEmitterBitValue bit0)
            tape :=
              MachineDescription.eraseRightTape (erased + 1)
                (bit1 :: bit2 :: bit3 :: suffix) }) =
      { state :=
          controllerResultEmitterState
            (controllerResultEmitterUpdateCode boundary.toNat
              (controllerResultEmitterCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := MachineDescription.eraseRightTape (erased + 4) suffix }
  rw [dovetailControllerResultEmitterDescription_run_second_bit]
  rw [show 2 = 1 + 1 by decide, MachineDescription.runConfig_add]
  change
    DovetailControllerResultEmitterDescription.runConfig 1
        (DovetailControllerResultEmitterDescription.runConfig 1
          { state :=
              controllerResultEmitterState boundary.toNat 2
                (controllerResultEmitterBitValue bit0 * 2 +
                  controllerResultEmitterBitValue bit1)
            tape :=
              MachineDescription.eraseRightTape ((erased + 1) + 1)
                (bit2 :: bit3 :: suffix) }) =
      { state :=
          controllerResultEmitterState
            (controllerResultEmitterUpdateCode boundary.toNat
              (controllerResultEmitterCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := MachineDescription.eraseRightTape (erased + 4) suffix }
  rw [dovetailControllerResultEmitterDescription_run_third_bit]
  rw [dovetailControllerResultEmitterDescription_run_fourth_bit]

private theorem controllerResultEmitterUpdateCode_symbol
    (boundary : ControllerResultEmitterBoundary)
    (symbol : MachineCodeSymbol) :
    controllerResultEmitterUpdateCode boundary.toNat
        (controllerResultEmitterSymbolCode symbol) =
      (boundary.update symbol).toNat := by
  cases boundary <;> cases symbol <;> rfl

private theorem dovetailControllerResultEmitterDescription_run_encoded_symbol
    (boundary : ControllerResultEmitterBoundary)
    (symbol : MachineCodeSymbol)
    (erased : Nat) (suffix : Word Bool) :
    DovetailControllerResultEmitterDescription.runConfig 4
        { state := controllerResultEmitterState boundary.toNat 0 0
          tape :=
            MachineDescription.eraseRightTape erased
              (List.append
                (MachineDescription.encodeCodeSymbolAsInput symbol) suffix) } =
      { state :=
          controllerResultEmitterState
            (controllerResultEmitterUpdateCode boundary.toNat
              (controllerResultEmitterSymbolCode symbol)) 0 0
        tape := MachineDescription.eraseRightTape (erased + 4) suffix } := by
  cases symbol
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      controllerResultEmitterCodeOfBits, controllerResultEmitterSymbolCode] using
      (dovetailControllerResultEmitterDescription_run_bits boundary
        false false false false erased suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      controllerResultEmitterCodeOfBits, controllerResultEmitterSymbolCode] using
      (dovetailControllerResultEmitterDescription_run_bits boundary
        false false false true erased suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      controllerResultEmitterCodeOfBits, controllerResultEmitterSymbolCode] using
      (dovetailControllerResultEmitterDescription_run_bits boundary
        false false true false erased suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      controllerResultEmitterCodeOfBits, controllerResultEmitterSymbolCode] using
      (dovetailControllerResultEmitterDescription_run_bits boundary
        false false true true erased suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      controllerResultEmitterCodeOfBits, controllerResultEmitterSymbolCode] using
      (dovetailControllerResultEmitterDescription_run_bits boundary
        false true false false erased suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      controllerResultEmitterCodeOfBits, controllerResultEmitterSymbolCode] using
      (dovetailControllerResultEmitterDescription_run_bits boundary
        false true false true erased suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      controllerResultEmitterCodeOfBits, controllerResultEmitterSymbolCode] using
      (dovetailControllerResultEmitterDescription_run_bits boundary
        false true true false erased suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      controllerResultEmitterCodeOfBits, controllerResultEmitterSymbolCode] using
      (dovetailControllerResultEmitterDescription_run_bits boundary
        false true true true erased suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      controllerResultEmitterCodeOfBits, controllerResultEmitterSymbolCode] using
      (dovetailControllerResultEmitterDescription_run_bits boundary
        true false false false erased suffix)

private theorem dovetailControllerResultEmitterDescription_run_symbol
    (boundary : ControllerResultEmitterBoundary)
    (symbol : MachineCodeSymbol)
    (erased : Nat) (suffix : Word Bool) :
    DovetailControllerResultEmitterDescription.runConfig 4
        { state :=
            controllerResultEmitterState boundary.toNat 0 0
          tape :=
            MachineDescription.eraseRightTape erased
              (List.append
                (MachineDescription.encodeCodeSymbolAsInput symbol) suffix) } =
      { state :=
          controllerResultEmitterState
            (boundary.update symbol).toNat 0 0
        tape := MachineDescription.eraseRightTape (erased + 4) suffix } := by
  rw [dovetailControllerResultEmitterDescription_run_encoded_symbol]
  rw [controllerResultEmitterUpdateCode_symbol]

private def controllerResultEmitterScanBoundaryFrom
    (boundary : ControllerResultEmitterBoundary) :
    Word MachineCodeSymbol -> ControllerResultEmitterBoundary
  | [] => boundary
  | symbol :: rest =>
      controllerResultEmitterScanBoundaryFrom
        (boundary.update symbol) rest

private def controllerResultEmitterScanBoundary
    (code : Word MachineCodeSymbol) :
    ControllerResultEmitterBoundary :=
  controllerResultEmitterScanBoundaryFrom
    ControllerResultEmitterBoundary.other code

private theorem controllerResultEmitterScanBoundaryFrom_append
    (boundary : ControllerResultEmitterBoundary)
    (pre suffix : Word MachineCodeSymbol) :
    controllerResultEmitterScanBoundaryFrom boundary
        (List.append pre suffix) =
      controllerResultEmitterScanBoundaryFrom
        (controllerResultEmitterScanBoundaryFrom boundary pre) suffix := by
  induction pre generalizing boundary with
  | nil =>
      rfl
  | cons symbol rest ih =>
      exact ih (boundary.update symbol)

private theorem dovetailControllerResultEmitterDescription_run_code_from
    (boundary : ControllerResultEmitterBoundary)
    (code : Word MachineCodeSymbol)
    (erased : Nat) (suffix : Word Bool) :
    DovetailControllerResultEmitterDescription.runConfig
        (4 * code.length)
        { state :=
            controllerResultEmitterState boundary.toNat 0 0
          tape :=
            MachineDescription.eraseRightTape erased
              (List.append
                (MachineDescription.encodeCodeWordAsInput code) suffix) } =
      { state :=
          controllerResultEmitterState
            (controllerResultEmitterScanBoundaryFrom boundary code).toNat 0 0
        tape :=
          MachineDescription.eraseRightTape
            (erased + 4 * code.length) suffix } := by
  induction code generalizing boundary erased with
  | nil =>
      simp [MachineDescription.encodeCodeWordAsInput,
        controllerResultEmitterScanBoundaryFrom,
        MachineDescription.runConfig]
  | cons symbol rest ih =>
      rw [show 4 * (symbol :: rest).length = 4 + 4 * rest.length by
        simp
        omega]
      rw [MachineDescription.runConfig_add]
      simp only [MachineDescription.encodeCodeWordAsInput]
      have happ :
          List.append
              (List.append
                (MachineDescription.encodeCodeSymbolAsInput symbol)
                (MachineDescription.encodeCodeWordAsInput rest))
              suffix =
            List.append
              (MachineDescription.encodeCodeSymbolAsInput symbol)
              (List.append
                (MachineDescription.encodeCodeWordAsInput rest) suffix) :=
        List.append_assoc
          (MachineDescription.encodeCodeSymbolAsInput symbol)
          (MachineDescription.encodeCodeWordAsInput rest) suffix
      rw [happ]
      change
        DovetailControllerResultEmitterDescription.runConfig
            (4 * rest.length)
            (DovetailControllerResultEmitterDescription.runConfig 4
              { state := controllerResultEmitterState boundary.toNat 0 0
                tape :=
                  MachineDescription.eraseRightTape erased
                    (List.append
                      (MachineDescription.encodeCodeSymbolAsInput symbol)
                      (List.append
                        (MachineDescription.encodeCodeWordAsInput rest)
                        suffix)) }) =
          { state :=
              controllerResultEmitterState
                (controllerResultEmitterScanBoundaryFrom boundary
                  (symbol :: rest)).toNat 0 0
            tape :=
              MachineDescription.eraseRightTape
                (erased + (4 + 4 * rest.length)) suffix }
      rw [dovetailControllerResultEmitterDescription_run_symbol]
      rw [ih]
      simp [controllerResultEmitterScanBoundaryFrom]
      congr 1
      omega

private def controllerResultEmitterFinalTape
    (erased : Nat) : ControllerResultEmitterBoundary -> Tape Bool
  | ControllerResultEmitterBoundary.falseResult =>
      MachineDescription.boolOutputTape erased false
  | ControllerResultEmitterBoundary.trueResult =>
      MachineDescription.boolOutputTape erased true
  | _ => MachineDescription.eraseRightTape (erased + 1) []

private theorem dovetailControllerResultEmitterDescription_run_blank
    (boundary : ControllerResultEmitterBoundary) (erased : Nat) :
    DovetailControllerResultEmitterDescription.runConfig 1
        { state := controllerResultEmitterState boundary.toNat 0 0
          tape := MachineDescription.eraseRightTape erased [] } =
      { state := DovetailControllerResultEmitterDescription.halt
        tape := controllerResultEmitterFinalTape erased boundary } := by
  cases boundary <;>
    simp [DovetailControllerResultEmitterDescription,
      controllerResultEmitterBitTransitions,
      controllerResultEmitterPrefixTransitions,
      controllerResultEmitterBlankTransitions,
      controllerResultEmitterState,
      controllerResultEmitterHalt,
      controllerResultEmitterFinalTape,
      ControllerResultEmitterBoundary.toNat,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition,
      MachineDescription.eraseRightTape,
      MachineDescription.boolOutputTape,
      Tape.read, Tape.write, Tape.move, Tape.moveRight,
      List.replicate_succ]

private theorem dovetailControllerResultEmitterDescription_run_code_halt
    (code : Word MachineCodeSymbol) :
    DovetailControllerResultEmitterDescription.runConfig
        (4 * code.length + 1)
        (DovetailControllerResultEmitterDescription.initial
          (MachineDescription.encodeCodeWordAsInput code)) =
      { state := DovetailControllerResultEmitterDescription.halt
        tape :=
          controllerResultEmitterFinalTape
            (0 + 4 * code.length)
            (controllerResultEmitterScanBoundary code) } := by
  rw [MachineDescription.runConfig_add]
  have hinitial :
      DovetailControllerResultEmitterDescription.initial
          (MachineDescription.encodeCodeWordAsInput code) =
        { state :=
            controllerResultEmitterState
              ControllerResultEmitterBoundary.other.toNat 0 0
          tape :=
            MachineDescription.eraseRightTape 0
              (List.append
                (MachineDescription.encodeCodeWordAsInput code) []) } := by
    simp [DovetailControllerResultEmitterDescription,
      MachineDescription.initial,
      MachineDescription.eraseRightTape_zero_eq_input]
  rw [hinitial]
  rw [dovetailControllerResultEmitterDescription_run_code_from]
  rw [dovetailControllerResultEmitterDescription_run_blank]
  rfl

private theorem controllerResultEmitterFinalTape_normalizedOutput
    (boundary : ControllerResultEmitterBoundary) (erased : Nat) :
    Tape.normalizedOutput
        (controllerResultEmitterFinalTape erased boundary) =
      boundary.output := by
  cases boundary
  · exact MachineDescription.eraseRightTape_normalizedOutput_empty
      (erased + 1)
  · exact MachineDescription.eraseRightTape_normalizedOutput_empty
      (erased + 1)
  · exact MachineDescription.eraseRightTape_normalizedOutput_empty
      (erased + 1)
  · exact MachineDescription.boolOutputTape_normalizedOutput erased false
  · exact MachineDescription.boolOutputTape_normalizedOutput erased true

private theorem dovetailControllerResultEmitterDescription_haltsWithOutput_code
    (code : Word MachineCodeSymbol) :
    DovetailControllerResultEmitterDescription.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput code)
      (controllerResultEmitterScanBoundary code).output := by
  refine ⟨4 * code.length + 1, ?_⟩
  constructor
  · rw [dovetailControllerResultEmitterDescription_run_code_halt]
  · rw [dovetailControllerResultEmitterDescription_run_code_halt]
    exact controllerResultEmitterFinalTape_normalizedOutput
      (controllerResultEmitterScanBoundary code) (0 + 4 * code.length)

private theorem controllerResultEmitterScanBoundaryFrom_encodeCells_some_other
    (w : Word Bool) :
    controllerResultEmitterScanBoundaryFrom
        ControllerResultEmitterBoundary.other
        (MachineDescription.encodeCellsAppend (w.map some) []) =
      ControllerResultEmitterBoundary.other := by
  induction w with
  | nil =>
      rfl
  | cons b rest ih =>
      cases b <;>
        simp [MachineDescription.encodeCellsAppend,
          MachineDescription.encodeCellAppend,
          MachineDescription.encodeCell,
          controllerResultEmitterScanBoundaryFrom,
          ControllerResultEmitterBoundary.update, ih]

private theorem controllerResultEmitterScanBoundaryFrom_encodeNat_from_tick
    (n : Nat) :
    controllerResultEmitterScanBoundaryFrom
        ControllerResultEmitterBoundary.tick
        (MachineDescription.encodeNat n) =
      ControllerResultEmitterBoundary.tickDone := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simpa [MachineDescription.encodeNat,
        controllerResultEmitterScanBoundaryFrom,
        ControllerResultEmitterBoundary.update] using ih

private theorem controllerResultEmitterScanBoundaryFrom_encodeNat_succ
    (boundary : ControllerResultEmitterBoundary) (n : Nat) :
    controllerResultEmitterScanBoundaryFrom boundary
        (MachineDescription.encodeNat (n + 1)) =
      ControllerResultEmitterBoundary.tickDone := by
  simp [MachineDescription.encodeNat,
    controllerResultEmitterScanBoundaryFrom,
    ControllerResultEmitterBoundary.update,
    controllerResultEmitterScanBoundaryFrom_encodeNat_from_tick]

private theorem controllerResultEmitterScanBoundaryFrom_encodeCells_singleton
    (b : Bool) :
    controllerResultEmitterScanBoundaryFrom
        ControllerResultEmitterBoundary.tickDone
        (MachineDescription.encodeCellsAppend [some b] []) =
      (if b then ControllerResultEmitterBoundary.trueResult
        else ControllerResultEmitterBoundary.falseResult) := by
  cases b <;>
    rfl

private theorem controllerResultEmitterScanBoundaryFrom_encodeCells_cons_cons
    (first second : Bool) (rest : Word Bool) :
    controllerResultEmitterScanBoundaryFrom
        ControllerResultEmitterBoundary.tickDone
        (MachineDescription.encodeCellsAppend
          ((first :: second :: rest).map some) []) =
      ControllerResultEmitterBoundary.other := by
  cases first <;> cases second <;>
    simp [MachineDescription.encodeCellsAppend,
      MachineDescription.encodeCellAppend,
      MachineDescription.encodeCell,
      controllerResultEmitterScanBoundaryFrom,
      ControllerResultEmitterBoundary.update,
      controllerResultEmitterScanBoundaryFrom_encodeCells_some_other]

private theorem controllerResultEmitterScanBoundaryFrom_encodeBoolWord_singleton
    (boundary : ControllerResultEmitterBoundary) (b : Bool) :
    controllerResultEmitterScanBoundaryFrom boundary
        (MachineDescription.encodeBoolWord [b]) =
      (if b then ControllerResultEmitterBoundary.trueResult
        else ControllerResultEmitterBoundary.falseResult) := by
  rw [show
      MachineDescription.encodeBoolWord [b] =
        List.append (MachineDescription.encodeNat 1)
          (MachineDescription.encodeCellsAppend [some b] []) by
    simp [MachineDescription.encodeBoolWord,
      MachineDescription.encodeBoolWordAppend,
      MachineDescription.encodeCellListAppend,
      MachineDescription.encodeNatAppend]]
  rw [controllerResultEmitterScanBoundaryFrom_append]
  rw [controllerResultEmitterScanBoundaryFrom_encodeNat_succ]
  exact controllerResultEmitterScanBoundaryFrom_encodeCells_singleton b

private theorem controllerResultEmitterScanBoundaryFrom_encodeBoolWord_cons_cons
    (boundary : ControllerResultEmitterBoundary)
    (first second : Bool) (rest : Word Bool) :
    controllerResultEmitterScanBoundaryFrom boundary
        (MachineDescription.encodeBoolWord (first :: second :: rest)) =
      ControllerResultEmitterBoundary.other := by
  rw [show
      MachineDescription.encodeBoolWord (first :: second :: rest) =
        List.append
          (MachineDescription.encodeNat (rest.length + 1 + 1))
          (MachineDescription.encodeCellsAppend
            ((first :: second :: rest).map some) []) by
    simp [MachineDescription.encodeBoolWord,
      MachineDescription.encodeBoolWordAppend,
      MachineDescription.encodeCellListAppend,
      MachineDescription.encodeNatAppend]]
  rw [controllerResultEmitterScanBoundaryFrom_append]
  rw [controllerResultEmitterScanBoundaryFrom_encodeNat_succ]
  exact controllerResultEmitterScanBoundaryFrom_encodeCells_cons_cons
    first second rest

private theorem controllerResultEmitterScanBoundaryFrom_encodeBoolWord_output_iff
    (boundary : ControllerResultEmitterBoundary)
    (result : Word Bool) (b : Bool) :
    (controllerResultEmitterScanBoundaryFrom boundary
        (MachineDescription.encodeBoolWord result)).output = [b] <->
      result = [b] := by
  cases result with
  | nil =>
      cases boundary <;> cases b <;>
        simp [MachineDescription.encodeBoolWord,
          MachineDescription.encodeBoolWordAppend,
          MachineDescription.encodeCellListAppend,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat,
          MachineDescription.encodeCellsAppend,
          controllerResultEmitterScanBoundaryFrom,
          ControllerResultEmitterBoundary.update,
          ControllerResultEmitterBoundary.output]
  | cons first tail =>
      cases tail with
      | nil =>
          cases first <;> cases b <;>
            simp [controllerResultEmitterScanBoundaryFrom_encodeBoolWord_singleton,
              ControllerResultEmitterBoundary.output]
      | cons second rest =>
          cases first <;> cases second <;> cases b <;>
            simp [controllerResultEmitterScanBoundaryFrom_encodeBoolWord_cons_cons,
              ControllerResultEmitterBoundary.output] <;>
            intro h <;>
            cases h

private theorem controllerResultEmitterScanBoundary_controllerEncode_output_iff
    (C : MachineDescription.DovetailControllerLayout) (b : Bool) :
    (controllerResultEmitterScanBoundary
        (MachineDescription.DovetailControllerLayout.encode C)).output =
        [b] <->
      C.result = [b] := by
  have hnat :
      MachineDescription.encodeNatAppend C.stage
          (MachineDescription.encodeBoolWordAppend C.result []) =
        List.append
          (MachineDescription.encodeNatAppend C.stage [])
          (MachineDescription.encodeBoolWordAppend C.result []) := by
    simpa using
      encodeNatAppend_append C.stage ([] : Word MachineCodeSymbol)
        (MachineDescription.encodeBoolWordAppend C.result [])
  have hinput :
      MachineDescription.encodeBoolWordAppend C.input
          (MachineDescription.encodeNatAppend C.stage
            (MachineDescription.encodeBoolWordAppend C.result [])) =
        List.append
          (MachineDescription.encodeBoolWordAppend C.input
            (MachineDescription.encodeNatAppend C.stage []))
          (MachineDescription.encodeBoolWordAppend C.result []) := by
    rw [hnat]
    exact
      encodeBoolWordAppend_append C.input
        (MachineDescription.encodeNatAppend C.stage [])
        (MachineDescription.encodeBoolWordAppend C.result [])
  change
    (controllerResultEmitterScanBoundaryFrom
        ControllerResultEmitterBoundary.other
        (MachineCodeSymbol.header ::
          MachineDescription.encodeBoolWordAppend C.input
            (MachineDescription.encodeNatAppend C.stage
              (MachineDescription.encodeBoolWordAppend C.result [])))).output =
        [b] <->
      C.result = [b]
  simp only [controllerResultEmitterScanBoundaryFrom,
    ControllerResultEmitterBoundary.update]
  rw [hinput]
  rw [controllerResultEmitterScanBoundaryFrom_append]
  simpa [MachineDescription.encodeBoolWord] using
    controllerResultEmitterScanBoundaryFrom_encodeBoolWord_output_iff
      (controllerResultEmitterScanBoundaryFrom
        ControllerResultEmitterBoundary.other
        (MachineDescription.encodeBoolWordAppend C.input
          (MachineDescription.encodeNatAppend C.stage [])))
      C.result b

theorem dovetailControllerResultEmitterDescription_haltsWithOutput_iff
    (C : MachineDescription.DovetailControllerLayout) (b : Bool) :
    DovetailControllerResultEmitterDescription.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput
          (MachineDescription.DovetailControllerLayout.encode C))
        [b] <->
      PairedRecognizerDovetailControllerRawOutput C.result = some [b] := by
  constructor
  · intro h
    have hcanonical :
        DovetailControllerResultEmitterDescription.HaltsWithOutput
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailControllerLayout.encode C))
          (controllerResultEmitterScanBoundary
            (MachineDescription.DovetailControllerLayout.encode C)).output :=
      dovetailControllerResultEmitterDescription_haltsWithOutput_code
        (MachineDescription.DovetailControllerLayout.encode C)
    have houtput :
        [b] =
          (controllerResultEmitterScanBoundary
            (MachineDescription.DovetailControllerLayout.encode C)).output :=
      MachineDescription.haltsWithOutput_functional_of_haltTransitionFree
        dovetailControllerResultEmitterDescription_haltTransitionFree
        h hcanonical
    have hresult : C.result = [b] :=
      (controllerResultEmitterScanBoundary_controllerEncode_output_iff
        C b).mp houtput.symm
    exact
      (MachineDescription.DovetailControllerLayout.rawOutput_eq_some_singleton_iff
        C.result b).mpr hresult
  · intro hraw
    have hresult : C.result = [b] :=
      (MachineDescription.DovetailControllerLayout.rawOutput_eq_some_singleton_iff
        C.result b).mp hraw
    have houtput :
        (controllerResultEmitterScanBoundary
          (MachineDescription.DovetailControllerLayout.encode C)).output =
          [b] :=
      (controllerResultEmitterScanBoundary_controllerEncode_output_iff
        C b).mpr hresult
    simpa [houtput] using
      dovetailControllerResultEmitterDescription_haltsWithOutput_code
        (MachineDescription.DovetailControllerLayout.encode C)

theorem encodedControllerResultEmitterRewriterConstruction_of_description :
    EncodedControllerResultEmitterRewriterConstruction :=
  ⟨DovetailControllerResultEmitterDescription,
    dovetailControllerResultEmitterDescription_subroutineReady,
    dovetailControllerResultEmitterDescription_haltsWithOutput_iff⟩

end Computability
end FoC
