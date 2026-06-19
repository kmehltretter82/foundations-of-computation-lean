import FoC.Computability.Compiler.Core.EncodingLemmas
import FoC.Computability.Compiler.Core.TransitionTableChecks

set_option doc.verso true

/-!
# Total-output emitter encoded rewriter

This module isolates the finite-machine obligation for
{name (full := FoC.Computability.PairedRecognizerDovetailTotalOutputCode)}`PairedRecognizerDovetailTotalOutputCode`.
The machine-level target is a normalized canonical output word.  This is
intentionally not a handoff contract: this primitive can shrink a large encoded
layout to the encoding of an empty or singleton Boolean word, and tape context
length cannot decrease.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace TotalOutputEmitter

def OutputCode
    (L : MachineDescription.DovetailLayout) : Word MachineCodeSymbol :=
  MachineDescription.encodeBoolWord
    (MachineDescription.DovetailLayout.outputWordFromHits L)

def OutputBits
    (L : MachineDescription.DovetailLayout) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput
    (OutputCode L)

def ReadySpec
    (emitter : MachineDescription) : Prop :=
  emitter.WellFormed ∧ emitter.HaltTransitionFree

def ForwardSpec
    (emitter : MachineDescription) : Prop :=
  forall L : MachineDescription.DovetailLayout,
    emitter.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput
        (MachineDescription.DovetailLayout.encode L))
      (OutputBits L)

def Spec
    (emitter : MachineDescription) : Prop :=
  ReadySpec emitter ∧ ForwardSpec emitter

def FiniteDescriptionConstruction : Prop :=
  exists emitter : MachineDescription,
    Spec emitter

inductive HitBoundary where
  | other
  | lastFalse
  | lastTrue
  | falseFalse
  | falseTrue
  | trueFalse
  | trueTrue
deriving DecidableEq

namespace HitBoundary

def toNat : HitBoundary -> Nat
  | other => 0
  | lastFalse => 1
  | lastTrue => 2
  | falseFalse => 3
  | falseTrue => 4
  | trueFalse => 5
  | trueTrue => 6

def fromNat : Nat -> HitBoundary
  | 1 => lastFalse
  | 2 => lastTrue
  | 3 => falseFalse
  | 4 => falseTrue
  | 5 => trueFalse
  | 6 => trueTrue
  | _ => other

def last? : HitBoundary -> Option Bool
  | lastFalse => some false
  | lastTrue => some true
  | falseFalse => some false
  | falseTrue => some true
  | trueFalse => some false
  | trueTrue => some true
  | other => none

def updateBool (boundary : HitBoundary) (bit : Bool) :
    HitBoundary :=
  match boundary.last? with
  | none => if bit then lastTrue else lastFalse
  | some false => if bit then falseTrue else falseFalse
  | some true => if bit then trueTrue else trueFalse

def update (boundary : HitBoundary) (symbol : MachineCodeSymbol) :
    HitBoundary :=
  match symbol with
  | MachineCodeSymbol.zero => boundary.updateBool false
  | MachineCodeSymbol.one => boundary.updateBool true
  | _ => other

def ofHits (acceptHit rejectHit : Bool) : HitBoundary :=
  match acceptHit, rejectHit with
  | false, false => falseFalse
  | false, true => falseTrue
  | true, false => trueFalse
  | true, true => trueTrue

def outputWord : HitBoundary -> Word Bool
  | trueFalse => [true]
  | trueTrue => [true]
  | falseTrue => [false]
  | _ => []

theorem outputWord_ofHits
    (acceptHit rejectHit : Bool) :
    (ofHits acceptHit rejectHit).outputWord =
      MachineDescription.DovetailLayout.outputWordFromOption
        (if acceptHit = true then
          some [true]
        else if rejectHit = true then
          some [false]
        else
          none) := by
  cases acceptHit <;> cases rejectHit <;>
    rfl

end HitBoundary

def totalOutputEmitterBitValue : Bool -> Nat
  | false => 0
  | true => 1

def totalOutputEmitterCodeOfBits
    (bit0 bit1 bit2 bit3 : Bool) : Nat :=
  (((totalOutputEmitterBitValue bit0) * 2 +
      totalOutputEmitterBitValue bit1) * 2 +
      totalOutputEmitterBitValue bit2) * 2 +
    totalOutputEmitterBitValue bit3

def totalOutputEmitterSymbolCode : MachineCodeSymbol -> Nat
  | MachineCodeSymbol.header => 0
  | MachineCodeSymbol.transition => 1
  | MachineCodeSymbol.tick => 2
  | MachineCodeSymbol.done => 3
  | MachineCodeSymbol.blank => 4
  | MachineCodeSymbol.zero => 5
  | MachineCodeSymbol.one => 6
  | MachineCodeSymbol.moveLeft => 7
  | MachineCodeSymbol.moveRight => 8

def totalOutputEmitterUpdateCode
    (boundary : Nat) (code : Nat) : Nat :=
  match code with
  | 5 => (HitBoundary.fromNat boundary).updateBool false |>.toNat
  | 6 => (HitBoundary.fromNat boundary).updateBool true |>.toNat
  | _ => HitBoundary.other.toNat

def totalOutputEmitterState
    (boundary len bits : Nat) : Nat :=
  boundary * 16 + ((2 ^ len) - 1 + bits)

def totalOutputEmitterScanStateCount : Nat := 7 * 16

def totalOutputEmitterWriterSlots : Nat := 13

def totalOutputEmitterWriterStart
    (boundary : HitBoundary) : Nat :=
  totalOutputEmitterScanStateCount +
    boundary.toNat * totalOutputEmitterWriterSlots

def totalOutputEmitterHalt : Nat :=
  totalOutputEmitterScanStateCount +
    7 * totalOutputEmitterWriterSlots

def totalOutputEmitterBoundaryOutputBits
    (boundary : HitBoundary) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput
    (MachineDescription.encodeBoolWord boundary.outputWord)

def totalOutputEmitterWriterTransitionsFrom
    (source : Nat) : Word Bool -> List TransitionDescription
  | [] => []
  | bit :: rest =>
      MachineDescription.transition source none (some bit) Direction.right
          (if rest = [] then totalOutputEmitterHalt else source + 1) ::
        totalOutputEmitterWriterTransitionsFrom (source + 1) rest

def totalOutputEmitterWriterTransitions
    (boundary : HitBoundary) : List TransitionDescription :=
  totalOutputEmitterWriterTransitionsFrom
    (totalOutputEmitterWriterStart boundary)
    (totalOutputEmitterBoundaryOutputBits boundary)

def totalOutputEmitterPrefixTransitions
    (boundary : Nat) : List TransitionDescription :=
  [ MachineDescription.transition
      (totalOutputEmitterState boundary 0 0)
      (some false) none Direction.right
      (totalOutputEmitterState boundary 1 0)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 0 0)
      (some true) none Direction.right
      (totalOutputEmitterState boundary 1 1)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 1 0)
      (some false) none Direction.right
      (totalOutputEmitterState boundary 2 0)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 1 0)
      (some true) none Direction.right
      (totalOutputEmitterState boundary 2 1)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 1 1)
      (some false) none Direction.right
      (totalOutputEmitterState boundary 2 2)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 1 1)
      (some true) none Direction.right
      (totalOutputEmitterState boundary 2 3)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 2 0)
      (some false) none Direction.right
      (totalOutputEmitterState boundary 3 0)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 2 0)
      (some true) none Direction.right
      (totalOutputEmitterState boundary 3 1)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 2 1)
      (some false) none Direction.right
      (totalOutputEmitterState boundary 3 2)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 2 1)
      (some true) none Direction.right
      (totalOutputEmitterState boundary 3 3)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 2 2)
      (some false) none Direction.right
      (totalOutputEmitterState boundary 3 4)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 2 2)
      (some true) none Direction.right
      (totalOutputEmitterState boundary 3 5)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 2 3)
      (some false) none Direction.right
      (totalOutputEmitterState boundary 3 6)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 2 3)
      (some true) none Direction.right
      (totalOutputEmitterState boundary 3 7)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 3 0)
      (some false) none Direction.right
      (totalOutputEmitterState
        (totalOutputEmitterUpdateCode boundary 0) 0 0)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 3 0)
      (some true) none Direction.right
      (totalOutputEmitterState
        (totalOutputEmitterUpdateCode boundary 1) 0 0)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 3 1)
      (some false) none Direction.right
      (totalOutputEmitterState
        (totalOutputEmitterUpdateCode boundary 2) 0 0)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 3 1)
      (some true) none Direction.right
      (totalOutputEmitterState
        (totalOutputEmitterUpdateCode boundary 3) 0 0)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 3 2)
      (some false) none Direction.right
      (totalOutputEmitterState
        (totalOutputEmitterUpdateCode boundary 4) 0 0)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 3 2)
      (some true) none Direction.right
      (totalOutputEmitterState
        (totalOutputEmitterUpdateCode boundary 5) 0 0)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 3 3)
      (some false) none Direction.right
      (totalOutputEmitterState
        (totalOutputEmitterUpdateCode boundary 6) 0 0)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 3 3)
      (some true) none Direction.right
      (totalOutputEmitterState
        (totalOutputEmitterUpdateCode boundary 7) 0 0)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 3 4)
      (some false) none Direction.right
      (totalOutputEmitterState
        (totalOutputEmitterUpdateCode boundary 8) 0 0)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 3 4)
      (some true) none Direction.right
      (totalOutputEmitterState
        (totalOutputEmitterUpdateCode boundary 9) 0 0)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 3 5)
      (some false) none Direction.right
      (totalOutputEmitterState
        (totalOutputEmitterUpdateCode boundary 10) 0 0)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 3 5)
      (some true) none Direction.right
      (totalOutputEmitterState
        (totalOutputEmitterUpdateCode boundary 11) 0 0)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 3 6)
      (some false) none Direction.right
      (totalOutputEmitterState
        (totalOutputEmitterUpdateCode boundary 12) 0 0)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 3 6)
      (some true) none Direction.right
      (totalOutputEmitterState
        (totalOutputEmitterUpdateCode boundary 13) 0 0)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 3 7)
      (some false) none Direction.right
      (totalOutputEmitterState
        (totalOutputEmitterUpdateCode boundary 14) 0 0)
  , MachineDescription.transition
      (totalOutputEmitterState boundary 3 7)
      (some true) none Direction.right
      (totalOutputEmitterState
        (totalOutputEmitterUpdateCode boundary 15) 0 0)
  ]

def totalOutputEmitterBitTransitions :
    List TransitionDescription :=
  totalOutputEmitterPrefixTransitions HitBoundary.other.toNat ++
    totalOutputEmitterPrefixTransitions HitBoundary.lastFalse.toNat ++
    totalOutputEmitterPrefixTransitions HitBoundary.lastTrue.toNat ++
    totalOutputEmitterPrefixTransitions HitBoundary.falseFalse.toNat ++
    totalOutputEmitterPrefixTransitions HitBoundary.falseTrue.toNat ++
    totalOutputEmitterPrefixTransitions HitBoundary.trueFalse.toNat ++
    totalOutputEmitterPrefixTransitions HitBoundary.trueTrue.toNat

def totalOutputEmitterBlankTransitions :
    List TransitionDescription :=
  [ MachineDescription.transition
      (totalOutputEmitterState HitBoundary.other.toNat 0 0)
      none none Direction.right
      (totalOutputEmitterWriterStart HitBoundary.other)
  , MachineDescription.transition
      (totalOutputEmitterState HitBoundary.lastFalse.toNat 0 0)
      none none Direction.right
      (totalOutputEmitterWriterStart HitBoundary.lastFalse)
  , MachineDescription.transition
      (totalOutputEmitterState HitBoundary.lastTrue.toNat 0 0)
      none none Direction.right
      (totalOutputEmitterWriterStart HitBoundary.lastTrue)
  , MachineDescription.transition
      (totalOutputEmitterState HitBoundary.falseFalse.toNat 0 0)
      none none Direction.right
      (totalOutputEmitterWriterStart HitBoundary.falseFalse)
  , MachineDescription.transition
      (totalOutputEmitterState HitBoundary.falseTrue.toNat 0 0)
      none none Direction.right
      (totalOutputEmitterWriterStart HitBoundary.falseTrue)
  , MachineDescription.transition
      (totalOutputEmitterState HitBoundary.trueFalse.toNat 0 0)
      none none Direction.right
      (totalOutputEmitterWriterStart HitBoundary.trueFalse)
  , MachineDescription.transition
      (totalOutputEmitterState HitBoundary.trueTrue.toNat 0 0)
      none none Direction.right
      (totalOutputEmitterWriterStart HitBoundary.trueTrue)
  ]

def totalOutputEmitterAllWriterTransitions :
    List TransitionDescription :=
  totalOutputEmitterWriterTransitions HitBoundary.other ++
    totalOutputEmitterWriterTransitions HitBoundary.lastFalse ++
    totalOutputEmitterWriterTransitions HitBoundary.lastTrue ++
    totalOutputEmitterWriterTransitions HitBoundary.falseFalse ++
    totalOutputEmitterWriterTransitions HitBoundary.falseTrue ++
    totalOutputEmitterWriterTransitions HitBoundary.trueFalse ++
    totalOutputEmitterWriterTransitions HitBoundary.trueTrue

def Description : MachineDescription where
  stateCount := totalOutputEmitterHalt + 1
  start := totalOutputEmitterState HitBoundary.other.toNat 0 0
  halt := totalOutputEmitterHalt
  transitions :=
    totalOutputEmitterBitTransitions ++
      totalOutputEmitterBlankTransitions ++
        totalOutputEmitterAllWriterTransitions

theorem description_wellFormed :
    Description.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := Description.transitions)
      (stateCount := Description.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := Description.transitions)
      (by
        native_decide) t u ht hu hkey

theorem description_haltTransitionFree :
    Description.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := Description.transitions)
    (state := Description.halt)
    (by
      native_decide) t ht

theorem description_ready :
    ReadySpec Description :=
  ⟨description_wellFormed, description_haltTransitionFree⟩

theorem run_first_bit
    (boundary : HitBoundary)
    (bit : Bool) (erased : Nat) (suffix : Word Bool) :
    Description.runConfig 1
        { state := totalOutputEmitterState boundary.toNat 0 0
          tape := MachineDescription.eraseRightTape erased (bit :: suffix) } =
      { state :=
          totalOutputEmitterState boundary.toNat 1
            (totalOutputEmitterBitValue bit)
        tape := MachineDescription.eraseRightTape (erased + 1) suffix } := by
  cases boundary <;> cases bit <;> cases suffix <;> rfl

theorem run_second_bit
    (boundary : HitBoundary)
    (bit0 bit1 : Bool) (erased : Nat) (suffix : Word Bool) :
    Description.runConfig 1
        { state :=
            totalOutputEmitterState boundary.toNat 1
              (totalOutputEmitterBitValue bit0)
          tape := MachineDescription.eraseRightTape erased (bit1 :: suffix) } =
      { state :=
          totalOutputEmitterState boundary.toNat 2
            (totalOutputEmitterBitValue bit0 * 2 +
              totalOutputEmitterBitValue bit1)
        tape := MachineDescription.eraseRightTape (erased + 1) suffix } := by
  cases boundary <;> cases bit0 <;> cases bit1 <;> cases suffix <;> rfl

theorem run_third_bit
    (boundary : HitBoundary)
    (bit0 bit1 bit2 : Bool) (erased : Nat) (suffix : Word Bool) :
    Description.runConfig 1
        { state :=
            totalOutputEmitterState boundary.toNat 2
              (totalOutputEmitterBitValue bit0 * 2 +
                totalOutputEmitterBitValue bit1)
          tape := MachineDescription.eraseRightTape erased (bit2 :: suffix) } =
      { state :=
          totalOutputEmitterState boundary.toNat 3
            ((totalOutputEmitterBitValue bit0 * 2 +
                totalOutputEmitterBitValue bit1) * 2 +
              totalOutputEmitterBitValue bit2)
        tape := MachineDescription.eraseRightTape (erased + 1) suffix } := by
  cases boundary <;> cases bit0 <;> cases bit1 <;> cases bit2 <;>
    cases suffix <;> rfl

theorem run_fourth_bit
    (boundary : HitBoundary)
    (bit0 bit1 bit2 bit3 : Bool) (erased : Nat) (suffix : Word Bool) :
    Description.runConfig 1
        { state :=
            totalOutputEmitterState boundary.toNat 3
              ((totalOutputEmitterBitValue bit0 * 2 +
                  totalOutputEmitterBitValue bit1) * 2 +
                totalOutputEmitterBitValue bit2)
          tape := MachineDescription.eraseRightTape erased (bit3 :: suffix) } =
      { state :=
          totalOutputEmitterState
            (totalOutputEmitterUpdateCode boundary.toNat
              (totalOutputEmitterCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := MachineDescription.eraseRightTape (erased + 1) suffix } := by
  cases boundary <;> cases bit0 <;> cases bit1 <;> cases bit2 <;>
    cases bit3 <;> cases suffix <;> rfl

theorem run_bits
    (boundary : HitBoundary)
    (bit0 bit1 bit2 bit3 : Bool)
    (erased : Nat) (suffix : Word Bool) :
    Description.runConfig 4
        { state := totalOutputEmitterState boundary.toNat 0 0
          tape :=
            MachineDescription.eraseRightTape erased
              (List.append [bit0, bit1, bit2, bit3] suffix) } =
      { state :=
          totalOutputEmitterState
            (totalOutputEmitterUpdateCode boundary.toNat
              (totalOutputEmitterCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := MachineDescription.eraseRightTape (erased + 4) suffix } := by
  rw [show 4 = 1 + 3 by omega, MachineDescription.runConfig_add]
  change
    Description.runConfig 3
        (Description.runConfig 1
          { state := totalOutputEmitterState boundary.toNat 0 0
            tape :=
              MachineDescription.eraseRightTape erased
                (bit0 :: bit1 :: bit2 :: bit3 :: suffix) }) =
      { state :=
          totalOutputEmitterState
            (totalOutputEmitterUpdateCode boundary.toNat
              (totalOutputEmitterCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := MachineDescription.eraseRightTape (erased + 4) suffix }
  rw [run_first_bit]
  rw [show 3 = 1 + 2 by omega, MachineDescription.runConfig_add]
  change
    Description.runConfig 2
        (Description.runConfig 1
          { state :=
              totalOutputEmitterState boundary.toNat 1
                (totalOutputEmitterBitValue bit0)
            tape :=
              MachineDescription.eraseRightTape (erased + 1)
                (bit1 :: bit2 :: bit3 :: suffix) }) =
      { state :=
          totalOutputEmitterState
            (totalOutputEmitterUpdateCode boundary.toNat
              (totalOutputEmitterCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := MachineDescription.eraseRightTape (erased + 4) suffix }
  rw [run_second_bit]
  rw [show 2 = 1 + 1 by omega, MachineDescription.runConfig_add]
  change
    Description.runConfig 1
        (Description.runConfig 1
          { state :=
              totalOutputEmitterState boundary.toNat 2
                (totalOutputEmitterBitValue bit0 * 2 +
                  totalOutputEmitterBitValue bit1)
            tape :=
              MachineDescription.eraseRightTape ((erased + 1) + 1)
                (bit2 :: bit3 :: suffix) }) =
      { state :=
          totalOutputEmitterState
            (totalOutputEmitterUpdateCode boundary.toNat
              (totalOutputEmitterCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := MachineDescription.eraseRightTape (erased + 4) suffix }
  rw [run_third_bit]
  rw [run_fourth_bit]

theorem updateCode_symbol
    (boundary : HitBoundary)
    (symbol : MachineCodeSymbol) :
    totalOutputEmitterUpdateCode boundary.toNat
        (totalOutputEmitterSymbolCode symbol) =
      (boundary.update symbol).toNat := by
  cases boundary <;> cases symbol <;> rfl

theorem run_encoded_symbol
    (boundary : HitBoundary)
    (symbol : MachineCodeSymbol)
    (erased : Nat) (suffix : Word Bool) :
    Description.runConfig 4
        { state := totalOutputEmitterState boundary.toNat 0 0
          tape :=
            MachineDescription.eraseRightTape erased
              (List.append
                (MachineDescription.encodeCodeSymbolAsInput symbol) suffix) } =
      { state :=
          totalOutputEmitterState
            (totalOutputEmitterUpdateCode boundary.toNat
              (totalOutputEmitterSymbolCode symbol)) 0 0
        tape := MachineDescription.eraseRightTape (erased + 4) suffix } := by
  cases symbol
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      totalOutputEmitterCodeOfBits, totalOutputEmitterSymbolCode] using
      (run_bits boundary false false false false erased suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      totalOutputEmitterCodeOfBits, totalOutputEmitterSymbolCode] using
      (run_bits boundary false false false true erased suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      totalOutputEmitterCodeOfBits, totalOutputEmitterSymbolCode] using
      (run_bits boundary false false true false erased suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      totalOutputEmitterCodeOfBits, totalOutputEmitterSymbolCode] using
      (run_bits boundary false false true true erased suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      totalOutputEmitterCodeOfBits, totalOutputEmitterSymbolCode] using
      (run_bits boundary false true false false erased suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      totalOutputEmitterCodeOfBits, totalOutputEmitterSymbolCode] using
      (run_bits boundary false true false true erased suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      totalOutputEmitterCodeOfBits, totalOutputEmitterSymbolCode] using
      (run_bits boundary false true true false erased suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      totalOutputEmitterCodeOfBits, totalOutputEmitterSymbolCode] using
      (run_bits boundary false true true true erased suffix)
  · simpa [MachineDescription.encodeCodeSymbolAsInput,
      totalOutputEmitterCodeOfBits, totalOutputEmitterSymbolCode] using
      (run_bits boundary true false false false erased suffix)

theorem run_symbol
    (boundary : HitBoundary)
    (symbol : MachineCodeSymbol)
    (erased : Nat) (suffix : Word Bool) :
    Description.runConfig 4
        { state :=
            totalOutputEmitterState boundary.toNat 0 0
          tape :=
            MachineDescription.eraseRightTape erased
              (List.append
                (MachineDescription.encodeCodeSymbolAsInput symbol) suffix) } =
      { state :=
          totalOutputEmitterState
            (boundary.update symbol).toNat 0 0
        tape := MachineDescription.eraseRightTape (erased + 4) suffix } := by
  rw [run_encoded_symbol]
  rw [updateCode_symbol]

def scanBoundaryFrom
    (boundary : HitBoundary) :
    Word MachineCodeSymbol -> HitBoundary
  | [] => boundary
  | symbol :: rest =>
      scanBoundaryFrom (boundary.update symbol) rest

def scanBoundary
    (code : Word MachineCodeSymbol) : HitBoundary :=
  scanBoundaryFrom HitBoundary.other code

theorem scanBoundaryFrom_append
    (boundary : HitBoundary)
    (pre suffix : Word MachineCodeSymbol) :
    scanBoundaryFrom boundary (List.append pre suffix) =
      scanBoundaryFrom (scanBoundaryFrom boundary pre) suffix := by
  induction pre generalizing boundary with
  | nil =>
      rfl
  | cons symbol rest ih =>
      exact ih (boundary.update symbol)

theorem run_code_from
    (boundary : HitBoundary)
    (code : Word MachineCodeSymbol)
    (erased : Nat) (suffix : Word Bool) :
    Description.runConfig
        (4 * code.length)
        { state :=
            totalOutputEmitterState boundary.toNat 0 0
          tape :=
            MachineDescription.eraseRightTape erased
              (List.append
                (MachineDescription.encodeCodeWordAsInput code) suffix) } =
      { state :=
          totalOutputEmitterState
            (scanBoundaryFrom boundary code).toNat 0 0
        tape :=
          MachineDescription.eraseRightTape
            (erased + 4 * code.length) suffix } := by
  induction code generalizing boundary erased with
  | nil =>
      simp [MachineDescription.encodeCodeWordAsInput,
        scanBoundaryFrom, MachineDescription.runConfig]
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
        Description.runConfig
            (4 * rest.length)
            (Description.runConfig 4
              { state := totalOutputEmitterState boundary.toNat 0 0
                tape :=
                  MachineDescription.eraseRightTape erased
                    (List.append
                      (MachineDescription.encodeCodeSymbolAsInput symbol)
                      (List.append
                        (MachineDescription.encodeCodeWordAsInput rest)
                        suffix)) }) =
          { state :=
              totalOutputEmitterState
                (scanBoundaryFrom boundary (symbol :: rest)).toNat 0 0
            tape :=
              MachineDescription.eraseRightTape
                (erased + (4 + 4 * rest.length)) suffix }
      rw [run_symbol]
      rw [ih]
      simp [scanBoundaryFrom]
      congr 1
      omega

def finalTape (erased : Nat) (boundary : HitBoundary) :
    Tape Bool :=
  { left :=
      (totalOutputEmitterBoundaryOutputBits boundary).reverse.map some ++
        List.replicate (erased + 1) none
    head := none
    right := [] }

theorem run_blank
    (boundary : HitBoundary) (erased : Nat) :
    Description.runConfig
        (1 + (totalOutputEmitterBoundaryOutputBits boundary).length)
        { state := totalOutputEmitterState boundary.toNat 0 0
          tape := MachineDescription.eraseRightTape erased [] } =
      { state := Description.halt
        tape := finalTape erased boundary } := by
  cases boundary <;> rfl

theorem run_code_halt
    (code : Word MachineCodeSymbol) :
    Description.runConfig
        (4 * code.length + 1 +
          (totalOutputEmitterBoundaryOutputBits
            (scanBoundary code)).length)
        (Description.initial
          (MachineDescription.encodeCodeWordAsInput code)) =
      { state := Description.halt
        tape :=
          finalTape (0 + 4 * code.length)
            (scanBoundary code) } := by
  rw [show
      4 * code.length + 1 +
          (totalOutputEmitterBoundaryOutputBits
            (scanBoundary code)).length =
        4 * code.length +
          (1 + (totalOutputEmitterBoundaryOutputBits
            (scanBoundary code)).length) by omega]
  rw [MachineDescription.runConfig_add]
  have hinitial :
      Description.initial
          (MachineDescription.encodeCodeWordAsInput code) =
        { state :=
            totalOutputEmitterState HitBoundary.other.toNat 0 0
          tape :=
            MachineDescription.eraseRightTape 0
              (List.append
                (MachineDescription.encodeCodeWordAsInput code) []) } := by
    simp [Description, MachineDescription.initial,
      MachineDescription.eraseRightTape_zero_eq_input]
  rw [hinitial]
  rw [run_code_from]
  change
    Description.runConfig
        (1 + (totalOutputEmitterBoundaryOutputBits
          (scanBoundary code)).length)
        { state := totalOutputEmitterState (scanBoundary code).toNat 0 0
          tape := MachineDescription.eraseRightTape
            (0 + 4 * code.length) [] } =
      { state := Description.halt
        tape :=
          finalTape (0 + 4 * code.length)
            (scanBoundary code) }
  rw [run_blank]

theorem finalTape_normalizedOutput
    (boundary : HitBoundary) (erased : Nat) :
    Tape.normalizedOutput (finalTape erased boundary) =
      totalOutputEmitterBoundaryOutputBits boundary := by
  have hfilter :
      forall xs : Word Bool,
        List.filterMap
            ((fun cell : Option Bool => cell) ∘
              (fun b : Bool => some b)) xs = xs := by
    intro xs
    induction xs with
    | nil =>
        rfl
    | cons b rest ih =>
        simp [Function.comp, ih]
  simp [finalTape, Tape.normalizedOutput, Tape.cells,
    List.filterMap_append, List.reverse_append, hfilter]

theorem haltsWithOutput_code
    (code : Word MachineCodeSymbol) :
    Description.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput code)
      (totalOutputEmitterBoundaryOutputBits (scanBoundary code)) := by
  refine
    ⟨4 * code.length + 1 +
      (totalOutputEmitterBoundaryOutputBits (scanBoundary code)).length, ?_⟩
  constructor
  · rw [run_code_halt]
  · rw [run_code_halt]
    exact finalTape_normalizedOutput
      (scanBoundary code) (0 + 4 * code.length)

theorem scanBoundaryFrom_hit_suffix
    (boundary : HitBoundary) (acceptHit rejectHit : Bool) :
    scanBoundaryFrom boundary
        (MachineDescription.encodeBoolAppend acceptHit
          (MachineDescription.encodeBoolAppend rejectHit [])) =
      HitBoundary.ofHits acceptHit rejectHit := by
  cases boundary <;> cases acceptHit <;> cases rejectHit <;>
    rfl

theorem scanBoundary_encode
    (L : MachineDescription.DovetailLayout) :
    scanBoundary (MachineDescription.DovetailLayout.encode L) =
      HitBoundary.ofHits L.acceptHit L.rejectHit := by
  cases L with
  | mk input stage acceptConfig rejectConfig acceptHit rejectHit =>
      let suffix : Word MachineCodeSymbol :=
        MachineDescription.encodeBoolAppend acceptHit
          (MachineDescription.encodeBoolAppend rejectHit [])
      let pre : Word MachineCodeSymbol :=
        MachineCodeSymbol.transition ::
          MachineDescription.encodeBoolWordAppend input
            (MachineDescription.encodeNatAppend stage
              (MachineDescription.encodeConfigurationAppend acceptConfig
                (MachineDescription.encodeConfigurationAppend rejectConfig [])))
      have hreject :
          MachineDescription.encodeConfigurationAppend rejectConfig suffix =
            List.append
              (MachineDescription.encodeConfigurationAppend rejectConfig [])
              suffix := by
        simpa [suffix] using
          encodeConfigurationAppend_append rejectConfig
            ([] : Word MachineCodeSymbol) suffix
      have haccept :
          MachineDescription.encodeConfigurationAppend acceptConfig
              (MachineDescription.encodeConfigurationAppend rejectConfig
                suffix) =
            List.append
              (MachineDescription.encodeConfigurationAppend acceptConfig
                (MachineDescription.encodeConfigurationAppend rejectConfig []))
              suffix := by
        rw [hreject]
        exact
          encodeConfigurationAppend_append acceptConfig
            (MachineDescription.encodeConfigurationAppend rejectConfig [])
            suffix
      have hstage :
          MachineDescription.encodeNatAppend stage
              (MachineDescription.encodeConfigurationAppend acceptConfig
                (MachineDescription.encodeConfigurationAppend rejectConfig
                  suffix)) =
            List.append
              (MachineDescription.encodeNatAppend stage
                (MachineDescription.encodeConfigurationAppend acceptConfig
                  (MachineDescription.encodeConfigurationAppend rejectConfig [])))
              suffix := by
        rw [haccept]
        exact
          encodeNatAppend_append stage
            (MachineDescription.encodeConfigurationAppend acceptConfig
              (MachineDescription.encodeConfigurationAppend rejectConfig []))
            suffix
      have hinput :
          MachineDescription.encodeBoolWordAppend input
              (MachineDescription.encodeNatAppend stage
                (MachineDescription.encodeConfigurationAppend acceptConfig
                  (MachineDescription.encodeConfigurationAppend rejectConfig
                    suffix))) =
            List.append
              (MachineDescription.encodeBoolWordAppend input
                (MachineDescription.encodeNatAppend stage
                  (MachineDescription.encodeConfigurationAppend acceptConfig
                    (MachineDescription.encodeConfigurationAppend rejectConfig []))))
              suffix := by
        rw [hstage]
        exact
          encodeBoolWordAppend_append input
            (MachineDescription.encodeNatAppend stage
              (MachineDescription.encodeConfigurationAppend acceptConfig
                (MachineDescription.encodeConfigurationAppend rejectConfig [])))
            suffix
      change
        scanBoundaryFrom HitBoundary.other
          (MachineCodeSymbol.transition ::
            MachineDescription.encodeBoolWordAppend input
              (MachineDescription.encodeNatAppend stage
                (MachineDescription.encodeConfigurationAppend acceptConfig
                  (MachineDescription.encodeConfigurationAppend rejectConfig
                    suffix)))) =
          HitBoundary.ofHits acceptHit rejectHit
      rw [hinput]
      change
        scanBoundaryFrom HitBoundary.other
          (List.append pre suffix) =
          HitBoundary.ofHits acceptHit rejectHit
      rw [scanBoundaryFrom_append]
      exact scanBoundaryFrom_hit_suffix
        (scanBoundaryFrom HitBoundary.other pre) acceptHit rejectHit

theorem boundaryOutputBits_encode
    (L : MachineDescription.DovetailLayout) :
    totalOutputEmitterBoundaryOutputBits
        (scanBoundary (MachineDescription.DovetailLayout.encode L)) =
      OutputBits L := by
  rw [scanBoundary_encode]
  cases L with
  | mk input stage acceptConfig rejectConfig acceptHit rejectHit =>
      cases acceptHit <;> cases rejectHit <;>
        rfl

theorem description_forward :
    ForwardSpec Description := by
  intro L
  simpa [boundaryOutputBits_encode L] using
    haltsWithOutput_code
      (MachineDescription.DovetailLayout.encode L)

theorem finiteDescriptionConstruction_scaffold :
    FiniteDescriptionConstruction := by
  exact ⟨Description, description_ready, description_forward⟩

def OutputRealizedConstruction : Prop :=
  exists emitter : MachineDescription,
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      PairedRecognizerDovetailTotalOutputCode
      emitter

theorem outputRealized_of_spec
    {emitter : MachineDescription}
    (hemitter : Spec emitter) :
    TapeCodePrimitiveOutputSubroutineRealizedByDescription
      PairedRecognizerDovetailTotalOutputCode
      emitter := by
  constructor
  · constructor
    · exact hemitter.left.left
    · intro code out htransform
      rcases
          (pairedRecognizerDovetailTotalOutputCode_transform_eq_some_iff
            code out).mp htransform with
        ⟨L, hcode, hout⟩
      subst code
      subst out
      exact hemitter.right L
  · exact hemitter.left.right

theorem outputRealizedConstruction_scaffold :
    OutputRealizedConstruction := by
  rcases finiteDescriptionConstruction_scaffold with
    ⟨emitter, hemitter⟩
  exact
    ⟨emitter,
      outputRealized_of_spec hemitter⟩

theorem outputRealizedSubroutine :
    exists emitter : MachineDescription,
      TapeCodePrimitiveOutputSubroutineRealizedByDescription
        PairedRecognizerDovetailTotalOutputCode
        emitter :=
  outputRealizedConstruction_scaffold

/- There is deliberately no closed-handoff theorem for this primitive: the
   output may be shorter than the input, so the exact right-shifted handoff tape
   is not reachable in general.  The two earlier dovetail phases validate and
   hand off canonical layouts; this final phase realizes the normalized output
   on those valid layout inputs. -/

end TotalOutputEmitter
end EncodedRewriters

end Computability
end FoC
