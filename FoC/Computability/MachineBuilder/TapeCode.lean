import FoC.Computability.MachineBuilder.Encoding

set_option doc.verso true

/-!
# Machine-builder tape-code primitives
-/

namespace FoC
namespace Computability

open Languages

namespace MachineDescription

/-!
## Executable tape-code primitives

These primitives are executable transformations on the finite
{name}`MachineCodeSymbol` words that represent work-tape layouts.  They are
not transition tables yet; they are the precise code-level behavior that later
finite fragments must realize.
-/

structure TapeCodePrimitive where
  transform :
    Word MachineCodeSymbol -> Option (Word MachineCodeSymbol)

namespace TapeCodePrimitive

def Realizes (P : TapeCodePrimitive)
    (f : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol)) :
    Prop :=
  forall w : Word MachineCodeSymbol, P.transform w = f w

def identity : TapeCodePrimitive where
  transform := fun w => some w

theorem identity_transform (w : Word MachineCodeSymbol) :
    identity.transform w = some w :=
  rfl

theorem identity_realizes :
    identity.Realizes (fun w => some w) := by
  intro w
  rfl

def erase : TapeCodePrimitive where
  transform := fun _ => some []

theorem erase_transform (w : Word MachineCodeSymbol) :
    erase.transform w = some [] :=
  rfl

theorem erase_realizes :
    erase.Realizes (fun _ => some []) := by
  intro w
  rfl

def prepend (pre : Word MachineCodeSymbol) : TapeCodePrimitive where
  transform := fun w => some (List.append pre w)

theorem prepend_transform
    (pre w : Word MachineCodeSymbol) :
    (prepend pre).transform w = some (List.append pre w) :=
  rfl

theorem prepend_realizes (pre : Word MachineCodeSymbol) :
    (prepend pre).Realizes (fun w => some (List.append pre w)) := by
  intro w
  rfl

def append (suffix : Word MachineCodeSymbol) : TapeCodePrimitive where
  transform := fun w => some (List.append w suffix)

theorem append_transform
    (suffix w : Word MachineCodeSymbol) :
    (append suffix).transform w = some (List.append w suffix) :=
  rfl

theorem append_realizes (suffix : Word MachineCodeSymbol) :
    (append suffix).Realizes (fun w => some (List.append w suffix)) := by
  intro w
  rfl

def compareNatEq (target : Nat) : TapeCodePrimitive where
  transform := fun tokens =>
    match decodeNat tokens with
    | none => none
    | some (n, suffix) => some (encodeBoolAppend (n == target) suffix)

theorem compareNatEq_transform_encodeNatAppend
    (target n : Nat) (suffix : Word MachineCodeSymbol) :
    (compareNatEq target).transform (encodeNatAppend n suffix) =
      some (encodeBoolAppend (n == target) suffix) := by
  simp [compareNatEq, decodeNat_encodeNatAppend]

theorem compareNatEq_result_true_iff
    (target n : Nat) :
    (n == target) = true <-> n = target := by
  simp

def compareNatLt (bound : Nat) : TapeCodePrimitive where
  transform := fun tokens =>
    match decodeNat tokens with
    | none => none
    | some (n, suffix) =>
        some (encodeBoolAppend (decide (n < bound)) suffix)

theorem compareNatLt_transform_encodeNatAppend
    (bound n : Nat) (suffix : Word MachineCodeSymbol) :
    (compareNatLt bound).transform (encodeNatAppend n suffix) =
      some (encodeBoolAppend (decide (n < bound)) suffix) := by
  simp [compareNatLt, decodeNat_encodeNatAppend]

theorem compareNatLt_result_true_iff
    (bound n : Nat) :
    decide (n < bound) = true <-> n < bound := by
  simp

def writeHead (cell : Option Bool) : TapeCodePrimitive where
  transform := fun tokens =>
    match decodeTape tokens with
    | some (T, []) => some (encodeTape (Tape.write cell T))
    | _ => none

theorem writeHead_transform_encodeTape
    (cell : Option Bool) (T : Tape Bool) :
    (writeHead cell).transform (encodeTape T) =
      some (encodeTape (Tape.write cell T)) := by
  simp [writeHead, decodeTape_encodeTape]

def moveHead (dir : Direction) : TapeCodePrimitive where
  transform := fun tokens =>
    match decodeTape tokens with
    | some (T, []) => some (encodeTape (Tape.move dir T))
    | _ => none

theorem moveHead_transform_encodeTape
    (dir : Direction) (T : Tape Bool) :
    (moveHead dir).transform (encodeTape T) =
      some (encodeTape (Tape.move dir T)) := by
  simp [moveHead, decodeTape_encodeTape]

def writeMove (cell : Option Bool) (dir : Direction) :
    TapeCodePrimitive where
  transform := fun tokens =>
    match decodeTape tokens with
    | some (T, []) =>
        some (encodeTape (Tape.move dir (Tape.write cell T)))
    | _ => none

theorem writeMove_transform_encodeTape
    (cell : Option Bool) (dir : Direction) (T : Tape Bool) :
    (writeMove cell dir).transform (encodeTape T) =
      some (encodeTape (Tape.move dir (Tape.write cell T))) := by
  simp [writeMove, decodeTape_encodeTape]

def transitionTapeAction
    (t : TransitionDescription) : TapeCodePrimitive :=
  writeMove t.write t.move

theorem transitionTapeAction_transform_encodeTape
    (t : TransitionDescription) (T : Tape Bool) :
    (transitionTapeAction t).transform (encodeTape T) =
      some (encodeTape
        (Tape.move t.move (Tape.write t.write T))) := by
  simp [transitionTapeAction, writeMove_transform_encodeTape]

theorem transitionTapeAction_transform_encodeTape_of_lookupTransition
    {D : MachineDescription} {c : Configuration}
    {t : TransitionDescription}
    (hlookup :
      D.lookupTransition c.state (Tape.read c.tape) = some t) :
    (transitionTapeAction t).transform (encodeTape c.tape) =
      some (encodeTape (D.runConfig 1 c).tape) := by
  rw [transitionTapeAction_transform_encodeTape,
    runConfig_one_of_lookupTransition_some hlookup]

def compose (P Q : TapeCodePrimitive) : TapeCodePrimitive where
  transform := fun w =>
    match P.transform w with
    | none => none
    | some mid => Q.transform mid

theorem compose_transform_some
    {P Q : TapeCodePrimitive}
    {w mid out : Word MachineCodeSymbol}
    (hP : P.transform w = some mid)
    (hQ : Q.transform mid = some out) :
    (compose P Q).transform w = some out := by
  simp [compose, hP, hQ]

theorem compose_realizes
    {P Q : TapeCodePrimitive}
    {f g : Word MachineCodeSymbol -> Option (Word MachineCodeSymbol)}
    (hP : P.Realizes f)
    (hQ : Q.Realizes g) :
    (compose P Q).Realizes
      (fun w =>
        match f w with
        | none => none
        | some mid => g mid) := by
  intro w
  simp [Realizes] at hP hQ
  unfold compose
  simp
  rw [hP w]
  cases hfw : f w with
  | none =>
      simp
  | some mid =>
      simp [hQ mid]

end TapeCodePrimitive

def stepConfigurationCodePrimitive
    (D : MachineDescription) : TapeCodePrimitive where
  transform := stepConfigurationCode D

theorem stepConfigurationCodePrimitive_encodeConfiguration
    (D : MachineDescription) (c : Configuration) :
    (stepConfigurationCodePrimitive D).transform
        (encodeConfiguration c) =
      some (encodeConfiguration (D.runConfig 1 c)) :=
  stepConfigurationCode_encodeConfiguration D c

end MachineDescription

end Computability
end FoC
