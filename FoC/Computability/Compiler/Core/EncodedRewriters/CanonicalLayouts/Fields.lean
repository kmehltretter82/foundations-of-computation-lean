import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.Basic

set_option doc.verso true

/-!
# Canonical scalar and payload-field validators
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace CanonicalLayouts
namespace Fields

def decodeNatComplete (code : Word MachineCodeSymbol) : Option Nat :=
  match MachineDescription.decodeNat code with
  | some (n, []) => some n
  | _ => none

def decodeBoolWordComplete
    (code : Word MachineCodeSymbol) : Option (Word Bool) :=
  match MachineDescription.decodeBoolWord code with
  | some (w, []) => some w
  | _ => none

def decodeCodeWordFieldComplete
    (code : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match MachineDescription.decodeBoolWord code with
  | some (bits, []) => MachineDescription.decodeCodeWordAsInput bits
  | _ => none

theorem decodeNatComplete_encode (n : Nat) :
    decodeNatComplete (MachineDescription.encodeNat n) = some n := by
  have hdecode :
      MachineDescription.decodeNat (MachineDescription.encodeNat n) =
        some (n, []) := by
    simpa using MachineDescription.decodeNat_encodeNat_append n []
  rw [decodeNatComplete, hdecode]

theorem decodeNatComplete_eq_some_encode
    {code : Word MachineCodeSymbol} {n : Nat}
    (h : decodeNatComplete code = some n) :
    code = MachineDescription.encodeNat n := by
  unfold decodeNatComplete at h
  cases hdecode : MachineDescription.decodeNat code with
  | none =>
      simp [hdecode] at h
  | some parsed =>
      cases parsed with
      | mk decoded suffix =>
          cases suffix with
          | nil =>
              simp [hdecode] at h
              cases h
              simpa [MachineDescription.encodeNatAppend] using
                MachineDescription.decodeNat_eq_some_encodeNatAppend hdecode
          | cons _ _ =>
              simp [hdecode] at h

theorem decodeBoolWordComplete_encode (w : Word Bool) :
    decodeBoolWordComplete (MachineDescription.encodeBoolWord w) = some w := by
  rw [decodeBoolWordComplete,
    MachineDescription.decodeBoolWord_encodeBoolWord w]

theorem decodeBoolWordComplete_eq_some_encode
    {code : Word MachineCodeSymbol} {w : Word Bool}
    (h : decodeBoolWordComplete code = some w) :
    code = MachineDescription.encodeBoolWord w := by
  unfold decodeBoolWordComplete at h
  cases hdecode : MachineDescription.decodeBoolWord code with
  | none =>
      simp [hdecode] at h
  | some parsed =>
      cases parsed with
      | mk decoded suffix =>
          cases suffix with
          | nil =>
              simp [hdecode] at h
              cases h
              simpa [MachineDescription.encodeBoolWord] using
                MachineDescription.decodeBoolWord_eq_some_encodeBoolWordAppend
                  hdecode
          | cons _ _ =>
              simp [hdecode] at h

theorem decodeCodeWordFieldComplete_encode
    (code : Word MachineCodeSymbol) :
    decodeCodeWordFieldComplete
        (MachineDescription.encodeBoolWord
          (MachineDescription.encodeCodeWordAsInput code)) =
      some code := by
  simp [decodeCodeWordFieldComplete,
    MachineDescription.decodeBoolWord_encodeBoolWord,
    MachineDescription.decodeCodeWordAsInput_encodeCodeWordAsInput]

theorem decodeCodeWordFieldComplete_eq_some_encode
    {field code : Word MachineCodeSymbol}
    (h : decodeCodeWordFieldComplete field = some code) :
    field =
      MachineDescription.encodeBoolWord
        (MachineDescription.encodeCodeWordAsInput code) := by
  unfold decodeCodeWordFieldComplete at h
  cases hdecode : MachineDescription.decodeBoolWord field with
  | none =>
      simp [hdecode] at h
  | some parsed =>
      cases parsed with
      | mk bits suffix =>
          cases suffix with
          | nil =>
              simp [hdecode] at h
              have hbits :
                  bits = MachineDescription.encodeCodeWordAsInput code :=
                MachineDescription.decodeCodeWordAsInput_eq_some_encodeCodeWordAsInput
                  h
              have hfield :
                  field = MachineDescription.encodeBoolWord bits := by
                simpa [MachineDescription.encodeBoolWord] using
                  MachineDescription.decodeBoolWord_eq_some_encodeBoolWordAppend
                    hdecode
              rw [hfield, hbits]
          | cons _ _ =>
              simp [hdecode] at h

theorem encodeNat_cons (n : Nat) :
    exists symbol : MachineCodeSymbol,
    exists tail : Word MachineCodeSymbol,
      MachineDescription.encodeNat n = symbol :: tail := by
  cases n with
  | zero => exact ⟨MachineCodeSymbol.done, [], rfl⟩
  | succ n => exact ⟨MachineCodeSymbol.tick, MachineDescription.encodeNat n, rfl⟩

theorem encodeBoolWord_cons (w : Word Bool) :
    exists symbol : MachineCodeSymbol,
    exists tail : Word MachineCodeSymbol,
      MachineDescription.encodeBoolWord w = symbol :: tail :=
  EncodedRewriters.encodeBoolWord_cons w

end Fields
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
