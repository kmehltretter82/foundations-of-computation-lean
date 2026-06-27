import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.Basic

set_option doc.verso true

/-!
# Canonical scalar and payload-field validators
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace CanonicalLayouts
namespace Fields

def decodeNatComplete (code : Word MachineCodeSymbol) : Option Nat :=
  match decodeNat code with
  | some (n, []) => some n
  | _ => none

def decodeBoolWordComplete
    (code : Word MachineCodeSymbol) : Option (Word Bool) :=
  match decodeBoolWord code with
  | some (w, []) => some w
  | _ => none

def decodeBoolComplete (code : Word MachineCodeSymbol) : Option Bool :=
  match decodeBool code with
  | some (b, []) => some b
  | _ => none

def decodeCodeWordFieldComplete
    (code : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodeBoolWord code with
  | some (bits, []) => decodeCodeWordAsInput bits
  | _ => none

def decodeCellListComplete
    (code : Word MachineCodeSymbol) :
    Option (List (Option Bool)) :=
  match decodeCellList code with
  | some (cells, []) => some cells
  | _ => none

def decodeTapeComplete
    (code : Word MachineCodeSymbol) : Option (Tape Bool) :=
  match decodeTape code with
  | some (T, []) => some T
  | _ => none

def decodeConfigurationComplete
    (code : Word MachineCodeSymbol) :
    Option Configuration :=
  match decodeConfiguration code with
  | some (cfg, []) => some cfg
  | _ => none

theorem decodeNatComplete_encode (n : Nat) :
    decodeNatComplete (encodeNat n) = some n := by
  have hdecode :
      decodeNat (encodeNat n) =
        some (n, []) := by
    simpa using decodeNat_encodeNat_append n []
  rw [decodeNatComplete, hdecode]

theorem decodeNatComplete_eq_some_encode
    {code : Word MachineCodeSymbol} {n : Nat}
    (h : decodeNatComplete code = some n) :
    code = encodeNat n := by
  unfold decodeNatComplete at h
  cases hdecode : decodeNat code with
  | none =>
      simp [hdecode] at h
  | some parsed =>
      cases parsed with
      | mk decoded suffix =>
          cases suffix with
          | nil =>
              simp [hdecode] at h
              cases h
              simpa [encodeNatAppend] using
                decodeNat_eq_some_encodeNatAppend hdecode
          | cons _ _ =>
              simp [hdecode] at h

theorem decodeBoolWordComplete_encode (w : Word Bool) :
    decodeBoolWordComplete (encodeBoolWord w) =
      some w := by
  simp [decodeBoolWordComplete,
    decodeBoolWord_encodeBoolWord]

theorem decodeBoolWordComplete_eq_some_encode
    {code : Word MachineCodeSymbol} {w : Word Bool}
    (h : decodeBoolWordComplete code = some w) :
    code = encodeBoolWord w := by
  unfold decodeBoolWordComplete at h
  cases hdecode : decodeBoolWord code with
  | none =>
      simp [hdecode] at h
  | some parsed =>
      cases parsed with
      | mk decoded suffix =>
          cases suffix with
          | nil =>
              simp [hdecode] at h
              cases h
              simpa [encodeBoolWord] using
                decodeBoolWord_eq_some_encodeBoolWordAppend
                  hdecode
          | cons _ _ =>
              simp [hdecode] at h

theorem decodeBoolComplete_encode (b : Bool) :
    decodeBoolComplete (encodeBoolAppend b []) =
      some b := by
  simp [decodeBoolComplete, decodeBool_encodeBoolAppend]

theorem decodeBoolComplete_eq_some_encode
    {code : Word MachineCodeSymbol} {b : Bool}
    (h : decodeBoolComplete code = some b) :
    code = encodeBoolAppend b [] := by
  unfold decodeBoolComplete at h
  cases hdecode : decodeBool code with
  | none =>
      simp [hdecode] at h
  | some parsed =>
      cases parsed with
      | mk decoded suffix =>
          cases suffix with
          | nil =>
              simp [hdecode] at h
              cases h
              exact
                decodeBool_eq_some_encodeBoolAppend
                  hdecode
          | cons _ _ =>
              simp [hdecode] at h

theorem decodeCodeWordFieldComplete_encode
    (code : Word MachineCodeSymbol) :
    decodeCodeWordFieldComplete
        (encodeBoolWord
          (encodeCodeWordAsInput code)) =
      some code := by
  simp [decodeCodeWordFieldComplete,
    decodeBoolWord_encodeBoolWord,
    decodeCodeWordAsInput_encodeCodeWordAsInput]

theorem decodeCodeWordFieldComplete_eq_some_encode
    {field code : Word MachineCodeSymbol}
    (h : decodeCodeWordFieldComplete field = some code) :
    field =
      encodeBoolWord
        (encodeCodeWordAsInput code) := by
  unfold decodeCodeWordFieldComplete at h
  cases hdecode : decodeBoolWord field with
  | none =>
      simp [hdecode] at h
  | some parsed =>
      cases parsed with
      | mk bits suffix =>
          cases suffix with
          | nil =>
              simp [hdecode] at h
              have hbits :
                  bits = encodeCodeWordAsInput code :=
                decodeCodeWordAsInput_eq_some_encodeCodeWordAsInput
                  h
              have hfield :
                  field = encodeBoolWord bits := by
                simpa [encodeBoolWord] using
                  decodeBoolWord_eq_some_encodeBoolWordAppend
                    hdecode
              rw [hfield, hbits]
          | cons _ _ =>
              simp [hdecode] at h

theorem decodeCellListComplete_encode
    (cells : List (Option Bool)) :
    decodeCellListComplete
        (encodeCellListAppend cells []) =
      some cells := by
  simp [decodeCellListComplete,
    decodeCellList_encodeCellListAppend]

theorem decodeCellListComplete_eq_some_encode
    {code : Word MachineCodeSymbol}
    {cells : List (Option Bool)}
    (h : decodeCellListComplete code = some cells) :
    code = encodeCellListAppend cells [] := by
  unfold decodeCellListComplete at h
  cases hdecode : decodeCellList code with
  | none =>
      simp [hdecode] at h
  | some parsed =>
      cases parsed with
      | mk decoded suffix =>
          cases suffix with
          | nil =>
              simp [hdecode] at h
              cases h
              exact
                decodeCellList_eq_some_encodeCellListAppend
                  hdecode
          | cons _ _ =>
              simp [hdecode] at h

theorem decodeTapeComplete_encode
    (T : Tape Bool) :
    decodeTapeComplete (encodeTape T) = some T := by
  simp [decodeTapeComplete, decodeTape_encodeTape]

theorem decodeTapeComplete_eq_some_encode
    {code : Word MachineCodeSymbol} {T : Tape Bool}
    (h : decodeTapeComplete code = some T) :
    code = encodeTape T := by
  unfold decodeTapeComplete at h
  cases hdecode : decodeTape code with
  | none =>
      simp [hdecode] at h
  | some parsed =>
      cases parsed with
      | mk decoded suffix =>
          cases suffix with
          | nil =>
              simp [hdecode] at h
              cases h
              simpa [encodeTape] using
                decodeTape_eq_some_encodeTapeAppend
                  hdecode
          | cons _ _ =>
              simp [hdecode] at h

theorem decodeConfigurationComplete_encode
    (cfg : Configuration) :
    decodeConfigurationComplete
        (encodeConfiguration cfg) =
      some cfg := by
  simp [decodeConfigurationComplete,
    decodeConfiguration_encodeConfiguration]

theorem decodeConfigurationComplete_eq_some_encode
    {code : Word MachineCodeSymbol}
    {cfg : Configuration}
    (h : decodeConfigurationComplete code = some cfg) :
    code = encodeConfiguration cfg := by
  unfold decodeConfigurationComplete at h
  cases hdecode : decodeConfiguration code with
  | none =>
      simp [hdecode] at h
  | some parsed =>
      cases parsed with
      | mk decoded suffix =>
          cases suffix with
          | nil =>
              simp [hdecode] at h
              cases h
              simpa [encodeConfiguration] using
                decodeConfiguration_eq_some_encodeConfigurationAppend
                  hdecode
          | cons _ _ =>
              simp [hdecode] at h

theorem encodeNat_cons (n : Nat) :
    exists symbol : MachineCodeSymbol,
    exists tail : Word MachineCodeSymbol,
      encodeNat n = symbol :: tail := by
  cases n with
  | zero => exact ⟨MachineCodeSymbol.done, [], rfl⟩
  | succ n => exact ⟨MachineCodeSymbol.tick, encodeNat n, rfl⟩

theorem encodeBoolWord_cons (w : Word Bool) :
    exists symbol : MachineCodeSymbol,
    exists tail : Word MachineCodeSymbol,
      encodeBoolWord w = symbol :: tail :=
  EncodedRewriters.encodeBoolWord_cons w

end Fields
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
