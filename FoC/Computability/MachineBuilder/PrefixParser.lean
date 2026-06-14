import FoC.Computability.MachineBuilder.TapeCode

set_option doc.verso true

/-!
# Machine-builder prefix parser
-/

namespace FoC
namespace Computability

open Languages

namespace MachineDescription

/-!
## Description-prefix parser primitives

The universal-prefix machine first has to recognize whether its code-symbol
input begins with one complete machine description.  The primitives in this
module are the code-level behavior that later finite controller fragments
realize: one partial normalizer that succeeds exactly on parser success, and
one total branch primitive that emits an explicit success/failure bit.
-/

namespace PrefixParser

def normalizeCode (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodeDescriptionPrefix tokens with
  | none => none
  | some (D, input) => some (List.append (encodeDescription D) input)

theorem normalizeCode_of_decodeDescriptionPrefix
    {tokens : Word MachineCodeSymbol} {D : MachineDescription}
    {input : Word MachineCodeSymbol}
    (h : decodeDescriptionPrefix tokens = some (D, input)) :
    normalizeCode tokens =
      some (List.append (encodeDescription D) input) := by
  unfold normalizeCode
  rw [h]
  rfl

theorem normalizeCode_eq_some_iff
    (tokens out : Word MachineCodeSymbol) :
    normalizeCode tokens = some out <->
      exists D : MachineDescription,
        exists input : Word MachineCodeSymbol,
          decodeDescriptionPrefix tokens = some (D, input) ∧
            out = List.append (encodeDescription D) input := by
  constructor
  · intro h
    unfold normalizeCode at h
    cases hdecode : decodeDescriptionPrefix tokens with
    | none =>
        simp [hdecode] at h
    | some parsed =>
        rcases parsed with ⟨D, input⟩
        rw [hdecode] at h
        cases h
        exact ⟨D, input, rfl, rfl⟩
  · intro h
    rcases h with ⟨D, input, hdecode, hout⟩
    rw [hout]
    exact normalizeCode_of_decodeDescriptionPrefix hdecode

theorem normalizeCode_eq_none_iff
    (tokens : Word MachineCodeSymbol) :
    normalizeCode tokens = none <->
      decodeDescriptionPrefix tokens = none := by
  constructor
  · intro h
    unfold normalizeCode at h
    cases hdecode : decodeDescriptionPrefix tokens with
    | none =>
        rfl
    | some parsed =>
        rcases parsed with ⟨D, input⟩
        rw [hdecode] at h
        cases h
  · intro h
    simp [normalizeCode, h]

theorem normalizeCode_eq_some_self_iff
    (tokens : Word MachineCodeSymbol) :
    normalizeCode tokens = some tokens <->
      exists D : MachineDescription,
        exists input : Word MachineCodeSymbol,
          decodeDescriptionPrefix tokens = some (D, input) := by
  constructor
  · intro h
    rcases (normalizeCode_eq_some_iff tokens tokens).mp h with
      ⟨D, input, hdecode, _⟩
    exact ⟨D, input, hdecode⟩
  · intro h
    rcases h with ⟨D, input, hdecode⟩
    have htokens :
        tokens = List.append (encodeDescription D) input :=
      decodeDescriptionPrefix_eq_some_encodeDescription_append hdecode
    have hnormalize := normalizeCode_of_decodeDescriptionPrefix hdecode
    simpa [htokens] using hnormalize

def normalizeCodePrimitive : TapeCodePrimitive where
  transform := normalizeCode

theorem normalizeCodePrimitive_realizes :
    normalizeCodePrimitive.Realizes normalizeCode := by
  intro tokens
  rfl

def branchCode (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodeDescriptionPrefix tokens with
  | none => some (encodeBoolWord [false])
  | some (D, input) =>
      some
        (encodeBoolWordAppend [true]
          (List.append (encodeDescription D) input))

theorem branchCode_of_decodeDescriptionPrefix
    {tokens : Word MachineCodeSymbol} {D : MachineDescription}
    {input : Word MachineCodeSymbol}
    (h : decodeDescriptionPrefix tokens = some (D, input)) :
    branchCode tokens =
      some (encodeBoolWordAppend [true] tokens) := by
  have htokens :
      tokens = List.append (encodeDescription D) input :=
    decodeDescriptionPrefix_eq_some_encodeDescription_append h
  unfold branchCode
  rw [h, htokens]

theorem branchCode_of_decodeDescriptionPrefix_none
    {tokens : Word MachineCodeSymbol}
    (h : decodeDescriptionPrefix tokens = none) :
    branchCode tokens = some (encodeBoolWord [false]) := by
  simp [branchCode, h]

theorem branchCode_total (tokens : Word MachineCodeSymbol) :
    exists out : Word MachineCodeSymbol, branchCode tokens = some out := by
  cases hdecode : decodeDescriptionPrefix tokens with
  | none =>
      exact ⟨encodeBoolWord [false],
        branchCode_of_decodeDescriptionPrefix_none hdecode⟩
  | some parsed =>
      rcases parsed with ⟨D, input⟩
      exact ⟨encodeBoolWordAppend [true] tokens,
        branchCode_of_decodeDescriptionPrefix hdecode⟩

theorem branchCode_eq_some_iff
    (tokens out : Word MachineCodeSymbol) :
    branchCode tokens = some out <->
      (decodeDescriptionPrefix tokens = none ∧
        out = encodeBoolWord [false]) ∨
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        decodeDescriptionPrefix tokens = some (D, input) ∧
          out =
            encodeBoolWordAppend [true]
              (List.append (encodeDescription D) input) := by
  constructor
  · intro h
    unfold branchCode at h
    cases hdecode : decodeDescriptionPrefix tokens with
    | none =>
        simp [hdecode] at h
        cases h
        exact Or.inl ⟨rfl, rfl⟩
    | some parsed =>
        cases parsed with
        | mk D input =>
            simp [hdecode] at h
            cases h
            exact Or.inr ⟨D, input, rfl, rfl⟩
  · intro h
    rcases h with hfailure | hsuccess
    · rcases hfailure with ⟨hdecode, rfl⟩
      exact branchCode_of_decodeDescriptionPrefix_none hdecode
    · rcases hsuccess with ⟨D, input, hdecode, rfl⟩
      unfold branchCode
      rw [hdecode]

def branchCodePrimitive : TapeCodePrimitive where
  transform := branchCode

theorem branchCodePrimitive_realizes :
    branchCodePrimitive.Realizes branchCode := by
  intro tokens
  rfl

structure CodeConstruction where
  normalize : TapeCodePrimitive
  branch : TapeCodePrimitive
  normalize_realizes : normalize.Realizes normalizeCode
  branch_realizes : branch.Realizes branchCode

def codeConstruction : CodeConstruction where
  normalize := normalizeCodePrimitive
  branch := branchCodePrimitive
  normalize_realizes := normalizeCodePrimitive_realizes
  branch_realizes := branchCodePrimitive_realizes

end PrefixParser

end MachineDescription

end Computability
end FoC
