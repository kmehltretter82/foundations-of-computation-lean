import FoC.Computability.Encoding

set_option doc.verso true

/-!
# Languages of encoded machine descriptions

This module is the semantic bridge between description syntax and description
execution.  It defines the languages obtained by decoding complete or
prefix-coded descriptions and then running the decoded machine.

Encoding and parser inversion remain in
{module}`FoC.Computability.Encoding`; executable table semantics remain in
{module}`FoC.Computability.MachineDescription`.  Nothing here claims that a
single finite universal runner has been constructed.
-/

namespace FoC
namespace Computability

open Languages

namespace MachineDescription

/-- A complete description code halts on a separately encoded input. -/
def CodeAccepts
    (machine input : Word MachineCodeSymbol) : Prop :=
  exists D : MachineDescription,
    decodeDescription machine = some D ∧
      D.HaltsOnInput (encodeCodeWordAsInput input)

/-- A description prefix halts on the input occupying the remaining suffix. -/
def CodePrefixAccepts (encoded : Word MachineCodeSymbol) : Prop :=
  exists D : MachineDescription, exists input : Word MachineCodeSymbol,
    decodeDescriptionPrefix encoded = some (D, input) ∧
      D.HaltsOnInput (encodeCodeWordAsInput input)

/-- Inputs accepted by one fixed complete description code. -/
def CodeAcceptedLanguage
    (machine : Word MachineCodeSymbol) : Language MachineCodeSymbol :=
  fun input => CodeAccepts machine input

/-- Description-prefix/input words accepted by their decoded description. -/
def CodePrefixAcceptedLanguage : Language MachineCodeSymbol :=
  fun encoded => CodePrefixAccepts encoded

/-- Code words whose Boolean encoding is accepted by a fixed description. -/
def EncodedInputLanguage
    (D : MachineDescription) : Language MachineCodeSymbol :=
  fun input => D.HaltsOnInput (encodeCodeWordAsInput input)

theorem codeAccepts_encodeDescription_iff
    (D : MachineDescription) (input : Word MachineCodeSymbol) :
    CodeAccepts (encodeDescription D) input <->
      D.HaltsOnInput (encodeCodeWordAsInput input) := by
  constructor
  · intro h
    cases h with
    | intro decoded hdecoded =>
        have henc := decodeDescription_encodeDescription D
        rw [henc] at hdecoded
        cases hdecoded.left
        exact hdecoded.right
  · intro h
    exact Exists.intro D
      (And.intro (decodeDescription_encodeDescription D) h)

theorem codeAccepts_of_encodeDescription
    {D : MachineDescription} {input : Word MachineCodeSymbol}
    (h : D.HaltsOnInput (encodeCodeWordAsInput input)) :
    CodeAccepts (encodeDescription D) input :=
  (codeAccepts_encodeDescription_iff D input).mpr h

theorem codePrefixAccepts_encodeDescription_append_iff
    (D : MachineDescription) (input : Word MachineCodeSymbol) :
    CodePrefixAccepts (List.append (encodeDescription D) input) <->
      D.HaltsOnInput (encodeCodeWordAsInput input) := by
  constructor
  · intro h
    rcases h with ⟨decoded, decodedInput, hdecode, hhalts⟩
    have hprefix :=
      decodeDescriptionPrefix_encodeDescription_append D input
    rw [hprefix] at hdecode
    cases hdecode
    exact hhalts
  · intro h
    exact ⟨D, input,
      decodeDescriptionPrefix_encodeDescription_append D input, h⟩

theorem codePrefixAccepts_of_encodeDescription_append
    {D : MachineDescription} {input : Word MachineCodeSymbol}
    (h : D.HaltsOnInput (encodeCodeWordAsInput input)) :
    CodePrefixAccepts (List.append (encodeDescription D) input) :=
  (codePrefixAccepts_encodeDescription_append_iff D input).mpr h

theorem encodeDescription_codeAccepts_elim
    {D : MachineDescription} {input : Word MachineCodeSymbol}
    (h : CodeAccepts (encodeDescription D) input) :
    D.HaltsOnInput (encodeCodeWordAsInput input) :=
  (codeAccepts_encodeDescription_iff D input).mp h

end MachineDescription

end Computability
end FoC
