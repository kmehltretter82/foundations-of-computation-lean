import FoC.Computability.DescriptionCodeValidity

set_option doc.verso true

/-!
# Self-delimiting finite-description pair halting

The canonical finite pair currency stores one complete description code at the
front of a code-symbol word and uses the uniquely decoded suffix as that
description's input.  Failed prefix decoding and decoded descriptions that are
not well formed are outside the language.  This makes concatenation honest for
valid description codes without adding a second tagged alphabet.
-/

namespace FoC
namespace Computability

open Languages

/-- Valid finite-description pair halting with a self-delimiting first
component.  The complete description prefix determines the input suffix. -/
def CodePairHaltingLanguage : Language MachineCodeSymbol :=
  fun encoded =>
    exists D : MachineDescription,
    exists input : Word MachineCodeSymbol,
      MachineDescription.decodeDescriptionPrefix encoded = some (D, input) ∧
        D.WellFormed ∧
          D.HaltsOnInput
            (MachineDescription.encodeCodeWordAsInput input)

theorem mem_codePairHaltingLanguage_iff
    (encoded : Word MachineCodeSymbol) :
    encoded ∈ CodePairHaltingLanguage <->
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeDescriptionPrefix encoded = some (D, input) ∧
          D.WellFormed ∧
            D.HaltsOnInput
              (MachineDescription.encodeCodeWordAsInput input) :=
  Iff.rfl

/-- A word on which prefix decoding fails is an explicit malformed reject. -/
theorem not_mem_codePairHaltingLanguage_of_decode_none
    {encoded : Word MachineCodeSymbol}
    (hdecode : MachineDescription.decodeDescriptionPrefix encoded = none) :
    ¬ encoded ∈ CodePairHaltingLanguage := by
  rintro ⟨D, input, hdecoded, _hwell, _hhalt⟩
  rw [hdecode] at hdecoded
  cases hdecoded

/-- A decoded but non-well-formed description is also an explicit reject. -/
theorem not_mem_codePairHaltingLanguage_of_decode_not_wellFormed
    {encoded : Word MachineCodeSymbol} {D : MachineDescription}
    {input : Word MachineCodeSymbol}
    (hdecode :
      MachineDescription.decodeDescriptionPrefix encoded = some (D, input))
    (hnot : ¬ D.WellFormed) :
    ¬ encoded ∈ CodePairHaltingLanguage := by
  rintro ⟨decoded, decodedInput, hdecoded, hwell, _hhalt⟩
  rw [hdecode] at hdecoded
  cases hdecoded
  exact hnot hwell

/-- Canonical concatenation has the advertised unique description/input
boundary. -/
theorem encodeDescription_append_mem_codePairHaltingLanguage_iff
    (D : MachineDescription) (input : Word MachineCodeSymbol) :
    List.append (MachineDescription.encodeDescription D) input ∈
        CodePairHaltingLanguage <->
      D.WellFormed ∧
        D.HaltsOnInput (MachineDescription.encodeCodeWordAsInput input) := by
  constructor
  · rintro ⟨decoded, decodedInput, hdecode, hwell, hhalt⟩
    have hcanonical :=
      MachineDescription.decodeDescriptionPrefix_encodeDescription_append
        D input
    rw [hcanonical] at hdecode
    cases hdecode
    exact ⟨hwell, hhalt⟩
  · rintro ⟨hwell, hhalt⟩
    exact ⟨D, input,
      MachineDescription.decodeDescriptionPrefix_encodeDescription_append
        D input,
      hwell, hhalt⟩

/-- The self-delimiting presentation is exactly concatenation of a valid
complete machine code with a separately supplied input accepted by that code. -/
theorem mem_codePairHaltingLanguage_iff_exists_codeAccepts
    (encoded : Word MachineCodeSymbol) :
    encoded ∈ CodePairHaltingLanguage <->
      exists machine input : Word MachineCodeSymbol,
        encoded = List.append machine input ∧
          MachineDescription.CodeAccepts machine input := by
  constructor
  · rintro ⟨D, input, hdecode, hwell, hhalt⟩
    have hencoded :=
      MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
        hdecode
    exact ⟨MachineDescription.encodeDescription D, input, hencoded,
      MachineDescription.codeAccepts_of_encodeDescription hwell hhalt⟩
  · rintro ⟨machine, input, rfl, D, hdecode, hwell, hhalt⟩
    have hmachine :=
      MachineDescription.decodeDescription_eq_some_encodeDescription hdecode
    subst machine
    exact (encodeDescription_append_mem_codePairHaltingLanguage_iff
      D input).2 ⟨hwell, hhalt⟩

/-- On a valid complete code, finite self-append is the checked diagonal map:
the first copy is the unique description and the second copy is its input. -/
theorem selfAppend_mem_codePairHaltingLanguage_iff_codeAccepts
    {code : Word MachineCodeSymbol}
    (hvalid : MachineDescription.DescriptionCodeValid code) :
    List.append code code ∈ CodePairHaltingLanguage <->
      MachineDescription.CodeAccepts code code := by
  rcases
      (MachineDescription.descriptionCodeValid_iff_exists_encodeDescription_wellFormed
        code).1 hvalid with
    ⟨D, rfl, hwell⟩
  rw [encodeDescription_append_mem_codePairHaltingLanguage_iff,
    MachineDescription.codeAccepts_encodeDescription_iff]

end Computability
end FoC
