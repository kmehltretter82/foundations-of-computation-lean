import FoC.Computability.Encoding

set_option doc.verso true

/-!
# Languages of encoded machine descriptions

This module is the semantic bridge between description syntax and description
execution. It distinguishes raw complete decoding, complete well-formed codes,
and prefix-coded descriptions before running the decoded machine. The raw
relations remain available for compatibility; the canonical complete-code
relations require well-formedness.

Encoding and parser inversion are provided by
{module}`FoC.Computability.Encoding`; executable table semantics are provided
by {module}`FoC.Computability.MachineDescription`.  The concrete finite
universal-prefix runner is assembled separately in
{module -checked}`FoC.Computability.Compiler.UniversalAndRanges.FiniteSource`.
-/

namespace FoC
namespace Computability

open Languages

namespace MachineDescription

/-!
## Complete and Prefix-Coded Acceptance

The predicates in this group distinguish raw and valid separately supplied
complete descriptions from a word whose leading description is decoded in
place. Prefix acceptance intentionally remains a raw execution relation because
its finite runner parses a leading description while preserving the suffix.
-/

/-- A raw complete description code halts on a separately encoded input. -/
def RawCodeAccepts
    (machine input : Word MachineCodeSymbol) : Prop :=
  exists D : MachineDescription,
    decodeDescription machine = some D ∧
      D.HaltsOnInput (encodeCodeWordAsInput input)

/-- A word is the complete code of a well-formed finite description. -/
def DescriptionCodeValid
    (machine : Word MachineCodeSymbol) : Prop :=
  exists D : MachineDescription,
    decodeDescription machine = some D ∧ D.WellFormed

/-- A valid complete description code halts on a separately encoded input. -/
def CodeAccepts
    (machine input : Word MachineCodeSymbol) : Prop :=
  exists D : MachineDescription,
    decodeDescription machine = some D ∧ D.WellFormed ∧
      D.HaltsOnInput (encodeCodeWordAsInput input)

/-- A description prefix halts on the input occupying the remaining suffix. -/
def CodePrefixAccepts (encoded : Word MachineCodeSymbol) : Prop :=
  exists D : MachineDescription, exists input : Word MachineCodeSymbol,
    decodeDescriptionPrefix encoded = some (D, input) ∧
      D.HaltsOnInput (encodeCodeWordAsInput input)

/-- Inputs accepted by one fixed raw complete description code. -/
def RawCodeAcceptedLanguage
    (machine : Word MachineCodeSymbol) : Language MachineCodeSymbol :=
  fun input => RawCodeAccepts machine input

/-- Inputs accepted by one fixed valid complete description code. -/
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

/-!
## Canonical Encoding Laws

Canonical description encodings decode back to their source description. The
following equivalences remove the existential decoder witness. Raw acceptance
exposes halting directly, while valid acceptance also exposes the required
well-formedness contract.
-/

theorem rawCodeAccepts_encodeDescription_iff
    (D : MachineDescription) (input : Word MachineCodeSymbol) :
    RawCodeAccepts (encodeDescription D) input <->
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

theorem rawCodeAccepts_of_encodeDescription
    {D : MachineDescription} {input : Word MachineCodeSymbol}
    (h : D.HaltsOnInput (encodeCodeWordAsInput input)) :
    RawCodeAccepts (encodeDescription D) input :=
  (rawCodeAccepts_encodeDescription_iff D input).mpr h

theorem descriptionCodeValid_encodeDescription_iff
    (D : MachineDescription) :
    DescriptionCodeValid (encodeDescription D) <-> D.WellFormed := by
  constructor
  · intro h
    rcases h with ⟨decoded, hdecode, hwell⟩
    have henc := decodeDescription_encodeDescription D
    rw [henc] at hdecode
    cases hdecode
    exact hwell
  · intro h
    exact ⟨D, decodeDescription_encodeDescription D, h⟩

theorem codeAccepts_encodeDescription_iff
    (D : MachineDescription) (input : Word MachineCodeSymbol) :
    CodeAccepts (encodeDescription D) input <->
      D.WellFormed ∧
        D.HaltsOnInput (encodeCodeWordAsInput input) := by
  constructor
  · intro h
    rcases h with ⟨decoded, hdecode, hwell, hhalts⟩
    have henc := decodeDescription_encodeDescription D
    rw [henc] at hdecode
    cases hdecode
    exact ⟨hwell, hhalts⟩
  · intro h
    exact ⟨D, decodeDescription_encodeDescription D, h.left, h.right⟩

theorem codeAccepts_of_encodeDescription
    {D : MachineDescription} {input : Word MachineCodeSymbol}
    (hD : D.WellFormed)
    (h : D.HaltsOnInput (encodeCodeWordAsInput input)) :
    CodeAccepts (encodeDescription D) input :=
  (codeAccepts_encodeDescription_iff D input).mpr ⟨hD, h⟩

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
    D.WellFormed ∧
      D.HaltsOnInput (encodeCodeWordAsInput input) :=
  (codeAccepts_encodeDescription_iff D input).mp h

end MachineDescription

end Computability
end FoC
