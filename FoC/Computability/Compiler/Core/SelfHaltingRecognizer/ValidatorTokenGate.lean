import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorSpec
import FoC.Computability.Compiler.Dovetail.Scanner.TokenAligned

set_option doc.verso true

/-!
# Exact-code validator: token-alignment gate

This module closes leaf 1 of the exact-code validator roadmap.  It reuses the
finite token-alignment pre-scanner to certify that an arbitrary public Boolean
input is a nonempty canonical four-bit encoding of machine-code symbols.  Valid
complete description codes satisfy that gate more specifically: their first
symbol is the description header.

The gate deliberately does not claim code validity.  It only establishes the
aligned, nonempty input currency required by the later header, transition, and
well-formedness checks.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer

open Languages
open MachineDescription

open EncRewriters.CanonicalLayouts.DovetailLayoutScanner

/-- The reusable finite description used as the validator's token gate. -/
abbrev ExactCodeValidatorTokenGateDescription : MachineDescription :=
  CodeWordAlignedPreScannerDescription

/-- Valid complete description codes begin with the distinguished header. -/
theorem descriptionCodeValid_exists_header_tail
    {w : Word MachineCodeSymbol}
    (hvalid : MachineDescription.DescriptionCodeValid w) :
    exists tail : Word MachineCodeSymbol,
      w = MachineCodeSymbol.header :: tail := by
  rcases
      (MachineDescription.descriptionCodeValid_iff_exists_encodeDescription_wellFormed
        w).mp hvalid with
    ⟨D, rfl, _⟩
  exact ⟨_, rfl⟩

/-- The token gate is well formed and has no outgoing halt transition. -/
theorem exactCodeValidatorTokenGateDescription_subroutineReady :
    ExactCodeValidatorTokenGateDescription.SubroutineReady :=
  codeWordAlignedPreScannerDescription_subroutineReady

/--
Every valid complete description code passes the token gate and reaches its
exact source-preserving handoff tape.
-/
theorem exactCodeValidatorTokenGateDescription_valid
    {w : Word MachineCodeSymbol}
    (hvalid : MachineDescription.DescriptionCodeValid w) :
    ExactCodeValidatorTokenGateDescription.HaltsFromTape
      (Tape.input (encodeCodeWordAsInput w))
      (codeWordAlignedHandoffTape (encodeCodeWordAsInput w)) := by
  rcases descriptionCodeValid_exists_header_tail hvalid with ⟨tail, rfl⟩
  exact
    codeWordAlignedPreScannerDescription_haltsFromTape
      MachineCodeSymbol.header tail

/--
Exact all-word characterization of the token gate.  In particular, malformed
bit groups, partial groups, and the empty word cannot halt.
-/
theorem exactCodeValidatorTokenGateDescription_haltsFromTape_iff
    (bits : Word Bool) (T : Tape Bool) :
    ExactCodeValidatorTokenGateDescription.HaltsFromTape
        (Tape.input bits) T <->
      exists symbol : MachineCodeSymbol,
      exists rest : Word MachineCodeSymbol,
        bits = encodeCodeWordAsInput (symbol :: rest) ∧
          T = codeWordAlignedHandoffTape bits := by
  constructor
  · intro h
    exact codeWordAlignedPreScannerDescription_haltsFromTape_inv h
  · rintro ⟨symbol, rest, rfl, rfl⟩
    exact
      codeWordAlignedPreScannerDescription_haltsFromTape symbol rest

/-- The empty public input cannot pass the validator's token gate. -/
theorem exactCodeValidatorTokenGateDescription_not_haltsFromTape_nil
    (T : Tape Bool) :
    ¬ ExactCodeValidatorTokenGateDescription.HaltsFromTape
        (Tape.input []) T := by
  rw [exactCodeValidatorTokenGateDescription_haltsFromTape_iff]
  rintro ⟨symbol, rest, hbits, _⟩
  cases symbol <;>
    simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput] at hbits

end SelfHaltingRecognizer
end Computability
end FoC
