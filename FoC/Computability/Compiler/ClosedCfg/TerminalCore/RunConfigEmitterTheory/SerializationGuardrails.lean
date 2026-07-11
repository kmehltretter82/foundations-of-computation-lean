import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterTheory.ScratchWidth

set_option doc.verso true

/-!
# Exact tape-serialization guardrails

The final #18 configuration encoding contains the exact stored left and right
cell lists, including stored blanks.  Those window boundaries are not
observable from an unguarded logical tape: tapes that differ only by trailing
stored blanks are equivalent and every machine run preserves that
equivalence.  Consequently a uniform subroutine cannot serialize the exact
window from an arbitrary unguarded tape alone.

This does not make #18 impossible.  The structured lowerer retains explicit
guard cells around each logical tape in its physical one-tape endpoint.  The
target-specific serializer must consume those guards (or receive separately
maintained length metadata) instead of using only normalized tape output.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterTheory

/-- Blank tape with one additional stored blank in its right window. -/
def storedRightBlankTape : Tape Bool where
  left := []
  head := none
  right := [none]

theorem blank_equiv_storedRightBlankTape :
    Tape.Equiv (Tape.blank : Tape Bool) storedRightBlankTape := by
  simp [Tape.Equiv, Tape.blank, storedRightBlankTape,
    Tape.dropTrailingNone]

/-- Exact tape encodings distinguish the two equivalent windows. -/
theorem encodeTape_blank_ne_storedRightBlankTape :
    encodeCodeWordAsInput (encodeTape (Tape.blank : Tape Bool)) ≠
      encodeCodeWordAsInput (encodeTape storedRightBlankTape) := by
  decide

/-- False contract: serialize the exact stored tape window from the unguarded
logical tape itself. -/
def ExactLogicalTapeSerializerSpec (serializer : MachineDescription) : Prop :=
  serializer.SubroutineReady ∧
    forall T : Tape Bool,
      serializer.HaltsFromTape T
        (Tape.input (encodeCodeWordAsInput (encodeTape T)))

private theorem normalizedOutput_input (bits : Word Bool) :
    Tape.normalizedOutput (Tape.input bits) = bits := by
  cases bits <;>
    simp [Tape.normalizedOutput, Tape.cells, Tape.input, Tape.blank,
      Function.comp_def]

/-- No deterministic finite machine can satisfy the false exact-window
serializer contract.  The proof uses the smallest collision: an implicit
blank boundary versus one stored trailing blank. -/
theorem not_exists_exactLogicalTapeSerializer :
    ¬ exists serializer : MachineDescription,
      ExactLogicalTapeSerializerSpec serializer := by
  rintro ⟨serializer, hready, hserialize⟩
  rcases
      HaltsFromTapeEquiv_of_input_equiv
        blank_equiv_storedRightBlankTape
        (hserialize (Tape.blank : Tape Bool)) with
    ⟨actual, hactual, hactualEquiv⟩
  have hactualEq :
      actual =
        Tape.input
          (encodeCodeWordAsInput (encodeTape storedRightBlankTape)) := by
    exact
      haltsFromTape_functional_of_haltTransitionFree
        hready.right hactual (hserialize storedRightBlankTape)
  subst actual
  have hbits := Tape.Equiv.normalizedOutput_eq hactualEquiv
  rw [normalizedOutput_input, normalizedOutput_input] at hbits
  exact encodeTape_blank_ne_storedRightBlankTape hbits.symm

end RunConfigEmitterTheory
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
