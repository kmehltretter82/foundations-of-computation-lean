import FoC.Computability.Compiler.Core.EncRewriters.CanonicalLayouts.Basic

set_option doc.verso true

/-!
# Canonical layout emitters

Emitter phases start from an already validated canonical payload and halt just
to the right of the emitted canonical code word.  The contract here captures
that reusable shape independently of the concrete projection or merge logic.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace CanonicalLayouts

def ExactOutputTape
    (outputCode : α -> Word MachineCodeSymbol) (a : α) : Tape Bool :=
  Tape.input
    (encodeCodeWordAsInput (outputCode a))

def OutputTape
    (outputCode : α -> Word MachineCodeSymbol) (a : α) : Tape Bool :=
  Tape.move Direction.right
    (Tape.input
      (encodeCodeWordAsInput (outputCode a)))

def ExactEmitterSpec
    (inputBits : α -> Word Bool)
    (outputCode : α -> Word MachineCodeSymbol)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    (forall a : α,
      emitter.HaltsWithTape
        (inputBits a)
        (ExactOutputTape outputCode a)) ∧
      forall a : α,
      forall T : Tape Bool,
        emitter.HaltsWithTape (inputBits a) T ->
          T = ExactOutputTape outputCode a

def EmitterSpec
    (inputBits : α -> Word Bool)
    (outputCode : α -> Word MachineCodeSymbol)
    (emitter : MachineDescription) : Prop :=
  emitter.SubroutineReady ∧
    (forall a : α,
      emitter.HaltsWithTape
        (inputBits a)
        (OutputTape outputCode a)) ∧
      forall a : α,
      forall T : Tape Bool,
        emitter.HaltsWithTape (inputBits a) T ->
          T = OutputTape outputCode a

def EmitterConstruction
    (inputBits : α -> Word Bool)
    (outputCode : α -> Word MachineCodeSymbol) : Prop :=
  exists emitter : MachineDescription,
    EmitterSpec inputBits outputCode emitter

def ExactEmitterConstruction
    (inputBits : α -> Word Bool)
    (outputCode : α -> Word MachineCodeSymbol) : Prop :=
  exists emitter : MachineDescription,
    ExactEmitterSpec inputBits outputCode emitter

theorem exactOutputTape_normalizedOutput
    (outputCode : α -> Word MachineCodeSymbol) (a : α) :
    Tape.normalizedOutput (ExactOutputTape outputCode a) =
      encodeCodeWordAsInput (outputCode a) := by
  simpa [ExactOutputTape, Tape.output] using
    Tape.normalizedOutput_output
      (encodeCodeWordAsInput (outputCode a))

theorem exactOutputTape_cells
    (outputCode : α -> Word MachineCodeSymbol) (a : α) :
    Tape.cells (ExactOutputTape outputCode a) =
      match encodeCodeWordAsInput (outputCode a) with
      | [] => [none]
      | bit :: rest => some bit :: rest.map some := by
  unfold ExactOutputTape
  cases hbits : encodeCodeWordAsInput (outputCode a) with
  | nil =>
      simp [Tape.cells_input]
  | cons bit rest =>
      simp [Tape.cells_input]

theorem outputTape_normalizedOutput
    (outputCode : α -> Word MachineCodeSymbol) (a : α) :
    Tape.normalizedOutput (OutputTape outputCode a) =
      encodeCodeWordAsInput (outputCode a) := by
  simpa [OutputTape] using
    EncRewriters.tape_normalizedOutput_move_right_input
      (encodeCodeWordAsInput (outputCode a))

theorem outputTape_cells
    (outputCode : α -> Word MachineCodeSymbol) (a : α) :
    Tape.cells (OutputTape outputCode a) =
      match encodeCodeWordAsInput (outputCode a) with
      | [] => [none, none]
      | bit :: [] => [some bit, none]
      | first :: second :: rest =>
          some first :: some second :: rest.map some := by
  unfold OutputTape
  cases hbits : encodeCodeWordAsInput (outputCode a) with
  | nil =>
      simp [Tape.cells_move_right_input]
  | cons first rest =>
      cases rest with
      | nil =>
          simp [Tape.cells_move_right_input]
      | cons second tail =>
          simp [Tape.cells_move_right_input]

end CanonicalLayouts
end EncRewriters

end Computability
end FoC
