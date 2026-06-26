import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.Basic

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

namespace EncodedRewriters
namespace CanonicalLayouts

def ExactOutputTape
    (outputCode : α -> Word MachineCodeSymbol) (a : α) : Tape Bool :=
  Tape.input
    (MachineDescription.encodeCodeWordAsInput (outputCode a))

def OutputTape
    (outputCode : α -> Word MachineCodeSymbol) (a : α) : Tape Bool :=
  Tape.move Direction.right
    (Tape.input
      (MachineDescription.encodeCodeWordAsInput (outputCode a)))

abbrev RightShiftedOutputTape
    (outputCode : α -> Word MachineCodeSymbol) (a : α) : Tape Bool :=
  OutputTape outputCode a

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

abbrev RightShiftedEmitterSpec
    (inputBits : α -> Word Bool)
    (outputCode : α -> Word MachineCodeSymbol)
    (emitter : MachineDescription) : Prop :=
  EmitterSpec inputBits outputCode emitter

def ExactEmitterConstruction
    (inputBits : α -> Word Bool)
    (outputCode : α -> Word MachineCodeSymbol) : Prop :=
  exists emitter : MachineDescription,
    ExactEmitterSpec inputBits outputCode emitter

abbrev RightShiftedEmitterConstruction
    (inputBits : α -> Word Bool)
    (outputCode : α -> Word MachineCodeSymbol) : Prop :=
  EmitterConstruction inputBits outputCode

theorem exactOutputTape_normalizedOutput
    (outputCode : α -> Word MachineCodeSymbol) (a : α) :
    Tape.normalizedOutput (ExactOutputTape outputCode a) =
      MachineDescription.encodeCodeWordAsInput (outputCode a) := by
  simpa [ExactOutputTape, Tape.output] using
    Tape.normalizedOutput_output
      (MachineDescription.encodeCodeWordAsInput (outputCode a))

theorem outputTape_normalizedOutput
    (outputCode : α -> Word MachineCodeSymbol) (a : α) :
    Tape.normalizedOutput (OutputTape outputCode a) =
      MachineDescription.encodeCodeWordAsInput (outputCode a) := by
  simpa [OutputTape] using
    EncodedRewriters.tape_normalizedOutput_move_right_input
      (MachineDescription.encodeCodeWordAsInput (outputCode a))

theorem rightShiftedOutputTape_normalizedOutput
    (outputCode : α -> Word MachineCodeSymbol) (a : α) :
    Tape.normalizedOutput (RightShiftedOutputTape outputCode a) =
      MachineDescription.encodeCodeWordAsInput (outputCode a) :=
  outputTape_normalizedOutput outputCode a

end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
