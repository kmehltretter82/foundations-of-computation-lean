import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.Basic

set_option doc.verso true

/-!
# Canonical simulator-layout validators
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace CanonicalLayouts
namespace Simulator

abbrev Layout := MachineDescription.SimulatorLayout

def decode : Word MachineCodeSymbol -> Option Layout :=
  MachineDescription.SimulatorLayout.decodeComplete

def encode : Layout -> Word MachineCodeSymbol :=
  MachineDescription.SimulatorLayout.encode

abbrev bits : Layout -> Word Bool :=
  Bits encode

abbrev inputTape : Layout -> Tape Bool :=
  InputTape encode

abbrev handoffTape : Layout -> Tape Bool :=
  HandoffTape encode

abbrev identityPrimitive : MachineDescription.TapeCodePrimitive :=
  IdentityPrimitive decode

abbrev ClosedRecognizerSpec (recognizer : MachineDescription) : Prop :=
  CanonicalLayouts.ClosedRecognizerSpec decode encode recognizer

abbrev ClosedRecognizerConstruction : Prop :=
  CanonicalLayouts.ClosedRecognizerConstruction decode encode

abbrev IdentityClosedHandoffConstruction : Prop :=
  CanonicalLayouts.IdentityClosedHandoffConstruction decode

theorem decode_encode (L : Layout) :
    decode (encode L) = some L :=
  MachineDescription.SimulatorLayout.decodeComplete_encode L

theorem decode_eq_some_encode
    {code : Word MachineCodeSymbol} {L : Layout}
    (h : decode code = some L) :
    code = encode L :=
  MachineDescription.SimulatorLayout.decodeComplete_eq_some_encode h

theorem encode_cons (L : Layout) :
    exists symbol : MachineCodeSymbol,
    exists tail : Word MachineCodeSymbol,
      encode L = symbol :: tail := by
  cases L
  exact ⟨MachineCodeSymbol.header, _, rfl⟩

theorem identityPrimitive_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    identityPrimitive.transform code = some out <->
      exists L : Layout, code = encode L ∧ out = encode L :=
  CanonicalLayouts.identityPrimitive_transform_eq_some_iff
    decode_encode (fun h => decode_eq_some_encode h) code out

theorem identityClosedHandoffConstruction_of_closedRecognizer
    (h : ClosedRecognizerConstruction) :
    IdentityClosedHandoffConstruction :=
  CanonicalLayouts.identityClosedHandoffConstruction_of_closedRecognizer
    decode_encode (fun h => decode_eq_some_encode h) encode_cons h

end Simulator
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
