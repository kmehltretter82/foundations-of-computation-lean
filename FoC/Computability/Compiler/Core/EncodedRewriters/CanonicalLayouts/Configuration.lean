import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.Fields

set_option doc.verso true

/-!
# Canonical configuration validators

This module specializes the shared canonical-layout contracts to complete
encoded {name (full := FoC.Computability.MachineDescription.Configuration)}`MachineDescription.Configuration`
values.  Dovetail-layout scanners use this as the field-level contract for the
accept and reject configurations.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace CanonicalLayouts
namespace Configuration

abbrev Layout := MachineDescription.Configuration

def decode : Word MachineCodeSymbol -> Option Layout :=
  CanonicalLayouts.Fields.decodeConfigurationComplete

def encode : Layout -> Word MachineCodeSymbol :=
  MachineDescription.encodeConfiguration

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

theorem decode_encode (cfg : Layout) :
    decode (encode cfg) = some cfg :=
  CanonicalLayouts.Fields.decodeConfigurationComplete_encode cfg

theorem decode_eq_some_encode
    {code : Word MachineCodeSymbol} {cfg : Layout}
    (h : decode code = some cfg) :
    code = encode cfg :=
  CanonicalLayouts.Fields.decodeConfigurationComplete_eq_some_encode h

theorem encode_cons (cfg : Layout) :
    exists symbol : MachineCodeSymbol,
    exists tail : Word MachineCodeSymbol,
      encode cfg = symbol :: tail := by
  rcases EncodedRewriters.encodeNatAppend_cons cfg.state
      (MachineDescription.encodeTapeAppend cfg.tape []) with
    ⟨symbol, tail, htail⟩
  exact ⟨symbol, tail, by simpa [encode,
    MachineDescription.encodeConfiguration,
    MachineDescription.encodeConfigurationAppend] using htail⟩

theorem identityPrimitive_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    identityPrimitive.transform code = some out <->
      exists cfg : Layout, code = encode cfg ∧ out = encode cfg :=
  CanonicalLayouts.identityPrimitive_transform_eq_some_iff
    decode_encode (fun h => decode_eq_some_encode h) code out

theorem identityPrimitive_encode (cfg : Layout) :
    identityPrimitive.transform (encode cfg) = some (encode cfg) :=
  CanonicalLayouts.identityPrimitive_encode decode_encode cfg

theorem identityClosedHandoffConstruction_of_closedRecognizer
    (h : ClosedRecognizerConstruction) :
    IdentityClosedHandoffConstruction :=
  CanonicalLayouts.identityClosedHandoffConstruction_of_closedRecognizer
    decode_encode (fun h => decode_eq_some_encode h) encode_cons h

end Configuration
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
