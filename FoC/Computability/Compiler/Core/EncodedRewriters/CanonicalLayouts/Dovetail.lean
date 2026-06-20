import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.Basic

set_option doc.verso true

/-!
# Canonical dovetail-layout validators
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace CanonicalLayouts
namespace Dovetail

abbrev Layout := MachineDescription.DovetailLayout

def decode : Word MachineCodeSymbol -> Option Layout :=
  MachineDescription.DovetailLayout.decodeComplete

def encode : Layout -> Word MachineCodeSymbol :=
  MachineDescription.DovetailLayout.encode

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
  MachineDescription.DovetailLayout.decodeComplete_encode L

theorem decode_eq_some_encode
    {code : Word MachineCodeSymbol} {L : Layout}
    (h : decode code = some L) :
    code = encode L :=
  MachineDescription.DovetailLayout.decodeComplete_eq_some_encode h

theorem encode_cons (L : Layout) :
    exists symbol : MachineCodeSymbol,
    exists tail : Word MachineCodeSymbol,
      encode L = symbol :: tail := by
  rcases EncodedRewriters.dovetailLayout_encode_cons L with ⟨tail, htail⟩
  exact ⟨MachineCodeSymbol.transition, tail, htail⟩

theorem identityPrimitive_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    identityPrimitive.transform code = some out <->
      exists L : Layout, code = encode L ∧ out = encode L :=
  CanonicalLayouts.identityPrimitive_transform_eq_some_iff
    decode_encode (fun h => decode_eq_some_encode h) code out

theorem identityPrimitive_encode (L : Layout) :
    identityPrimitive.transform (encode L) = some (encode L) :=
  CanonicalLayouts.identityPrimitive_encode decode_encode L

theorem identityClosedHandoffConstruction_of_closedRecognizer
    (h : ClosedRecognizerConstruction) :
    IdentityClosedHandoffConstruction :=
  CanonicalLayouts.identityClosedHandoffConstruction_of_closedRecognizer
    decode_encode (fun h => decode_eq_some_encode h) encode_cons h

end Dovetail
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
