import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.Basic

set_option doc.verso true

/-!
# Canonical dovetail-controller-layout validators
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace CanonicalLayouts
namespace Controller

abbrev Layout := MachineDescription.DovetailControllerLayout

def decode : Word MachineCodeSymbol -> Option Layout :=
  MachineDescription.DovetailControllerLayout.decodeComplete

def encode : Layout -> Word MachineCodeSymbol :=
  MachineDescription.DovetailControllerLayout.encode

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

theorem decode_encode (C : Layout) :
    decode (encode C) = some C :=
  MachineDescription.DovetailControllerLayout.decodeComplete_encode C

theorem decode_eq_some_encode
    {code : Word MachineCodeSymbol} {C : Layout}
    (h : decode code = some C) :
    code = encode C :=
  MachineDescription.DovetailControllerLayout.decodeComplete_eq_some_encode h

theorem encode_cons (C : Layout) :
    exists symbol : MachineCodeSymbol,
    exists tail : Word MachineCodeSymbol,
      encode C = symbol :: tail := by
  cases C
  exact ⟨MachineCodeSymbol.header, _, rfl⟩

theorem identityPrimitive_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    identityPrimitive.transform code = some out <->
      exists C : Layout, code = encode C ∧ out = encode C :=
  CanonicalLayouts.identityPrimitive_transform_eq_some_iff
    decode_encode (fun h => decode_eq_some_encode h) code out

theorem identityClosedHandoffConstruction_of_closedRecognizer
    (h : ClosedRecognizerConstruction) :
    IdentityClosedHandoffConstruction :=
  CanonicalLayouts.identityClosedHandoffConstruction_of_closedRecognizer
    decode_encode (fun h => decode_eq_some_encode h) encode_cons h

end Controller
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
