import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.Normalizer.Soundness.Final

set_option doc.verso true

/-!
# Description Prefix Decoder

This module exposes the finite description-prefix decoder supplied by the
parser normalizer without depending on the downstream finite-source assembly.
-/

namespace FoC
namespace Computability

open Languages

def CodePrefixDescriptionPrefixDecoderConstruction : Prop :=
  exists state : Type,
  exists decoder : TuringMachine MachineCodeSymbol state,
    forall encoded : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput decoder encoded <->
        exists D : MachineDescription,
        exists input : Word MachineCodeSymbol,
          MachineDescription.decodeDescriptionPrefix encoded =
            some (D, input)

theorem codePrefixParserNormalizerMachine_haltsOnInput_iff_decodeDescriptionPrefix
    (encoded : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInput codePrefixParserNormalizerMachine encoded <->
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeDescriptionPrefix encoded =
          some (D, input) := by
  constructor
  · intro h
    rcases h with ⟨final, hcomputes, hhalted⟩
    let out : Word MachineCodeSymbol :=
      Tape.normalizedOutput final.tape
    have hout :
        TuringMachine.HaltsWithOutput
          codePrefixParserNormalizerMachine encoded out :=
      ⟨final, hcomputes, hhalted, rfl⟩
    have htransform :
        CodePrefixParserNormalizerCode.transform encoded = some out :=
      (codePrefixParserNormalizerMachine_code_spec encoded out).mp hout
    rcases
        (codePrefixParserNormalizerCode_transform_eq_some_iff
          encoded out).mp htransform with
      ⟨D, input, hdecode, _hout⟩
    exact ⟨D, input, hdecode⟩
  · intro h
    rcases h with ⟨D, input, hdecode⟩
    have hencoded :
        encoded = List.append (MachineDescription.encodeDescription D)
          input :=
      MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
        hdecode
    have htransform :
        CodePrefixParserNormalizerCode.transform encoded =
          some encoded :=
      (codePrefixParserNormalizerCode_transform_eq_some_iff
        encoded encoded).mpr
        ⟨D, input, hdecode, by rw [hencoded]⟩
    exact
      TuringMachine.halts_with_output_implies_halts
        ((codePrefixParserNormalizerMachine_code_spec
          encoded encoded).mpr htransform)

theorem codePrefixDescriptionPrefixDecoderConstruction :
    CodePrefixDescriptionPrefixDecoderConstruction :=
  ⟨CodePrefixParserNormalizerState,
    codePrefixParserNormalizerMachine,
    codePrefixParserNormalizerMachine_haltsOnInput_iff_decodeDescriptionPrefix⟩

end Computability
end FoC
