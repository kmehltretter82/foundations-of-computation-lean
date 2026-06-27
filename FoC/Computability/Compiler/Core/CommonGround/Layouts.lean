import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts

set_option doc.verso true

/-!
# Common canonical layout helpers

This module re-exports stable canonical layout names and provides the small
adapter facts that are reused by parser and runner construction files.
-/

namespace FoC
namespace Computability

open Languages

namespace CommonGround

namespace LayoutTapes

export EncodedRewriters.CanonicalLayouts
  ( Bits
    InputTape
    HandoffTape
    handoffTape_normalizedOutput
    handoffTape_handoff )

end LayoutTapes

namespace FieldInversions

export EncodedRewriters.CanonicalLayouts.Fields
  ( decodeNatComplete
    decodeNatComplete_encode
    decodeNatComplete_eq_some_encode
    decodeBoolComplete
    decodeBoolComplete_encode
    decodeBoolComplete_eq_some_encode
    decodeBoolWordComplete
    decodeBoolWordComplete_encode
    decodeBoolWordComplete_eq_some_encode
    decodeCodeWordFieldComplete
    decodeCodeWordFieldComplete_encode
    decodeCodeWordFieldComplete_eq_some_encode
    decodeCellListComplete
    decodeCellListComplete_encode
    decodeCellListComplete_eq_some_encode
    decodeTapeComplete
    decodeTapeComplete_encode
    decodeTapeComplete_eq_some_encode
    decodeConfigurationComplete
    decodeConfigurationComplete_encode
    decodeConfigurationComplete_eq_some_encode )

end FieldInversions

namespace DovetailLayouts

export EncodedRewriters.CanonicalLayouts.Dovetail
  ( Layout
    decode
    encode
    bits
    inputTape
    handoffTape
    identityPrimitive
    ClosedRecognizerSpec
    ClosedRecognizerConstruction
    IdentityClosedHandoffConstruction
    decode_encode
    decode_eq_some_encode
    encode_cons
    identityPrimitive_transform_eq_some_iff
    identityPrimitive_encode
    identityClosedHandoffConstruction_of_closedRecognizer )

abbrev IdentityRightShiftedConstruction : Prop :=
  exists runner : MachineDescription,
    EncodedRewriters.RightShiftedOutputCompiledSubroutineByDescription
      identityPrimitive runner

theorem identityPrimitive_transform_eq_some_cons
    {code out : Word MachineCodeSymbol}
    (h : identityPrimitive.transform code = some out) :
    exists symbol : MachineCodeSymbol,
    exists tail : Word MachineCodeSymbol,
      out = symbol :: tail :=
  EncodedRewriters.CanonicalLayouts.identityPrimitive_transform_eq_some_cons
    decode_encode (fun h => decode_eq_some_encode h) encode_cons h

theorem identityClosedHandoffConstruction_of_rightShifted
    (h : IdentityRightShiftedConstruction) :
    IdentityClosedHandoffConstruction := by
  rcases h with ⟨runner, hrunner⟩
  exact
    ⟨runner,
      EncodedRewriters.closedHandoffCompiled_of_rightShiftedOutputCompiled
        hrunner
        (by
          intro code out htransform
          exact identityPrimitive_transform_eq_some_cons htransform)⟩

end DovetailLayouts

namespace SimulatorLayouts

export EncodedRewriters.CanonicalLayouts.Simulator
  ( Layout
    decode
    encode
    bits
    inputTape
    handoffTape
    identityPrimitive
    ClosedRecognizerSpec
    ClosedRecognizerConstruction
    IdentityClosedHandoffConstruction
    decode_encode
    decode_eq_some_encode
    encode_cons
    identityPrimitive_transform_eq_some_iff
    identityClosedHandoffConstruction_of_closedRecognizer )

export MachineDescription.SimulatorLayout
  ( encodeAppend
    decodeComplete
    decodeComplete_encode
    decodeComplete_eq_some_encode
    asBoolInput
    run
    runCode
    runCodePrimitive
    normalizeCodePrimitive_encode
    normalizeCodePrimitive )

theorem handoffTape_normalizedOutput (L : Layout) :
    Tape.normalizedOutput (handoffTape L) =
      MachineDescription.encodeCodeWordAsInput (encode L) := by
  simpa [bits, encode, LayoutTapes.Bits] using
    LayoutTapes.handoffTape_normalizedOutput encode L

theorem handoffTape_handoff (L : Layout) :
    Tape.move tapeCodePrimitiveCodeWordHandoffMove (handoffTape L) =
      inputTape L := by
  simpa [handoffTape, inputTape, encode] using
    LayoutTapes.handoffTape_handoff encode_cons L

theorem handoffTape_move_left_eq_tape (L : Layout) :
    Tape.move Direction.left (handoffTape L) =
      Tape.input (MachineDescription.SimulatorLayout.asBoolInput L) := by
  simpa [handoffTape, inputTape, encode, LayoutTapes.HandoffTape,
    LayoutTapes.InputTape, MachineDescription.SimulatorLayout.asBoolInput,
    tapeCodePrimitiveCodeWordHandoffMove] using
    handoffTape_handoff L

theorem runCodePrimitive_transform_eq_some_cons
    {D : MachineDescription} {code out : Word MachineCodeSymbol}
    (h :
      (MachineDescription.SimulatorLayout.runCodePrimitive D).transform code =
        some out) :
    exists symbol : MachineCodeSymbol,
    exists tail : Word MachineCodeSymbol,
      out = symbol :: tail := by
  unfold MachineDescription.SimulatorLayout.runCodePrimitive at h
  unfold MachineDescription.SimulatorLayout.runCode at h
  cases hdecode : MachineDescription.SimulatorLayout.decodeComplete code with
  | none =>
      simp [hdecode] at h
  | some L =>
      simp [hdecode] at h
      cases h
      exact
        EncodedRewriters.CanonicalLayouts.Simulator.encode_cons
          (MachineDescription.SimulatorLayout.run D L.stage L)

end SimulatorLayouts

end CommonGround

end Computability
end FoC
