import FoC.Computability.Compiler.Core.EncodedRewriters.RightShifted

set_option doc.verso true

/-!
# Canonical encoded-layout validators

This module contains the reusable tape-shape and adapter layer for complete
canonical code-word layouts.  Concrete validators only need to provide the
closed recognizer spec below; the generic theorem packages that recognizer as
the closed-handoff identity primitive expected by the sequencing layer.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace CanonicalLayouts

def Bits {α : Type}
    (encode : α -> Word MachineCodeSymbol) (a : α) : Word Bool :=
  encodeCodeWordAsInput (encode a)

def InputTape {α : Type}
    (encode : α -> Word MachineCodeSymbol) (a : α) : Tape Bool :=
  FoC.Computability.Tape.input (Bits encode a)

def HandoffTape {α : Type}
    (encode : α -> Word MachineCodeSymbol) (a : α) : Tape Bool :=
  FoC.Computability.Tape.move Direction.right (InputTape encode a)

def IdentityPrimitive {α : Type}
    (decode : Word MachineCodeSymbol -> Option α) :
    TapeCodePrimitive where
  transform := fun code =>
    match decode code with
    | none => none
    | some _ => some code

theorem identityPrimitive_transform_eq_some_iff
    {α : Type}
    {decode : Word MachineCodeSymbol -> Option α}
    {encode : α -> Word MachineCodeSymbol}
    (hdecodeEncode :
      forall a : α, decode (encode a) = some a)
    (hdecodeEqSomeEncode :
      forall {code : Word MachineCodeSymbol} {a : α},
        decode code = some a -> code = encode a)
    (code out : Word MachineCodeSymbol) :
    (IdentityPrimitive decode).transform code = some out <->
      exists a : α, code = encode a ∧ out = encode a := by
  constructor
  · intro h
    unfold IdentityPrimitive at h
    cases hdecode : decode code with
    | none =>
        simp [hdecode] at h
    | some a =>
        simp [hdecode] at h
        cases h
        exact ⟨a, hdecodeEqSomeEncode hdecode, hdecodeEqSomeEncode hdecode⟩
  · intro h
    rcases h with ⟨a, rfl, rfl⟩
    simp [IdentityPrimitive, hdecodeEncode a]

theorem identityPrimitive_encode
    {α : Type}
    {decode : Word MachineCodeSymbol -> Option α}
    {encode : α -> Word MachineCodeSymbol}
    (hdecodeEncode :
      forall a : α, decode (encode a) = some a)
    (a : α) :
    (IdentityPrimitive decode).transform (encode a) = some (encode a) := by
  simp [IdentityPrimitive, hdecodeEncode a]

theorem handoffTape_normalizedOutput
    {α : Type}
    (encode : α -> Word MachineCodeSymbol) (a : α) :
    FoC.Computability.Tape.normalizedOutput (HandoffTape encode a) =
      Bits encode a := by
  simpa [HandoffTape, InputTape, Bits] using
    EncodedRewriters.tape_normalizedOutput_move_right_input (Bits encode a)

theorem handoffTape_handoff
    {α : Type}
    {encode : α -> Word MachineCodeSymbol}
    (hencodeCons :
      forall a : α,
        exists symbol : MachineCodeSymbol,
        exists tail : Word MachineCodeSymbol,
          encode a = symbol :: tail)
    (a : α) :
    FoC.Computability.Tape.move tapeCodePrimitiveCodeWordHandoffMove
        (HandoffTape encode a) =
      InputTape encode a := by
  rcases hencodeCons a with ⟨symbol, tail, htail⟩
  simpa [HandoffTape, InputTape, Bits, htail,
    tapeCodePrimitiveCodeWordHandoffMove] using
    EncodedRewriters.tape_move_left_move_right_input_encodeCodeWordAsInput_cons
      symbol tail

def ClosedRecognizerSpec {α : Type}
    (decode : Word MachineCodeSymbol -> Option α)
    (encode : α -> Word MachineCodeSymbol)
    (recognizer : MachineDescription) : Prop :=
  recognizer.SubroutineReady ∧
    (forall a : α,
      recognizer.HaltsWithTape
        (Bits encode a)
        (HandoffTape encode a)) ∧
      forall code : Word MachineCodeSymbol,
      forall T : FoC.Computability.Tape Bool,
        recognizer.HaltsWithTape
            (encodeCodeWordAsInput code) T ->
          exists a : α,
            decode code = some a ∧
              T = HandoffTape encode a

def ClosedRecognizerConstruction {α : Type}
    (decode : Word MachineCodeSymbol -> Option α)
    (encode : α -> Word MachineCodeSymbol) : Prop :=
  exists recognizer : MachineDescription,
    ClosedRecognizerSpec decode encode recognizer

def IdentityClosedHandoffConstruction {α : Type}
    (decode : Word MachineCodeSymbol -> Option α) : Prop :=
  exists closed : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      (IdentityPrimitive decode)
      closed tapeCodePrimitiveCodeWordHandoffMove

theorem identityPrimitive_transform_eq_some_cons
    {α : Type}
    {decode : Word MachineCodeSymbol -> Option α}
    {encode : α -> Word MachineCodeSymbol}
    (hdecodeEncode :
      forall a : α, decode (encode a) = some a)
    (hdecodeEqSomeEncode :
      forall {code : Word MachineCodeSymbol} {a : α},
        decode code = some a -> code = encode a)
    (hencodeCons :
      forall a : α,
        exists symbol : MachineCodeSymbol,
        exists tail : Word MachineCodeSymbol,
          encode a = symbol :: tail)
    {code out : Word MachineCodeSymbol}
    (h : (IdentityPrimitive decode).transform code = some out) :
    exists symbol : MachineCodeSymbol,
    exists tail : Word MachineCodeSymbol,
      out = symbol :: tail := by
  rcases
      (identityPrimitive_transform_eq_some_iff
        hdecodeEncode hdecodeEqSomeEncode code out).mp h with
    ⟨a, _hcode, hout⟩
  rcases hencodeCons a with ⟨symbol, tail, htail⟩
  exact ⟨symbol, tail, by rw [hout, htail]⟩

theorem identityClosedHandoffConstruction_of_closedRecognizer
    {α : Type}
    {decode : Word MachineCodeSymbol -> Option α}
    {encode : α -> Word MachineCodeSymbol}
    (hdecodeEncode :
      forall a : α, decode (encode a) = some a)
    (hdecodeEqSomeEncode :
      forall {code : Word MachineCodeSymbol} {a : α},
        decode code = some a -> code = encode a)
    (hencodeCons :
      forall a : α,
        exists symbol : MachineCodeSymbol,
        exists tail : Word MachineCodeSymbol,
          encode a = symbol :: tail)
    (h :
      ClosedRecognizerConstruction decode encode) :
    IdentityClosedHandoffConstruction decode := by
  rcases h with ⟨recognizer, hrecognizer⟩
  refine ⟨recognizer, ?_⟩
  constructor
  · constructor
    · constructor
      · exact hrecognizer.left.left
      · intro code out
        constructor
        · intro hhalt
          rcases hhalt with ⟨n, hn⟩
          let T : FoC.Computability.Tape Bool :=
            (recognizer.runConfig n
              (recognizer.initial
                (encodeCodeWordAsInput code))).tape
          have hTape :
              recognizer.HaltsWithTape
                  (encodeCodeWordAsInput code) T := by
            refine ⟨n, ?_⟩
            exact ⟨hn.left, rfl⟩
          rcases hrecognizer.right.right code T hTape with
            ⟨a, hdecode, hT⟩
          have houtBits :
              encodeCodeWordAsInput out =
                encodeCodeWordAsInput (encode a) := by
            calc
              encodeCodeWordAsInput out =
                  FoC.Computability.Tape.normalizedOutput T := by
                    simpa [T] using hn.right.symm
              _ =
                  encodeCodeWordAsInput (encode a) := by
                    rw [hT]
                    simp [Bits, handoffTape_normalizedOutput]
          have hout : out = encode a :=
            encodeCodeWordAsInput_injective houtBits
          have hcode : code = encode a :=
            hdecodeEqSomeEncode hdecode
          rw [hcode, hout]
          exact identityPrimitive_encode hdecodeEncode a
        · intro htransform
          rcases
              (identityPrimitive_transform_eq_some_iff
                hdecodeEncode hdecodeEqSomeEncode code out).mp
                htransform with
            ⟨a, hcode, hout⟩
          subst code
          subst out
          have hhalt :
              recognizer.HaltsWithOutput
                (encodeCodeWordAsInput (encode a))
                (FoC.Computability.Tape.normalizedOutput
                  (HandoffTape encode a)) :=
            haltsWithOutput_of_haltsWithTape
              (hrecognizer.right.left a)
          simpa [Bits, handoffTape_normalizedOutput] using hhalt
    · exact hrecognizer.left.right
  · intro code T hhalt
    rcases hrecognizer.right.right code T hhalt with
      ⟨a, hdecode, hT⟩
    refine ⟨encode a, ?_, ?_, ?_⟩
    · have hcode : code = encode a :=
        hdecodeEqSomeEncode hdecode
      subst code
      exact identityPrimitive_encode hdecodeEncode a
    · rw [hT]
      simp [Bits, handoffTape_normalizedOutput]
    · rw [hT]
      exact handoffTape_handoff hencodeCons a

end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
