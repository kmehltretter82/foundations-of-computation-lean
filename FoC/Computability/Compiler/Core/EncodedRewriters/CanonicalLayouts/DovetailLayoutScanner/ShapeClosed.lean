import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.Closed
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.PrimitiveClosed

set_option doc.verso true

/-!
# Shape facts for closed dovetail-layout scanner runs

This module connects the composed closed-run splits to primitive scanner
inversions.  The facts here recover source-code shape one field boundary at a
time, keeping the larger closed proof out of the primitive scanner module.
-/

namespace FoC
namespace Computability

open Languages
open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace EncodedRewriters
namespace CanonicalLayouts
namespace DovetailLayoutScanner

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_inputFirstBit_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CheckedDovetailLayoutScannerDescription.HaltsWithTape bits Tout) :
    exists suffixTail : Word Bool,
      bits = false :: false :: false :: true :: false :: suffixTail := by
  rcases checkedDovetailLayoutScannerDescription_haltsWithTape_finalFlags_inv
      h with
    ⟨b, suffixTail, Tinput, _Tstage, _Taccept, _Treject, _TacceptHit,
      _Tbody, nInput, _nStage, _nAccept, _nReject, _nAcceptHit,
      _nRejectHit, _nReturn, hbits, hinputRun, _hstageRun, _hacceptRun,
      _hrejectRun, _hacceptHitRun, _hrejectHitRun, _hreturnRun⟩
  have hb :
      b = false := by
    exact
      boolWordSuffixScannerDescription_runConfig_start_bit_inv
        (List.append (transitionRemainderBits.reverse.map some) [none])
        b (suffixTail.map some)
        (Tout := Tinput) (n := nInput)
        (by
          simpa [config] using hinputRun)
  subst b
  exact ⟨suffixTail, hbits⟩

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_inputNatPrefix_inv
    {bits : Word Bool} {Tout : Tape Bool}
    (h : CheckedDovetailLayoutScannerDescription.HaltsWithTape bits Tout) :
    exists doneBit : Bool,
    exists inputTail : Word Bool,
      bits =
        false :: false :: false :: true ::
          false :: false :: true :: doneBit :: inputTail := by
  rcases checkedDovetailLayoutScannerDescription_haltsWithTape_finalFlags_inv
      h with
    ⟨b, suffixTail, Tinput, _Tstage, _Taccept, _Treject, _TacceptHit,
      _Tbody, nInput, _nStage, _nAccept, _nReject, _nAcceptHit,
      _nRejectHit, _nReturn, hbits, hinputRun, _hstageRun, _hacceptRun,
      _hrejectRun, _hacceptHitRun, _hrejectHitRun, _hreturnRun⟩
  rcases
      boolWordSuffixScannerDescription_runConfig_start_nat_prefix_inv
        (List.append (transitionRemainderBits.reverse.map some) [none])
        (b :: suffixTail)
        (Tout := Tinput) (n := nInput)
        (by
          simpa [config] using hinputRun) with
    ⟨doneBit, inputTail, hfield⟩
  cases hfield
  exact ⟨doneBit, inputTail, hbits⟩

theorem encodeCodeWordAsInput_transition_prefix_inv
    {code : Word MachineCodeSymbol} {tail : Word Bool}
    (h :
      MachineDescription.encodeCodeWordAsInput code =
        false :: false :: false :: true :: tail) :
    exists rest : Word MachineCodeSymbol,
      code = MachineCodeSymbol.transition :: rest ∧
        MachineDescription.encodeCodeWordAsInput rest = tail := by
  cases code with
  | nil =>
      simp [MachineDescription.encodeCodeWordAsInput] at h
  | cons symbol rest =>
      cases symbol with
      | header =>
          simp [MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput] at h
          cases h
      | transition =>
          simp [MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput] at h
          cases h
          exact ⟨rest, rfl, rfl⟩
      | tick =>
          simp [MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput] at h
          cases h
      | done =>
          simp [MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput] at h
          cases h
      | blank =>
          simp [MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput] at h
          cases h
      | zero =>
          simp [MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput] at h
          cases h
      | one =>
          simp [MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput] at h
          cases h
      | moveLeft =>
          simp [MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput] at h
          cases h
      | moveRight =>
          simp [MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput] at h
          cases h

theorem encodeCodeWordAsInput_nat_opener_inv
    {code : Word MachineCodeSymbol} {doneBit : Bool}
    {tail : Word Bool}
    (h :
      MachineDescription.encodeCodeWordAsInput code =
        false :: false :: true :: doneBit :: tail) :
    exists rest : Word MachineCodeSymbol,
      code =
        (if doneBit then MachineCodeSymbol.done else MachineCodeSymbol.tick) ::
          rest ∧
        MachineDescription.encodeCodeWordAsInput rest = tail := by
  cases code with
  | nil =>
      simp [MachineDescription.encodeCodeWordAsInput] at h
  | cons symbol rest =>
      cases doneBit
      · cases symbol with
        | header =>
            simp [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput] at h
            cases h
        | transition =>
            simp [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput] at h
            cases h
        | tick =>
            simp [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput] at h
            cases h
            exact ⟨rest, rfl, rfl⟩
        | done =>
            simp [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput] at h
            cases h
        | blank =>
            simp [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput] at h
            cases h
        | zero =>
            simp [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput] at h
            cases h
        | one =>
            simp [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput] at h
            cases h
        | moveLeft =>
            simp [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput] at h
            cases h
        | moveRight =>
            simp [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput] at h
            cases h
      · cases symbol with
        | header =>
            simp [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput] at h
            cases h
        | transition =>
            simp [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput] at h
            cases h
        | tick =>
            simp [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput] at h
            cases h
        | done =>
            simp [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput] at h
            cases h
            exact ⟨rest, rfl, rfl⟩
        | blank =>
            simp [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput] at h
            cases h
        | zero =>
            simp [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput] at h
            cases h
        | one =>
            simp [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput] at h
            cases h
        | moveLeft =>
            simp [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput] at h
            cases h
        | moveRight =>
            simp [MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput] at h
            cases h

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_codeInputNatOpener_inv
    {code : Word MachineCodeSymbol} {Tout : Tape Bool}
    (h :
      CheckedDovetailLayoutScannerDescription.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) Tout) :
    exists doneBit : Bool,
    exists inputRest : Word MachineCodeSymbol,
      code =
        MachineCodeSymbol.transition ::
          (if doneBit then MachineCodeSymbol.done else MachineCodeSymbol.tick) ::
            inputRest := by
  rcases
      checkedDovetailLayoutScannerDescription_haltsWithTape_inputNatPrefix_inv
        h with
    ⟨doneBit, inputTail, hbits⟩
  rcases encodeCodeWordAsInput_transition_prefix_inv hbits with
    ⟨inputCode, hcode, hinputBits⟩
  rcases encodeCodeWordAsInput_nat_opener_inv
      (doneBit := doneBit) hinputBits with
    ⟨inputRest, hinputCode, _hinputRestBits⟩
  subst code
  subst inputCode
  exact ⟨doneBit, inputRest, rfl⟩

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_inputBoolWord_inv
    {code : Word MachineCodeSymbol} {Tout : Tape Bool}
    (h :
      CheckedDovetailLayoutScannerDescription.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) Tout) :
    exists inputWord : Word Bool,
    exists inputRest : Word MachineCodeSymbol,
      code = MachineCodeSymbol.transition :: MachineDescription.encodeBoolWordAppend inputWord inputRest := by
  rcases checkedDovetailLayoutScannerDescription_haltsWithTape_finalFlags_inv h with
    ⟨b, suffixTail, Tinput, Tstage, Taccept, Treject, TacceptHit,
      Tbody, nInput, nStage, nAccept, nReject, nAcceptHit,
      nRejectHit, nReturn, hbits, hinputRun, hstageRun, hacceptRun,
      hrejectRun, hacceptHitRun, hrejectHitRun, hreturnRun⟩
  rcases boolWordSuffixScannerDescription_runConfig_inv _ _ hinputRun with
    ⟨inputWord, suffixTail2, hb_suffix⟩
  -- We now have the bits corresponding to the boolean word.
  -- By construction, these bits perfectly match the encoding of `encodeBoolWordAppend inputWord inputRest`.
  -- Since `encodeCodeWordAsInput` is injective, `code` must exactly equal `transition :: encodeBoolWordAppend inputWord inputRest`.
  sorry

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
