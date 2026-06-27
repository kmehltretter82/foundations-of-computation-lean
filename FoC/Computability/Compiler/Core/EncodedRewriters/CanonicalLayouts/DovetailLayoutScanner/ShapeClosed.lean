import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.Closed
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.BoolWordClosed

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
open MachineDescription
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
      encodeCodeWordAsInput code =
        false :: false :: false :: true :: tail) :
    exists rest : Word MachineCodeSymbol,
      code = MachineCodeSymbol.transition :: rest ∧
        encodeCodeWordAsInput rest = tail := by
  cases code with
  | nil =>
      simp [encodeCodeWordAsInput] at h
  | cons symbol rest =>
      cases symbol with
      | header =>
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput] at h
          cases h
      | transition =>
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput] at h
          cases h
          exact ⟨rest, rfl, rfl⟩
      | tick =>
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput] at h
          cases h
      | done =>
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput] at h
          cases h
      | blank =>
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput] at h
          cases h
      | zero =>
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput] at h
          cases h
      | one =>
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput] at h
          cases h
      | moveLeft =>
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput] at h
          cases h
      | moveRight =>
          simp [encodeCodeWordAsInput,
            encodeCodeSymbolAsInput] at h
          cases h

theorem encodeCodeWordAsInput_nat_opener_inv
    {code : Word MachineCodeSymbol} {doneBit : Bool}
    {tail : Word Bool}
    (h :
      encodeCodeWordAsInput code =
        false :: false :: true :: doneBit :: tail) :
    exists rest : Word MachineCodeSymbol,
      code =
        (if doneBit then MachineCodeSymbol.done else MachineCodeSymbol.tick) ::
          rest ∧
        encodeCodeWordAsInput rest = tail := by
  cases code with
  | nil =>
      simp [encodeCodeWordAsInput] at h
  | cons symbol rest =>
      cases doneBit
      · cases symbol with
        | header =>
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at h
            cases h
        | transition =>
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at h
            cases h
        | tick =>
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at h
            cases h
            exact ⟨rest, rfl, rfl⟩
        | done =>
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at h
            cases h
        | blank =>
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at h
            cases h
        | zero =>
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at h
            cases h
        | one =>
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at h
            cases h
        | moveLeft =>
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at h
            cases h
        | moveRight =>
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at h
            cases h
      · cases symbol with
        | header =>
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at h
            cases h
        | transition =>
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at h
            cases h
        | tick =>
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at h
            cases h
        | done =>
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at h
            cases h
            exact ⟨rest, rfl, rfl⟩
        | blank =>
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at h
            cases h
        | zero =>
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at h
            cases h
        | one =>
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at h
            cases h
        | moveLeft =>
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at h
            cases h
        | moveRight =>
            simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] at h
            cases h

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_codeInputNatOpener_inv
    {code : Word MachineCodeSymbol} {Tout : Tape Bool}
    (h :
      CheckedDovetailLayoutScannerDescription.HaltsWithTape
        (encodeCodeWordAsInput code) Tout) :
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
        (encodeCodeWordAsInput code) Tout) :
    exists inputWord : Word Bool,
    exists inputRest : Word MachineCodeSymbol,
      code = MachineCodeSymbol.transition :: encodeBoolWordAppend inputWord inputRest := by
  rcases checkedDovetailLayoutScannerDescription_haltsWithTape_finalFlags_inv h with
    ⟨b, suffixTail, Tinput, Tstage, Taccept, Treject, TacceptHit,
      Tbody, nInput, nStage, nAccept, nReject, nAcceptHit,
      nRejectHit, nReturn, hbits, hinputRun, hstageRun, hacceptRun,
      hrejectRun, hacceptHitRun, hrejectHitRun, hreturnRun⟩
  rcases encodeCodeWordAsInput_transition_prefix_inv hbits with
    ⟨inputCode, hcode, hinputBits⟩
  have hinputRunCode :
      BoolWordSuffixScannerDescription.runConfig nInput
          (config BoolWordSuffixScannerDescription.start
            (List.append (transitionRemainderBits.reverse.map some) [none])
            ((encodeCodeWordAsInput inputCode).map
              some)) =
        { state := BoolWordSuffixScannerDescription.halt
          tape := Tinput } := by
    rw [hinputBits]
    simpa [config] using hinputRun
  rcases
      boolWordSuffixScannerDescription_runConfig_code_inv
        (List.append (transitionRemainderBits.reverse.map some) [none])
        inputCode hinputRunCode with
    ⟨inputWord, inputRest, hinputCode⟩
  exact ⟨inputWord, inputRest, by rw [hcode, hinputCode]⟩

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
