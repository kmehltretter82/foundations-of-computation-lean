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
      cellListSuffixScannerDescription_runConfig_start_bit_inv
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
      cellListSuffixScannerDescription_runConfig_start_nat_prefix_inv
        (List.append (transitionRemainderBits.reverse.map some) [none])
        (b :: suffixTail)
        (Tout := Tinput) (n := nInput)
        (by
          simpa [config] using hinputRun) with
    ⟨doneBit, inputTail, hfield⟩
  cases hfield
  exact ⟨doneBit, inputTail, hbits⟩

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
