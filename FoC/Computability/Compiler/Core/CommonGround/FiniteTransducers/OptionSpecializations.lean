import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OptionAppend
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.MapAppend
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.EraseAppend

set_option doc.verso true

/-!
# Optional-output compiler specializations

This module records that the optional-output compiler is the common
one-state compiler behind the bit-map and erase compiler slices.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace CommonGround
namespace FiniteTransducers

theorem optionAppendFinalTransducer_some_eq_bitMap
    (emit : Bool -> Bool) (final : Word Bool) :
    optionAppendFinalTransducer (fun bit => some (emit bit)) final =
      bitMapAppendFinalTransducer emit final := by
  rfl

theorem optionAppendFinalTransducer_none_eq_erase
    (final : Word Bool) :
    optionAppendFinalTransducer (fun _bit => none) final =
      eraseAppendFinalTransducer final := by
  rfl

theorem generatedOptionAppendWordDescription_some_eq_map
    (emit : Bool -> Bool) (final : Word Bool) :
    generatedOptionAppendWordDescription
        (fun bit => some (emit bit)) final =
      generatedMapAppendWordDescription emit final := by
  cases h : FiniteTransducer.copyAppendWordWriteTransitionsFrom 0
      (FiniteTransducer.copyAppendWordHalt final) final with
  | nil =>
      simp [generatedOptionAppendWordDescription,
        generatedMapAppendWordDescription,
        FiniteTransducer.optionAppendWordTransitions,
        FiniteTransducer.mapAppendWordTransitions,
        FiniteTransducer.optionAppendWordScanFalseTransition,
        FiniteTransducer.optionAppendWordScanTrueTransition,
        FiniteTransducer.mapAppendWordScanFalseTransition,
        FiniteTransducer.mapAppendWordScanTrueTransition, h]
  | cons _first _rest =>
      simp [generatedOptionAppendWordDescription,
        generatedMapAppendWordDescription,
        FiniteTransducer.optionAppendWordTransitions,
        FiniteTransducer.mapAppendWordTransitions,
        FiniteTransducer.optionAppendWordScanFalseTransition,
        FiniteTransducer.optionAppendWordScanTrueTransition,
        FiniteTransducer.mapAppendWordScanFalseTransition,
        FiniteTransducer.mapAppendWordScanTrueTransition, h]

theorem generatedOptionAppendWordDescription_none_eq_erase
    (final : Word Bool) :
    generatedOptionAppendWordDescription (fun _bit => none) final =
      generatedEraseAppendWordDescription final := by
  cases h : FiniteTransducer.copyAppendWordWriteTransitionsFrom 0
      (FiniteTransducer.copyAppendWordHalt final) final with
  | nil =>
      simp [generatedOptionAppendWordDescription,
        generatedEraseAppendWordDescription,
        FiniteTransducer.optionAppendWordTransitions,
        FiniteTransducer.eraseAppendWordTransitions,
        FiniteTransducer.optionAppendWordScanFalseTransition,
        FiniteTransducer.optionAppendWordScanTrueTransition,
        FiniteTransducer.eraseAppendWordScanFalseTransition,
        FiniteTransducer.eraseAppendWordScanTrueTransition, h]
  | cons _first _rest =>
      simp [generatedOptionAppendWordDescription,
        generatedEraseAppendWordDescription,
        FiniteTransducer.optionAppendWordTransitions,
        FiniteTransducer.eraseAppendWordTransitions,
        FiniteTransducer.optionAppendWordScanFalseTransition,
        FiniteTransducer.optionAppendWordScanTrueTransition,
        FiniteTransducer.eraseAppendWordScanFalseTransition,
        FiniteTransducer.eraseAppendWordScanTrueTransition, h]

theorem FSTOptionAppendFinalWordTargetTape_some_eq_map
    (emit : Bool -> Bool) (input final : Word Bool)
    (leftScratch : Nat) :
    FSTOptionAppendFinalWordTargetTape
        (fun bit => some (emit bit)) input final leftScratch =
      FSTMapAppendFinalWordTargetTape emit input final leftScratch := by
  simp [FSTOptionAppendFinalWordTargetTape,
    FSTMapAppendFinalWordTargetTape, Function.comp_def]

theorem FSTOptionAppendFinalWordTargetTape_none_eq_erase
    (input final : Word Bool) (leftScratch : Nat) :
    FSTOptionAppendFinalWordTargetTape
        (fun _bit => none) input final leftScratch =
      FSTEraseAppendFinalWordTargetTape input final leftScratch := by
  simp [FSTOptionAppendFinalWordTargetTape,
    FSTEraseAppendFinalWordTargetTape]

theorem bitMapAppendFinalTransducer_compiledByOptionDescription
    (emit : Bool -> Bool) (final : Word Bool) :
    ExactCompiledByDescription
      (bitMapAppendFinalTransducer emit final)
      (generatedOptionAppendWordDescription
        (fun bit => some (emit bit)) final)
      (fun input _output leftScratch =>
        FSTMapAppendFinalWordTargetTape emit input final leftScratch) := by
  constructor
  · exact generatedOptionAppendWordDescription_subroutineReady
      (fun bit => some (emit bit)) final
  · intro input output leftScratch hrun
    have hrun' :
        (optionAppendFinalTransducer
          (fun bit => some (emit bit)) final).RunsToOutput
            input output := by
      simpa [optionAppendFinalTransducer_some_eq_bitMap] using hrun
    have hhalt :=
      (optionAppendFinalTransducer_compiledByGeneratedDescription
        (fun bit => some (emit bit)) final).right
          input output leftScratch hrun'
    simpa [FSTOptionAppendFinalWordTargetTape_some_eq_map] using hhalt

theorem eraseAppendFinalTransducer_compiledByOptionDescription
    (final : Word Bool) :
    ExactCompiledByDescription
      (eraseAppendFinalTransducer final)
      (generatedOptionAppendWordDescription (fun _bit => none) final)
      (fun input _output leftScratch =>
        FSTEraseAppendFinalWordTargetTape input final leftScratch) := by
  constructor
  · exact generatedOptionAppendWordDescription_subroutineReady
      (fun _bit => none) final
  · intro input output leftScratch hrun
    have hrun' :
        (optionAppendFinalTransducer
          (fun _bit => none) final).RunsToOutput input output := by
      simpa [optionAppendFinalTransducer_none_eq_erase] using hrun
    have hhalt :=
      (optionAppendFinalTransducer_compiledByGeneratedDescription
        (fun _bit => none) final).right input output leftScratch hrun'
    simpa [FSTOptionAppendFinalWordTargetTape_none_eq_erase] using hhalt

end FiniteTransducers
end CommonGround

end Computability
end FoC
