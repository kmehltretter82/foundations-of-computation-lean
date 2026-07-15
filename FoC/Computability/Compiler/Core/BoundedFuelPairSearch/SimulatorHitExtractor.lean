import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.AppendWord
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind
import FoC.Computability.Compiler.Core.EncRewriters.TotalOutputEmitter
import FoC.Computability.Compiler.Structured.Lowering.Composition

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open EncRewriters.TotalOutputEmitter

namespace BoundedFuelPairSearch

set_option doc.verso true

/-!
# Total simulator-hit extraction

This module extracts the accumulated hit bit from a serialized simulator
layout using checked finite tables.
-/

/-- Add a final encoded {lit}`true` cell token after a simulator layout.  The
existing total-output emitter then sees {lit}`(layout.hit, true)` as its final two
Boolean tokens. -/
def SimulatorHitSentinelCode (L : SimulatorLayout) :
    Word MachineCodeSymbol :=
  SimulatorLayout.encodeAppend L (encodeBoolAppend true [])

theorem simulatorHitSentinelCode_eq_append
    (L : SimulatorLayout) :
    SimulatorHitSentinelCode L =
      List.append (SimulatorLayout.encode L) [MachineCodeSymbol.one] := by
  cases L with
  | mk input stage config hit =>
      have hhit :
          encodeBoolAppend hit (encodeBoolAppend true []) =
            List.append (encodeBoolAppend hit [])
              [MachineCodeSymbol.one] := by
        simp [encodeBoolAppend, encodeCellAppend, encodeCell]
      have hconfig :
          encodeConfigurationAppend config
              (encodeBoolAppend hit (encodeBoolAppend true [])) =
            List.append
              (encodeConfigurationAppend config
                (encodeBoolAppend hit [])) [MachineCodeSymbol.one] := by
        rw [hhit]
        exact encodeConfigurationAppend_append config
          (encodeBoolAppend hit []) [MachineCodeSymbol.one]
      have hstage :
          encodeNatAppend stage
              (encodeConfigurationAppend config
                (encodeBoolAppend hit (encodeBoolAppend true []))) =
            List.append
              (encodeNatAppend stage
                (encodeConfigurationAppend config
                  (encodeBoolAppend hit []))) [MachineCodeSymbol.one] := by
        rw [hconfig]
        exact encodeNatAppend_append stage
          (encodeConfigurationAppend config (encodeBoolAppend hit []))
          [MachineCodeSymbol.one]
      have hinput :
          encodeBoolWordAppend input
              (encodeNatAppend stage
                (encodeConfigurationAppend config
                  (encodeBoolAppend hit (encodeBoolAppend true [])))) =
            List.append
              (encodeBoolWordAppend input
                (encodeNatAppend stage
                  (encodeConfigurationAppend config
                    (encodeBoolAppend hit [])))) [MachineCodeSymbol.one] := by
        rw [hstage]
        exact encodeBoolWordAppend_append input
          (encodeNatAppend stage
            (encodeConfigurationAppend config (encodeBoolAppend hit [])))
          [MachineCodeSymbol.one]
      simp only [SimulatorHitSentinelCode, SimulatorLayout.encode,
        SimulatorLayout.encodeAppend]
      rw [hinput]
      rfl

theorem simulatorHitSentinelBits_eq_append
    (L : SimulatorLayout) :
    encodeCodeWordAsInput (SimulatorHitSentinelCode L) =
      List.append (SimulatorLayout.asBoolInput L)
        (encodeCodeSymbolAsInput MachineCodeSymbol.one) := by
  rw [simulatorHitSentinelCode_eq_append,
    encodeCodeWordAsInput_append]
  rfl

theorem fstSourceTape_zero_equiv_input (bits : Word Bool) :
    Tape.Equiv (FSTSourceTape bits 0) (Tape.input bits) := by
  cases bits <;>
    simp [FSTSourceTape, tapeAtCells, Tape.input, Tape.blank, Tape.Equiv,
      FoC.Computability.dropTrailingNone_append_none]

def SimulatorHitSentinelAppender : MachineDescription :=
  generatedAppendFixedFourBitsDescription false true true false

theorem simulatorHitSentinelAppender_subroutineReady :
    SimulatorHitSentinelAppender.SubroutineReady := by
  exact generatedAppendFixedFourBitsDescription_subroutineReady
    false true true false

def SimulatorHitSentinelRightEdgeTape (L : SimulatorLayout) : Tape Bool :=
  FSTRightAppendedTargetTape
    (encodeCodeWordAsInput (SimulatorHitSentinelCode L)) 0

theorem simulatorHitSentinelAppender_haltsFromTapeEquiv
    (L : SimulatorLayout) :
    SimulatorHitSentinelAppender.HaltsFromTapeEquiv
      (SimulatorLayout.tape L)
      (SimulatorHitSentinelRightEdgeTape L) := by
  apply MachineDescription.HaltsFromTapeEquiv_of_input_equiv
    (Tin := FSTSourceTape (SimulatorLayout.asBoolInput L) 0)
  · simpa [SimulatorLayout.tape] using
      fstSourceTape_zero_equiv_input (SimulatorLayout.asBoolInput L)
  · simpa [SimulatorHitSentinelAppender,
      SimulatorHitSentinelRightEdgeTape,
      simulatorHitSentinelBits_eq_append,
      encodeCodeSymbolAsInput] using
      generatedAppendFixedFourBitsDescription_haltsFrom_FSTSourceTape
        false true true false (SimulatorLayout.asBoolInput L) 0

def SimulatorHitSentinelAlignedTape (L : SimulatorLayout) : Tape Bool :=
  rightEdgeRewindTargetTape
    (encodeCodeWordAsInput (SimulatorHitSentinelCode L)) []

theorem simulatorHitSentinelRewinder_haltsFromTape
    (L : SimulatorLayout) :
    rightEdgeRewindDescription.HaltsFromTape
      (SimulatorHitSentinelRightEdgeTape L)
      (SimulatorHitSentinelAlignedTape L) := by
  simpa [SimulatorHitSentinelRightEdgeTape,
    SimulatorHitSentinelAlignedTape,
    FSTRightAppendedTargetTape, rightEdgeRewindSourceTape,
    tapeAtCells] using
    rightEdgeRewindDescription_haltsFromTape
      (encodeCodeWordAsInput (SimulatorHitSentinelCode L)) []

theorem rightEdgeRewindTargetTape_nil_equiv_input (bits : Word Bool) :
    Tape.Equiv (rightEdgeRewindTargetTape bits []) (Tape.input bits) := by
  cases bits <;>
    simp [rightEdgeRewindTargetTape, tapeAtCells, Tape.input, Tape.blank,
      Tape.Equiv, Tape.dropTrailingNone,
      FoC.Computability.dropTrailingNone_append_none]

def SimulatorHitEmitterTargetTape (L : SimulatorLayout) : Tape Bool :=
  finalTape
    (0 + 4 * (SimulatorHitSentinelCode L).length)
    (scanBoundary (SimulatorHitSentinelCode L))

theorem totalOutputEmitter_haltsFromTape_simulatorHit
    (L : SimulatorLayout) :
    EncRewriters.TotalOutputEmitter.Description.HaltsFromTape
      (Tape.input (encodeCodeWordAsInput (SimulatorHitSentinelCode L)))
      (SimulatorHitEmitterTargetTape L) := by
  refine ⟨4 * (SimulatorHitSentinelCode L).length + 1 +
      (totalOutputEmitterBoundaryOutputBits
        (scanBoundary (SimulatorHitSentinelCode L))).length, ?_⟩
  have hrun := run_code_halt (SimulatorHitSentinelCode L)
  constructor
  · simpa [MachineDescription.initial] using
      congrArg MachineDescription.Configuration.state hrun
  · simpa [MachineDescription.initial, SimulatorHitEmitterTargetTape] using
      congrArg MachineDescription.Configuration.tape hrun

theorem totalOutputEmitter_haltsFromAlignedTapeEquiv_simulatorHit
    (L : SimulatorLayout) :
    EncRewriters.TotalOutputEmitter.Description.HaltsFromTapeEquiv
      (SimulatorHitSentinelAlignedTape L)
      (SimulatorHitEmitterTargetTape L) := by
  apply MachineDescription.HaltsFromTapeEquiv_of_input_equiv
    (Tin := Tape.input
      (encodeCodeWordAsInput (SimulatorHitSentinelCode L)))
  · exact Tape.Equiv.symm
      (by
        simpa [SimulatorHitSentinelAlignedTape] using
          rightEdgeRewindTargetTape_nil_equiv_input
            (encodeCodeWordAsInput (SimulatorHitSentinelCode L)))
  · exact totalOutputEmitter_haltsFromTape_simulatorHit L

/-- Physical preprocessing for hit extraction: append one encoded {lit}`true`
cell, then return to the left edge of the now-extended code word. -/
def SimulatorHitAppendRewindDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    SimulatorHitSentinelAppender rightEdgeRewindDescription

theorem simulatorHitAppendRewindDescription_subroutineReady :
    SimulatorHitAppendRewindDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    simulatorHitSentinelAppender_subroutineReady
    rightEdgeRewindDescription_subroutineReady

/-- The complete total hit extractor uses only checked-in finite tables. -/
def SimulatorHitExtractorDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    SimulatorHitAppendRewindDescription
    EncRewriters.TotalOutputEmitter.Description

theorem simulatorHitExtractorDescription_subroutineReady :
    SimulatorHitExtractorDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    simulatorHitAppendRewindDescription_subroutineReady
    EncRewriters.TotalOutputEmitter.description_ready

theorem simulatorHitAppendRewindDescription_haltsFromTapeEquiv
    (L : SimulatorLayout) :
    SimulatorHitAppendRewindDescription.HaltsFromTapeEquiv
      (SimulatorLayout.tape L)
      (SimulatorHitSentinelAlignedTape L) := by
  exact canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    simulatorHitSentinelAppender_subroutineReady
    rightEdgeRewindDescription_subroutineReady
    (simulatorHitSentinelAppender_haltsFromTapeEquiv L)
    (simulatorHitSentinelRewinder_haltsFromTape L).toEquiv

theorem simulatorHitExtractorDescription_haltsFromTapeEquiv
    (L : SimulatorLayout) :
    SimulatorHitExtractorDescription.HaltsFromTapeEquiv
      (SimulatorLayout.tape L)
      (SimulatorHitEmitterTargetTape L) := by
  exact canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    simulatorHitAppendRewindDescription_subroutineReady
    EncRewriters.TotalOutputEmitter.description_ready
    (simulatorHitAppendRewindDescription_haltsFromTapeEquiv L)
    (totalOutputEmitter_haltsFromAlignedTapeEquiv_simulatorHit L)

theorem scanBoundary_simulatorHitSentinelCode
    (L : SimulatorLayout) :
    EncRewriters.TotalOutputEmitter.scanBoundary
        (SimulatorHitSentinelCode L) =
      EncRewriters.TotalOutputEmitter.HitBoundary.ofHits L.hit true := by
  cases L with
  | mk input stage config hit =>
      let suffix : Word MachineCodeSymbol :=
        encodeBoolAppend hit (encodeBoolAppend true [])
      let pre : Word MachineCodeSymbol :=
        MachineCodeSymbol.header ::
          encodeBoolWordAppend input
            (encodeNatAppend stage
              (encodeConfigurationAppend config []))
      have hconfig :
          encodeConfigurationAppend config suffix =
            List.append (encodeConfigurationAppend config []) suffix := by
        exact encodeConfigurationAppend_append config [] suffix
      have hstage :
          encodeNatAppend stage
              (encodeConfigurationAppend config suffix) =
            List.append
              (encodeNatAppend stage
                (encodeConfigurationAppend config [])) suffix := by
        rw [hconfig]
        exact encodeNatAppend_append stage
          (encodeConfigurationAppend config []) suffix
      have hinput :
          encodeBoolWordAppend input
              (encodeNatAppend stage
                (encodeConfigurationAppend config suffix)) =
            List.append
              (encodeBoolWordAppend input
                (encodeNatAppend stage
                  (encodeConfigurationAppend config []))) suffix := by
        rw [hstage]
        exact encodeBoolWordAppend_append input
          (encodeNatAppend stage
            (encodeConfigurationAppend config [])) suffix
      change
        scanBoundaryFrom HitBoundary.other
            (MachineCodeSymbol.header ::
              encodeBoolWordAppend input
                (encodeNatAppend stage
                  (encodeConfigurationAppend config suffix))) =
          HitBoundary.ofHits hit true
      rw [hinput]
      change
        scanBoundaryFrom HitBoundary.other
            (List.append pre suffix) =
          HitBoundary.ofHits hit true
      rw [scanBoundaryFrom_append]
      exact scanBoundaryFrom_hit_suffix
        (scanBoundaryFrom HitBoundary.other pre) hit true

theorem hitSentinelBoundaryOutputBits
    (L : SimulatorLayout) :
    totalOutputEmitterBoundaryOutputBits
        (scanBoundary (SimulatorHitSentinelCode L)) =
      encodeCodeWordAsInput (encodeBoolWord [L.hit]) := by
  rw [scanBoundary_simulatorHitSentinelCode]
  cases L.hit <;> rfl

end BoundedFuelPairSearch

end Computability
end FoC
