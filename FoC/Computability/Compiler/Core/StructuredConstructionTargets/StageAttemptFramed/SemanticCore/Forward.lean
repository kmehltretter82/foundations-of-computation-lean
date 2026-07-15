import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.SemanticCore.ValidB

namespace FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open EncRewriters.CanonicalLayouts.DovetailLayoutScanner
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

theorem leads_index_to_attempt_halt_covered
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (i : StructuredConstructionTargets.StageAttemptFramedStructuredIndex attempt) :
    ∃ Tout T1 : Tape Bool,
      Leads attempt hattempt
        (cfg attempt hattempt .header0
          (Tape.input
            (StructuredConstructionTargets.stageAttemptFramedStructuredInputBits
              i.C))
          Tape.blank Tape.blank)
        (cfg attempt hattempt (.run attempt.halt) Tout T1
          (tapeAtCells (parsedInputLeft2 i.C) [])) ∧
      CoveredTapes Tout T1 ∧
      Tape.normalizedOutput Tout = resultBits i.result := by
  let bits := stageInputBits i.C
  let sourceResult := resultBits i.C.result
  let expected := resultBits i.result
  let Tin := reconstructedTape bits sourceResult
  let c : MachineDescription.Configuration :=
    { state := attempt.start, tape := Tin }
  let canonical := attempt.initial bits
  have hTin : Tape.Equiv Tin (Tape.input bits) :=
    reconstructedTape_equiv_input_result bits sourceResult
      (stageInputBits_ne_nil i.C)
  have hequiv := MachineDescription.runConfig_equiv attempt i.fuel
    (c := c) (d := canonical) (by rfl) hTin
  have hcanonical :
      (attempt.runConfig i.fuel canonical).state = attempt.halt ∧
        Tape.normalizedOutput (attempt.runConfig i.fuel canonical).tape = expected := by
    simpa [bits, expected, canonical, stageInputBits, resultBits,
      MachineDescription.HaltsWithOutputIn] using
      i.attempt_halts
  have hstate : (attempt.runConfig i.fuel c).state = attempt.halt :=
    hequiv.left.trans hcanonical.left
  let Tout := (attempt.runConfig i.fuel c).tape
  have hrun : attempt.runConfig i.fuel c =
      { state := attempt.halt, tape := Tout } := by
    cases hfinal : attempt.runConfig i.fuel c with
    | mk state tape =>
        simp [Tout, hfinal] at hstate ⊢
        exact hstate
  rcases MachineDescription.firstReaches_halt_of_runConfig_eq
      hattempt.right hrun with
    ⟨first, _hfirstLe, hfirstRun, hminimal⟩
  have hcoveredStart : CoveredTapes Tin (markerTape bits) :=
    covered_reconstructed_marker bits sourceResult (stageInputBits_ne_nil i.C)
  rcases leads_attempt_first_halt_covered
      (attempt := attempt) (hattempt := hattempt)
      (n := first) (c := c) (Tout := Tout)
      (T1 := markerTape bits)
      (T2 := tapeAtCells (parsedInputLeft2 i.C) [])
      hattempt.left.right.left hfirstRun hminimal hcoveredStart with
    ⟨T1, hlift, hcovered⟩
  have hprefix := leads_controller_to_run_start
    (attempt := attempt) (hattempt := hattempt) i.C
  have houtput : Tape.normalizedOutput Tout = expected := by
    exact (Tape.Equiv.normalizedOutput_eq hequiv.right).trans hcanonical.right
  refine ⟨Tout, T1, ?_, hcovered, ?_⟩
  · simpa [bits, sourceResult, Tin, c] using hprefix.trans hlift
  · simpa [expected] using houtput

theorem leads_index_to_halt
    {attempt : MachineDescription} {hattempt : attempt.SubroutineReady}
    (i : StructuredConstructionTargets.StageAttemptFramedStructuredIndex attempt) :
    ∃ T0 T1 : Tape Bool,
      Leads attempt hattempt
        (cfg attempt hattempt .header0
          (Tape.input
            (StructuredConstructionTargets.stageAttemptFramedStructuredInputBits
              i.C))
          Tape.blank Tape.blank)
        (cfg attempt hattempt .halt T0 T1
          (CommonGround.ControllerInvocation.StageAttemptFramedOutputTape
            i.C i.result)) := by
  rcases leads_index_to_attempt_halt_covered
      (attempt := attempt) (hattempt := hattempt) i with
    ⟨Tout, T1, hrun, hcovered, houtput⟩
  rcases leads_run_halt_to_result_first
      (attempt := attempt) (hattempt := hattempt)
      Tout T1 (tapeAtCells (parsedInputLeft2 i.C) []) hcovered with
    ⟨workStream, markerRest, hnormalize, hcover0, hshape0,
      hnormalizeOutput⟩
  have hfilter0 : workStream.filterMap id = resultBits i.result := by
    rw [← normalizedOutput_tapeAtCells_left_none]
    exact hnormalizeOutput.trans houtput
  have hfilterLength : workStream.filterMap id =
      List.append (stageNatBits i.result.length) (cellsBits i.result) := by
    exact hfilter0.trans (resultBits_eq_length_cells i.result)
  rcases leads_resultFirst_length
      (attempt := attempt) (hattempt := hattempt)
      0 i.result.length (cellsBits i.result)
      [none] [none] workStream (some false :: markerRest)
      (tapeAtCells (parsedInputLeft2 i.C) [])
      hcover0 hshape0 hfilterLength MarkerStack.boundary with
    ⟨L0a, L1a, worka, markersa, hlength,
      hcovera, hshapea, hfiltera, hstacka⟩
  rcases leads_cells
      (attempt := attempt) (hattempt := hattempt)
      0 i.result [] L0a L1a worka markersa
      (writeOutputPrefix (stageNatBits i.result.length)
        (cellsBits i.result)
        (tapeAtCells (parsedInputLeft2 i.C) []))
      hcovera hshapea (by simpa using hfiltera)
      (by simpa using hstacka) with
    ⟨L0b, L1b, workb, markersb, hcells,
      hcoverb, hshapeb, hfilterb, hstackb⟩
  let writtenResult :=
    writeOutputPrefix (cellsBits i.result) []
      (writeOutputPrefix (stageNatBits i.result.length)
        (cellsBits i.result)
        (tapeAtCells (parsedInputLeft2 i.C) []))
  rcases leads_seekCell_finish
      (attempt := attempt) (hattempt := hattempt)
      L0b L1b workb markersb writtenResult
      hcoverb hshapeb hfilterb hstackb with
    ⟨T0b, T1b, hfinish⟩
  have hwritten : writtenResult =
      writeOutputBitsFinal (resultBits i.result)
        (tapeAtCells (parsedInputLeft2 i.C) []) := by
    rw [resultBits_eq_length_cells]
    simpa [writtenResult, writeOutputPrefix] using
      (writeOutputPrefix_append
        (stageNatBits i.result.length) (cellsBits i.result) []
        (tapeAtCells (parsedInputLeft2 i.C) [])).symm
  have hrewind := leads_rewind_framedPayload_exact
    (attempt := attempt) (hattempt := hattempt)
    i.C i.result T0b T1b
  rw [← hwritten] at hrewind
  refine ⟨keepR.apply T0b, T1b, ?_⟩
  exact hrun.trans
    (hnormalize.trans (hlength.trans (hcells.trans (hfinish.trans hrewind))))

end FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore
