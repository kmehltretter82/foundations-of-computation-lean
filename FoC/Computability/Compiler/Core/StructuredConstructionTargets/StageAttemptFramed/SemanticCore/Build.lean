import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.SemanticCore.Forward
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.SemanticCore.Diverge
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.SemanticCore.InvRun
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.SemanticCore.InvValid

namespace FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

def LogicalHaltRecoversIndex
    (attempt : MachineDescription) (hattempt : attempt.SubroutineReady) : Prop :=
  forall C : DovetailControllerLayout,
    (exists k : Nat,
      ((coreD attempt hattempt).runConfig k
        (cfg attempt hattempt .header0
          (Tape.input
            (StructuredConstructionTargets.stageAttemptFramedStructuredInputBits
              C))
          Tape.blank Tape.blank)).state =
        (coreD attempt hattempt).halt) ->
      exists i :
          StructuredConstructionTargets.StageAttemptFramedStructuredIndex
            attempt,
        C = i.C

theorem logicalHaltRecoversIndex
    (attempt : MachineDescription) (hattempt : attempt.SubroutineReady) :
    LogicalHaltRecoversIndex attempt hattempt := by
  intro C hlogical
  rcases hlogical with ⟨n, hhalt⟩
  rcases controller_core_halt_implies_attempt_halt C n hhalt with
    ⟨fuel0, Tout0, hattemptRun0⟩
  let bits := stageInputBits C
  let sourceResult := resultBits C.result
  let Tin := reconstructedTape bits sourceResult
  let c : MachineDescription.Configuration :=
    { state := attempt.start, tape := Tin }
  have hattemptRun0' :
      attempt.runConfig fuel0 c =
        { state := attempt.halt, tape := Tout0 } := by
    simpa [bits, sourceResult, Tin, c] using hattemptRun0
  rcases MachineDescription.firstReaches_halt_of_runConfig_eq
      hattempt.right hattemptRun0' with
    ⟨fuel, _hfirstLe, hattemptRun, hminimal⟩
  have hcoveredStart : CoveredTapes Tin (markerTape bits) := by
    exact covered_reconstructed_marker bits sourceResult
      (stageInputBits_ne_nil C)
  rcases leads_attempt_first_halt_covered
      (attempt := attempt) (hattempt := hattempt)
      (n := fuel) (c := c) (Tout := Tout0)
      (T1 := markerTape bits)
      (T2 := tapeAtCells (parsedInputLeft2 C) [])
      hattempt.left.right.left hattemptRun hminimal hcoveredStart with
    ⟨T1, hlift, hcovered⟩
  have hprefix := leads_controller_to_run_start
    (attempt := attempt) (hattempt := hattempt) C
  have htoRunHalt :
      Leads attempt hattempt
        (cfg attempt hattempt .header0
          (Tape.input
            (StructuredConstructionTargets.stageAttemptFramedStructuredInputBits
              C))
          Tape.blank Tape.blank)
        (cfg attempt hattempt (.run attempt.halt)
          Tout0 T1 (tapeAtCells (parsedInputLeft2 C) [])) := by
    simpa [bits, sourceResult, Tin, c] using hprefix.trans hlift
  rcases target_halts_of_leads
      ((table attempt hattempt).description_haltTransitionFree)
      htoRunHalt hhalt with
    ⟨m, hm⟩
  have hhaltRun : EventuallyHalts attempt hattempt
      (cfg attempt hattempt (.run attempt.halt)
        Tout0 T1 (tapeAtCells (parsedInputLeft2 C) [])) := by
    exact ⟨m, hm⟩
  rcases validator_result_of_run_halt
      Tout0 T1 (tapeAtCells (parsedInputLeft2 C) [])
      hcovered hhaltRun with
    ⟨result, houtput⟩
  have hattemptHalts := haltsWithOutputIn_of_reconstructed_run
    C fuel Tout0 result
    (by simpa [bits, sourceResult, Tin, c] using hattemptRun)
    houtput
  let i :
      StructuredConstructionTargets.StageAttemptFramedStructuredIndex
        attempt :=
    { C := C
      result := result
      fuel := fuel
      attempt_halts := hattemptHalts }
  exact ⟨i, rfl⟩

theorem stageAttemptFramedStructuredSemanticCoreConstruction_of_logicalClosed
    (attempt : MachineDescription) (hattempt : attempt.SubroutineReady)
    (hrecover : LogicalHaltRecoversIndex attempt hattempt) :
    StructuredConstructionTargets.StageAttemptFramedStructuredSemanticCoreConstruction
      attempt := by
  classical
  let forwardExists := fun i =>
    leads_index_to_halt (attempt := attempt) (hattempt := hattempt) i
  let tape0 := fun i => Classical.choose (forwardExists i)
  let tape1 := fun i =>
    Classical.choose (Classical.choose_spec (forwardExists i))
  have hleads : forall i,
      Leads attempt hattempt
        (cfg attempt hattempt .header0
          (Tape.input
            (StructuredConstructionTargets.stageAttemptFramedStructuredInputBits
              i.C))
          Tape.blank Tape.blank)
        (cfg attempt hattempt .halt (tape0 i) (tape1 i)
          (CommonGround.ControllerInvocation.StageAttemptFramedOutputTape
            i.C i.result)) := by
    intro i
    exact Classical.choose_spec (Classical.choose_spec (forwardExists i))
  let lowered := fun i :
      StructuredConstructionTargets.StageAttemptFramedStructuredIndex attempt =>
    encodedGuardedStructured3Tapes
      (tape0 i) (tape1 i)
      (StructuredConstructionTargets.stageAttemptFramedStructuredOutputTape i)
  have hforward :
      forall i :
          StructuredConstructionTargets.StageAttemptFramedStructuredIndex
            attempt,
        (lowerStructured3Description (coreD attempt hattempt)).HaltsFromTapeEquiv
          (StructuredConstructionTargets.stageAttemptFramedStructuredInitializedTape
            i.C)
          (lowered i) := by
    intro i
    rcases (hleads i).to_runConfig with ⟨j, hrun⟩
    have hhalts :
        (coreD attempt hattempt).HaltsWithTapes
          (cfg attempt hattempt .header0
            (Tape.input
              (StructuredConstructionTargets.stageAttemptFramedStructuredInputBits
                i.C))
            Tape.blank Tape.blank)
          [tape0 i, tape1 i,
            StructuredConstructionTargets.stageAttemptFramedStructuredOutputTape
              i] := by
      refine ⟨j, ?_⟩
      change
        (coreD attempt hattempt).runConfig j
            (cfg attempt hattempt .header0
              (Tape.input
                (StructuredConstructionTargets.stageAttemptFramedStructuredInputBits
                  i.C))
              Tape.blank Tape.blank) =
          cfg attempt hattempt .halt (tape0 i) (tape1 i)
            (StructuredConstructionTargets.stageAttemptFramedStructuredOutputTape
              i)
      simpa [StructuredConstructionTargets.stageAttemptFramedStructuredOutputTape]
        using hrun
    have hlowered :=
      lowerStructured3Description_haltsFromConfigWithTapes
        (table attempt hattempt).description_wellFormed
        (table attempt hattempt).description_haltTransitionFree
        (table attempt hattempt).description_supportsReadWriteRows3
        (c := cfg attempt hattempt .header0
          (Tape.input
            (StructuredConstructionTargets.stageAttemptFramedStructuredInputBits
              i.C))
          Tape.blank Tape.blank)
        (tapes := [tape0 i, tape1 i,
          StructuredConstructionTargets.stageAttemptFramedStructuredOutputTape
            i])
        rfl rfl hhalts
    change
      (lowerStructured3Description
        (table attempt hattempt).description).HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes
          [Tape.input
            (StructuredConstructionTargets.stageAttemptFramedStructuredInputBits
              i.C), Tape.blank, Tape.blank])
        (encodedGuardedStructuredTapes
          [tape0 i, tape1 i,
            StructuredConstructionTargets.stageAttemptFramedStructuredOutputTape
              i])
    exact hlowered
  have hclosed :
      forall C : DovetailControllerLayout, forall T : Tape Bool,
        (lowerStructured3Description (coreD attempt hattempt)).HaltsFromTape
            (StructuredConstructionTargets.stageAttemptFramedStructuredInitializedTape
              C) T ->
          exists i :
              StructuredConstructionTargets.StageAttemptFramedStructuredIndex
                attempt,
            C = i.C ∧ Tape.Equiv T (lowered i) := by
    intro C T hhalt
    have hlogical := structured_halt_of_lower_coreD_halt
      attempt hattempt
      (Tape.input
        (StructuredConstructionTargets.stageAttemptFramedStructuredInputBits C))
      Tape.blank Tape.blank T (by
        change
          (lowerStructured3Description
            (table attempt hattempt).description).HaltsFromTape
            (encodedGuardedStructuredTapes
              [Tape.input
                (StructuredConstructionTargets.stageAttemptFramedStructuredInputBits
                  C), Tape.blank, Tape.blank]) T at hhalt
        exact hhalt)
    rcases hrecover C hlogical with ⟨i, hiC⟩
    subst C
    refine ⟨i, rfl, ?_⟩
    have hready :
        (lowerStructured3Description
          (coreD attempt hattempt)).SubroutineReady :=
      lowerStructured3Description_subroutineReady
        (table attempt hattempt).description_wellFormed
        (table attempt hattempt).description_supportsReadWriteRows3
    exact
      StructuredConstructionTargets.haltsFromTape_equiv_target_of_forward
        hready hhalt (hforward i)
  refine ⟨{
    tape0 := tape0
    tape1 := tape1
    components := {
      core := coreD attempt hattempt
      coreWellFormed := (table attempt hattempt).description_wellFormed
      coreHaltTransitionFree :=
        (table attempt hattempt).description_haltTransitionFree
      coreSupportsRows :=
        (table attempt hattempt).description_supportsReadWriteRows3
      loweredShape := by intro i; rfl
      semanticCore := {
        forward := hforward
        closedIndex := hclosed } } }⟩

theorem stageAttemptFramedStructuredSemanticCoreConstruction
    (attempt : MachineDescription) (hattempt : attempt.SubroutineReady) :
    StructuredConstructionTargets.StageAttemptFramedStructuredSemanticCoreConstruction
      attempt :=
  stageAttemptFramedStructuredSemanticCoreConstruction_of_logicalClosed
    attempt hattempt (logicalHaltRecoversIndex attempt hattempt)

end FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore
