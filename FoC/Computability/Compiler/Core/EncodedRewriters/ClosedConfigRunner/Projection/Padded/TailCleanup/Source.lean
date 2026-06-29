import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.Spec

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

def sourceBits (L : DovetailLayout) : Word Bool :=
  List.append
    (SelectedProjectionTailProjector.outputPrefixBits L)
    (SelectedProjectionTailProjector.sourceFieldBits L)

def sourceRewindDescription : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1
    , transition 1 (some false) (some false) Direction.left 1
    , transition 1 (some true) (some true) Direction.left 1
    , transition 1 none none Direction.right 2 ]

def rewindSourceTape (bits : Word Bool) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    (bits.reverse.map some) []

def rewindTargetTape (bits : Word Bool) : Tape Bool :=
  DovetailInitialLayoutInitializer.tapeAtCells
    [none] (List.append (bits.map some) [none])

theorem sourceRewindDescription_wellFormed :
    sourceRewindDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := sourceRewindDescription.transitions)
      (stateCount := sourceRewindDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := sourceRewindDescription.transitions)
      (by decide)

theorem sourceRewindDescription_haltTransitionFree :
    sourceRewindDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := sourceRewindDescription.transitions)
    (state := sourceRewindDescription.halt)
    (by decide)

theorem sourceRewindDescription_subroutineReady :
    sourceRewindDescription.SubroutineReady :=
  ⟨sourceRewindDescription_wellFormed,
    sourceRewindDescription_haltTransitionFree⟩

theorem sourceRewindDescription_run_scan
    (leftBits : Word Bool) (current : Bool)
    (rightCells : List (Option Bool)) :
    sourceRewindDescription.runConfig (leftBits.length + 1)
        { state := 1
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (leftBits.map some)
              (some current :: rightCells) } =
      { state := 1
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells []
            (none ::
              List.append
                ((List.append leftBits.reverse [current]).map some)
                rightCells) } := by
  induction leftBits generalizing current rightCells with
  | nil =>
      cases current <;>
        simp [sourceRewindDescription,
          DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.move, Tape.moveLeft, Tape.write]
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        omega]
      rw [runConfig_add]
      have hstep :
          sourceRewindDescription.runConfig 1
              { state := 1
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    ((next :: rest).map some)
                    (some current :: rightCells) } =
            { state := 1
              tape :=
                DovetailInitialLayoutInitializer.tapeAtCells
                  (rest.map some)
                  (some next :: some current :: rightCells) } := by
        cases current <;>
          simp [sourceRewindDescription,
            DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstep]
      simpa [List.append_assoc] using
        ih next (some current :: rightCells)

theorem sourceRewindDescription_step_finish
    (bits : Word Bool) :
    sourceRewindDescription.runConfig 1
        { state := 1
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells []
              (none :: List.append (bits.map some) [none]) } =
      { state := sourceRewindDescription.halt
        tape := rewindTargetTape bits } := by
  cases bits with
  | nil =>
      simp [sourceRewindDescription, rewindTargetTape,
        DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
        stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.move, Tape.moveRight, Tape.write]
  | cons bit rest =>
      cases bit <;>
        simp [sourceRewindDescription, rewindTargetTape,
          DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
          stepConfig, lookupTransition, Matches, transition,
          Tape.read, Tape.move, Tape.moveRight, Tape.write]

theorem sourceRewindDescription_run_from_leftStack
    (leftStack : Word Bool) :
    sourceRewindDescription.runConfig (leftStack.length + 2)
        { state := sourceRewindDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (leftStack.map some) [] } =
      { state := sourceRewindDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells [none]
            (List.append (leftStack.reverse.map some) [none]) } := by
  cases leftStack with
  | nil =>
      simp [sourceRewindDescription, DovetailInitialLayoutInitializer.tapeAtCells,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight, Tape.write]
  | cons current rest =>
      rw [show (current :: rest).length + 2 =
        1 + ((rest.length + 1) + 1) by
        simp
        omega]
      rw [runConfig_add]
      have hstart :
          sourceRewindDescription.runConfig 1
              { state := sourceRewindDescription.start
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    ((current :: rest).map some) [] } =
            { state := 1
              tape :=
                DovetailInitialLayoutInitializer.tapeAtCells
                  (rest.map some) [some current, none] } := by
        cases current <;>
          simp [sourceRewindDescription,
            DovetailInitialLayoutInitializer.tapeAtCells, runConfig,
            stepConfig, lookupTransition, Matches, transition,
            Tape.read, Tape.move, Tape.moveLeft, Tape.write]
      rw [hstart]
      rw [show (rest.length + 1) + 1 = (rest.length + 1) + 1 by rfl]
      rw [runConfig_add]
      rw [sourceRewindDescription_run_scan rest current [none]]
      simpa [rewindTargetTape, List.map_append, List.append_assoc] using
        sourceRewindDescription_step_finish
          (List.append rest.reverse [current])

theorem sourceRewindDescription_run
    (bits : Word Bool) :
    sourceRewindDescription.runConfig (bits.length + 2)
        { state := sourceRewindDescription.start
          tape := rewindSourceTape bits } =
      { state := sourceRewindDescription.halt
        tape := rewindTargetTape bits } := by
  simpa [rewindSourceTape, rewindTargetTape] using
    sourceRewindDescription_run_from_leftStack bits.reverse

theorem sourceRewindDescription_haltsFromTape
    (bits : Word Bool) :
    sourceRewindDescription.HaltsFromTape
      (rewindSourceTape bits) (rewindTargetTape bits) := by
  refine ⟨bits.length + 2, ?_⟩
  constructor
  · rw [sourceRewindDescription_run]
  · rw [sourceRewindDescription_run]

theorem sourceScannerRightHandoffTape_eq_rewindSourceTape
    (L : DovetailLayout) :
    SelectedProjectionTailProjector.sourceScannerRightHandoffTape L
        ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
          some) =
      rewindSourceTape (sourceBits L) := by
  rw [SelectedProjectionTailProjector.sourceScannerRightHandoffTape_eq,
    rewindSourceTape, sourceBits,
    SelectedProjectionTailProjector.sourceFieldBits]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev_map_some_withBase
      L.acceptConfig
      (List.append
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage).reverse.map some)
        ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
          some))]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev_map_some_withBase
      L.rejectConfig]
  have hacceptBits :
      (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev
          L.acceptConfig).map some =
        (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          L.acceptConfig []).reverse.map some := by
    have h :=
      congrArg (fun xs : Word Bool => xs.reverse.map some)
        (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev_reverse
          L.acceptConfig)
    simpa using h
  have hrejectBits :
      (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev
          L.rejectConfig).map some =
        (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          L.rejectConfig []).reverse.map some := by
    have h :=
      congrArg (fun xs : Word Bool => xs.reverse.map some)
        (CanonicalLayouts.DovetailLayoutScanner.configurationRestoredBitsRev_reverse
          L.rejectConfig)
    simpa using h
  rw [hacceptBits, hrejectBits]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      L.rejectConfig
      (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits L.acceptHit
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.rejectHit []))]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      L.acceptConfig
      (List.append
        (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          L.rejectConfig [])
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits L.acceptHit
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            L.rejectHit [])))]
  simp [CanonicalLayouts.DovetailLayoutScanner.finalHitFlagsRestoredLeftWithBase,
    CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    List.map_append, List.map_reverse, List.reverse_append,
    List.append_assoc]

theorem sourceRewindDescription_haltsFrom_sourceScannerRightHandoffTape
    (L : DovetailLayout) :
    sourceRewindDescription.HaltsFromTape
      (SelectedProjectionTailProjector.sourceScannerRightHandoffTape L
        ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
          some))
      (rewindTargetTape (sourceBits L)) := by
  rw [sourceScannerRightHandoffTape_eq_rewindSourceTape L]
  exact sourceRewindDescription_haltsFromTape (sourceBits L)

def sourceRightEndDescription : MachineDescription where
  stateCount := 2
  start := 0
  halt := 1
  transitions :=
    [ transition 0 (some false) (some false) Direction.right 0
    , transition 0 (some true) (some true) Direction.right 0
    , transition 0 none none Direction.left 1 ]

def sourceRightEndTape (bits : Word Bool) : Tape Bool :=
  Tape.move Direction.left
    (DovetailInitialLayoutInitializer.tapeAtCells
      (List.append (bits.reverse.map some) [none]) [none])

theorem sourceRightEndDescription_wellFormed :
    sourceRightEndDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := sourceRightEndDescription.transitions)
      (stateCount := sourceRightEndDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := sourceRightEndDescription.transitions)
      (by decide)

theorem sourceRightEndDescription_haltTransitionFree :
    sourceRightEndDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := sourceRightEndDescription.transitions)
    (state := sourceRightEndDescription.halt)
    (by decide)

theorem sourceRightEndDescription_subroutineReady :
    sourceRightEndDescription.SubroutineReady :=
  ⟨sourceRightEndDescription_wellFormed,
    sourceRightEndDescription_haltTransitionFree⟩

theorem sourceRightEndDescription_step_bit
    (left right : List (Option Bool)) (bit : Bool) :
    sourceRightEndDescription.runConfig 1
        { state := sourceRightEndDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              left (some bit :: right) } =
      { state := sourceRightEndDescription.start
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (some bit :: left) right } := by
  cases bit <;> cases right <;>
    simp [sourceRightEndDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem sourceRightEndDescription_step_finish
    (left : List (Option Bool)) :
    sourceRightEndDescription.runConfig 1
        { state := sourceRightEndDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              left [none] } =
      { state := sourceRightEndDescription.halt
        tape :=
          Tape.move Direction.left
            (DovetailInitialLayoutInitializer.tapeAtCells left [none]) } := by
  cases left <;>
    simp [sourceRightEndDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

theorem sourceRightEndDescription_run_scan
    (bits : Word Bool) (left : List (Option Bool)) :
    sourceRightEndDescription.runConfig bits.length
        { state := sourceRightEndDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              left (List.append (bits.map some) [none]) } =
      { state := sourceRightEndDescription.start
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (List.append (bits.reverse.map some) left) [none] } := by
  induction bits generalizing left with
  | nil =>
      simp [runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [runConfig_add]
      change
        sourceRightEndDescription.runConfig rest.length
            (sourceRightEndDescription.runConfig 1
              { state := sourceRightEndDescription.start
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    left
                    (some bit :: List.append (rest.map some) [none]) }) =
          { state := sourceRightEndDescription.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                [none] }
      rw [sourceRightEndDescription_step_bit left
        (List.append (rest.map some) [none]) bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

theorem sourceRightEndDescription_run
    (bits : Word Bool) :
    sourceRightEndDescription.runConfig (bits.length + 1)
        { state := sourceRightEndDescription.start
          tape := rewindTargetTape bits } =
      { state := sourceRightEndDescription.halt
        tape := sourceRightEndTape bits } := by
  rw [rewindTargetTape]
  rw [runConfig_add]
  rw [sourceRightEndDescription_run_scan bits [none]]
  simpa [sourceRightEndTape, rewindTargetTape, List.append_assoc] using
    sourceRightEndDescription_step_finish
      (List.append (bits.reverse.map some) [none])

theorem sourceRightEndDescription_haltsFromTape
    (bits : Word Bool) :
    sourceRightEndDescription.HaltsFromTape
      (rewindTargetTape bits) (sourceRightEndTape bits) := by
  refine ⟨bits.length + 1, ?_⟩
  constructor
  · rw [sourceRightEndDescription_run]
  · rw [sourceRightEndDescription_run]

theorem sourceRightEndDescription_haltsFrom_rewindTarget_sourceBits
    (L : DovetailLayout) :
    sourceRightEndDescription.HaltsFromTape
      (rewindTargetTape (sourceBits L))
      (sourceRightEndTape (sourceBits L)) :=
  sourceRightEndDescription_haltsFromTape (sourceBits L)

theorem tapeAtCells_move_left_move_right_cons_cons
    (left : List (Option Bool)) (head next : Option Bool)
    (right : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (DovetailInitialLayoutInitializer.tapeAtCells left
            (head :: next :: right))) =
      DovetailInitialLayoutInitializer.tapeAtCells left
        (head :: next :: right) := by
  simp [DovetailInitialLayoutInitializer.tapeAtCells, Tape.move,
    Tape.moveLeft, Tape.moveRight]

theorem rewindTargetTape_sourceBits_move_left_move_right
    (L : DovetailLayout) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (rewindTargetTape (sourceBits L))) =
      rewindTargetTape (sourceBits L) := by
  simp [rewindTargetTape, sourceBits,
    SelectedProjectionTailProjector.outputPrefixBits,
    encodeCodeSymbolAsInput,
    DovetailInitialLayoutInitializer.tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem tape_move_left_tapeAtCells_single_move_left_move_right
    (left : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (Tape.move Direction.left
            (DovetailInitialLayoutInitializer.tapeAtCells left [none]))) =
      Tape.move Direction.left
        (DovetailInitialLayoutInitializer.tapeAtCells left [none]) := by
  cases left with
  | nil =>
      simp [DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons cell rest =>
      simp [DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.move, Tape.moveLeft, Tape.moveRight]

theorem sourceRightEndTape_move_left_move_right
    (bits : Word Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right (sourceRightEndTape bits)) =
      sourceRightEndTape bits := by
  simp [sourceRightEndTape,
    tape_move_left_tapeAtCells_single_move_left_move_right]

def sourceRightEndLeftFields
    (L : DovetailLayout) : List (Option Bool) :=
  List.append
    ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
      L.rejectHit []).reverse.map some)
    (List.append
      ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
        L.acceptHit []).reverse.map some)
      (List.append
        ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          L.rejectConfig []).reverse.map some)
        (List.append
          ((CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
            L.acceptConfig []).reverse.map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              L.stage).reverse.map some)
            (List.append
              ((SelectedProjectionTailProjector.outputPrefixBits L).reverse.map
                some)
              [none])))))

theorem sourceRightEndTape_sourceBits_eq_fields
    (L : DovetailLayout) :
    sourceRightEndTape (sourceBits L) =
      Tape.move Direction.left
        (DovetailInitialLayoutInitializer.tapeAtCells
          (sourceRightEndLeftFields L) [none]) := by
  rw [sourceRightEndTape, sourceBits,
    SelectedProjectionTailProjector.sourceFieldBits,
    sourceRightEndLeftFields]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      L.rejectConfig
      (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits L.acceptHit
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
          L.rejectHit []))]
  rw [←
    CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits_append_nil
      L.acceptConfig
      (List.append
        (CanonicalLayouts.DovetailLayoutScanner.configurationFieldBits
          L.rejectConfig [])
        (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits L.acceptHit
          (CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            L.rejectHit [])))]
  simp [CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
    CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
    List.map_append, List.reverse_append, List.append_assoc]


end SelectedProjectionPaddedTailCleanup

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
