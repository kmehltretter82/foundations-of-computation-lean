import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Padded.TailCleanup.Source

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup

def skipOneBoolFieldLeftDescription : MachineDescription where
  stateCount := 5
  start := 0
  halt := 4
  transitions :=
    [ transition 0 (some false) (some false) Direction.left 1
    , transition 0 (some true) (some true) Direction.left 1
    , transition 1 (some false) (some false) Direction.left 2
    , transition 1 (some true) (some true) Direction.left 2
    , transition 2 (some false) (some false) Direction.left 3
    , transition 2 (some true) (some true) Direction.left 3
    , transition 3 (some false) (some false) Direction.left 4
    , transition 3 (some true) (some true) Direction.left 4 ]

theorem skipOneBoolFieldLeftDescription_wellFormed :
    skipOneBoolFieldLeftDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := skipOneBoolFieldLeftDescription.transitions)
      (stateCount := skipOneBoolFieldLeftDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := skipOneBoolFieldLeftDescription.transitions)
      (by decide)

theorem skipOneBoolFieldLeftDescription_haltTransitionFree :
    skipOneBoolFieldLeftDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := skipOneBoolFieldLeftDescription.transitions)
    (state := skipOneBoolFieldLeftDescription.halt)
    (by decide)

theorem skipOneBoolFieldLeftDescription_subroutineReady :
    skipOneBoolFieldLeftDescription.SubroutineReady :=
  ⟨skipOneBoolFieldLeftDescription_wellFormed,
    skipOneBoolFieldLeftDescription_haltTransitionFree⟩

theorem skipOneBoolFieldLeftDescription_run
    (b0 b1 b2 b3 b4 : Bool)
    (left right : List (Option Bool)) :
    skipOneBoolFieldLeftDescription.runConfig 4
        { state := skipOneBoolFieldLeftDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (some b1 :: some b2 :: some b3 :: some b4 :: left)
              (some b0 :: right) } =
      { state := skipOneBoolFieldLeftDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            left
            (some b4 :: some b3 :: some b2 :: some b1 ::
              some b0 :: right) } := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    simp [skipOneBoolFieldLeftDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

def selectedHitRightEndTape
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  if useAccept then
    Tape.move Direction.left
      (DovetailInitialLayoutInitializer.tapeAtCells
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
        (List.append
          ((CanonicalLayouts.DovetailLayoutScanner.boolFieldBits
            L.rejectHit []).map some)
          [none]))
  else
    sourceRightEndTape (sourceBits L)

def selectedHitPositionDescription
    (useAccept : Bool) : MachineDescription :=
  if useAccept then
    skipOneBoolFieldLeftDescription
  else
    ExactIdentityDescription

theorem selectedHitPositionDescription_subroutineReady
    (useAccept : Bool) :
    (selectedHitPositionDescription useAccept).SubroutineReady := by
  cases useAccept
  · simpa [selectedHitPositionDescription] using
      ⟨exactIdentityDescription_wellFormed,
        exactIdentityDescription_haltTransitionFree⟩
  · simpa [selectedHitPositionDescription] using
      skipOneBoolFieldLeftDescription_subroutineReady

theorem selectedHitPositionDescription_haltsFromTape
    (useAccept : Bool) (L : DovetailLayout) :
    (selectedHitPositionDescription useAccept).HaltsFromTape
      (sourceRightEndTape (sourceBits L))
      (selectedHitRightEndTape useAccept L) := by
  cases useAccept
  · refine ⟨0, ?_⟩
    constructor <;>
      simp [selectedHitPositionDescription, selectedHitRightEndTape,
        ExactIdentityDescription, runConfig]
  · refine ⟨4, ?_⟩
    constructor <;>
      by_cases hreject : L.rejectHit <;>
      by_cases haccept : L.acceptHit <;>
        simp [selectedHitPositionDescription, selectedHitRightEndTape,
          sourceRightEndTape_sourceBits_eq_fields,
          sourceRightEndLeftFields,
          skipOneBoolFieldLeftDescription,
          hreject, haccept,
          CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
          CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
          encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
          DovetailInitialLayoutInitializer.tapeAtCells,
          runConfig, stepConfig, lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft]

def acceptHitFromRewindDescription : MachineDescription where
  stateCount := 6
  start := 0
  halt := 5
  transitions :=
    [ transition 0 (some false) (some false) Direction.right 0
    , transition 0 (some true) (some true) Direction.right 0
    , transition 0 none none Direction.left 1
    , transition 1 (some false) (some false) Direction.left 2
    , transition 1 (some true) (some true) Direction.left 2
    , transition 2 (some false) (some false) Direction.left 3
    , transition 2 (some true) (some true) Direction.left 3
    , transition 3 (some false) (some false) Direction.left 4
    , transition 3 (some true) (some true) Direction.left 4
    , transition 4 (some false) (some false) Direction.left 5
    , transition 4 (some true) (some true) Direction.left 5 ]

theorem acceptHitFromRewindDescription_wellFormed :
    acceptHitFromRewindDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := acceptHitFromRewindDescription.transitions)
      (stateCount := acceptHitFromRewindDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := acceptHitFromRewindDescription.transitions)
      (by decide)

theorem acceptHitFromRewindDescription_haltTransitionFree :
    acceptHitFromRewindDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := acceptHitFromRewindDescription.transitions)
    (state := acceptHitFromRewindDescription.halt)
    (by decide)

theorem acceptHitFromRewindDescription_subroutineReady :
    acceptHitFromRewindDescription.SubroutineReady :=
  ⟨acceptHitFromRewindDescription_wellFormed,
    acceptHitFromRewindDescription_haltTransitionFree⟩

theorem acceptHitFromRewindDescription_step_scan_bit
    (left right : List (Option Bool)) (bit : Bool) :
    acceptHitFromRewindDescription.runConfig 1
        { state := acceptHitFromRewindDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              left (some bit :: right) } =
      { state := acceptHitFromRewindDescription.start
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            (some bit :: left) right } := by
  cases bit <;> cases right <;>
    simp [acceptHitFromRewindDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem acceptHitFromRewindDescription_step_scan_finish
    (left : List (Option Bool)) :
    acceptHitFromRewindDescription.runConfig 1
        { state := acceptHitFromRewindDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              left [none] } =
      { state := 1
        tape :=
          Tape.move Direction.left
            (DovetailInitialLayoutInitializer.tapeAtCells left [none]) } := by
  cases left <;>
    simp [acceptHitFromRewindDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

theorem acceptHitFromRewindDescription_run_scan
    (bits : Word Bool) (left : List (Option Bool)) :
    acceptHitFromRewindDescription.runConfig bits.length
        { state := acceptHitFromRewindDescription.start
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              left (List.append (bits.map some) [none]) } =
      { state := acceptHitFromRewindDescription.start
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
        acceptHitFromRewindDescription.runConfig rest.length
            (acceptHitFromRewindDescription.runConfig 1
              { state := acceptHitFromRewindDescription.start
                tape :=
                  DovetailInitialLayoutInitializer.tapeAtCells
                    left
                    (some bit :: List.append (rest.map some) [none]) }) =
          { state := acceptHitFromRewindDescription.start
            tape :=
              DovetailInitialLayoutInitializer.tapeAtCells
                (List.append ((bit :: rest).reverse.map some) left)
                [none] }
      rw [acceptHitFromRewindDescription_step_scan_bit left
        (List.append (rest.map some) [none]) bit]
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some bit :: left)

theorem acceptHitFromRewindDescription_run_to_rejectHit
    (bits : Word Bool) :
    acceptHitFromRewindDescription.runConfig (bits.length + 1)
        { state := acceptHitFromRewindDescription.start
          tape := rewindTargetTape bits } =
      { state := 1
        tape := sourceRightEndTape bits } := by
  rw [rewindTargetTape]
  rw [runConfig_add]
  rw [acceptHitFromRewindDescription_run_scan bits [none]]
  simpa [sourceRightEndTape, rewindTargetTape, List.append_assoc] using
    acceptHitFromRewindDescription_step_scan_finish
      (List.append (bits.reverse.map some) [none])

theorem acceptHitFromRewindDescription_run_skip_rejectHit
    (b0 b1 b2 b3 b4 : Bool)
    (left right : List (Option Bool)) :
    acceptHitFromRewindDescription.runConfig 4
        { state := 1
          tape :=
            DovetailInitialLayoutInitializer.tapeAtCells
              (some b1 :: some b2 :: some b3 :: some b4 :: left)
              (some b0 :: right) } =
      { state := acceptHitFromRewindDescription.halt
        tape :=
          DovetailInitialLayoutInitializer.tapeAtCells
            left
            (some b4 :: some b3 :: some b2 :: some b1 ::
              some b0 :: right) } := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    simp [acceptHitFromRewindDescription,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

theorem acceptHitFromRewindDescription_run_to_selectedHit
    (L : DovetailLayout) :
    acceptHitFromRewindDescription.runConfig
        ((sourceBits L).length + 5)
        { state := acceptHitFromRewindDescription.start
          tape := rewindTargetTape (sourceBits L) } =
      { state := acceptHitFromRewindDescription.halt
        tape := selectedHitRightEndTape true L } := by
  rw [show (sourceBits L).length + 5 =
      ((sourceBits L).length + 1) + 4 by omega]
  rw [runConfig_add]
  rw [acceptHitFromRewindDescription_run_to_rejectHit]
  by_cases hreject : L.rejectHit <;>
  by_cases haccept : L.acceptHit <;>
    simp [selectedHitRightEndTape,
      sourceRightEndTape_sourceBits_eq_fields,
      sourceRightEndLeftFields,
      acceptHitFromRewindDescription,
      hreject, haccept,
      CanonicalLayouts.DovetailLayoutScanner.boolFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellFieldBits,
      CanonicalLayouts.DovetailLayoutScanner.cellCodeBits,
      encodeCell, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      DovetailInitialLayoutInitializer.tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft]

theorem acceptHitFromRewindDescription_haltsFrom_rewindTarget_sourceBits
    (L : DovetailLayout) :
    acceptHitFromRewindDescription.HaltsFromTape
      (rewindTargetTape (sourceBits L))
      (selectedHitRightEndTape true L) := by
  refine ⟨(sourceBits L).length + 5, ?_⟩
  constructor <;>
    rw [acceptHitFromRewindDescription_run_to_selectedHit]

def selectedHitFromRewindDescription
    (useAccept : Bool) : MachineDescription :=
  if useAccept then
    acceptHitFromRewindDescription
  else
    sourceRightEndDescription

theorem selectedHitFromRewindDescription_subroutineReady
    (useAccept : Bool) :
    (selectedHitFromRewindDescription useAccept).SubroutineReady := by
  cases useAccept
  · simpa [selectedHitFromRewindDescription] using
      sourceRightEndDescription_subroutineReady
  · simpa [selectedHitFromRewindDescription] using
      acceptHitFromRewindDescription_subroutineReady

theorem selectedHitFromRewindDescription_haltsFrom_rewindTarget_sourceBits
    (useAccept : Bool) (L : DovetailLayout) :
    (selectedHitFromRewindDescription useAccept).HaltsFromTape
      (rewindTargetTape (sourceBits L))
      (selectedHitRightEndTape useAccept L) := by
  cases useAccept
  · simpa [selectedHitFromRewindDescription, selectedHitRightEndTape] using
      sourceRightEndDescription_haltsFrom_rewindTarget_sourceBits L
  · simpa [selectedHitFromRewindDescription] using
      acceptHitFromRewindDescription_haltsFrom_rewindTarget_sourceBits L


end SelectedProjectionPaddedTailCleanup

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
