import FoC.Computability.Compiler.ClosedCfg.ProjTail.SelectedFootprintCompactionShape

set_option doc.verso true

/-!
# Live selected-footprint ingress end marker

The live #15 source starts on two blank right-boundary cells.  This first
ingress phase replaces those cells by a nonblank two-cell marker and lands on
the final pair-encoded payload cell.  Later phases can therefore traverse the
blank-inclusive pair stream and return to a detectable right edge.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace LiveIngress
namespace EndMarker

def description : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition 0 none (some true) Direction.left 1
    , transition 1 none (some true) Direction.left 2 ]

theorem description_wellFormed : description.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := description.transitions)
      (stateCount := description.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := description.transitions)
      (by decide)

theorem description_haltTransitionFree :
    description.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := description.transitions)
    (state := description.halt)
    (by decide)

theorem description_subroutineReady : description.SubroutineReady :=
  ⟨description_wellFormed, description_haltTransitionFree⟩

def sourceTape (current : Option Bool)
    (rest : List (Option Bool)) : Tape Bool :=
  { left := none :: current :: rest
    head := none
    right := [] }

def targetTape (current : Option Bool)
    (rest : List (Option Bool)) : Tape Bool :=
  { left := rest
    head := current
    right := [some true, some true] }

def markedTape (T : Tape Bool) : Tape Bool :=
  Tape.move Direction.left
    (Tape.write (some true)
      (Tape.move Direction.left (Tape.write (some true) T)))

theorem markedTape_sourceTape (current : Option Bool)
    (rest : List (Option Bool)) :
    markedTape (sourceTape current rest) = targetTape current rest := by
  simp [markedTape, sourceTape, targetTape, Tape.write, Tape.move,
    Tape.moveLeft]

theorem run (current : Option Bool) (rest : List (Option Bool)) :
    description.runConfig 2
        { state := description.start
          tape := sourceTape current rest } =
      { state := description.halt
        tape := targetTape current rest } := by
  simp [description, sourceTape, targetTape, runConfig, stepConfig,
    lookupTransition, Matches, transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft]

theorem haltsFromTape (current : Option Bool)
    (rest : List (Option Bool)) :
    description.HaltsFromTape
      (sourceTape current rest) (targetTape current rest) := by
  refine ⟨2, ?_⟩
  have hrun := run current rest
  exact ⟨congrArg (fun c => c.state) hrun,
    congrArg (fun c => c.tape) hrun⟩

theorem liveSourceTape_shape (useAccept : Bool) (L : DovetailLayout) :
    exists rest : List (Option Bool),
      countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape
          useAccept L =
        sourceTape none rest := by
  rw [countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape_eq_rightEndCompactionSourceTape]
  rcases parsedLayoutBits_eq_false_false_tail L with ⟨tail, hbits⟩
  simp [rightEndCompactionSourceTape,
    countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorLeftCells,
    sourceTape, tapeAtCells, List.reverse_append]
  rw [hbits]
  simp [selectedSegmentLogicalTapeDecoderDensifierFootprintCells,
    List.reverse_append]
  simp [selectedSegmentLogicalTapeDecoderCellCells]

theorem haltsFrom_liveSource (useAccept : Bool) (L : DovetailLayout) :
    description.HaltsFromTape
      (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape
        useAccept L)
      (markedTape
        (countWindowPostFieldDecodedPrefixSelectedSegmentFootprintCompactorSourceTape
          useAccept L)) := by
  rcases liveSourceTape_shape useAccept L with ⟨rest, hsource⟩
  rw [hsource]
  rw [markedTape_sourceTape]
  exact haltsFromTape none rest

end EndMarker
end LiveIngress
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
