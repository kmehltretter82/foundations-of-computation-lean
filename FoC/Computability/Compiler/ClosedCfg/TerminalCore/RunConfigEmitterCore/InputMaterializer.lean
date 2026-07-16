import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind
import FoC.Computability.Compiler.Core.CommonGround.Identity
import FoC.Computability.Compiler.Core.CommonGround.SeqComposition
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.OptionCellExpandAppendImpl

set_option doc.verso true

/-!
# Right-end-left structured input materializer

The terminal run-config emitter starts on the final bit of a known nonempty
simulator layout.  This module gives a dependency-light route from that boundary to the
canonical guarded three-logical-tape embedding.  It uses the shared right-edge
rewinder and exact option-cell expander directly; no closed-layout recognizer
or structured output projector is needed on this forward-only boundary.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace InputMaterializer

open CommonGround.FiniteTransducers

/-- Generic tape shape with the head on the last bit, an explicit blank on
each side, and no additional visible right padding. -/
def rightEndLeftSourceTape (bits : Word Bool) : Tape Bool :=
  Tape.move Direction.left
    (tapeAtCells (List.append (bits.reverse.map some) [none]) [none])

/-- Word-start tape produced by the dependency-light right-edge rewinder. -/
def wordStartTape (bits : Word Bool) : Tape Bool :=
  rightEdgeRewindTargetTape bits []

theorem wordStartTape_eq (bits : Word Bool) :
    wordStartTape bits =
      tapeAtCells [none] (List.append (bits.map some) [none]) := by
  rfl

/-- The explicit boundary blanks differ from the ordinary input tape only by
proof-transparent window padding. -/
theorem wordStartTape_equiv_input (bits : Word Bool) :
    Tape.Equiv (wordStartTape bits) (Tape.input bits) := by
  rw [wordStartTape_eq]
  cases bits with
  | nil =>
      refine ⟨rfl, rfl, ?_⟩
      rfl
  | cons bit rest =>
      refine ⟨rfl, rfl, ?_⟩
      simpa [tapeAtCells, Tape.input] using
        dropTrailingNone_append_none (rest.map some)

/-- A nonempty right-end-left source is exactly the boundary form consumed by
the existing right-edge rewinder. -/
theorem rightEndLeftSourceTape_eq_lastBitBoundary
    (bits : Word Bool) (hbits : bits ≠ []) :
    exists pref : Word Bool, exists last : Bool,
      bits = List.append pref [last] ∧
        rightEndLeftSourceTape bits =
          tapeAtCells
            (List.append (pref.reverse.map some) [none])
            [some last, none] := by
  change List Bool at bits
  cases hrev : bits.reverse with
  | nil =>
      have : bits = [] := by
        simpa using congrArg List.reverse hrev
      contradiction
  | cons last prefixRev =>
      have hbitsEq : bits = List.append prefixRev.reverse [last] := by
        have := congrArg List.reverse hrev
        simpa using this
      refine ⟨prefixRev.reverse, last, hbitsEq, ?_⟩
      subst bits
      simp [rightEndLeftSourceTape, tapeAtCells, Tape.move, Tape.moveLeft]

/-- Exact generic rewind from the final source bit to the first source bit. -/
theorem rightEdgeRewindDescription_haltsFrom_rightEndLeft
    (bits : Word Bool) (hbits : bits ≠ []) :
    rightEdgeRewindDescription.HaltsFromTape
      (rightEndLeftSourceTape bits) (wordStartTape bits) := by
  rcases rightEndLeftSourceTape_eq_lastBitBoundary bits hbits with
    ⟨pref, last, hbitsEq, hsource⟩
  rw [hsource, wordStartTape, hbitsEq]
  simpa using
    rightEdgeRewindDescription_haltsFrom_lastBitBoundary
      pref.reverse last []

/-- Park the rewind result on its explicit left boundary so a following
sequential handoff can return exactly to the first bit. -/
def parkedRewindDescription : MachineDescription :=
  seqSubroutine rightEdgeRewindDescription ExactIdentityDescription
    Direction.left

theorem parkedRewindDescription_subroutineReady :
    parkedRewindDescription.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    rightEdgeRewindDescription_subroutineReady
    CommonGround.Identity.exactIdentityDescription_subroutineReady

theorem parkedRewindDescription_haltsFrom_rightEndLeft
    (bits : Word Bool) (hbits : bits ≠ []) :
    parkedRewindDescription.HaltsFromTape
      (rightEndLeftSourceTape bits)
      (Tape.move Direction.left (wordStartTape bits)) := by
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
      rightEdgeRewindDescription_subroutineReady
      CommonGround.Identity.exactIdentityDescription_subroutineReady
      (rightEdgeRewindDescription_haltsFrom_rightEndLeft bits hbits)
      rfl
      (CommonGround.Identity.exactIdentityDescription_haltsFromTape _)

theorem move_right_move_left_wordStartTape
    (bits : Word Bool) :
    Tape.move Direction.right (Tape.move Direction.left (wordStartTape bits)) =
      wordStartTape bits := by
  rw [wordStartTape_eq]
  cases bits with
  | nil =>
      simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]
  | cons bit rest =>
      cases bit <;> cases rest <;>
        simp [tapeAtCells, Tape.move, Tape.moveLeft, Tape.moveRight]

/-- Concrete composition that enters the guarded three-tape encoding from a
right-end-left Boolean word. -/
def description : MachineDescription :=
  seqSubroutine parkedRewindDescription
    StructuredConstructionTargets.optionCellExpandAppendDescription
    Direction.right

theorem description_subroutineReady : description.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    parkedRewindDescription_subroutineReady
    StructuredConstructionTargets.optionCellExpandAppendDescription_subroutineReady

/-- Forward materialization.  The target is exact for the canonical input
tape; the source-side explicit window blanks are transported transparently,
so the generic boundary honestly exposes tape equivalence. -/
theorem description_haltsFromTapeEquiv
    (bits : Word Bool) (hbits : bits ≠ []) :
    description.HaltsFromTapeEquiv
      (rightEndLeftSourceTape bits)
      (StructuredConstructionTargets.structured3InputEmbeddingEmitterTargetTape
        bits) := by
  have hemits :
      StructuredConstructionTargets.optionCellExpandAppendDescription.HaltsFromTape
        (Tape.input bits)
        (StructuredConstructionTargets.structured3InputEmbeddingEmitterTargetTape
          bits) := by
    unfold StructuredConstructionTargets.structured3InputEmbeddingEmitterTargetTape
    rw [←
      StructuredConstructionTargets.optionCellExpandAppendTargetCells_eq_structured3
        bits]
    exact
      StructuredConstructionTargets.optionCellExpandAppendDescription_runSpec.forward
        bits
  have hemitsEquiv :
      StructuredConstructionTargets.optionCellExpandAppendDescription.HaltsFromTapeEquiv
        (wordStartTape bits)
        (StructuredConstructionTargets.structured3InputEmbeddingEmitterTargetTape
          bits) := by
    exact
      HaltsFromTapeEquiv_of_input_equiv
        (Tape.Equiv.symm (wordStartTape_equiv_input bits)) hemits
  unfold description
  exact
    CommonGround.SeqComposition.seqSubroutine_haltsFromTapeEquiv_of_haltsFromTape_eq
      parkedRewindDescription_subroutineReady
      StructuredConstructionTargets.optionCellExpandAppendDescription_subroutineReady
      (parkedRewindDescription_haltsFrom_rightEndLeft bits hbits)
      (move_right_move_left_wordStartTape bits)
      hemitsEquiv

end InputMaterializer
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
