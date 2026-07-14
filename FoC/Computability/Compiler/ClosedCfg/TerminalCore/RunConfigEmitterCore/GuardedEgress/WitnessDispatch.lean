import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.SuffixParser
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.WitnessStage

set_option doc.verso true

/-!
# Metadata-witness parser/normalizer dispatch

The suffix parser and witness normalizer use overlapping local state ranges.
This module keeps the parser in its original block, copies the normalizer above
it, and connects each of the four parser exits to the matching normalizer entry
through a distinct right-left blank-head bounce.  The bounce changes only
finite control up to tape equivalence.
-/

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.MetadataWitnessDispatch

open Languages MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.StaticDispatcherReaderAssembly

def normalizerOffset : Nat :=
  MetadataWitnessSuffixParser.description.stateCount

def normalizerBlock : MachineDescription :=
  MachineDescription.offsetDescription normalizerOffset
    MetadataWitnessStage.Normalizer.description

/-- Parser exit selected by the witness branch and final hit bit. -/
def parserExitState (known hit : Bool) : Nat :=
  if known then MetadataWitnessSuffixParser.knownExitState hit
  else MetadataWitnessSuffixParser.otherExitState hit

/-- Local normalizer entry selected by the same branch and hit bit. -/
def normalizerLocalEntryState (known hit : Bool) : Nat :=
  if known then MetadataWitnessStage.Normalizer.knownSeekWitnessState hit
  else MetadataWitnessStage.Normalizer.otherSeekRawState hit

def normalizerEntryState (known hit : Bool) : Nat :=
  normalizerOffset + normalizerLocalEntryState known hit

def handoffIndex : Bool -> Bool -> Nat
  | false, false => 0
  | false, true => 1
  | true, false => 2
  | true, true => 3

def handoffBase : Nat := normalizerBlock.stateCount

def handoffScratchState (known hit : Bool) : Nat :=
  handoffBase + handoffIndex known hit

def stateCount : Nat := handoffBase + 4

/-- Two-step control-only handoff for one parser exit. -/
def handoffDescription (known hit : Bool) : MachineDescription :=
  blankHeadBounceJumpDescription stateCount
    (parserExitState known hit) (handoffScratchState known hit)
    (normalizerEntryState known hit)

def handoffTransitions : List TransitionDescription :=
  (handoffDescription false false).transitions ++
    (handoffDescription false true).transitions ++
    (handoffDescription true false).transitions ++
    (handoffDescription true true).transitions

/-- Parser, four finite-control handoffs, and an offset normalizer block. -/
def description : MachineDescription where
  stateCount := stateCount
  start := MetadataWitnessSuffixParser.description.start
  halt := normalizerBlock.halt
  transitions :=
    MetadataWitnessSuffixParser.description.transitions ++
      handoffTransitions ++ normalizerBlock.transitions

set_option maxRecDepth 100000 in
theorem description_subroutineReady : description.SubroutineReady :=
  machineDescription_subroutineReady_of_transition_checks
    description (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem description_deterministic : description.Deterministic :=
  description_subroutineReady.left.right.right.right.right

theorem parserTransitions_subset
    (t : TransitionDescription)
    (ht : t ∈ MetadataWitnessSuffixParser.description.transitions) :
    t ∈ description.transitions := by
  simp [description, ht]

theorem normalizerTransitions_subset
    (t : TransitionDescription) (ht : t ∈ normalizerBlock.transitions) :
    t ∈ description.transitions := by
  simp [description, ht]

theorem handoffTransitions_subset
    (known hit : Bool) (t : TransitionDescription)
    (ht : t ∈ (handoffDescription known hit).transitions) :
    t ∈ description.transitions := by
  cases known <;> cases hit <;>
    simp [description, handoffTransitions] at ht ⊢ <;>
    simp_all

theorem parserExit_transitionFreeAt (known hit : Bool) :
    MetadataWitnessSuffixParser.description.TransitionFreeAt
      (parserExitState known hit) := by
  cases known
  · exact MetadataWitnessSuffixParser.description_transitionFreeAt_otherExit hit
  · exact MetadataWitnessSuffixParser.description_transitionFreeAt_knownExit hit

theorem handoffSource_ne_scratch (known hit : Bool) :
    parserExitState known hit ≠ handoffScratchState known hit := by
  cases known <;> cases hit <;> decide

theorem handoffDescription_transitionFreeAt_target
    (known hit : Bool) :
    (handoffDescription known hit).TransitionFreeAt
      (normalizerEntryState known hit) := by
  cases known <;> cases hit <;>
    exact transition_notFrom_of_all (by decide)

theorem normalizerBlock_transitionFreeAt_halt :
    normalizerBlock.TransitionFreeAt normalizerBlock.halt := by
  exact MachineDescription.offsetDescription_haltTransitionFree
    normalizerOffset MetadataWitnessStage.Normalizer.description_subroutineReady.right

theorem suffixParser_runsFrom_known
    (left : List (Option Bool))
    (raw : List MetadataTokenCopy.TokenKind)
    (scratchCount : Nat) (hit : Bool) (finalState : Nat)
    (right : List (Option Bool)) :
    RunsFromStateTapeEquiv MetadataWitnessSuffixParser.description
      MetadataWitnessSuffixParser.description.start
      (MetadataWitnessSuffixParser.knownExitState hit)
      (MetadataWitnessSuffixParser.sourceTape left raw scratchCount hit
        (List.append (MetadataTokenCopy.encodedTokenCells .one)
          (MetadataTokenCopy.encodedTokens
            (MetadataWitnessBridge.natTokens finalState))) right)
      (MetadataWitnessSuffixParser.knownTargetTape
        left raw scratchCount finalState right) := by
  rcases MetadataWitnessSuffixParser.run_known
      left raw scratchCount hit finalState right with ⟨steps, hrun⟩
  exact ⟨steps, _, hrun, Tape.Equiv.refl _⟩

theorem suffixParser_runsFrom_other
    (left : List (Option Bool))
    (raw : List MetadataTokenCopy.TokenKind)
    (scratchCount : Nat) (hit : Bool)
    (right : List (Option Bool)) :
    RunsFromStateTapeEquiv MetadataWitnessSuffixParser.description
      MetadataWitnessSuffixParser.description.start
      (MetadataWitnessSuffixParser.otherExitState hit)
      (MetadataWitnessSuffixParser.sourceTape left raw scratchCount hit
        (MetadataTokenCopy.encodedTokenCells .zero) right)
      (MetadataWitnessSuffixParser.otherTargetTape
        left raw scratchCount right) := by
  rcases MetadataWitnessSuffixParser.run_other
      left raw scratchCount hit right with ⟨steps, hrun⟩
  exact ⟨steps, _, hrun, Tape.Equiv.refl _⟩

theorem knownTargetTape_read
    (left : List (Option Bool))
    (raw : List MetadataTokenCopy.TokenKind)
    (scratchCount finalState : Nat)
    (right : List (Option Bool)) :
    Tape.read (MetadataWitnessSuffixParser.knownTargetTape
      left raw scratchCount finalState right) = none := by
  rfl

theorem otherTargetTape_read
    (left : List (Option Bool))
    (raw : List MetadataTokenCopy.TokenKind)
    (scratchCount : Nat) (right : List (Option Bool)) :
    Tape.read (MetadataWitnessSuffixParser.otherTargetTape
      left raw scratchCount right) = none := by
  rfl

theorem description_runsFrom_parser
    (known hit : Bool) {Tin Tmid : Tape Bool}
    (hrun :
      RunsFromStateTapeEquiv MetadataWitnessSuffixParser.description
        MetadataWitnessSuffixParser.description.start
        (parserExitState known hit) Tin Tmid) :
    RunsFromStateTapeEquiv description
      MetadataWitnessSuffixParser.description.start
      (parserExitState known hit) Tin Tmid := by
  exact runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
    parserTransitions_subset description_deterministic
    (parserExit_transitionFreeAt known hit) hrun

theorem description_runsFrom_handoff
    (known hit : Bool) (T : Tape Bool)
    (hread : Tape.read T = none) :
    RunsFromStateTapeEquiv description
      (parserExitState known hit) (normalizerEntryState known hit) T T := by
  have hsmall :
      RunsFromStateTapeEquiv (handoffDescription known hit)
        (parserExitState known hit) (normalizerEntryState known hit) T T := by
    simpa [handoffDescription] using
      (blankHeadBounceJumpDescription_runsFromBlankHead
        (stateCount := stateCount)
        (source := parserExitState known hit)
        (scratch := handoffScratchState known hit)
        (target := normalizerEntryState known hit)
        (handoffSource_ne_scratch known hit) hread)
  exact runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
    (handoffTransitions_subset known hit) description_deterministic
    (handoffDescription_transitionFreeAt_target known hit) hsmall

theorem description_runsFrom_normalizer
    (known hit : Bool) {Tin Tout : Tape Bool}
    (hrun :
      RunsFromStateTapeEquiv MetadataWitnessStage.Normalizer.description
        (normalizerLocalEntryState known hit)
        MetadataWitnessStage.Normalizer.description.halt Tin Tout) :
    RunsFromStateTapeEquiv description
      (normalizerEntryState known hit) description.halt Tin Tout := by
  have hoffset := runsFromStateTapeEquiv_offsetDescription
    normalizerOffset hrun
  have hlift :=
    runsFromStateTapeEquiv_of_subset_deterministic_of_transitionFree
      normalizerTransitions_subset description_deterministic
      normalizerBlock_transitionFreeAt_halt hoffset
  simpa [normalizerBlock, normalizerEntryState, description] using hlift

theorem description_runsFrom_of_runs
    (known hit : Bool) {Tin Tmid Tout : Tape Bool}
    (hparser :
      RunsFromStateTapeEquiv MetadataWitnessSuffixParser.description
        MetadataWitnessSuffixParser.description.start
        (parserExitState known hit) Tin Tmid)
    (hread : Tape.read Tmid = none)
    (hnormalizer :
      RunsFromStateTapeEquiv MetadataWitnessStage.Normalizer.description
        (normalizerLocalEntryState known hit)
        MetadataWitnessStage.Normalizer.description.halt Tmid Tout) :
    RunsFromStateTapeEquiv description description.start description.halt
      Tin Tout := by
  have hparser' := description_runsFrom_parser known hit hparser
  have hhandoff := description_runsFrom_handoff known hit Tmid hread
  have hnormalizer' :=
    description_runsFrom_normalizer known hit hnormalizer
  simpa [description] using
    runsFromStateTapeEquiv_trans hparser'
      (runsFromStateTapeEquiv_trans hhandoff hnormalizer')

theorem description_runsFrom_known_of_normalizer
    (left : List (Option Bool))
    (raw : List MetadataTokenCopy.TokenKind)
    (scratchCount : Nat) (hit : Bool) (finalState : Nat)
    (right : List (Option Bool)) {Tout : Tape Bool}
    (hnormalizer :
      RunsFromStateTapeEquiv MetadataWitnessStage.Normalizer.description
        (MetadataWitnessStage.Normalizer.knownSeekWitnessState hit)
        MetadataWitnessStage.Normalizer.description.halt
        (MetadataWitnessSuffixParser.knownTargetTape
          left raw scratchCount finalState right) Tout) :
    RunsFromStateTapeEquiv description description.start description.halt
      (MetadataWitnessSuffixParser.sourceTape left raw scratchCount hit
        (List.append (MetadataTokenCopy.encodedTokenCells .one)
          (MetadataTokenCopy.encodedTokens
            (MetadataWitnessBridge.natTokens finalState))) right)
      Tout := by
  exact description_runsFrom_of_runs true hit
    (by simpa [parserExitState] using
      (suffixParser_runsFrom_known
        left raw scratchCount hit finalState right))
    (knownTargetTape_read left raw scratchCount finalState right)
    (by simpa [normalizerLocalEntryState] using hnormalizer)

theorem description_runsFrom_other_of_normalizer
    (left : List (Option Bool))
    (raw : List MetadataTokenCopy.TokenKind)
    (scratchCount : Nat) (hit : Bool)
    (right : List (Option Bool)) {Tout : Tape Bool}
    (hnormalizer :
      RunsFromStateTapeEquiv MetadataWitnessStage.Normalizer.description
        (MetadataWitnessStage.Normalizer.otherSeekRawState hit)
        MetadataWitnessStage.Normalizer.description.halt
        (MetadataWitnessSuffixParser.otherTargetTape
          left raw scratchCount right) Tout) :
    RunsFromStateTapeEquiv description description.start description.halt
      (MetadataWitnessSuffixParser.sourceTape left raw scratchCount hit
        (MetadataTokenCopy.encodedTokenCells .zero) right)
      Tout := by
  exact description_runsFrom_of_runs false hit
    (by simpa [parserExitState] using
      (suffixParser_runsFrom_other left raw scratchCount hit right))
    (otherTargetTape_read left raw scratchCount right)
    (by simpa [normalizerLocalEntryState] using hnormalizer)

theorem description_haltsFromTapeEquiv_known_of_normalizer
    (left : List (Option Bool))
    (raw : List MetadataTokenCopy.TokenKind)
    (scratchCount : Nat) (hit : Bool) (finalState : Nat)
    (right : List (Option Bool)) {Tout : Tape Bool}
    (hnormalizer :
      RunsFromStateTapeEquiv MetadataWitnessStage.Normalizer.description
        (MetadataWitnessStage.Normalizer.knownSeekWitnessState hit)
        MetadataWitnessStage.Normalizer.description.halt
        (MetadataWitnessSuffixParser.knownTargetTape
          left raw scratchCount finalState right) Tout) :
    description.HaltsFromTapeEquiv
      (MetadataWitnessSuffixParser.sourceTape left raw scratchCount hit
        (List.append (MetadataTokenCopy.encodedTokenCells .one)
          (MetadataTokenCopy.encodedTokens
            (MetadataWitnessBridge.natTokens finalState))) right)
      Tout := by
  exact (description_runsFrom_known_of_normalizer
    left raw scratchCount hit finalState right hnormalizer
    ).toHaltsFromTapeEquiv rfl rfl

theorem description_haltsFromTapeEquiv_other_of_normalizer
    (left : List (Option Bool))
    (raw : List MetadataTokenCopy.TokenKind)
    (scratchCount : Nat) (hit : Bool)
    (right : List (Option Bool)) {Tout : Tape Bool}
    (hnormalizer :
      RunsFromStateTapeEquiv MetadataWitnessStage.Normalizer.description
        (MetadataWitnessStage.Normalizer.otherSeekRawState hit)
        MetadataWitnessStage.Normalizer.description.halt
        (MetadataWitnessSuffixParser.otherTargetTape
          left raw scratchCount right) Tout) :
    description.HaltsFromTapeEquiv
      (MetadataWitnessSuffixParser.sourceTape left raw scratchCount hit
        (MetadataTokenCopy.encodedTokenCells .zero) right)
      Tout := by
  exact (description_runsFrom_other_of_normalizer
    left raw scratchCount hit right hnormalizer
    ).toHaltsFromTapeEquiv rfl rfl

end GuardedEgress.MetadataWitnessDispatch
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
