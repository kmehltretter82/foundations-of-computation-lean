import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition.StateSelectorRuns

set_option doc.verso true

/-!
# Compact metadata-prefix materializer

This phase owns the metadata half of the remaining #18 decomposition.  It
starts with tape 0 at the encoded configuration left-list length, tape 1 at the
exact stage counter, and tape 2 at the blank immediately right of the
selector-bearing scratch block.

The machine temporarily writes {lit}`false` at that tape-2 blank, walks left
across the selector and scratch markers, preserves the first blank as the
metadata delimiter, and copies the already-scanned input/stage/raw-state prefix
backward from tape 0.  A four-bit lag discards exactly the fixed header token.
It restores tape 0 to the header of the complete preserved layout and walks
tape 2 right to the temporary false head.  The next phase therefore needs only
one forward scan through the prefix and configuration.

The selector and remaining scratch cells are read but never changed.  The
temporary false head is deliberately left for the final configuration/hit
phase, which decodes the source hit and overwrites it with the actual value.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace FieldDecomposition
namespace MetadataPrefix

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open StructuredConstructionTargets.FuelOutputCore
open ClassifiedBoundary

/-!
## Typed finite-control table
-/

inductive State where
  | start
  | scratchLeft
  | copyEnter
  | copy0
  | copy1 (a : Bool)
  | copy2 (a b : Bool)
  | copy3 (a b c : Bool)
  | copy4 (a b c d : Bool)
  | copy4p (a b c d pending : Bool)
  | outputEnter
  | metadataRight
  | scratchRight
  | halt
deriving DecidableEq, Repr

def boolValues : List Bool := [false, true]

theorem bool_mem_boolValues (bit : Bool) : bit ∈ boolValues := by
  cases bit <;> simp [boolValues]

def copyStates : List State :=
  .copy0 ::
    List.append
      (boolValues.map State.copy1)
      (List.append
        (boolValues.flatMap fun a =>
          boolValues.map fun b => State.copy2 a b)
        (List.append
          (boolValues.flatMap fun a =>
            boolValues.flatMap fun b =>
              boolValues.map fun c => State.copy3 a b c)
          (List.append
            (boolValues.flatMap fun a =>
              boolValues.flatMap fun b =>
                boolValues.flatMap fun c =>
                  boolValues.map fun d => State.copy4 a b c d)
            (boolValues.flatMap fun a =>
              boolValues.flatMap fun b =>
                boolValues.flatMap fun c =>
                  boolValues.flatMap fun d =>
                    boolValues.map fun pending =>
                      State.copy4p a b c d pending))))

def states : List State :=
  [ .start, .scratchLeft, .copyEnter ] ++
    copyStates ++
    [ .outputEnter, .metadataRight, .scratchRight, .halt ]

theorem state_mem (s : State) : s ∈ states := by
  cases s with
  | start => simp [states]
  | scratchLeft => simp [states]
  | copyEnter => simp [states]
  | copy0 => simp [states, copyStates]
  | copy1 a =>
      simp [states, copyStates, bool_mem_boolValues]
  | copy2 a b =>
      simp [states, copyStates, bool_mem_boolValues]
  | copy3 a b c =>
      simp [states, copyStates, bool_mem_boolValues]
  | copy4 a b c d =>
      simp [states, copyStates, bool_mem_boolValues]
  | copy4p a b c d pending =>
      simp [states, copyStates, bool_mem_boolValues]
  | outputEnter => simp [states]
  | metadataRight => simp [states]
  | scratchRight => simp [states]
  | halt => simp [states]

/-- Copy metadata backward, discard the four-bit header held at the left edge,
restore the original header cursor, and return to the marked tape-2 head. -/
def next :
    State -> Option Bool -> Option Bool -> Option Bool ->
      Option (TypedStep State)
  | .start, _, _, _ =>
      some ⟨.scratchLeft, keepS, keepS, writeL (some false)⟩
  | .scratchLeft, _, _, some _ =>
      some ⟨.scratchLeft, keepS, keepS, keepL⟩
  | .scratchLeft, _, _, none =>
      some ⟨.copyEnter, keepS, keepS, keepL⟩
  | .copyEnter, _, _, _ =>
      some ⟨.copy0, keepL, keepS, keepS⟩
  | .copy0, some bit, _, _ =>
      some ⟨.copy1 bit, keepL, keepS, keepS⟩
  | .copy1 a, some bit, _, _ =>
      some ⟨.copy2 a bit, keepL, keepS, keepS⟩
  | .copy2 a b, some bit, _, _ =>
      some ⟨.copy3 a b bit, keepL, keepS, keepS⟩
  | .copy3 a b c, some bit, _, _ =>
      some ⟨.copy4 a b c bit, keepL, keepS, keepS⟩
  | .copy4 a b c d, some bit, _, _ =>
      some ⟨.copy4p b c d bit a, keepL, keepS, keepS⟩
  | .copy4p a b c d pending, some bit, _, _ =>
      some ⟨.copy4p b c d bit a,
        keepL, keepS, writeL (some pending)⟩
  | .copy4p false false false false pending, none, _, _ =>
      some ⟨.outputEnter, keepR, keepS, writeS (some pending)⟩
  | .outputEnter, _, _, _ =>
      some ⟨.metadataRight, keepS, keepS, keepR⟩
  | .metadataRight, _, _, some _ =>
      some ⟨.metadataRight, keepS, keepS, keepR⟩
  | .metadataRight, _, _, none =>
      some ⟨.scratchRight, keepS, keepS, keepR⟩
  | .scratchRight, _, _, some _ =>
      some ⟨.scratchRight, keepS, keepS, keepR⟩
  | .scratchRight, _, _, none =>
      some ⟨.halt, keepS, keepS, keepL⟩
  | _, _, _, _ => none

theorem next_target_mem :
    forall s : State, s ∈ states ->
      forall (r0 r1 r2 : Option Bool) (st : TypedStep State),
        next s r0 r1 r2 = some st -> st.target ∈ states := by
  intro _s _hs _r0 _r1 _r2 st _hnext
  exact state_mem st.target

def table : TypedStateTable State :=
  TypedStateTable.ofList
    states
    .start
    .halt
    next
    (state_mem .start)
    (state_mem .halt)
    (by intro r0 r1 r2; rfl)
    next_target_mem

def description : Description :=
  table.description

theorem description_wellFormed : description.WellFormed :=
  table.description_wellFormed

theorem description_haltTransitionFree :
    description.HaltTransitionFree :=
  table.description_haltTransitionFree

theorem description_supportsReadWriteRows3 :
    SupportsReadWriteRows3 description :=
  table.description_supportsReadWriteRows3

theorem description_subroutineReady : description.SubroutineReady :=
  table.description_subroutineReady

/-!
## Exact marked-metadata boundary
-/

/-- Tape 0 after the backward metadata copy.  The complete encoded simulator
layout is preserved, with the head returned to its header.  The final
configuration/hit phase consumes this prefix and the configuration fields in
one forward scan. -/
def headerStartTape (L : SimulatorLayout) : Tape Bool :=
  rightEdgeRewindTargetTape (SimulatorLayout.asBoolInput L) []

def sourceTapes
    (D : MachineDescription) (L : SimulatorLayout) : List (Tape Bool) :=
  [ StateSelector.postStateTape L
  , FieldDecomposition.stageCounterTape L.stage
  , StateSelector.selectorScratchTape D L ]

/-- Exact logical target.  Tape 0 is restored to the layout header; tape 1 is
untouched; tape 2 has compact metadata, the byte-for-byte selector/scratch
block, and the temporary false head. -/
def targetTapes
    (D : MachineDescription) (L : SimulatorLayout) : List (Tape Bool) :=
  [ headerStartTape L
  , FieldDecomposition.stageCounterTape L.stage
  , ClassifiedBoundary.metadataHitTapeWithSelectorMarked D L ]

def sourceTape
    (D : MachineDescription) (L : SimulatorLayout) : Tape Bool :=
  encodedGuardedStructuredTapes (sourceTapes D L)

def targetTape
    (D : MachineDescription) (L : SimulatorLayout) : Tape Bool :=
  encodedGuardedStructuredTapes (targetTapes D L)

theorem sourceTape_eq_stateSelectorTarget
    (D : MachineDescription) (L : SimulatorLayout) :
    sourceTape D L = StateSelector.targetTape D L := by
  rfl

/-- Exact remaining run proof for the concrete table above. -/
def RunObligation : Prop :=
  forall (D : MachineDescription) (L : SimulatorLayout),
    description.HaltsWithTapes
      (ThreeTape.config description.start
        (StateSelector.postStateTape L)
        (FieldDecomposition.stageCounterTape L.stage)
        (StateSelector.selectorScratchTape D L))
      (targetTapes D L)

/-- Final construction after metadata materialization: decode the encoded
prefix and left/head/right fields on tape 0 exactly, decode the hit token, and
overwrite the temporary false tape-2 head with the actual hit. -/
def ConfigTapeAndHitSpec
    (D : MachineDescription) (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall L : SimulatorLayout,
      materializer.HaltsFromTapeEquiv
        (targetTape D L)
        (ClassifiedBoundary.classifiedLoopTargetTape D L)

def ConfigTapeAndHitConstruction (D : MachineDescription) : Prop :=
  exists materializer : MachineDescription,
    ConfigTapeAndHitSpec D materializer

end MetadataPrefix
end FieldDecomposition
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
