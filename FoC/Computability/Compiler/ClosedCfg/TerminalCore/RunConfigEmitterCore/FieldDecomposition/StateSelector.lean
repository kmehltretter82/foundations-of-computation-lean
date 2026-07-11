import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition.StageCounter

set_option doc.verso true

/-!
# Raw-state parser and scratch-resident selector

This is the third executable phase of the #18 field decomposer.  It starts at
the raw configuration-state token exposed by {lit}`StageCounter`, preserves the
already materialized stage counter, and parses the unary state field against
the finite values of a fixed description {lit}`D`.

The classification is made physical without allocating tape cells.  The phase
temporarily marks the blank immediately right of the scratch reservoir, writes
the selector into the nearest reserved markers, returns to the temporary mark,
and restores that cell to blank.  Its exact endpoint therefore has the same
window as the original scratch tape and is ready for the remaining exact
configuration and metadata phases.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace FieldDecomposition
namespace StateSelector

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open StructuredConstructionTargets.FuelOutputCore
open ClassifiedBoundary

/-!
## Finite state bound
-/

/-- One more than the sum of every description state mentioned by the
fixed-step kernel.  Every known state is strictly below this bound. -/
def stateBound (D : MachineDescription) : Nat :=
  (fixedStepValues D).sum + 1

theorem stateBound_pos (D : MachineDescription) : 0 < stateBound D := by
  simp [stateBound]

theorem mem_le_sum
    {value : Nat} {values : List Nat} (hmem : value ∈ values) :
    value ≤ values.sum := by
  induction values with
  | nil =>
      simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      cases hmem with
      | inl heq =>
          subst value
          simp
      | inr htail =>
          have hle := ih htail
          simp only [List.sum_cons]
          lia

theorem mem_fixedStepValues_lt_stateBound
    {D : MachineDescription} {value : Nat}
    (hmem : value ∈ fixedStepValues D) :
    value < stateBound D := by
  unfold stateBound
  have hle := mem_le_sum hmem
  lia

/-- Initial bounded unary count. -/
def zeroCount (D : MachineDescription) : Fin (stateBound D) :=
  ⟨0, stateBound_pos D⟩

/-- Increment a bounded count, falling into overflow when the next value is
outside finite control. -/
def nextCount?
    {D : MachineDescription} (count : Fin (stateBound D)) :
    Option (Fin (stateBound D)) :=
  if hnext : count.val + 1 < stateBound D then
    some ⟨count.val + 1, hnext⟩
  else
    none

/-!
## Typed selector table
-/

/-- Typed control for unary classification and fixed selector emission. -/
inductive State (D : MachineDescription) where
  | parse (count : Fin (stateBound D)) (pos : GroupPos)
  | overflow (pos : GroupPos)
  | mark (tag : StateClass D)
  | emit
      (tag : StateClass D)
      (index : Fin (selectorBits tag).length)
  | rewind
      (tag : StateClass D)
      (steps : Fin ((selectorBits tag).length + 1))
  | restore (tag : StateClass D)
  | halt
deriving DecidableEq

def groupPositions : List GroupPos :=
  [.p0, .p1, .p2, .p3]

theorem pos_mem_groupPositions (pos : GroupPos) :
    pos ∈ groupPositions := by
  cases pos <;> simp [groupPositions]

theorem selectorBits_length_pos
    {D : MachineDescription} (tag : StateClass D) :
    0 < (selectorBits tag).length := by
  cases tag with
  | known state hstate =>
      rw [selectorBits_length_known hstate]
      lia
  | other =>
      rw [selectorBits_length_other]
      decide

def initialEmitIndex
    {D : MachineDescription} (tag : StateClass D) :
    Fin (selectorBits tag).length :=
  ⟨0, selectorBits_length_pos tag⟩

def succEmitIndex
    {D : MachineDescription} {tag : StateClass D}
    (index : Fin (selectorBits tag).length)
    (hnext : index.val + 1 < (selectorBits tag).length) :
    Fin (selectorBits tag).length :=
  ⟨index.val + 1, hnext⟩

def initialReturnSteps
    {D : MachineDescription} {tag : StateClass D}
    (last : Fin (selectorBits tag).length) :
    Fin ((selectorBits tag).length + 1) :=
  ⟨last.val, by lia⟩

def predReturnSteps
    {D : MachineDescription} {tag : StateClass D}
    (steps : Fin ((selectorBits tag).length + 1))
    (hpos : 0 < steps.val) :
    Fin ((selectorBits tag).length + 1) :=
  ⟨steps.val - 1, by lia⟩

/-- Parse one canonical unary state field, then overwrite only its reserved
scratch markers with the finite selector. -/
def next (D : MachineDescription) :
    State D -> Option Bool -> Option Bool -> Option Bool ->
      Option (TypedStep (State D))
  | .parse count .p0, some false, _, _ =>
      some ⟨.parse count .p1, keepR, keepS, keepS⟩
  | .parse count .p1, some false, _, _ =>
      some ⟨.parse count .p2, keepR, keepS, keepS⟩
  | .parse count .p2, some true, _, _ =>
      some ⟨.parse count .p3, keepR, keepS, keepS⟩
  | .parse count .p3, some false, _, _ =>
      match nextCount? count with
      | some count' =>
          some ⟨.parse count' .p0, keepR, keepS, keepS⟩
      | none =>
          some ⟨.overflow .p0, keepR, keepS, keepS⟩
  | .parse count .p3, some true, _, _ =>
      some ⟨.mark (classifyState D count.val), keepR, keepS, keepS⟩
  | .overflow .p0, some false, _, _ =>
      some ⟨.overflow .p1, keepR, keepS, keepS⟩
  | .overflow .p1, some false, _, _ =>
      some ⟨.overflow .p2, keepR, keepS, keepS⟩
  | .overflow .p2, some true, _, _ =>
      some ⟨.overflow .p3, keepR, keepS, keepS⟩
  | .overflow .p3, some false, _, _ =>
      some ⟨.overflow .p0, keepR, keepS, keepS⟩
  | .overflow .p3, some true, _, _ =>
      some ⟨.mark .other, keepR, keepS, keepS⟩
  | .mark tag, _, _, _ =>
      some
        ⟨.emit tag (initialEmitIndex tag),
          keepS, keepS, writeL (some false)⟩
  | .emit tag index, _, _, _ =>
      let bit := (selectorBits tag).get index
      if hlast : index.val + 1 = (selectorBits tag).length then
        some
          ⟨.rewind tag (initialReturnSteps index),
            keepS, keepS, writeR (some bit)⟩
      else
        have hnext : index.val + 1 < (selectorBits tag).length := by
          lia
        some
          ⟨.emit tag (succEmitIndex index hnext),
            keepS, keepS, writeL (some bit)⟩
  | .rewind tag steps, _, _, _ =>
      if hzero : steps.val = 0 then
        some ⟨.restore tag, keepS, keepS, keepS⟩
      else
        have hpos : 0 < steps.val := by lia
        some
          ⟨.rewind tag (predReturnSteps steps hpos),
            keepS, keepS, keepR⟩
  | .restore _, _, _, _ =>
      some ⟨.halt, keepS, keepS, writeS none⟩
  | _, _, _, _ => none

def parseStates (D : MachineDescription) : List (State D) :=
  (List.finRange (stateBound D)).flatMap fun count =>
    groupPositions.map fun pos => State.parse count pos

def overflowStates (D : MachineDescription) : List (State D) :=
  groupPositions.map State.overflow

def tagStates
    (D : MachineDescription) (tag : StateClass D) : List (State D) :=
  State.mark tag ::
    List.append
      ((List.finRange (selectorBits tag).length).map
        fun index => State.emit tag index)
      (List.append
        ((List.finRange ((selectorBits tag).length + 1)).map
          fun steps => State.rewind tag steps)
        [State.restore tag])

def states (D : MachineDescription) : List (State D) :=
  List.append (parseStates D)
    (List.append (overflowStates D)
      (List.append
        ((stateClasses D).flatMap (tagStates D))
        [State.halt]))

theorem state_mem (D : MachineDescription) (s : State D) :
    s ∈ states D := by
  cases s with
  | parse count pos =>
      simp [states, parseStates, List.mem_finRange,
        pos_mem_groupPositions]
  | overflow pos =>
      simp [states, overflowStates, pos_mem_groupPositions]
  | mark tag =>
      simp [states, tagStates, mem_stateClasses]
  | emit tag index =>
      simp [states, tagStates, mem_stateClasses, List.mem_finRange]
  | rewind tag steps =>
      simp [states, tagStates, mem_stateClasses, List.mem_finRange]
  | restore tag =>
      simp [states, tagStates, mem_stateClasses]
  | halt =>
      simp [states]

theorem next_target_mem
    (D : MachineDescription) :
    forall s : State D, s ∈ states D ->
      forall (r0 r1 r2 : Option Bool) (st : TypedStep (State D)),
        next D s r0 r1 r2 = some st -> st.target ∈ states D := by
  intro _s _hs _r0 _r1 _r2 st _hnext
  exact state_mem D st.target

def table (D : MachineDescription) : TypedStateTable (State D) :=
  TypedStateTable.ofList
    (states D)
    (.parse (zeroCount D) .p0)
    .halt
    (next D)
    (state_mem D _)
    (state_mem D _)
    (by intro r0 r1 r2; rfl)
    (next_target_mem D)

def description (D : MachineDescription) : Description :=
  (table D).description

theorem description_wellFormed (D : MachineDescription) :
    (description D).WellFormed :=
  (table D).description_wellFormed

theorem description_haltTransitionFree (D : MachineDescription) :
    (description D).HaltTransitionFree :=
  (table D).description_haltTransitionFree

theorem description_supportsReadWriteRows3 (D : MachineDescription) :
    SupportsReadWriteRows3 (description D) :=
  (table D).description_supportsReadWriteRows3

theorem description_subroutineReady (D : MachineDescription) :
    (description D).SubroutineReady :=
  (table D).description_subroutineReady

/-!
## Exact phase boundary
-/

/-- Configuration-field tokens after the raw state. -/
def postStateTokens (L : SimulatorLayout) : Word MachineCodeSymbol :=
  List.append (encodeNat L.config.tape.left.length)
    (List.append (L.config.tape.left.map cellTok)
      (cellTok L.config.tape.head ::
        List.append (encodeNat L.config.tape.right.length)
          (List.append (L.config.tape.right.map cellTok)
            [cellTok (some L.hit)])))

/-- Tape 0 at the first bit of the encoded left-list length. -/
def postStateTape (L : SimulatorLayout) : Tape Bool :=
  tapeAtCells
    (pushBits (codeBits (encodeNat L.config.state))
      (pushBits (codeBits (encodeNat L.stage))
        (pushBits (codeBits ((L.input.map some).map cellTok))
          (pushBits (codeBits (encodeNat (L.input.map some).length))
            (pushBits (tokBits MachineCodeSymbol.header) [none])))))
    (List.append (codeBits (postStateTokens L)) [none])

/-- Scratch tape after reserving the selector nearest its right blank. -/
def selectorScratchTape
    (D : MachineDescription) (L : SimulatorLayout) : Tape Bool :=
  tapeAtCells
    (List.append
      ((selectorBits (classifyState D L.config.state)).map some)
      (remainingScratchMarkers D L)) []

@[simp] theorem selectorScratchTape_read
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.read (selectorScratchTape D L) = none := by
  rfl

theorem selectorScratchTape_contextLength
    (D : MachineDescription) (L : SimulatorLayout) :
    Tape.contextLength (selectorScratchTape D L) =
      Tape.contextLength (SourceCounter.layoutMarkerTape L) := by
  have hcap := selectorBits_length_le_scratchWidth D L
  rw [RunConfigEmitterTheory.scratchWidthMarkers_length] at hcap
  simp [selectorScratchTape, SourceCounter.layoutMarkerTape,
    remainingScratchMarkers, Tape.contextLength, tapeAtCells]
  lia

/-!
The executable table above is the durable finite-control phase.  The next
proof module establishes its exact run from {name}`StageCounter.targetTape` to
the boundary named here, after which configuration-list decoding can proceed
without replaying classification.
-/

end StateSelector
end FieldDecomposition
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
