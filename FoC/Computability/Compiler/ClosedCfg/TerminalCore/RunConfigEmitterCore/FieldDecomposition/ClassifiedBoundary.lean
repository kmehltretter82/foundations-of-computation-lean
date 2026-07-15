import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition

set_option doc.verso true

/-!
# Classified field-decomposition boundary

The loop dispatcher cannot be entered as an ordinary sequential subroutine at
an input-dependent typed state.  For a fixed description {lit}`D`, this module
therefore makes the finite classification result physical inside the existing
scratch-marker block.  A fixed-start ingress scanner reads the reserved
selector, restores every reserved cell to a marker, and transitions internally
to the matching dispatcher state.

No new tape window is allocated.  The selector overwrites the markers nearest
the live hit in reverse physical order, so moving left from the hit reads the
payload in forward order.  After classification, the scanner can restore all
visited selector cells to {lit}`some true`, scan to the existing metadata
delimiter, and return right to a temporarily marked hit.  The endpoint is then
exactly the original compact metadata tape.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace FieldDecomposition
namespace ClassifiedBoundary

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

/-!
## Finite D-specific selector
-/

/-- Self-delimiting selector consumed by the fixed-start dispatcher ingress.
The leading Boolean distinguishes the generic branch.  A known branch carries
its fixed description state; only the finitely many values in
{name}`fixedStepValues` can occur for fixed {lit}`D`. -/
def selectorCode
    {D : MachineDescription} (tag : StateClass D) :
    Word MachineCodeSymbol :=
  match tag with
  | .known state _ =>
      encodeBoolAppend true (encodeNatAppend state [])
  | .other =>
      encodeBoolAppend false []

/-- Boolean cells of the token-level selector. -/
def selectorBits
    {D : MachineDescription} (tag : StateClass D) : Word Bool :=
  encodeCodeWordAsInput (selectorCode tag)

@[simp] theorem selectorBits_known
    {D : MachineDescription} {state : Nat}
    (hstate : state ∈ fixedStepValues D) :
    selectorBits (StateClass.known state hstate) =
      encodeCodeWordAsInput
        (encodeBoolAppend true (encodeNatAppend state [])) := by
  rfl
theorem encodeNat_length (n : Nat) :
    (encodeNat n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [encodeNat, ih]

theorem selectorBits_length_known
    {D : MachineDescription} {state : Nat}
    (hstate : state ∈ fixedStepValues D) :
    (selectorBits (StateClass.known state hstate)).length =
      4 * (state + 2) := by
  simp [selectorBits, selectorCode,
    encodeCodeWordAsInput_length, encodeBoolAppend,
    encodeCellAppend, encodeCell, encodeNatAppend, encodeNat_length]

theorem selectorBits_length_other (D : MachineDescription) :
    (selectorBits (StateClass.other : StateClass D)).length = 4 := by
  simp [selectorBits, selectorCode,
    encodeCodeWordAsInput_length, encodeBoolAppend,
    encodeCellAppend, encodeCell]

/-- The original layout reservoir always has room for the D-specific selector.
For a known state {lit}`q`, the selector uses {lit}`4 * (q + 2)` bits; the
source layout contains the full unary state field plus several independent
delimited fields. -/
theorem selectorBits_length_le_scratchWidth
    (D : MachineDescription) (L : SimulatorLayout) :
    (selectorBits (classifyState D L.config.state)).length ≤
      (RunConfigEmitterTheory.scratchWidthMarkers L).length := by
  rw [RunConfigEmitterTheory.scratchWidthMarkers_length]
  have hcapacity :=
    RunConfigEmitterTheory.scratchWidth_ge_stateSelectorBits L
  by_cases hstate : L.config.state ∈ fixedStepValues D
  · rw [classifyState_of_mem hstate]
    rw [selectorBits_length_known hstate]
    exact hcapacity
  · rw [classifyState_of_not_mem hstate]
    rw [selectorBits_length_other]
    lia

/-!
## Reserved-marker layout
-/

/-- Markers not overwritten by the selector. -/
def remainingScratchMarkers
    (D : MachineDescription) (L : SimulatorLayout) :
    List (Option Bool) :=
  List.replicate
    ((RunConfigEmitterTheory.scratchWidthMarkers L).length -
      (selectorBits (classifyState D L.config.state)).length)
    (some true)

/-- Tape-left context nearest-first at the classified handoff.  The selector
is read forward by moving left; remaining markers and the existing metadata
delimiter follow it. -/
def classifiedMetadataLeft
    (D : MachineDescription) (L : SimulatorLayout) :
    List (Option Bool) :=
  List.append
    ((selectorBits (classifyState D L.config.state)).map some)
    (List.append (remainingScratchMarkers D L)
      (none :: ((FieldDecomposition.metadataBits L).map some).reverse))

/-- Exact classified metadata tape.  It has the same finite window as the
ordinary metadata tape; only the nearest scratch markers are overwritten. -/
def metadataHitTapeWithSelector
    (D : MachineDescription) (L : SimulatorLayout) : Tape Bool :=
  tapeAtCells (classifiedMetadataLeft D L) [some L.hit, none]
/-- The start row saves the original hit in its two-way finite control and
temporarily writes {lit}`false` at the hit.  Once selector cells are restored
to true, this is the unique non-true cell encountered after scanning right
from the metadata delimiter. -/
def metadataHitTapeWithSelectorMarked
    (D : MachineDescription) (L : SimulatorLayout) : Tape Bool :=
  tapeAtCells (classifiedMetadataLeft D L) [some false, none]
/-- Scratch block after the selector scanner has restored every reserved cell
to a true marker. -/
def restoredScratchMarkers
    (D : MachineDescription) (L : SimulatorLayout) :
    List (Option Bool) :=
  List.append
    (List.replicate
      (selectorBits (classifyState D L.config.state)).length (some true))
    (remainingScratchMarkers D L)

theorem restoredScratchMarkers_eq
    (D : MachineDescription) (L : SimulatorLayout) :
    restoredScratchMarkers D L =
      RunConfigEmitterTheory.scratchWidthMarkers L := by
  unfold restoredScratchMarkers remainingScratchMarkers
  have hcap := selectorBits_length_le_scratchWidth D L
  have hcombine :=
    (FoC.Computability.list_replicate_add_append
      (some true : Option Bool)
      (selectorBits (classifyState D L.config.state)).length
      ((RunConfigEmitterTheory.scratchWidthMarkers L).length -
        (selectorBits (classifyState D L.config.state)).length)
      ([] : List (Option Bool))).symm
  rw [Nat.add_sub_of_le hcap] at hcombine
  simpa [RunConfigEmitterTheory.scratchWidthMarkers] using hcombine

/-- Exact tape after selector restoration and hit restoration. -/
def metadataHitTapeAfterSelectorRestore
    (D : MachineDescription) (L : SimulatorLayout) : Tape Bool :=
  tapeAtCells
    (List.append (restoredScratchMarkers D L)
      (none :: ((FieldDecomposition.metadataBits L).map some).reverse))
    [some L.hit, none]

/-- Unlike an appended selector, the reserved-marker selector is erased back
to the compact metadata tape by exact equality. -/
theorem metadataHitTapeAfterSelectorRestore_eq
    (D : MachineDescription) (L : SimulatorLayout) :
    metadataHitTapeAfterSelectorRestore D L =
      FieldDecomposition.metadataHitTape L := by
  rw [metadataHitTapeAfterSelectorRestore, restoredScratchMarkers_eq]
  simp [FieldDecomposition.metadataHitTape,
    FieldDecomposition.metadataHitTapeWithHit,
    FieldDecomposition.metadataPrefixCells,
    RunConfigEmitterTheory.scratchWidthMarkers,
    tapeAtCells, List.reverse_append]

/-!
## D-specific loop boundary
-/

/-- Exact logical tapes carrying both loop data and the physical branch
selector needed by a fixed-start combined dispatcher. -/
def classifiedLoopTapes
    (D : MachineDescription) (L : SimulatorLayout) : List (Tape Bool) :=
  [ L.config.tape
  , FieldDecomposition.stageCounterTape L.stage
  , metadataHitTapeWithSelector D L ]

/-- Fixed-start ingress reaches the classified loop entry while removing the
physical selector from the metadata tape. -/
def SelectorIngressEndpointSpec
    (D : MachineDescription) (combined : Description)
    (entryState : StateClass D -> Nat) : Prop :=
  combined.WellFormed ∧
    combined.HaltTransitionFree ∧
    SupportsReadWriteRows3 combined ∧
    (forall tag : StateClass D,
      entryState tag < combined.stateCount) ∧
    forall L : SimulatorLayout,
      exists steps : Nat,
        combined.runConfig steps
            (ThreeTape.config combined.start
              L.config.tape
              (FieldDecomposition.stageCounterTape L.stage)
              (metadataHitTapeWithSelector D L)) =
          ThreeTape.config
            (entryState (classifyState D L.config.state))
            L.config.tape
            (FieldDecomposition.stageCounterTape L.stage)
            (FieldDecomposition.metadataHitTape L)
end ClassifiedBoundary
end FieldDecomposition
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
