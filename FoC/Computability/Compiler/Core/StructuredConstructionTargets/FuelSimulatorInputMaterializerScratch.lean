import FoC.Computability.Compiler.Core.StructuredConstructionTargets.Base

set_option doc.verso true

/-!
# FuelSimulator input materializer scratch

This scratch file records the current narrow emitter route for
`FUELSIMULATOR_MATERIALIZER_PILOT_PLAN.md`.  It is intentionally not imported
by production modules.

The shared closed-index sequencing proof is closed in
{module}`FoC.Computability.Compiler.Core.StructuredConstructionTargets.Base`.
The remaining shared emitter leaf has been narrowed from arbitrary
{lit}`Tape Bool` sources to canonical input tapes
{lit}`Tape.input bits`.  That matters because a one-way stream transducer can
scan the public input word, whereas an arbitrary source tape would require
preserving unknown left context and head placement.

The next emitter machine boundary should produce the exact physical target
shape below, with the physical head rewound to the left boundary separator.
A normalized-output-only transducer is insufficient because
{name (full := FoC.Computability.Tape.Equiv)}`Tape.Equiv` preserves the head cell and left/right contexts up to
trailing blanks.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

/-- Source family for the narrowed shared embedding emitter. -/
def scratchInputEmbeddingEmitterSource (bits : Word Bool) : Tape Bool :=
  Tape.input bits

/-- Exact target family for the narrowed shared embedding emitter. -/
def scratchInputEmbeddingEmitterTarget (bits : Word Bool) : Tape Bool :=
  structured3InputMaterializerTargetTape (Tape.input bits) Tape.blank

/--
The emitter target is the guarded three-logical-tape encoding of the public
input tape, blank scratch, and blank output buffer.
-/
theorem scratchInputEmbeddingEmitterTarget_eq_encodedGuardedStructured3Tapes
    (bits : Word Bool) :
    scratchInputEmbeddingEmitterTarget bits =
      encodedGuardedStructured3Tapes
        (Tape.input bits) Tape.blank Tape.blank := by
  rfl

/--
Physical cells the emitter must leave to the right of the left boundary
separator, with the head on that separator.
-/
theorem scratchInputEmbeddingEmitterTarget_cells
    (bits : Word Bool) :
    Tape.cells (scratchInputEmbeddingEmitterTarget bits) =
      structured3InputEmbeddingEmitterTargetCells bits := by
  rw [structured3InputEmbeddingEmitterTargetCells_eq]
  rfl

/--
The stream-expansion emitter needs one bit of control state.  Before seeing an
input bit, the terminating blank is the current blank head cell of
{lit}`Tape.input []`; after seeing at least one bit, the terminating blank is the
right guard after the copied input word.
-/
inductive ScratchInputEmbeddingEmitterScanState where
  | fresh
  | afterBit
  deriving DecidableEq, Repr

/-- Static cells written before scanning the public input word. -/
def scratchInputEmbeddingEmitterPrefixCells : List (Option Bool) :=
  List.append tapeSeparatorCells
    (List.append (logicalCellCode (none : Option Bool)) headMarkerCells)

/-- Physical cells emitted for one scanned input bit. -/
def scratchInputEmbeddingEmitterBitCells (bit : Bool) :
    List (Option Bool) :=
  logicalCellCode (some bit)

/--
Cells emitted from the scanned input window before the right guard.  The empty
case emits the blank head cell of {lit}`Tape.input []`; the nonempty case emits
the logical-cell code of each input bit.
-/
def scratchInputEmbeddingEmitterScannedCells
    (bits : Word Bool) : List (Option Bool) :=
  match bits with
  | [] => logicalCellCode (none : Option Bool)
  | bit :: rest =>
      List.append (scratchInputEmbeddingEmitterBitCells bit)
        (logicalCellListCode (rest.map some))

/-- Right guard after the public input logical tape segment. -/
def scratchInputEmbeddingEmitterRightGuardCells : List (Option Bool) :=
  logicalCellCode (none : Option Bool)

/-- Static suffix for blank scratch tape, blank output tape, and final separator. -/
def scratchInputEmbeddingEmitterSuffixCells : List (Option Bool) :=
  List.append tapeSeparatorCells
    (List.append guardedBlankLogicalTapeCode
      (List.append tapeSeparatorCells
        (List.append guardedBlankLogicalTapeCode tapeSeparatorCells)))

/--
Draft target cells for the planned {lit}`optionCellExpandAppendDescription` leaf.
The eventual machine should write these cells and rewind to the first
separator.
-/
def scratchOptionCellExpandAppendTargetCells
    (bits : Word Bool) : List (Option Bool) :=
  List.append scratchInputEmbeddingEmitterPrefixCells
    (List.append (scratchInputEmbeddingEmitterScannedCells bits)
      (List.append scratchInputEmbeddingEmitterRightGuardCells
        scratchInputEmbeddingEmitterSuffixCells))

/--
The draft stream-expansion target is definitionally the same physical target as
the production narrowed embedding emitter.
-/
theorem scratchOptionCellExpandAppendTargetCells_eq
    (bits : Word Bool) :
    scratchOptionCellExpandAppendTargetCells bits =
      structured3InputEmbeddingEmitterTargetCells bits := by
  cases bits with
  | nil =>
      rfl
  | cons bit rest =>
      simp [scratchOptionCellExpandAppendTargetCells,
        structured3InputEmbeddingEmitterTargetCells,
        scratchInputEmbeddingEmitterPrefixCells,
        scratchInputEmbeddingEmitterScannedCells,
        scratchInputEmbeddingEmitterRightGuardCells,
        scratchInputEmbeddingEmitterSuffixCells,
        guardedInputWordLogicalTapeCode,
        scratchInputEmbeddingEmitterBitCells,
        guardedBlankLogicalTapeCode, List.append_assoc]

/--
Concrete draft run contract for the missing option-cell expansion primitive.
This is intentionally lower-level than the public materializer theorem: it says
exactly which physical cells must be emitted for each canonical input tape.
-/
structure ScratchOptionCellExpandAppendRunSpec
    (emitter : MachineDescription) : Prop where
  ready : emitter.SubroutineReady
  forward :
    forall bits : Word Bool,
      emitter.HaltsFromTape
        (Tape.input bits)
        (tapeAtCells []
          (scratchOptionCellExpandAppendTargetCells bits))

/-- Scratch-facing alias for the promoted production stream-expansion table. -/
def scratchOptionCellExpandAppendDescription : MachineDescription :=
  optionCellExpandAppendDescription

theorem scratchOptionCellExpandAppendDescription_runSpec :
    ScratchOptionCellExpandAppendRunSpec
      scratchOptionCellExpandAppendDescription := by
  constructor
  · exact optionCellExpandAppendDescription_runSpec.ready
  · intro bits
    unfold scratchOptionCellExpandAppendDescription
    rw [scratchOptionCellExpandAppendTargetCells_eq,
      ← optionCellExpandAppendTargetCells_eq_structured3]
    exact optionCellExpandAppendDescription_runSpec.forward bits

/--
The draft option-cell expansion contract is strong enough to discharge the
shared production emitter target-cell contract.
-/
theorem scratchStructured3InputEmbeddingEmitterTargetCellsRunSpec_of_expand
    {emitter : MachineDescription}
    (hspec : ScratchOptionCellExpandAppendRunSpec emitter) :
    Structured3InputEmbeddingEmitterTargetCellsRunSpec emitter := by
  constructor
  · exact hspec.ready
  · intro bits
    unfold structured3InputEmbeddingEmitterTargetTape
    rw [← scratchOptionCellExpandAppendTargetCells_eq bits]
    exact hspec.forward bits

/--
Next concrete emitter boundary:

1. Expand the scanned input word into
   {lit}`logicalTapeCode (guardLogicalTape (Tape.input bits))`, preserving physical
   blank separators, not only normalized output bits.
2. Append the two blank guarded logical tapes and trailing separator.
3. Rewind to the left boundary separator so the final tape is
   {lit}`Tape.Equiv` to {lit}`scratchInputEmbeddingEmitterTarget bits`.
-/
def scratchInputEmbeddingEmitterMachineBoundary : Prop :=
  exists emitter : MachineDescription,
    Structured3InputEmbeddingEmitterTargetCellsRunSpec emitter

theorem scratchInputEmbeddingEmitterMachineBoundary_of_expand :
    scratchInputEmbeddingEmitterMachineBoundary := by
  exact
    ⟨scratchOptionCellExpandAppendDescription,
      scratchStructured3InputEmbeddingEmitterTargetCellsRunSpec_of_expand
        scratchOptionCellExpandAppendDescription_runSpec⟩

end StructuredConstructionTargets

end Computability
end FoC
