import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredInputMaterializer

set_option doc.verso true

/-!
# Option-cell expansion emitter target shapes

This module holds the exact physical target cells and the run contract for the
option-cell expansion primitive below the shared structured-input embedding
emitter.  The definitions were moved out of the structured construction target
base adapter module ({lit}`StructuredConstructionTargets.Base`) so the concrete
finite table and its proofs can live in a dedicated implementation module
without growing the base adapter module.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

/-- Encoded logical-tape segment for a guarded public input word. -/
def guardedInputWordLogicalTapeCode (bits : Word Bool) :
    List (Option Bool) :=
  List.append (logicalCellCode (none : Option Bool))
    (List.append headMarkerCells
      (List.append
        (match bits with
        | [] => logicalCellCode (none : Option Bool)
        | bit :: rest =>
            List.append (logicalCellCode (some bit))
              (logicalCellListCode (rest.map some)))
        (logicalCellCode (none : Option Bool))))

theorem guardedInputWordLogicalTapeCode_eq_logicalTapeCode
    (bits : Word Bool) :
    guardedInputWordLogicalTapeCode bits =
      logicalTapeCode (guardLogicalTape (Tape.input bits)) := by
  cases bits with
  | nil =>
      rfl
  | cons bit rest =>
      change
        List.append (logicalCellCode (none : Option Bool))
          (List.append headMarkerCells
            (List.append
              (List.append (logicalCellCode (some bit))
                (logicalCellListCode (rest.map some)))
              (logicalCellCode (none : Option Bool)))) =
        List.append (logicalCellListCode [none])
          (List.append headMarkerCells
            (List.append (logicalCellCode (some bit))
              (logicalCellListCode (List.append (rest.map some) [none]))))
      simp [logicalCellListBits, List.append_assoc]

/-- Encoded logical-tape segment for a guarded blank tape. -/
def guardedBlankLogicalTapeCode : List (Option Bool) :=
  guardedInputWordLogicalTapeCode []

theorem guardedBlankLogicalTapeCode_eq_logicalTapeCode :
    guardedBlankLogicalTapeCode =
      logicalTapeCode (guardLogicalTape Tape.blank) := by
  rfl

/--
Explicit physical cells for the narrowed input-tape embedding emitter target.
-/
def structured3InputEmbeddingEmitterTargetCells
    (bits : Word Bool) : List (Option Bool) :=
  List.append tapeSeparatorCells
    (List.append (guardedInputWordLogicalTapeCode bits)
      (List.append tapeSeparatorCells
        (List.append guardedBlankLogicalTapeCode
          (List.append tapeSeparatorCells
            (List.append guardedBlankLogicalTapeCode
              tapeSeparatorCells)))))

theorem structured3InputEmbeddingEmitterTargetCells_eq
    (bits : Word Bool) :
    structured3InputEmbeddingEmitterTargetCells bits =
      Tape.cells
        (structured3InputMaterializerTargetTape
          (Tape.input bits) Tape.blank) := by
  rw [structured3InputEmbeddingEmitterTargetCells,
    guardedInputWordLogicalTapeCode_eq_logicalTapeCode,
    guardedBlankLogicalTapeCode_eq_logicalTapeCode,
    structured3InputMaterializerTargetTape,
    encodedGuardedStructured3Tapes_cells]

/-- Exact tape represented by the explicit input-embedding target cells. -/
def structured3InputEmbeddingEmitterTargetTape
    (bits : Word Bool) : Tape Bool :=
  tapeAtCells [] (structured3InputEmbeddingEmitterTargetCells bits)

theorem structured3InputEmbeddingEmitterTargetTape_eq_materializerTarget
    (bits : Word Bool) :
    structured3InputEmbeddingEmitterTargetTape bits =
      structured3InputMaterializerTargetTape
        (Tape.input bits) Tape.blank := by
  unfold structured3InputEmbeddingEmitterTargetTape
  unfold structured3InputEmbeddingEmitterTargetCells
  rw [guardedInputWordLogicalTapeCode_eq_logicalTapeCode]
  rw [guardedBlankLogicalTapeCode_eq_logicalTapeCode]
  rfl

/--
Control state for the stream-expansion phase below the narrowed shared
embedding emitter.

The phase needs to distinguish the initial blank of {lit}`Tape.input []` from
the blank just to the right of a nonempty input word.
-/
inductive OptionCellExpandAppendScanState where
  | fresh
  | afterBit
  deriving DecidableEq, Repr

/-- Static cells written before scanning the public input word. -/
def optionCellExpandAppendPrefixCells : List (Option Bool) :=
  List.append tapeSeparatorCells
    (List.append (logicalCellCode (none : Option Bool)) headMarkerCells)

/-- Physical cells emitted for one scanned public input bit. -/
def optionCellExpandAppendBitCells (bit : Bool) : List (Option Bool) :=
  logicalCellCode (some bit)

/--
Physical cells emitted from the scanned input window before the right guard.
The empty source word contributes the blank head cell of {lit}`Tape.input []`;
the nonempty source word contributes the logical-cell code of each input bit.
-/
def optionCellExpandAppendScannedCells
    (bits : Word Bool) : List (Option Bool) :=
  match bits with
  | [] => logicalCellCode (none : Option Bool)
  | bit :: rest =>
      List.append (optionCellExpandAppendBitCells bit)
        (logicalCellListCode (rest.map some))

/-- Right guard after the public input logical-tape segment. -/
def optionCellExpandAppendRightGuardCells : List (Option Bool) :=
  logicalCellCode (none : Option Bool)

/-- Static suffix for blank scratch tape, blank output tape, and final separator. -/
def optionCellExpandAppendSuffixCells : List (Option Bool) :=
  List.append tapeSeparatorCells
    (List.append guardedBlankLogicalTapeCode
      (List.append tapeSeparatorCells
        (List.append guardedBlankLogicalTapeCode tapeSeparatorCells)))

/--
Exact physical target for the option-cell expansion primitive.

The expansion primitive writes these cells and rewinds to the first separator.
This target is shared by the FuelSimulator materializer's embedding emitter.
-/
def optionCellExpandAppendTargetCells
    (bits : Word Bool) : List (Option Bool) :=
  List.append optionCellExpandAppendPrefixCells
    (List.append (optionCellExpandAppendScannedCells bits)
      (List.append optionCellExpandAppendRightGuardCells
        optionCellExpandAppendSuffixCells))

theorem optionCellExpandAppendTargetCells_eq_structured3
    (bits : Word Bool) :
    optionCellExpandAppendTargetCells bits =
      structured3InputEmbeddingEmitterTargetCells bits := by
  cases bits with
  | nil =>
      rfl
  | cons bit rest =>
      simp [optionCellExpandAppendTargetCells,
        structured3InputEmbeddingEmitterTargetCells,
        optionCellExpandAppendPrefixCells,
        optionCellExpandAppendScannedCells,
        optionCellExpandAppendRightGuardCells,
        optionCellExpandAppendSuffixCells,
        guardedInputWordLogicalTapeCode,
        optionCellExpandAppendBitCells,
        guardedBlankLogicalTapeCode, List.append_assoc]

/--
Concrete run contract for the option-cell expansion primitive below the shared
embedding emitter.
-/
structure OptionCellExpandAppendRunSpec
    (emitter : MachineDescription) : Prop where
  ready : emitter.SubroutineReady
  forward :
    forall bits : Word Bool,
      emitter.HaltsFromTape
        (Tape.input bits)
        (tapeAtCells [] (optionCellExpandAppendTargetCells bits))

end StructuredConstructionTargets

end Computability
end FoC
