import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.LiveTail.EmitterRuns
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.ThreeTapeHelpers

set_option doc.verso true

/-!
# Structured live-tail emitter components

This module starts the three-logical-tape implementation path for the assembly
live-tail emitter.  It keeps the rows in the current lowerer-facing
three-tape fragment while proving reusable phase runs that the full emitter can
compose later.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncodedRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

private abbrev structuredRow :=
  Structured.MultiTapeLowering.ThreeTape.row

private abbrev structuredStay :=
  Structured.MultiTapeLowering.ThreeTape.keepS

private def structuredPreserve
    (move : Structured.HeadMove) : Structured.TapeAction :=
  match move with
  | Structured.HeadMove.stay =>
      Structured.MultiTapeLowering.ThreeTape.keepS
  | Structured.HeadMove.left =>
      Structured.MultiTapeLowering.ThreeTape.keepL
  | Structured.HeadMove.right =>
      Structured.MultiTapeLowering.ThreeTape.keepR

private def structuredWriteBit
    (bit : Bool) (move : Structured.HeadMove) :
    Structured.TapeAction :=
  match move with
  | Structured.HeadMove.stay =>
      Structured.MultiTapeLowering.ThreeTape.writeS (some bit)
  | Structured.HeadMove.left =>
      Structured.MultiTapeLowering.ThreeTape.writeBitL bit
  | Structured.HeadMove.right =>
      Structured.MultiTapeLowering.ThreeTape.writeBitR bit

private def structuredAnyReadRows
    (mkRow : Option Bool -> Structured.Transition) :
    List Structured.Transition :=
  [ mkRow none, mkRow (some false), mkRow (some true) ]

private def structuredAnySourceScratchReadRows
    (mkRow : Option Bool -> Option Bool -> Structured.Transition) :
    List Structured.Transition :=
  [ mkRow none none
  , mkRow none (some false)
  , mkRow none (some true)
  , mkRow (some false) none
  , mkRow (some false) (some false)
  , mkRow (some false) (some true)
  , mkRow (some true) none
  , mkRow (some true) (some false)
  , mkRow (some true) (some true) ]

private def structuredLiveTailPreserveWriteOutputRow
    (source target : Nat) (sourceRead scratchRead : Option Bool)
    (bit : Bool) : Structured.Transition :=
  structuredRow source sourceRead scratchRead none
    structuredStay
    structuredStay
    (structuredWriteBit bit Structured.HeadMove.right)
    target

private def structuredLiveTailPreserveWriteOutputRows
    (source target : Nat) (bit : Bool) : List Structured.Transition :=
  structuredAnySourceScratchReadRows fun sourceRead scratchRead =>
    structuredLiveTailPreserveWriteOutputRow source target sourceRead
      scratchRead bit

private def structuredMixedOptionCellQuoteLiveTailHeaderBits :
    Word Bool :=
  [false, false, false, false]

def structuredMixedOptionCellQuoteLiveTailOutputTape
    (bits : Word Bool) : Tape Bool :=
  Structured.MultiTapeLowering.ThreeTape.outputFromBits bits

/--
Three-tape structured emitter for the fixed header code symbol.

The source and scratch tapes are preserved; tape 2 receives
{name}`encodeCodeSymbolAsInput` for {name}`MachineCodeSymbol.header`.
-/
def structuredMixedOptionCellQuoteLiveTailHeaderEmitterDescription :
    Structured.Description :=
  Structured.MultiTapeLowering.ThreeTape.description 100 0 99
    (structuredLiveTailPreserveWriteOutputRows 0 1 false ++
      structuredLiveTailPreserveWriteOutputRows 1 2 false ++
      structuredLiveTailPreserveWriteOutputRows 2 3 false ++
      structuredLiveTailPreserveWriteOutputRows 3 99 false)

theorem structuredMixedOptionCellQuoteLiveTailHeaderEmitterDescription_supportsReadWriteRows3 :
    Structured.MultiTapeLowering.supportsReadWriteRows3
      structuredMixedOptionCellQuoteLiveTailHeaderEmitterDescription =
        true := by
  decide

theorem structuredMixedOptionCellQuoteLiveTailHeaderEmitterDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredMixedOptionCellQuoteLiveTailHeaderEmitterDescription :=
  Structured.MultiTapeLowering.supportedReadWriteRows3_of_supports_eq_true
    structuredMixedOptionCellQuoteLiveTailHeaderEmitterDescription_supportsReadWriteRows3

def structuredMixedOptionCellQuoteLiveTailHeaderConfig
    (state : Nat) (source scratch : Tape Bool) (outputBits : Word Bool) :
    Structured.Configuration :=
  Structured.MultiTapeLowering.ThreeTape.config state
    source scratch
    (structuredMixedOptionCellQuoteLiveTailOutputTape outputBits)

theorem structuredMixedOptionCellQuoteLiveTailHeaderBits_eq :
    structuredMixedOptionCellQuoteLiveTailHeaderBits =
      encodeCodeSymbolAsInput MachineCodeSymbol.header := by
  rfl

theorem structuredMixedOptionCellQuoteLiveTailHeaderEmitterDescription_run
    (source scratch : Tape Bool) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailHeaderEmitterDescription.runConfig
        4
        (structuredMixedOptionCellQuoteLiveTailHeaderConfig
          0 source scratch outputBits) =
      structuredMixedOptionCellQuoteLiveTailHeaderConfig
        structuredMixedOptionCellQuoteLiveTailHeaderEmitterDescription.halt
        source scratch
        (List.append outputBits
          structuredMixedOptionCellQuoteLiveTailHeaderBits) := by
  cases source with
  | mk sourceLeft sourceHead sourceRight =>
      cases scratch with
      | mk scratchLeft scratchHead scratchRight =>
          cases sourceHead with
          | none =>
              cases scratchHead with
              | none =>
                  simp [structuredMixedOptionCellQuoteLiveTailHeaderEmitterDescription,
                    structuredMixedOptionCellQuoteLiveTailHeaderConfig,
                    structuredMixedOptionCellQuoteLiveTailOutputTape,
                    structuredMixedOptionCellQuoteLiveTailHeaderBits,
                    structuredLiveTailPreserveWriteOutputRows,
                    structuredLiveTailPreserveWriteOutputRow,
                    structuredAnySourceScratchReadRows,
                    structuredWriteBit,
                    Structured.MultiTapeLowering.ThreeTape.description,
                    Structured.MultiTapeLowering.ThreeTape.config,
                    Structured.MultiTapeLowering.ThreeTape.outputFromBits,
                    Structured.Description.runConfig,
                    Structured.Description.stepConfig,
                    Structured.Description.lookupTransition,
                    Structured.Description.Matches,
                    Structured.TapeAction.stay,
                    Structured.TapeAction.apply, Structured.HeadMove.apply,
                    Tape.read, Tape.write, Tape.move, Tape.moveRight,
                    List.reverse_append]
              | some scratchBit =>
                  cases scratchBit <;>
                    simp [structuredMixedOptionCellQuoteLiveTailHeaderEmitterDescription,
                      structuredMixedOptionCellQuoteLiveTailHeaderConfig,
                      structuredMixedOptionCellQuoteLiveTailOutputTape,
                      structuredMixedOptionCellQuoteLiveTailHeaderBits,
                      structuredLiveTailPreserveWriteOutputRows,
                      structuredLiveTailPreserveWriteOutputRow,
                      structuredAnySourceScratchReadRows,
                      structuredWriteBit,
                      Structured.MultiTapeLowering.ThreeTape.description,
                      Structured.MultiTapeLowering.ThreeTape.config,
                      Structured.MultiTapeLowering.ThreeTape.outputFromBits,
                      Structured.Description.runConfig,
                      Structured.Description.stepConfig,
                      Structured.Description.lookupTransition,
                      Structured.Description.Matches,
                      Structured.TapeAction.stay,
                      Structured.TapeAction.apply, Structured.HeadMove.apply,
                      Tape.read, Tape.write, Tape.move, Tape.moveRight,
                      List.reverse_append]
          | some sourceBit =>
              cases sourceBit <;>
                cases scratchHead with
                | none =>
                    simp [structuredMixedOptionCellQuoteLiveTailHeaderEmitterDescription,
                      structuredMixedOptionCellQuoteLiveTailHeaderConfig,
                      structuredMixedOptionCellQuoteLiveTailOutputTape,
                      structuredMixedOptionCellQuoteLiveTailHeaderBits,
                      structuredLiveTailPreserveWriteOutputRows,
                      structuredLiveTailPreserveWriteOutputRow,
                      structuredAnySourceScratchReadRows,
                      structuredWriteBit,
                      Structured.MultiTapeLowering.ThreeTape.description,
                      Structured.MultiTapeLowering.ThreeTape.config,
                      Structured.MultiTapeLowering.ThreeTape.outputFromBits,
                      Structured.Description.runConfig,
                      Structured.Description.stepConfig,
                      Structured.Description.lookupTransition,
                      Structured.Description.Matches,
                      Structured.TapeAction.stay,
                      Structured.TapeAction.apply, Structured.HeadMove.apply,
                      Tape.read, Tape.write, Tape.move, Tape.moveRight,
                      List.reverse_append]
                | some scratchBit =>
                    cases scratchBit <;>
                      simp [structuredMixedOptionCellQuoteLiveTailHeaderEmitterDescription,
                        structuredMixedOptionCellQuoteLiveTailHeaderConfig,
                        structuredMixedOptionCellQuoteLiveTailOutputTape,
                        structuredMixedOptionCellQuoteLiveTailHeaderBits,
                        structuredLiveTailPreserveWriteOutputRows,
                        structuredLiveTailPreserveWriteOutputRow,
                        structuredAnySourceScratchReadRows,
                        structuredWriteBit,
                        Structured.MultiTapeLowering.ThreeTape.description,
                        Structured.MultiTapeLowering.ThreeTape.config,
                        Structured.MultiTapeLowering.ThreeTape.outputFromBits,
                        Structured.Description.runConfig,
                        Structured.Description.stepConfig,
                        Structured.Description.lookupTransition,
                        Structured.Description.Matches,
                        Structured.TapeAction.stay,
                        Structured.TapeAction.apply, Structured.HeadMove.apply,
                        Tape.read, Tape.write, Tape.move, Tape.moveRight,
                        List.reverse_append]

private def structuredLiveTailCellPassInitialRow
    (read : Bool) (target : Nat) : Structured.Transition :=
  structuredRow 0 (some read) none none
    (structuredPreserve Structured.HeadMove.right)
    structuredStay
    (structuredWriteBit false Structured.HeadMove.right)
    target

private def structuredLiveTailCellPassWriteRow
    (source : Nat) (sourceRead : Option Bool) (bit : Bool)
    (target : Nat) : Structured.Transition :=
  structuredRow source sourceRead none none
    structuredStay
    structuredStay
    (structuredWriteBit bit Structured.HeadMove.right)
    target

private def structuredLiveTailCellPassWriteRows
    (source : Nat) (bit : Bool) (target : Nat) :
    List Structured.Transition :=
  structuredAnyReadRows fun sourceRead =>
    structuredLiveTailCellPassWriteRow source sourceRead bit target

private def structuredLiveTailCellPassHaltRow :
    Structured.Transition :=
  structuredRow 0 none none none
    structuredStay
    structuredStay
    structuredStay
    99

/--
Three-tape structured cell-pass emitter for quoted Boolean cells.

Tape 0 scans the bits to quote, tape 1 is reserved scratch, and tape 2 receives
{name}`preservingCellPassCellBits` at its current blank.  The table is
intentionally kept in the three-read/three-action row fragment accepted by
{name}`Structured.MultiTapeLowering.supportsReadWriteRows3`.
-/
def structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription :
    Structured.Description :=
  Structured.MultiTapeLowering.ThreeTape.description 100 0 99
    ([ structuredLiveTailCellPassInitialRow false 10
     , structuredLiveTailCellPassInitialRow true 20
     , structuredLiveTailCellPassHaltRow ] ++
      structuredLiveTailCellPassWriteRows 10 true 11 ++
      structuredLiveTailCellPassWriteRows 11 false 12 ++
      structuredLiveTailCellPassWriteRows 12 true 0 ++
      structuredLiveTailCellPassWriteRows 20 true 21 ++
      structuredLiveTailCellPassWriteRows 21 true 22 ++
      structuredLiveTailCellPassWriteRows 22 false 0)

theorem structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_supportsReadWriteRows3 :
    Structured.MultiTapeLowering.supportsReadWriteRows3
      structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription =
        true := by
  decide

theorem structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription :=
  Structured.MultiTapeLowering.supportedReadWriteRows3_of_supports_eq_true
    structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_supportsReadWriteRows3

def structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
    (processedRev remaining : Word Bool) : Tape Bool :=
  tapeAtCells (List.append (processedRev.map some) [none])
    (List.append (remaining.map some) [none])

def structuredMixedOptionCellQuoteLiveTailScratchTape : Tape Bool :=
  Tape.blank

def structuredMixedOptionCellQuoteLiveTailCellPassConfig
    (state : Nat) (processedRev remaining outputBits : Word Bool) :
    Structured.Configuration :=
  Structured.MultiTapeLowering.ThreeTape.config state
    (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
      processedRev remaining)
    structuredMixedOptionCellQuoteLiveTailScratchTape
    (structuredMixedOptionCellQuoteLiveTailOutputTape outputBits)

private def structuredMixedOptionCellQuoteLiveTailCellChunkBits
    (bit : Bool) : Word Bool :=
  if bit then preservingCellPassOneBits else preservingCellPassZeroBits

theorem structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run_bit
    (bit : Bool) (processedRev rest outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.runConfig
        4
        (structuredMixedOptionCellQuoteLiveTailCellPassConfig
          0 processedRev (bit :: rest) outputBits) =
      structuredMixedOptionCellQuoteLiveTailCellPassConfig
        0 (bit :: processedRev) rest
        (List.append outputBits
          (structuredMixedOptionCellQuoteLiveTailCellChunkBits bit)) := by
  cases bit <;> cases rest <;> (try cases ‹Bool›) <;>
    simp [structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription,
      structuredMixedOptionCellQuoteLiveTailCellPassConfig,
      structuredMixedOptionCellQuoteLiveTailCellPassSourceTape,
      structuredMixedOptionCellQuoteLiveTailScratchTape,
      structuredMixedOptionCellQuoteLiveTailOutputTape,
      structuredMixedOptionCellQuoteLiveTailCellChunkBits,
      preservingCellPassZeroBits, preservingCellPassOneBits,
      structuredLiveTailCellPassInitialRow,
      structuredLiveTailCellPassWriteRows,
      structuredLiveTailCellPassWriteRow,
      structuredLiveTailCellPassHaltRow,
      structuredAnyReadRows,
      structuredPreserve, structuredWriteBit,
      Structured.MultiTapeLowering.ThreeTape.description,
      Structured.MultiTapeLowering.ThreeTape.config,
      Structured.MultiTapeLowering.ThreeTape.outputFromBits,
      Structured.Description.runConfig,
      Structured.Description.stepConfig,
      Structured.Description.lookupTransition,
      Structured.Description.Matches,
      Structured.TapeAction.stay,
      Structured.TapeAction.apply, Structured.HeadMove.apply,
      Tape.blank, Tape.read, Tape.write, Tape.move, Tape.moveRight,
      tapeAtCells, List.reverse_append]

theorem structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run_done
    (processedRev outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.runConfig
        1
        (structuredMixedOptionCellQuoteLiveTailCellPassConfig
          0 processedRev [] outputBits) =
      structuredMixedOptionCellQuoteLiveTailCellPassConfig
        structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.halt
        processedRev [] outputBits := by
  simp [structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription,
    structuredMixedOptionCellQuoteLiveTailCellPassConfig,
    structuredMixedOptionCellQuoteLiveTailCellPassSourceTape,
    structuredMixedOptionCellQuoteLiveTailScratchTape,
    structuredMixedOptionCellQuoteLiveTailOutputTape,
    structuredLiveTailCellPassInitialRow,
    structuredLiveTailCellPassWriteRows,
    structuredLiveTailCellPassWriteRow,
    structuredLiveTailCellPassHaltRow,
    structuredAnyReadRows,
    structuredPreserve, structuredWriteBit,
    Structured.MultiTapeLowering.ThreeTape.description,
    Structured.MultiTapeLowering.ThreeTape.config,
    Structured.MultiTapeLowering.ThreeTape.outputFromBits,
    Structured.Description.runConfig,
    Structured.Description.stepConfig,
    Structured.Description.lookupTransition,
    Structured.Description.Matches,
    Structured.TapeAction.stay,
    Structured.TapeAction.apply, Structured.HeadMove.apply,
    Tape.blank, Tape.read, tapeAtCells]

theorem structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run_loop
    (processedRev remaining outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.runConfig
        (4 * remaining.length + 1)
        (structuredMixedOptionCellQuoteLiveTailCellPassConfig
          0 processedRev remaining outputBits) =
      structuredMixedOptionCellQuoteLiveTailCellPassConfig
        structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.halt
        (List.append remaining.reverse processedRev)
        []
        (List.append outputBits
          (preservingCellPassCellBits remaining)) := by
  induction remaining generalizing processedRev outputBits with
  | nil =>
      simpa [preservingCellPassCellBits] using
        structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run_done
          processedRev outputBits
  | cons bit rest ih =>
      refine
        Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
          (D := structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription)
          (m := 4 * rest.length + 1)
          (htotal := ?_)
          (structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run_bit
            bit processedRev rest outputBits)
          ?_
      · simp
        lia
      cases bit
      · simpa [structuredMixedOptionCellQuoteLiveTailCellChunkBits,
          preservingCellPassCellBits,
          preservingCellPassZeroBits,
          preservingCellPassOneBits,
          List.append_assoc] using
          ih (false :: processedRev)
            (List.append outputBits
              (structuredMixedOptionCellQuoteLiveTailCellChunkBits false))
      · simpa [structuredMixedOptionCellQuoteLiveTailCellChunkBits,
          preservingCellPassCellBits,
          preservingCellPassZeroBits,
          preservingCellPassOneBits,
          List.append_assoc] using
          ih (true :: processedRev)
            (List.append outputBits
              (structuredMixedOptionCellQuoteLiveTailCellChunkBits true))

theorem structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run
    (bits outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.runConfig
        (4 * bits.length + 1)
        (structuredMixedOptionCellQuoteLiveTailCellPassConfig
          0 [] bits outputBits) =
      structuredMixedOptionCellQuoteLiveTailCellPassConfig
        structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.halt
        bits.reverse
        []
        (List.append outputBits
          (preservingCellPassCellBits bits)) := by
  simpa using
    structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run_loop
      [] bits outputBits

theorem structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run_assemblyPrefix
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.runConfig
        (4 *
            (assemblySourceRestFinishSourcePrefixBits p.w p.stage).length +
          1)
        (structuredMixedOptionCellQuoteLiveTailCellPassConfig
          0 [] (assemblySourceRestFinishSourcePrefixBits p.w p.stage)
          (assemblySourceRestFinishLengthHeaderBits
            p.w p.sourceRestBits p.stage)) =
      structuredMixedOptionCellQuoteLiveTailCellPassConfig
        structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription.halt
        (assemblySourceRestFinishSourcePrefixBits p.w p.stage).reverse
        []
        (assemblySourceRestLiveTailEmitterEmittedPrefix p) := by
  rw [assemblySourceRestLiveTailEmitterEmittedPrefix,
    assemblySourceRestFinishPrefixQuoteOutputBits,
    assemblySourceRestFinishQuotedPrefixBits]
  exact
    structuredMixedOptionCellQuoteLiveTailCellPassEmitterDescription_run
      (assemblySourceRestFinishSourcePrefixBits p.w p.stage)
      (assemblySourceRestFinishLengthHeaderBits
        p.w p.sourceRestBits p.stage)

private def structuredLiveTailCountRow
    (read : Bool) : Structured.Transition :=
  structuredRow 0 (some read) none none
    (structuredPreserve Structured.HeadMove.right)
    (structuredWriteBit true Structured.HeadMove.right)
    structuredStay
    0

private def structuredLiveTailCountDoneRow :
    Structured.Transition :=
  structuredRow 0 none none none
    structuredStay
    (structuredPreserve Structured.HeadMove.left)
    structuredStay
    99

/--
Three-tape structured counter for a Boolean segment on tape 0.

Each scanned source bit advances tape 0 and appends one marker to tape 1.
The output tape is untouched.  The done row moves tape 1 left onto the last
marker, matching the orientation needed by later unary-header emission phases.
-/
def structuredMixedOptionCellQuoteLiveTailCountDescription :
    Structured.Description :=
  Structured.MultiTapeLowering.ThreeTape.description 100 0 99
    [ structuredLiveTailCountRow false
    , structuredLiveTailCountRow true
    , structuredLiveTailCountDoneRow ]

theorem structuredMixedOptionCellQuoteLiveTailCountDescription_supportsReadWriteRows3 :
    Structured.MultiTapeLowering.supportsReadWriteRows3
      structuredMixedOptionCellQuoteLiveTailCountDescription = true := by
  decide

theorem structuredMixedOptionCellQuoteLiveTailCountDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredMixedOptionCellQuoteLiveTailCountDescription :=
  Structured.MultiTapeLowering.supportedReadWriteRows3_of_supports_eq_true
    structuredMixedOptionCellQuoteLiveTailCountDescription_supportsReadWriteRows3

def structuredMixedOptionCellQuoteLiveTailCountMarkerTape
    (markers : Nat) : Tape Bool :=
  Structured.MultiTapeLowering.ThreeTape.markerScratch markers

def structuredMixedOptionCellQuoteLiveTailCountReadTape
    (markers : Nat) : Tape Bool :=
  Tape.move Direction.left
    (structuredMixedOptionCellQuoteLiveTailCountMarkerTape markers)

def structuredMixedOptionCellQuoteLiveTailCountConfig
    (state : Nat) (processedRev remaining : Word Bool)
    (markers : Nat) (outputBits : Word Bool) :
    Structured.Configuration :=
  Structured.MultiTapeLowering.ThreeTape.config state
    (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
      processedRev remaining)
    (structuredMixedOptionCellQuoteLiveTailCountMarkerTape markers)
    (structuredMixedOptionCellQuoteLiveTailOutputTape outputBits)

def structuredMixedOptionCellQuoteLiveTailCountDoneConfig
    (processedRev : Word Bool) (markers : Nat)
    (outputBits : Word Bool) : Structured.Configuration :=
  Structured.MultiTapeLowering.ThreeTape.config
    structuredMixedOptionCellQuoteLiveTailCountDescription.halt
    (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
      processedRev [])
    (structuredMixedOptionCellQuoteLiveTailCountReadTape markers)
    (structuredMixedOptionCellQuoteLiveTailOutputTape outputBits)

theorem structuredMixedOptionCellQuoteLiveTailCountDescription_run_bit
    (bit : Bool) (processedRev rest : Word Bool)
    (markers : Nat) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCountDescription.runConfig 1
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 processedRev (bit :: rest) markers outputBits) =
      structuredMixedOptionCellQuoteLiveTailCountConfig
        0 (bit :: processedRev) rest markers.succ outputBits := by
  cases bit <;> cases rest <;> (try cases ‹Bool›) <;>
    simp [structuredMixedOptionCellQuoteLiveTailCountDescription,
      structuredMixedOptionCellQuoteLiveTailCountConfig,
      structuredMixedOptionCellQuoteLiveTailCellPassSourceTape,
      structuredMixedOptionCellQuoteLiveTailCountMarkerTape,
      structuredMixedOptionCellQuoteLiveTailOutputTape,
      structuredLiveTailCountRow,
      structuredLiveTailCountDoneRow,
      structuredPreserve, structuredWriteBit,
      Structured.MultiTapeLowering.ThreeTape.description,
      Structured.MultiTapeLowering.ThreeTape.config,
      Structured.MultiTapeLowering.ThreeTape.markerScratch,
      Structured.MultiTapeLowering.ThreeTape.outputFromBits,
      Structured.Description.runConfig,
      Structured.Description.stepConfig,
      Structured.Description.lookupTransition,
      Structured.Description.Matches,
      Structured.TapeAction.stay,
      Structured.TapeAction.apply, Structured.HeadMove.apply,
      Tape.read, Tape.write, Tape.move, Tape.moveRight,
      tapeAtCells, List.replicate_succ]

theorem structuredMixedOptionCellQuoteLiveTailCountDescription_run_done
    (processedRev : Word Bool) (markers : Nat) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCountDescription.runConfig 1
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 processedRev [] markers outputBits) =
      structuredMixedOptionCellQuoteLiveTailCountDoneConfig
        processedRev markers outputBits := by
  cases markers with
  | zero =>
      simp [structuredMixedOptionCellQuoteLiveTailCountDescription,
        structuredMixedOptionCellQuoteLiveTailCountConfig,
        structuredMixedOptionCellQuoteLiveTailCountDoneConfig,
        structuredMixedOptionCellQuoteLiveTailCellPassSourceTape,
        structuredMixedOptionCellQuoteLiveTailCountMarkerTape,
        structuredMixedOptionCellQuoteLiveTailCountReadTape,
        structuredMixedOptionCellQuoteLiveTailOutputTape,
        structuredLiveTailCountRow,
        structuredLiveTailCountDoneRow,
        structuredPreserve, structuredWriteBit,
        Structured.MultiTapeLowering.ThreeTape.description,
        Structured.MultiTapeLowering.ThreeTape.config,
        Structured.MultiTapeLowering.ThreeTape.markerScratch,
        Structured.MultiTapeLowering.ThreeTape.outputFromBits,
        Structured.Description.runConfig,
        Structured.Description.stepConfig,
        Structured.Description.lookupTransition,
      Structured.Description.Matches,
      Structured.TapeAction.stay,
      Structured.TapeAction.apply, Structured.HeadMove.apply,
      Tape.read, Tape.move, Tape.moveLeft,
      tapeAtCells]
  | succ markers =>
      simp [structuredMixedOptionCellQuoteLiveTailCountDescription,
        structuredMixedOptionCellQuoteLiveTailCountConfig,
        structuredMixedOptionCellQuoteLiveTailCountDoneConfig,
        structuredMixedOptionCellQuoteLiveTailCellPassSourceTape,
        structuredMixedOptionCellQuoteLiveTailCountMarkerTape,
        structuredMixedOptionCellQuoteLiveTailCountReadTape,
        structuredMixedOptionCellQuoteLiveTailOutputTape,
        structuredLiveTailCountRow,
        structuredLiveTailCountDoneRow,
        structuredPreserve, structuredWriteBit,
        Structured.MultiTapeLowering.ThreeTape.description,
        Structured.MultiTapeLowering.ThreeTape.config,
        Structured.MultiTapeLowering.ThreeTape.markerScratch,
        Structured.MultiTapeLowering.ThreeTape.outputFromBits,
        Structured.Description.runConfig,
        Structured.Description.stepConfig,
        Structured.Description.lookupTransition,
      Structured.Description.Matches,
      Structured.TapeAction.stay,
      Structured.TapeAction.apply, Structured.HeadMove.apply,
      Tape.read, Tape.move, Tape.moveLeft,
      tapeAtCells, List.replicate_succ]

theorem structuredMixedOptionCellQuoteLiveTailCountDescription_run_loop
    (processedRev remaining : Word Bool) (markers : Nat)
    (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCountDescription.runConfig
        (remaining.length + 1)
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 processedRev remaining markers outputBits) =
      structuredMixedOptionCellQuoteLiveTailCountDoneConfig
        (List.append remaining.reverse processedRev)
        (markers + remaining.length)
        outputBits := by
  induction remaining generalizing processedRev markers with
  | nil =>
      simpa using
        structuredMixedOptionCellQuoteLiveTailCountDescription_run_done
          processedRev markers outputBits
  | cons bit rest ih =>
      refine
        Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
          (D := structuredMixedOptionCellQuoteLiveTailCountDescription)
          (n := 1)
          (m := rest.length + 1)
          (htotal := ?_)
          (structuredMixedOptionCellQuoteLiveTailCountDescription_run_bit
            bit processedRev rest markers outputBits)
          ?_
      · simp [Nat.add_comm, Nat.add_left_comm]
      · have hmarkers :
            markers.succ + rest.length =
              markers + (rest.length + 1) := by
          simp [Nat.succ_eq_add_one, Nat.add_comm,
            Nat.add_left_comm]
        simpa [Nat.succ_eq_add_one, hmarkers, List.append_assoc] using
          ih (bit :: processedRev) markers.succ

theorem structuredMixedOptionCellQuoteLiveTailCountDescription_run
    (bits outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCountDescription.runConfig
        (bits.length + 1)
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 [] bits 0 outputBits) =
      structuredMixedOptionCellQuoteLiveTailCountDoneConfig
        bits.reverse bits.length outputBits := by
  simpa using
    structuredMixedOptionCellQuoteLiveTailCountDescription_run_loop
      [] bits 0 outputBits

private def structuredLiveTailWriteOutputRow
    (source target : Nat) (sourceRead tape1Read : Option Bool)
    (bit : Bool) (tape1Action : Structured.TapeAction) :
    Structured.Transition :=
  structuredRow source sourceRead tape1Read none
    structuredStay
    tape1Action
    (structuredWriteBit bit Structured.HeadMove.right)
    target

private def structuredLiveTailLengthMarkerRows
    (source target : Nat) (bit : Bool)
    (moveTape1 : Structured.HeadMove := Structured.HeadMove.stay) :
    List Structured.Transition :=
  structuredAnyReadRows fun sourceRead =>
    structuredLiveTailWriteOutputRow source target sourceRead (some true)
      bit (structuredPreserve moveTape1)

private def structuredLiveTailLengthFinalRows
    (source target : Nat) (bit : Bool) :
    List Structured.Transition :=
  structuredAnyReadRows fun sourceRead =>
    structuredLiveTailWriteOutputRow source target sourceRead none bit
      structuredStay

private def structuredMixedOptionCellQuoteLiveTailLengthTickBits :
    Word Bool :=
  [false, false, true, false]

private def structuredMixedOptionCellQuoteLiveTailLengthDoneBits :
    Word Bool :=
  [false, false, true, true]

/--
Three-tape structured emitter for {lit}`stageNatBits n` from unary scratch
markers.

Tape 1 starts on the rightmost marker produced by the counter phase.  Each
marker emits one tick symbol and moves left; the blank to the left of the
marker block emits the final done symbol.
-/
def structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription :
    Structured.Description :=
  Structured.MultiTapeLowering.ThreeTape.description 100 0 99
    (structuredLiveTailLengthMarkerRows 0 1 false ++
      structuredLiveTailLengthMarkerRows 1 2 false ++
      structuredLiveTailLengthMarkerRows 2 3 true ++
      structuredLiveTailLengthMarkerRows 3 0 false
        Structured.HeadMove.left ++
      structuredLiveTailLengthFinalRows 0 11 false ++
      structuredLiveTailLengthFinalRows 11 12 false ++
      structuredLiveTailLengthFinalRows 12 13 true ++
      structuredLiveTailLengthFinalRows 13 99 true)

theorem structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription_supportsReadWriteRows3 :
    Structured.MultiTapeLowering.supportsReadWriteRows3
      structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription =
        true := by
  decide

theorem structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription :=
  Structured.MultiTapeLowering.supportedReadWriteRows3_of_supports_eq_true
    structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription_supportsReadWriteRows3

def structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape
    (markers : Nat) : Tape Bool :=
  tapeAtCells []
    (none ::
      List.append (List.replicate markers (some true)) [none])

def structuredMixedOptionCellQuoteLiveTailLengthPhaseTape
    (remaining emitted : Nat) : Tape Bool :=
  match remaining with
  | 0 => structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape emitted
  | remaining' + 1 =>
      tapeAtCells (List.replicate remaining' (some true))
        (some true ::
          List.append (List.replicate emitted (some true)) [none])

def structuredMixedOptionCellQuoteLiveTailLengthConfig
    (state : Nat) (source : Tape Bool) (remaining emitted : Nat)
    (outputBits : Word Bool) : Structured.Configuration :=
  Structured.MultiTapeLowering.ThreeTape.config state
    source
    (structuredMixedOptionCellQuoteLiveTailLengthPhaseTape
      remaining emitted)
    (structuredMixedOptionCellQuoteLiveTailOutputTape outputBits)

theorem structuredMixedOptionCellQuoteLiveTailCountReadTape_eq_lengthPhaseTape
    (markers : Nat) :
    structuredMixedOptionCellQuoteLiveTailCountReadTape markers =
      structuredMixedOptionCellQuoteLiveTailLengthPhaseTape markers 0 := by
  cases markers <;>
    simp [structuredMixedOptionCellQuoteLiveTailCountReadTape,
      structuredMixedOptionCellQuoteLiveTailCountMarkerTape,
      structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
      structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
      Structured.MultiTapeLowering.ThreeTape.markerScratch,
      Tape.move, Tape.moveLeft, tapeAtCells, List.replicate_succ]

theorem structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription_run_marker
    (remaining emitted : Nat) (source : Tape Bool)
    (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription.runConfig
        4
        (structuredMixedOptionCellQuoteLiveTailLengthConfig
          0 source remaining.succ emitted outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthConfig
        0 source remaining emitted.succ
        (List.append outputBits
          structuredMixedOptionCellQuoteLiveTailLengthTickBits) := by
  cases source with
  | mk left head right =>
      cases head with
      | none =>
          cases remaining <;>
            simp [structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription,
              structuredMixedOptionCellQuoteLiveTailLengthConfig,
              structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
              structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
              structuredMixedOptionCellQuoteLiveTailOutputTape,
              structuredMixedOptionCellQuoteLiveTailLengthTickBits,
              structuredLiveTailLengthMarkerRows,
              structuredLiveTailLengthFinalRows,
              structuredLiveTailWriteOutputRow,
              structuredAnyReadRows,
              structuredPreserve, structuredWriteBit,
              Structured.MultiTapeLowering.ThreeTape.description,
              Structured.MultiTapeLowering.ThreeTape.config,
              Structured.MultiTapeLowering.ThreeTape.outputFromBits,
              Structured.Description.runConfig,
              Structured.Description.stepConfig,
              Structured.Description.lookupTransition,
              Structured.Description.Matches,
              Structured.TapeAction.stay,
              Structured.TapeAction.apply, Structured.HeadMove.apply,
              Tape.read, Tape.write, Tape.move, Tape.moveLeft,
              Tape.moveRight, tapeAtCells, List.replicate_succ,
              List.reverse_append]
      | some bit =>
          cases bit <;> cases remaining <;>
            simp [structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription,
              structuredMixedOptionCellQuoteLiveTailLengthConfig,
              structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
              structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
              structuredMixedOptionCellQuoteLiveTailOutputTape,
              structuredMixedOptionCellQuoteLiveTailLengthTickBits,
              structuredLiveTailLengthMarkerRows,
              structuredLiveTailLengthFinalRows,
              structuredLiveTailWriteOutputRow,
              structuredAnyReadRows,
              structuredPreserve, structuredWriteBit,
              Structured.MultiTapeLowering.ThreeTape.description,
              Structured.MultiTapeLowering.ThreeTape.config,
              Structured.MultiTapeLowering.ThreeTape.outputFromBits,
              Structured.Description.runConfig,
              Structured.Description.stepConfig,
              Structured.Description.lookupTransition,
              Structured.Description.Matches,
              Structured.TapeAction.stay,
              Structured.TapeAction.apply, Structured.HeadMove.apply,
              Tape.read, Tape.write, Tape.move, Tape.moveLeft,
              Tape.moveRight, tapeAtCells, List.replicate_succ,
              List.reverse_append]

theorem structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription_run_final
    (emitted : Nat) (source : Tape Bool) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription.runConfig
        4
        (structuredMixedOptionCellQuoteLiveTailLengthConfig
          0 source 0 emitted outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthConfig
        structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription.halt
        source 0 emitted
        (List.append outputBits
          structuredMixedOptionCellQuoteLiveTailLengthDoneBits) := by
  cases source with
  | mk left head right =>
      cases head with
      | none =>
          simp [structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription,
            structuredMixedOptionCellQuoteLiveTailLengthConfig,
            structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
            structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
            structuredMixedOptionCellQuoteLiveTailOutputTape,
            structuredMixedOptionCellQuoteLiveTailLengthDoneBits,
            structuredLiveTailLengthMarkerRows,
            structuredLiveTailLengthFinalRows,
            structuredLiveTailWriteOutputRow,
            structuredAnyReadRows,
            structuredPreserve, structuredWriteBit,
            Structured.MultiTapeLowering.ThreeTape.description,
            Structured.MultiTapeLowering.ThreeTape.config,
            Structured.MultiTapeLowering.ThreeTape.outputFromBits,
            Structured.Description.runConfig,
            Structured.Description.stepConfig,
            Structured.Description.lookupTransition,
            Structured.Description.Matches,
            Structured.TapeAction.stay,
            Structured.TapeAction.apply, Structured.HeadMove.apply,
            Tape.read, Tape.write, Tape.move, Tape.moveRight,
            tapeAtCells, List.reverse_append]
      | some bit =>
          cases bit <;>
            simp [structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription,
              structuredMixedOptionCellQuoteLiveTailLengthConfig,
              structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
              structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
              structuredMixedOptionCellQuoteLiveTailOutputTape,
              structuredMixedOptionCellQuoteLiveTailLengthDoneBits,
              structuredLiveTailLengthMarkerRows,
              structuredLiveTailLengthFinalRows,
              structuredLiveTailWriteOutputRow,
              structuredAnyReadRows,
              structuredPreserve, structuredWriteBit,
              Structured.MultiTapeLowering.ThreeTape.description,
              Structured.MultiTapeLowering.ThreeTape.config,
              Structured.MultiTapeLowering.ThreeTape.outputFromBits,
              Structured.Description.runConfig,
              Structured.Description.stepConfig,
              Structured.Description.lookupTransition,
              Structured.Description.Matches,
              Structured.TapeAction.stay,
              Structured.TapeAction.apply, Structured.HeadMove.apply,
              Tape.read, Tape.write, Tape.move, Tape.moveRight,
              tapeAtCells, List.reverse_append]

theorem structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription_run_loop
    (remaining emitted : Nat) (source : Tape Bool)
    (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription.runConfig
        (4 * remaining + 4)
        (structuredMixedOptionCellQuoteLiveTailLengthConfig
          0 source remaining emitted outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthConfig
        structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription.halt
        source 0 (emitted + remaining)
        (List.append outputBits
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            remaining)) := by
  induction remaining generalizing emitted outputBits with
  | zero =>
      simpa [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_zero] using
        structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription_run_final
          emitted source outputBits
  | succ remaining ih =>
      refine
        Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
          (D := structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription)
          (m := 4 * remaining + 4)
          (htotal := ?_)
          (structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription_run_marker
            remaining emitted source outputBits)
          ?_
      · lia
      · simpa [structuredMixedOptionCellQuoteLiveTailLengthTickBits,
          DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
          List.append_assoc, Nat.succ_eq_add_one, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using
          ih emitted.succ
            (List.append outputBits
              structuredMixedOptionCellQuoteLiveTailLengthTickBits)

theorem structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription_run
    (markers : Nat) (source : Tape Bool) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription.runConfig
        (4 * markers + 4)
        (structuredMixedOptionCellQuoteLiveTailLengthConfig
          0 source markers 0 outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthConfig
        structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription.halt
        source 0 markers
        (List.append outputBits
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            markers)) := by
  simpa using
    structuredMixedOptionCellQuoteLiveTailLengthEmitterDescription_run_loop
      markers 0 source outputBits

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
