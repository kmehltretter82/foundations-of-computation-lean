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

def structuredPreserve
    (move : Structured.HeadMove) : Structured.TapeAction :=
  match move with
  | Structured.HeadMove.stay =>
      Structured.MultiTapeLowering.ThreeTape.keepS
  | Structured.HeadMove.left =>
      Structured.MultiTapeLowering.ThreeTape.keepL
  | Structured.HeadMove.right =>
      Structured.MultiTapeLowering.ThreeTape.keepR

def structuredWriteBit
    (bit : Bool) (move : Structured.HeadMove) :
    Structured.TapeAction :=
  match move with
  | Structured.HeadMove.stay =>
      Structured.MultiTapeLowering.ThreeTape.writeS (some bit)
  | Structured.HeadMove.left =>
      Structured.MultiTapeLowering.ThreeTape.writeBitL bit
  | Structured.HeadMove.right =>
      Structured.MultiTapeLowering.ThreeTape.writeBitR bit

def structuredAnyReadRows
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

private def structuredAnySourceOutputReadRows
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

def structuredLiveTailCellPassInitialRow
    (read : Bool) (target : Nat) : Structured.Transition :=
  structuredRow 0 (some read) none none
    (structuredPreserve Structured.HeadMove.right)
    structuredStay
    (structuredWriteBit false Structured.HeadMove.right)
    target

def structuredLiveTailCellPassWriteRow
    (source : Nat) (sourceRead : Option Bool) (bit : Bool)
    (target : Nat) : Structured.Transition :=
  structuredRow source sourceRead none none
    structuredStay
    structuredStay
    (structuredWriteBit bit Structured.HeadMove.right)
    target

def structuredLiveTailCellPassWriteRows
    (source : Nat) (bit : Bool) (target : Nat) :
    List Structured.Transition :=
  structuredAnyReadRows fun sourceRead =>
    structuredLiveTailCellPassWriteRow source sourceRead bit target

def structuredLiveTailCellPassHaltRow :
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

def structuredMixedOptionCellQuoteLiveTailCellChunkBits
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

/--
Combined structured length-header phase.

Starting with {lit}`markers` unary cells on tape 1 and output positioned at its
right blank, this phase appends the fixed header symbol followed by
{name}`DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits`
for {lit}`markers`.  Source tape 0 is preserved.
-/
def structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription :
    Structured.Description :=
  Structured.MultiTapeLowering.ThreeTape.description 100 0 99
    (structuredLiveTailPreserveWriteOutputRows 0 1 false ++
      structuredLiveTailPreserveWriteOutputRows 1 2 false ++
      structuredLiveTailPreserveWriteOutputRows 2 3 false ++
      structuredLiveTailPreserveWriteOutputRows 3 10 false ++
      structuredLiveTailLengthMarkerRows 10 11 false ++
      structuredLiveTailLengthMarkerRows 11 12 false ++
      structuredLiveTailLengthMarkerRows 12 13 true ++
      structuredLiveTailLengthMarkerRows 13 10 false
        Structured.HeadMove.left ++
      structuredLiveTailLengthFinalRows 10 21 false ++
      structuredLiveTailLengthFinalRows 21 22 false ++
      structuredLiveTailLengthFinalRows 22 23 true ++
      structuredLiveTailLengthFinalRows 23 99 true)

theorem structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription_supportsReadWriteRows3 :
    Structured.MultiTapeLowering.supportsReadWriteRows3
      structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription =
        true := by
  decide

theorem structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription :=
  Structured.MultiTapeLowering.supportedReadWriteRows3_of_supports_eq_true
    structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription_supportsReadWriteRows3

def structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
    (state : Nat) (source : Tape Bool) (remaining emitted : Nat)
    (outputBits : Word Bool) : Structured.Configuration :=
  Structured.MultiTapeLowering.ThreeTape.config state
    source
    (structuredMixedOptionCellQuoteLiveTailLengthPhaseTape
      remaining emitted)
    (structuredMixedOptionCellQuoteLiveTailOutputTape outputBits)

theorem structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription_run_header
    (source : Tape Bool) (remaining emitted : Nat)
    (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription.runConfig
        4
        (structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
          0 source remaining emitted outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        10 source remaining emitted
        (List.append outputBits
          structuredMixedOptionCellQuoteLiveTailHeaderBits) := by
  cases source with
  | mk sourceLeft sourceHead sourceRight =>
      cases remaining with
      | zero =>
          cases emitted <;>
            cases sourceHead <;> (try cases ‹Bool›) <;>
              simp [structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
                structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
                structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
                structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
                structuredMixedOptionCellQuoteLiveTailOutputTape,
                structuredMixedOptionCellQuoteLiveTailHeaderBits,
                structuredLiveTailPreserveWriteOutputRows,
                structuredLiveTailPreserveWriteOutputRow,
                structuredAnySourceScratchReadRows,
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
                tapeAtCells, List.replicate_succ, List.reverse_append]
      | succ remaining =>
          cases sourceHead <;> (try cases ‹Bool›) <;>
            simp [structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
              structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
              structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
              structuredMixedOptionCellQuoteLiveTailOutputTape,
              structuredMixedOptionCellQuoteLiveTailHeaderBits,
              structuredLiveTailPreserveWriteOutputRows,
              structuredLiveTailPreserveWriteOutputRow,
              structuredAnySourceScratchReadRows,
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

theorem structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription_run_marker
    (remaining emitted : Nat) (source : Tape Bool)
    (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription.runConfig
        4
        (structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
          10 source remaining.succ emitted outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        10 source remaining emitted.succ
        (List.append outputBits
          structuredMixedOptionCellQuoteLiveTailLengthTickBits) := by
  cases source with
  | mk left head right =>
      cases head with
      | none =>
          cases remaining <;>
            simp [structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
              structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
              structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
              structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
              structuredMixedOptionCellQuoteLiveTailOutputTape,
              structuredMixedOptionCellQuoteLiveTailLengthTickBits,
              structuredLiveTailPreserveWriteOutputRows,
              structuredLiveTailPreserveWriteOutputRow,
              structuredAnySourceScratchReadRows,
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
            simp [structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
              structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
              structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
              structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
              structuredMixedOptionCellQuoteLiveTailOutputTape,
              structuredMixedOptionCellQuoteLiveTailLengthTickBits,
              structuredLiveTailPreserveWriteOutputRows,
              structuredLiveTailPreserveWriteOutputRow,
              structuredAnySourceScratchReadRows,
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

theorem structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription_run_final
    (emitted : Nat) (source : Tape Bool) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription.runConfig
        4
        (structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
          10 source 0 emitted outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription.halt
        source 0 emitted
        (List.append outputBits
          structuredMixedOptionCellQuoteLiveTailLengthDoneBits) := by
  cases source with
  | mk left head right =>
      cases head with
      | none =>
          simp [structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
            structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
            structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
            structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
            structuredMixedOptionCellQuoteLiveTailOutputTape,
            structuredMixedOptionCellQuoteLiveTailLengthDoneBits,
            structuredLiveTailPreserveWriteOutputRows,
            structuredLiveTailPreserveWriteOutputRow,
            structuredAnySourceScratchReadRows,
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
            simp [structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
              structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
              structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
              structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
              structuredMixedOptionCellQuoteLiveTailOutputTape,
              structuredMixedOptionCellQuoteLiveTailLengthDoneBits,
              structuredLiveTailPreserveWriteOutputRows,
              structuredLiveTailPreserveWriteOutputRow,
              structuredAnySourceScratchReadRows,
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

theorem structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription_run_length
    (remaining emitted : Nat) (source : Tape Bool)
    (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription.runConfig
        (4 * remaining + 4)
        (structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
          10 source remaining emitted outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription.halt
        source 0 (emitted + remaining)
        (List.append outputBits
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            remaining)) := by
  induction remaining generalizing emitted outputBits with
  | zero =>
      simpa [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_zero] using
        structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription_run_final
          emitted source outputBits
  | succ remaining ih =>
      refine
        Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
          (D := structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription)
          (m := 4 * remaining + 4)
          (htotal := ?_)
          (structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription_run_marker
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

theorem structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription_run
    (markers : Nat) (source : Tape Bool) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription.runConfig
        (4 * markers + 8)
        (structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
          0 source markers 0 outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription.halt
        source 0 markers
        (List.append (List.append outputBits
            structuredMixedOptionCellQuoteLiveTailHeaderBits)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            markers)) := by
  refine
    Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
      (D := structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription)
      (n := 4)
      (m := 4 * markers + 4)
      (htotal := ?_)
      (structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription_run_header
        source markers 0 outputBits)
      ?_
  · lia
  · simpa [Nat.zero_add] using
      structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription_run_length
        markers 0 source
        (List.append outputBits
          structuredMixedOptionCellQuoteLiveTailHeaderBits)

theorem structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription_run_assembly
    (p : AssemblySourceRestLiveTailEmitterParam) (source : Tape Bool) :
    structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription.runConfig
        (4 *
            ((assemblySourceRestFinishSourcePrefixBits p.w p.stage).length +
              p.sourceRestBits.length) + 8)
        (structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
          0 source
          ((assemblySourceRestFinishSourcePrefixBits p.w p.stage).length +
            p.sourceRestBits.length)
          0 []) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription.halt
        source 0
        ((assemblySourceRestFinishSourcePrefixBits p.w p.stage).length +
          p.sourceRestBits.length)
        (assemblySourceRestFinishLengthHeaderBits
          p.w p.sourceRestBits p.stage) := by
  rw [assemblySourceRestFinishLengthHeaderBits]
  simpa [structuredMixedOptionCellQuoteLiveTailHeaderBits_eq] using
    structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription_run
      ((assemblySourceRestFinishSourcePrefixBits p.w p.stage).length +
        p.sourceRestBits.length)
      source []

/--
The source segment whose length is emitted by the assembly live-tail
length-header phase.

This is the semantic source word from the shared source-rest views, not yet the
exact head position of the final combined three-tape machine.
-/
def structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits
    (p : AssemblySourceRestLiveTailEmitterParam) : Word Bool :=
  assemblySourceRestFinishSourceBits p.w p.sourceRestBits p.stage

theorem structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits_eq
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p =
      List.append
        (assemblySourceRestFinishSourcePrefixBits p.w p.stage)
        p.sourceRestBits := by
  rw [structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits,
    assemblySourceRestFinishSourceBits_eq_prefix_append_sourceRest]

theorem structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits_length
    (p : AssemblySourceRestLiveTailEmitterParam) :
    (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length =
      (assemblySourceRestFinishSourcePrefixBits p.w p.stage).length +
        p.sourceRestBits.length := by
  rw [structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits,
    assemblySourceRestFinishSourceBits_length_eq_prefix_add]

theorem structuredMixedOptionCellQuoteLiveTailCountDescription_run_assemblyLength
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredMixedOptionCellQuoteLiveTailCountDescription.runConfig
        ((structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length +
          1)
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 [] (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p)
          0 []) =
      structuredMixedOptionCellQuoteLiveTailCountDoneConfig
        (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).reverse
        (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length
        [] := by
  exact
    structuredMixedOptionCellQuoteLiveTailCountDescription_run
      (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p) []

theorem structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription_run_afterCount_assembly
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription.runConfig
        (4 *
            (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length +
          8)
        (structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
          0
          (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
            (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits
              p).reverse [])
          (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits
            p).length
          0 []) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription.halt
        (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
          (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits
            p).reverse [])
        0
        (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits
          p).length
        (assemblySourceRestFinishLengthHeaderBits
          p.w p.sourceRestBits p.stage) := by
  simpa [structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits_length] using
    structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription_run_assembly
      p
      (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
        (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits
          p).reverse [])

/--
Lowerer-facing row table for the first composed live-tail phases: count the
assembly source segment on tape 0, then emit the length header from tape 1 onto
tape 2.

The table uses the generic phase-packaging helpers so the count phase's local
halt jumps directly to the offset length-header phase.  The final semantic run
theorem still needs the phase-isolation/run-packaging lemmas that will compose
the already-proved phase runs inside this larger table.
-/
def structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription :
    Structured.Description :=
  Structured.MultiTapeLowering.ThreeTape.description 220 0 199
    (Structured.MultiTapeLowering.ThreeTape.phaseRows 0
        structuredMixedOptionCellQuoteLiveTailCountDescription.halt 100
        structuredMixedOptionCellQuoteLiveTailCountDescription.transitions ++
      Structured.MultiTapeLowering.ThreeTape.offsetRows 100
        structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription.transitions)

theorem structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_supportsReadWriteRows3 :
    Structured.MultiTapeLowering.supportsReadWriteRows3
      structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription =
        true := by
  apply
    Structured.MultiTapeLowering.ThreeTape.description_supportsReadWriteRows3
  intro t ht
  simp at ht
  rcases ht with hcount | hlength
  · exact
      Structured.MultiTapeLowering.ThreeTape.phaseRows_supportsReadWriteRow3
        structuredMixedOptionCellQuoteLiveTailCountDescription_supported.rows_supported
        t hcount
  · exact
      Structured.MultiTapeLowering.ThreeTape.offsetRows_supportsReadWriteRow3
        structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription_supported.rows_supported
        t hlength

theorem structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription :=
  Structured.MultiTapeLowering.supportedReadWriteRows3_of_supports_eq_true
    structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_supportsReadWriteRows3

def structuredMixedOptionCellQuoteLiveTailCountLengthHeaderAfterCountConfig
    (processedRev : Word Bool) (markers : Nat)
    (outputBits : Word Bool) : Structured.Configuration :=
  Structured.MultiTapeLowering.ThreeTape.config 100
    (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
      processedRev [])
    (structuredMixedOptionCellQuoteLiveTailCountReadTape markers)
    (structuredMixedOptionCellQuoteLiveTailOutputTape outputBits)

theorem structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_count_bit
    (bit : Bool) (processedRev rest : Word Bool)
    (markers : Nat) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.runConfig
        1
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 processedRev (bit :: rest) markers outputBits) =
      structuredMixedOptionCellQuoteLiveTailCountConfig
        0 (bit :: processedRev) rest markers.succ outputBits := by
  cases bit <;> cases rest <;> (try cases ‹Bool›) <;>
    simp [structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription,
      structuredMixedOptionCellQuoteLiveTailCountDescription,
      structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
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
      Structured.MultiTapeLowering.ThreeTape.phaseRows,
      Structured.MultiTapeLowering.ThreeTape.offsetRows,
      Structured.MultiTapeLowering.ThreeTape.offsetTransition,
      Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
      Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
      Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
      Structured.Description.runConfig,
      Structured.Description.stepConfig,
      Structured.Description.lookupTransition,
      Structured.Description.Matches,
      Structured.TapeAction.stay,
      Structured.TapeAction.apply, Structured.HeadMove.apply,
      Tape.read, Tape.write, Tape.move, Tape.moveRight,
      tapeAtCells, List.replicate_succ]

theorem structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_count_done
    (processedRev : Word Bool) (markers : Nat) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.runConfig
        1
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 processedRev [] markers outputBits) =
      structuredMixedOptionCellQuoteLiveTailCountLengthHeaderAfterCountConfig
        processedRev markers outputBits := by
  cases markers with
  | zero =>
      simp [structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription,
        structuredMixedOptionCellQuoteLiveTailCountDescription,
        structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
        structuredMixedOptionCellQuoteLiveTailCountConfig,
        structuredMixedOptionCellQuoteLiveTailCountLengthHeaderAfterCountConfig,
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
        Structured.MultiTapeLowering.ThreeTape.phaseRows,
        Structured.MultiTapeLowering.ThreeTape.offsetRows,
        Structured.MultiTapeLowering.ThreeTape.offsetTransition,
        Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
        Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
        Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
        Structured.Description.runConfig,
        Structured.Description.stepConfig,
        Structured.Description.lookupTransition,
        Structured.Description.Matches,
        Structured.TapeAction.stay,
        Structured.TapeAction.apply, Structured.HeadMove.apply,
        Tape.read, Tape.move, Tape.moveLeft,
        tapeAtCells]
  | succ markers =>
      simp [structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription,
        structuredMixedOptionCellQuoteLiveTailCountDescription,
        structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
        structuredMixedOptionCellQuoteLiveTailCountConfig,
        structuredMixedOptionCellQuoteLiveTailCountLengthHeaderAfterCountConfig,
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
        Structured.MultiTapeLowering.ThreeTape.phaseRows,
        Structured.MultiTapeLowering.ThreeTape.offsetRows,
        Structured.MultiTapeLowering.ThreeTape.offsetTransition,
        Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
        Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
        Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
        Structured.Description.runConfig,
        Structured.Description.stepConfig,
        Structured.Description.lookupTransition,
        Structured.Description.Matches,
        Structured.TapeAction.stay,
        Structured.TapeAction.apply, Structured.HeadMove.apply,
        Tape.read, Tape.move, Tape.moveLeft,
        tapeAtCells, List.replicate_succ]

theorem structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_count_loop
    (processedRev remaining : Word Bool) (markers : Nat)
    (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.runConfig
        (remaining.length + 1)
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 processedRev remaining markers outputBits) =
      structuredMixedOptionCellQuoteLiveTailCountLengthHeaderAfterCountConfig
        (List.append remaining.reverse processedRev)
        (markers + remaining.length)
        outputBits := by
  induction remaining generalizing processedRev markers with
  | nil =>
      simpa using
        structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_count_done
          processedRev markers outputBits
  | cons bit rest ih =>
      refine
        Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
          (D := structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription)
          (n := 1)
          (m := rest.length + 1)
          (htotal := ?_)
          (structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_count_bit
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

theorem structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_count
    (bits outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.runConfig
        (bits.length + 1)
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 [] bits 0 outputBits) =
      structuredMixedOptionCellQuoteLiveTailCountLengthHeaderAfterCountConfig
        bits.reverse bits.length outputBits := by
  simpa using
    structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_count_loop
      [] bits 0 outputBits

theorem structuredMixedOptionCellQuoteLiveTailCountLengthHeaderAfterCountConfig_eq_lengthHeaderConfig
    (processedRev : Word Bool) (markers : Nat) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCountLengthHeaderAfterCountConfig
        processedRev markers outputBits =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        100
        (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
          processedRev [])
        markers 0 outputBits := by
  simp [structuredMixedOptionCellQuoteLiveTailCountLengthHeaderAfterCountConfig,
    structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
    structuredMixedOptionCellQuoteLiveTailCountReadTape_eq_lengthPhaseTape]

theorem structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_count_assembly
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.runConfig
        ((structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length +
          1)
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 [] (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p)
          0 []) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        100
        (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
          (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits
            p).reverse [])
        (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits
          p).length
        0 [] := by
  rw [structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_count]
  exact
    structuredMixedOptionCellQuoteLiveTailCountLengthHeaderAfterCountConfig_eq_lengthHeaderConfig
      (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).reverse
      (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length
      []

theorem structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_length_header
    (source : Tape Bool) (remaining emitted : Nat)
    (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.runConfig
        4
        (structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
          100 source remaining emitted outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        110 source remaining emitted
        (List.append outputBits
          structuredMixedOptionCellQuoteLiveTailHeaderBits) := by
  cases source with
  | mk sourceLeft sourceHead sourceRight =>
      cases remaining with
      | zero =>
          cases emitted <;>
            cases sourceHead <;> (try cases ‹Bool›) <;>
              simp [structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription,
                structuredMixedOptionCellQuoteLiveTailCountDescription,
                structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
                structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
                structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
                structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
                structuredMixedOptionCellQuoteLiveTailOutputTape,
                structuredMixedOptionCellQuoteLiveTailHeaderBits,
                structuredLiveTailCountRow,
                structuredLiveTailCountDoneRow,
                structuredLiveTailPreserveWriteOutputRows,
                structuredLiveTailPreserveWriteOutputRow,
                structuredAnySourceScratchReadRows,
                structuredLiveTailLengthMarkerRows,
                structuredLiveTailLengthFinalRows,
                structuredLiveTailWriteOutputRow,
                structuredAnyReadRows,
                structuredPreserve, structuredWriteBit,
                Structured.MultiTapeLowering.ThreeTape.description,
                Structured.MultiTapeLowering.ThreeTape.config,
                Structured.MultiTapeLowering.ThreeTape.outputFromBits,
                Structured.MultiTapeLowering.ThreeTape.phaseRows,
                Structured.MultiTapeLowering.ThreeTape.offsetRows,
                Structured.MultiTapeLowering.ThreeTape.offsetTransition,
                Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
                Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
                Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
                Structured.Description.runConfig,
                Structured.Description.stepConfig,
                Structured.Description.lookupTransition,
                Structured.Description.Matches,
                Structured.TapeAction.stay,
                Structured.TapeAction.apply, Structured.HeadMove.apply,
                Tape.read, Tape.write, Tape.move, Tape.moveRight,
                tapeAtCells, List.replicate_succ, List.reverse_append]
      | succ remaining =>
          cases sourceHead <;> (try cases ‹Bool›) <;>
            simp [structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription,
              structuredMixedOptionCellQuoteLiveTailCountDescription,
              structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
              structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
              structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
              structuredMixedOptionCellQuoteLiveTailOutputTape,
              structuredMixedOptionCellQuoteLiveTailHeaderBits,
              structuredLiveTailCountRow,
              structuredLiveTailCountDoneRow,
              structuredLiveTailPreserveWriteOutputRows,
              structuredLiveTailPreserveWriteOutputRow,
              structuredAnySourceScratchReadRows,
              structuredLiveTailLengthMarkerRows,
              structuredLiveTailLengthFinalRows,
              structuredLiveTailWriteOutputRow,
              structuredAnyReadRows,
              structuredPreserve, structuredWriteBit,
              Structured.MultiTapeLowering.ThreeTape.description,
              Structured.MultiTapeLowering.ThreeTape.config,
              Structured.MultiTapeLowering.ThreeTape.outputFromBits,
              Structured.MultiTapeLowering.ThreeTape.phaseRows,
              Structured.MultiTapeLowering.ThreeTape.offsetRows,
              Structured.MultiTapeLowering.ThreeTape.offsetTransition,
              Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
              Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
              Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
              Structured.Description.runConfig,
              Structured.Description.stepConfig,
              Structured.Description.lookupTransition,
              Structured.Description.Matches,
              Structured.TapeAction.stay,
              Structured.TapeAction.apply, Structured.HeadMove.apply,
              Tape.read, Tape.write, Tape.move, Tape.moveRight,
              tapeAtCells, List.reverse_append]

theorem structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_length_marker
    (remaining emitted : Nat) (source : Tape Bool)
    (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.runConfig
        4
        (structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
          110 source remaining.succ emitted outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        110 source remaining emitted.succ
        (List.append outputBits
          structuredMixedOptionCellQuoteLiveTailLengthTickBits) := by
  cases source with
  | mk left head right =>
      cases head with
      | none =>
          cases remaining <;>
            simp [structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription,
              structuredMixedOptionCellQuoteLiveTailCountDescription,
              structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
              structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
              structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
              structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
              structuredMixedOptionCellQuoteLiveTailOutputTape,
              structuredMixedOptionCellQuoteLiveTailLengthTickBits,
              structuredLiveTailCountRow,
              structuredLiveTailCountDoneRow,
              structuredLiveTailPreserveWriteOutputRows,
              structuredLiveTailPreserveWriteOutputRow,
              structuredAnySourceScratchReadRows,
              structuredLiveTailLengthMarkerRows,
              structuredLiveTailLengthFinalRows,
              structuredLiveTailWriteOutputRow,
              structuredAnyReadRows,
              structuredPreserve, structuredWriteBit,
              Structured.MultiTapeLowering.ThreeTape.description,
              Structured.MultiTapeLowering.ThreeTape.config,
              Structured.MultiTapeLowering.ThreeTape.outputFromBits,
              Structured.MultiTapeLowering.ThreeTape.phaseRows,
              Structured.MultiTapeLowering.ThreeTape.offsetRows,
              Structured.MultiTapeLowering.ThreeTape.offsetTransition,
              Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
              Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
              Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
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
            simp [structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription,
              structuredMixedOptionCellQuoteLiveTailCountDescription,
              structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
              structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
              structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
              structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
              structuredMixedOptionCellQuoteLiveTailOutputTape,
              structuredMixedOptionCellQuoteLiveTailLengthTickBits,
              structuredLiveTailCountRow,
              structuredLiveTailCountDoneRow,
              structuredLiveTailPreserveWriteOutputRows,
              structuredLiveTailPreserveWriteOutputRow,
              structuredAnySourceScratchReadRows,
              structuredLiveTailLengthMarkerRows,
              structuredLiveTailLengthFinalRows,
              structuredLiveTailWriteOutputRow,
              structuredAnyReadRows,
              structuredPreserve, structuredWriteBit,
              Structured.MultiTapeLowering.ThreeTape.description,
              Structured.MultiTapeLowering.ThreeTape.config,
              Structured.MultiTapeLowering.ThreeTape.outputFromBits,
              Structured.MultiTapeLowering.ThreeTape.phaseRows,
              Structured.MultiTapeLowering.ThreeTape.offsetRows,
              Structured.MultiTapeLowering.ThreeTape.offsetTransition,
              Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
              Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
              Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
              Structured.Description.runConfig,
              Structured.Description.stepConfig,
              Structured.Description.lookupTransition,
              Structured.Description.Matches,
              Structured.TapeAction.stay,
              Structured.TapeAction.apply, Structured.HeadMove.apply,
              Tape.read, Tape.write, Tape.move, Tape.moveLeft,
              Tape.moveRight, tapeAtCells, List.replicate_succ,
              List.reverse_append]

theorem structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_length_final
    (emitted : Nat) (source : Tape Bool) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.runConfig
        4
        (structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
          110 source 0 emitted outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.halt
        source 0 emitted
        (List.append outputBits
          structuredMixedOptionCellQuoteLiveTailLengthDoneBits) := by
  cases source with
  | mk left head right =>
      cases head with
      | none =>
          simp [structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription,
            structuredMixedOptionCellQuoteLiveTailCountDescription,
            structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
            structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
            structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
            structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
            structuredMixedOptionCellQuoteLiveTailOutputTape,
            structuredMixedOptionCellQuoteLiveTailLengthDoneBits,
            structuredLiveTailCountRow,
            structuredLiveTailCountDoneRow,
            structuredLiveTailPreserveWriteOutputRows,
            structuredLiveTailPreserveWriteOutputRow,
            structuredAnySourceScratchReadRows,
            structuredLiveTailLengthMarkerRows,
            structuredLiveTailLengthFinalRows,
            structuredLiveTailWriteOutputRow,
            structuredAnyReadRows,
            structuredPreserve, structuredWriteBit,
            Structured.MultiTapeLowering.ThreeTape.description,
            Structured.MultiTapeLowering.ThreeTape.config,
            Structured.MultiTapeLowering.ThreeTape.outputFromBits,
            Structured.MultiTapeLowering.ThreeTape.phaseRows,
            Structured.MultiTapeLowering.ThreeTape.offsetRows,
            Structured.MultiTapeLowering.ThreeTape.offsetTransition,
            Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
            Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
            Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
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
            simp [structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription,
              structuredMixedOptionCellQuoteLiveTailCountDescription,
              structuredMixedOptionCellQuoteLiveTailLengthHeaderEmitterDescription,
              structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig,
              structuredMixedOptionCellQuoteLiveTailLengthPhaseTape,
              structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
              structuredMixedOptionCellQuoteLiveTailOutputTape,
              structuredMixedOptionCellQuoteLiveTailLengthDoneBits,
              structuredLiveTailCountRow,
              structuredLiveTailCountDoneRow,
              structuredLiveTailPreserveWriteOutputRows,
              structuredLiveTailPreserveWriteOutputRow,
              structuredAnySourceScratchReadRows,
              structuredLiveTailLengthMarkerRows,
              structuredLiveTailLengthFinalRows,
              structuredLiveTailWriteOutputRow,
              structuredAnyReadRows,
              structuredPreserve, structuredWriteBit,
              Structured.MultiTapeLowering.ThreeTape.description,
              Structured.MultiTapeLowering.ThreeTape.config,
              Structured.MultiTapeLowering.ThreeTape.outputFromBits,
              Structured.MultiTapeLowering.ThreeTape.phaseRows,
              Structured.MultiTapeLowering.ThreeTape.offsetRows,
              Structured.MultiTapeLowering.ThreeTape.offsetTransition,
              Structured.MultiTapeLowering.ThreeTape.mapTransitionStates,
              Structured.MultiTapeLowering.ThreeTape.retargetRowsTarget,
              Structured.MultiTapeLowering.ThreeTape.retargetTransitionTarget,
              Structured.Description.runConfig,
              Structured.Description.stepConfig,
              Structured.Description.lookupTransition,
              Structured.Description.Matches,
              Structured.TapeAction.stay,
              Structured.TapeAction.apply, Structured.HeadMove.apply,
              Tape.read, Tape.write, Tape.move, Tape.moveRight,
              tapeAtCells, List.reverse_append]

theorem structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_length_loop
    (remaining emitted : Nat) (source : Tape Bool)
    (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.runConfig
        (4 * remaining + 4)
        (structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
          110 source remaining emitted outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.halt
        source 0 (emitted + remaining)
        (List.append outputBits
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            remaining)) := by
  induction remaining generalizing emitted outputBits with
  | zero =>
      simpa [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_zero] using
        structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_length_final
          emitted source outputBits
  | succ remaining ih =>
      refine
        Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
          (D := structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription)
          (m := 4 * remaining + 4)
          (htotal := ?_)
          (structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_length_marker
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

theorem structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_length
    (markers : Nat) (source : Tape Bool) (outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.runConfig
        (4 * markers + 8)
        (structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
          100 source markers 0 outputBits) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.halt
        source 0 markers
        (List.append (List.append outputBits
            structuredMixedOptionCellQuoteLiveTailHeaderBits)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            markers)) := by
  refine
    Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
      (D := structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription)
      (n := 4)
      (m := 4 * markers + 4)
      (htotal := ?_)
      (structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_length_header
        source markers 0 outputBits)
      ?_
  · lia
  · simpa [Nat.zero_add] using
      structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_length_loop
        markers 0 source
        (List.append outputBits
          structuredMixedOptionCellQuoteLiveTailHeaderBits)

theorem structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_assembly
    (p : AssemblySourceRestLiveTailEmitterParam) :
    structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.runConfig
        (((structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length +
            1) +
          (4 *
              (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits
                p).length +
            8))
        (structuredMixedOptionCellQuoteLiveTailCountConfig
          0 [] (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p)
          0 []) =
      structuredMixedOptionCellQuoteLiveTailLengthHeaderConfig
        structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription.halt
        (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
          (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits
            p).reverse [])
        0
        (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits
          p).length
        (assemblySourceRestFinishLengthHeaderBits
          p.w p.sourceRestBits p.stage) := by
  refine
    Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
      (D := structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription)
      (n :=
        (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length +
          1)
      (m :=
        4 *
            (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits
              p).length +
          8)
      (htotal := rfl)
      (structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_count_assembly
        p)
      ?_
  rw [assemblySourceRestFinishLengthHeaderBits]
  simpa [structuredMixedOptionCellQuoteLiveTailHeaderBits_eq,
    structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits_length] using
    structuredMixedOptionCellQuoteLiveTailCountLengthHeaderDescription_run_length
      (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits p).length
      (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
        (structuredMixedOptionCellQuoteLiveTailAssemblyLengthCountBits
          p).reverse [])
      []

private def structuredLiveTailRewindInitRow
    (sourceRead outputRead : Option Bool) : Structured.Transition :=
  structuredRow 0 sourceRead none outputRead
    structuredStay
    (structuredPreserve Structured.HeadMove.right)
    structuredStay
    1

private def structuredLiveTailRewindLoopRow
    (sourceRead outputRead : Option Bool) : Structured.Transition :=
  structuredRow 1 sourceRead (some true) outputRead
    (structuredPreserve Structured.HeadMove.left)
    (structuredPreserve Structured.HeadMove.right)
    structuredStay
    1

private def structuredLiveTailRewindDoneRow
    (sourceRead outputRead : Option Bool) : Structured.Transition :=
  structuredRow 1 sourceRead none outputRead
    structuredStay
    structuredStay
    structuredStay
    99

/--
Move tape 0 back from the right boundary of a counted word to the first cell
of that word, using the unary marker block on tape 1 as the loop counter.
Tape 2 is preserved at its current output blank.
-/
def structuredMixedOptionCellQuoteLiveTailRewindDescription :
    Structured.Description :=
  Structured.MultiTapeLowering.ThreeTape.description 100 0 99
    (structuredAnySourceOutputReadRows structuredLiveTailRewindInitRow ++
      structuredAnySourceOutputReadRows structuredLiveTailRewindLoopRow ++
      structuredAnySourceOutputReadRows structuredLiveTailRewindDoneRow)

theorem structuredMixedOptionCellQuoteLiveTailRewindDescription_supportsReadWriteRows3 :
    Structured.MultiTapeLowering.supportsReadWriteRows3
      structuredMixedOptionCellQuoteLiveTailRewindDescription =
        true := by
  decide

theorem structuredMixedOptionCellQuoteLiveTailRewindDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredMixedOptionCellQuoteLiveTailRewindDescription :=
  Structured.MultiTapeLowering.supportedReadWriteRows3_of_supports_eq_true
    structuredMixedOptionCellQuoteLiveTailRewindDescription_supportsReadWriteRows3

def structuredMixedOptionCellQuoteLiveTailRewindSourceTape
    (leftRev right : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append (leftRev.map some) [none])
    (List.append (right.map some) [none])

def structuredMixedOptionCellQuoteLiveTailRewindScratchTape
    (remaining moved : Nat) : Tape Bool :=
  match remaining with
  | 0 =>
      tapeAtCells
        (List.append (List.replicate moved (some true)) [none])
        [none]
  | remaining' + 1 =>
      tapeAtCells
        (List.append (List.replicate moved (some true)) [none])
        (some true ::
          List.append (List.replicate remaining' (some true)) [none])

def structuredMixedOptionCellQuoteLiveTailRewindConfig
    (state : Nat) (leftRev right : Word Bool) (moved : Nat)
    (outputBits : Word Bool) : Structured.Configuration :=
  Structured.MultiTapeLowering.ThreeTape.config state
    (structuredMixedOptionCellQuoteLiveTailRewindSourceTape leftRev right)
    (structuredMixedOptionCellQuoteLiveTailRewindScratchTape
      leftRev.length moved)
    (structuredMixedOptionCellQuoteLiveTailOutputTape outputBits)

theorem structuredMixedOptionCellQuoteLiveTailRewindSourceTape_initial
    (bits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailRewindSourceTape bits.reverse [] =
      structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
        bits.reverse [] := by
  simp [structuredMixedOptionCellQuoteLiveTailRewindSourceTape,
    structuredMixedOptionCellQuoteLiveTailCellPassSourceTape]

theorem structuredMixedOptionCellQuoteLiveTailRewindSourceTape_done
    (bits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailRewindSourceTape [] bits =
      structuredMixedOptionCellQuoteLiveTailCellPassSourceTape [] bits := by
  simp [structuredMixedOptionCellQuoteLiveTailRewindSourceTape,
    structuredMixedOptionCellQuoteLiveTailCellPassSourceTape]

theorem structuredMixedOptionCellQuoteLiveTailRewindScratchTape_initial
    (markers : Nat) :
    structuredMixedOptionCellQuoteLiveTailRewindScratchTape markers 0 =
      Tape.move Direction.right
        (structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape
          markers) := by
  cases markers <;>
    simp [structuredMixedOptionCellQuoteLiveTailRewindScratchTape,
      structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
      tapeAtCells, Tape.move, Tape.moveRight, List.replicate_succ]

theorem structuredMixedOptionCellQuoteLiveTailRewindDescription_run_init
    (leftRev right outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailRewindDescription.runConfig
        1
        (Structured.MultiTapeLowering.ThreeTape.config 0
          (structuredMixedOptionCellQuoteLiveTailRewindSourceTape
            leftRev right)
          (structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape
            leftRev.length)
          (structuredMixedOptionCellQuoteLiveTailOutputTape outputBits)) =
      structuredMixedOptionCellQuoteLiveTailRewindConfig
        1 leftRev right 0 outputBits := by
  cases right with
  | nil =>
      simp [structuredMixedOptionCellQuoteLiveTailRewindDescription,
        structuredMixedOptionCellQuoteLiveTailRewindConfig,
        structuredMixedOptionCellQuoteLiveTailRewindSourceTape,
        structuredMixedOptionCellQuoteLiveTailRewindScratchTape_initial,
        structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
        structuredMixedOptionCellQuoteLiveTailOutputTape,
        structuredLiveTailRewindInitRow,
        structuredLiveTailRewindLoopRow,
        structuredLiveTailRewindDoneRow,
        structuredAnySourceOutputReadRows,
        structuredPreserve,
        Structured.MultiTapeLowering.ThreeTape.description,
        Structured.MultiTapeLowering.ThreeTape.config,
        Structured.MultiTapeLowering.ThreeTape.outputFromBits,
        Structured.Description.runConfig,
        Structured.Description.stepConfig,
        Structured.Description.lookupTransition,
        Structured.Description.Matches,
        Structured.TapeAction.stay,
        Structured.TapeAction.apply, Structured.HeadMove.apply,
        Tape.read, Tape.move, Tape.moveRight,
        tapeAtCells]
  | cons bit right =>
      cases bit <;>
        simp [structuredMixedOptionCellQuoteLiveTailRewindDescription,
          structuredMixedOptionCellQuoteLiveTailRewindConfig,
          structuredMixedOptionCellQuoteLiveTailRewindSourceTape,
          structuredMixedOptionCellQuoteLiveTailRewindScratchTape_initial,
          structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape,
          structuredMixedOptionCellQuoteLiveTailOutputTape,
          structuredLiveTailRewindInitRow,
          structuredLiveTailRewindLoopRow,
          structuredLiveTailRewindDoneRow,
          structuredAnySourceOutputReadRows,
          structuredPreserve,
          Structured.MultiTapeLowering.ThreeTape.description,
          Structured.MultiTapeLowering.ThreeTape.config,
          Structured.MultiTapeLowering.ThreeTape.outputFromBits,
          Structured.Description.runConfig,
          Structured.Description.stepConfig,
          Structured.Description.lookupTransition,
          Structured.Description.Matches,
          Structured.TapeAction.stay,
          Structured.TapeAction.apply, Structured.HeadMove.apply,
          Tape.read, Tape.move, Tape.moveRight,
          tapeAtCells]

theorem structuredMixedOptionCellQuoteLiveTailRewindDescription_run_loop_step
    (bit : Bool) (leftRev right outputBits : Word Bool) (moved : Nat) :
    structuredMixedOptionCellQuoteLiveTailRewindDescription.runConfig
        1
        (structuredMixedOptionCellQuoteLiveTailRewindConfig
          1 (bit :: leftRev) right moved outputBits) =
      structuredMixedOptionCellQuoteLiveTailRewindConfig
        1 leftRev (bit :: right) moved.succ outputBits := by
  cases leftRev <;> cases bit <;> cases right with
  | nil =>
      simp [structuredMixedOptionCellQuoteLiveTailRewindDescription,
        structuredMixedOptionCellQuoteLiveTailRewindConfig,
        structuredMixedOptionCellQuoteLiveTailRewindSourceTape,
        structuredMixedOptionCellQuoteLiveTailRewindScratchTape,
        structuredMixedOptionCellQuoteLiveTailOutputTape,
        structuredLiveTailRewindInitRow,
        structuredLiveTailRewindLoopRow,
        structuredLiveTailRewindDoneRow,
        structuredAnySourceOutputReadRows,
        structuredPreserve,
        Structured.MultiTapeLowering.ThreeTape.description,
        Structured.MultiTapeLowering.ThreeTape.config,
        Structured.MultiTapeLowering.ThreeTape.outputFromBits,
        Structured.Description.runConfig,
        Structured.Description.stepConfig,
        Structured.Description.lookupTransition,
        Structured.Description.Matches,
        Structured.TapeAction.stay,
        Structured.TapeAction.apply, Structured.HeadMove.apply,
        Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight,
        tapeAtCells, List.replicate_succ]
  | cons head tail =>
      cases head <;>
        simp [structuredMixedOptionCellQuoteLiveTailRewindDescription,
          structuredMixedOptionCellQuoteLiveTailRewindConfig,
          structuredMixedOptionCellQuoteLiveTailRewindSourceTape,
          structuredMixedOptionCellQuoteLiveTailRewindScratchTape,
          structuredMixedOptionCellQuoteLiveTailOutputTape,
          structuredLiveTailRewindInitRow,
          structuredLiveTailRewindLoopRow,
          structuredLiveTailRewindDoneRow,
          structuredAnySourceOutputReadRows,
          structuredPreserve,
          Structured.MultiTapeLowering.ThreeTape.description,
          Structured.MultiTapeLowering.ThreeTape.config,
          Structured.MultiTapeLowering.ThreeTape.outputFromBits,
          Structured.Description.runConfig,
          Structured.Description.stepConfig,
          Structured.Description.lookupTransition,
          Structured.Description.Matches,
          Structured.TapeAction.stay,
          Structured.TapeAction.apply, Structured.HeadMove.apply,
          Tape.read, Tape.move, Tape.moveLeft, Tape.moveRight,
          tapeAtCells, List.replicate_succ]

theorem structuredMixedOptionCellQuoteLiveTailRewindDescription_run_loop_done
    (right outputBits : Word Bool) (moved : Nat) :
    structuredMixedOptionCellQuoteLiveTailRewindDescription.runConfig
        1
        (structuredMixedOptionCellQuoteLiveTailRewindConfig
          1 [] right moved outputBits) =
      structuredMixedOptionCellQuoteLiveTailRewindConfig
        structuredMixedOptionCellQuoteLiveTailRewindDescription.halt
        [] right moved outputBits := by
  cases right with
  | nil =>
      simp [structuredMixedOptionCellQuoteLiveTailRewindDescription,
        structuredMixedOptionCellQuoteLiveTailRewindConfig,
        structuredMixedOptionCellQuoteLiveTailRewindSourceTape,
        structuredMixedOptionCellQuoteLiveTailRewindScratchTape,
        structuredMixedOptionCellQuoteLiveTailOutputTape,
        structuredLiveTailRewindInitRow,
        structuredLiveTailRewindLoopRow,
        structuredLiveTailRewindDoneRow,
        structuredAnySourceOutputReadRows,
        structuredPreserve,
        Structured.MultiTapeLowering.ThreeTape.description,
        Structured.MultiTapeLowering.ThreeTape.config,
        Structured.MultiTapeLowering.ThreeTape.outputFromBits,
        Structured.Description.runConfig,
        Structured.Description.stepConfig,
        Structured.Description.lookupTransition,
        Structured.Description.Matches,
        Structured.TapeAction.stay,
        Structured.TapeAction.apply, Structured.HeadMove.apply,
        Tape.read, tapeAtCells]
  | cons bit right =>
      cases bit <;>
        simp [structuredMixedOptionCellQuoteLiveTailRewindDescription,
          structuredMixedOptionCellQuoteLiveTailRewindConfig,
          structuredMixedOptionCellQuoteLiveTailRewindSourceTape,
          structuredMixedOptionCellQuoteLiveTailRewindScratchTape,
          structuredMixedOptionCellQuoteLiveTailOutputTape,
          structuredLiveTailRewindInitRow,
          structuredLiveTailRewindLoopRow,
          structuredLiveTailRewindDoneRow,
          structuredAnySourceOutputReadRows,
          structuredPreserve,
          Structured.MultiTapeLowering.ThreeTape.description,
          Structured.MultiTapeLowering.ThreeTape.config,
          Structured.MultiTapeLowering.ThreeTape.outputFromBits,
          Structured.Description.runConfig,
          Structured.Description.stepConfig,
          Structured.Description.lookupTransition,
          Structured.Description.Matches,
          Structured.TapeAction.stay,
          Structured.TapeAction.apply, Structured.HeadMove.apply,
          Tape.read, tapeAtCells]

theorem structuredMixedOptionCellQuoteLiveTailRewindDescription_run_loop
    (leftRev right outputBits : Word Bool) (moved : Nat) :
    structuredMixedOptionCellQuoteLiveTailRewindDescription.runConfig
        (leftRev.length + 1)
        (structuredMixedOptionCellQuoteLiveTailRewindConfig
          1 leftRev right moved outputBits) =
      structuredMixedOptionCellQuoteLiveTailRewindConfig
        structuredMixedOptionCellQuoteLiveTailRewindDescription.halt
        [] (List.append leftRev.reverse right)
        (moved + leftRev.length) outputBits := by
  induction leftRev generalizing right moved with
  | nil =>
      simpa using
        structuredMixedOptionCellQuoteLiveTailRewindDescription_run_loop_done
          right outputBits moved
  | cons bit leftRev ih =>
      refine
        Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
          (D := structuredMixedOptionCellQuoteLiveTailRewindDescription)
          (n := 1)
          (m := leftRev.length + 1)
          (htotal := ?_)
          (structuredMixedOptionCellQuoteLiveTailRewindDescription_run_loop_step
            bit leftRev right outputBits moved)
          ?_
      · simp [Nat.add_comm, Nat.add_left_comm]
      · have hmoved :
            moved.succ + leftRev.length =
              moved + (leftRev.length + 1) := by
          simp [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm]
        simpa [List.append_assoc, hmoved] using
          ih (bit :: right) moved.succ

theorem structuredMixedOptionCellQuoteLiveTailRewindDescription_run
    (bits outputBits : Word Bool) :
    structuredMixedOptionCellQuoteLiveTailRewindDescription.runConfig
        (bits.length + 2)
        (Structured.MultiTapeLowering.ThreeTape.config 0
          (structuredMixedOptionCellQuoteLiveTailCellPassSourceTape
            bits.reverse [])
          (structuredMixedOptionCellQuoteLiveTailLengthDoneCounterTape
            bits.length)
          (structuredMixedOptionCellQuoteLiveTailOutputTape outputBits)) =
      structuredMixedOptionCellQuoteLiveTailRewindConfig
        structuredMixedOptionCellQuoteLiveTailRewindDescription.halt
        [] bits bits.length outputBits := by
  refine
    Structured.MultiTapeLowering.ThreeTape.runConfig_chain2_of_eq
      (D := structuredMixedOptionCellQuoteLiveTailRewindDescription)
      (n := 1)
      (m := bits.reverse.length + 1)
      (c1 :=
        structuredMixedOptionCellQuoteLiveTailRewindConfig
          1 bits.reverse [] 0 outputBits)
      (htotal := ?_)
      ?_
      ?_
  · simp [List.length_reverse]
    lia
  · simpa [structuredMixedOptionCellQuoteLiveTailRewindSourceTape_initial] using
      structuredMixedOptionCellQuoteLiveTailRewindDescription_run_init
        bits.reverse [] outputBits
  · simpa [List.length_reverse, List.reverse_reverse, Nat.zero_add,
      structuredMixedOptionCellQuoteLiveTailRewindSourceTape_done] using
      structuredMixedOptionCellQuoteLiveTailRewindDescription_run_loop
        bits.reverse [] outputBits 0

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
