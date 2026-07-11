import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.StateClassifier
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterTheory.ScratchWidth
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.OptionCellExpandAppendSpec
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelOutputCore.Runs
import FoC.Computability.Compiler.Dovetail.Scanner.Simulator.Definitions

set_option doc.verso true

/-!
# Simulator-layout field-decomposition boundary

After the #18 input materializer, logical tape 0 contains the complete encoded
simulator layout and logical tapes 1 and 2 are blank.  The execution loops need
a different representation: the live configuration tape on tape 0, a raw
unary stage counter on tape 1, and self-delimiting preserved metadata with the
hit bit at the head of tape 2.

This module names that exact boundary and records the clean reusable prefix of
the physical route.  The existing structured Boolean-word decoder can expose
the input field, but it does not materialize the stage counter or decode the
configuration.  Its padded source and output-buffer initialization also differ
exactly from the post-embedding boundary.  Consequently the construction
contract below remains the honest integrated parser/decomposer obligation.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace FieldDecomposition

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open DovetailInitialLayoutInitializer.StageInputMarkedScanner
open CanonicalLayouts.DovetailLayoutScanner
open CanonicalLayouts.SimulatorLayoutScanner
open StructuredConstructionTargets.FuelOutputCore

/-!
## Preserved loop metadata
-/

/-- Fields that must survive counter consumption but are not the live
configuration tape.  The original raw state is retained for the generic
classifier branch; known-state execution may instead keep its changing state
in finite control. -/
structure Metadata where
  input : Word Bool
  stage : Nat
  state : Nat

/-- Canonical self-delimiting metadata code. -/
def Metadata.encodeAppend
    (M : Metadata) (suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  encodeBoolWordAppend M.input
    (encodeNatAppend M.stage
      (encodeNatAppend M.state suffix))

def Metadata.encode (M : Metadata) : Word MachineCodeSymbol :=
  M.encodeAppend []

/-- Executable inverse of the preserved metadata code. -/
def Metadata.decode
    (tokens : Word MachineCodeSymbol) :
    Option (Metadata × Word MachineCodeSymbol) :=
  match decodeBoolWord tokens with
  | none => none
  | some (input, rest) =>
      match decodeNat rest with
      | none => none
      | some (stage, rest) =>
          match decodeNat rest with
          | none => none
          | some (state, suffix) =>
              some (⟨input, stage, state⟩, suffix)

theorem Metadata.decode_encodeAppend
    (M : Metadata) (suffix : Word MachineCodeSymbol) :
    Metadata.decode (M.encodeAppend suffix) = some (M, suffix) := by
  cases M
  simp [Metadata.decode, Metadata.encodeAppend,
    decodeBoolWord_encodeBoolWordAppend, decodeNat_encodeNatAppend]

/-- Metadata extracted from an ordinary simulator layout. -/
def metadata (L : SimulatorLayout) : Metadata :=
  ⟨L.input, L.stage, L.config.state⟩

/-- Boolean encoding stored immediately left of the hit head. -/
def metadataBits (L : SimulatorLayout) : Word Bool :=
  encodeCodeWordAsInput (metadata L).encode

/-- Cells to the left of the live hit head.  The original-input scratch width
is carried as a raw unary block immediately left of the head, independently of
the final configuration encoding.  A blank separates it from the canonical
input/stage/raw-state metadata. -/
def metadataPrefixCells (L : SimulatorLayout) : List (Option Bool) :=
  List.append ((metadataBits L).map some)
    (none :: RunConfigEmitterTheory.scratchWidthMarkers L)

/-- Metadata tape with a caller-selected live hit value. -/
def metadataHitTapeWithHit
    (L : SimulatorLayout) (hit : Bool) : Tape Bool :=
  tapeAtCells (metadataPrefixCells L).reverse [some hit, none]

/-- Tape-2 loop layout: canonical metadata and the independent scratch-width
marker block lie to the left, the live hit bit is at the head, and one explicit
blank is retained on the right. -/
def metadataHitTape (L : SimulatorLayout) : Tape Bool :=
  metadataHitTapeWithHit L L.hit

@[simp] theorem metadataHitTapeWithHit_read
    (L : SimulatorLayout) (hit : Bool) :
    Tape.read (metadataHitTapeWithHit L hit) = some hit := by
  rfl

@[simp] theorem writeS_apply_metadataHitTapeWithHit
    (L : SimulatorLayout) (oldHit newHit : Bool) :
    (writeS (some newHit)).apply (metadataHitTapeWithHit L oldHit) =
      metadataHitTapeWithHit L newHit := by
  rfl

theorem metadata_decode (L : SimulatorLayout) :
    Metadata.decode (metadata L).encode = some (metadata L, []) := by
  exact Metadata.decode_encodeAppend (metadata L) []

/-!
## Exact post-decomposition layout
-/

/-- Raw stage counter consumed by either execution loop. -/
def stageCounterTape (stage : Nat) : Tape Bool :=
  tapeAtCells []
    (List.append
      (List.replicate stage (some true : Option Bool)) [none])

@[simp] theorem stageCounterTape_read_zero :
    Tape.read (stageCounterTape 0) = none := by
  rfl

@[simp] theorem stageCounterTape_read_succ (stage : Nat) :
    Tape.read (stageCounterTape (stage + 1)) = some true := by
  simp [stageCounterTape, tapeAtCells, Tape.read, List.replicate_succ]

/-- Exact logical tapes needed at the known/other dispatcher boundary. -/
def loopTapes (L : SimulatorLayout) : List (Tape Bool) :=
  [L.config.tape, stageCounterTape L.stage, metadataHitTape L]

/-- Physical post-embedding source produced by the checked #18 input
materializer. -/
def embeddedSourceTape (L : SimulatorLayout) : Tape Bool :=
  StructuredConstructionTargets.structured3InputEmbeddingEmitterTargetTape
    (SimulatorLayout.asBoolInput L)

theorem embeddedSourceTape_eq_guarded (L : SimulatorLayout) :
    embeddedSourceTape L =
      encodedGuardedStructuredTapes
        [ Tape.input (SimulatorLayout.asBoolInput L)
        , Tape.blank
        , Tape.blank ] := by
  rw [embeddedSourceTape]
  rw [StructuredConstructionTargets.structured3InputEmbeddingEmitterTargetTape_eq_materializerTarget]
  rfl

/-!
## Canonical source decomposition
-/

/-- Axiom-clean exact token decomposition supplied by the closed fuel-output
core.  Its typed phase table is the closest existing parser template: it walks
the input length/bits, stage, state, both configuration cell lists and head,
and the hit field. -/
theorem source_encode_decomp (L : SimulatorLayout) :
    SimulatorLayout.encode L =
      MachineCodeSymbol.header ::
        List.append (encodeNat (L.input.map some).length)
          (List.append ((L.input.map some).map cellTok)
            (List.append (encodeNat L.stage)
              (List.append (encodeNat L.config.state)
                (List.append (encodeNat L.config.tape.left.length)
                  (List.append (L.config.tape.left.map cellTok)
                    (cellTok L.config.tape.head ::
                      List.append (encodeNat L.config.tape.right.length)
                        (List.append (L.config.tape.right.map cellTok)
                          (List.append [cellTok (some L.hit)]
                            ([] : Word MachineCodeSymbol))))))))) :=
  encode_decomp L

/-!
The active implementation is split into the source counter, stage counter,
state selector, metadata prefix, and exact configuration/hit materializer.
The latter must preserve blank cells and the left/head/right split; normalized
output is not an adequate configuration representation.
-/

end FieldDecomposition
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
