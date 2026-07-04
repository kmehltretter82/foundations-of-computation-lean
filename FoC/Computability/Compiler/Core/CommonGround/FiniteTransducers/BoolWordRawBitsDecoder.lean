import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.FixedSkips
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.OneGapCompactor
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.TapeLemmas
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.BoolWord

set_option doc.verso true

/-!
# Boolean-word raw-bits decoder

This module packages the generic part of the encoded Boolean-word to raw-bits
materializer.  It decodes the fixed header-prefixed encoded Boolean-word field
and preserves the caller suffix deterministically after the decoded raw bits.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace CommonGround
namespace FiniteTransducers

/--
The encoded Boolean-word field as raw tape bits, without any surrounding code
symbol or caller suffix.
-/
def boolWordRawBitsDecoderEncodedFieldBits
    (bits : Word Bool) : Word Bool :=
  List.append
    (stageNatBits bits.length)
    (cellsCodeBits (bits.map some))

/-- The only caller prefix accepted by the generic decoder. -/
def boolWordRawBitsDecoderHeaderBits : Word Bool :=
  encodeCodeSymbolAsInput MachineCodeSymbol.header

/--
Source tape for the generic Boolean-word raw-bits decoder.  The input starts
with the canonical header bit pattern, then the encoded Boolean-word field,
then the Boolean-word boundary bit, a caller suffix, and the usual right-edge
padding.
-/
def boolWordRawBitsDecoderSourceTape
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  rightEdgeRewindTargetTape
    (List.append boolWordRawBitsDecoderHeaderBits
      (List.append
        (boolWordRawBitsDecoderEncodedFieldBits bits)
        (false :: suffixTail)))
    rightPadding

/--
Deterministic target padding for the honest decoder: the decoded raw bits get
their scan-stop blank, then the original Boolean boundary/suffix is preserved
as option cells, followed by the original source boundary blank and right
padding.
-/
def boolWordRawBitsDecoderPreservedPadding
    (suffixTail : Word Bool) (rightPadding : List (Option Bool)) :
    List (Option Bool) :=
  List.append ((false :: suffixTail).map some) (none :: rightPadding)

/--
Final raw-bits target: decoded Boolean bits in right-edge scan-source shape,
with the deterministic preserved suffix padding.
-/
def boolWordRawBitsDecoderTargetTape
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  rightEdgeScanSourceTapeFromLeft [none] bits
    (boolWordRawBitsDecoderPreservedPadding suffixTail rightPadding)

def BoolWordRawBitsDecoderSpec
    (decoder : MachineDescription) : Prop :=
  decoder.SubroutineReady ∧
    forall (bits suffixTail : Word Bool)
      (rightPadding : List (Option Bool)),
      decoder.HaltsFromTape
        (boolWordRawBitsDecoderSourceTape
          bits suffixTail rightPadding)
        (boolWordRawBitsDecoderTargetTape
          bits suffixTail rightPadding)

def BoolWordRawBitsDecoderConstruction : Prop :=
  exists decoder : MachineDescription,
    BoolWordRawBitsDecoderSpec decoder

def boolWordRawBitsDecoderHeaderBase : List (Option Bool) :=
  List.append (boolWordRawBitsDecoderHeaderBits.reverse.map some) [none]

def boolWordRawBitsDecoderAfterHeaderTape
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells boolWordRawBitsDecoderHeaderBase
    (List.append ((boolWordRawBitsDecoderEncodedFieldBits bits).map some)
      (some false ::
        List.append (suffixTail.map some) (none :: rightPadding)))

def boolWordRawBitsDecoderPrefixHandoffTape
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  (boolWordCanonicalHandoffConfigWithBaseAndRight
    bits boolWordRawBitsDecoderHeaderBase
    (false :: suffixTail) (none :: rightPadding)).tape

def boolWordRawBitsDecoderPrefixScannerDescription :
    MachineDescription :=
  canonicalSeqDescription
    rightMoveAcrossFourBitsDescription
    BoolWordSuffixScannerDescription

theorem boolWordRawBitsDecoderPrefixScannerDescription_subroutineReady :
    boolWordRawBitsDecoderPrefixScannerDescription.SubroutineReady :=
  canonicalSeqDescription_subroutineReady
    rightMoveAcrossFourBitsDescription_subroutineReady
    boolWordSuffixScannerDescription_subroutineReady

theorem rightMoveAcrossFourBitsDescription_haltsFrom_rawBitsDecoderSource
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    rightMoveAcrossFourBitsDescription.HaltsFromTape
      (boolWordRawBitsDecoderSourceTape bits suffixTail rightPadding)
      (boolWordRawBitsDecoderAfterHeaderTape bits suffixTail
        rightPadding) := by
  simpa [boolWordRawBitsDecoderSourceTape,
    boolWordRawBitsDecoderAfterHeaderTape,
    boolWordRawBitsDecoderHeaderBase,
    boolWordRawBitsDecoderHeaderBits,
    rightEdgeRewindTargetTape, encodeCodeSymbolAsInput,
    List.map_append, List.append_assoc] using
    rightMoveAcrossFourBitsDescription_haltsFromTape_bits
      false false false false [none]
      (List.append ((boolWordRawBitsDecoderEncodedFieldBits bits).map some)
        (some false ::
          List.append (suffixTail.map some) (none :: rightPadding)))

theorem boolWordRawBitsDecoderAfterHeaderTape_move_left_move_right
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (boolWordRawBitsDecoderAfterHeaderTape bits suffixTail
            rightPadding)) =
      boolWordRawBitsDecoderAfterHeaderTape bits suffixTail
        rightPadding := by
  rcases stageNatBits_false_false_tail bits.length with
    ⟨stageTail, hstage⟩
  simp [boolWordRawBitsDecoderAfterHeaderTape,
    boolWordRawBitsDecoderEncodedFieldBits, hstage, tapeAtCells,
    Tape.move, Tape.moveLeft, Tape.moveRight, List.append_assoc]

theorem boolWordSuffixScannerDescription_haltsFrom_rawBitsDecoderAfterHeader
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    BoolWordSuffixScannerDescription.HaltsFromTape
      (boolWordRawBitsDecoderAfterHeaderTape bits suffixTail
        rightPadding)
      (boolWordRawBitsDecoderPrefixHandoffTape bits suffixTail
        rightPadding) := by
  rcases
      run_boolWordSuffix_raw_to_canonical_handoff_withBaseAndRight
        bits boolWordRawBitsDecoderHeaderBase suffixTail
        (none :: rightPadding) with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [boolWordRawBitsDecoderAfterHeaderTape,
      boolWordRawBitsDecoderPrefixHandoffTape,
      boolWordRawBitsDecoderEncodedFieldBits, List.map_append,
      List.append_assoc] using
      congrArg Configuration.state hsteps
  · simpa [boolWordRawBitsDecoderAfterHeaderTape,
      boolWordRawBitsDecoderPrefixHandoffTape,
      boolWordRawBitsDecoderEncodedFieldBits, List.map_append,
      List.append_assoc] using
      congrArg Configuration.tape hsteps

theorem boolWordRawBitsDecoderPrefixScannerDescription_haltsFromTape
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    boolWordRawBitsDecoderPrefixScannerDescription.HaltsFromTape
      (boolWordRawBitsDecoderSourceTape bits suffixTail rightPadding)
      (boolWordRawBitsDecoderPrefixHandoffTape bits suffixTail
        rightPadding) := by
  exact
    canonicalSeqDescription_haltsFromTape_of_haltsFromTape
      rightMoveAcrossFourBitsDescription_subroutineReady
      boolWordSuffixScannerDescription_subroutineReady
      (rightMoveAcrossFourBitsDescription_haltsFrom_rawBitsDecoderSource
        bits suffixTail rightPadding)
      (boolWordRawBitsDecoderAfterHeaderTape_move_left_move_right
        bits suffixTail rightPadding)
      (boolWordSuffixScannerDescription_haltsFrom_rawBitsDecoderAfterHeader
        bits suffixTail rightPadding)

def BoolWordCanonicalHandoffToRawScanSourceSpec
    (materializer : MachineDescription) : Prop :=
  materializer.SubroutineReady ∧
    forall (bits suffixTail : Word Bool)
      (rightPadding : List (Option Bool)),
      materializer.HaltsFromTape
        (boolWordRawBitsDecoderPrefixHandoffTape
          bits suffixTail rightPadding)
        (boolWordRawBitsDecoderTargetTape
          bits suffixTail rightPadding)

def BoolWordCanonicalHandoffToRawScanSourceConstruction : Prop :=
  exists materializer : MachineDescription,
    BoolWordCanonicalHandoffToRawScanSourceSpec materializer

/--
Concrete table for the remaining materializer.

The first phase reads the restored Boolean-cell code on the left stack in the
reverse physical order produced by the canonical suffix scanner:

* {lit}`false,true,true,false` decodes a raw {lit}`true`;
* {lit}`true,false,true,false` decodes a raw {lit}`false`;
* {lit}`true,true,false,false` is the restored {name}`MachineCodeSymbol.done`
  marker and enters cleanup.

The cleanup phase erases the restored metadata/header scaffold and the final
phase is the local gap-closing pass intended to compact the decoded raw cells
toward the preserved boundary/suffix.  The run theorem below is the remaining
proof that this table realizes the exact tape contract for all canonical
inputs.
-/
def boolWordCanonicalHandoffToRawScanSourceMaterializerDescription :
    MachineDescription where
  stateCount := 80
  start := 0
  halt := 79
  transitions :=
    [ transition 0 (some false) none Direction.left 10
    , transition 0 (some true) none Direction.left 20
    , transition 0 none none Direction.right 40

    , transition 10 (some true) none Direction.left 11
    , transition 11 (some true) none Direction.left 12
    , transition 12 (some false) (some true) Direction.left 0

    , transition 20 (some false) none Direction.left 21
    , transition 21 (some true) none Direction.left 22
    , transition 22 (some false) (some false) Direction.left 0

    , transition 20 (some true) none Direction.left 30
    , transition 30 (some false) none Direction.left 31
    , transition 31 (some false) none Direction.left 40

    , transition 40 (some false) none Direction.left 40
    , transition 40 (some true) none Direction.left 40
    , transition 40 none none Direction.right 50

    , transition 50 none none Direction.right 50
    , transition 50 (some false) (some false) Direction.left 60
    , transition 50 (some true) (some true) Direction.left 60

    , transition 60 none none Direction.right 61
    , transition 61 (some false) none Direction.left 62
    , transition 61 (some true) none Direction.left 63
    , transition 61 none none Direction.left 79
    , transition 62 none (some false) Direction.right 64
    , transition 63 none (some true) Direction.right 64
    , transition 64 none none Direction.right 61
    ]

theorem boolWordCanonicalHandoffToRawScanSourceMaterializerDescription_wellFormed :
    boolWordCanonicalHandoffToRawScanSourceMaterializerDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l :=
        boolWordCanonicalHandoffToRawScanSourceMaterializerDescription.transitions)
      (stateCount :=
        boolWordCanonicalHandoffToRawScanSourceMaterializerDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l :=
        boolWordCanonicalHandoffToRawScanSourceMaterializerDescription.transitions)
      (by decide)

theorem boolWordCanonicalHandoffToRawScanSourceMaterializerDescription_haltTransitionFree :
    boolWordCanonicalHandoffToRawScanSourceMaterializerDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l :=
      boolWordCanonicalHandoffToRawScanSourceMaterializerDescription.transitions)
    (state :=
      boolWordCanonicalHandoffToRawScanSourceMaterializerDescription.halt)
    (by decide)

theorem boolWordCanonicalHandoffToRawScanSourceMaterializerDescription_subroutineReady :
    boolWordCanonicalHandoffToRawScanSourceMaterializerDescription.SubroutineReady :=
  ⟨boolWordCanonicalHandoffToRawScanSourceMaterializerDescription_wellFormed,
    boolWordCanonicalHandoffToRawScanSourceMaterializerDescription_haltTransitionFree⟩

theorem boolWordCanonicalHandoffToRawScanSourceMaterializerDescription_haltsFromTape
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    boolWordCanonicalHandoffToRawScanSourceMaterializerDescription.HaltsFromTape
      (boolWordRawBitsDecoderPrefixHandoffTape
        bits suffixTail rightPadding)
      (boolWordRawBitsDecoderTargetTape
        bits suffixTail rightPadding) := by
  sorry

/--
The concrete remaining finite-machine leaf.  The only unresolved proof is the
run theorem for
{name}`boolWordCanonicalHandoffToRawScanSourceMaterializerDescription`; the
existential no longer hides which table is intended.
-/
theorem boolWordCanonicalHandoffToRawScanSourceConstruction_core :
    BoolWordCanonicalHandoffToRawScanSourceConstruction := by
  exact
    ⟨boolWordCanonicalHandoffToRawScanSourceMaterializerDescription,
      boolWordCanonicalHandoffToRawScanSourceMaterializerDescription_subroutineReady,
      boolWordCanonicalHandoffToRawScanSourceMaterializerDescription_haltsFromTape⟩

private theorem dovetailTapeAtCells_move_left_move_right_move_left_append_cons
    (pref tail right : List (Option Bool)) (cell : Option Bool) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (Tape.move Direction.left
            (DovetailInitialLayoutInitializer.tapeAtCells
              (List.append pref (cell :: tail)) right))) =
      Tape.move Direction.left
        (DovetailInitialLayoutInitializer.tapeAtCells
          (List.append pref (cell :: tail)) right) := by
  rw [show
      Tape.move Direction.right
          (Tape.move Direction.left
            (DovetailInitialLayoutInitializer.tapeAtCells
              (List.append pref (cell :: tail)) right)) =
        DovetailInitialLayoutInitializer.tapeAtCells
          (List.append pref (cell :: tail)) right by
    simpa [DovetailInitialLayoutInitializer.tapeAtCells,
      tapeAtCells] using
      tapeAtCells_move_right_move_left_append_cons
        pref tail right cell]

theorem boolWordRawBitsDecoderPrefixHandoffTape_move_left_move_right
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    Tape.move Direction.left
        (Tape.move Direction.right
          (boolWordRawBitsDecoderPrefixHandoffTape bits suffixTail
            rightPadding)) =
      boolWordRawBitsDecoderPrefixHandoffTape bits suffixTail
        rightPadding := by
  simpa [boolWordRawBitsDecoderPrefixHandoffTape,
    boolWordCanonicalHandoffConfigWithBaseAndRight,
    cellListCanonicalHandoffConfigWithBaseAndRight,
    cellListCanonicalRestoredLeftWithBase,
    cellListCanonicalFinishStartLeftWithBase,
    boolWordRawBitsDecoderHeaderBase, boolWordRawBitsDecoderHeaderBits,
    encodeCodeSymbolAsInput, doneBits, List.append_assoc] using
    dovetailTapeAtCells_move_left_move_right_move_left_append_cons
      ((List.map some (cellsCodeBits (List.map some bits))).reverse)
      (some true :: some false :: some false ::
        List.append (cellListCanonicalLengthPrefixRev bits.length)
          boolWordRawBitsDecoderHeaderBase)
      (some false :: List.append (suffixTail.map some)
        (none :: rightPadding))
      (some true)

/--
The finite-machine leaf for the honest Boolean-word decoder.  It decodes the
header-prefixed encoded field and preserves the suffix/right-padding shape
specified above.
-/
theorem boolWordRawBitsDecoderConstruction_core :
    BoolWordRawBitsDecoderConstruction := by
  rcases boolWordCanonicalHandoffToRawScanSourceConstruction_core with
    ⟨materializer, hmaterializer⟩
  refine
    ⟨canonicalSeqDescription
      boolWordRawBitsDecoderPrefixScannerDescription
      materializer, ?_⟩
  constructor
  · exact
      canonicalSeqDescription_subroutineReady
        boolWordRawBitsDecoderPrefixScannerDescription_subroutineReady
        hmaterializer.left
  · intro bits suffixTail rightPadding
    exact
      canonicalSeqDescription_haltsFromTape_of_haltsFromTape
        boolWordRawBitsDecoderPrefixScannerDescription_subroutineReady
        hmaterializer.left
        (boolWordRawBitsDecoderPrefixScannerDescription_haltsFromTape
          bits suffixTail rightPadding)
        (boolWordRawBitsDecoderPrefixHandoffTape_move_left_move_right
          bits suffixTail rightPadding)
        (hmaterializer.right bits suffixTail rightPadding)

end FiniteTransducers
end CommonGround

end Computability
end FoC
