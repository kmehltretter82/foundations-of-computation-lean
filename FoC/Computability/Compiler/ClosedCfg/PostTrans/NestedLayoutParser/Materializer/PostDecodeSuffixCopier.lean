import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.BoolWordRawBitsDecoder.StructuredBody
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredTableChecks
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeHelpers
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeTactic

set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

namespace FoC
namespace Computability

open Languages
open CommonGround.FiniteTransducers

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace ThreeTape
namespace NestedLayoutMaterializerInternal
namespace PostDecodeSuffixCopier

def seekDecodedStop : Nat := 0
def copySuffix : Nat := 1
def restoreSuffix : Nat := 2
def rewindDecoded : Nat := 8
def halt : Nat := 9

def stateCount : Nat := 10

def rowsForSourceRead
    (source : Nat) (sourceRead : Option Bool)
    (action0 action1 action2 : TapeAction)
    (target : Nat) : List Transition :=
  allReads2
    (fun read1 read2 =>
      row source sourceRead read1 read2
        action0 action1 action2 target)

def rowsForCounterRead
    (source : Nat) (counterRead : Option Bool)
    (action0 action1 action2 : TapeAction)
    (target : Nat) : List Transition :=
  allReads2
    (fun read0 read2 =>
      row source read0 counterRead read2
        action0 action1 action2 target)

def rowsForOutputRead
    (source : Nat) (outputRead : Option Bool)
    (action0 action1 action2 : TapeAction)
    (target : Nat) : List Transition :=
  allReads2
    (fun read0 read1 =>
      row source read0 read1 outputRead
        action0 action1 action2 target)

def rowsForSourceOutputRead
    (source : Nat) (sourceRead outputRead : Option Bool)
    (action0 action1 action2 : TapeAction)
    (target : Nat) : List Transition :=
  allReads1
    (fun read1 =>
      row source sourceRead read1 outputRead
        action0 action1 action2 target)

def rows : List Transition :=
  [ rowsForOutputRead seekDecodedStop (some false)
      keepS keepS keepR seekDecodedStop
  , rowsForOutputRead seekDecodedStop (some true)
      keepS keepS keepR seekDecodedStop
  , rowsForOutputRead seekDecodedStop none
      keepS keepS keepS copySuffix
  , rowsForSourceRead copySuffix (some false)
      eraseR keepS (writeBitR false) copySuffix
  , rowsForSourceRead copySuffix (some true)
      eraseR keepS (writeBitR true) copySuffix
  , rowsForSourceRead copySuffix none
      keepL keepS keepL restoreSuffix
  , rowsForSourceOutputRead restoreSuffix none (some false)
      (writeBitL false) keepS keepL restoreSuffix
  , rowsForSourceOutputRead restoreSuffix none (some true)
      (writeBitL true) keepS keepL restoreSuffix
  , rowsForSourceRead restoreSuffix (some false)
      keepR keepS keepS rewindDecoded
  , rowsForSourceRead restoreSuffix (some true)
      keepR keepS keepS rewindDecoded
  , rowsForOutputRead rewindDecoded (some false)
      keepS keepS keepL rewindDecoded
  , rowsForOutputRead rewindDecoded (some true)
      keepS keepS keepL rewindDecoded
  , rowsForOutputRead rewindDecoded none
      keepS keepS keepR halt ].flatten

def description : Description :=
  ThreeTape.description stateCount seekDecodedStop halt rows

syntax "copier_step " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| copier_step [$lemmas,*]) =>
      `(tactic|
        three_tape_step [
          description, rows, rowsForSourceRead, rowsForCounterRead,
          rowsForOutputRead, rowsForSourceOutputRead, allReads1,
          allReadCells, allReads2, allReadRows3, allReads3, List.find?,
          seekDecodedStop, copySuffix, restoreSuffix, rewindDecoded, halt,
          $lemmas,*])

def sourceConfig
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) : Configuration :=
  config seekDecodedStop
    (structuredBoolWordRawBitsDecoderSourceTargetTape
      bits suffixTail rightPadding)
    (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
      (bits.length + 1))
    (rightEdgeScanSourceTapeFromLeft [none] bits [])

def targetConfig
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) : Configuration :=
  config halt
    (structuredBoolWordRawBitsDecoderSourceTargetTape
      bits suffixTail rightPadding)
    (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
      (bits.length + 1))
    (rightEdgeScanSourceTapeFromLeft [none]
      (List.append bits (false :: suffixTail)) [])

def decodedStopTape
    (left : List (Option Bool)) (bits : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append (bits.reverse.map some) left) [none]

theorem seekDecodedStop_step_bit
    (source counter : Tape Bool)
    (hsource : source.head = some false)
    (hcounter : counter.head = none)
    (left : List (Option Bool)) (bit : Bool) (rest : Word Bool) :
    description.runConfig 1
        (config seekDecodedStop source counter
          (tapeAtCells left (some bit :: rest.map some ++ [none]))) =
      config seekDecodedStop source counter
        (tapeAtCells (some bit :: left) (rest.map some ++ [none])) := by
  cases bit <;>
    copier_step [hsource, hcounter]
  all_goals cases rest <;> rfl

theorem seekDecodedStop_step_blank
    (source counter : Tape Bool)
    (hsource : source.head = some false)
    (hcounter : counter.head = none)
    (left : List (Option Bool)) :
    description.runConfig 1
        (config seekDecodedStop source counter
          (tapeAtCells left [none])) =
      config copySuffix source counter
        (tapeAtCells left [none]) := by
  copier_step [hsource, hcounter]

theorem seekDecodedStop_run
    (source counter : Tape Bool)
    (hsource : source.head = some false)
    (hcounter : counter.head = none)
    (left : List (Option Bool)) (bits : Word Bool) :
    description.runConfig (bits.length + 1)
        (config seekDecodedStop source counter
          (tapeAtCells left (bits.map some ++ [none]))) =
      config copySuffix source counter
        (decodedStopTape left bits) := by
  induction bits generalizing left with
  | nil =>
      simpa [decodedStopTape] using
        seekDecodedStop_step_blank source counter hsource hcounter left
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp
        lia]
      rw [Structured.Description.runConfig_add]
      change
        description.runConfig (rest.length + 1)
          (description.runConfig 1
            (config seekDecodedStop source counter
              (tapeAtCells left
                (some bit :: rest.map some ++ [none])))) = _
      rw [seekDecodedStop_step_bit source counter hsource hcounter]
      rw [ih (some bit :: left)]
      change
        config copySuffix source counter
            (decodedStopTape (some bit :: left) rest) =
          config copySuffix source counter
            (decodedStopTape left
              (show Word Bool from bit :: rest))
      simp [decodedStopTape, List.reverse_cons, List.append_assoc]

def copySourceTape
    (baseLeft : List (Option Bool))
    (copied remaining : Word Bool)
    (rightPadding : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate copied.length (none : Option Bool)) baseLeft)
    (List.append (remaining.map some) (none :: rightPadding))

def copyOutputTape
    (outputBaseLeft : List (Option Bool))
    (copied : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append (copied.reverse.map some) outputBaseLeft) []

theorem copySuffix_step_bit
    (counter : Tape Bool) (hcounter : counter.head = none)
    (baseLeft outputBaseLeft : List (Option Bool))
    (rightPadding : List (Option Bool))
    (copied remaining : Word Bool) (bit : Bool) :
    description.runConfig 1
        (config copySuffix
          (copySourceTape baseLeft copied (bit :: remaining) rightPadding)
          counter
          (copyOutputTape outputBaseLeft copied)) =
      config copySuffix
        (copySourceTape baseLeft (List.append copied [bit]) remaining
          rightPadding)
        counter
        (copyOutputTape outputBaseLeft (List.append copied [bit])) := by
  cases bit <;>
    copier_step [copySourceTape, copyOutputTape, hcounter,
      List.reverse_append, List.append_assoc]
  all_goals
    cases remaining <;>
      simp [List.replicate_succ, List.append_assoc]

theorem copySuffix_run_loop
    (counter : Tape Bool) (hcounter : counter.head = none)
    (baseLeft outputBaseLeft : List (Option Bool))
    (rightPadding : List (Option Bool))
    (copied remaining : Word Bool) :
    description.runConfig remaining.length
        (config copySuffix
          (copySourceTape baseLeft copied remaining rightPadding)
          counter
          (copyOutputTape outputBaseLeft copied)) =
      config copySuffix
        (copySourceTape baseLeft (List.append copied remaining) []
          rightPadding)
        counter
        (copyOutputTape outputBaseLeft
          (List.append copied remaining)) := by
  induction remaining generalizing copied with
  | nil =>
      simp [Structured.Description.runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp
        lia]
      rw [Structured.Description.runConfig_add]
      change
        description.runConfig rest.length
          (description.runConfig 1
            (config copySuffix
              (copySourceTape baseLeft copied
                (show Word Bool from bit :: rest) rightPadding)
              counter
              (copyOutputTape outputBaseLeft copied))) = _
      rw [copySuffix_step_bit counter hcounter]
      rw [ih (List.append copied [bit])]
      simp [List.append_assoc]

theorem copySuffix_step_blank
    (counter : Tape Bool) (hcounter : counter.head = none)
    (sourceLeft outputLeft : List (Option Bool))
    (rightPadding : List (Option Bool))
    (sourceCell : Option Bool) (outputBit : Bool) :
    description.runConfig 1
        (config copySuffix
          (tapeAtCells (sourceCell :: sourceLeft)
            (none :: rightPadding))
          counter
          (tapeAtCells (some outputBit :: outputLeft) [])) =
      config restoreSuffix
        (tapeAtCells sourceLeft
          (sourceCell :: none :: rightPadding))
        counter
        (tapeAtCells outputLeft [some outputBit, none]) := by
  cases sourceCell with
  | none =>
    cases outputBit <;>
      copier_step [hcounter]
  | some sourceBit =>
    cases sourceBit <;> cases outputBit <;>
      copier_step [hcounter]

theorem restoreSuffix_step_bit
    (counter : Tape Bool) (hcounter : counter.head = none)
    (sourceLeft outputLeft : List (Option Bool))
    (sourceRight outputRight : List (Option Bool))
    (sourceCell outputCell : Option Bool) (bit : Bool) :
    description.runConfig 1
        (config restoreSuffix
          (tapeAtCells (sourceCell :: sourceLeft)
            (none :: sourceRight))
          counter
          (tapeAtCells (outputCell :: outputLeft)
            (some bit :: outputRight))) =
      config restoreSuffix
        (tapeAtCells sourceLeft
          (sourceCell :: some bit :: sourceRight))
        counter
        (tapeAtCells outputLeft
          (outputCell :: some bit :: outputRight)) := by
  cases sourceCell with
  | none =>
    cases outputCell with
    | none =>
      cases bit <;>
        copier_step [hcounter]
    | some outputBit =>
      cases outputBit <;> cases bit <;>
        copier_step [hcounter]
  | some sourceBit =>
    cases sourceBit <;>
      cases outputCell with
      | none =>
        cases bit <;>
          copier_step [hcounter]
      | some outputBit =>
        cases outputBit <;> cases bit <;>
          copier_step [hcounter]

theorem restoreSuffix_run_loop
    (counter : Tape Bool) (hcounter : counter.head = none)
    (sourceBase outputBase : List (Option Bool))
    (sourceBoundary outputBoundary : Option Bool)
    (rightPadding : List (Option Bool))
    (restored : List Bool) (bit : Bool) (rest : List Bool) :
    description.runConfig (bit :: rest).length
        (config restoreSuffix
          (tapeAtCells
            (List.append
              (List.replicate rest.length (none : Option Bool))
              (sourceBoundary :: sourceBase))
            (none :: List.append (restored.map some)
              (none :: rightPadding)))
          counter
          (tapeAtCells
            (List.append (rest.map some)
              (outputBoundary :: outputBase))
            (some bit :: List.append (restored.map some) [none]))) =
      config restoreSuffix
        (tapeAtCells sourceBase
          (sourceBoundary ::
            List.append
              ((List.append
                (bit :: rest).reverse
                restored).map some)
              (none :: rightPadding)))
        counter
        (tapeAtCells outputBase
          (outputBoundary ::
            List.append
              ((List.append
                (bit :: rest).reverse
                restored).map some)
              [none])) := by
  induction rest generalizing restored bit with
  | nil =>
      change description.runConfig 1 _ = _
      change
        description.runConfig 1
          (config restoreSuffix
            (tapeAtCells (sourceBoundary :: sourceBase)
              (none :: List.append (restored.map some)
                (none :: rightPadding)))
            counter
            (tapeAtCells (outputBoundary :: outputBase)
              (some bit :: List.append (restored.map some) [none]))) = _
      rw [restoreSuffix_step_bit counter hcounter]
      simp [List.append_assoc]
  | cons next tail ih =>
      rw [show (bit :: next :: tail).length =
          1 + (next :: tail).length by
        simp
        lia]
      rw [Structured.Description.runConfig_add]
      change
        description.runConfig (next :: tail).length
          (description.runConfig 1
            (config restoreSuffix
              (tapeAtCells
                (none ::
                  List.append
                    (List.replicate tail.length (none : Option Bool))
                    (sourceBoundary :: sourceBase))
                (none :: List.append (restored.map some)
                  (none :: rightPadding)))
              counter
              (tapeAtCells
                (some next ::
                  List.append (tail.map some)
                    (outputBoundary :: outputBase))
                (some bit :: List.append (restored.map some) [none])))) = _
      rw [restoreSuffix_step_bit counter hcounter]
      change
        description.runConfig (next :: tail).length
          (config restoreSuffix
            (tapeAtCells
              (List.append
                (List.replicate tail.length (none : Option Bool))
                (sourceBoundary :: sourceBase))
              (none :: List.append ((bit :: restored).map some)
                (none :: rightPadding)))
            counter
            (tapeAtCells
              (List.append (tail.map some)
                (outputBoundary :: outputBase))
              (some next :: List.append ((bit :: restored).map some)
                [none]))) = _
      rw [ih (bit :: restored) next]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem restoreSuffix_step_boundary
    (counter : Tape Bool) (hcounter : counter.head = none)
    (sourceLeft outputLeft : List (Option Bool))
    (sourceRight outputRight : List (Option Bool))
    (sourceBit : Bool) (outputCell : Option Bool) :
    description.runConfig 1
        (config restoreSuffix
          (tapeAtCells sourceLeft (some sourceBit :: sourceRight))
          counter
          (tapeAtCells outputLeft (outputCell :: outputRight))) =
      config rewindDecoded
        (tapeAtCells (some sourceBit :: sourceLeft) sourceRight)
        counter
        (tapeAtCells outputLeft (outputCell :: outputRight)) := by
  cases sourceBit <;>
    cases outputCell with
    | none =>
        copier_step [hcounter]
        cases sourceRight <;> rfl
    | some outputBit =>
        cases outputBit <;>
          copier_step [hcounter]
        all_goals cases sourceRight <;> rfl

theorem rewindDecoded_step_bit
    (source counter : Tape Bool)
    (hsource : source.head = some false)
    (hcounter : counter.head = none)
    (outputLeft : List (Option Bool))
    (outputCell : Option Bool) (bit : Bool)
    (outputRight : List (Option Bool)) :
    description.runConfig 1
        (config rewindDecoded source counter
          (tapeAtCells (outputCell :: outputLeft)
            (some bit :: outputRight))) =
      config rewindDecoded source counter
        (tapeAtCells outputLeft
          (outputCell :: some bit :: outputRight)) := by
  cases outputCell with
  | none =>
      cases bit <;>
        copier_step [hsource, hcounter]
  | some outputLeftBit =>
      cases outputLeftBit <;> cases bit <;>
        copier_step [hsource, hcounter]

theorem rewindDecoded_step_blank
    (source counter : Tape Bool)
    (hsource : source.head = some false)
    (hcounter : counter.head = none)
    (outputRight : List (Option Bool)) :
    description.runConfig 1
        (config rewindDecoded source counter
          (tapeAtCells [] (none :: outputRight))) =
      config halt source counter
        (tapeAtCells [none] outputRight) := by
  copier_step [hsource, hcounter]
  all_goals cases outputRight <;> rfl

theorem rewindDecoded_run_scan_withBoundary
    (source counter : Tape Bool)
    (hsource : source.head = some false)
    (hcounter : counter.head = none)
    (leftBits : List Bool) (current : Bool)
    (rightCells : List (Option Bool)) :
    description.runConfig (leftBits.length + 1)
        (config rewindDecoded source counter
          (tapeAtCells
            (List.append (leftBits.map some) [none])
            (some current :: rightCells))) =
      config rewindDecoded source counter
        (tapeAtCells []
          (none ::
            List.append
              ((List.append leftBits.reverse [current]).map some)
              rightCells)) := by
  induction leftBits generalizing current rightCells with
  | nil =>
      simpa using
        rewindDecoded_step_bit source counter hsource hcounter
          [] none current rightCells
  | cons next rest ih =>
      rw [show (next :: rest).length + 1 =
          1 + (rest.length + 1) by
        simp
        lia]
      rw [Structured.Description.runConfig_add]
      change
        description.runConfig (rest.length + 1)
          (description.runConfig 1
            (config rewindDecoded source counter
              (tapeAtCells
                (some next ::
                  List.append (rest.map some) [none])
                (some current :: rightCells)))) = _
      rw [rewindDecoded_step_bit source counter hsource hcounter]
      rw [ih next (some current :: rightCells)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

def rewindDecodedSourceTape
    (bits : List Bool) (rightCells : List (Option Bool)) : Tape Bool :=
  match bits.reverse with
  | [] =>
      tapeAtCells [] (none :: rightCells)
  | current :: leftBits =>
      tapeAtCells
        (List.append (leftBits.map some) [none])
        (some current :: rightCells)

theorem rewindDecoded_run
    (source counter : Tape Bool)
    (hsource : source.head = some false)
    (hcounter : counter.head = none)
    (bits : List Bool) (rightCells : List (Option Bool)) :
    description.runConfig (bits.length + 1)
        (config rewindDecoded source counter
          (rewindDecodedSourceTape bits rightCells)) =
      config halt source counter
        (tapeAtCells [none]
          (List.append (bits.map some) rightCells)) := by
  cases hreverse : bits.reverse with
  | nil =>
      have hbits : bits = [] := by
        simpa using congrArg List.reverse hreverse
      subst bits
      simpa [rewindDecodedSourceTape] using
        rewindDecoded_step_blank source counter hsource hcounter rightCells
  | cons current leftBits =>
      have hbits :
          bits = List.append leftBits.reverse [current] := by
        simpa [List.reverse_cons] using congrArg List.reverse hreverse
      unfold rewindDecodedSourceTape
      rw [hreverse]
      rw [hbits]
      rw [show
          (List.append leftBits.reverse [current]).length + 1 =
            (leftBits.length + 1) + 1 by
        simp]
      rw [Structured.Description.runConfig_add]
      change
        description.runConfig 1
          (description.runConfig (leftBits.length + 1)
            (config rewindDecoded source counter
              (tapeAtCells
                (List.append (leftBits.map some) [none])
                (some current :: rightCells)))) = _
      rw [rewindDecoded_run_scan_withBoundary
        source counter hsource hcounter]
      rw [rewindDecoded_step_blank source counter hsource hcounter]

theorem copyRestore_run
    (counter : Tape Bool) (hcounter : counter.head = none)
    (sourceBase outputBase : List (Option Bool))
    (sourceBoundary : Bool) (outputBoundary : Option Bool)
    (rightPadding : List (Option Bool))
    (suffix : List Bool) (current : Bool) (rest : List Bool)
    (hreverse : suffix.reverse = current :: rest) :
    description.runConfig (2 * suffix.length + 2)
        (config copySuffix
          (copySourceTape (some sourceBoundary :: sourceBase)
            [] suffix rightPadding)
          counter
          (copyOutputTape (outputBoundary :: outputBase) [])) =
      config rewindDecoded
        (tapeAtCells (some sourceBoundary :: sourceBase)
          (List.append (suffix.map some) (none :: rightPadding)))
        counter
        (tapeAtCells outputBase
          (outputBoundary ::
            List.append (suffix.map some) [none])) := by
  have hlength : suffix.length = rest.length + 1 := by
    have := congrArg List.length hreverse
    simpa using this
  have hsuffix :
      suffix = List.append rest.reverse [current] := by
    simpa [List.reverse_cons] using congrArg List.reverse hreverse
  rw [show 2 * suffix.length + 2 =
      suffix.length + (1 + (suffix.length + 1)) by
    lia]
  rw [Structured.Description.runConfig_add]
  rw [copySuffix_run_loop counter hcounter]
  rw [show List.append ([] : List Bool) suffix = suffix by rfl]
  rw [Structured.Description.runConfig_add]
  rw [hlength]
  simp only [copySourceTape, copyOutputTape, List.map_nil,
    List.length_nil, hlength, List.replicate_succ, hreverse,
    List.map_cons]
  rw [show
    List.append ([] : List (Option Bool)) (none :: rightPadding) =
      none :: rightPadding by rfl]
  change
    description.runConfig ((rest.length + 1) + 1)
      (description.runConfig 1
        (config copySuffix
          (tapeAtCells
            (none ::
              List.append
                (List.replicate rest.length (none : Option Bool))
                (some sourceBoundary :: sourceBase))
            (none :: rightPadding))
          counter
          (tapeAtCells
            (some current ::
              List.append (rest.map some)
                (outputBoundary :: outputBase))
            []))) = _
  rw [copySuffix_step_blank counter hcounter]
  rw [Structured.Description.runConfig_add]
  have hrestore :
      description.runConfig (rest.length + 1)
          (config restoreSuffix
            (tapeAtCells
              (List.append
                (List.replicate rest.length (none : Option Bool))
                (some sourceBoundary :: sourceBase))
              (none :: none :: rightPadding))
            counter
            (tapeAtCells
              (List.append (rest.map some)
                (outputBoundary :: outputBase))
              [some current, none])) =
        config restoreSuffix
          (tapeAtCells sourceBase
            (some sourceBoundary ::
              List.append (suffix.map some) (none :: rightPadding)))
          counter
          (tapeAtCells outputBase
            (outputBoundary ::
              List.append (suffix.map some) [none])) := by
    simpa [hsuffix, List.map_append, List.append_assoc] using
      restoreSuffix_run_loop counter hcounter
        sourceBase outputBase (some sourceBoundary) outputBoundary
        rightPadding [] current rest
  rw [hrestore]
  rw [restoreSuffix_step_boundary counter hcounter]

def sourcePrefixBits (bits : Word Bool) : List Bool :=
  List.append boolWordRawBitsDecoderHeaderBits
    (boolWordRawBitsDecoderEncodedFieldBits bits)

def sourceBaseLeft (bits : Word Bool) : List (Option Bool) :=
  List.append ((sourcePrefixBits bits).reverse.map some) [none]

def decodedOutputBaseLeft (bits : Word Bool) : List (Option Bool) :=
  List.append (bits.reverse.map some) [none]

theorem sourcePrefixBits_ne_nil (bits : Word Bool) :
    sourcePrefixBits bits ≠ [] := by
  simp [sourcePrefixBits, boolWordRawBitsDecoderHeaderBits,
    MachineDescription.encodeCodeSymbolAsInput]

theorem sourceTargetTape_eq_copySourceTape
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    structuredBoolWordRawBitsDecoderSourceTargetTape
        bits suffixTail rightPadding =
      copySourceTape (sourceBaseLeft bits) []
        (false :: suffixTail) rightPadding := by
  simp [structuredBoolWordRawBitsDecoderSourceTargetTape,
    sourceBaseLeft, sourcePrefixBits, copySourceTape,
    List.map_append, List.reverse_append, List.append_assoc]

theorem decodedStopTape_eq_copyOutputTape
    (bits : Word Bool) :
    decodedStopTape [none] bits =
      copyOutputTape (decodedOutputBaseLeft bits) [] := by
  simp [decodedStopTape, decodedOutputBaseLeft, copyOutputTape,
    tapeAtCells]

theorem copySourceTape_empty
    (baseLeft : List (Option Bool)) (suffix : Word Bool)
    (rightPadding : List (Option Bool)) :
    copySourceTape baseLeft [] suffix rightPadding =
      tapeAtCells baseLeft
        (List.append (suffix.map some) (none :: rightPadding)) := by
  simp [copySourceTape]

theorem copyRestore_run_actual
    (counter : Tape Bool) (hcounter : counter.head = none)
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    description.runConfig (2 * (false :: suffixTail).length + 2)
        (config copySuffix
          (structuredBoolWordRawBitsDecoderSourceTargetTape
            bits suffixTail rightPadding)
          counter
          (decodedStopTape [none] bits)) =
      config rewindDecoded
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          bits suffixTail rightPadding)
        counter
        (rewindDecodedSourceTape bits
          (List.append ((false :: suffixTail).map some) [none])) := by
  have hprefixReverse : (sourcePrefixBits bits).reverse ≠ [] := by
    intro hnil
    have hp : sourcePrefixBits bits = [] := by
      simpa using congrArg List.reverse hnil
    exact sourcePrefixBits_ne_nil bits hp
  rcases List.exists_cons_of_ne_nil hprefixReverse with
    ⟨sourceBoundary, sourceRest, hprefixReverse⟩
  have hsourceBase :
      sourceBaseLeft bits =
        some sourceBoundary ::
          List.append (sourceRest.map some) [none] := by
    simp [sourceBaseLeft, hprefixReverse]
  have hsuffixReverse : (false :: suffixTail).reverse ≠ [] := by
    simp
  rcases List.exists_cons_of_ne_nil hsuffixReverse with
    ⟨current, rest, hsuffixReverse⟩
  rw [sourceTargetTape_eq_copySourceTape,
    decodedStopTape_eq_copyOutputTape, hsourceBase]
  cases hbitsReverse : bits.reverse with
  | nil =>
      have houtputBase : decodedOutputBaseLeft bits = [none] := by
        simp [decodedOutputBaseLeft, hbitsReverse]
      rw [houtputBase]
      simpa [rewindDecodedSourceTape, hbitsReverse, hsourceBase,
        sourceTargetTape_eq_copySourceTape, copySourceTape_empty] using
        copyRestore_run counter hcounter
          (List.append (sourceRest.map some) [none]) []
          sourceBoundary none rightPadding
          (false :: suffixTail) current rest hsuffixReverse
  | cons outputBoundary outputRest =>
      have houtputBase :
          decodedOutputBaseLeft bits =
            some outputBoundary ::
              List.append (outputRest.map some) [none] := by
        simp [decodedOutputBaseLeft, hbitsReverse]
      rw [houtputBase]
      simpa [rewindDecodedSourceTape, hbitsReverse, hsourceBase,
        sourceTargetTape_eq_copySourceTape, copySourceTape_empty] using
        copyRestore_run counter hcounter
          (List.append (sourceRest.map some) [none])
          (List.append (outputRest.map some) [none])
          sourceBoundary (some outputBoundary) rightPadding
          (false :: suffixTail) current rest hsuffixReverse

theorem sourceTargetTape_head
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    (structuredBoolWordRawBitsDecoderSourceTargetTape
      bits suffixTail rightPadding).head = some false := by
  simp [structuredBoolWordRawBitsDecoderSourceTargetTape, tapeAtCells]

theorem counterDecodeTape_zero_head
    (blanksRight : Nat) :
    (structuredBoolWordRawBitsDecoderCounterDecodeTape
      0 blanksRight).head = none := by
  simp [structuredBoolWordRawBitsDecoderCounterDecodeTape, tapeAtCells]

theorem description_run
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    description.runConfig
        (2 * bits.length + 2 * (false :: suffixTail).length + 4)
        (sourceConfig bits suffixTail rightPadding) =
      targetConfig bits suffixTail rightPadding := by
  let source := structuredBoolWordRawBitsDecoderSourceTargetTape
    bits suffixTail rightPadding
  let counter := structuredBoolWordRawBitsDecoderCounterDecodeTape
    0 (bits.length + 1)
  have hsource : source.head = some false := by
    exact sourceTargetTape_head bits suffixTail rightPadding
  have hcounter : counter.head = none := by
    exact counterDecodeTape_zero_head (bits.length + 1)
  rw [show
      2 * bits.length + 2 * (false :: suffixTail).length + 4 =
        (bits.length + 1) +
          ((2 * (false :: suffixTail).length + 2) +
            (bits.length + 1)) by
    lia]
  rw [Structured.Description.runConfig_add]
  change
    description.runConfig
        ((2 * (false :: suffixTail).length + 2) +
          (bits.length + 1))
      (description.runConfig (bits.length + 1)
        (config seekDecodedStop source counter
          (rightEdgeScanSourceTapeFromLeft [none] bits []))) = _
  have hseek :=
    seekDecodedStop_run source counter hsource hcounter [none] bits
  change
    description.runConfig (bits.length + 1)
        (config seekDecodedStop source counter
          (rightEdgeScanSourceTapeFromLeft [none] bits [])) =
      config copySuffix source counter
        (decodedStopTape [none] bits) at hseek
  rw [hseek]
  rw [Structured.Description.runConfig_add]
  change
    description.runConfig (bits.length + 1)
      (description.runConfig
        (2 * (false :: suffixTail).length + 2)
        (config copySuffix source counter
          (decodedStopTape [none] bits))) = _
  rw [copyRestore_run_actual counter hcounter bits suffixTail rightPadding]
  rw [rewindDecoded_run source counter hsource hcounter bits]
  simp [targetConfig, source, counter,
    rightEdgeScanSourceTapeFromLeft, List.map_append,
    List.append_assoc]

theorem description_supported :
    SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

theorem description_wellFormed : description.WellFormed := by
  apply structuredDescription_wellFormed_of_bool
  decide

theorem description_haltTransitionFree :
    description.HaltTransitionFree := by
  apply structuredDescription_haltTransitionFree_of_bool
  decide

def loweredDescription : MachineDescription :=
  lowerStructured3Description description

theorem loweredDescription_subroutineReady :
    loweredDescription.SubroutineReady := by
  simpa [loweredDescription] using
    lowerStructured3Description_subroutineReady
      description_wellFormed description_supported

theorem loweredDescription_haltsFromTapeEquiv
    (bits suffixTail : Word Bool)
    (rightPadding : List (Option Bool)) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          bits suffixTail rightPadding)
        (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
          (bits.length + 1))
        (rightEdgeScanSourceTapeFromLeft [none] bits []))
      (encodedGuardedStructured3Tapes
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          bits suffixTail rightPadding)
        (structuredBoolWordRawBitsDecoderCounterDecodeTape 0
          (bits.length + 1))
        (rightEdgeScanSourceTapeFromLeft [none]
          (List.append bits (false :: suffixTail)) [])) := by
  simpa [loweredDescription, encodedGuardedStructured3Tapes,
    sourceConfig, targetConfig] using
    lowerStructured3Description_haltsFromConfigWithTapes
      description_wellFormed description_haltTransitionFree
      description_supported
      (c := sourceConfig bits suffixTail rightPadding)
      (tapes :=
        [ structuredBoolWordRawBitsDecoderSourceTargetTape
            bits suffixTail rightPadding
        , structuredBoolWordRawBitsDecoderCounterDecodeTape 0
            (bits.length + 1)
        , rightEdgeScanSourceTapeFromLeft [none]
            (List.append bits (false :: suffixTail)) [] ])
      rfl rfl
      ⟨2 * bits.length + 2 * (false :: suffixTail).length + 4,
        description_run bits suffixTail rightPadding⟩

end PostDecodeSuffixCopier
end NestedLayoutMaterializerInternal
end ThreeTape
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
