import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.OutputLengthAllocator
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeTactic

set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace CommonGround
namespace FiniteTransducers
namespace Structured
namespace MultiTapeLowering
namespace ThreeTape
namespace CountWindowInputMat
namespace InPlaceDecoder

open EncRewriters.CanonicalLayouts.DovetailLayoutScanner

theorem wordAppend_assoc (a b c : Word Bool) :
    List.append (List.append a b) c =
      List.append a (List.append b c) := by
  exact List.append_assoc a b c

def header1 : Nat := 0
def header2 : Nat := 1
def header3 : Nat := 2
def header4 : Nat := 3
def field1 : Nat := 4
def field2 : Nat := 5
def field3 : Nat := 6
def field4 : Nat := 7
def markerSentinel : Nat := 8
def markerRewind : Nat := 9
def decode1 : Nat := 10
def decode2 : Nat := 11
def decode3 : Nat := 12
def decode4False : Nat := 13
def decode4True : Nat := 14
def decodedRewind : Nat := 15
def halt : Nat := 16

def rowsForSourceRead
    (source : Nat) (sourceRead : Option Bool)
    (action0 action1 action2 : TapeAction)
    (target : Nat) : List Transition :=
  allReads2
    (fun read1 read2 =>
      row source sourceRead read1 read2
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
  [ rowsForSourceRead header1 (some false) keepR keepS keepS header2
  , rowsForSourceRead header2 (some false) keepR keepS keepS header3
  , rowsForSourceRead header3 (some false) keepR keepS keepS header4
  , rowsForSourceRead header4 (some false) keepR keepS keepS field1
  , rowsForSourceRead field1 (some false) keepR keepS keepS field2
  , rowsForSourceRead field2 (some false) keepR keepS keepS field3
  , rowsForSourceRead field3 (some true) keepR keepS keepS field4
  , rowsForSourceOutputRead field4 (some false) none
      keepR keepS (writeBitR true) field1
  , rowsForSourceOutputRead field4 (some true) none
      keepR keepS keepS markerSentinel
  , rowsForOutputRead markerSentinel none keepS keepS keepL markerRewind
  , rowsForOutputRead markerRewind (some true) keepS keepS keepL markerRewind
  , rowsForOutputRead markerRewind none keepS keepS keepR decode1
  , rowsForSourceOutputRead decode1 (some false) (some true)
      keepR keepS keepS decode2
  , rowsForSourceOutputRead decode1 (some false) none
      keepS keepS keepL decodedRewind
  , rowsForSourceOutputRead decode2 (some true) (some true)
      keepR keepS keepS decode3
  , rowsForSourceOutputRead decode3 (some false) (some true)
      keepR keepS keepS decode4False
  , rowsForSourceOutputRead decode3 (some true) (some true)
      keepR keepS keepS decode4True
  , rowsForSourceOutputRead decode4False (some true) (some true)
      keepR keepS (writeBitR false) decode1
  , rowsForSourceOutputRead decode4True (some false) (some true)
      keepR keepS (writeBitR true) decode1
  , rowsForOutputRead decodedRewind (some false)
      keepS keepS keepL decodedRewind
  , rowsForOutputRead decodedRewind (some true)
      keepS keepS keepL decodedRewind
  , rowsForOutputRead decodedRewind none
      keepS keepS keepR halt ].flatten

def description : Description :=
  ThreeTape.description 17 header1 halt rows

syntax "decoder_step " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| decoder_step [$lemmas,*]) =>
      `(tactic|
        three_tape_step [
          description, rows, rowsForSourceRead, rowsForOutputRead,
          rowsForSourceOutputRead, allReads1, allReads2, allReadCells,
          List.find?,
          header1, header2, header3, header4, field1, field2, field3,
          field4, markerSentinel, markerRewind, decode1, decode2, decode3,
          decode4False, decode4True, decodedRewind, halt, $lemmas,*])

theorem description_subroutineReady : description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool description (by decide)

theorem description_supports : SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

def scanTape
    (left : List (Option Bool)) (bits : Word Bool) : Tape Bool :=
  tapeAtCells (List.append left [none])
    (List.append (bits.map some) [none])

def markedOutputTape (marked remaining : Nat) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate marked (some true : Option Bool)) [none])
    (List.replicate (remaining + 1) (none : Option Bool))


theorem header_run
    (stage tail : Word Bool) (n : Nat) :
    description.runConfig 4
        (config header1
          (rightEdgeRewindTargetTape
            (List.append [false, false, false, false]
              (List.append stage tail)) [])
          Tape.blank
          (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
            n [])) =
      config field1
        (scanTape [some false, some false, some false, some false]
          (List.append stage tail))
        Tape.blank (markedOutputTape 0 n) := by
  cases stage <;> cases tail <;> cases n <;>
    decoder_step [scanTape, markedOutputTape,
      structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding,
      rightEdgeRewindTargetTape, List.replicate_succ, List.append_assoc,
      tapeAtCells]

theorem tick_run
    (left : List (Option Bool)) (rest : Word Bool)
    (marked remaining : Nat) :
    description.runConfig 4
        (config field1
          (scanTape left
            (List.append [false, false, true, false] rest))
          Tape.blank (markedOutputTape marked (remaining + 1))) =
      config field1
        (scanTape
          (some false :: some true :: some false :: some false :: left)
          rest)
        Tape.blank (markedOutputTape (marked + 1) remaining) := by
  cases rest <;> cases marked <;> cases remaining <;>
    decoder_step [scanTape, markedOutputTape, List.replicate_succ,
      List.append_assoc, tapeAtCells]

theorem done_run
    (left : List (Option Bool)) (tail : Word Bool) (marked : Nat) :
    description.runConfig 4
        (config field1
          (scanTape left
            (List.append [false, false, true, true] tail))
          Tape.blank (markedOutputTape marked 0)) =
      config markerSentinel
        (scanTape
          (some true :: some true :: some false :: some false :: left)
          tail)
        Tape.blank (markedOutputTape marked 0) := by
  cases tail <;> cases marked <;>
    decoder_step [scanTape, markedOutputTape, List.replicate_succ,
      List.append_assoc, tapeAtCells]

theorem unary_run
    (processed tail : Word Bool) (n marked : Nat) :
    description.runConfig (4 * (n + 1))
        (config field1
          (scanTape (processed.reverse.map some)
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                n)
              tail))
          Tape.blank (markedOutputTape marked n)) =
      config markerSentinel
        (scanTape
          ((List.append processed
            (List.append (OutputLengthAllocator.tickStream n)
              [false, false, true, true])).reverse.map some)
          tail)
        Tape.blank (markedOutputTape (marked + n) 0) := by
  induction n generalizing processed marked with
  | zero =>
      simpa [OutputLengthAllocator.tickStream] using
        done_run (processed.reverse.map some) tail marked
  | succ n ih =>
      rw [show 4 * (n + 1 + 1) = 4 + 4 * (n + 1) by lia]
      rw [Description.runConfig_add]
      change
        description.runConfig (4 * (n + 1))
          (description.runConfig 4
            (config field1
              (scanTape (processed.reverse.map some)
                (List.append [false, false, true, false]
                  (List.append
                    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                      n)
                    tail)))
              Tape.blank (markedOutputTape marked (n + 1)))) = _
      rw [tick_run]
      have hleft :
          some false :: some true :: some false :: some false ::
              processed.reverse.map some =
            (List.append processed [false, false, true, false]).reverse.map
              some := by
        simp [List.reverse_append, List.map_append, List.append_assoc]
      rw [hleft]
      simpa [OutputLengthAllocator.tickStream, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (List.append processed [false, false, true, false]) (marked + 1)

def markerRewindTape (remaining processed : Nat) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate remaining (some true : Option Bool)) [none])
    (some true ::
      List.append
        (List.replicate processed (some true : Option Bool)) [none])

def decodeInputTape (count : Nat) : Tape Bool :=
  tapeAtCells [none]
    (List.append
      (List.replicate count (some true : Option Bool)) [none])

theorem marker_sentinel_zero_step
    (left : List (Option Bool)) (rest : Word Bool) :
    description.runConfig 1
        (config markerSentinel (scanTape left (false :: rest)) Tape.blank
          (markedOutputTape 0 0)) =
      config markerRewind (scanTape left (false :: rest)) Tape.blank
        (tapeAtCells [] [none, none]) := by
  cases rest <;>
    decoder_step [scanTape, markedOutputTape, List.replicate_succ,
      tapeAtCells]

theorem marker_sentinel_succ_step
    (left : List (Option Bool)) (rest : Word Bool) (remaining : Nat) :
    description.runConfig 1
        (config markerSentinel (scanTape left (false :: rest)) Tape.blank
          (markedOutputTape (remaining + 1) 0)) =
      config markerRewind (scanTape left (false :: rest)) Tape.blank
        (markerRewindTape remaining 0) := by
  cases rest <;> cases remaining <;>
    decoder_step [scanTape, markedOutputTape, markerRewindTape,
      List.replicate_succ, List.append_assoc, tapeAtCells]

theorem marker_rewind_step_succ
    (left : List (Option Bool)) (rest : Word Bool)
    (remaining processed : Nat) :
    description.runConfig 1
        (config markerRewind (scanTape left (false :: rest)) Tape.blank
          (markerRewindTape (remaining + 1) processed)) =
      config markerRewind (scanTape left (false :: rest)) Tape.blank
        (markerRewindTape remaining (processed + 1)) := by
  cases rest <;> cases remaining <;> cases processed <;>
    decoder_step [scanTape, markerRewindTape, List.replicate_succ,
      List.append_assoc, tapeAtCells]

theorem marker_rewind_step_zero
    (left : List (Option Bool)) (rest : Word Bool) (processed : Nat) :
    description.runConfig 1
        (config markerRewind (scanTape left (false :: rest)) Tape.blank
          (markerRewindTape 0 processed)) =
      config markerRewind (scanTape left (false :: rest)) Tape.blank
        (tapeAtCells []
          (none ::
            List.append
              (List.replicate (processed + 1) (some true : Option Bool))
              [none])) := by
  cases rest <;> cases processed <;>
    decoder_step [scanTape, markerRewindTape, List.replicate_succ,
      List.append_assoc, tapeAtCells]

theorem marker_rewind_run
    (left : List (Option Bool)) (rest : Word Bool)
    (remaining processed : Nat) :
    description.runConfig (remaining + 1)
        (config markerRewind (scanTape left (false :: rest)) Tape.blank
          (markerRewindTape remaining processed)) =
      config markerRewind (scanTape left (false :: rest)) Tape.blank
        (tapeAtCells []
          (none ::
            List.append
              (List.replicate (remaining + processed + 1)
                (some true : Option Bool))
              [none])) := by
  induction remaining generalizing processed with
  | zero =>
      simpa using marker_rewind_step_zero left rest processed
  | succ remaining ih =>
      rw [show remaining + 1 + 1 = 1 + (remaining + 1) by lia]
      rw [Description.runConfig_add]
      rw [marker_rewind_step_succ]
      rw [ih (processed + 1)]
      congr 4
      lia

theorem marker_rewind_finish_step
    (left : List (Option Bool)) (rest : Word Bool) (count : Nat) :
    description.runConfig 1
        (config markerRewind (scanTape left (false :: rest)) Tape.blank
          (tapeAtCells []
            (none ::
              List.append
                (List.replicate count (some true : Option Bool)) [none]))) =
      config decode1 (scanTape left (false :: rest)) Tape.blank
        (decodeInputTape count) := by
  cases rest <;> cases count <;>
    decoder_step [scanTape, decodeInputTape, List.replicate_succ,
      List.append_assoc, tapeAtCells]

theorem marker_return_run
    (left : List (Option Bool)) (rest : Word Bool) (count : Nat) :
    description.runConfig (count + 2)
        (config markerSentinel (scanTape left (false :: rest)) Tape.blank
          (markedOutputTape count 0)) =
      config decode1 (scanTape left (false :: rest)) Tape.blank
        (decodeInputTape count) := by
  cases count with
  | zero =>
      rw [show 0 + 2 = 1 + 1 by rfl]
      rw [Description.runConfig_add]
      rw [marker_sentinel_zero_step]
      simpa [List.replicate] using
        marker_rewind_finish_step left rest 0
  | succ count =>
      rw [show count + 1 + 2 = 1 + ((count + 1) + 1) by lia]
      rw [Description.runConfig_add]
      rw [marker_sentinel_succ_step]
      rw [Description.runConfig_add]
      rw [marker_rewind_run left rest count 0]
      rw [marker_rewind_finish_step]

def decodedOutputTape
    (processed : Word Bool) (remaining : Nat) : Tape Bool :=
  tapeAtCells
    (List.append (processed.reverse.map some) [none])
    (List.append
      (List.replicate remaining (some true : Option Bool)) [none])

theorem decodedOutputTape_nil (remaining : Nat) :
    decodedOutputTape [] remaining = decodeInputTape remaining := by
  rfl

theorem decode_bit_run
    (left : List (Option Bool)) (bit : Bool) (rest : Word Bool)
    (processed : Word Bool) (remaining : Nat) :
    description.runConfig 4
        (config decode1
          (scanTape left
            (List.append (cellCodeBits (some bit)) rest))
          Tape.blank (decodedOutputTape processed (remaining + 1))) =
      config decode1
        (scanTape
          (List.append ((cellCodeBits (some bit)).reverse.map some) left)
          rest)
        Tape.blank
        (decodedOutputTape (List.append processed [bit]) remaining) := by
  cases bit <;> cases rest <;> cases processed <;> cases remaining <;>
    decoder_step [scanTape, decodedOutputTape, cellCodeBits, encodeCell,
      encodeCodeWordAsInput, encodeCodeSymbolAsInput, List.replicate_succ,
      List.reverse_append, List.map_append, List.append_assoc, tapeAtCells]

theorem decode_bits_run
    (left : List (Option Bool)) (bits rest processed : Word Bool) :
    description.runConfig (4 * bits.length)
        (config decode1
          (scanTape left
            (List.append (cellsCodeBits (bits.map some)) rest))
          Tape.blank (decodedOutputTape processed bits.length)) =
      config decode1
        (scanTape
          (List.append
            ((cellsCodeBits (bits.map some)).reverse.map some) left)
          rest)
        Tape.blank
        (decodedOutputTape (List.append processed bits) 0) := by
  induction bits generalizing left processed with
  | nil =>
      simp [cellsCodeBits, Description.runConfig]
  | cons bit bits ih =>
      simp only [List.map_cons, cellsCodeBits, List.length_cons]
      rw [show 4 * (bits.length + 1) = 4 + 4 * bits.length by lia]
      rw [Description.runConfig_add]
      rw [wordAppend_assoc]
      change
        description.runConfig (4 * bits.length)
          (description.runConfig 4
            (config decode1
              (scanTape left
                (List.append (cellCodeBits (some bit))
                  (List.append (cellsCodeBits (bits.map some)) rest)))
              Tape.blank
              (decodedOutputTape processed (bits.length + 1)))) = _
      rw [decode_bit_run]
      simpa [cellsCodeBits, List.reverse_append, List.map_append,
        List.append_assoc] using
        ih
          (List.append ((cellCodeBits (some bit)).reverse.map some) left)
          (List.append processed [bit])

theorem decode_bits_from_empty_run
    (left : List (Option Bool)) (bits rest : Word Bool) :
    description.runConfig (4 * bits.length)
        (config decode1
          (scanTape left
            (List.append (cellsCodeBits (bits.map some)) rest))
          Tape.blank (decodeInputTape bits.length)) =
      config decode1
        (scanTape
          (List.append
            ((cellsCodeBits (bits.map some)).reverse.map some) left)
          rest)
        Tape.blank (decodedOutputTape bits 0) := by
  rw [← decodedOutputTape_nil]
  have h := decode_bits_run left bits rest []
  have hnil :
      (List.append ([] : Word Bool) bits : Word Bool) = bits := by
    cases bits <;> rfl
  rw [hnil] at h
  exact h

def decodedRewindTape
    (remaining : Word Bool) (current : Bool)
    (processed : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append (remaining.map some) [none])
    (some current :: List.append (processed.map some) [none])

theorem decoded_sentinel_empty_step
    (left : List (Option Bool)) (suffix : Word Bool) :
    description.runConfig 1
        (config decode1 (scanTape left (false :: suffix)) Tape.blank
          (decodedOutputTape [] 0)) =
      config decodedRewind (scanTape left (false :: suffix)) Tape.blank
        (tapeAtCells [] [none, none]) := by
  cases suffix <;>
    decoder_step [scanTape, decodedOutputTape, List.replicate_succ,
      tapeAtCells]

theorem decoded_sentinel_nonempty_step
    (left : List (Option Bool)) (suffix : Word Bool)
    (current : Bool) (remaining : Word Bool) :
    description.runConfig 1
        (config decode1 (scanTape left (false :: suffix)) Tape.blank
          (decodedOutputTape ((current :: remaining).reverse) 0)) =
      config decodedRewind (scanTape left (false :: suffix)) Tape.blank
        (decodedRewindTape remaining current []) := by
  cases suffix <;> cases current <;> cases remaining <;>
    decoder_step [scanTape, decodedOutputTape, decodedRewindTape,
      List.replicate_succ, List.reverse_append, List.map_append,
      List.append_assoc, tapeAtCells]

theorem decoded_rewind_step
    (left : List (Option Bool)) (suffix : Word Bool)
    (remaining : Word Bool) (current : Bool) (processed : Word Bool) :
    description.runConfig 1
        (config decodedRewind (scanTape left (false :: suffix)) Tape.blank
          (decodedRewindTape remaining current processed)) =
      match remaining with
      | [] =>
          config decodedRewind (scanTape left (false :: suffix)) Tape.blank
            (tapeAtCells []
              (none :: List.append ((current :: processed).map some)
                [none]))
      | next :: tail =>
          config decodedRewind (scanTape left (false :: suffix)) Tape.blank
            (decodedRewindTape tail next (current :: processed)) := by
  cases remaining with
  | nil =>
      cases suffix <;> cases current <;> cases processed <;>
        decoder_step [scanTape, decodedRewindTape, List.append_assoc,
          tapeAtCells]
  | cons next tail =>
      cases suffix <;> cases current <;> cases next <;> cases tail <;>
        cases processed <;>
          decoder_step [scanTape, decodedRewindTape, List.append_assoc,
            tapeAtCells]

theorem decoded_rewind_run
    (left : List (Option Bool)) (suffix : Word Bool)
    (remaining : Word Bool) (current : Bool) (processed : Word Bool) :
    description.runConfig (remaining.length + 1)
        (config decodedRewind (scanTape left (false :: suffix)) Tape.blank
          (decodedRewindTape remaining current processed)) =
      config decodedRewind (scanTape left (false :: suffix)) Tape.blank
        (tapeAtCells []
          (none :: List.append
            ((List.append remaining.reverse (current :: processed)).map some)
            [none])) := by
  induction remaining generalizing current processed with
  | nil =>
      simpa [decodedRewindTape] using
        decoded_rewind_step left suffix [] current processed
  | cons next tail ih =>
      rw [show (next :: tail).length + 1 = 1 + (tail.length + 1) by
        simp
        lia]
      rw [Description.runConfig_add]
      rw [decoded_rewind_step]
      rw [ih next (current :: processed)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem decoded_rewind_finish_step
    (left : List (Option Bool)) (suffix bits : Word Bool) :
    description.runConfig 1
        (config decodedRewind (scanTape left (false :: suffix)) Tape.blank
          (tapeAtCells []
            (none :: List.append (bits.map some) [none]))) =
      config halt (scanTape left (false :: suffix)) Tape.blank
        (rightEdgeScanSourceTapeFromLeft [none] bits []) := by
  cases suffix <;> cases bits <;>
    decoder_step [scanTape, rightEdgeScanSourceTapeFromLeft,
      List.append_assoc, tapeAtCells]

theorem decoded_rewind_from_sentinel
    (left : List (Option Bool)) (suffix bits : Word Bool) :
    description.runConfig (bits.length + 2)
        (config decode1 (scanTape left (false :: suffix)) Tape.blank
          (decodedOutputTape bits 0)) =
      config halt (scanTape left (false :: suffix)) Tape.blank
        (rightEdgeScanSourceTapeFromLeft [none] bits []) := by
  cases hrev : bits.reverse with
  | nil =>
      cases bits with
      | nil =>
          rw [show [].length + 2 = 1 + 1 by rfl]
          rw [Description.runConfig_add]
          rw [decoded_sentinel_empty_step]
          simpa using decoded_rewind_finish_step left suffix []
      | cons bit bits =>
          simp at hrev
  | cons current remaining =>
      have hword : (current :: remaining).reverse = bits := by
        rw [← hrev]
        simp
      have hlen : remaining.length + 1 = bits.length := by
        have := congrArg List.length hrev
        simp at this
        lia
      rw [show bits.length + 2 =
          1 + ((remaining.length + 1) + 1) by lia]
      rw [Description.runConfig_add]
      rw [← hword]
      rw [decoded_sentinel_nonempty_step]
      rw [Description.runConfig_add]
      rw [decoded_rewind_run left suffix remaining current []]
      rw [show List.append remaining.reverse [current] =
          (current :: remaining).reverse by simp]
      rw [hword]
      rw [decoded_rewind_finish_step]

def fieldTail (bits suffixTail : Word Bool) : Word Bool :=
  List.append (cellsCodeBits (bits.map some)) (false :: suffixTail)

def fieldTailRest (bits suffixTail : Word Bool) : Word Bool :=
  (fieldTail bits suffixTail).tail

theorem fieldTail_eq_false_cons
    (bits suffixTail : Word Bool) :
    fieldTail bits suffixTail = false :: fieldTailRest bits suffixTail := by
  cases bits with
  | nil => rfl
  | cons bit bits =>
      cases bit <;>
        rfl

theorem processedPrefix_eq_header_stage (n : Nat) :
    OutputLengthAllocator.processedPrefix n =
      List.append [false, false, false, false]
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          n) := by
  rw [OutputLengthAllocator.processedPrefix,
    OutputLengthAllocator.stageNatBits_eq_tickStream_append_done]

theorem decoded_source_eq_target
    (bits suffixTail : Word Bool) :
    scanTape
        (List.append
          ((cellsCodeBits (bits.map some)).reverse.map some)
          ((OutputLengthAllocator.processedPrefix bits.length).reverse.map
            some))
        (false :: suffixTail) =
      structuredBoolWordRawBitsDecoderSourceTargetTape
        bits suffixTail [] := by
  rw [processedPrefix_eq_header_stage]
  simp [scanTape, structuredBoolWordRawBitsDecoderSourceTargetTape,
    boolWordRawBitsDecoderHeaderBits,
    boolWordRawBitsDecoderEncodedFieldBits, encodeCodeSymbolAsInput,
    List.reverse_append, List.map_append, List.append_assoc, tapeAtCells]

theorem parse_field_run (bits suffixTail : Word Bool) :
    description.runConfig (4 * (bits.length + 1))
        (config field1
          (scanTape [some false, some false, some false, some false]
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                bits.length)
              (fieldTail bits suffixTail)))
          Tape.blank (markedOutputTape 0 bits.length)) =
      config markerSentinel
        (scanTape
          ((OutputLengthAllocator.processedPrefix bits.length).reverse.map
            some)
          (fieldTail bits suffixTail))
        Tape.blank (markedOutputTape bits.length 0) := by
  simpa [OutputLengthAllocator.processedPrefix] using
    unary_run
      (show Word Bool from [false, false, false, false])
      (fieldTail bits suffixTail) bits.length 0

def fullFuel (bits : Word Bool) : Nat :=
  4 +
    (4 * (bits.length + 1) +
      ((bits.length + 2) +
        (4 * bits.length + (bits.length + 2))))

theorem full_run (bits suffixTail : Word Bool) :
    description.runConfig (fullFuel bits)
        (config header1
          (rightEdgeRewindTargetTape
            (OutputLengthAllocator.rawWord bits.length
              (fieldTail bits suffixTail)) [])
          Tape.blank
          (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
            bits.length [])) =
      config halt
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          bits suffixTail [])
        Tape.blank
        (rightEdgeScanSourceTapeFromLeft [none] bits []) := by
  rw [fullFuel]
  rw [Description.runConfig_add]
  change
    description.runConfig
        (4 * (bits.length + 1) +
          ((bits.length + 2) +
            (4 * bits.length + (bits.length + 2))))
      (description.runConfig 4
        (config header1
          (rightEdgeRewindTargetTape
            (List.append [false, false, false, false]
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                  bits.length)
                (fieldTail bits suffixTail))) [])
          Tape.blank
          (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
            bits.length []))) = _
  rw [header_run]
  rw [Description.runConfig_add]
  rw [parse_field_run]
  rw [fieldTail_eq_false_cons]
  rw [Description.runConfig_add]
  rw [marker_return_run]
  rw [← fieldTail_eq_false_cons bits suffixTail]
  change
    description.runConfig (4 * bits.length + (bits.length + 2))
      (config decode1
        (scanTape
          ((OutputLengthAllocator.processedPrefix bits.length).reverse.map
            some)
          (List.append (cellsCodeBits (bits.map some))
            (false :: suffixTail)))
        Tape.blank (decodeInputTape bits.length)) = _
  rw [Description.runConfig_add]
  rw [decode_bits_from_empty_run]
  rw [decoded_rewind_from_sentinel]
  rw [decoded_source_eq_target]

def loweredDescription : MachineDescription :=
  lowerStructured3Description description

theorem loweredDescription_subroutineReady :
    loweredDescription.SubroutineReady := by
  simpa [loweredDescription] using
    lowerStructured3Description_subroutineReady
      description_subroutineReady.left description_supports

theorem loweredDescription_haltsFromTapeEquiv
    (bits suffixTail : Word Bool) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rightEdgeRewindTargetTape
          (OutputLengthAllocator.rawWord bits.length
            (fieldTail bits suffixTail)) [])
        Tape.blank
        (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
          bits.length []))
      (encodedGuardedStructured3Tapes
        (structuredBoolWordRawBitsDecoderSourceTargetTape
          bits suffixTail [])
        Tape.blank
        (rightEdgeScanSourceTapeFromLeft [none] bits [])) := by
  simpa [loweredDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      description_subroutineReady.left description_subroutineReady.right
      description_supports
      (c := config header1
        (rightEdgeRewindTargetTape
          (OutputLengthAllocator.rawWord bits.length
            (fieldTail bits suffixTail)) [])
        Tape.blank
        (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
          bits.length []))
      (tapes :=
        [ structuredBoolWordRawBitsDecoderSourceTargetTape
            bits suffixTail []
        , Tape.blank
        , rightEdgeScanSourceTapeFromLeft [none] bits [] ])
      rfl rfl ⟨fullFuel bits, full_run bits suffixTail⟩

end InPlaceDecoder
end CountWindowInputMat
end ThreeTape
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
