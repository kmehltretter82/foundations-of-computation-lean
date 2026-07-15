import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.Shapes
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
namespace CountWindowInputMat
namespace OutputLengthAllocator

def header1 : Nat := 0
def header2 : Nat := 1
def header3 : Nat := 2
def header4 : Nat := 3
def field1 : Nat := 4
def field2 : Nat := 5
def field3 : Nat := 6
def field4 : Nat := 7
def scanTail : Nat := 8
def restoreOutput : Nat := 9
def rewindBoundary : Nat := 10
def rewindBits : Nat := 11
def halt : Nat := 12

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

def rows : List Transition :=
  [ rowsForSourceRead header1 (some false) keepR keepS keepS header2
  , rowsForSourceRead header2 (some false) keepR keepS keepS header3
  , rowsForSourceRead header3 (some false) keepR keepS keepS header4
  , rowsForSourceRead header4 (some false) keepR keepS keepS field1
  , rowsForSourceRead field1 (some false) keepR keepS keepS field2
  , rowsForSourceRead field2 (some false) keepR keepS keepS field3
  , rowsForSourceRead field3 (some true) keepR keepS keepS field4
  , rowsForSourceRead field4 (some false) keepR keepS
      (writeBitR true) field1
  , rowsForSourceRead field4 (some true) keepR keepS
      (writeS (some true)) scanTail
  , rowsForSourceRead scanTail (some false) keepR keepS keepS scanTail
  , rowsForSourceRead scanTail (some true) keepR keepS keepS scanTail
  , rowsForSourceRead scanTail none keepS keepS keepS restoreOutput
  , rowsForOutputRead restoreOutput (some true) keepS keepS eraseL
      restoreOutput
  , rowsForOutputRead restoreOutput none keepS keepS keepR rewindBoundary
  , rowsForSourceRead rewindBoundary none keepL keepS keepS rewindBits
  , rowsForSourceRead rewindBits (some false) keepL keepS keepS rewindBits
  , rowsForSourceRead rewindBits (some true) keepL keepS keepS rewindBits
  , rowsForSourceRead rewindBits none keepR keepS keepS halt ].flatten

def description : Description :=
  ThreeTape.description 13 header1 halt rows

syntax "allocator_step " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| allocator_step [$lemmas,*]) =>
      `(tactic|
        three_tape_step [
          description, rows, rowsForSourceRead, rowsForOutputRead,
          allReads2, allReadCells, List.find?, header1, header2, header3,
          header4, field1, field2, field3, field4, scanTail,
          restoreOutput, rewindBoundary, rewindBits, halt, $lemmas,*])

theorem description_subroutineReady : description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool description (by decide)

theorem description_supports : SupportsReadWriteRows3 description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

def scanTape
    (left : List (Option Bool)) (bits : Word Bool) : Tape Bool :=
  tapeAtCells left (bits.map some)

def markerTape (count : Nat) : Tape Bool :=
  tapeAtCells
    (List.replicate count (some true : Option Bool)) []

def markerCurrentTape (count : Nat) : Tape Bool :=
  tapeAtCells
    (List.replicate count (some true : Option Bool)) [some true]

def tickStream : Nat -> Word Bool
  | 0 => []
  | n + 1 =>
      List.append [false, false, true, false] (tickStream n)

theorem stageNatBits_eq_tickStream_append_done (n : Nat) :
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits n =
      List.append (tickStream n) [false, false, true, true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
        ih]
      rfl

theorem header_run
    (stage tail : Word Bool) :
    description.runConfig 4
        (config header1
          (Tape.input
            (List.append [false, false, false, false]
              (List.append stage tail)))
          Tape.blank Tape.blank) =
      config field1
        (scanTape [some false, some false, some false, some false]
          (List.append stage tail))
        Tape.blank Tape.blank := by
  cases stage <;> cases tail <;>
    allocator_step [scanTape, Tape.input]

theorem tick_run
    (left : List (Option Bool)) (rest : Word Bool) (count : Nat) :
    description.runConfig 4
        (config field1
          (scanTape left
            (List.append [false, false, true, false] rest))
          Tape.blank (markerTape count)) =
      config field1
        (scanTape
          (some false :: some true :: some false :: some false :: left)
          rest)
        Tape.blank (markerTape (count + 1)) := by
  cases rest <;> cases count <;>
    allocator_step [scanTape, markerTape, List.replicate_succ]

theorem done_run
    (left : List (Option Bool)) (tail : Word Bool) (count : Nat) :
    description.runConfig 4
        (config field1
          (scanTape left
            (List.append [false, false, true, true] tail))
          Tape.blank (markerTape count)) =
      config scanTail
        (scanTape
          (some true :: some true :: some false :: some false :: left)
          tail)
        Tape.blank (markerCurrentTape count) := by
  cases tail <;> cases count <;>
    allocator_step [scanTape, markerTape, markerCurrentTape,
      List.replicate_succ]

theorem parse_run
    (processed tail : Word Bool) (n count : Nat) :
    description.runConfig (4 * (n + 1))
        (config field1
          (scanTape (processed.reverse.map some)
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits n)
              tail))
          Tape.blank (markerTape count)) =
      config scanTail
        (scanTape
          ((List.append processed
            (List.append (tickStream n) [false, false, true, true])).reverse.map
              some)
          tail)
        Tape.blank (markerCurrentTape (count + n)) := by
  induction n generalizing processed count with
  | zero =>
      simpa [tickStream] using
        done_run (processed.reverse.map some) tail count
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
                    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits n)
                    tail)))
              Tape.blank (markerTape count))) = _
      rw [tick_run]
      have hleft :
          some false :: some true :: some false :: some false ::
              processed.reverse.map some =
            (List.append processed [false, false, true, false]).reverse.map
              some := by
        simp [List.reverse_append, List.map_append, List.append_assoc]
      rw [hleft]
      simpa [tickStream, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        ih (List.append processed [false, false, true, false]) (count + 1)

theorem scanTail_step_bit
    (left : List (Option Bool)) (bit : Bool) (rest : Word Bool)
    (count : Nat) :
    description.runConfig 1
        (config scanTail (scanTape left (bit :: rest)) Tape.blank
          (markerCurrentTape count)) =
      config scanTail (scanTape (some bit :: left) rest) Tape.blank
        (markerCurrentTape count) := by
  cases bit <;> cases rest <;> cases count <;>
    allocator_step [scanTape, markerCurrentTape, List.replicate_succ]

theorem scanTail_run
    (left : List (Option Bool)) (bits : Word Bool) (count : Nat) :
    description.runConfig bits.length
        (config scanTail (scanTape left bits) Tape.blank
          (markerCurrentTape count)) =
      config scanTail
        (scanTape (List.append (bits.reverse.map some) left) []) Tape.blank
        (markerCurrentTape count) := by
  induction bits generalizing left with
  | nil =>
      simp [Description.runConfig, scanTape]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by simp; lia]
      rw [Description.runConfig_add]
      rw [scanTail_step_bit]
      rw [ih]
      simp [scanTape, List.reverse_cons, List.map_append,
        List.append_assoc]

theorem scanTail_finish
    (left : List (Option Bool)) (count : Nat) :
    description.runConfig 1
        (config scanTail (scanTape left []) Tape.blank
          (markerCurrentTape count)) =
      config restoreOutput (scanTape left []) Tape.blank
        (markerCurrentTape count) := by
  cases left <;> cases count <;>
    allocator_step [scanTape, markerCurrentTape, List.replicate_succ]

theorem scanTail_to_boundary
    (processed tail : Word Bool) (count : Nat) :
    description.runConfig (tail.length + 1)
        (config scanTail (scanTape (processed.reverse.map some) tail)
          Tape.blank (markerCurrentTape count)) =
      config restoreOutput
        (rightEdgeRewindSourceTape (List.append processed tail) [])
        Tape.blank (markerCurrentTape count) := by
  rw [Description.runConfig_add]
  rw [scanTail_run]
  rw [scanTail_finish]
  simp [scanTape, rightEdgeRewindSourceTape, List.reverse_append,
    List.map_append, List.append_assoc, tapeAtCells]

def restoreMarkerTape (remaining erased : Nat) : Tape Bool :=
  tapeAtCells
    (List.replicate remaining (some true : Option Bool))
    (some true :: List.replicate erased (none : Option Bool))

theorem restoreMarkerTape_zero (count : Nat) :
    restoreMarkerTape count 0 = markerCurrentTape count := by
  simp [restoreMarkerTape, markerCurrentTape]

theorem restore_marker_step_succ
    (word : Word Bool) (remaining erased : Nat) :
    description.runConfig 1
        (config restoreOutput (rightEdgeRewindSourceTape word []) Tape.blank
          (restoreMarkerTape (remaining + 1) erased)) =
      config restoreOutput (rightEdgeRewindSourceTape word []) Tape.blank
        (restoreMarkerTape remaining (erased + 1)) := by
  cases word <;> cases remaining <;> cases erased <;>
    allocator_step [restoreMarkerTape, rightEdgeRewindSourceTape,
      List.replicate_succ, tapeAtCells]

theorem restore_marker_step_zero
    (word : Word Bool) (erased : Nat) :
    description.runConfig 1
        (config restoreOutput (rightEdgeRewindSourceTape word []) Tape.blank
          (restoreMarkerTape 0 erased)) =
      config restoreOutput (rightEdgeRewindSourceTape word []) Tape.blank
        (tapeAtCells []
          (List.replicate (erased + 2) (none : Option Bool))) := by
  cases word <;> cases erased <;>
    allocator_step [restoreMarkerTape, rightEdgeRewindSourceTape,
      List.replicate_succ, tapeAtCells]

theorem restore_markers_run
    (word : Word Bool) (remaining erased : Nat) :
    description.runConfig (remaining + 1)
        (config restoreOutput (rightEdgeRewindSourceTape word []) Tape.blank
          (restoreMarkerTape remaining erased)) =
      config restoreOutput (rightEdgeRewindSourceTape word []) Tape.blank
        (tapeAtCells []
          (List.replicate (remaining + erased + 2)
            (none : Option Bool))) := by
  induction remaining generalizing erased with
  | zero =>
      simpa using restore_marker_step_zero word erased
  | succ remaining ih =>
      rw [show remaining + 1 + 1 = 1 + (remaining + 1) by lia]
      rw [Description.runConfig_add]
      rw [restore_marker_step_succ]
      rw [ih (erased + 1)]
      congr 4
      lia

theorem restore_finish_step (word : Word Bool) (count : Nat) :
    description.runConfig 1
        (config restoreOutput (rightEdgeRewindSourceTape word []) Tape.blank
          (tapeAtCells []
            (List.replicate (count + 2) (none : Option Bool)))) =
      config rewindBoundary (rightEdgeRewindSourceTape word []) Tape.blank
        (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
          count []) := by
  cases word <;> cases count <;>
    allocator_step [rightEdgeRewindSourceTape,
      structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding,
      List.replicate_succ, tapeAtCells]

theorem restore_run (word : Word Bool) (count : Nat) :
    description.runConfig (count + 2)
        (config restoreOutput (rightEdgeRewindSourceTape word []) Tape.blank
          (markerCurrentTape count)) =
      config rewindBoundary (rightEdgeRewindSourceTape word []) Tape.blank
        (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
          count []) := by
  rw [show count + 2 = (count + 1) + 1 by lia]
  rw [Description.runConfig_add]
  rw [← restoreMarkerTape_zero]
  rw [restore_markers_run]
  rw [restore_finish_step]

def rewindTape
    (remaining : Word Bool) (current : Bool)
    (processed : Word Bool) : Tape Bool :=
  tapeAtCells (remaining.map some)
    (some current :: List.append (processed.map some) [none])

theorem rewind_boundary_step
    (current : Bool) (remaining : Word Bool) (count : Nat) :
    description.runConfig 1
        (config rewindBoundary
          (rightEdgeRewindSourceTape ((current :: remaining).reverse) [])
          Tape.blank
          (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
            count [])) =
      config rewindBits (rewindTape remaining current []) Tape.blank
        (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
          count []) := by
  cases current <;> cases remaining <;> cases count <;>
    allocator_step [rewindTape, rightEdgeRewindSourceTape,
      structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding,
      List.replicate_succ, List.map_append, tapeAtCells]

theorem rewind_step
    (remaining : Word Bool) (current : Bool) (processed : Word Bool)
    (count : Nat) :
    description.runConfig 1
        (config rewindBits (rewindTape remaining current processed) Tape.blank
          (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
            count [])) =
      match remaining with
      | [] =>
          config rewindBits
            (tapeAtCells []
              (none :: List.append ((current :: processed).map some)
                [none]))
            Tape.blank
            (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
              count [])
      | next :: tail =>
          config rewindBits (rewindTape tail next (current :: processed))
            Tape.blank
            (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
              count []) := by
  cases remaining with
  | nil =>
      cases current <;> cases processed <;> cases count <;>
        allocator_step [rewindTape,
          structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding,
          List.replicate_succ, List.append_assoc, tapeAtCells]
  | cons next tail =>
      cases current <;> cases next <;> cases tail <;> cases processed <;>
        cases count <;>
          allocator_step [rewindTape,
            structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding,
            List.replicate_succ, List.append_assoc, tapeAtCells]

theorem rewind_bits_run
    (remaining : Word Bool) (current : Bool) (processed : Word Bool)
    (count : Nat) :
    description.runConfig (remaining.length + 1)
        (config rewindBits (rewindTape remaining current processed) Tape.blank
          (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
            count [])) =
      config rewindBits
        (tapeAtCells []
          (none :: List.append
            ((List.append remaining.reverse (current :: processed)).map some)
            [none]))
        Tape.blank
        (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
          count []) := by
  induction remaining generalizing current processed with
  | nil =>
      simpa [rewindTape] using rewind_step [] current processed count
  | cons next tail ih =>
      rw [show (next :: tail).length + 1 = 1 + (tail.length + 1) by
        simp
        lia]
      rw [Description.runConfig_add]
      rw [rewind_step]
      rw [ih next (current :: processed)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem rewind_finish_step
    (current : Bool) (rest : Word Bool) (count : Nat) :
    description.runConfig 1
        (config rewindBits
          (tapeAtCells []
            (none :: List.append ((current :: rest).map some) [none]))
          Tape.blank
          (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
            count [])) =
      config halt (rightEdgeRewindTargetTape (current :: rest) []) Tape.blank
        (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
          count []) := by
  cases current <;> cases rest <;> cases count <;>
    allocator_step [rightEdgeRewindTargetTape,
      structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding,
      List.replicate_succ, tapeAtCells]

theorem rewind_from_nonempty
    (bit : Bool) (bits : Word Bool) (count : Nat) :
    description.runConfig ((bit :: bits).length + 2)
        (config rewindBoundary
          (rightEdgeRewindSourceTape (bit :: bits) []) Tape.blank
          (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
            count [])) =
      config halt (rightEdgeRewindTargetTape (bit :: bits) []) Tape.blank
        (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
          count []) := by
  cases hrev : (bit :: bits).reverse with
  | nil =>
      have : (bit :: bits).reverse ≠ [] := by simp
      contradiction
  | cons current remaining =>
      have hword : (current :: remaining).reverse = bit :: bits := by
        rw [← hrev]
        simp
      have hlen : remaining.length = bits.length := by
        have := congrArg List.length hrev
        simp at this
        lia
      rw [show (bit :: bits).length + 2 =
          1 + ((remaining.length + 1) + 1) by simp [hlen]; lia]
      rw [Description.runConfig_add]
      have hsource :
          rightEdgeRewindSourceTape (bit :: bits) [] =
            rightEdgeRewindSourceTape ((current :: remaining).reverse) [] := by
        rw [hword]
      rw [hsource]
      rw [rewind_boundary_step]
      rw [Description.runConfig_add]
      rw [rewind_bits_run remaining current [] count]
      rw [show List.append remaining.reverse [current] =
          (current :: remaining).reverse by simp]
      rw [hword]
      rw [rewind_finish_step]

def rawWord (n : Nat) (tail : Word Bool) : Word Bool :=
  List.append [false, false, false, false]
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits n)
      tail)

def processedPrefix (n : Nat) : Word Bool :=
  List.append [false, false, false, false]
    (List.append (tickStream n) [false, false, true, true])

theorem processedPrefix_append_eq_rawWord
    (n : Nat) (tail : Word Bool) :
    List.append (processedPrefix n) tail = rawWord n tail := by
  rw [processedPrefix, rawWord, stageNatBits_eq_tickStream_append_done]
  simp [List.append_assoc]

theorem parse_after_header_run (n : Nat) (tail : Word Bool) :
    description.runConfig (4 * (n + 1))
        (config field1
          (scanTape [some false, some false, some false, some false]
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits n)
              tail))
          Tape.blank Tape.blank) =
      config scanTail
        (scanTape ((processedPrefix n).reverse.map some) tail)
        Tape.blank (markerCurrentTape n) := by
  simpa [processedPrefix, markerTape, tapeAtCells, Tape.blank,
    List.append_assoc] using
    parse_run [false, false, false, false] tail n 0

theorem header_to_parser_run (n : Nat) (tail : Word Bool) :
    description.runConfig 4
        (config header1 (Tape.input (rawWord n tail))
          Tape.blank Tape.blank) =
      config field1
        (scanTape [some false, some false, some false, some false]
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits n)
            tail))
        Tape.blank Tape.blank := by
  simpa [rawWord, List.append_assoc] using
    header_run
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits n)
      tail

theorem parsed_to_boundary_run (n : Nat) (tail : Word Bool) :
    description.runConfig (tail.length + 1)
        (config scanTail
          (scanTape ((processedPrefix n).reverse.map some) tail)
          Tape.blank (markerCurrentTape n)) =
      config restoreOutput (rightEdgeRewindSourceTape (rawWord n tail) [])
        Tape.blank (markerCurrentTape n) := by
  rw [scanTail_to_boundary]
  rw [processedPrefix_append_eq_rawWord]

theorem rewind_rawWord_run (n : Nat) (tail : Word Bool) :
    description.runConfig ((rawWord n tail).length + 2)
        (config rewindBoundary
          (rightEdgeRewindSourceTape (rawWord n tail) []) Tape.blank
          (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
            n [])) =
      config halt (rightEdgeRewindTargetTape (rawWord n tail) []) Tape.blank
        (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
          n []) := by
  simpa [rawWord, List.append_assoc] using
    rewind_from_nonempty false
      (List.append [false, false, false]
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            n)
          tail))
      n

def fullFuel (n : Nat) (tail : Word Bool) : Nat :=
  4 +
    (4 * (n + 1) +
      ((tail.length + 1) +
        ((n + 2) + ((rawWord n tail).length + 2))))

theorem full_run (n : Nat) (tail : Word Bool) :
    description.runConfig (fullFuel n tail)
        (config header1 (Tape.input (rawWord n tail))
          Tape.blank Tape.blank) =
      config halt (rightEdgeRewindTargetTape (rawWord n tail) []) Tape.blank
        (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
          n []) := by
  rw [fullFuel]
  rw [Description.runConfig_add]
  rw [header_to_parser_run]
  rw [Description.runConfig_add]
  rw [parse_after_header_run]
  rw [Description.runConfig_add]
  rw [parsed_to_boundary_run]
  rw [Description.runConfig_add]
  rw [restore_run]
  rw [rewind_rawWord_run]

def loweredDescription : MachineDescription :=
  lowerStructured3Description description

theorem loweredDescription_subroutineReady :
    loweredDescription.SubroutineReady := by
  simpa [loweredDescription] using
    lowerStructured3Description_subroutineReady
      description_subroutineReady.left description_supports

theorem loweredDescription_haltsFromTapeEquiv
    (n : Nat) (tail : Word Bool) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (Tape.input (rawWord n tail)) Tape.blank Tape.blank)
      (encodedGuardedStructured3Tapes
        (rightEdgeRewindTargetTape (rawWord n tail) []) Tape.blank
        (structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding
          n [])) := by
  simpa [loweredDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      description_subroutineReady.left description_subroutineReady.right
      description_supports
      (c := config header1 (Tape.input (rawWord n tail)) Tape.blank Tape.blank)
      (tapes :=
        [ rightEdgeRewindTargetTape (rawWord n tail) []
        , Tape.blank
        , structuredBoolWordRawBitsDecoderInitialOutputTapeWithPadding n [] ])
      rfl rfl ⟨fullFuel n tail, full_run n tail⟩

end OutputLengthAllocator
end CountWindowInputMat
end ThreeTape
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
