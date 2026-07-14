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
namespace CanonicalBoolWordDecoderSetup

def start : Nat := 0
def scan : Nat := 1
def rewind : Nat := 2
def halt : Nat := 3

def rowsForSourceRead
    (source : Nat) (sourceRead : Option Bool)
    (action0 action1 action2 : TapeAction)
    (target : Nat) : List Transition :=
  allReads2
    (fun read1 read2 =>
      row source sourceRead read1 read2
        action0 action1 action2 target)

def rows : List Transition :=
  [ [row start (some false) none none keepR keepS keepR scan]
  , rowsForSourceRead scan (some false) keepR keepS keepS scan
  , rowsForSourceRead scan (some true) keepR keepS keepS scan
  , rowsForSourceRead scan none keepL keepS keepS rewind
  , rowsForSourceRead rewind (some false) keepL keepS keepS rewind
  , rowsForSourceRead rewind (some true) keepL keepS keepS rewind
  , rowsForSourceRead rewind none keepR keepS keepS halt ].flatten

def description : Description :=
  ThreeTape.description 4 start halt rows

syntax "setup_step " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| setup_step [$lemmas,*]) =>
      `(tactic|
        three_tape_step [
          description, rows, rowsForSourceRead, allReads2, allReadCells,
          List.find?, start, scan, rewind, halt, $lemmas,*])

theorem description_subroutineReady : description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool description (by decide)

theorem description_supports : SupportsReadWriteRows3 description :=
  Structured.MultiTapeLowering.supportedReadWriteRows3_of_supports_eq_true
    (by decide)

def scanTape (left : List (Option Bool))
    (bits : Word Bool) : Tape Bool :=
  tapeAtCells left (bits.map some)

theorem start_step (rest : Word Bool) :
    description.runConfig 1
        (config start (Tape.input (false :: rest)) Tape.blank Tape.blank) =
      config scan (scanTape [some false] rest)
        Tape.blank structuredBoolWordRawBitsDecoderInitialOutputTape := by
  cases rest <;>
    setup_step [scanTape, Tape.input,
      structuredBoolWordRawBitsDecoderInitialOutputTape]

theorem scan_step_bit
    (left : List (Option Bool)) (bit : Bool) (rest : Word Bool) :
    description.runConfig 1
        (config scan (scanTape left (bit :: rest)) Tape.blank
          structuredBoolWordRawBitsDecoderInitialOutputTape) =
      config scan (scanTape (some bit :: left) rest) Tape.blank
        structuredBoolWordRawBitsDecoderInitialOutputTape := by
  cases bit <;> cases rest <;>
    setup_step [scanTape,
      structuredBoolWordRawBitsDecoderInitialOutputTape]

theorem scan_run
    (left : List (Option Bool)) (bits : Word Bool) :
    description.runConfig bits.length
        (config scan (scanTape left bits) Tape.blank
          structuredBoolWordRawBitsDecoderInitialOutputTape) =
      config scan
        (scanTape (List.append (bits.reverse.map some) left) [])
        Tape.blank structuredBoolWordRawBitsDecoderInitialOutputTape := by
  induction bits generalizing left with
  | nil =>
      simp [Structured.Description.runConfig, scanTape]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by simp; lia]
      rw [Structured.Description.runConfig_add]
      rw [scan_step_bit]
      rw [ih]
      simp [scanTape, List.reverse_cons, List.map_append,
        List.append_assoc]

theorem scan_finish_step
    (left : List (Option Bool)) (cell : Option Bool) :
    description.runConfig 1
        (config scan (scanTape (cell :: left) []) Tape.blank
          structuredBoolWordRawBitsDecoderInitialOutputTape) =
      config rewind (tapeAtCells left [cell, none]) Tape.blank
        structuredBoolWordRawBitsDecoderInitialOutputTape := by
  cases cell with
  | none =>
      setup_step [scanTape,
        structuredBoolWordRawBitsDecoderInitialOutputTape]
  | some bit =>
      cases bit <;>
        setup_step [scanTape,
          structuredBoolWordRawBitsDecoderInitialOutputTape]

def rewindSourceTape
    (remaining : Word Bool) (current : Bool)
    (processed : Word Bool) : Tape Bool :=
  tapeAtCells (remaining.map some)
    (some current :: List.append (processed.map some) [none])

theorem rewind_step
    (remaining : Word Bool) (current : Bool)
    (processed : Word Bool) :
    description.runConfig 1
        (config rewind (rewindSourceTape remaining current processed)
          Tape.blank structuredBoolWordRawBitsDecoderInitialOutputTape) =
      match remaining with
      | [] =>
          config rewind
            (tapeAtCells []
              (none :: List.append ((current :: processed).map some)
                [none]))
            Tape.blank structuredBoolWordRawBitsDecoderInitialOutputTape
      | next :: tail =>
          config rewind
            (rewindSourceTape tail next (current :: processed))
            Tape.blank structuredBoolWordRawBitsDecoderInitialOutputTape := by
  cases remaining with
  | nil =>
      cases current <;>
        setup_step [rewindSourceTape,
          structuredBoolWordRawBitsDecoderInitialOutputTape,
          List.append_assoc]
  | cons next tail =>
      cases current <;> cases next <;> cases tail <;>
        setup_step [rewindSourceTape,
          structuredBoolWordRawBitsDecoderInitialOutputTape,
          List.append_assoc]

theorem rewind_run
    (remaining : Word Bool) (current : Bool)
    (processed : Word Bool) :
    description.runConfig (remaining.length + 1)
        (config rewind (rewindSourceTape remaining current processed)
          Tape.blank structuredBoolWordRawBitsDecoderInitialOutputTape) =
      config rewind
        (tapeAtCells []
          (none :: List.append
            ((List.append remaining.reverse (current :: processed)).map some)
            [none]))
        Tape.blank structuredBoolWordRawBitsDecoderInitialOutputTape := by
  induction remaining generalizing current processed with
  | nil =>
      simpa [rewindSourceTape] using rewind_step [] current processed
  | cons next tail ih =>
      rw [show (next :: tail).length + 1 = 1 + (tail.length + 1) by
        simp
        lia]
      rw [Structured.Description.runConfig_add]
      rw [rewind_step]
      rw [ih next (current :: processed)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem rewind_finish_step (bits : Word Bool) :
    description.runConfig 1
        (config rewind
          (tapeAtCells []
            (none :: List.append (bits.map some) [none]))
          Tape.blank structuredBoolWordRawBitsDecoderInitialOutputTape) =
      config halt (rightEdgeRewindTargetTape bits []) Tape.blank
        structuredBoolWordRawBitsDecoderInitialOutputTape := by
  cases bits <;>
    setup_step [rightEdgeRewindTargetTape,
      structuredBoolWordRawBitsDecoderInitialOutputTape]

theorem finish_from_scanned
    (current : Bool) (remaining : Word Bool) :
    description.runConfig ((current :: remaining).length + 2)
        (config scan
          (scanTape ((current :: remaining).map some) [])
          Tape.blank structuredBoolWordRawBitsDecoderInitialOutputTape) =
      config halt
        (rightEdgeRewindTargetTape (current :: remaining).reverse [])
        Tape.blank structuredBoolWordRawBitsDecoderInitialOutputTape := by
  rw [show (current :: remaining).length + 2 =
      1 + ((remaining.length + 1) + 1) by simp; lia]
  rw [Structured.Description.runConfig_add]
  change
    description.runConfig ((remaining.length + 1) + 1)
      (description.runConfig 1
        (config scan
          (scanTape (some current :: remaining.map some) [])
          Tape.blank structuredBoolWordRawBitsDecoderInitialOutputTape)) = _
  rw [scan_finish_step (remaining.map some) (some current)]
  rw [Structured.Description.runConfig_add]
  change
    description.runConfig 1
      (description.runConfig (remaining.length + 1)
        (config rewind (rewindSourceTape remaining current [])
          Tape.blank structuredBoolWordRawBitsDecoderInitialOutputTape)) = _
  rw [rewind_run remaining current []]
  have hbits :
      List.append remaining.reverse [current] =
        (current :: remaining).reverse := by
    simp
  rw [hbits]
  change
    description.runConfig 1
      (config rewind
        (tapeAtCells []
          (none :: List.append (((current :: remaining).reverse).map some)
            [none]))
        Tape.blank structuredBoolWordRawBitsDecoderInitialOutputTape) = _
  rw [rewind_finish_step]

theorem full_run (rest : Word Bool) :
    description.runConfig (2 * (false :: rest).length + 2)
        (config start (Tape.input (false :: rest)) Tape.blank Tape.blank) =
      config halt (rightEdgeRewindTargetTape (false :: rest) [])
        Tape.blank structuredBoolWordRawBitsDecoderInitialOutputTape := by
  rw [show 2 * (false :: rest).length + 2 =
      1 + (rest.length + ((false :: rest).length + 2)) by
    simp
    lia]
  rw [Structured.Description.runConfig_add]
  rw [start_step]
  rw [Structured.Description.runConfig_add]
  rw [scan_run]
  cases hrev : (false :: rest).reverse with
  | nil =>
      have : (false :: rest).reverse ≠ [] := by simp
      contradiction
  | cons current remaining =>
      have hleft :
          List.append (rest.reverse.map some) [some false] =
            (current :: remaining).map some := by
        rw [← hrev]
        simp [List.reverse_cons, List.map_append]
      have hword :
          (current :: remaining).reverse = false :: rest := by
        rw [← hrev]
        simp
      have hlen : remaining.length = rest.length := by
        have := congrArg List.length hrev
        simp at this
        lia
      rw [hleft]
      simpa [hword, hlen] using finish_from_scanned current remaining

def loweredDescription : MachineDescription :=
  lowerStructured3Description description

theorem loweredDescription_subroutineReady :
    loweredDescription.SubroutineReady := by
  simpa [loweredDescription] using
    lowerStructured3Description_subroutineReady
      description_subroutineReady.left description_supports

theorem loweredDescription_haltsFromTapeEquiv
    (rest : Word Bool) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (Tape.input (false :: rest)) Tape.blank Tape.blank)
      (encodedGuardedStructured3Tapes
        (rightEdgeRewindTargetTape (false :: rest) []) Tape.blank
        structuredBoolWordRawBitsDecoderInitialOutputTape) := by
  simpa [loweredDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      description_subroutineReady.left description_subroutineReady.right
      description_supports
      (c := config start (Tape.input (false :: rest)) Tape.blank Tape.blank)
      (tapes :=
        [ rightEdgeRewindTargetTape (false :: rest) []
        , Tape.blank
        , structuredBoolWordRawBitsDecoderInitialOutputTape ])
      rfl rfl ⟨2 * (false :: rest).length + 2, full_run rest⟩

def canonicalRawWord (bits suffix : Word Bool) : Word Bool :=
  List.append boolWordRawBitsDecoderHeaderBits
    (List.append
      (boolWordRawBitsDecoderEncodedFieldBits bits)
      (false :: suffix))

theorem decoderSource_singleBlank_equiv_input
    (bits suffix : Word Bool) :
    Tape.Equiv
      (boolWordRawBitsDecoderSourceTape bits suffix [none])
      (Tape.input (canonicalRawWord bits suffix)) := by
  simp [boolWordRawBitsDecoderSourceTape, canonicalRawWord,
    boolWordRawBitsDecoderHeaderBits,
    MachineDescription.encodeCodeSymbolAsInput,
    rightEdgeRewindTargetTape, tapeAtCells, Tape.input, Tape.Equiv,
    Tape.dropTrailingNone, List.map_append, List.append_assoc]
  simpa [List.replicate_succ, List.append_assoc] using
    FoC.Computability.dropTrailingNone_append_replicate_none
      (List.append
        ((boolWordRawBitsDecoderEncodedFieldBits bits).map some)
        (some false :: suffix.map some)) 2

theorem loweredDescription_haltsFrom_decoderInput
    (bits suffix : Word Bool) :
    loweredDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (Tape.input (canonicalRawWord bits suffix)) Tape.blank Tape.blank)
      (encodedGuardedStructured3Tapes
        (boolWordRawBitsDecoderSourceTape bits suffix []) Tape.blank
        structuredBoolWordRawBitsDecoderInitialOutputTape) := by
  simpa [canonicalRawWord, boolWordRawBitsDecoderHeaderBits,
    MachineDescription.encodeCodeSymbolAsInput,
    boolWordRawBitsDecoderSourceTape, rightEdgeRewindTargetTape,
    List.append_assoc] using
    loweredDescription_haltsFromTapeEquiv
      (false :: false :: false ::
        List.append (boolWordRawBitsDecoderEncodedFieldBits bits)
          (false :: suffix))

end CanonicalBoolWordDecoderSetup
end NestedLayoutMaterializerInternal
end ThreeTape
end MultiTapeLowering
end Structured
end FiniteTransducers
end CommonGround

end Computability
end FoC
