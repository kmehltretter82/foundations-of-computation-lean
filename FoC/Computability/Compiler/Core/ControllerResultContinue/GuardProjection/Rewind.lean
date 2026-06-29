import FoC.Computability.Compiler.Core.ControllerResultContinue.GuardProjection.Scanner

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace ControllerResultContinueConstruction
def ResultNoneGuardRewindDescription : MachineDescription where
  stateCount := 5
  start := 0
  halt := 4
  transitions :=
    [ transition 0 none none Direction.left 1
    , transition 1 none none Direction.left 2
    , transition 2 (some false) (some false)
        Direction.left 2
    , transition 2 (some true) (some true)
        Direction.left 2
    , transition 2 none none Direction.right 3
    , transition 3 none none Direction.right 4
    , transition 3 (some false) (some false)
        Direction.right 4
    , transition 3 (some true) (some true)
        Direction.right 4
    ]

theorem resultNoneGuardRewindDescription_wellFormed :
    ResultNoneGuardRewindDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := ResultNoneGuardRewindDescription.transitions)
      (stateCount := ResultNoneGuardRewindDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_all
      (l := ResultNoneGuardRewindDescription.transitions)
      (by decide)

theorem resultNoneGuardRewindDescription_haltTransitionFree :
    ResultNoneGuardRewindDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := ResultNoneGuardRewindDescription.transitions)
    (state := ResultNoneGuardRewindDescription.halt)
    (by decide)

theorem resultNoneGuardRewindDescription_subroutineReady :
    ResultNoneGuardRewindDescription.SubroutineReady :=
  ⟨resultNoneGuardRewindDescription_wellFormed,
    resultNoneGuardRewindDescription_haltTransitionFree⟩

def resultNoneGuardRewindLeftScanTape
    (leftRev : Word Bool) (right : List (Option Bool)) : Tape Bool :=
  match leftRev with
  | [] =>
      { left := []
        head := none
        right := right }
  | b :: rest =>
      { left := rest.map some
        head := some b
        right := right }

def resultNoneGuardRewindBoundaryTape
    (bits : Word Bool) : Tape Bool :=
  { left := []
    head := none
    right := (bits.map some) ++ [none, none] }

def resultNoneGuardRewindFinalTape
    (bits : Word Bool) : Tape Bool :=
  Tape.move Direction.right
    (Tape.move Direction.right
      (resultNoneGuardRewindBoundaryTape bits))

theorem resultNoneGuardRewindDescription_run_start
    (leftRev : Word Bool) :
    ResultNoneGuardRewindDescription.runConfig 2
        { state := ResultNoneGuardRewindDescription.start
          tape := resultNoneGuardScannedBlankTape leftRev } =
      { state := 2
        tape := resultNoneGuardRewindLeftScanTape
          leftRev [none, none] } := by
  cases leftRev with
  | nil =>
      rfl
  | cons b rest =>
      cases b <;> rfl

theorem resultNoneGuardRewindDescription_run_left_scan
    (leftRev : Word Bool) (right : List (Option Bool)) :
    ResultNoneGuardRewindDescription.runConfig leftRev.length
        { state := 2
          tape := resultNoneGuardRewindLeftScanTape leftRev right } =
      { state := 2
        tape :=
          { left := []
            head := none
            right := (leftRev.reverse.map some) ++ right } } := by
  induction leftRev generalizing right with
  | nil =>
      rfl
  | cons b rest ih =>
      rw [show (b :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [runConfig_add]
      cases b
      · have hstep :
            ResultNoneGuardRewindDescription.runConfig 1
                { state := 2
                  tape :=
                    resultNoneGuardRewindLeftScanTape
                      (false :: rest) right } =
              { state := 2
                tape :=
                  resultNoneGuardRewindLeftScanTape rest
                    (some false :: right) } := by
          cases rest with
          | nil =>
              rfl
          | cons c tail =>
              cases c <;> rfl
        rw [hstep]
        rw [ih]
        simp [List.append_assoc]
      · have hstep :
            ResultNoneGuardRewindDescription.runConfig 1
                { state := 2
                  tape :=
                    resultNoneGuardRewindLeftScanTape
                      (true :: rest) right } =
              { state := 2
                tape :=
                  resultNoneGuardRewindLeftScanTape rest
                    (some true :: right) } := by
          cases rest with
          | nil =>
              rfl
          | cons c tail =>
              cases c <;> rfl
        rw [hstep]
        rw [ih]
        simp [List.append_assoc]

theorem resultNoneGuardRewindDescription_run_finish
    (bits : Word Bool) :
    ResultNoneGuardRewindDescription.runConfig 2
        { state := 2
          tape := resultNoneGuardRewindBoundaryTape bits } =
      { state := ResultNoneGuardRewindDescription.halt
        tape := resultNoneGuardRewindFinalTape bits } := by
  cases bits with
  | nil =>
      rfl
  | cons b rest =>
      cases b <;> cases rest <;> rfl

theorem resultNoneGuardRewindDescription_run_scanned
    (bits : Word Bool) :
    ResultNoneGuardRewindDescription.runConfig
        (bits.length + 4)
        { state := ResultNoneGuardRewindDescription.start
          tape := resultNoneGuardScannedBlankTape bits.reverse } =
      { state := ResultNoneGuardRewindDescription.halt
        tape := resultNoneGuardRewindFinalTape bits } := by
  rw [show bits.length + 4 = 2 + (bits.length + 2) by omega]
  rw [runConfig_add]
  rw [resultNoneGuardRewindDescription_run_start]
  rw [show bits.length + 2 = bits.reverse.length + 2 by simp]
  rw [runConfig_add]
  rw [resultNoneGuardRewindDescription_run_left_scan]
  change
    ResultNoneGuardRewindDescription.runConfig 2
        { state := 2
          tape :=
            { left := []
              head := none
              right := (bits.reverse.reverse.map some) ++ [none, none] } } =
      { state := ResultNoneGuardRewindDescription.halt
        tape := resultNoneGuardRewindFinalTape bits }
  simp only [List.reverse_reverse]
  exact resultNoneGuardRewindDescription_run_finish bits

theorem resultNoneGuardRewind_dropTrailingNone_map_some
    (bits : Word Bool) :
    Tape.dropTrailingNone (bits.map some) = bits.map some := by
  induction bits with
  | nil =>
      rfl
  | cons b rest ih =>
      cases b <;>
        simp [Tape.dropTrailingNone, ih]

theorem resultNoneGuardRewind_dropTrailingNone_map_some_append_blanks
    (bits : Word Bool) :
    Tape.dropTrailingNone (bits.map some ++ [none, none]) =
      bits.map some := by
  induction bits with
  | nil =>
      rfl
  | cons b rest ih =>
      cases b <;>
        simp [Tape.dropTrailingNone, ih]

theorem resultNoneGuardRewindFinalTape_handoff_equiv
    (bits : Word Bool) :
    Tape.Equiv
      (resultNoneGuardRewindFinalTape bits)
      (Tape.move Direction.right (Tape.input bits)) := by
  cases bits with
  | nil =>
      simp [resultNoneGuardRewindFinalTape,
        resultNoneGuardRewindBoundaryTape, Tape.input, Tape.blank,
        Tape.move, Tape.moveRight, Tape.Equiv,
        Tape.dropTrailingNone]
  | cons b rest =>
      cases rest with
      | nil =>
          cases b <;>
            simp [resultNoneGuardRewindFinalTape,
              resultNoneGuardRewindBoundaryTape, Tape.input,
              Tape.move, Tape.moveRight, Tape.Equiv,
              Tape.dropTrailingNone]
      | cons c tail =>
          cases b <;> cases c <;>
            simp [resultNoneGuardRewindFinalTape,
              resultNoneGuardRewindBoundaryTape, Tape.input,
              Tape.move, Tape.moveRight, Tape.Equiv,
              Tape.dropTrailingNone,
              resultNoneGuardRewind_dropTrailingNone_map_some,
              resultNoneGuardRewind_dropTrailingNone_map_some_append_blanks]

def resultNoneGuardOffsetTransition
    (offset : Nat) (t : TransitionDescription) :
    TransitionDescription :=
  { source := offset + t.source
    read := t.read
    write := t.write
    move := t.move
    target := offset + t.target }

def resultNoneGuardRewindOffset : Nat :=
  ResultNoneGuardScannerDescription.stateCount

def resultNoneGuardScanRewindAcceptTransitions :
    List TransitionDescription :=
  [ transition
      (resultNoneGuardState ResultNoneGuardBoundary.other.toNat 0 0)
      none none Direction.right
      (resultNoneGuardRewindOffset + ResultNoneGuardRewindDescription.start)
  , transition
      (resultNoneGuardState ResultNoneGuardBoundary.tick.toNat 0 0)
      none none Direction.right
      (resultNoneGuardRewindOffset + ResultNoneGuardRewindDescription.start)
  , transition
      (resultNoneGuardState ResultNoneGuardBoundary.tickDone.toNat 0 0)
      none none Direction.right
      (resultNoneGuardRewindOffset + ResultNoneGuardRewindDescription.start)
  ]

def resultNoneGuardScanRewindTransitionChunks :
    List (List TransitionDescription) :=
  resultNoneGuardBitTransitionChunks ++
    [ resultNoneGuardScanRewindAcceptTransitions
    , ResultNoneGuardRewindDescription.transitions.map
        (resultNoneGuardOffsetTransition resultNoneGuardRewindOffset)
    ]

def ResultNoneGuardScanRewindDescription : MachineDescription where
  stateCount :=
    ResultNoneGuardScannerDescription.stateCount +
      ResultNoneGuardRewindDescription.stateCount
  start := ResultNoneGuardScannerDescription.start
  halt := resultNoneGuardRewindOffset + ResultNoneGuardRewindDescription.halt
  transitions := resultNoneGuardScanRewindTransitionChunks.flatten

theorem resultNoneGuardScanRewindDescription_wellFormed :
    ResultNoneGuardScanRewindDescription.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_chunk_all
      (chunks := resultNoneGuardScanRewindTransitionChunks)
      (stateCount := ResultNoneGuardScanRewindDescription.stateCount)
      (by decide)
  · exact transition_deterministic_of_chunk_all
      (chunks := resultNoneGuardScanRewindTransitionChunks)
      (by decide)

theorem resultNoneGuardScanRewindDescription_haltTransitionFree :
    ResultNoneGuardScanRewindDescription.HaltTransitionFree :=
  transition_notFrom_of_chunk_all
    (chunks := resultNoneGuardScanRewindTransitionChunks)
    (state := ResultNoneGuardScanRewindDescription.halt)
    (by decide)

theorem resultNoneGuardScanRewindDescription_subroutineReady :
    ResultNoneGuardScanRewindDescription.SubroutineReady :=
  ⟨resultNoneGuardScanRewindDescription_wellFormed,
    resultNoneGuardScanRewindDescription_haltTransitionFree⟩

theorem resultNoneGuardScanRewindDescription_state_ne_halt_of_later_ne_halt
    {c : Configuration} {n k : Nat}
    (hle : n ≤ k)
    (hlater :
      (ResultNoneGuardScanRewindDescription.runConfig k c).state ≠
        ResultNoneGuardScanRewindDescription.halt) :
    (ResultNoneGuardScanRewindDescription.runConfig n c).state ≠
      ResultNoneGuardScanRewindDescription.halt :=
  CommonGround.SeqComposition.runConfig_state_ne_halt_of_later_ne_halt
    resultNoneGuardScanRewindDescription_haltTransitionFree hle hlater

theorem resultNoneGuardScanRewindDescription_ne_halt_of_reaches_stepConfig_none
    {c stuck : Configuration} {k n : Nat}
    (hrun :
      ResultNoneGuardScanRewindDescription.runConfig k c = stuck)
    (hstep :
      ResultNoneGuardScanRewindDescription.stepConfig stuck = none)
    (hstuck :
      stuck.state ≠ ResultNoneGuardScanRewindDescription.halt) :
    (ResultNoneGuardScanRewindDescription.runConfig n c).state ≠
      ResultNoneGuardScanRewindDescription.halt :=
  CommonGround.SeqComposition.runConfig_state_ne_halt_of_reaches_stuck
    resultNoneGuardScanRewindDescription_haltTransitionFree hrun hstep hstuck

theorem resultNoneGuardScanRewindDescription_run_blank_of_accepts
    (boundary : ResultNoneGuardBoundary)
    (haccept : boundary.accepts)
    (leftRev : Word Bool) :
    ResultNoneGuardScanRewindDescription.runConfig 1
        { state := resultNoneGuardState boundary.toNat 0 0
          tape := appendRightScanTape leftRev [] } =
      { state :=
          resultNoneGuardRewindOffset +
            ResultNoneGuardRewindDescription.start
        tape := resultNoneGuardScannedBlankTape leftRev } := by
  cases boundary
  · rfl
  · rfl
  · rfl
  · cases haccept
  · cases haccept

theorem resultNoneGuardScanRewindDescription_reject_blank_stepConfig_none
    (boundary : ResultNoneGuardBoundary)
    (hreject : ¬ boundary.accepts)
    (leftRev : Word Bool) :
    ResultNoneGuardScanRewindDescription.stepConfig
        { state := resultNoneGuardState boundary.toNat 0 0
          tape := appendRightScanTape leftRev [] } =
      none := by
  cases boundary
  · exact (hreject trivial).elim
  · exact (hreject trivial).elim
  · exact (hreject trivial).elim
  · cases leftRev <;> rfl
  · cases leftRev <;> rfl

theorem resultNoneGuardScanRewindDescription_reject_blank_state_ne_halt
    (boundary : ResultNoneGuardBoundary)
    (hreject : ¬ boundary.accepts) :
    resultNoneGuardState boundary.toNat 0 0 ≠
      ResultNoneGuardScanRewindDescription.halt := by
  cases boundary
  · exact (hreject trivial).elim
  · exact (hreject trivial).elim
  · exact (hreject trivial).elim
  · decide
  · decide

theorem resultNoneGuardScanRewindDescription_run_bits
    (boundary : ResultNoneGuardBoundary)
    (bit0 bit1 bit2 bit3 : Bool)
    (leftRev suffix : Word Bool) :
    ResultNoneGuardScanRewindDescription.runConfig 4
        { state := resultNoneGuardState boundary.toNat 0 0
          tape :=
            appendRightScanTape leftRev
              (List.append [bit0, bit1, bit2, bit3] suffix) } =
      { state :=
          resultNoneGuardState
            (resultNoneGuardBoundaryUpdateCode boundary.toNat
              (resultNoneGuardCodeOfBits bit0 bit1 bit2 bit3)) 0 0
        tape := appendRightScanTape
          (bit3 :: bit2 :: bit1 :: bit0 :: leftRev) suffix } := by
  cases boundary <;> cases bit0 <;> cases bit1 <;> cases bit2 <;>
    cases bit3 <;> cases suffix <;> rfl

theorem resultNoneGuardScanRewindDescription_run_encoded_symbol
    (boundary : ResultNoneGuardBoundary)
    (symbol : MachineCodeSymbol)
    (leftRev suffix : Word Bool) :
    ResultNoneGuardScanRewindDescription.runConfig 4
        { state := resultNoneGuardState boundary.toNat 0 0
          tape :=
            appendRightScanTape leftRev
              (List.append
                (encodeCodeSymbolAsInput symbol)
                suffix) } =
      { state :=
          resultNoneGuardState
            (resultNoneGuardBoundaryUpdateCode boundary.toNat
              (resultNoneGuardSymbolCode symbol)) 0 0
        tape :=
          appendRightScanTape
            (List.append
              (encodeCodeSymbolAsInput symbol).reverse
              leftRev)
            suffix } := by
  cases symbol
  · simpa [encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScanRewindDescription_run_bits boundary
        false false false false leftRev suffix)
  · simpa [encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScanRewindDescription_run_bits boundary
        false false false true leftRev suffix)
  · simpa [encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScanRewindDescription_run_bits boundary
        false false true false leftRev suffix)
  · simpa [encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScanRewindDescription_run_bits boundary
        false false true true leftRev suffix)
  · simpa [encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScanRewindDescription_run_bits boundary
        false true false false leftRev suffix)
  · simpa [encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScanRewindDescription_run_bits boundary
        false true false true leftRev suffix)
  · simpa [encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScanRewindDescription_run_bits boundary
        false true true false leftRev suffix)
  · simpa [encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScanRewindDescription_run_bits boundary
        false true true true leftRev suffix)
  · simpa [encodeCodeSymbolAsInput,
      resultNoneGuardCodeOfBits, resultNoneGuardSymbolCode] using
      (resultNoneGuardScanRewindDescription_run_bits boundary
        true false false false leftRev suffix)

theorem resultNoneGuardScanRewindDescription_run_symbol
    (boundary : ResultNoneGuardBoundary)
    (symbol : MachineCodeSymbol)
    (leftRev suffix : Word Bool) :
    ResultNoneGuardScanRewindDescription.runConfig 4
        { state := resultNoneGuardState boundary.toNat 0 0
          tape :=
            appendRightScanTape leftRev
              (List.append
                (encodeCodeSymbolAsInput symbol)
                suffix) } =
      { state :=
          resultNoneGuardState (boundary.update symbol).toNat 0 0
        tape :=
          appendRightScanTape
            (List.append
              (encodeCodeSymbolAsInput symbol).reverse
              leftRev)
            suffix } := by
  rw [resultNoneGuardScanRewindDescription_run_encoded_symbol]
  rw [resultNoneGuardBoundaryUpdateCode_symbol]

theorem resultNoneGuardScanRewindDescription_run_code_from
    (boundary : ResultNoneGuardBoundary)
    (code : Word MachineCodeSymbol)
    (leftRev suffix : Word Bool) :
    ResultNoneGuardScanRewindDescription.runConfig
        (4 * code.length)
        { state := resultNoneGuardState boundary.toNat 0 0
          tape :=
            appendRightScanTape leftRev
              (List.append
                (encodeCodeWordAsInput code) suffix) } =
      { state :=
          resultNoneGuardState
            (resultNoneGuardScanBoundaryFrom boundary code).toNat 0 0
        tape :=
          appendRightScanTape
            (List.append
              (encodeCodeWordAsInput code).reverse
              leftRev)
            suffix } := by
  induction code generalizing boundary leftRev with
  | nil =>
      simp [encodeCodeWordAsInput,
        resultNoneGuardScanBoundaryFrom,
        runConfig]
  | cons symbol rest ih =>
      rw [show 4 * (symbol :: rest).length = 4 + 4 * rest.length by
        simp
        omega]
      rw [runConfig_add]
      simp only [encodeCodeWordAsInput]
      have happ :
          List.append
              (List.append
                (encodeCodeSymbolAsInput symbol)
                (encodeCodeWordAsInput rest))
              suffix =
            List.append
              (encodeCodeSymbolAsInput symbol)
              (List.append
                (encodeCodeWordAsInput rest)
                suffix) :=
        List.append_assoc
          (encodeCodeSymbolAsInput symbol)
          (encodeCodeWordAsInput rest) suffix
      rw [happ]
      change
        ResultNoneGuardScanRewindDescription.runConfig
            (4 * rest.length)
            (ResultNoneGuardScanRewindDescription.runConfig 4
              { state := resultNoneGuardState boundary.toNat 0 0
                tape :=
                  appendRightScanTape leftRev
                    (List.append
                      (encodeCodeSymbolAsInput symbol)
                      (List.append
                        (encodeCodeWordAsInput rest)
                        suffix)) }) =
          { state :=
              resultNoneGuardState
                (resultNoneGuardScanBoundaryFrom boundary
                  (symbol :: rest)).toNat 0 0
            tape :=
              appendRightScanTape
                (List.append
                  (List.append
                    (encodeCodeSymbolAsInput symbol)
                    (encodeCodeWordAsInput rest)).reverse
                  leftRev)
                suffix }
      rw [resultNoneGuardScanRewindDescription_run_symbol]
      rw [ih]
      simp [resultNoneGuardScanBoundaryFrom, List.reverse_append,
        List.append_assoc]

theorem resultNoneGuardScanRewindDescription_not_haltsWithTape_code_of_not_accepts
    (code : Word MachineCodeSymbol)
    (hreject : ¬ (resultNoneGuardScanBoundary code).accepts)
    (T : Tape Bool) :
    ¬ ResultNoneGuardScanRewindDescription.HaltsWithTape
        (encodeCodeWordAsInput code) T := by
  intro hhalt
  rcases hhalt with ⟨n, hn⟩
  let bits := encodeCodeWordAsInput code
  let stuck : Configuration :=
    { state :=
        resultNoneGuardState (resultNoneGuardScanBoundary code).toNat 0 0
      tape := appendRightScanTape bits.reverse [] }
  have hinitial :
      ResultNoneGuardScanRewindDescription.initial bits =
        { state :=
            resultNoneGuardState ResultNoneGuardBoundary.other.toNat 0 0
          tape := appendRightScanTape []
            (List.append bits []) } := by
    simp [bits, ResultNoneGuardScanRewindDescription,
      ResultNoneGuardScannerDescription, initial,
      appendRightScanTape_nil_eq_input]
  have hrun :
      ResultNoneGuardScanRewindDescription.runConfig
          (4 * code.length)
          (ResultNoneGuardScanRewindDescription.initial bits) =
        stuck := by
    rw [hinitial]
    simpa [stuck, bits, resultNoneGuardScanBoundary] using
      resultNoneGuardScanRewindDescription_run_code_from
        ResultNoneGuardBoundary.other code [] []
  have hstep :
      ResultNoneGuardScanRewindDescription.stepConfig stuck = none := by
    simpa [stuck, bits] using
      resultNoneGuardScanRewindDescription_reject_blank_stepConfig_none
        (resultNoneGuardScanBoundary code) hreject bits.reverse
  have hstuck :
      stuck.state ≠ ResultNoneGuardScanRewindDescription.halt := by
    simpa [stuck] using
      resultNoneGuardScanRewindDescription_reject_blank_state_ne_halt
        (resultNoneGuardScanBoundary code) hreject
  have hne :
      (ResultNoneGuardScanRewindDescription.runConfig n
          (ResultNoneGuardScanRewindDescription.initial bits)).state ≠
        ResultNoneGuardScanRewindDescription.halt :=
    resultNoneGuardScanRewindDescription_ne_halt_of_reaches_stepConfig_none
      (c := ResultNoneGuardScanRewindDescription.initial bits)
      (stuck := stuck)
      (k := 4 * code.length)
      (n := n) hrun hstep hstuck
  exact hne hn.left

theorem resultNoneGuardScanRewindDescription_accepts_of_haltsWithTape_code
    {code : Word MachineCodeSymbol} {T : Tape Bool}
    (hhalt :
      ResultNoneGuardScanRewindDescription.HaltsWithTape
        (encodeCodeWordAsInput code) T) :
    (resultNoneGuardScanBoundary code).accepts := by
  by_cases haccept : (resultNoneGuardScanBoundary code).accepts
  · exact haccept
  · exact False.elim
      ((resultNoneGuardScanRewindDescription_not_haltsWithTape_code_of_not_accepts
        code haccept T) hhalt)

theorem resultNoneGuardScanRewindDescription_run_rewind_start
    (leftRev : Word Bool) :
    ResultNoneGuardScanRewindDescription.runConfig 2
        { state :=
            resultNoneGuardRewindOffset +
              ResultNoneGuardRewindDescription.start
          tape := resultNoneGuardScannedBlankTape leftRev } =
      { state := resultNoneGuardRewindOffset + 2
        tape := resultNoneGuardRewindLeftScanTape
          leftRev [none, none] } := by
  cases leftRev with
  | nil =>
      rfl
  | cons b rest =>
      cases b <;> rfl

theorem resultNoneGuardScanRewindDescription_run_rewind_left_scan
    (leftRev : Word Bool) (right : List (Option Bool)) :
    ResultNoneGuardScanRewindDescription.runConfig leftRev.length
        { state := resultNoneGuardRewindOffset + 2
          tape := resultNoneGuardRewindLeftScanTape leftRev right } =
      { state := resultNoneGuardRewindOffset + 2
        tape :=
          { left := []
            head := none
            right := (leftRev.reverse.map some) ++ right } } := by
  induction leftRev generalizing right with
  | nil =>
      rfl
  | cons b rest ih =>
      rw [show (b :: rest).length = 1 + rest.length by
        simp
        omega]
      rw [runConfig_add]
      cases b
      · have hstep :
            ResultNoneGuardScanRewindDescription.runConfig 1
                { state := resultNoneGuardRewindOffset + 2
                  tape :=
                    resultNoneGuardRewindLeftScanTape
                      (false :: rest) right } =
              { state := resultNoneGuardRewindOffset + 2
                tape :=
                  resultNoneGuardRewindLeftScanTape rest
                    (some false :: right) } := by
          cases rest with
          | nil =>
              rfl
          | cons c tail =>
              cases c <;> rfl
        rw [hstep]
        rw [ih]
        simp [List.append_assoc]
      · have hstep :
            ResultNoneGuardScanRewindDescription.runConfig 1
                { state := resultNoneGuardRewindOffset + 2
                  tape :=
                    resultNoneGuardRewindLeftScanTape
                      (true :: rest) right } =
              { state := resultNoneGuardRewindOffset + 2
                tape :=
                  resultNoneGuardRewindLeftScanTape rest
                    (some true :: right) } := by
          cases rest with
          | nil =>
              rfl
          | cons c tail =>
              cases c <;> rfl
        rw [hstep]
        rw [ih]
        simp [List.append_assoc]

theorem resultNoneGuardScanRewindDescription_run_rewind_finish
    (bits : Word Bool) :
    ResultNoneGuardScanRewindDescription.runConfig 2
        { state := resultNoneGuardRewindOffset + 2
          tape := resultNoneGuardRewindBoundaryTape bits } =
      { state := ResultNoneGuardScanRewindDescription.halt
        tape := resultNoneGuardRewindFinalTape bits } := by
  cases bits with
  | nil =>
      rfl
  | cons b rest =>
      cases b <;> cases rest <;> rfl

theorem resultNoneGuardScanRewindDescription_run_rewind_scanned
    (bits : Word Bool) :
    ResultNoneGuardScanRewindDescription.runConfig
        (bits.length + 4)
        { state :=
            resultNoneGuardRewindOffset +
              ResultNoneGuardRewindDescription.start
          tape := resultNoneGuardScannedBlankTape bits.reverse } =
      { state := ResultNoneGuardScanRewindDescription.halt
        tape := resultNoneGuardRewindFinalTape bits } := by
  rw [show bits.length + 4 = 2 + (bits.length + 2) by omega]
  rw [runConfig_add]
  rw [resultNoneGuardScanRewindDescription_run_rewind_start]
  rw [show bits.length + 2 = bits.reverse.length + 2 by simp]
  rw [runConfig_add]
  rw [resultNoneGuardScanRewindDescription_run_rewind_left_scan]
  change
    ResultNoneGuardScanRewindDescription.runConfig 2
        { state := resultNoneGuardRewindOffset + 2
          tape :=
            { left := []
              head := none
              right := (bits.reverse.reverse.map some) ++ [none, none] } } =
      { state := ResultNoneGuardScanRewindDescription.halt
        tape := resultNoneGuardRewindFinalTape bits }
  simp only [List.reverse_reverse]
  exact resultNoneGuardScanRewindDescription_run_rewind_finish bits

theorem resultNoneGuardScanRewindDescription_run_code_halt_of_accepts
    (code : Word MachineCodeSymbol)
    (haccept : (resultNoneGuardScanBoundary code).accepts) :
    ResultNoneGuardScanRewindDescription.runConfig
        (4 * code.length + 1 +
          (encodeCodeWordAsInput code).length + 4)
        (ResultNoneGuardScanRewindDescription.initial
          (encodeCodeWordAsInput code)) =
      { state := ResultNoneGuardScanRewindDescription.halt
        tape :=
          resultNoneGuardRewindFinalTape
            (encodeCodeWordAsInput code) } := by
  rw [show
      4 * code.length + 1 +
          (encodeCodeWordAsInput code).length + 4 =
        4 * code.length +
          (1 + ((encodeCodeWordAsInput code).length + 4)) by
    omega]
  rw [runConfig_add]
  have hinitial :
      ResultNoneGuardScanRewindDescription.initial
          (encodeCodeWordAsInput code) =
        { state :=
            resultNoneGuardState ResultNoneGuardBoundary.other.toNat 0 0
          tape :=
            appendRightScanTape []
              (List.append
                (encodeCodeWordAsInput code) []) } := by
    simp [ResultNoneGuardScanRewindDescription,
      ResultNoneGuardScannerDescription,
      initial,
      appendRightScanTape_nil_eq_input]
  rw [hinitial]
  rw [resultNoneGuardScanRewindDescription_run_code_from]
  rw [show
      1 + ((encodeCodeWordAsInput code).length + 4) =
        1 + ((encodeCodeWordAsInput code).length + 4) by
    rfl]
  rw [runConfig_add]
  change
    ResultNoneGuardScanRewindDescription.runConfig
        ((encodeCodeWordAsInput code).length + 4)
        (ResultNoneGuardScanRewindDescription.runConfig 1
          { state :=
              resultNoneGuardState
                (resultNoneGuardScanBoundaryFrom
                  ResultNoneGuardBoundary.other code).toNat 0 0
            tape :=
              appendRightScanTape
                ((encodeCodeWordAsInput code).reverse.append [])
                [] }) =
      { state := ResultNoneGuardScanRewindDescription.halt
        tape :=
          resultNoneGuardRewindFinalTape
            (encodeCodeWordAsInput code) }
  rw [resultNoneGuardScanRewindDescription_run_blank_of_accepts]
  · simpa using
      resultNoneGuardScanRewindDescription_run_rewind_scanned
        (encodeCodeWordAsInput code)
  · simpa [resultNoneGuardScanBoundary] using haccept

theorem resultNoneGuardScanRewindDescription_haltsWithTape_code_of_accepts
    (code : Word MachineCodeSymbol)
    (haccept : (resultNoneGuardScanBoundary code).accepts) :
    ResultNoneGuardScanRewindDescription.HaltsWithTape
      (encodeCodeWordAsInput code)
      (resultNoneGuardRewindFinalTape
        (encodeCodeWordAsInput code)) := by
  refine
    ⟨4 * code.length + 1 +
        (encodeCodeWordAsInput code).length + 4, ?_⟩
  change
    (ResultNoneGuardScanRewindDescription.runConfig
          (4 * code.length + 1 +
            (encodeCodeWordAsInput code).length + 4)
          (ResultNoneGuardScanRewindDescription.initial
            (encodeCodeWordAsInput code))).state =
        ResultNoneGuardScanRewindDescription.halt ∧
      (ResultNoneGuardScanRewindDescription.runConfig
          (4 * code.length + 1 +
            (encodeCodeWordAsInput code).length + 4)
          (ResultNoneGuardScanRewindDescription.initial
            (encodeCodeWordAsInput code))).tape =
        resultNoneGuardRewindFinalTape
          (encodeCodeWordAsInput code)
  rw [resultNoneGuardScanRewindDescription_run_code_halt_of_accepts
    code haccept]
  exact ⟨rfl, rfl⟩

theorem resultNoneGuard_moveLeft_moveRight_input_equiv
    (bits : Word Bool) :
    Tape.Equiv
      (Tape.move Direction.left
        (Tape.move Direction.right (Tape.input bits)))
      (Tape.input bits) := by
  cases bits with
  | nil =>
      simp [Tape.input, Tape.blank, Tape.move, Tape.moveLeft,
        Tape.moveRight, Tape.Equiv, Tape.dropTrailingNone]
  | cons b rest =>
      cases rest with
      | nil =>
          cases b <;>
            simp [Tape.input, Tape.move, Tape.moveLeft,
              Tape.moveRight, Tape.Equiv, Tape.dropTrailingNone]
      | cons c tail =>
          cases b <;> cases c <;>
            simp [Tape.input, Tape.move, Tape.moveLeft,
              Tape.moveRight, Tape.Equiv, Tape.dropTrailingNone,
              resultNoneGuardRewind_dropTrailingNone_map_some]

theorem resultNoneGuardRewindFinalTape_moveLeft_input_equiv
    (bits : Word Bool) :
    Tape.Equiv
      (Tape.move Direction.left
        (resultNoneGuardRewindFinalTape bits))
      (Tape.input bits) := by
  exact
    Tape.Equiv.trans
      (Tape.Equiv.move
        (resultNoneGuardRewindFinalTape_handoff_equiv bits)
        Direction.left)
      (resultNoneGuard_moveLeft_moveRight_input_equiv bits)

theorem resultNoneGuardScanRewindDescription_handoff_equiv_of_haltsWithTape_code
    {code : Word MachineCodeSymbol} {T : Tape Bool}
    (hhalt :
      ResultNoneGuardScanRewindDescription.HaltsWithTape
        (encodeCodeWordAsInput code) T) :
    Tape.Equiv
      (Tape.move Direction.left T)
      (Tape.input (encodeCodeWordAsInput code)) := by
  have haccept :
      (resultNoneGuardScanBoundary code).accepts :=
    resultNoneGuardScanRewindDescription_accepts_of_haltsWithTape_code
      hhalt
  have hknown :
      ResultNoneGuardScanRewindDescription.HaltsWithTape
        (encodeCodeWordAsInput code)
        (resultNoneGuardRewindFinalTape
          (encodeCodeWordAsInput code)) :=
    resultNoneGuardScanRewindDescription_haltsWithTape_code_of_accepts
      code haccept
  have hT :
      T =
        resultNoneGuardRewindFinalTape
          (encodeCodeWordAsInput code) :=
    MachineDescription.haltsWithTape_functional_of_haltTransitionFree
      resultNoneGuardScanRewindDescription_haltTransitionFree
      hhalt hknown
  rw [hT]
  exact
    resultNoneGuardRewindFinalTape_moveLeft_input_equiv
      (encodeCodeWordAsInput code)

theorem resultNoneGuardScanRewindDescription_handoff_equiv_code_of_accepts
    (code : Word MachineCodeSymbol)
    (haccept : (resultNoneGuardScanBoundary code).accepts) :
    exists T : Tape Bool,
      ResultNoneGuardScanRewindDescription.HaltsWithTape
        (encodeCodeWordAsInput code) T ∧
        Tape.Equiv
          (Tape.move Direction.left T)
          (Tape.input (encodeCodeWordAsInput code)) := by
  refine
    ⟨resultNoneGuardRewindFinalTape
        (encodeCodeWordAsInput code), ?_, ?_⟩
  · exact
      resultNoneGuardScanRewindDescription_haltsWithTape_code_of_accepts
        code haccept
  · exact
      resultNoneGuardRewindFinalTape_moveLeft_input_equiv
        (encodeCodeWordAsInput code)


end ControllerResultContinueConstruction

end Computability
end FoC
