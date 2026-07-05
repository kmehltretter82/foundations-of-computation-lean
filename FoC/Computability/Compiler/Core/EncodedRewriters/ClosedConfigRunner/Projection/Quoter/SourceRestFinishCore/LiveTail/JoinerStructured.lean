import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.LiveTail.JoinerRuns
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.GapPayloadLocalCompactor
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.SentinelGapCompactor
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.ThreeTapeHelpers
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.ThreeTapeTactic
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.RawTailInsertion

set_option doc.verso true

/-!
# Structured live-tail joiner components

This module starts the three-logical-tape implementation path for the assembly
live-tail joiner.  The first definitions pin down the exact structured source
and target configurations before introducing row tables.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers

namespace EncodedRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

def structuredHeadMoveOfDirection : Direction -> Structured.HeadMove
  | Direction.left => Structured.HeadMove.left
  | Direction.right => Structured.HeadMove.right

def structuredActionOfTransition
    (t : TransitionDescription) : Structured.TapeAction :=
  Structured.TapeAction.writeMove t.write
    (structuredHeadMoveOfDirection t.move)

theorem structuredActionOfTransition_apply
    (t : TransitionDescription) (T : Tape Bool) :
    (structuredActionOfTransition t).apply T =
      Tape.move t.move (Tape.write t.write T) := by
  cases t with
  | mk source read write move target =>
      cases move <;> rfl

def structuredRowOfOneTapeTransition
    (t : TransitionDescription)
    (read1 read2 : Option Bool) : Structured.Transition :=
  Structured.MultiTapeLowering.ThreeTape.row
    t.source t.read read1 read2
    (structuredActionOfTransition t)
    Structured.MultiTapeLowering.ThreeTape.keepS
    Structured.MultiTapeLowering.ThreeTape.keepS
    t.target

def structuredRowsOfOneTapeTransition
    (t : TransitionDescription) : List Structured.Transition :=
  Structured.MultiTapeLowering.ThreeTape.allReads2
    (fun read1 read2 =>
      structuredRowOfOneTapeTransition t read1 read2)

def structuredLiftOneTapeRows :
    List TransitionDescription -> List Structured.Transition
  | [] => []
  | row :: rows =>
      structuredRowsOfOneTapeTransition row ++
        structuredLiftOneTapeRows rows

def structuredLiftOneTapeDescription
    (D : MachineDescription) : Structured.Description :=
  Structured.MultiTapeLowering.ThreeTape.description
    D.stateCount D.start D.halt
    (structuredLiftOneTapeRows D.transitions)

theorem structuredRowsOfOneTapeTransition_supportsReadWriteRow3
    (t : TransitionDescription) :
    forall row : Structured.Transition,
      row ∈ structuredRowsOfOneTapeTransition t ->
        Structured.MultiTapeLowering.supportsReadWriteRow3 row =
          true := by
  intro row hrow
  cases t with
  | mk source read write move target =>
      cases move <;>
        simp [structuredRowsOfOneTapeTransition,
          Structured.MultiTapeLowering.ThreeTape.allReads2] at hrow ⊢
      all_goals
        rcases hrow with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact
            Structured.MultiTapeLowering.ThreeTape.row_supportsReadWriteRow3
              _ _ _ _ _ _ _ _

theorem structuredRowsOfOneTapeTransition_find?_match
    (t : TransitionDescription)
    (state : Nat) (read0 read1 read2 : Option Bool)
    (hmatch : MachineDescription.Matches state read0 t = true) :
    List.find?
        (Structured.Description.Matches state [read0, read1, read2])
        (structuredRowsOfOneTapeTransition t) =
      some (structuredRowOfOneTapeTransition t read1 read2) := by
  cases t with
  | mk source read write move target =>
      cases move <;>
        cases read1 <;> (try cases ‹Bool›) <;>
          cases read2 <;> (try cases ‹Bool›) <;>
            simp [structuredRowsOfOneTapeTransition,
              structuredRowOfOneTapeTransition,
              structuredActionOfTransition, structuredHeadMoveOfDirection,
              Structured.MultiTapeLowering.ThreeTape.allReads2,
              Structured.MultiTapeLowering.ThreeTape.row,
              Structured.Description.Matches,
              MachineDescription.Matches] at hmatch ⊢ <;>
            exact hmatch

theorem structuredRowsOfOneTapeTransition_find?_noMatch
    (t : TransitionDescription)
    (state : Nat) (read0 read1 read2 : Option Bool)
    (hmatch : MachineDescription.Matches state read0 t = false) :
    List.find?
        (Structured.Description.Matches state [read0, read1, read2])
        (structuredRowsOfOneTapeTransition t) =
      none := by
  cases t with
  | mk source read write move target =>
      cases move <;>
        cases read1 <;> (try cases ‹Bool›) <;>
          cases read2 <;> (try cases ‹Bool›) <;>
            simp [structuredRowsOfOneTapeTransition,
              structuredRowOfOneTapeTransition,
              structuredActionOfTransition, structuredHeadMoveOfDirection,
              Structured.MultiTapeLowering.ThreeTape.allReads2,
              Structured.MultiTapeLowering.ThreeTape.row,
              Structured.Description.Matches,
              MachineDescription.Matches] at hmatch ⊢ <;>
            exact hmatch

theorem structuredLiftOneTapeRows_find?
    (rows : List TransitionDescription)
    (state : Nat) (read0 read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches state [read0, read1, read2])
        (structuredLiftOneTapeRows rows) =
      Option.map
        (fun t => structuredRowOfOneTapeTransition t read1 read2)
        (rows.find? (MachineDescription.Matches state read0)) := by
  induction rows with
  | nil =>
      rfl
  | cons t rest ih =>
      cases hmatch : MachineDescription.Matches state read0 t
      · simp [structuredLiftOneTapeRows, hmatch]
        rw [structuredRowsOfOneTapeTransition_find?_noMatch
          t state read0 read1 read2 hmatch]
        exact ih
      · simp [structuredLiftOneTapeRows, hmatch]
        rw [structuredRowsOfOneTapeTransition_find?_match
          t state read0 read1 read2 hmatch]
        exact Or.inl rfl

theorem structuredLiftOneTapeDescription_lookupTransition
    (D : MachineDescription)
    (state : Nat) (tape0 tape1 tape2 : Tape Bool) :
    (structuredLiftOneTapeDescription D).lookupTransition
        (Structured.MultiTapeLowering.ThreeTape.config
          state tape0 tape1 tape2) =
      Option.map
        (fun t =>
          structuredRowOfOneTapeTransition t
            (Tape.read tape1) (Tape.read tape2))
        (D.lookupTransition state (Tape.read tape0)) := by
  simp [Structured.Description.lookupTransition,
    MachineDescription.lookupTransition,
    structuredLiftOneTapeDescription,
    Structured.MultiTapeLowering.ThreeTape.description,
    Structured.MultiTapeLowering.ThreeTape.currentReads_config,
    structuredLiftOneTapeRows_find?]

theorem structuredLiftOneTapeDescription_stepConfig
    (D : MachineDescription)
    (state : Nat) (tape0 tape1 tape2 : Tape Bool) :
    (structuredLiftOneTapeDescription D).stepConfig
        (Structured.MultiTapeLowering.ThreeTape.config
          state tape0 tape1 tape2) =
      match D.stepConfig { state := state, tape := tape0 } with
      | none => none
      | some next =>
          some
            (Structured.MultiTapeLowering.ThreeTape.config
              next.state next.tape tape1 tape2) := by
  rw [Structured.Description.stepConfig,
    structuredLiftOneTapeDescription_lookupTransition]
  rw [MachineDescription.stepConfig]
  cases hlookup : D.lookupTransition state (Tape.read tape0) with
  | none =>
      rfl
  | some t =>
      cases t with
      | mk source read write move target =>
          cases move <;>
            rfl

theorem structuredLiftOneTapeDescription_runConfig
    (D : MachineDescription)
    (n state : Nat) (tape0 tape1 tape2 : Tape Bool) :
    (structuredLiftOneTapeDescription D).runConfig n
        (Structured.MultiTapeLowering.ThreeTape.config
          state tape0 tape1 tape2) =
      let next := D.runConfig n { state := state, tape := tape0 }
      Structured.MultiTapeLowering.ThreeTape.config
        next.state next.tape tape1 tape2 := by
  induction n generalizing state tape0 with
  | zero =>
      rfl
  | succ n ih =>
      rw [Structured.Description.runConfig]
      rw [structuredLiftOneTapeDescription_stepConfig]
      cases hstep : D.stepConfig { state := state, tape := tape0 } with
      | none =>
          simp [MachineDescription.runConfig, hstep]
      | some next =>
          rw [MachineDescription.runConfig]
          simp [hstep]
          exact ih next.state next.tape

theorem structuredLiftOneTapeDescription_runConfig_from_start
    (D : MachineDescription)
    (n : Nat) (tape0 tape1 tape2 : Tape Bool) :
    (structuredLiftOneTapeDescription D).runConfig n
        (Structured.MultiTapeLowering.ThreeTape.config
          D.start tape0 tape1 tape2) =
      let next := D.runConfig n { state := D.start, tape := tape0 }
      Structured.MultiTapeLowering.ThreeTape.config
        next.state next.tape tape1 tape2 := by
  exact structuredLiftOneTapeDescription_runConfig
    D n D.start tape0 tape1 tape2

theorem structuredLiftOneTapeDescription_runConfig_eq_halt_of_haltsFromTape
    (D : MachineDescription)
    {input output scratch work : Tape Bool}
    (h : D.HaltsFromTape input output) :
    exists n : Nat,
      (structuredLiftOneTapeDescription D).runConfig n
          (Structured.MultiTapeLowering.ThreeTape.config
            D.start input scratch work) =
        Structured.MultiTapeLowering.ThreeTape.config
          D.halt output scratch work := by
  rcases runConfig_eq_halt_of_haltsFromTape h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [structuredLiftOneTapeDescription_runConfig_from_start]
  rw [hn]

theorem structuredLiftOneTapeDescription_haltsWithTapes_of_haltsFromTape
    (D : MachineDescription)
    {input output scratch work : Tape Bool}
    (h : D.HaltsFromTape input output) :
    (structuredLiftOneTapeDescription D).HaltsWithTapes
      (Structured.MultiTapeLowering.ThreeTape.config
        D.start input scratch work)
      [output, scratch, work] := by
  rcases structuredLiftOneTapeDescription_runConfig_eq_halt_of_haltsFromTape
      D h with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [Structured.MultiTapeLowering.ThreeTape.config] using hn

theorem structuredLiftOneTapeRows_supportsReadWriteRow3
    (rows : List TransitionDescription) :
    forall row : Structured.Transition,
      row ∈ structuredLiftOneTapeRows rows ->
        Structured.MultiTapeLowering.supportsReadWriteRow3 row =
          true := by
  induction rows with
  | nil =>
      intro row hrow
      simp [structuredLiftOneTapeRows] at hrow
  | cons t rest ih =>
      intro row hrow
      simp [structuredLiftOneTapeRows] at hrow
      rcases hrow with hrow | hrow
      · exact structuredRowsOfOneTapeTransition_supportsReadWriteRow3
          t row hrow
      · exact ih row hrow

theorem structuredLiftOneTapeDescription_supportsReadWriteRows3
    (D : MachineDescription) :
    Structured.MultiTapeLowering.supportsReadWriteRows3
        (structuredLiftOneTapeDescription D) =
      true :=
  Structured.MultiTapeLowering.ThreeTape.description_supportsReadWriteRows3
    D.stateCount D.start D.halt
    (structuredLiftOneTapeRows D.transitions)
    (structuredLiftOneTapeRows_supportsReadWriteRow3 D.transitions)

theorem structuredLiftOneTapeDescription_supported
    (D : MachineDescription) :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      (structuredLiftOneTapeDescription D) :=
  Structured.MultiTapeLowering.supportedReadWriteRows3_of_supports_eq_true
    (structuredLiftOneTapeDescription_supportsReadWriteRows3 D)

def structuredRightBlankLocalGapCompactorDescription :
    Structured.Description :=
  structuredLiftOneTapeDescription
    CommonGround.FiniteTransducers.rightBlankLocalGapCompactorDescription

def structuredRightBlankGapPayloadScanDescription :
    Structured.Description :=
  structuredLiftOneTapeDescription
    CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription

def structuredLiftedSentinelGapCompactorDescription :
    Structured.Description :=
  structuredLiftOneTapeDescription
    CommonGround.FiniteTransducers.sentinelGapCompactorDescription

def structuredOneGapRightEndCompactorDescription :
    Structured.Description :=
  structuredLiftOneTapeDescription
    CommonGround.FiniteTransducers.oneGapRightEndCompactorDescription

def structuredScanQuoteRestToLocalGapSourceDescription :
    Structured.Description :=
  structuredLiftOneTapeDescription scanQuoteRestToLocalGapSourceDescription

def mixedOptionCellQuoteLiveTailJoinerOneTapeDescription :
    MachineDescription :=
  CommonGround.FiniteTransducers.canonicalSeqDescription
    scanQuoteRestToLocalGapSourceDescription
    CommonGround.FiniteTransducers.rightBlankLocalGapCompactorDescription

/-!
The straight lifted one-tape sequence is kept only as a diagnostic prototype.
It halts on small assembly probes, but it is not the public structured joiner:
the tailed three-tape debugger shows that it preserves normalized output for
empty source rest only modulo a wrong head position, and produces a normalized
output mismatch at the quote-rest/raw-tail boundary for nonempty source rest.
-/
def structuredMixedOptionCellQuoteLiveTailJoinerDiagnosticLiftDescription :
    Structured.Description :=
  structuredLiftOneTapeDescription
    mixedOptionCellQuoteLiveTailJoinerOneTapeDescription

theorem structuredRightBlankLocalGapCompactorDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredRightBlankLocalGapCompactorDescription :=
  structuredLiftOneTapeDescription_supported
    CommonGround.FiniteTransducers.rightBlankLocalGapCompactorDescription

theorem structuredRightBlankGapPayloadScanDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredRightBlankGapPayloadScanDescription :=
  structuredLiftOneTapeDescription_supported
    CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription

theorem structuredLiftedSentinelGapCompactorDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredLiftedSentinelGapCompactorDescription :=
  structuredLiftOneTapeDescription_supported
    CommonGround.FiniteTransducers.sentinelGapCompactorDescription

theorem structuredOneGapRightEndCompactorDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredOneGapRightEndCompactorDescription :=
  structuredLiftOneTapeDescription_supported
    CommonGround.FiniteTransducers.oneGapRightEndCompactorDescription

theorem structuredScanQuoteRestToLocalGapSourceDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredScanQuoteRestToLocalGapSourceDescription :=
  structuredLiftOneTapeDescription_supported
    scanQuoteRestToLocalGapSourceDescription

theorem structuredMixedOptionCellQuoteLiveTailJoinerDiagnosticLiftDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredMixedOptionCellQuoteLiveTailJoinerDiagnosticLiftDescription :=
  structuredLiftOneTapeDescription_supported
    mixedOptionCellQuoteLiveTailJoinerOneTapeDescription

theorem structuredRightBlankGapPayloadScanDescription_run_to_target
    (baseLeft : List (Option Bool)) (gap : Nat)
    (current : Bool) (payloadRest : Word Bool)
    (padding : List (Option Bool)) (scratch work : Tape Bool) :
    exists n : Nat,
      structuredRightBlankGapPayloadScanDescription.runConfig n
          (Structured.MultiTapeLowering.ThreeTape.config
            CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription.start
            (CommonGround.FiniteTransducers.rightBlankGapPayloadScanSourceTape
              baseLeft gap current payloadRest padding)
            scratch work) =
        Structured.MultiTapeLowering.ThreeTape.config
          CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription.halt
          (CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape
            baseLeft gap current payloadRest padding)
          scratch work := by
  simpa [structuredRightBlankGapPayloadScanDescription] using
    structuredLiftOneTapeDescription_runConfig_eq_halt_of_haltsFromTape
      CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription
      (input :=
        CommonGround.FiniteTransducers.rightBlankGapPayloadScanSourceTape
          baseLeft gap current payloadRest padding)
      (output :=
        CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape
          baseLeft gap current payloadRest padding)
      (scratch := scratch)
      (work := work)
      (CommonGround.FiniteTransducers.rightBlankGapPayloadScanDescription_haltsFromTape
        baseLeft gap current payloadRest padding)

theorem structuredLiftedSentinelGapCompactorDescription_run_final_pass
    (baseTail : List (Option Bool)) (leftBit current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat)
    (rightPadding : List (Option Bool)) (scratch work : Tape Bool) :
    exists n : Nat,
      structuredLiftedSentinelGapCompactorDescription.runConfig n
          (Structured.MultiTapeLowering.ThreeTape.config
            CommonGround.FiniteTransducers.sentinelGapCompactorDescription.start
            (CommonGround.FiniteTransducers.rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
              (some leftBit :: baseTail) current leftRest paddingScratch
              rightPadding)
            scratch work) =
        Structured.MultiTapeLowering.ThreeTape.config
          CommonGround.FiniteTransducers.sentinelGapCompactorDescription.halt
          (CommonGround.FiniteTransducers.leadingBlankLeftShiftTargetTapeWithPadding
            (some leftBit :: baseTail) (current :: leftRest).reverse
            (List.append
              (List.replicate paddingScratch (none : Option Bool))
              rightPadding))
          scratch work := by
  simpa [structuredLiftedSentinelGapCompactorDescription] using
    structuredLiftOneTapeDescription_runConfig_eq_halt_of_haltsFromTape
      CommonGround.FiniteTransducers.sentinelGapCompactorDescription
      (input :=
        CommonGround.FiniteTransducers.rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
          (some leftBit :: baseTail) current leftRest paddingScratch
          rightPadding)
      (output :=
        CommonGround.FiniteTransducers.leadingBlankLeftShiftTargetTapeWithPadding
          (some leftBit :: baseTail) (current :: leftRest).reverse
          (List.append
            (List.replicate paddingScratch (none : Option Bool))
            rightPadding))
      (scratch := scratch)
      (work := work)
      (CommonGround.FiniteTransducers.sentinelGapCompactorDescription_haltsFromTape_final_pass
        baseTail leftBit current leftRest paddingScratch rightPadding)

theorem structuredOneGapRightEndCompactorDescription_run_leftStack
    (baseLeft : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (padding : List (Option Bool))
    (scratch work : Tape Bool) :
    exists n : Nat,
      structuredOneGapRightEndCompactorDescription.runConfig n
          (Structured.MultiTapeLowering.ThreeTape.config
            CommonGround.FiniteTransducers.oneGapRightEndCompactorDescription.start
            (CommonGround.FiniteTransducers.rightEdgeRewindSourceTapeWithBase
              baseLeft (current :: leftRest).reverse padding)
            scratch work) =
        Structured.MultiTapeLowering.ThreeTape.config
          CommonGround.FiniteTransducers.oneGapRightEndCompactorDescription.halt
          (CommonGround.FiniteTransducers.leadingBlankLeftShiftTargetTapeWithPadding
            baseLeft (current :: leftRest).reverse padding)
          scratch work := by
  simpa [structuredOneGapRightEndCompactorDescription] using
    structuredLiftOneTapeDescription_runConfig_eq_halt_of_haltsFromTape
      CommonGround.FiniteTransducers.oneGapRightEndCompactorDescription
      (input :=
        CommonGround.FiniteTransducers.rightEdgeRewindSourceTapeWithBase
          baseLeft (current :: leftRest).reverse padding)
      (output :=
        CommonGround.FiniteTransducers.leadingBlankLeftShiftTargetTapeWithPadding
          baseLeft (current :: leftRest).reverse padding)
      (scratch := scratch)
      (work := work)
      (CommonGround.FiniteTransducers.oneGapRightEndCompactorDescription_haltsFromTapeWithBase_leftStack
        baseLeft current leftRest padding)

theorem structuredRightBlankLocalGapCompactorDescription_run_leftStack_rightPadding
    (baseLeft : List (Option Bool)) (current : Bool)
    (leftRest : Word Bool) (paddingScratch : Nat)
    (pad : Option Bool) (rightPadding : List (Option Bool))
    (scratch work : Tape Bool) :
    exists n : Nat,
      structuredRightBlankLocalGapCompactorDescription.runConfig n
          (Structured.MultiTapeLowering.ThreeTape.config
            CommonGround.FiniteTransducers.rightBlankLocalGapCompactorDescription.start
            (CommonGround.FiniteTransducers.rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
              baseLeft current leftRest paddingScratch
              (pad :: rightPadding))
            scratch work) =
        Structured.MultiTapeLowering.ThreeTape.config
          CommonGround.FiniteTransducers.rightBlankLocalGapCompactorDescription.halt
          (CommonGround.FiniteTransducers.leadingBlankLeftShiftTargetTapeWithPadding
            baseLeft (current :: leftRest).reverse
            (List.append
              (List.replicate paddingScratch (none : Option Bool))
              (pad :: rightPadding)))
          scratch work := by
  simpa [structuredRightBlankLocalGapCompactorDescription] using
    structuredLiftOneTapeDescription_runConfig_eq_halt_of_haltsFromTape
      CommonGround.FiniteTransducers.rightBlankLocalGapCompactorDescription
      (input :=
        CommonGround.FiniteTransducers.rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
          baseLeft current leftRest paddingScratch (pad :: rightPadding))
      (output :=
        CommonGround.FiniteTransducers.leadingBlankLeftShiftTargetTapeWithPadding
          baseLeft (current :: leftRest).reverse
          (List.append
            (List.replicate paddingScratch (none : Option Bool))
            (pad :: rightPadding)))
      (scratch := scratch)
      (work := work)
      (CommonGround.FiniteTransducers.rightBlankLocalGapCompactorDescription_haltsFromTapeWithBase_leftStack_rightPadding
        baseLeft current leftRest paddingScratch pad rightPadding)

theorem structuredRightBlankLocalGapCompactorDescription_run_gapBase_succ_to_nextSource
    (gap : Nat) (baseTail : List (Option Bool))
    (current : Bool) (leftRest : Word Bool)
    (paddingScratch : Nat) (rightPadding : List (Option Bool))
    (scratch work : Tape Bool) :
    exists n : Nat,
      structuredRightBlankLocalGapCompactorDescription.runConfig n
          (Structured.MultiTapeLowering.ThreeTape.config
            CommonGround.FiniteTransducers.rightBlankLocalGapCompactorDescription.start
            (CommonGround.FiniteTransducers.rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
              (CommonGround.FiniteTransducers.rightBlankLocalGapBaseLeft
                gap.succ baseTail)
              current leftRest paddingScratch
              (none :: rightPadding))
            scratch work) =
        Structured.MultiTapeLowering.ThreeTape.config
          CommonGround.FiniteTransducers.rightBlankLocalGapCompactorDescription.halt
          (CommonGround.FiniteTransducers.rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
            (CommonGround.FiniteTransducers.rightBlankLocalGapBaseLeft
              gap baseTail)
            current leftRest 2
            (List.append
              (List.replicate paddingScratch (none : Option Bool))
              rightPadding))
          scratch work := by
  simpa [structuredRightBlankLocalGapCompactorDescription] using
    structuredLiftOneTapeDescription_runConfig_eq_halt_of_haltsFromTape
      CommonGround.FiniteTransducers.rightBlankLocalGapCompactorDescription
      (input :=
        CommonGround.FiniteTransducers.rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
          (CommonGround.FiniteTransducers.rightBlankLocalGapBaseLeft
            gap.succ baseTail)
          current leftRest paddingScratch
          (none :: rightPadding))
      (output :=
        CommonGround.FiniteTransducers.rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
          (CommonGround.FiniteTransducers.rightBlankLocalGapBaseLeft
            gap baseTail)
          current leftRest 2
          (List.append
            (List.replicate paddingScratch (none : Option Bool))
            rightPadding))
      (scratch := scratch)
      (work := work)
      (CommonGround.FiniteTransducers.rightBlankLocalGapCompactorDescription_haltsFrom_gapBase_succ_to_nextSource
        gap baseTail current leftRest paddingScratch rightPadding)

def structuredJoinerEntryStart : Nat := 0

def structuredJoinerEntrySeparator : Nat := 1

def structuredJoinerEntryHalt : Nat := 2

/--
Entry phase for the assembly joiner.  It advances tape 0 from the last raw-tail
cell to the first quote-rest cell (or the trailing blank when quote-rest is
empty) while keeping the auxiliary tapes fixed.
-/
def structuredJoinerEntryRows : List Structured.Transition :=
  List.append
    (Structured.MultiTapeLowering.ThreeTape.allReadRows3
      structuredJoinerEntryStart structuredJoinerEntrySeparator
      Structured.MultiTapeLowering.ThreeTape.keepR
      Structured.MultiTapeLowering.ThreeTape.keepS
      Structured.MultiTapeLowering.ThreeTape.keepS)
    (Structured.MultiTapeLowering.ThreeTape.allReadRows3
      structuredJoinerEntrySeparator structuredJoinerEntryHalt
      Structured.MultiTapeLowering.ThreeTape.keepR
      Structured.MultiTapeLowering.ThreeTape.keepS
      Structured.MultiTapeLowering.ThreeTape.keepS)

def structuredJoinerEntryDescription : Structured.Description :=
  Structured.MultiTapeLowering.ThreeTape.description
    3 structuredJoinerEntryStart structuredJoinerEntryHalt
    structuredJoinerEntryRows

theorem structuredJoinerEntryRows_supportsReadWriteRow3 :
    forall row : Structured.Transition,
      row ∈ structuredJoinerEntryRows ->
        Structured.MultiTapeLowering.supportsReadWriteRow3 row =
          true := by
  intro row hrow
  simp [structuredJoinerEntryRows] at hrow
  rcases hrow with hrow | hrow <;> three_tape_support

theorem structuredJoinerEntryDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredJoinerEntryDescription :=
  Structured.MultiTapeLowering.ThreeTape.description_supported
    3 structuredJoinerEntryStart structuredJoinerEntryHalt
    structuredJoinerEntryRows
    structuredJoinerEntryRows_supportsReadWriteRow3

theorem structuredJoinerEntryDescription_lookup_start
    (source scratch work : Tape Bool) :
    structuredJoinerEntryDescription.lookupTransition
        (Structured.MultiTapeLowering.ThreeTape.config
          structuredJoinerEntryStart source scratch work) =
      some
        (Structured.MultiTapeLowering.ThreeTape.row
          structuredJoinerEntryStart
          (Tape.read source) (Tape.read scratch) (Tape.read work)
          Structured.MultiTapeLowering.ThreeTape.keepR
          Structured.MultiTapeLowering.ThreeTape.keepS
          Structured.MultiTapeLowering.ThreeTape.keepS
          structuredJoinerEntrySeparator) := by
  rw [Structured.Description.lookupTransition]
  change
    (structuredJoinerEntryRows.find?
        (Structured.Description.Matches
          structuredJoinerEntryStart
          [Tape.read source, Tape.read scratch, Tape.read work])) =
      some
        (Structured.MultiTapeLowering.ThreeTape.row
          structuredJoinerEntryStart
          (Tape.read source) (Tape.read scratch) (Tape.read work)
          Structured.MultiTapeLowering.ThreeTape.keepR
          Structured.MultiTapeLowering.ThreeTape.keepS
          Structured.MultiTapeLowering.ThreeTape.keepS
          structuredJoinerEntrySeparator)
  unfold structuredJoinerEntryRows
  exact
    Structured.MultiTapeLowering.ThreeTape.find?_append_of_find?_eq_some
      (Structured.MultiTapeLowering.ThreeTape.allReadRows3_find?_same
        structuredJoinerEntryStart structuredJoinerEntrySeparator
        (Tape.read source) (Tape.read scratch) (Tape.read work)
        Structured.MultiTapeLowering.ThreeTape.keepR
        Structured.MultiTapeLowering.ThreeTape.keepS
        Structured.MultiTapeLowering.ThreeTape.keepS)

theorem structuredJoinerEntryDescription_lookup_separator
    (source scratch work : Tape Bool) :
    structuredJoinerEntryDescription.lookupTransition
        (Structured.MultiTapeLowering.ThreeTape.config
          structuredJoinerEntrySeparator source scratch work) =
      some
        (Structured.MultiTapeLowering.ThreeTape.row
          structuredJoinerEntrySeparator
          (Tape.read source) (Tape.read scratch) (Tape.read work)
          Structured.MultiTapeLowering.ThreeTape.keepR
          Structured.MultiTapeLowering.ThreeTape.keepS
          Structured.MultiTapeLowering.ThreeTape.keepS
          structuredJoinerEntryHalt) := by
  rw [Structured.Description.lookupTransition]
  change
    (structuredJoinerEntryRows.find?
        (Structured.Description.Matches
          structuredJoinerEntrySeparator
          [Tape.read source, Tape.read scratch, Tape.read work])) =
      some
        (Structured.MultiTapeLowering.ThreeTape.row
          structuredJoinerEntrySeparator
          (Tape.read source) (Tape.read scratch) (Tape.read work)
          Structured.MultiTapeLowering.ThreeTape.keepR
          Structured.MultiTapeLowering.ThreeTape.keepS
          Structured.MultiTapeLowering.ThreeTape.keepS
          structuredJoinerEntryHalt)
  unfold structuredJoinerEntryRows
  change
    List.find?
        (Structured.Description.Matches
          structuredJoinerEntrySeparator
          [Tape.read source, Tape.read scratch, Tape.read work])
        (Structured.MultiTapeLowering.ThreeTape.allReadRows3
          structuredJoinerEntryStart structuredJoinerEntrySeparator
          Structured.MultiTapeLowering.ThreeTape.keepR
          Structured.MultiTapeLowering.ThreeTape.keepS
          Structured.MultiTapeLowering.ThreeTape.keepS ++
        Structured.MultiTapeLowering.ThreeTape.allReadRows3
          structuredJoinerEntrySeparator structuredJoinerEntryHalt
          Structured.MultiTapeLowering.ThreeTape.keepR
          Structured.MultiTapeLowering.ThreeTape.keepS
          Structured.MultiTapeLowering.ThreeTape.keepS) =
      some
        (Structured.MultiTapeLowering.ThreeTape.row
          structuredJoinerEntrySeparator
          (Tape.read source) (Tape.read scratch) (Tape.read work)
          Structured.MultiTapeLowering.ThreeTape.keepR
          Structured.MultiTapeLowering.ThreeTape.keepS
          Structured.MultiTapeLowering.ThreeTape.keepS
          structuredJoinerEntryHalt)
  rw [
    Structured.MultiTapeLowering.ThreeTape.find?_append_of_find?_eq_none
      (Structured.MultiTapeLowering.ThreeTape.allReadRows3_find?_other
        (state := structuredJoinerEntrySeparator)
        (source := structuredJoinerEntryStart)
        (target := structuredJoinerEntrySeparator)
        (Tape.read source) (Tape.read scratch) (Tape.read work)
        Structured.MultiTapeLowering.ThreeTape.keepR
        Structured.MultiTapeLowering.ThreeTape.keepS
        Structured.MultiTapeLowering.ThreeTape.keepS
        (by decide))]
  exact
    Structured.MultiTapeLowering.ThreeTape.allReadRows3_find?_same
      structuredJoinerEntrySeparator structuredJoinerEntryHalt
      (Tape.read source) (Tape.read scratch) (Tape.read work)
      Structured.MultiTapeLowering.ThreeTape.keepR
      Structured.MultiTapeLowering.ThreeTape.keepS
      Structured.MultiTapeLowering.ThreeTape.keepS

theorem structuredJoinerEntryDescription_step_start
    (source scratch work : Tape Bool) :
    structuredJoinerEntryDescription.stepConfig
        (Structured.MultiTapeLowering.ThreeTape.config
          structuredJoinerEntryStart source scratch work) =
      some
        (Structured.MultiTapeLowering.ThreeTape.config
          structuredJoinerEntrySeparator
          (Tape.move Direction.right source) scratch work) := by
  rw [Structured.Description.stepConfig]
  rw [structuredJoinerEntryDescription_lookup_start]
  unfold structuredJoinerEntryDescription
  three_tape_step []

theorem structuredJoinerEntryDescription_step_separator
    (source scratch work : Tape Bool) :
    structuredJoinerEntryDescription.stepConfig
        (Structured.MultiTapeLowering.ThreeTape.config
          structuredJoinerEntrySeparator source scratch work) =
      some
        (Structured.MultiTapeLowering.ThreeTape.config
          structuredJoinerEntryHalt
          (Tape.move Direction.right source) scratch work) := by
  rw [Structured.Description.stepConfig]
  rw [structuredJoinerEntryDescription_lookup_separator]
  unfold structuredJoinerEntryDescription
  three_tape_step []

theorem structuredJoinerEntryDescription_run_two
    (source scratch work : Tape Bool) :
    structuredJoinerEntryDescription.runConfig 2
        (Structured.MultiTapeLowering.ThreeTape.config
          structuredJoinerEntryStart source scratch work) =
      Structured.MultiTapeLowering.ThreeTape.config
        structuredJoinerEntryHalt
        (Tape.move Direction.right (Tape.move Direction.right source))
        scratch work := by
  three_tape_run [
    structuredJoinerEntryDescription_step_start,
    structuredJoinerEntryDescription_step_separator]

def structuredRowsForSourceRead
    (source : Nat) (sourceRead : Option Bool)
    (action0 action1 action2 : Structured.TapeAction)
    (target : Nat) : List Structured.Transition :=
  Structured.MultiTapeLowering.ThreeTape.allReads2
    (fun read1 read2 =>
      Structured.MultiTapeLowering.ThreeTape.row
        source sourceRead read1 read2
        action0 action1 action2 target)

theorem structuredRowsForSourceRead_supportsReadWriteRow3
    (source : Nat) (sourceRead : Option Bool)
    (action0 action1 action2 : Structured.TapeAction)
    (target : Nat) :
    forall row : Structured.Transition,
      row ∈ structuredRowsForSourceRead
          source sourceRead action0 action1 action2 target ->
        Structured.MultiTapeLowering.supportsReadWriteRow3 row =
          true := by
  intro row hrow
  simp [structuredRowsForSourceRead,
    Structured.MultiTapeLowering.ThreeTape.allReads2] at hrow
  rcases hrow with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact
      Structured.MultiTapeLowering.ThreeTape.row_supportsReadWriteRow3
        _ _ _ _ _ _ _ _

theorem structuredRowsForSourceRead_find?_same
    (source target : Nat) (sourceRead read1 read2 : Option Bool)
    (action0 action1 action2 : Structured.TapeAction) :
    List.find?
        (Structured.Description.Matches
          source [sourceRead, read1, read2])
        (structuredRowsForSourceRead
          source sourceRead action0 action1 action2 target) =
      some
        (Structured.MultiTapeLowering.ThreeTape.row
          source sourceRead read1 read2 action0 action1 action2
          target) := by
  cases sourceRead <;> (try cases ‹Bool›) <;>
    cases read1 <;> (try cases ‹Bool›) <;>
      cases read2 <;> (try cases ‹Bool›) <;>
        simp [structuredRowsForSourceRead,
          Structured.MultiTapeLowering.ThreeTape.allReads2,
          Structured.MultiTapeLowering.ThreeTape.row,
          Structured.Description.Matches]

theorem structuredRowsForSourceRead_find?_otherSourceRead
    (source target : Nat) (expected actual read1 read2 : Option Bool)
    (action0 action1 action2 : Structured.TapeAction)
    (hactual : actual ≠ expected) :
    List.find?
        (Structured.Description.Matches
          source [actual, read1, read2])
        (structuredRowsForSourceRead
          source expected action0 action1 action2 target) =
      none := by
  cases expected <;> (try cases ‹Bool›) <;>
    cases actual <;> (try cases ‹Bool›) <;>
      cases read1 <;> (try cases ‹Bool›) <;>
        cases read2 <;> (try cases ‹Bool›) <;>
          simp [structuredRowsForSourceRead,
            Structured.MultiTapeLowering.ThreeTape.allReads2,
            Structured.MultiTapeLowering.ThreeTape.row,
            Structured.Description.Matches] at hactual ⊢

def structuredQuoteRestCopyStart : Nat := 0

def structuredQuoteRestCopyHalt : Nat := 1

def structuredQuoteRestCopyRows : List Structured.Transition :=
  List.append
    (structuredRowsForSourceRead structuredQuoteRestCopyStart
      (some false)
      Structured.MultiTapeLowering.ThreeTape.keepR
      (Structured.MultiTapeLowering.ThreeTape.writeBitR false)
      Structured.MultiTapeLowering.ThreeTape.keepS
      structuredQuoteRestCopyStart)
    (List.append
      (structuredRowsForSourceRead structuredQuoteRestCopyStart
        (some true)
        Structured.MultiTapeLowering.ThreeTape.keepR
        (Structured.MultiTapeLowering.ThreeTape.writeBitR true)
        Structured.MultiTapeLowering.ThreeTape.keepS
        structuredQuoteRestCopyStart)
      (structuredRowsForSourceRead structuredQuoteRestCopyStart
        none
        Structured.MultiTapeLowering.ThreeTape.keepS
        Structured.MultiTapeLowering.ThreeTape.keepS
        Structured.MultiTapeLowering.ThreeTape.keepS
        structuredQuoteRestCopyHalt))

def structuredQuoteRestCopyDescription : Structured.Description :=
  Structured.MultiTapeLowering.ThreeTape.description
    2 structuredQuoteRestCopyStart structuredQuoteRestCopyHalt
    structuredQuoteRestCopyRows

theorem structuredQuoteRestCopyDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredQuoteRestCopyDescription := by
  refine ⟨rfl, ?_⟩
  intro row hrow
  simp [structuredQuoteRestCopyDescription,
    Structured.MultiTapeLowering.ThreeTape.description,
    structuredQuoteRestCopyRows] at hrow
  rcases hrow with hrow | hrow | hrow
  · exact
      structuredRowsForSourceRead_supportsReadWriteRow3
        structuredQuoteRestCopyStart (some false)
        Structured.MultiTapeLowering.ThreeTape.keepR
        (Structured.MultiTapeLowering.ThreeTape.writeBitR false)
        Structured.MultiTapeLowering.ThreeTape.keepS
        structuredQuoteRestCopyStart row hrow
  · exact
      structuredRowsForSourceRead_supportsReadWriteRow3
        structuredQuoteRestCopyStart (some true)
        Structured.MultiTapeLowering.ThreeTape.keepR
        (Structured.MultiTapeLowering.ThreeTape.writeBitR true)
        Structured.MultiTapeLowering.ThreeTape.keepS
        structuredQuoteRestCopyStart row hrow
  · exact
      structuredRowsForSourceRead_supportsReadWriteRow3
        structuredQuoteRestCopyStart none
        Structured.MultiTapeLowering.ThreeTape.keepS
        Structured.MultiTapeLowering.ThreeTape.keepS
        Structured.MultiTapeLowering.ThreeTape.keepS
        structuredQuoteRestCopyHalt row hrow

theorem structuredQuoteRestCopyRows_find?_false
    (read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches
          structuredQuoteRestCopyStart [some false, read1, read2])
        structuredQuoteRestCopyRows =
      some
        (Structured.MultiTapeLowering.ThreeTape.row
          structuredQuoteRestCopyStart (some false) read1 read2
          Structured.MultiTapeLowering.ThreeTape.keepR
          (Structured.MultiTapeLowering.ThreeTape.writeBitR false)
          Structured.MultiTapeLowering.ThreeTape.keepS
          structuredQuoteRestCopyStart) := by
  unfold structuredQuoteRestCopyRows
  exact
    Structured.MultiTapeLowering.ThreeTape.find?_append_of_find?_eq_some
      (structuredRowsForSourceRead_find?_same
        structuredQuoteRestCopyStart structuredQuoteRestCopyStart
        (some false) read1 read2
        Structured.MultiTapeLowering.ThreeTape.keepR
        (Structured.MultiTapeLowering.ThreeTape.writeBitR false)
        Structured.MultiTapeLowering.ThreeTape.keepS)

theorem structuredQuoteRestCopyRows_find?_true
    (read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches
          structuredQuoteRestCopyStart [some true, read1, read2])
        structuredQuoteRestCopyRows =
      some
        (Structured.MultiTapeLowering.ThreeTape.row
          structuredQuoteRestCopyStart (some true) read1 read2
          Structured.MultiTapeLowering.ThreeTape.keepR
          (Structured.MultiTapeLowering.ThreeTape.writeBitR true)
          Structured.MultiTapeLowering.ThreeTape.keepS
          structuredQuoteRestCopyStart) := by
  unfold structuredQuoteRestCopyRows
  change
    List.find?
        (Structured.Description.Matches
          structuredQuoteRestCopyStart [some true, read1, read2])
        (structuredRowsForSourceRead structuredQuoteRestCopyStart
            (some false)
            Structured.MultiTapeLowering.ThreeTape.keepR
            (Structured.MultiTapeLowering.ThreeTape.writeBitR false)
            Structured.MultiTapeLowering.ThreeTape.keepS
            structuredQuoteRestCopyStart ++
          (structuredRowsForSourceRead structuredQuoteRestCopyStart
              (some true)
              Structured.MultiTapeLowering.ThreeTape.keepR
              (Structured.MultiTapeLowering.ThreeTape.writeBitR true)
              Structured.MultiTapeLowering.ThreeTape.keepS
              structuredQuoteRestCopyStart ++
            structuredRowsForSourceRead structuredQuoteRestCopyStart
              none
              Structured.MultiTapeLowering.ThreeTape.keepS
              Structured.MultiTapeLowering.ThreeTape.keepS
              Structured.MultiTapeLowering.ThreeTape.keepS
              structuredQuoteRestCopyHalt)) =
      some
        (Structured.MultiTapeLowering.ThreeTape.row
          structuredQuoteRestCopyStart (some true) read1 read2
          Structured.MultiTapeLowering.ThreeTape.keepR
          (Structured.MultiTapeLowering.ThreeTape.writeBitR true)
          Structured.MultiTapeLowering.ThreeTape.keepS
          structuredQuoteRestCopyStart)
  rw [
    Structured.MultiTapeLowering.ThreeTape.find?_append_of_find?_eq_none
      (structuredRowsForSourceRead_find?_otherSourceRead
        structuredQuoteRestCopyStart structuredQuoteRestCopyStart
        (some false) (some true) read1 read2
        Structured.MultiTapeLowering.ThreeTape.keepR
        (Structured.MultiTapeLowering.ThreeTape.writeBitR false)
        Structured.MultiTapeLowering.ThreeTape.keepS
        (by decide))]
  exact
    Structured.MultiTapeLowering.ThreeTape.find?_append_of_find?_eq_some
      (structuredRowsForSourceRead_find?_same
        structuredQuoteRestCopyStart structuredQuoteRestCopyStart
        (some true) read1 read2
        Structured.MultiTapeLowering.ThreeTape.keepR
        (Structured.MultiTapeLowering.ThreeTape.writeBitR true)
        Structured.MultiTapeLowering.ThreeTape.keepS)

theorem structuredQuoteRestCopyRows_find?_blank
    (read1 read2 : Option Bool) :
    List.find?
        (Structured.Description.Matches
          structuredQuoteRestCopyStart [none, read1, read2])
        structuredQuoteRestCopyRows =
      some
        (Structured.MultiTapeLowering.ThreeTape.row
          structuredQuoteRestCopyStart none read1 read2
          Structured.MultiTapeLowering.ThreeTape.keepS
          Structured.MultiTapeLowering.ThreeTape.keepS
          Structured.MultiTapeLowering.ThreeTape.keepS
          structuredQuoteRestCopyHalt) := by
  unfold structuredQuoteRestCopyRows
  change
    List.find?
        (Structured.Description.Matches
          structuredQuoteRestCopyStart [none, read1, read2])
        (structuredRowsForSourceRead structuredQuoteRestCopyStart
            (some false)
            Structured.MultiTapeLowering.ThreeTape.keepR
            (Structured.MultiTapeLowering.ThreeTape.writeBitR false)
            Structured.MultiTapeLowering.ThreeTape.keepS
            structuredQuoteRestCopyStart ++
          (structuredRowsForSourceRead structuredQuoteRestCopyStart
              (some true)
              Structured.MultiTapeLowering.ThreeTape.keepR
              (Structured.MultiTapeLowering.ThreeTape.writeBitR true)
              Structured.MultiTapeLowering.ThreeTape.keepS
              structuredQuoteRestCopyStart ++
            structuredRowsForSourceRead structuredQuoteRestCopyStart
              none
              Structured.MultiTapeLowering.ThreeTape.keepS
              Structured.MultiTapeLowering.ThreeTape.keepS
              Structured.MultiTapeLowering.ThreeTape.keepS
              structuredQuoteRestCopyHalt)) =
      some
        (Structured.MultiTapeLowering.ThreeTape.row
          structuredQuoteRestCopyStart none read1 read2
          Structured.MultiTapeLowering.ThreeTape.keepS
          Structured.MultiTapeLowering.ThreeTape.keepS
          Structured.MultiTapeLowering.ThreeTape.keepS
          structuredQuoteRestCopyHalt)
  rw [
    Structured.MultiTapeLowering.ThreeTape.find?_append_of_find?_eq_none
      (structuredRowsForSourceRead_find?_otherSourceRead
        structuredQuoteRestCopyStart structuredQuoteRestCopyStart
        (some false) none read1 read2
        Structured.MultiTapeLowering.ThreeTape.keepR
        (Structured.MultiTapeLowering.ThreeTape.writeBitR false)
        Structured.MultiTapeLowering.ThreeTape.keepS
        (by decide))]
  rw [
    Structured.MultiTapeLowering.ThreeTape.find?_append_of_find?_eq_none
      (structuredRowsForSourceRead_find?_otherSourceRead
        structuredQuoteRestCopyStart structuredQuoteRestCopyStart
        (some true) none read1 read2
        Structured.MultiTapeLowering.ThreeTape.keepR
        (Structured.MultiTapeLowering.ThreeTape.writeBitR true)
        Structured.MultiTapeLowering.ThreeTape.keepS
        (by decide))]
  exact
    structuredRowsForSourceRead_find?_same
      structuredQuoteRestCopyStart structuredQuoteRestCopyHalt
      none read1 read2
      Structured.MultiTapeLowering.ThreeTape.keepS
      Structured.MultiTapeLowering.ThreeTape.keepS
      Structured.MultiTapeLowering.ThreeTape.keepS

theorem structuredQuoteRestCopyDescription_lookup_false
    (source scratch work : Tape Bool)
    (hsource : Tape.read source = some false) :
    structuredQuoteRestCopyDescription.lookupTransition
        (Structured.MultiTapeLowering.ThreeTape.config
          structuredQuoteRestCopyStart source scratch work) =
      some
        (Structured.MultiTapeLowering.ThreeTape.row
          structuredQuoteRestCopyStart
          (some false) (Tape.read scratch) (Tape.read work)
          Structured.MultiTapeLowering.ThreeTape.keepR
          (Structured.MultiTapeLowering.ThreeTape.writeBitR false)
          Structured.MultiTapeLowering.ThreeTape.keepS
          structuredQuoteRestCopyStart) := by
  rw [Structured.Description.lookupTransition]
  change
    List.find?
        (Structured.Description.Matches
          structuredQuoteRestCopyStart
          [Tape.read source, Tape.read scratch, Tape.read work])
        structuredQuoteRestCopyRows =
      some
        (Structured.MultiTapeLowering.ThreeTape.row
          structuredQuoteRestCopyStart
          (some false) (Tape.read scratch) (Tape.read work)
          Structured.MultiTapeLowering.ThreeTape.keepR
          (Structured.MultiTapeLowering.ThreeTape.writeBitR false)
          Structured.MultiTapeLowering.ThreeTape.keepS
          structuredQuoteRestCopyStart)
  rw [hsource]
  exact structuredQuoteRestCopyRows_find?_false
    (Tape.read scratch) (Tape.read work)

theorem structuredQuoteRestCopyDescription_lookup_true
    (source scratch work : Tape Bool)
    (hsource : Tape.read source = some true) :
    structuredQuoteRestCopyDescription.lookupTransition
        (Structured.MultiTapeLowering.ThreeTape.config
          structuredQuoteRestCopyStart source scratch work) =
      some
        (Structured.MultiTapeLowering.ThreeTape.row
          structuredQuoteRestCopyStart
          (some true) (Tape.read scratch) (Tape.read work)
          Structured.MultiTapeLowering.ThreeTape.keepR
          (Structured.MultiTapeLowering.ThreeTape.writeBitR true)
          Structured.MultiTapeLowering.ThreeTape.keepS
          structuredQuoteRestCopyStart) := by
  rw [Structured.Description.lookupTransition]
  change
    List.find?
        (Structured.Description.Matches
          structuredQuoteRestCopyStart
          [Tape.read source, Tape.read scratch, Tape.read work])
        structuredQuoteRestCopyRows =
      some
        (Structured.MultiTapeLowering.ThreeTape.row
          structuredQuoteRestCopyStart
          (some true) (Tape.read scratch) (Tape.read work)
          Structured.MultiTapeLowering.ThreeTape.keepR
          (Structured.MultiTapeLowering.ThreeTape.writeBitR true)
          Structured.MultiTapeLowering.ThreeTape.keepS
          structuredQuoteRestCopyStart)
  rw [hsource]
  exact structuredQuoteRestCopyRows_find?_true
    (Tape.read scratch) (Tape.read work)

theorem structuredQuoteRestCopyDescription_lookup_blank
    (source scratch work : Tape Bool)
    (hsource : Tape.read source = none) :
    structuredQuoteRestCopyDescription.lookupTransition
        (Structured.MultiTapeLowering.ThreeTape.config
          structuredQuoteRestCopyStart source scratch work) =
      some
        (Structured.MultiTapeLowering.ThreeTape.row
          structuredQuoteRestCopyStart
          none (Tape.read scratch) (Tape.read work)
          Structured.MultiTapeLowering.ThreeTape.keepS
          Structured.MultiTapeLowering.ThreeTape.keepS
          Structured.MultiTapeLowering.ThreeTape.keepS
          structuredQuoteRestCopyHalt) := by
  rw [Structured.Description.lookupTransition]
  change
    List.find?
        (Structured.Description.Matches
          structuredQuoteRestCopyStart
          [Tape.read source, Tape.read scratch, Tape.read work])
        structuredQuoteRestCopyRows =
      some
        (Structured.MultiTapeLowering.ThreeTape.row
          structuredQuoteRestCopyStart
          none (Tape.read scratch) (Tape.read work)
          Structured.MultiTapeLowering.ThreeTape.keepS
          Structured.MultiTapeLowering.ThreeTape.keepS
          Structured.MultiTapeLowering.ThreeTape.keepS
          structuredQuoteRestCopyHalt)
  rw [hsource]
  exact structuredQuoteRestCopyRows_find?_blank
    (Tape.read scratch) (Tape.read work)

theorem structuredQuoteRestCopyDescription_step_bit
    (baseLeft : List (Option Bool)) (bit : Bool)
    (remaining copied : Word Bool) (work : Tape Bool) :
    structuredQuoteRestCopyDescription.runConfig 1
        (Structured.MultiTapeLowering.ThreeTape.config
          structuredQuoteRestCopyStart
          (tapeAtCells baseLeft
            (some bit :: List.append (remaining.map some) [none]))
          (Structured.MultiTapeLowering.ThreeTape.outputFromBits copied)
          work) =
      Structured.MultiTapeLowering.ThreeTape.config
        structuredQuoteRestCopyStart
        (tapeAtCells (some bit :: baseLeft)
          (List.append (remaining.map some) [none]))
        (Structured.MultiTapeLowering.ThreeTape.outputFromBits
          (List.append copied [bit]))
        work := by
  rw [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig]
  cases bit
  · rw [structuredQuoteRestCopyDescription_lookup_false _ _ _ (by rfl)]
    unfold structuredQuoteRestCopyDescription
    three_tape_step [
      Structured.MultiTapeLowering.ThreeTape.outputFromBits]
    cases h :
        List.map some remaining ++ [none] <;> rfl
  · rw [structuredQuoteRestCopyDescription_lookup_true _ _ _ (by rfl)]
    unfold structuredQuoteRestCopyDescription
    three_tape_step [
      Structured.MultiTapeLowering.ThreeTape.outputFromBits]
    cases h :
        List.map some remaining ++ [none] <;> rfl

theorem structuredQuoteRestCopyDescription_step_blank
    (baseLeft : List (Option Bool)) (copied : Word Bool)
    (work : Tape Bool) :
    structuredQuoteRestCopyDescription.runConfig 1
        (Structured.MultiTapeLowering.ThreeTape.config
          structuredQuoteRestCopyStart
          (tapeAtCells baseLeft [none])
          (Structured.MultiTapeLowering.ThreeTape.outputFromBits copied)
          work) =
      Structured.MultiTapeLowering.ThreeTape.config
        structuredQuoteRestCopyHalt
        (tapeAtCells baseLeft [none])
        (Structured.MultiTapeLowering.ThreeTape.outputFromBits copied)
        work := by
  rw [Structured.Description.runConfig]
  rw [Structured.Description.stepConfig]
  rw [structuredQuoteRestCopyDescription_lookup_blank _ _ _ (by rfl)]
  unfold structuredQuoteRestCopyDescription
  three_tape_step [
    Structured.MultiTapeLowering.ThreeTape.outputFromBits]

theorem structuredQuoteRestCopyDescription_run_loop
    (remaining copied : Word Bool)
    (baseLeft : List (Option Bool)) (work : Tape Bool) :
    structuredQuoteRestCopyDescription.runConfig
        (remaining.length + 1)
        (Structured.MultiTapeLowering.ThreeTape.config
          structuredQuoteRestCopyStart
          (tapeAtCells baseLeft
            (List.append (remaining.map some) [none]))
          (Structured.MultiTapeLowering.ThreeTape.outputFromBits copied)
          work) =
      Structured.MultiTapeLowering.ThreeTape.config
        structuredQuoteRestCopyHalt
        (tapeAtCells
          (List.append (remaining.reverse.map some) baseLeft)
          [none])
        (Structured.MultiTapeLowering.ThreeTape.outputFromBits
          (List.append copied remaining))
        work := by
  induction remaining generalizing baseLeft copied with
  | nil =>
      simpa using
        structuredQuoteRestCopyDescription_step_blank baseLeft copied work
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 = 1 + (rest.length + 1) by
        simp [Nat.add_comm, Nat.add_left_comm]]
      rw [Structured.Description.runConfig_add]
      rw [show
        List.append (List.map some (bit :: rest)) [none] =
          some bit :: List.append (List.map some rest) [none] by
        rfl]
      rw [structuredQuoteRestCopyDescription_step_bit]
      rw [ih (List.append copied [bit]) (some bit :: baseLeft)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem structuredQuoteRestCopyDescription_run
    (quoteRest : Word Bool) (baseLeft : List (Option Bool))
    (work : Tape Bool) :
    structuredQuoteRestCopyDescription.runConfig
        (quoteRest.length + 1)
        (Structured.MultiTapeLowering.ThreeTape.config
          structuredQuoteRestCopyStart
          (tapeAtCells baseLeft
            (List.append (quoteRest.map some) [none]))
          (Structured.MultiTapeLowering.ThreeTape.outputFromBits [])
          work) =
      Structured.MultiTapeLowering.ThreeTape.config
        structuredQuoteRestCopyHalt
        (tapeAtCells
          (List.append (quoteRest.reverse.map some) baseLeft)
          [none])
        (Structured.MultiTapeLowering.ThreeTape.outputFromBits quoteRest)
        work := by
  simpa using
    structuredQuoteRestCopyDescription_run_loop quoteRest [] baseLeft work

def structuredMixedOptionCellQuoteLiveTailJoinerScratchTape :
    Tape Bool :=
  Structured.MultiTapeLowering.ThreeTape.outputFromBits []

def structuredMixedOptionCellQuoteLiveTailJoinerWorkTape :
    Tape Bool :=
  Structured.MultiTapeLowering.ThreeTape.outputFromBits []

/-!
The raw tail insertion component is the current lowerer-facing body candidate
for the joiner: at the visible-cell level it transforms
{lit}`emittedPrefix ++ rawTail ++ quoteRest` into
{lit}`emittedPrefix ++ quoteRest ++ rawTail`.

Its source contract starts at the prefix/raw-tail boundary and its final tape is
parked past the restored tail, so the bridges below deliberately prove
{name}`Tape.cells` or {name}`Tape.normalizedOutput` facts rather than exact
public joiner configuration equality.
-/
def structuredRawTailInsertionJoinerDescription :
    Structured.Description :=
  Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.description

theorem structuredRawTailInsertionJoinerDescription_supported :
    Structured.MultiTapeLowering.SupportsReadWriteRows3
      structuredRawTailInsertionJoinerDescription :=
  Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.description_supported

def structuredRawTailInsertionJoinerInitialConfig
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Configuration :=
  Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.initialConfig
    (assemblySourceRestLiveTailEmitterEmittedPrefix p)
    (assemblySourceRestLiveTailEmitterRawTail p)
    (assemblySourceRestLiveTailEmitterQuoteRest p)

def structuredRawTailInsertionJoinerFinalConfig
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Configuration :=
  Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.finalConfig
    (assemblySourceRestLiveTailEmitterEmittedPrefix p)
    (assemblySourceRestLiveTailEmitterRawTail p)
    (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionSource_cells_eq_separated
    (emittedPrefix rawTail quoteRest : Word Bool) :
    Tape.cells
        (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.sourceTape
          emittedPrefix rawTail quoteRest) =
      Tape.cells
        (mixedOptionCellQuoteLiveTailSeparatedTape
          emittedPrefix rawTail quoteRest) := by
  cases rawTail with
  | nil =>
      simp [
        Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.sourceTape,
        mixedOptionCellQuoteLiveTailSeparatedTape,
        DovetailInitialLayoutInitializer.tapeAtCells,
        CommonGround.FiniteTransducers.tapeAtCells,
        Tape.cells, List.map_reverse]
  | cons head rest =>
      rw [mixedOptionCellQuoteLiveTailSeparatedTape_cells_cons]
      simp [
        Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.sourceTape,
        CommonGround.FiniteTransducers.tapeAtCells,
        Tape.cells, List.map_reverse]

theorem structuredRawTailInsertionSource_normalizedOutput_eq_separated
    (emittedPrefix rawTail quoteRest : Word Bool) :
    Tape.normalizedOutput
        (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.sourceTape
          emittedPrefix rawTail quoteRest) =
      Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailSeparatedTape
          emittedPrefix rawTail quoteRest) := by
  simp [Tape.normalizedOutput,
    structuredRawTailInsertionSource_cells_eq_separated]

theorem structuredRawTailInsertionRestoredSource_normalizedOutput_eq_joined
    (emittedPrefix rawTail quoteRest : Word Bool) :
    Tape.normalizedOutput
        (Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoredSourceTape
          emittedPrefix rawTail quoteRest) =
      Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailJoinedTape
          emittedPrefix rawTail quoteRest) := by
  rw [
    Structured.MultiTapeLowering.ThreeTape.RawTailInsertion.restoredSourceTape_normalizedOutput]
  cases rawTail with
  | nil =>
      simp [mixedOptionCellQuoteLiveTailJoinedTape,
        DovetailInitialLayoutInitializer.tapeAtCells,
        Tape.normalizedOutput, Tape.cells, List.map_reverse,
        List.append_assoc, Function.comp_def]
  | cons head rest =>
      change
        List.append emittedPrefix
            (List.append quoteRest (head :: rest)) =
          (Tape.cells
            (mixedOptionCellQuoteLiveTailJoinedTape
              emittedPrefix (head :: rest) quoteRest)).filterMap
            (fun cell => cell)
      rw [mixedOptionCellQuoteLiveTailJoinedTape_cells_cons]
      simp [List.filterMap_append, Function.comp_def]

theorem structuredRawTailInsertionJoinerInitial_source_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerInitialConfig p).tapes 0) =
      Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailSeparatedTape
          (assemblySourceRestLiveTailEmitterEmittedPrefix p)
          (assemblySourceRestLiveTailEmitterRawTail p)
          (assemblySourceRestLiveTailEmitterQuoteRest p)) := by
  exact
    structuredRawTailInsertionSource_normalizedOutput_eq_separated
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerInitial_source_normalizedOutput_eq_afterRawTailScanTape
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerInitialConfig p).tapes 0) =
      Tape.normalizedOutput
        (MixedParserStackWholeSourceAfterRawTailScanTape
          p.w p.sourceRestBits p.stage) := by
  rw [structuredRawTailInsertionJoinerInitial_source_normalizedOutput]
  rw [assemblySourceRestLiveTailJoinerSeparatedTape_eq_afterRawTailScanTape]

theorem structuredRawTailInsertionJoinerFinal_source_normalizedOutput
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerFinalConfig p).tapes 0) =
      Tape.normalizedOutput
        (mixedOptionCellQuoteLiveTailJoinedTape
          (assemblySourceRestLiveTailEmitterEmittedPrefix p)
          (assemblySourceRestLiveTailEmitterRawTail p)
          (assemblySourceRestLiveTailEmitterQuoteRest p)) := by
  exact
    structuredRawTailInsertionRestoredSource_normalizedOutput_eq_joined
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p)

theorem structuredRawTailInsertionJoinerFinal_source_normalizedOutput_eq_targetTape
    (p : AssemblySourceRestLiveTailEmitterParam) :
    Tape.normalizedOutput
        (Structured.Description.tapeAt
          (structuredRawTailInsertionJoinerFinalConfig p).tapes 0) =
      Tape.normalizedOutput
        (assemblySourceRestFinishTargetTape
          p.w p.sourceRestBits p.stage) := by
  rw [structuredRawTailInsertionJoinerFinal_source_normalizedOutput]
  rw [assemblySourceRestLiveTailJoinerJoinedTape_eq_targetTape]

def structuredMixedOptionCellQuoteLiveTailJoinerCompactionLeftCells
    (w sourceRestBits : Word Bool) (stage : Nat)
    (head : Bool) (rawTailRest : Word Bool) :
    List (Option Bool) :=
  List.append
    (((List.append
      (MixedParserStackRewriterLengthHeader
        (assemblySourceRestFinishParserPrefixCells w)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage)
        sourceRestBits)
      (MixedParserStackRewriterPrefixQuote
        (assemblySourceRestFinishParserPrefixCells w)
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage))).reverse.map some).reverse)
    ((head :: rawTailRest).map some)

def structuredMixedOptionCellQuoteLiveTailJoinerCompactionRightPadding
    (sourceRestBits : Word Bool) : List (Option Bool) :=
  List.append ((preservingCellPassCellBits sourceRestBits).map some) [none]

def structuredMixedOptionCellQuoteLiveTailJoinerInitialConfig
    (state : Nat) (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Configuration :=
  Structured.MultiTapeLowering.ThreeTape.config state
    (mixedOptionCellQuoteLiveTailSeparatedTape
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p))
    structuredMixedOptionCellQuoteLiveTailJoinerScratchTape
    structuredMixedOptionCellQuoteLiveTailJoinerWorkTape

def structuredMixedOptionCellQuoteLiveTailJoinerFinalConfig
    (state : Nat) (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Configuration :=
  Structured.MultiTapeLowering.ThreeTape.config state
    (mixedOptionCellQuoteLiveTailJoinedTape
      (assemblySourceRestLiveTailEmitterEmittedPrefix p)
      (assemblySourceRestLiveTailEmitterRawTail p)
      (assemblySourceRestLiveTailEmitterQuoteRest p))
    structuredMixedOptionCellQuoteLiveTailJoinerScratchTape
    structuredMixedOptionCellQuoteLiveTailJoinerWorkTape

theorem structuredJoinerInitialConfig_sourceTape
    (state : Nat) (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Description.tapeAt
        (structuredMixedOptionCellQuoteLiveTailJoinerInitialConfig
          state p).tapes
        0 =
      mixedOptionCellQuoteLiveTailSeparatedTape
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) := by
  rfl

theorem structuredJoinerFinalConfig_sourceTape
    (state : Nat) (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Description.tapeAt
        (structuredMixedOptionCellQuoteLiveTailJoinerFinalConfig
          state p).tapes
        0 =
      mixedOptionCellQuoteLiveTailJoinedTape
        (assemblySourceRestLiveTailEmitterEmittedPrefix p)
        (assemblySourceRestLiveTailEmitterRawTail p)
        (assemblySourceRestLiveTailEmitterQuoteRest p) := by
  rfl

theorem structuredJoinerAssemblySource_rawTail_nonempty
    (p : AssemblySourceRestLiveTailEmitterParam) :
    exists head : Bool,
    exists rawTailRest : Word Bool,
      assemblySourceRestLiveTailEmitterRawTail p =
        head :: rawTailRest := by
  cases p with
  | mk w sourceRestBits stage =>
      simpa [assemblySourceRestLiveTailEmitterRawTail] using
        assemblySourceRestFinishRawTailBits_cons_exists
          sourceRestBits stage

theorem structuredJoinerAssemblySource_rawTail_append_singleton
    (p : AssemblySourceRestLiveTailEmitterParam) :
    exists rawTailInit : Word Bool,
    exists last : Bool,
      assemblySourceRestLiveTailEmitterRawTail p =
        List.append rawTailInit [last] := by
  rcases structuredJoinerAssemblySource_rawTail_nonempty p with
    ⟨head, rest, hraw⟩
  rcases exists_reverse_append_singleton_of_cons head rest with
    ⟨rawTailInit, last, htail⟩
  refine ⟨rawTailInit.reverse, last, ?_⟩
  simpa using hraw.trans htail

theorem structuredJoinerInitialConfig_eq_afterRawTailScanTape
    (state : Nat) (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Description.tapeAt
        (structuredMixedOptionCellQuoteLiveTailJoinerInitialConfig
          state p).tapes
        0 =
      MixedParserStackWholeSourceAfterRawTailScanTape
        p.w p.sourceRestBits p.stage := by
  rw [structuredJoinerInitialConfig_sourceTape]
  exact assemblySourceRestLiveTailJoinerSeparatedTape_eq_afterRawTailScanTape
    p

theorem structuredJoinerInitialConfig_moveRight_eq_rightEndCompactionSource
    (state : Nat) (p : AssemblySourceRestLiveTailEmitterParam)
    (head : Bool) (rawTailRest : Word Bool)
    (hraw :
      assemblySourceRestLiveTailEmitterRawTail p = head :: rawTailRest) :
    Tape.move Direction.right
        (Structured.Description.tapeAt
          (structuredMixedOptionCellQuoteLiveTailJoinerInitialConfig
            state p).tapes
          0) =
      CommonGround.FiniteTransducers.rightEndCompactionSourceTapeWithRightPadding
        (structuredMixedOptionCellQuoteLiveTailJoinerCompactionLeftCells
          p.w p.sourceRestBits p.stage head rawTailRest)
        (structuredMixedOptionCellQuoteLiveTailJoinerCompactionRightPadding
          p.sourceRestBits) := by
  cases p with
  | mk w sourceRestBits stage =>
      simpa [structuredJoinerInitialConfig_eq_afterRawTailScanTape,
        assemblySourceRestLiveTailEmitterRawTail,
        structuredMixedOptionCellQuoteLiveTailJoinerCompactionLeftCells,
        structuredMixedOptionCellQuoteLiveTailJoinerCompactionRightPadding]
        using
          MixedParserStackWholeSourceAfterRawTailScanTape_move_right_eq_rightEndSource
            w sourceRestBits stage head rawTailRest hraw

theorem structuredJoinerInitialConfig_moveRightRight_sourceRestCons
    (state : Nat) (w sourceRestTail : Word Bool)
    (bit : Bool) (stage : Nat) :
    exists rawTailInit : Word Bool,
    exists last : Bool,
      assemblySourceRestFinishRawTailBits (bit :: sourceRestTail) stage =
        List.append rawTailInit [last] ∧
      Tape.move Direction.right
          (Tape.move Direction.right
            (Structured.Description.tapeAt
              (structuredMixedOptionCellQuoteLiveTailJoinerInitialConfig
                state
                { w := w, sourceRestBits := bit :: sourceRestTail,
                  stage := stage }).tapes
              0)) =
        tapeAtCells
          (none :: some last ::
            List.append (rawTailInit.reverse.map some)
              ((assemblySourceRestFinishPrefixQuoteOutputBits
                w (bit :: sourceRestTail) stage).reverse.map some))
          (some false :: some true :: some bit ::
            some (if bit then false else true) ::
              List.append
                ((preservingCellPassCellBits sourceRestTail).map some)
                [none]) := by
  rw [structuredJoinerInitialConfig_sourceTape]
  simpa [assemblySourceRestLiveTailEmitterEmittedPrefix,
    assemblySourceRestLiveTailEmitterRawTail,
    assemblySourceRestLiveTailEmitterQuoteRest] using
    mixedOptionCellQuoteLiveTailSeparatedTape_move_right_right_assembly_sourceRestCons
      w sourceRestTail bit stage

theorem structuredJoinerInitialConfig_moveRight_eq_gapPayloadScanSource_sourceRestCons
    (state : Nat) (w sourceRestTail : Word Bool)
    (bit : Bool) (stage : Nat) :
    exists rawTailInit : Word Bool,
    exists last : Bool,
      assemblySourceRestFinishRawTailBits (bit :: sourceRestTail) stage =
        List.append rawTailInit [last] ∧
      Tape.move Direction.right
          (Structured.Description.tapeAt
            (structuredMixedOptionCellQuoteLiveTailJoinerInitialConfig
              state
              { w := w, sourceRestBits := bit :: sourceRestTail,
                stage := stage }).tapes
            0) =
        CommonGround.FiniteTransducers.rightBlankGapPayloadScanSourceTape
          (some last ::
            List.append (rawTailInit.reverse.map some)
              ((assemblySourceRestFinishPrefixQuoteOutputBits
                w (bit :: sourceRestTail) stage).reverse.map some))
          1
          false
          (true :: bit :: (if bit then false else true) ::
            preservingCellPassCellBits sourceRestTail)
          [] := by
  rcases assemblySourceRestFinishRawTailBits_lastSplit_exists
      (bit :: sourceRestTail) stage with
    ⟨rawTailInit, last, hraw⟩
  refine ⟨rawTailInit, last, hraw, ?_⟩
  rw [structuredJoinerInitialConfig_sourceTape]
  rw [assemblySourceRestLiveTailEmitterEmittedPrefix,
    assemblySourceRestLiveTailEmitterRawTail,
    assemblySourceRestLiveTailEmitterQuoteRest]
  rw [hraw]
  rw [mixedOptionCellQuoteLiveTailSeparatedTape_move_right_rawTailLast]
  cases bit <;>
    simp [CommonGround.FiniteTransducers.rightBlankGapPayloadScanSourceTape,
      DovetailInitialLayoutInitializer.tapeAtCells,
      CommonGround.FiniteTransducers.tapeAtCells,
      preservingCellPassCellBits, preservingCellPassZeroBits,
      preservingCellPassOneBits, List.replicate_succ]

theorem structuredJoinerQuoteRestPayload_lastSplit_sourceRestCons
    (sourceRestTail : Word Bool) (bit : Bool) :
    exists payloadPref : Word Bool,
    exists payloadLast : Bool,
      false :: true :: bit :: (if bit then false else true) ::
          preservingCellPassCellBits sourceRestTail =
        List.append payloadPref [payloadLast] := by
  rcases exists_reverse_append_singleton_of_cons false
      (true :: bit :: (if bit then false else true) ::
        preservingCellPassCellBits sourceRestTail) with
    ⟨payloadRev, payloadLast, hpayload⟩
  exact ⟨payloadRev.reverse, payloadLast, hpayload⟩

theorem structuredJoinerGapPayloadScanTarget_moveRight_eq_sentinelSource_sourceRestCons
    (baseTail : List (Option Bool)) (rawLast : Bool)
    (sourceRestTail payloadPref : Word Bool)
    (bit payloadLast : Bool)
    (hpayload :
      false :: true :: bit :: (if bit then false else true) ::
          preservingCellPassCellBits sourceRestTail =
        List.append payloadPref [payloadLast]) :
    Tape.move Direction.right
        (CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape
          (some rawLast :: baseTail)
          1
          false
          (true :: bit :: (if bit then false else true) ::
            preservingCellPassCellBits sourceRestTail)
          []) =
      CommonGround.FiniteTransducers.rightBlankLocalGapCompactorSourceTapeWithBaseAndRight
        (some rawLast :: baseTail)
        payloadLast
        payloadPref.reverse
        0
        [] := by
  simpa [CommonGround.FiniteTransducers.rightBlankLocalGapBaseLeft] using
    CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape_move_right_eq_localGapSource
      (some rawLast :: baseTail)
      0
      false
      payloadLast
      (true :: bit :: (if bit then false else true) ::
        preservingCellPassCellBits sourceRestTail)
      payloadPref
      []
      hpayload

theorem structuredLiftedSentinelGapCompactorDescription_run_from_scanTarget_sourceRestCons
    (baseTail : List (Option Bool)) (rawLast : Bool)
    (sourceRestTail payloadPref : Word Bool)
    (bit payloadLast : Bool)
    (hpayload :
      false :: true :: bit :: (if bit then false else true) ::
          preservingCellPassCellBits sourceRestTail =
        List.append payloadPref [payloadLast])
    (scratch work : Tape Bool) :
    exists n : Nat,
      structuredLiftedSentinelGapCompactorDescription.runConfig n
          (Structured.MultiTapeLowering.ThreeTape.config
            CommonGround.FiniteTransducers.sentinelGapCompactorDescription.start
            (Tape.move Direction.right
              (CommonGround.FiniteTransducers.rightBlankGapPayloadScanTargetTape
                (some rawLast :: baseTail)
                1
                false
                (true :: bit :: (if bit then false else true) ::
                  preservingCellPassCellBits sourceRestTail)
                []))
            scratch work) =
        Structured.MultiTapeLowering.ThreeTape.config
          CommonGround.FiniteTransducers.sentinelGapCompactorDescription.halt
          (CommonGround.FiniteTransducers.leadingBlankLeftShiftTargetTapeWithPadding
            (some rawLast :: baseTail)
            (payloadLast :: payloadPref.reverse).reverse
            [])
          scratch work := by
  rcases
      structuredLiftedSentinelGapCompactorDescription_run_final_pass
        baseTail rawLast payloadLast payloadPref.reverse 0 []
        scratch work with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [
    structuredJoinerGapPayloadScanTarget_moveRight_eq_sentinelSource_sourceRestCons
      baseTail rawLast sourceRestTail payloadPref bit payloadLast hpayload]
  simpa using hn

theorem structuredJoinerEntryDescription_run_initial_sourceRestCons
    (w sourceRestTail : Word Bool) (bit : Bool) (stage : Nat) :
    exists rawTailInit : Word Bool,
    exists last : Bool,
      assemblySourceRestFinishRawTailBits (bit :: sourceRestTail) stage =
        List.append rawTailInit [last] ∧
      structuredJoinerEntryDescription.runConfig 2
          (structuredMixedOptionCellQuoteLiveTailJoinerInitialConfig
            structuredJoinerEntryStart
            { w := w, sourceRestBits := bit :: sourceRestTail,
              stage := stage }) =
        Structured.MultiTapeLowering.ThreeTape.config
          structuredJoinerEntryHalt
          (tapeAtCells
            (none :: some last ::
              List.append (rawTailInit.reverse.map some)
                ((assemblySourceRestFinishPrefixQuoteOutputBits
                  w (bit :: sourceRestTail) stage).reverse.map some))
            (some false :: some true :: some bit ::
              some (if bit then false else true) ::
                List.append
                  ((preservingCellPassCellBits sourceRestTail).map some)
                  [none]))
          structuredMixedOptionCellQuoteLiveTailJoinerScratchTape
          structuredMixedOptionCellQuoteLiveTailJoinerWorkTape := by
  rcases structuredJoinerInitialConfig_moveRightRight_sourceRestCons
      structuredJoinerEntryStart w sourceRestTail bit stage with
    ⟨rawTailInit, last, hraw, hmove⟩
  refine ⟨rawTailInit, last, hraw, ?_⟩
  rw [structuredMixedOptionCellQuoteLiveTailJoinerInitialConfig]
  rw [structuredJoinerEntryDescription_run_two]
  exact congrArg
    (fun source =>
      Structured.MultiTapeLowering.ThreeTape.config
        structuredJoinerEntryHalt source
        structuredMixedOptionCellQuoteLiveTailJoinerScratchTape
        structuredMixedOptionCellQuoteLiveTailJoinerWorkTape)
    hmove

theorem structuredQuoteRestCopyDescription_run_entryTape_sourceRestCons
    (w sourceRestTail rawTailInit : Word Bool)
    (bit last : Bool) (stage : Nat) (work : Tape Bool) :
    structuredQuoteRestCopyDescription.runConfig
        ((false :: true :: bit :: (if bit then false else true) ::
            preservingCellPassCellBits sourceRestTail).length + 1)
        (Structured.MultiTapeLowering.ThreeTape.config
          structuredQuoteRestCopyStart
          (tapeAtCells
            (none :: some last ::
              List.append (rawTailInit.reverse.map some)
                ((assemblySourceRestFinishPrefixQuoteOutputBits
                  w (bit :: sourceRestTail) stage).reverse.map some))
            (some false :: some true :: some bit ::
              some (if bit then false else true) ::
                List.append
                  ((preservingCellPassCellBits sourceRestTail).map some)
                  [none]))
          (Structured.MultiTapeLowering.ThreeTape.outputFromBits [])
          work) =
      Structured.MultiTapeLowering.ThreeTape.config
        structuredQuoteRestCopyHalt
        (tapeAtCells
          (List.append
            ((false :: true :: bit :: (if bit then false else true) ::
              preservingCellPassCellBits sourceRestTail).reverse.map some)
            (none :: some last ::
              List.append (rawTailInit.reverse.map some)
                ((assemblySourceRestFinishPrefixQuoteOutputBits
                  w (bit :: sourceRestTail) stage).reverse.map some)))
          [none])
        (Structured.MultiTapeLowering.ThreeTape.outputFromBits
          (false :: true :: bit :: (if bit then false else true) ::
            preservingCellPassCellBits sourceRestTail))
        work := by
  simpa using
    structuredQuoteRestCopyDescription_run
      (false :: true :: bit :: (if bit then false else true) ::
        preservingCellPassCellBits sourceRestTail)
      (none :: some last ::
        List.append (rawTailInit.reverse.map some)
          ((assemblySourceRestFinishPrefixQuoteOutputBits
            w (bit :: sourceRestTail) stage).reverse.map some))
      work

theorem structuredJoinerInitialConfig_moveRight_sourceRestNil
    (state : Nat) (w : Word Bool) (stage : Nat) :
    exists rawTailInit : Word Bool,
    exists last : Bool,
      assemblySourceRestFinishRawTailBits [] stage =
        List.append rawTailInit [last] ∧
      Tape.move Direction.right
          (Structured.Description.tapeAt
            (structuredMixedOptionCellQuoteLiveTailJoinerInitialConfig
              state
              { w := w, sourceRestBits := [], stage := stage }).tapes
            0) =
        tapeAtCells
          (some last ::
            List.append (rawTailInit.reverse.map some)
              ((assemblySourceRestFinishPrefixQuoteOutputBits
                w [] stage).reverse.map some))
          (none ::
            List.append ((preservingCellPassCellBits []).map some)
              [none]) := by
  rcases assemblySourceRestFinishRawTailBits_lastSplit_exists
      ([] : Word Bool) stage with
    ⟨rawTailInit, last, hraw⟩
  refine ⟨rawTailInit, last, hraw, ?_⟩
  rw [structuredJoinerInitialConfig_sourceTape]
  rw [assemblySourceRestLiveTailEmitterEmittedPrefix,
    assemblySourceRestLiveTailEmitterRawTail,
    assemblySourceRestLiveTailEmitterQuoteRest]
  rw [hraw]
  exact
    mixedOptionCellQuoteLiveTailSeparatedTape_move_right_rawTailLast
      (assemblySourceRestFinishPrefixQuoteOutputBits w [] stage)
      rawTailInit (preservingCellPassCellBits []) last

theorem structuredJoinerFinalConfig_eq_targetTape
    (state : Nat) (p : AssemblySourceRestLiveTailEmitterParam) :
    Structured.Description.tapeAt
        (structuredMixedOptionCellQuoteLiveTailJoinerFinalConfig
          state p).tapes
        0 =
      assemblySourceRestFinishTargetTape
        p.w p.sourceRestBits p.stage := by
  rw [structuredJoinerFinalConfig_sourceTape]
  exact assemblySourceRestLiveTailJoinerJoinedTape_eq_targetTape p

theorem structuredJoinerFinalConfig_eq_assembly_stageSplit
    (state : Nat) (w sourceRestBits : Word Bool) (stage : Nat) :
    Structured.Description.tapeAt
        (structuredMixedOptionCellQuoteLiveTailJoinerFinalConfig
          state
          { w := w, sourceRestBits := sourceRestBits, stage := stage }).tapes
        0 =
      tapeAtCells
        ((List.append
          (assemblySourceRestFinishPrefixQuoteOutputBits
            w sourceRestBits stage)
          (preservingCellPassCellBits sourceRestBits)).reverse.map some)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)
          (sourceRestBits.map some)) := by
  rw [structuredJoinerFinalConfig_sourceTape]
  simpa [assemblySourceRestLiveTailEmitterEmittedPrefix,
    assemblySourceRestLiveTailEmitterRawTail,
    assemblySourceRestLiveTailEmitterQuoteRest] using
    mixedOptionCellQuoteLiveTailJoinedTape_eq_assembly_stageSplit
      w sourceRestBits stage

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
