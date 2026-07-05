import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.SourceRestFinishCore.LiveTail.JoinerRuns
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.ThreeTapeHelpers
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.StructuredMultiTapeLowering.ThreeTapeTactic

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
  rcases hrow with hrow | hrow
  · exact
      Structured.MultiTapeLowering.ThreeTape.allReadRows3_supportsReadWriteRow3
        structuredJoinerEntryStart structuredJoinerEntrySeparator
        Structured.MultiTapeLowering.ThreeTape.keepR
        Structured.MultiTapeLowering.ThreeTape.keepS
        Structured.MultiTapeLowering.ThreeTape.keepS
        row hrow
  · exact
      Structured.MultiTapeLowering.ThreeTape.allReadRows3_supportsReadWriteRow3
        structuredJoinerEntrySeparator structuredJoinerEntryHalt
        Structured.MultiTapeLowering.ThreeTape.keepR
        Structured.MultiTapeLowering.ThreeTape.keepS
        Structured.MultiTapeLowering.ThreeTape.keepS
        row hrow

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
  three_tape_step

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
  three_tape_step

theorem structuredJoinerEntryDescription_run_two
    (source scratch work : Tape Bool) :
    structuredJoinerEntryDescription.runConfig 2
        (Structured.MultiTapeLowering.ThreeTape.config
          structuredJoinerEntryStart source scratch work) =
      Structured.MultiTapeLowering.ThreeTape.config
        structuredJoinerEntryHalt
        (Tape.move Direction.right (Tape.move Direction.right source))
        scratch work := by
  simp [Structured.Description.runConfig,
    structuredJoinerEntryDescription_step_start,
    structuredJoinerEntryDescription_step_separator]

def structuredMixedOptionCellQuoteLiveTailJoinerScratchTape :
    Tape Bool :=
  Structured.MultiTapeLowering.ThreeTape.outputFromBits []

def structuredMixedOptionCellQuoteLiveTailJoinerWorkTape :
    Tape Bool :=
  Structured.MultiTapeLowering.ThreeTape.outputFromBits []

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
