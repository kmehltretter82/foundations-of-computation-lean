import FoC.Computability.Compiler.ClosedCfg.QuoteRest.LTJoinerRuns
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.GapPayloadLocalCompactor
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.SentinelGapCompactor
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeHelpers
import FoC.Computability.Compiler.Structured.Lowering.ThreeTapeTactic
import FoC.Computability.Compiler.Structured.Lowering.RawTailInsertion

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

namespace EncRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

def structuredHeadMoveOfDirection : Direction -> Structured.HeadMove
  | Direction.left => Structured.HeadMove.left
  | Direction.right => Structured.HeadMove.right

def structuredActionOfTransition
    (t : TransitionDescription) : Structured.TapeAction :=
  Structured.TapeAction.writeMove t.write
    (structuredHeadMoveOfDirection t.move)

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

def structuredRowsForSourceRead
    (source : Nat) (sourceRead : Option Bool)
    (action0 action1 action2 : Structured.TapeAction)
    (target : Nat) : List Structured.Transition :=
  Structured.MultiTapeLowering.ThreeTape.allReads2
    (fun read1 read2 =>
      Structured.MultiTapeLowering.ThreeTape.row
        source sourceRead read1 read2
        action0 action1 action2 target)

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

def structuredMixedOptionCellQuoteLiveTailJoinerScratchTape :
    Tape Bool :=
  Structured.MultiTapeLowering.ThreeTape.outputFromBits []

def structuredMixedOptionCellQuoteLiveTailJoinerWorkTape :
    Tape Bool :=
  Structured.MultiTapeLowering.ThreeTape.outputFromBits []


end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
