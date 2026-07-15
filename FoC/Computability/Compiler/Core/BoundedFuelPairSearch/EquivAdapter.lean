import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.CandidateAttemptLoop
import FoC.Computability.Compiler.Core.BoundedFuelPairSearch.LoweredInversion
import FoC.Computability.Compiler.Core.StructuredConstructionTargets.BoundedFuelPairSearch
import FoC.Computability.Compiler.Structured.HeadRoutes.Tape2Projector.Runs

namespace FoC
namespace Computability

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace BoundedFuelPairSearch
namespace U12EquivAdapter

open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.Tape2Projector

/-- Fixed-output closeout after the generic tape-0/tape-1 prefix eraser.
State 0 erases the contiguous logical tape-2 code and steps one blank farther
right. State 1 rewinds over the erased region to the retained sentinel, writes
the fixed Boolean there, and halts one cell to its right. -/
def closeoutDescription (b : Bool) : MachineDescription where
  stateCount := 3
  start := 0
  halt := 2
  transitions :=
    [ transition 0 (some false) none Direction.right 0
    , transition 0 (some true) none Direction.right 0
    , transition 0 none none Direction.right 1
    , transition 1 none none Direction.left 1
    , transition 1 (some false) (some b) Direction.right 2
    , transition 1 (some true) (some b) Direction.right 2 ]

theorem closeoutDescription_subroutineReady (b : Bool) :
    (closeoutDescription b).SubroutineReady := by
  apply machineDescription_subroutineReady_of_transition_checks
  all_goals cases b <;> decide

private theorem replicate_none_append_none_cons
    (n : Nat) (tail : List (Option Bool)) :
    List.append (List.replicate n (none : Option Bool))
        (none :: tail) =
      List.append (List.replicate (n + 1) (none : Option Bool)) tail := by
  exact list_replicate_append_self (none : Option Bool) n tail

theorem closeoutDescription_step_bit_tapeAtCells
    (b bit : Bool) (left right : List (Option Bool)) :
    (closeoutDescription b).runConfig 1
        { state := 0
          tape := tapeAtCells left (some bit :: right) } =
      { state := 0
        tape := tapeAtCells (none :: left) right } := by
  cases b <;> cases bit <;> cases right <;>
    simp [closeoutDescription, tapeAtCells, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

theorem closeoutDescription_run_eraseRight
    (b : Bool) (bits : List Bool)
    (left right : List (Option Bool)) :
    (closeoutDescription b).runConfig bits.length
        { state := 0
          tape := tapeAtCells left
            (List.append (bits.map some) (none :: right)) } =
      { state := 0
        tape := tapeAtCells
          (List.append
            (List.replicate bits.length (none : Option Bool)) left)
          (none :: right) } := by
  induction bits generalizing left with
  | nil => rfl
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by simp; lia]
      rw [runConfig_add]
      rw [show
        List.append ((bit :: rest).map some) (none :: right) =
          some bit :: List.append (rest.map some) (none :: right) by simp]
      rw [closeoutDescription_step_bit_tapeAtCells]
      rw [ih (none :: left)]
      rw [show 1 + rest.length = rest.length + 1 by lia]
      rw [← replicate_none_append_none_cons]

theorem closeoutDescription_run_seekSentinel
    (b : Bool) (padding : Nat) (anchor : Bool)
    (left right : List (Option Bool)) :
    (closeoutDescription b).runConfig (padding + 1)
        { state := 1
          tape := tapeAtCells
            (List.append
              (List.replicate padding (none : Option Bool))
              (some anchor :: left))
            (none :: right) } =
      { state := 1
        tape := tapeAtCells left
          (some anchor ::
            List.append
              (List.replicate (padding + 1) (none : Option Bool)) right) } := by
  induction padding generalizing right with
  | zero =>
      cases b <;> cases anchor <;> cases left <;> cases right <;>
        simp [closeoutDescription, runConfig, stepConfig,
          lookupTransition, Matches, transition, tapeAtCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft,
          List.replicate_succ]
  | succ padding ih =>
      rw [show Nat.succ padding + 1 = 1 + (padding + 1) by lia]
      rw [runConfig_add]
      have hstep :
          (closeoutDescription b).runConfig 1
              { state := 1
                tape := tapeAtCells
                  (List.append
                    (List.replicate (Nat.succ padding)
                      (none : Option Bool))
                    (some anchor :: left))
                  (none :: right) } =
            { state := 1
              tape := tapeAtCells
                (List.append
                  (List.replicate padding (none : Option Bool))
                  (some anchor :: left))
                (none :: none :: right) } := by
        cases b <;> cases anchor <;> cases left <;> cases right <;>
          simp [closeoutDescription, runConfig, stepConfig,
            lookupTransition, Matches, transition, tapeAtCells,
            Tape.read, Tape.write, Tape.move, Tape.moveLeft,
            List.replicate_succ]
      rw [hstep]
      rw [ih (none :: right)]
      have hright :
          List.append
              (List.replicate (padding + 1) (none : Option Bool))
              (none :: right) =
            List.append
              (List.replicate (Nat.succ padding + 1)
                (none : Option Bool)) right := by
        rw [replicate_none_append_none_cons]
      rw [hright]
      rw [show Nat.succ padding + 1 = 1 + (padding + 1) by lia]

theorem closeoutDescription_step_blank_tapeAtCells
    (b : Bool) (left : List (Option Bool)) :
    (closeoutDescription b).runConfig 1
        { state := 0
          tape := tapeAtCells left [none] } =
      { state := 1
        tape := tapeAtCells (none :: left) [none] } := by
  cases b <;>
    simp [closeoutDescription, tapeAtCells, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

theorem closeoutDescription_step_anchor_tapeAtCells
    (b anchor : Bool) (right : List (Option Bool)) :
    (closeoutDescription b).runConfig 1
        { state := 1
          tape := tapeAtCells [] (some anchor :: none :: right) } =
      { state := 2
        tape := tapeAtCells [some b] (none :: right) } := by
  cases b <;> cases anchor <;> cases right <;>
    simp [closeoutDescription, tapeAtCells, runConfig, stepConfig,
      lookupTransition, Matches, transition, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]

private theorem replicate_none_append_replicate_none_tail
    (leftLength rightLength : Nat) (tail : List (Option Bool)) :
    List.append
        (List.replicate leftLength (none : Option Bool))
        (List.append
          (List.replicate rightLength (none : Option Bool)) tail) =
      List.append
        (List.replicate (leftLength + rightLength) (none : Option Bool))
        tail := by
  induction leftLength with
  | zero => simp
  | succ leftLength ih =>
      rw [List.replicate_succ]
      change none ::
          List.append
            (List.replicate leftLength (none : Option Bool))
            (List.append
              (List.replicate rightLength (none : Option Bool)) tail) =
        List.append
          (List.replicate (Nat.succ leftLength + rightLength)
            (none : Option Bool)) tail
      rw [ih]
      rw [show Nat.succ leftLength + rightLength =
        (leftLength + rightLength) + 1 by lia]
      rw [List.replicate_succ]
      rfl

def closeoutPadding
    (tape0Bits tape1Bits tape2Bits : List Bool) : Nat :=
  tape2Bits.length + (tape0Bits.length + tape1Bits.length + 2) + 1

def closeoutTargetTape
    (b : Bool) (padding : Nat) : Tape Bool :=
  tapeAtCells [some b]
    (List.replicate (padding + 1) (none : Option Bool))

theorem closeoutDescription_run_prefixTargetTape
    (b : Bool) (tape0Bits tape1Bits tape2Bits : List Bool) :
    (closeoutDescription b).runConfig
        (tape2Bits.length + 1 +
          (closeoutPadding tape0Bits tape1Bits tape2Bits + 1) + 1)
        { state := (closeoutDescription b).start
          tape := prefixTargetTape tape0Bits tape1Bits tape2Bits } =
      { state := (closeoutDescription b).halt
        tape := closeoutTargetTape b
          (closeoutPadding tape0Bits tape1Bits tape2Bits) } := by
  rw [show tape2Bits.length + 1 +
      (closeoutPadding tape0Bits tape1Bits tape2Bits + 1) + 1 =
    tape2Bits.length +
      (1 + ((closeoutPadding tape0Bits tape1Bits tape2Bits + 1) + 1)) by
    lia]
  rw [runConfig_add]
  unfold prefixTargetTape
  rw [show (closeoutDescription b).start = 0 by rfl]
  rw [closeoutDescription_run_eraseRight]
  rw [runConfig_add]
  rw [closeoutDescription_step_blank_tapeAtCells]
  have hleft :
      none ::
          List.append
            (List.replicate tape2Bits.length (none : Option Bool))
            (List.append
              (List.replicate
                (tape0Bits.length + tape1Bits.length + 2)
                (none : Option Bool))
              [some false]) =
        List.append
          (List.replicate
            (closeoutPadding tape0Bits tape1Bits tape2Bits)
            (none : Option Bool))
          [some false] := by
    rw [replicate_none_append_replicate_none_tail]
    unfold closeoutPadding
    rw [show tape2Bits.length +
        (tape0Bits.length + tape1Bits.length + 2) + 1 =
      (tape2Bits.length +
        (tape0Bits.length + tape1Bits.length + 2)) + 1 by lia]
    rw [List.replicate_succ]
    rfl
  rw [hleft]
  rw [runConfig_add]
  rw [closeoutDescription_run_seekSentinel]
  simp only [closeoutTargetTape, List.replicate_succ]
  rw [show
    List.append
        (none ::
          List.replicate
            (closeoutPadding tape0Bits tape1Bits tape2Bits)
            (none : Option Bool))
        [] =
      none ::
        List.replicate
          (closeoutPadding tape0Bits tape1Bits tape2Bits)
          (none : Option Bool) by
    exact List.append_nil _]
  change
    (closeoutDescription b).runConfig 1
        { state := 1
          tape := tapeAtCells []
            (some false :: none ::
              List.replicate
                (closeoutPadding tape0Bits tape1Bits tape2Bits)
                (none : Option Bool)) } =
      { state := 2
        tape := tapeAtCells [some b]
          (none ::
            List.replicate
              (closeoutPadding tape0Bits tape1Bits tape2Bits)
              (none : Option Bool)) }
  exact closeoutDescription_step_anchor_tapeAtCells b false _

theorem closeoutDescription_haltsFromTape_prefixTargetTape
    (b : Bool) (tape0Bits tape1Bits tape2Bits : List Bool) :
    (closeoutDescription b).HaltsFromTape
      (prefixTargetTape tape0Bits tape1Bits tape2Bits)
      (closeoutTargetTape b
        (closeoutPadding tape0Bits tape1Bits tape2Bits)) := by
  refine ⟨tape2Bits.length + 1 +
    (closeoutPadding tape0Bits tape1Bits tape2Bits + 1) + 1, ?_⟩
  constructor <;> rw [closeoutDescription_run_prefixTargetTape]

theorem closeoutTargetTape_equiv_rightShiftedInput
    (b : Bool) (padding : Nat) :
    Tape.Equiv (closeoutTargetTape b padding)
      (Tape.move Direction.right (Tape.input [b])) := by
  unfold closeoutTargetTape
  rw [show padding + 1 = Nat.succ padding by lia]
  rw [List.replicate_succ]
  cases b <;>
    simp [tapeAtCells, Tape.input, Tape.Equiv,
      Tape.move, Tape.moveRight,
      FoC.Computability.dropTrailingNone_replicate_none] <;> rfl

theorem closeoutDescription_haltsFromTapeEquiv_prefixTargetTape
    (b : Bool) (tape0Bits tape1Bits tape2Bits : List Bool) :
    (closeoutDescription b).HaltsFromTapeEquiv
      (prefixTargetTape tape0Bits tape1Bits tape2Bits)
      (Tape.move Direction.right (Tape.input [b])) := by
  exact
    ⟨closeoutTargetTape b
        (closeoutPadding tape0Bits tape1Bits tape2Bits),
      closeoutDescription_haltsFromTape_prefixTargetTape
        b tape0Bits tape1Bits tape2Bits,
      closeoutTargetTape_equiv_rightShiftedInput b _⟩

def fixedBoolCloseoutDescription (b : Bool) : MachineDescription :=
  canonicalPrimitiveSeqDescription prefixEraserDescription
    (closeoutDescription b)

theorem fixedBoolCloseoutDescription_subroutineReady (b : Bool) :
    (fixedBoolCloseoutDescription b).SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    prefixEraserDescription_subroutineReady
    (closeoutDescription_subroutineReady b)

theorem fixedBoolCloseoutDescription_haltsFrom_encodedGuardedStructured3Tapes
    (b : Bool) (T0 T1 T2 : Tape Bool) :
    (fixedBoolCloseoutDescription b).HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 T1 T2)
      (Tape.move Direction.right (Tape.input [b])) := by
  apply canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    prefixEraserDescription_subroutineReady
    (closeoutDescription_subroutineReady b)
  · exact MachineDescription.HaltsFromTape.toEquiv
      (prefixEraserDescription_haltsFrom_encodedGuardedStructured3Tapes
        T0 T1 T2)
  · exact closeoutDescription_haltsFromTapeEquiv_prefixTargetTape b _ _ _

section MasterDivergence

open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open StructuredConstructionTargets
open StructuredConstructionTargets.FusedLayoutEmission
open StructuredConstructionTargets.RawLayoutPreparation
open StructuredConstructionTargets.FuelSimulatorCore
open StructuredConstructionTargets.FuelSimulatorCore.RawLayoutEmission
open U12CandidateAttemptLoop
open U12MasterLoop

variable
    (source sourceSimulator recognizer checkerSimulator : MachineDescription)
    (b : Bool)
    (hsourceSimulator :
      FixedDescriptionBoundedSimulatorEquivSpec source sourceSimulator)
    (hcheckerSimulator :
      SuccessOnlyFairBoundedWrapperSpec recognizer checkerSimulator)

local notation "M" =>
  U12MasterLoop.table source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator.left hcheckerSimulator.left

theorem sourceEmit_seekRawEnd_stepConfig_ne_none
    (T0 T1 T2 : Tape Bool) :
    (M).description.stepConfig
        ((M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          T0 T1 T2) ≠ none := by
  have hmem := U12MasterLoop.sourceEmit_mem
    source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator.left hcheckerSimulator.left
    (Sum.inl RawLayoutPreparation.State.seekRawEnd)
    (fusedTable source.start).start_mem
  unfold TypedStateTable.config
  rw [(M).stepConfig_config hmem]
  cases hread : Tape.read T2 with
  | none =>
      simp [U12MasterLoop.table, U12MasterLoop.next,
        fusedTable, TypedStateTable.ofList, fusedNext,
        RawLayoutPreparation.next] <;> intro h <;> cases h
  | some bit =>
      cases bit <;>
        simp [U12MasterLoop.table, U12MasterLoop.next,
          fusedTable, TypedStateTable.ofList, fusedNext,
          RawLayoutPreparation.next] <;> intro h <;> cases h

/-- Under failure of the semantic evidence proposition, the initialized
master trajectory cannot stall. A putative stall at time k would freeze
every later run, while k + 1 complete false candidates reach the always
defined source-emission entry after at least k + 1 concrete steps. -/
theorem initialized_stepConfig_ne_none_of_no_evidence
    (hrecognizer : FixedBoolSimulatorLayoutRecognizerSpec source recognizer b)
    (raw : List Bool)
    (hnoEvidence :
      ¬ PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence
          source (show Word Bool from raw) b) :
    forall k : Nat,
      (M).description.stepConfig
        ((M).description.runConfig k
          ((M).config (.bootstrap U12ZeroBootstrap.State.lengthScan)
            (Tape.input (show Word Bool from raw)) Tape.blank Tape.blank)) ≠
        none := by
  intro k hstuck
  let input : Word Bool := show Word Bool from raw
  let origin := SuccessOnlyDiagonalCursor.initial
  let bootstrap0 := U12ZeroBootstrap.bootstrapFuelTape (raw.length + 2)
  let bootstrap1 := U12ZeroBootstrap.bootstrapFuelTape 1
  let bootstrap2 := U12ZeroBootstrap.bootstrapCandidateTape raw
  let startConfig :=
    (M).config (.bootstrap U12ZeroBootstrap.State.lengthScan)
      (Tape.input input) Tape.blank Tape.blank
  have hbootstrap := U12MasterLoop.leads_bootstrap
    source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator.left hcheckerSimulator.left raw
  rcases hbootstrap.to_runConfig with ⟨bootstrapSteps, hbootstrapRun⟩
  have horigin := U12ZeroBootstrap.exact_bootstrap_persistentOrigin raw
  have hfalse : forall j : Nat, j < k + 1 ->
      (successOnlyCheckerRunLayout recognizer source input
        (SuccessOnlyDiagonalCursor.advanceN j origin).limit
        (SuccessOnlyDiagonalCursor.advanceN j origin).candidateFuel
        (SuccessOnlyDiagonalCursor.advanceN j origin).sourceFuel
        (SuccessOnlyDiagonalCursor.advanceN j origin).checkerFuel).hit =
          false := by
    intro j _hj
    exact U12CandidateAttemptLoop.hit_eq_false_of_no_evidence
      source recognizer b hrecognizer input hnoEvidence
      (SuccessOnlyDiagonalCursor.advanceN j origin)
  rcases U12CandidateAttemptLoop.falseCandidates_advanceN_boundedRun
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator input (k + 1) origin
      bootstrap0 bootstrap1 bootstrap2 hfalse
      (by simpa [origin, bootstrap0, SuccessOnlyDiagonalCursor.initial]
        using horigin.1)
      (by simpa [origin, bootstrap1, SuccessOnlyDiagonalCursor.initial]
        using horigin.2.1)
      (by simpa [origin, bootstrap2, SuccessOnlyDiagonalCursor.initial]
        using horigin.2.2) with
    ⟨A0, A1, A2, loopSteps, hloopBound, hloopRun,
      _hA0, _hA1, _hA2⟩
  let totalSteps := bootstrapSteps + loopSteps
  have htotalBound : k < totalSteps := by
    simp [totalSteps]
    lia
  have htotalRun :
      (M).description.runConfig totalSteps startConfig =
        (M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          A0 A1 A2 := by
    unfold totalSteps
    rw [Description.runConfig_add]
    rw [show
      (M).description.runConfig bootstrapSteps startConfig =
        (M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          bootstrap0 bootstrap1 bootstrap2 by
      simpa [startConfig, input, bootstrap0, bootstrap1, bootstrap2]
        using hbootstrapRun]
    exact hloopRun
  have hkLe : k ≤ totalSteps := Nat.le_of_lt htotalBound
  have hsplit : k + (totalSteps - k) = totalSteps :=
    Nat.add_sub_of_le hkLe
  have hstable :
      (M).description.runConfig totalSteps startConfig =
        (M).description.runConfig k startConfig := by
    calc
      (M).description.runConfig totalSteps startConfig =
          (M).description.runConfig (totalSteps - k)
            ((M).description.runConfig k startConfig) := by
        rw [← Description.runConfig_add, hsplit]
      _ = (M).description.runConfig k startConfig :=
        Description.runConfig_of_stepConfig_none
          (by simpa [startConfig, input] using hstuck) _
  have hendpointEq :
      (M).config
          (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
          A0 A1 A2 =
        (M).description.runConfig k startConfig := by
    exact htotalRun.symm.trans hstable
  have hendpointStuck :
      (M).description.stepConfig
          ((M).config
            (.sourceEmit (Sum.inl RawLayoutPreparation.State.seekRawEnd))
            A0 A1 A2) = none := by
    rw [hendpointEq]
    simpa [startConfig, input] using hstuck
  exact
    (sourceEmit_seekRawEnd_stepConfig_ne_none
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator A0 A1 A2) hendpointStuck

theorem stepConfig_runConfig_ne_none_of_haltsFromConfig
    {D : Description}
    (hDhtf : D.HaltTransitionFree)
    {c : CommonGround.FiniteTransducers.Structured.Configuration}
    (hhalts : D.HaltsFromConfig c) :
    forall k : Nat,
      (D.runConfig k c).state ≠ D.halt ->
        D.stepConfig (D.runConfig k c) ≠ none := by
  rcases hhalts with ⟨haltSteps, hhalt⟩
  intro k hkState hstuck
  by_cases hkLe : k ≤ haltSteps
  · have hsplit : k + (haltSteps - k) = haltSteps :=
      Nat.add_sub_of_le hkLe
    have hstable : D.runConfig haltSteps c = D.runConfig k c := by
      calc
        D.runConfig haltSteps c =
            D.runConfig (haltSteps - k) (D.runConfig k c) := by
          rw [← Description.runConfig_add, hsplit]
        _ = D.runConfig k c :=
          Description.runConfig_of_stepConfig_none hstuck _
    apply hkState
    rw [← hstable]
    exact hhalt
  · have hhaltLe : haltSteps ≤ k := by lia
    have hsplit : haltSteps + (k - haltSteps) = k :=
      Nat.add_sub_of_le hhaltLe
    have hstable : D.runConfig k c = D.runConfig haltSteps c := by
      calc
        D.runConfig k c =
            D.runConfig (k - haltSteps) (D.runConfig haltSteps c) := by
          rw [← Description.runConfig_add, hsplit]
        _ = D.runConfig haltSteps c :=
          Description.runConfig_halt hDhtf
            (D.runConfig haltSteps c) hhalt _
    apply hkState
    rw [hstable]
    exact hhalt

/-- The initialized master trajectory is defined at every nonhalt point.
If evidence exists, its already-constructed logical run reaches halt and
determinism rules out a prior stall. If evidence does not exist, the
quantitative false-candidate argument supplies arbitrarily late defined
source-emission endpoints. -/
theorem initialized_stepConfig_ne_none_of_ne_halt
    (hrecognizer : FixedBoolSimulatorLayoutRecognizerSpec source recognizer b)
    (raw : List Bool) :
    forall k : Nat,
      ((M).description.runConfig k
          ((M).config (.bootstrap U12ZeroBootstrap.State.lengthScan)
            (Tape.input (show Word Bool from raw)) Tape.blank Tape.blank)).state ≠
          (M).description.halt ->
        (M).description.stepConfig
          ((M).description.runConfig k
            ((M).config (.bootstrap U12ZeroBootstrap.State.lengthScan)
              (Tape.input (show Word Bool from raw)) Tape.blank Tape.blank)) ≠
          none := by
  classical
  by_cases hevidence :
      PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence
        source (show Word Bool from raw) b
  · rcases U12CandidateAttemptLoop.leads_initialized_of_evidence
        source sourceSimulator recognizer checkerSimulator b
        hsourceSimulator hcheckerSimulator hrecognizer raw hevidence with
      ⟨A0, A1, A2, hforward, _hA2⟩
    rcases hforward.to_runConfig with ⟨haltSteps, hhaltRun⟩
    have hhalts : (M).description.HaltsFromConfig
        ((M).config (.bootstrap U12ZeroBootstrap.State.lengthScan)
          (Tape.input (show Word Bool from raw)) Tape.blank Tape.blank) := by
      refine ⟨haltSteps, ?_⟩
      change
        ((M).description.runConfig haltSteps
          ((M).config (.bootstrap U12ZeroBootstrap.State.lengthScan)
            (Tape.input (show Word Bool from raw)) Tape.blank Tape.blank)).state =
          (M).description.halt
      have hstate := congrArg
        (fun c : CommonGround.FiniteTransducers.Structured.Configuration =>
          c.state) hhaltRun
      rw [show (M).description.halt =
        (M).stateId U12MasterLoop.State.halt by rfl]
      simpa [TypedStateTable.config] using hstate
    exact stepConfig_runConfig_ne_none_of_haltsFromConfig
      (M).description_haltTransitionFree hhalts
  · intro k _hkState
    exact initialized_stepConfig_ne_none_of_no_evidence
      source sourceSimulator recognizer checkerSimulator b
      hsourceSimulator hcheckerSimulator hrecognizer raw hevidence k

/-- A physical halt of the lowered initialized master yields the original
fixed-Boolean fuel-pair evidence. The only target-specific premise is the
row-progress fact for the assembled master table. -/
theorem evidence_of_lowered_haltsFromTape_initialized
    (hrecognizer : FixedBoolSimulatorLayoutRecognizerSpec source recognizer b)
    (hconfigProgress :
      forall {a d : CommonGround.FiniteTransducers.Structured.Configuration},
        (M).description.stepConfig a = some d ->
          a.state ≠ d.state ∨ a.tapes ≠ d.tapes)
    (raw : List Bool) (Tout : Tape Bool)
    (hhalt :
      (lowerStructured3Description (M).description).HaltsFromTape
        (encodedGuardedStructuredTapes
          ((M).config (.bootstrap U12ZeroBootstrap.State.lengthScan)
            (Tape.input (show Word Bool from raw))
            Tape.blank Tape.blank).tapes)
        Tout) :
    PairedRecognizerDovetailControllerStageAttemptFuelPairEvidence
      source (show Word Bool from raw) b := by
  let c :=
    (M).config (.bootstrap U12ZeroBootstrap.State.lengthScan)
      (Tape.input (show Word Bool from raw)) Tape.blank Tape.blank
  have hlogical :=
    FoC.Computability.BoundedFuelPairSearch.U12LoweredInversion.lowerStructured3Description_haltsFromTape_implies_haltsFromConfig
        (M).description_wellFormed
        (M).description_haltTransitionFree
        (M).description_supportsReadWriteRows3
        c (by rfl) (by rfl)
        (by
          simpa [c] using
            initialized_stepConfig_ne_none_of_ne_halt
              source sourceSimulator recognizer checkerSimulator b
              hsourceSimulator hcheckerSimulator hrecognizer raw)
        hconfigProgress
        (by simpa [c] using hhalt)
  exact U12CandidateAttemptLoop.evidence_of_haltsFromConfig_initialized
    source sourceSimulator recognizer checkerSimulator b
    hsourceSimulator hcheckerSimulator hrecognizer raw
    (by simpa [c] using hlogical)

end MasterDivergence

end U12EquivAdapter
end BoundedFuelPairSearch
end Computability
end FoC
