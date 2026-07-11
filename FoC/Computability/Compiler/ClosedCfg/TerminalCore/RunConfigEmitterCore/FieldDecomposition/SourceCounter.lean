import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition.ClassifiedBoundary

set_option doc.verso true

/-!
# Original-source scratch-width counter

This is the first executable phase of the #18 field decomposer.  It skips the
first bit of the encoded simulator layout, emits one raw marker on logical tape
2 for every remaining source bit, then rewinds logical tape 0 to the padded
word start needed by later parser phases.  Logical tape 1 remains exactly
blank.

The resulting marker count is the original input scratch width.  It is
therefore independent of every later change to the simulated configuration
and can be threaded unchanged through the execution loops and serializer.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace FieldDecomposition
namespace SourceCounter

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

/-!
## Exact logical tape families
-/

/-- Source cursor while scanning right.  The processed prefix is nearest-first
in {lit}`processedRev`; the remaining word begins under the head. -/
def scanTape (processedRev remaining : Word Bool) : Tape Bool :=
  tapeAtCells (processedRev.map some) (remaining.map some)

/-- Rewind cursor.  {lit}`remainingRev` is the not-yet-rewound reversed prefix;
{lit}`scanned` is already restored in forward order to the right. -/
def rewindTape (remainingRev scanned : Word Bool) : Tape Bool :=
  match remainingRev with
  | [] =>
      tapeAtCells []
        (none :: List.append (scanned.map some) [none])
  | bit :: rest =>
      tapeAtCells (rest.map some)
        (some bit :: List.append (scanned.map some) [none])

/-- Raw marker block, with the head on the blank immediately to its right. -/
def markerTape (markers : Nat) : Tape Bool :=
  tapeAtCells
    (List.replicate markers (some true : Option Bool)) []

theorem scanTape_cons
    (processedRev : Word Bool) (bit : Bool) (rest : Word Bool) :
    keepR.apply (scanTape processedRev (bit :: rest)) =
      scanTape (bit :: processedRev) rest := by
  cases rest <;>
    rfl
  done

theorem markerTape_writeR
    (markers : Nat) :
    (writeR (some true)).apply (markerTape markers) =
      markerTape (markers + 1) := by
  simp [markerTape, writeR, TapeAction.apply, HeadMove.apply,
    Tape.write, Tape.move, Tape.moveRight, tapeAtCells,
    List.replicate_succ]
  done

theorem scanTape_turn
    (bit : Bool) (processedRev : Word Bool) :
    keepL.apply (scanTape (bit :: processedRev) []) =
      rewindTape (bit :: processedRev) [] := by
  rfl
  done

theorem rewindTape_step
    (bit : Bool) (rest scanned : Word Bool) :
    keepL.apply (rewindTape (bit :: rest) scanned) =
      rewindTape rest (bit :: scanned) := by
  cases rest <;>
    rfl
  done

theorem rewindTape_done (scanned : Word Bool) :
    keepR.apply (rewindTape [] scanned) =
      rightEdgeRewindTargetTape scanned [] := by
  cases scanned <;>
    rfl
  done

theorem scanTape_nil_cons_eq_input
    (bit : Bool) (rest : Word Bool) :
    scanTape [] (bit :: rest) = Tape.input (bit :: rest) := by
  rfl
  done

@[simp] theorem markerTape_zero : markerTape 0 = Tape.blank := by
  rfl
  done

/-!
## Typed finite-control table
-/

inductive State where
  | start
  | scan
  | rewind
  | done
  | halt
deriving DecidableEq, Repr

def states : List State :=
  [.start, .scan, .rewind, .done, .halt]

theorem start_mem_states : State.start ∈ states := by
  simp [states]
  done

theorem scan_mem_states : State.scan ∈ states := by
  simp [states]
  done

theorem rewind_mem_states : State.rewind ∈ states := by
  simp [states]
  done

theorem done_mem_states : State.done ∈ states := by
  simp [states]
  done

theorem halt_mem_states : State.halt ∈ states := by
  simp [states]
  done

/-- Skip the first source bit, count every later bit, and rewind. -/
def next :
    State -> Option Bool -> Option Bool -> Option Bool ->
      Option (TypedStep State)
  | .start, some _, _, _ =>
      some
        { target := .scan
          action0 := keepR
          action1 := keepS
          action2 := keepS }
  | .scan, some _, _, _ =>
      some
        { target := .scan
          action0 := keepR
          action1 := keepS
          action2 := writeR (some true) }
  | .scan, none, _, _ =>
      some
        { target := .rewind
          action0 := keepL
          action1 := keepS
          action2 := keepS }
  | .rewind, some _, _, _ =>
      some
        { target := .rewind
          action0 := keepL
          action1 := keepS
          action2 := keepS }
  | .rewind, none, _, _ =>
      some
        { target := .done
          action0 := keepR
          action1 := keepS
          action2 := keepS }
  | .done, _, _, _ =>
      some
        { target := .halt
          action0 := keepS
          action1 := keepS
          action2 := keepS }
  | _, _, _, _ => none

theorem next_target_mem :
    forall s : State, s ∈ states ->
      forall (r0 r1 r2 : Option Bool) (st : TypedStep State),
        next s r0 r1 r2 = some st -> st.target ∈ states := by
  intro s hs r0 r1 r2 st hnext
  cases s with
  | start =>
      cases r0 <;> simp [next] at hnext
      cases hnext
      exact scan_mem_states
  | scan =>
      cases r0 <;> simp only [next] at hnext
      · cases hnext
        exact rewind_mem_states
      · cases hnext
        exact scan_mem_states
  | rewind =>
      cases r0 <;> simp only [next] at hnext
      · cases hnext
        exact done_mem_states
      · cases hnext
        exact rewind_mem_states
  | done =>
      cases hnext
      exact halt_mem_states
  | halt =>
      simp [next] at hnext
  done

def table : TypedStateTable State :=
  TypedStateTable.ofList
    states
    .start
    .halt
    next
    start_mem_states
    halt_mem_states
    (by intro r0 r1 r2; rfl)
    next_target_mem

def description : Description :=
  table.description

theorem description_wellFormed : description.WellFormed := by
  exact table.description_wellFormed
  done

theorem description_haltTransitionFree :
    description.HaltTransitionFree := by
  exact table.description_haltTransitionFree
  done

theorem description_supportsReadWriteRows3 :
    SupportsReadWriteRows3 description := by
  exact table.description_supportsReadWriteRows3
  done

theorem description_subroutineReady :
    description.SubroutineReady := by
  exact table.description_subroutineReady
  done

/-!
## Exact typed execution
-/

def cfg (s : State) (T0 T2 : Tape Bool) :
    CommonGround.FiniteTransducers.Structured.Configuration :=
  ThreeTape.config (table.stateId s) T0 Tape.blank T2

theorem stepConfig_start
    (first : Bool) (rest : Word Bool) (markers : Nat) :
    description.stepConfig
        (cfg .start (scanTape [] (first :: rest))
          (markerTape markers)) =
      some
        (cfg .scan (scanTape [first] rest)
          (markerTape markers)) := by
  unfold description cfg
  rw [table.stepConfig_config start_mem_states]
  change (next .start (some first) none none).map _ = _
  simp only [next, Option.map_some]
  rw [scanTape_cons]
  simp [keepS, TapeAction.stay, TapeAction.apply, HeadMove.apply]
  done

theorem stepConfig_scan
    (processedRev : Word Bool) (bit : Bool) (rest : Word Bool)
    (markers : Nat) :
    description.stepConfig
        (cfg .scan (scanTape processedRev (bit :: rest))
          (markerTape markers)) =
      some
        (cfg .scan (scanTape (bit :: processedRev) rest)
          (markerTape (markers + 1))) := by
  unfold description cfg
  rw [table.stepConfig_config scan_mem_states]
  change (next .scan (some bit) none none).map _ = _
  simp only [next, Option.map_some]
  rw [scanTape_cons, markerTape_writeR]
  simp [keepS, TapeAction.stay, TapeAction.apply, HeadMove.apply]
  done

theorem stepConfig_turn
    (last : Bool) (processedRev : Word Bool) (markers : Nat) :
    description.stepConfig
        (cfg .scan (scanTape (last :: processedRev) [])
          (markerTape markers)) =
      some
        (cfg .rewind (rewindTape (last :: processedRev) [])
          (markerTape markers)) := by
  unfold description cfg
  rw [table.stepConfig_config scan_mem_states]
  change (next .scan none none none).map _ = _
  simp only [next, Option.map_some]
  rw [scanTape_turn]
  simp [keepS, TapeAction.stay, TapeAction.apply, HeadMove.apply]
  done

theorem stepConfig_rewind
    (bit : Bool) (rest scanned : Word Bool) (markers : Nat) :
    description.stepConfig
        (cfg .rewind (rewindTape (bit :: rest) scanned)
          (markerTape markers)) =
      some
        (cfg .rewind (rewindTape rest (bit :: scanned))
          (markerTape markers)) := by
  unfold description cfg
  rw [table.stepConfig_config rewind_mem_states]
  change (next .rewind (some bit) none none).map _ = _
  simp only [next, Option.map_some]
  rw [rewindTape_step]
  simp [keepS, TapeAction.stay, TapeAction.apply, HeadMove.apply]
  done

theorem stepConfig_rewind_done
    (scanned : Word Bool) (markers : Nat) :
    description.stepConfig
        (cfg .rewind (rewindTape [] scanned) (markerTape markers)) =
      some
        (cfg .done (rightEdgeRewindTargetTape scanned [])
          (markerTape markers)) := by
  unfold description cfg
  rw [table.stepConfig_config rewind_mem_states]
  change (next .rewind none none none).map _ = _
  simp only [next, Option.map_some]
  rw [rewindTape_done]
  simp [keepS, TapeAction.stay, TapeAction.apply, HeadMove.apply]
  done

theorem stepConfig_done (T0 T2 : Tape Bool) :
    description.stepConfig (cfg .done T0 T2) =
      some (cfg .halt T0 T2) := by
  unfold description cfg
  rw [table.stepConfig_config done_mem_states]
  change (next .done (Tape.read T0) none (Tape.read T2)).map _ = _
  simp [next, keepS, TapeAction.stay, TapeAction.apply, HeadMove.apply]
  done

theorem runConfig_one_of_stepConfig
    {c d : CommonGround.FiniteTransducers.Structured.Configuration}
    (hstep : description.stepConfig c = some d) :
    description.runConfig 1 c = d := by
  simp [Description.runConfig, hstep]
  done

/-- Exact rightward counting pass. -/
theorem runConfig_scan
    (processedRev remaining : Word Bool) (markers : Nat) :
    description.runConfig remaining.length
        (cfg .scan (scanTape processedRev remaining)
          (markerTape markers)) =
      cfg .scan
        (scanTape (List.append remaining.reverse processedRev) [])
        (markerTape (markers + remaining.length)) := by
  induction remaining generalizing processedRev markers with
  | nil =>
      simp [Description.runConfig]
  | cons bit rest ih =>
      rw [show (bit :: rest).length = 1 + rest.length by
        simp [Nat.add_comm]]
      rw [Description.runConfig_add]
      rw [runConfig_one_of_stepConfig
        (stepConfig_scan processedRev bit rest markers)]
      rw [ih (bit :: processedRev) (markers + 1)]
      have hrev :
          List.append rest.reverse (bit :: processedRev) =
            List.append (bit :: rest).reverse processedRev := by
        simp [List.reverse_cons, List.append_assoc]
      have hmarkers :
          (markers + 1) + rest.length =
            markers + (1 + rest.length) := by
        lia
      rw [hrev, hmarkers]
  done

/-- Exact leftward rewind and parser-ready padded endpoint. -/
theorem runConfig_rewind
    (remainingRev scanned : Word Bool) (markers : Nat) :
    description.runConfig (remainingRev.length + 1)
        (cfg .rewind (rewindTape remainingRev scanned)
          (markerTape markers)) =
      cfg .done
        (rightEdgeRewindTargetTape
          (List.append remainingRev.reverse scanned) [])
        (markerTape markers) := by
  induction remainingRev generalizing scanned with
  | nil =>
      simpa using
        runConfig_one_of_stepConfig
          (stepConfig_rewind_done scanned markers)
  | cons bit rest ih =>
      rw [show (bit :: rest).length + 1 =
          1 + (rest.length + 1) by
        simp [Nat.add_comm, Nat.add_left_comm]]
      rw [Description.runConfig_add]
      rw [runConfig_one_of_stepConfig
        (stepConfig_rewind bit rest scanned markers)]
      rw [ih (bit :: scanned)]
      have hword :
          List.append rest.reverse (bit :: scanned) =
            List.append (bit :: rest).reverse scanned := by
        simp [List.reverse_cons, List.append_assoc]
      rw [hword]
  done

theorem runConfig_one_turn_word
    (first : Bool) (rest : Word Bool) (markers : Nat) :
    description.runConfig 1
        (cfg .scan (scanTape (first :: rest).reverse [])
          (markerTape markers)) =
      cfg .rewind (rewindTape (first :: rest).reverse [])
        (markerTape markers) := by
  cases hrev : (first :: rest).reverse with
  | nil =>
      have hlen := congrArg List.length hrev
      simp at hlen
  | cons last processedRev =>
      simpa [hrev] using
        runConfig_one_of_stepConfig
          (stepConfig_turn last processedRev markers)
  done

/-- Full source-counting phase through the explicit pre-halt state. -/
theorem runConfig_to_done
    (first : Bool) (rest : Word Bool) :
    description.runConfig (2 * rest.length + 4)
        (cfg .start (Tape.input (first :: rest)) Tape.blank) =
      cfg .done
        (rightEdgeRewindTargetTape (first :: rest) [])
        (markerTape rest.length) := by
  let c1 :=
    cfg .scan (scanTape [first] rest) (markerTape 0)
  let c2 :=
    cfg .scan (scanTape (first :: rest).reverse [])
      (markerTape rest.length)
  let c3 :=
    cfg .rewind (rewindTape (first :: rest).reverse [])
      (markerTape rest.length)
  have h1 :
      description.runConfig 1
          (cfg .start (Tape.input (first :: rest)) Tape.blank) = c1 := by
    simpa [c1, scanTape_nil_cons_eq_input] using
      runConfig_one_of_stepConfig (stepConfig_start first rest 0)
  have h2 :
      description.runConfig rest.length c1 = c2 := by
    simpa [c1, c2, List.reverse_cons] using
      runConfig_scan [first] rest 0
  have h3 :
      description.runConfig 1 c2 = c3 := by
    simpa [c2, c3] using
      runConfig_one_turn_word first rest rest.length
  have h4 :
      description.runConfig ((first :: rest).reverse.length + 1) c3 =
        cfg .done
          (rightEdgeRewindTargetTape (first :: rest) [])
          (markerTape rest.length) := by
    simpa [c3] using
      runConfig_rewind (first :: rest).reverse [] rest.length
  apply runConfig_chain4_of_eq
      (D := description)
      (n := 1) (m := rest.length) (k := 1)
      (l := (first :: rest).reverse.length + 1)
      (c1 := c1) (c2 := c2) (c3 := c3)
  · simp
    lia
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  done

theorem runConfig_to_halt
    (first : Bool) (rest : Word Bool) :
    description.runConfig (2 * rest.length + 5)
        (cfg .start (Tape.input (first :: rest)) Tape.blank) =
      cfg .halt
        (rightEdgeRewindTargetTape (first :: rest) [])
        (markerTape rest.length) := by
  rw [show 2 * rest.length + 5 =
      (2 * rest.length + 4) + 1 by lia]
  rw [Description.runConfig_add]
  rw [runConfig_to_done]
  exact
    runConfig_one_of_stepConfig
      (stepConfig_done
        (rightEdgeRewindTargetTape (first :: rest) [])
        (markerTape rest.length))
  done

theorem haltsWithTapes
    (first : Bool) (rest : Word Bool) :
    description.HaltsWithTapes
        (ThreeTape.config description.start
          (Tape.input (first :: rest)) Tape.blank Tape.blank)
        [ rightEdgeRewindTargetTape (first :: rest) []
        , Tape.blank
        , markerTape rest.length ] := by
  refine ⟨2 * rest.length + 5, ?_⟩
  change
    description.runConfig (2 * rest.length + 5)
        (cfg .start (Tape.input (first :: rest)) Tape.blank) =
      cfg .halt
        (rightEdgeRewindTargetTape (first :: rest) [])
        (markerTape rest.length)
  exact runConfig_to_halt first rest
  done

/-!
## Simulator-layout specialization
-/

/-- Physical scratch-width block carried into all later #18 phases. -/
def layoutMarkerTape (L : SimulatorLayout) : Tape Bool :=
  tapeAtCells (RunConfigEmitterTheory.scratchWidthMarkers L) []

theorem layout_bits_cons_and_width (L : SimulatorLayout) :
    exists first : Bool, exists rest : Word Bool,
      SimulatorLayout.asBoolInput L = first :: rest ∧
        rest.length =
          FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
            L := by
  cases hbits : SimulatorLayout.asBoolInput L with
  | nil =>
      have hlen :=
        RunConfigEmitterTheory.simulatorLayout_asBoolInput_length_ge_two L
      simp [hbits] at hlen
  | cons first rest =>
      refine ⟨first, rest, rfl, ?_⟩
      have hwidth :=
        RunConfigEmitterTheory.fixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_eq_length_sub_one
          L
      rw [hbits] at hwidth
      simp at hwidth
      exact hwidth.symm
  done

theorem markerTape_eq_layoutMarkerTape
    (L : SimulatorLayout) (rest : Word Bool)
    (hrest :
      rest.length =
        FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
          L) :
    markerTape rest.length = layoutMarkerTape L := by
  simp [markerTape, layoutMarkerTape,
    RunConfigEmitterTheory.scratchWidthMarkers, hrest]
  done

theorem haltsWithTapes_layout (L : SimulatorLayout) :
    description.HaltsWithTapes
        (ThreeTape.config description.start
          (Tape.input (SimulatorLayout.asBoolInput L))
          Tape.blank Tape.blank)
        [ rightEdgeRewindTargetTape (SimulatorLayout.asBoolInput L) []
        , Tape.blank
        , layoutMarkerTape L ] := by
  rcases layout_bits_cons_and_width L with
    ⟨first, rest, hbits, hwidth⟩
  rw [hbits]
  rw [← markerTape_eq_layoutMarkerTape L rest hwidth]
  exact haltsWithTapes first rest
  done

/-!
## Lowered physical phase
-/

def loweredDescription : MachineDescription :=
  lowerStructured3Description description

theorem loweredDescription_wellFormed :
    loweredDescription.WellFormed := by
  exact lowerStructured3Description_wellFormed
    description_wellFormed description_supportsReadWriteRows3
  done

theorem loweredDescription_subroutineReady :
    loweredDescription.SubroutineReady := by
  exact lowerStructured3Description_subroutineReady
    description_wellFormed description_supportsReadWriteRows3
  done

/-- Exact physical boundary after source counting and rewind. -/
def targetTape (L : SimulatorLayout) : Tape Bool :=
  encodedGuardedStructuredTapes
    [ rightEdgeRewindTargetTape (SimulatorLayout.asBoolInput L) []
    , Tape.blank
    , layoutMarkerTape L ]

theorem loweredDescription_haltsFromTapeEquiv_guarded
    (L : SimulatorLayout) :
    loweredDescription.HaltsFromTapeEquiv
        (encodedGuardedStructuredTapes
          [ Tape.input (SimulatorLayout.asBoolInput L)
          , Tape.blank
          , Tape.blank ])
        (targetTape L) := by
  unfold loweredDescription targetTape
  apply lowerStructured3Description_haltsFromConfigWithTapes
    description_wellFormed
    description_haltTransitionFree
    description_supportsReadWriteRows3
    (c :=
      ThreeTape.config description.start
        (Tape.input (SimulatorLayout.asBoolInput L))
        Tape.blank Tape.blank)
  · rfl
  · rfl
  · exact haltsWithTapes_layout L
  done

theorem loweredDescription_haltsFromTapeEquiv
    (L : SimulatorLayout) :
    loweredDescription.HaltsFromTapeEquiv
      (FieldDecomposition.embeddedSourceTape L) (targetTape L) := by
  rw [FieldDecomposition.embeddedSourceTape_eq_guarded]
  exact loweredDescription_haltsFromTapeEquiv_guarded L
  done

def Spec (counter : MachineDescription) : Prop :=
  counter.SubroutineReady ∧
    forall L : SimulatorLayout,
      counter.HaltsFromTapeEquiv
        (FieldDecomposition.embeddedSourceTape L) (targetTape L)

def Construction : Prop :=
  exists counter : MachineDescription, Spec counter

/-- Completed first phase of the integrated field decomposer. -/
theorem construction_core : Construction :=
  ⟨loweredDescription,
    loweredDescription_subroutineReady,
    loweredDescription_haltsFromTapeEquiv⟩

/-!
## Exact next phase
-/

/-- Broad D-specific remainder after the now-complete source counter.

Starting with the original scratch-width markers on tape 2, it must parse the
padded layout on tape 0, emit the raw stage counter on tape 1, place canonical
input/original-stage/raw-state metadata behind the preserved scratch markers,
materialize the exact configuration tape (including blank cells and head
split), leave the hit bit at the tape-2 head, and reserve the D-specific finite
classification selector in the scratch markers nearest the hit.  The narrower
authoritative frontier after stage parsing is {lit}`StageCounter.PostStageSpec`.-/
def PostCountSpec
    (D : MachineDescription) (parser : MachineDescription) : Prop :=
  parser.SubroutineReady ∧
    forall L : SimulatorLayout,
      parser.HaltsFromTapeEquiv
        (targetTape L)
        (ClassifiedBoundary.classifiedLoopTargetTape D L)

def PostCountConstruction (D : MachineDescription) : Prop :=
  exists parser : MachineDescription, PostCountSpec D parser

end SourceCounter
end FieldDecomposition
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
