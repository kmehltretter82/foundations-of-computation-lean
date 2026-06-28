import FoC.Computability.Compiler.Core.EncodedRewriters.ClosedConfigRunner.Projection.Quoter.CellPass

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace BoundedLayoutRunner

namespace SelectedProjectionInputQuoterFiniteLeaf

open DovetailInitialLayoutInitializer

private abbrev SIMS :=
  DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription

private abbrev assemblyControlPrefixTransitions : List TransitionDescription :=
  [ transition 1800 (some false) (some false) Direction.right 1801
  , transition 1801 (some false) (some false) Direction.right 1802
  , transition 1802 (some false) (some false) Direction.right 1803
  , transition 1803 (some true) (some true) Direction.right 1804
  , transition 1804 (some false) (some false) Direction.right 1805
  , transition 1805 (some false) none Direction.right 0
  ]

/--
Finite skeleton for the exact input-quoter assembly layer.  The high states
consume the fixed {lit}`transition` symbol and the first two bits of the
stage-input field, replacing the second stage-input bit with the scanner
marker.  Control then drops into the existing marked stage-input scanner at
state {lit}`0`; state {lit}`210` is the important internal boundary where the
scanner has consumed the input prefix and the stage nat, leaving the
source-rest suffix under the head.
-/
def AssemblySkeletonDescription : MachineDescription where
  stateCount := 2000
  start := 1800
  halt := 1999
  transitions :=
    [ transition 1800 (some false) (some false) Direction.right 1801
    , transition 1801 (some false) (some false) Direction.right 1802
    , transition 1802 (some false) (some false) Direction.right 1803
    , transition 1803 (some true) (some true) Direction.right 1804
    , transition 1804 (some false) (some false) Direction.right 1805
    , transition 1805 (some false) none Direction.right 0
    ] ++ SIMS.transitions

def AssemblyPrefixDescription : MachineDescription where
  stateCount := 2000
  start := 1800
  halt := 210
  transitions :=
    [ transition 1800 (some false) (some false) Direction.right 1801
    , transition 1801 (some false) (some false) Direction.right 1802
    , transition 1802 (some false) (some false) Direction.right 1803
    , transition 1803 (some true) (some true) Direction.right 1804
    , transition 1804 (some false) (some false) Direction.right 1805
    , transition 1805 (some false) none Direction.right 0
    ] ++
      SIMS.transitions.filter
        (fun t => decide (t.source ≠ 210))

private abbrev ASM := AssemblySkeletonDescription
private abbrev AP := AssemblyPrefixDescription

theorem assemblySkeletonDescription_wellFormed :
    ASM.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := ASM.transitions)
      (stateCount := ASM.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := ASM.transitions)
      (by native_decide)

theorem assemblySkeletonDescription_haltTransitionFree :
    ASM.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := ASM.transitions)
    (state := ASM.halt)
    (by native_decide)

theorem assemblySkeletonDescription_subroutineReady :
    ASM.SubroutineReady :=
  ⟨assemblySkeletonDescription_wellFormed,
    assemblySkeletonDescription_haltTransitionFree⟩

theorem assemblyPrefixDescription_wellFormed :
    AP.WellFormed := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := AP.transitions)
      (stateCount := AP.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := AP.transitions)
      (by native_decide)

theorem assemblyPrefixDescription_haltTransitionFree :
    AP.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := AP.transitions)
    (state := AP.halt)
    (by native_decide)

theorem assemblyPrefixDescription_subroutineReady :
    AP.SubroutineReady :=
  ⟨assemblyPrefixDescription_wellFormed,
    assemblyPrefixDescription_haltTransitionFree⟩

theorem runConfig_eq_of_transitions
    {D E : MachineDescription}
    (htrans : D.transitions = E.transitions)
    (n : Nat) (c : Configuration) :
    D.runConfig n c = E.runConfig n c := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      simp only [runConfig]
      have hstep : D.stepConfig c = E.stepConfig c := by
        unfold stepConfig lookupTransition
        rw [htrans]
      rw [hstep]
      cases E.stepConfig c with
      | none => rfl
      | some next => exact ih next

theorem find?_source_ne_halt_guard_eq_find?
    (l : List TransitionDescription)
    (halt state : Nat) (read : Option Bool)
    (hstate : state ≠ halt) :
    l.find?
        (fun t => !decide (t.source = halt) && Matches state read t) =
      l.find? (Matches state read) := by
  induction l with
  | nil =>
      rfl
  | cons t ts ih =>
      by_cases hmatch : Matches state read t = true
      · have hsource : t.source = state := by
          by_cases hs : t.source = state
          · exact hs
          · cases read <;>
            simp [Matches, hs] at hmatch
        have hkeep : t.source ≠ halt := by
          intro hhalt
          exact hstate (by rw [← hsource, hhalt])
        have hhaltBool : decide (t.source = halt) = false := by
          simp [hkeep]
        simp [hmatch, hhaltBool]
      · simp [hmatch, ih]

theorem find?_filter_source_ne_halt_eq_find?
    (l : List TransitionDescription)
    (halt state : Nat) (read : Option Bool)
    (hstate : state ≠ halt) :
    (l.filter (fun t => decide (t.source ≠ halt))).find?
        (Matches state read) =
      l.find? (Matches state read) := by
  simpa [List.find?_filter, Bool.and_eq_true] using
    find?_source_ne_halt_guard_eq_find?
      l halt state read hstate

theorem find?_append_right_eq_of_find?_eq
    {α : Type} (p : α -> Bool)
    (pref left right : List α)
    (h : left.find? p = right.find? p) :
    (List.append pref left).find? p =
      (List.append pref right).find? p := by
  induction pref with
  | nil =>
      exact h
  | cons x xs ih =>
      by_cases hx : p x = true
      · simp [hx]
      · simpa [hx] using ih

theorem assemblyPrefixDescription_lookupTransition_eq_skeleton
    (state : Nat) (read : Option Bool) (hstate : state ≠ 210) :
    AP.lookupTransition state read = ASM.lookupTransition state read := by
  unfold lookupTransition
  change
    (List.append assemblyControlPrefixTransitions
        (SIMS.transitions.filter
          (fun t => decide (t.source ≠ 210)))).find?
        (Matches state read) =
      (List.append assemblyControlPrefixTransitions SIMS.transitions).find?
        (Matches state read)
  exact
    find?_append_right_eq_of_find?_eq
      (p := Matches state read)
      (pref := assemblyControlPrefixTransitions)
      (left := SIMS.transitions.filter
        (fun t => decide (t.source ≠ 210)))
      (right := SIMS.transitions)
      (find?_filter_source_ne_halt_eq_find?
        (l := SIMS.transitions) (halt := 210) (state := state)
        (read := read) hstate)

theorem assemblyPrefixDescription_stepConfig_eq_skeleton_of_state_ne_210
    (c : Configuration) (hstate : c.state ≠ 210) :
    AP.stepConfig c = ASM.stepConfig c := by
  unfold stepConfig
  rw [assemblyPrefixDescription_lookupTransition_eq_skeleton
    c.state (Tape.read c.tape) hstate]

theorem assemblyPrefixDescription_runConfig_eq_skeleton_of_trace_ne_210
    (n : Nat) (c : Configuration)
    (hne : forall k : Nat, k < n -> (ASM.runConfig k c).state ≠ 210) :
    AP.runConfig n c = ASM.runConfig n c := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      have hstate : c.state ≠ 210 := by
        simpa [runConfig] using hne 0 (Nat.zero_lt_succ n)
      simp only [runConfig]
      rw [assemblyPrefixDescription_stepConfig_eq_skeleton_of_state_ne_210
        c hstate]
      cases hstep : ASM.stepConfig c with
      | none =>
          rfl
      | some next =>
          exact ih next (by
            intro k hk
            have htrace := hne (k + 1) (Nat.succ_lt_succ hk)
            have hrun :
                ASM.runConfig (k + 1) c = ASM.runConfig k next := by
              simp [runConfig, hstep]
            simpa [hrun] using htrace)

theorem assemblySkeletonDescription_lookupTransition_eq_scanner
    (state : Nat) (read : Option Bool) (hstate : state < 1800) :
    ASM.lookupTransition state read = SIMS.lookupTransition state read := by
  have h1800' : 1800 ≠ state := by omega
  have h1801' : 1801 ≠ state := by omega
  have h1802' : 1802 ≠ state := by omega
  have h1803' : 1803 ≠ state := by omega
  have h1804' : 1804 ≠ state := by omega
  have h1805' : 1805 ≠ state := by omega
  cases read <;>
    simp [ASM, AssemblySkeletonDescription, lookupTransition, Matches,
      transition, h1800', h1801', h1802', h1803', h1804', h1805']

theorem assemblySkeletonDescription_stepConfig_eq_scanner
    (c : Configuration) (hstate : c.state < 1800) :
    ASM.stepConfig c = SIMS.stepConfig c := by
  unfold stepConfig
  rw [assemblySkeletonDescription_lookupTransition_eq_scanner
    c.state (Tape.read c.tape) hstate]

theorem assemblySkeletonDescription_runConfig_eq_scanner
    (n : Nat) (c : Configuration)
    (hstate : c.state < SIMS.stateCount) :
    ASM.runConfig n c = SIMS.runConfig n c := by
  induction n generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      simp only [runConfig]
      have hlt1800 : c.state < 1800 := by
        have hs : SIMS.stateCount = 1000 := rfl
        omega
      rw [assemblySkeletonDescription_stepConfig_eq_scanner c hlt1800]
      cases hstep : SIMS.stepConfig c with
      | none => rfl
      | some next =>
          exact ih next
            (stepConfig_state_bound
              DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputMarkedScannerDescription_wellFormed
              hstep)

def markedTailStartConfigWithBase
    (leftTail : List (Option Bool)) (tail : Word Bool) :
    Configuration :=
  { state := SIMS.start
    tape :=
      Tape.move Direction.right
        (tapeAtCells (some false :: leftTail)
          (none :: tail.map some)) }

def markedTailStartConfigWithBaseCells
    (leftTail tailCells : List (Option Bool)) :
    Configuration :=
  { state := SIMS.start
    tape :=
      Tape.move Direction.right
        (tapeAtCells (some false :: leftTail)
          (none :: tailCells)) }

def transitionPrefixLeftTail : List (Option Bool) :=
  [some true, some false, some false, some false]

def optionBitDefaultFalse : Option Bool -> Bool
  | none => false
  | some b => b

theorem optionBitDefaultFalse_map_some
    (bits : Word Bool) :
    List.map (optionBitDefaultFalse ∘ some) bits = bits := by
  induction bits with
  | nil =>
      rfl
  | cons b bits ih =>
      simp [optionBitDefaultFalse, ih]

theorem assemblyBoundaryLeft_empty_defaultBits
    (stage : Nat) :
    List.map optionBitDefaultFalse
        (List.reverse
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).reverse.map some)
            (List.append [some true, some true, none, some false]
              transitionPrefixLeftTail))) =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
        (DovetailInitialLayoutInitializer.stageInputBits
          ([] : Word Bool) stage) := by
  rw [DovetailInitialLayoutInitializer.stageInputBits_eq_false_false_tail]
  rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTail_nil]
  simp [transitionPrefixLeftTail, optionBitDefaultFalse,
    optionBitDefaultFalse_map_some,
    encodeCodeSymbolAsInput, List.reverse_append]

theorem assemblyBoundaryLeft_nonempty_defaultBits
    (b : Bool) (rest : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (List.reverse
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).reverse.map some)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
                (b :: rest)).reverse.map some)
              (List.append [none, some false] transitionPrefixLeftTail)))) =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
        (DovetailInitialLayoutInitializer.stageInputBits
          (b :: rest) stage) := by
  rw [DovetailInitialLayoutInitializer.stageInputBits_eq_false_false_tail]
  rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTail_eq_prefix_stageNat]
  simp [transitionPrefixLeftTail, optionBitDefaultFalse,
    optionBitDefaultFalse_map_some,
    encodeCodeSymbolAsInput, List.map_append, List.reverse_append]

def assemblySourceRestBoundaryLeftRev
    (w : Word Bool) (stage : Nat) : List (Option Bool) :=
  match w with
  | [] =>
      List.append
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage).reverse.map some)
        (List.append [some true, some true, none, some false]
          transitionPrefixLeftTail)
  | b :: rest =>
      List.append
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage).reverse.map some)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
            (b :: rest)).reverse.map some)
          (List.append [none, some false] transitionPrefixLeftTail))

theorem assemblySourceRestBoundaryLeftRev_defaultBits
    (w : Word Bool) (stage : Nat) :
    List.map optionBitDefaultFalse
        (List.reverse
          (assemblySourceRestBoundaryLeftRev w stage)) =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
        (DovetailInitialLayoutInitializer.stageInputBits w stage) := by
  cases w with
  | nil =>
      exact assemblyBoundaryLeft_empty_defaultBits stage
  | cons b rest =>
      exact assemblyBoundaryLeft_nonempty_defaultBits b rest stage

theorem assemblySourceRestBoundaryLeftRev_defaultBits_append
    (w sourceRestBits : Word Bool) (stage : Nat) :
    List.append
        (List.map optionBitDefaultFalse
          (List.reverse
            (assemblySourceRestBoundaryLeftRev w stage)))
        sourceRestBits =
      List.append
        (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
        (List.append
          (DovetailInitialLayoutInitializer.stageInputBits w stage)
          sourceRestBits) := by
  rw [assemblySourceRestBoundaryLeftRev_defaultBits]
  simp [List.append_assoc]

theorem assemblySourceRestBoundaryLeftRev_defaultBits_append_sourceRestFieldBits
    (L : DovetailLayout) :
    List.append
        (List.map optionBitDefaultFalse
          (List.reverse
            (assemblySourceRestBoundaryLeftRev L.input L.stage)))
        (SelectedProjectionTailProjector.sourceRestFieldBits L) =
      ParsedLayoutBits L := by
  rw [assemblySourceRestBoundaryLeftRev_defaultBits_append]
  rw [SelectedProjectionTailProjector.parsedLayoutBits_eq_transition_stageInput_sourceRestFieldBits]

theorem assemblySkeletonDescription_run_prefix_to_marked_tail
    (tail : Word Bool) :
    ASM.runConfig 6
        (config ASM.start []
          (List.append
            (List.map some
              (List.append
                (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                [false, false]))
            (tail.map some))) =
      markedTailStartConfigWithBase transitionPrefixLeftTail tail := by
  cases tail <;>
    simp [ASM, AssemblySkeletonDescription,
      SIMS,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      markedTailStartConfigWithBase, transitionPrefixLeftTail,
      encodeCodeSymbolAsInput, config, tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem assemblySkeletonDescription_run_prefix_to_marked_tail_cells
    (tailCells : List (Option Bool)) :
    ASM.runConfig 6
        (config ASM.start []
          (List.append
            (List.map some
              (List.append
                (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                [false, false]))
            tailCells)) =
      markedTailStartConfigWithBaseCells transitionPrefixLeftTail
        tailCells := by
  cases tailCells <;>
    simp [ASM, AssemblySkeletonDescription,
      SIMS,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      markedTailStartConfigWithBaseCells, transitionPrefixLeftTail,
      encodeCodeSymbolAsInput, config, tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem assemblySkeletonDescription_run_prefix_to_stageInput_tail
    (w : Word Bool) (stage : Nat) (sourceRestBits : Word Bool) :
    ASM.runConfig 6
        (config ASM.start []
          (List.append
            (List.map some
              (List.append
                (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                (DovetailInitialLayoutInitializer.stageInputBits
                  w stage)))
            (sourceRestBits.map some))) =
      markedTailStartConfigWithBase transitionPrefixLeftTail
        (List.append
          (DovetailInitialLayoutInitializer.stageInputSecondBitTail
            w stage)
          sourceRestBits) := by
  rw [DovetailInitialLayoutInitializer.stageInputBits_eq_false_false_tail]
  rw [show
      List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
          (false :: false ::
            DovetailInitialLayoutInitializer.stageInputSecondBitTail
              w stage) =
        List.append
          (List.append
            (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
            [false, false])
          (DovetailInitialLayoutInitializer.stageInputSecondBitTail
            w stage) by
      simp [encodeCodeSymbolAsInput]]
  simpa [List.map_append, List.append_assoc] using
    assemblySkeletonDescription_run_prefix_to_marked_tail
      (List.append
        (DovetailInitialLayoutInitializer.stageInputSecondBitTail
          w stage)
        sourceRestBits)

theorem assemblySkeletonDescription_run_prefix_to_stageInput_tail_cells
    (w : Word Bool) (stage : Nat)
    (sourceRestCells : List (Option Bool)) :
    ASM.runConfig 6
        (config ASM.start []
          (List.append
            (List.map some
              (List.append
                (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                (DovetailInitialLayoutInitializer.stageInputBits
                  w stage)))
            sourceRestCells)) =
      markedTailStartConfigWithBaseCells transitionPrefixLeftTail
        (List.append
          ((DovetailInitialLayoutInitializer.stageInputSecondBitTail
            w stage).map some)
          sourceRestCells) := by
  rw [DovetailInitialLayoutInitializer.stageInputBits_eq_false_false_tail]
  rw [show
      List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
          (false :: false ::
            DovetailInitialLayoutInitializer.stageInputSecondBitTail
              w stage) =
        List.append
          (List.append
            (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
            [false, false])
          (DovetailInitialLayoutInitializer.stageInputSecondBitTail
            w stage) by
      simp [encodeCodeSymbolAsInput]]
  simpa [List.map_append, List.append_assoc] using
    assemblySkeletonDescription_run_prefix_to_marked_tail_cells
      (List.append
        ((DovetailInitialLayoutInitializer.stageInputSecondBitTail
          w stage).map some)
        sourceRestCells)

theorem assemblyPrefixDescription_run_prefix_to_marked_tail
    (tail : Word Bool) :
    AP.runConfig 6
        (config AP.start []
          (List.append
            (List.map some
              (List.append
                (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                [false, false]))
            (tail.map some))) =
      markedTailStartConfigWithBase transitionPrefixLeftTail tail := by
  cases tail <;>
    simp [AP, AssemblyPrefixDescription,
      SIMS,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      markedTailStartConfigWithBase, transitionPrefixLeftTail,
      encodeCodeSymbolAsInput, config, tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem assemblyPrefixDescription_run_prefix_to_marked_tail_cells
    (tailCells : List (Option Bool)) :
    AP.runConfig 6
        (config AP.start []
          (List.append
            (List.map some
              (List.append
                (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                [false, false]))
            tailCells)) =
      markedTailStartConfigWithBaseCells transitionPrefixLeftTail
        tailCells := by
  cases tailCells <;>
    simp [AP, AssemblyPrefixDescription,
      SIMS,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      markedTailStartConfigWithBaseCells, transitionPrefixLeftTail,
      encodeCodeSymbolAsInput, config, tapeAtCells,
      runConfig, stepConfig, lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveRight]

theorem assemblyPrefixDescription_run_prefix_to_stageInput_tail_cells
    (w : Word Bool) (stage : Nat)
    (sourceRestCells : List (Option Bool)) :
    AP.runConfig 6
        (config AP.start []
          (List.append
            (List.map some
              (List.append
                (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                (DovetailInitialLayoutInitializer.stageInputBits
                  w stage)))
            sourceRestCells)) =
      markedTailStartConfigWithBaseCells transitionPrefixLeftTail
        (List.append
          ((DovetailInitialLayoutInitializer.stageInputSecondBitTail
            w stage).map some)
          sourceRestCells) := by
  rw [DovetailInitialLayoutInitializer.stageInputBits_eq_false_false_tail]
  rw [show
      List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
          (false :: false ::
            DovetailInitialLayoutInitializer.stageInputSecondBitTail
              w stage) =
        List.append
          (List.append
            (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
            [false, false])
          (DovetailInitialLayoutInitializer.stageInputSecondBitTail
            w stage) by
      simp [encodeCodeSymbolAsInput]]
  simpa [List.map_append, List.append_assoc] using
    assemblyPrefixDescription_run_prefix_to_marked_tail_cells
      (List.append
        ((DovetailInitialLayoutInitializer.stageInputSecondBitTail
          w stage).map some)
        sourceRestCells)

theorem assemblyPrefixDescription_run_prefix_to_stageInput_tail
    (w : Word Bool) (stage : Nat) (sourceRestBits : Word Bool) :
    AP.runConfig 6
        (config AP.start []
          (List.append
            (List.map some
              (List.append
                (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                (DovetailInitialLayoutInitializer.stageInputBits
                  w stage)))
            (sourceRestBits.map some))) =
      markedTailStartConfigWithBase transitionPrefixLeftTail
        (List.append
          (DovetailInitialLayoutInitializer.stageInputSecondBitTail
            w stage)
          sourceRestBits) := by
  rw [DovetailInitialLayoutInitializer.stageInputBits_eq_false_false_tail]
  rw [show
      List.append
          (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
          (false :: false ::
            DovetailInitialLayoutInitializer.stageInputSecondBitTail
              w stage) =
        List.append
          (List.append
            (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
            [false, false])
          (DovetailInitialLayoutInitializer.stageInputSecondBitTail
            w stage) by
      simp [encodeCodeSymbolAsInput]]
  simpa [List.map_append, List.append_assoc] using
    assemblyPrefixDescription_run_prefix_to_marked_tail
      (List.append
        (DovetailInitialLayoutInitializer.stageInputSecondBitTail
          w stage)
        sourceRestBits)

theorem assemblySkeletonDescription_run_marked_tail_done_stageNat_to_state200_withBase
    (stage : Nat) (suffixBits : Word Bool)
    (leftTail : List (Option Bool)) :
    ASM.runConfig 18
        (markedTailStartConfigWithBase leftTail
          (true :: true ::
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage)
              suffixBits)) =
      config 200
        (List.append [some true, some true, none, some false]
          leftTail)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)
          (suffixBits.map some)) := by
  cases stage <;>
    simp [ASM, AssemblySkeletonDescription, markedTailStartConfigWithBase,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits,
      encodeNat, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem assemblyPrefixDescription_run_marked_tail_done_stageNat_to_state200_withBase
    (stage : Nat) (suffixBits : Word Bool)
    (leftTail : List (Option Bool)) :
    AP.runConfig 18
        (markedTailStartConfigWithBase leftTail
          (true :: true ::
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage)
              suffixBits)) =
      config 200
        (List.append [some true, some true, none, some false]
          leftTail)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)
          (suffixBits.map some)) := by
  cases stage <;>
    simp [AP, AssemblyPrefixDescription, markedTailStartConfigWithBase,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits,
      encodeNat, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem assemblyPrefixDescription_run_marked_tail_done_stageNat_to_state200_withBase_cells
    (stage : Nat) (suffixCells : List (Option Bool))
    (leftTail : List (Option Bool)) :
    AP.runConfig 18
        (markedTailStartConfigWithBaseCells leftTail
          (List.append
            ((true :: true ::
              DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some)
            suffixCells)) =
      config 200
        (List.append [some true, some true, none, some false]
          leftTail)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)
          suffixCells) := by
  cases stage <;>
    cases suffixCells <;>
    simp [AP, AssemblyPrefixDescription, markedTailStartConfigWithBaseCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits,
      encodeNat, encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem assemblySkeletonDescription_run_marked_tail_tick_to_state120_withBase
    (bits : Word Bool) (leftTail : List (Option Bool)) :
    ASM.runConfig 6
        (markedTailStartConfigWithBase leftTail
          (true :: false :: bits)) =
      config 120
        (List.append [none, some true, none, some false] leftTail)
        (bits.map some) := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · simp [markedTailStartConfigWithBase,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
    generalize bits.map some = cells
    cases cells <;> rfl
  · simp [markedTailStartConfigWithBase, SIMS,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_marked_tail_tick_to_state120_withBase_cells
    (tailCells : List (Option Bool)) (leftTail : List (Option Bool)) :
    ASM.runConfig 6
        (markedTailStartConfigWithBaseCells leftTail
          (some true :: some false :: tailCells)) =
      config 120
        (List.append [none, some true, none, some false] leftTail)
        tailCells := by
  cases tailCells <;>
    simp [ASM, AssemblySkeletonDescription, markedTailStartConfigWithBaseCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem assemblyPrefixDescription_run_marked_tail_tick_to_state120_withBase_cells
    (tailCells : List (Option Bool)) (leftTail : List (Option Bool)) :
    AP.runConfig 6
        (markedTailStartConfigWithBaseCells leftTail
          (some true :: some false :: tailCells)) =
      config 120
        (List.append [none, some true, none, some false] leftTail)
        tailCells := by
  cases tailCells <;>
    simp [AP, AssemblyPrefixDescription, markedTailStartConfigWithBaseCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem assemblySkeletonDescription_run_state200_tick
    (left right : List (Option Bool)) :
    ASM.runConfig 4
        (config 200 left
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
              some)
            right)) =
      config 200
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.reverse.map
            some)
          left)
        right := by
  cases right <;>
    simp [ASM, AssemblySkeletonDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits,
      encodeCodeSymbolAsInput, config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblySkeletonDescription_run_state200_done_to_state210
    (left right : List (Option Bool)) :
    ASM.runConfig 4
        (config 200 left
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits.map
              some)
            right)) =
      config 210
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits.reverse.map
            some)
          left)
        right := by
  cases right <;>
    simp [ASM, AssemblySkeletonDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits,
      encodeCodeSymbolAsInput, config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblySkeletonDescription_run_state200_stageNat_to_state210
    (stage : Nat) (left right : List (Option Bool)) :
    ASM.runConfig (4 * stage + 4)
        (config 200 left
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).map some)
            right)) =
      config 210
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).reverse.map some)
          left)
        right := by
  induction stage generalizing left with
  | zero =>
      simpa [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_zero] using
        assemblySkeletonDescription_run_state200_done_to_state210
          left right
  | succ stage ih =>
      rw [show 4 * (stage + 1) + 4 = 4 + (4 * stage + 4) by
        omega]
      rw [runConfig_add]
      rw [show
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (stage + 1)).map some =
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
                some)
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some) by
          simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
            DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits,
            encodeCodeSymbolAsInput]]
      change
        ASM.runConfig (4 * stage + 4)
          (ASM.runConfig 4
            (config 200 left
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
                  some)
                (List.append
                  ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    stage).map some)
                  right)))) =
          config 210
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                (stage + 1)).reverse.map some)
              left)
            right
      rw [assemblySkeletonDescription_run_state200_tick]
      have h := ih
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.reverse.map
            some)
          left)
      simpa [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits,
        encodeCodeSymbolAsInput, List.reverse_append, List.map_append,
        List.append_assoc] using h

theorem assemblyPrefixDescription_run_state200_tick
    (left right : List (Option Bool)) :
    AP.runConfig 4
        (config 200 left
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
              some)
            right)) =
      config 200
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.reverse.map
            some)
          left)
        right := by
  cases right <;>
    simp [AP, AssemblyPrefixDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits,
      encodeCodeSymbolAsInput, config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblyPrefixDescription_run_state200_done_to_state210
    (left right : List (Option Bool)) :
    AP.runConfig 4
        (config 200 left
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits.map
              some)
            right)) =
      config 210
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits.reverse.map
            some)
          left)
        right := by
  cases right <;>
    simp [AP, AssemblyPrefixDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits,
      encodeCodeSymbolAsInput, config, tapeAtCells,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem assemblyPrefixDescription_run_state200_stageNat_to_state210
    (stage : Nat) (left right : List (Option Bool)) :
    AP.runConfig (4 * stage + 4)
        (config 200 left
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).map some)
            right)) =
      config 210
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).reverse.map some)
          left)
        right := by
  induction stage generalizing left with
  | zero =>
      simpa [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_zero] using
        assemblyPrefixDescription_run_state200_done_to_state210
          left right
  | succ stage ih =>
      rw [show 4 * (stage + 1) + 4 = 4 + (4 * stage + 4) by
        omega]
      rw [runConfig_add]
      rw [show
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (stage + 1)).map some =
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
                some)
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some) by
          simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
            DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits,
            encodeCodeSymbolAsInput]]
      change
        AP.runConfig (4 * stage + 4)
          (AP.runConfig 4
            (config 200 left
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
                  some)
                (List.append
                  ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    stage).map some)
                  right)))) =
          config 210
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                (stage + 1)).reverse.map some)
              left)
            right
      rw [assemblyPrefixDescription_run_state200_tick]
      have h := ih
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.reverse.map
            some)
          left)
      simpa [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits,
        encodeCodeSymbolAsInput, List.reverse_append, List.map_append,
        List.append_assoc] using h

def finishStartConfigWithTailBitsAndBase
    (w tailBits : Word Bool) (leftTail : List (Option Bool)) :
    Configuration :=
  config 150
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishStartLeft
        w)
      leftTail)
    (List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
        w).map some)
      (tailBits.map some))

def markingState120WithTailBitsAndBase
    (processed : Word Bool) (b : Bool) (rest tailBits : Word Bool)
    (leftTail : List (Option Bool)) :
    Configuration :=
  config 120
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRev
        processed.length)
      leftTail)
    (List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        rest.length).map some)
      (List.append
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
          processed).map some)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
            b).map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
              rest).map some)
            (tailBits.map some)))))

def state100AfterMarkedWithTailBitsAndBase
    (processed : Word Bool) (b : Bool) (rest tailBits : Word Bool)
    (leftTail : List (Option Bool)) :
    Configuration :=
  config 100
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishLengthPrefixRev
        processed.length)
      leftTail)
    (List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        rest.length).map some)
      (List.append
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
          processed).map some)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellBits
            b).map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
              rest).map some)
            (tailBits.map some)))))

def finishStartConfigWithTailCellsAndBase
    (w : Word Bool) (tailCells leftTail : List (Option Bool)) :
    Configuration :=
  config 150
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishStartLeft
        w)
      leftTail)
    (List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
        w).map some)
      tailCells)

def markingState120WithTailCellsAndBase
    (processed : Word Bool) (b : Bool) (rest : Word Bool)
    (tailCells leftTail : List (Option Bool)) :
    Configuration :=
  config 120
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRev
        processed.length)
      leftTail)
    (List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        rest.length).map some)
      (List.append
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
          processed).map some)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
            b).map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
              rest).map some)
            tailCells))))

def state100AfterMarkedWithTailCellsAndBase
    (processed : Word Bool) (b : Bool) (rest : Word Bool)
    (tailCells leftTail : List (Option Bool)) :
    Configuration :=
  config 100
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishLengthPrefixRev
        processed.length)
      leftTail)
    (List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        rest.length).map some)
      (List.append
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
          processed).map some)
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellBits
            b).map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
              rest).map some)
            tailCells))))

theorem assemblySkeletonDescription_run_mark_current_to_state100_withBase
    (processed : Word Bool) (b : Bool) (rest tailBits : Word Bool)
    (leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (markingState120WithTailBitsAndBase
            processed b rest tailBits leftTail) =
        state100AfterMarkedWithTailBitsAndBase
          processed b rest tailBits leftTail := by
  let scanRev :=
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.markingReturnScanRev
      processed rest
  refine
    ⟨(4 * rest.length + 4) +
        (4 * processed.length + (6 + (scanRev.length + 4))), ?_⟩
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · rw [runConfig_add]
    unfold markingState120WithTailBitsAndBase
    rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state120_stageNat]
    rw [runConfig_add]
    rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state130_markedCells]
    rw [runConfig_add]
    rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state130_currentCell]
    have hreturn :=
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state140_returnToLengthMarker
        scanRev b
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixTail
            processed.length)
          leftTail)
        (some (!b) ::
          List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
              rest).map some)
            (tailBits.map some))
    have hprefix :
        some false :: some true ::
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixTail
                processed.length)
              leftTail =
          List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishLengthPrefixRev
              processed.length)
            leftTail := by
      have h :=
        congrArg (fun xs => List.append xs leftTail)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRestored
            processed.length)
      simpa [List.append_assoc] using h
    rw [hprefix] at hreturn
    cases b <;>
    simpa [state100AfterMarkedWithTailBitsAndBase, scanRev,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.markingReturnScanRev,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRev,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRestored,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellBits,
      List.map_append, List.reverse_append, List.append_assoc]
      using hreturn
  · simp [markingState120WithTailBitsAndBase, config, SIMS,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_mark_current_to_state100_withBase_cells
    (processed : Word Bool) (b : Bool) (rest : Word Bool)
    (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (markingState120WithTailCellsAndBase
            processed b rest tailCells leftTail) =
        state100AfterMarkedWithTailCellsAndBase
          processed b rest tailCells leftTail := by
  let scanRev :=
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.markingReturnScanRev
      processed rest
  refine
    ⟨(4 * rest.length + 4) +
        (4 * processed.length + (6 + (scanRev.length + 4))), ?_⟩
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · rw [runConfig_add]
    unfold markingState120WithTailCellsAndBase
    rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state120_stageNat]
    rw [runConfig_add]
    rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state130_markedCells]
    rw [runConfig_add]
    rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state130_currentCell]
    have hreturn :=
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state140_returnToLengthMarker
        scanRev b
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixTail
            processed.length)
          leftTail)
        (some (!b) ::
          List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
              rest).map some)
            tailCells)
    have hprefix :
        some false :: some true ::
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixTail
                processed.length)
              leftTail =
          List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishLengthPrefixRev
              processed.length)
            leftTail := by
      have h :=
        congrArg (fun xs => List.append xs leftTail)
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRestored
            processed.length)
      simpa [List.append_assoc] using h
    rw [hprefix] at hreturn
    cases b <;>
    simpa [state100AfterMarkedWithTailCellsAndBase, scanRev,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.markingReturnScanRev,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRev,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRestored,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellBits,
      List.map_append, List.reverse_append, List.append_assoc]
      using hreturn
  · simp [markingState120WithTailCellsAndBase, config, SIMS,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_state100_tick
    (left tail : List (Option Bool)) :
    ASM.runConfig 4
        (config 100 left
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
              some)
            tail)) =
      config 120
        (List.append
          DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedTickRev
          left)
        tail := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · exact
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state100_tick
        left tail
  · simp [config, SIMS,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_state100_done
    (left tail : List (Option Bool)) :
    ASM.runConfig 4
        (config 100 left
          (List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits.map
              some)
            tail)) =
      config 150
        (List.append
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits.reverse.map
            some)
          left)
        tail := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · exact
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state100_done
        left tail
  · simp [config, SIMS,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_marking_loop_from_state120_withBase
    (processed : Word Bool) (b : Bool) (rest tailBits : Word Bool)
    (leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (markingState120WithTailBitsAndBase
            processed b rest tailBits leftTail) =
        finishStartConfigWithTailBitsAndBase
          (List.append processed (b :: rest)) tailBits leftTail := by
  induction rest generalizing processed b with
  | nil =>
      rcases assemblySkeletonDescription_run_mark_current_to_state100_withBase
          processed b [] tailBits leftTail with
        ⟨markSteps, hmark⟩
      refine ⟨markSteps + 4, ?_⟩
      rw [runConfig_add]
      rw [hmark]
      unfold state100AfterMarkedWithTailBitsAndBase
      change
        ASM.runConfig 4
            (config 100
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishLengthPrefixRev
                  processed.length)
                leftTail)
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits.map
                  some)
                (List.append
                  ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
                    processed).map some)
                  (List.append
                    ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellBits
                      b).map some)
                    (tailBits.map some))))) =
          finishStartConfigWithTailBitsAndBase
            (List.append processed [b]) tailBits leftTail
      rw [assemblySkeletonDescription_run_state100_done]
      unfold finishStartConfigWithTailBitsAndBase
      rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits_append_single_map]
      simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishStartLeft,
        List.length_append, List.append_assoc]
  | cons next rest ih =>
      rcases assemblySkeletonDescription_run_mark_current_to_state100_withBase
          processed b (next :: rest) tailBits leftTail with
        ⟨markSteps, hmark⟩
      rcases ih (List.append processed [b]) next with
        ⟨recSteps, hrec⟩
      refine ⟨markSteps + 4 + recSteps, ?_⟩
      rw [show markSteps + 4 + recSteps =
          markSteps + (4 + recSteps) by omega]
      rw [runConfig_add]
      rw [hmark]
      rw [runConfig_add]
      unfold state100AfterMarkedWithTailBitsAndBase
      rw [show
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (next :: rest).length).map some =
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
                some)
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                rest.length).map some) by
        simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
          DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits,
          encodeCodeSymbolAsInput]]
      change
        ASM.runConfig recSteps
            (ASM.runConfig 4
              (config 100
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishLengthPrefixRev
                    processed.length)
                  leftTail)
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
                    some)
                  (List.append
                    ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                      rest.length).map some)
                    (List.append
                      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
                        processed).map some)
                      (List.append
                        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellBits
                          b).map some)
                        (List.append
                          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                            (next :: rest)).map some)
                          (tailBits.map some)))))))) =
          finishStartConfigWithTailBitsAndBase
            (List.append processed (b :: next :: rest)) tailBits leftTail
      rw [assemblySkeletonDescription_run_state100_tick]
      unfold markingState120WithTailBitsAndBase at hrec
      rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits_append_single_map] at hrec
      simpa [DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRev_succ,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits_cons,
        List.length_append, List.map_append, List.append_assoc] using hrec

theorem assemblySkeletonDescription_run_marking_loop_from_state120_withBase_cells
    (processed : Word Bool) (b : Bool) (rest : Word Bool)
    (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (markingState120WithTailCellsAndBase
            processed b rest tailCells leftTail) =
        finishStartConfigWithTailCellsAndBase
          (List.append processed (b :: rest)) tailCells leftTail := by
  induction rest generalizing processed b with
  | nil =>
      rcases assemblySkeletonDescription_run_mark_current_to_state100_withBase_cells
          processed b [] tailCells leftTail with
        ⟨markSteps, hmark⟩
      refine ⟨markSteps + 4, ?_⟩
      rw [runConfig_add]
      rw [hmark]
      unfold state100AfterMarkedWithTailCellsAndBase
      change
        ASM.runConfig 4
            (config 100
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishLengthPrefixRev
                  processed.length)
                leftTail)
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.doneBits.map
                  some)
                (List.append
                  ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
                    processed).map some)
                  (List.append
                    ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellBits
                      b).map some)
                    tailCells)))) =
          finishStartConfigWithTailCellsAndBase
            (List.append processed [b]) tailCells leftTail
      rw [assemblySkeletonDescription_run_state100_done]
      unfold finishStartConfigWithTailCellsAndBase
      rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits_append_single_map]
      simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishStartLeft,
        List.length_append, List.append_assoc]
  | cons next rest ih =>
      rcases assemblySkeletonDescription_run_mark_current_to_state100_withBase_cells
          processed b (next :: rest) tailCells leftTail with
        ⟨markSteps, hmark⟩
      rcases ih (List.append processed [b]) next with
        ⟨recSteps, hrec⟩
      refine ⟨markSteps + 4 + recSteps, ?_⟩
      rw [show markSteps + 4 + recSteps =
          markSteps + (4 + recSteps) by omega]
      rw [runConfig_add]
      rw [hmark]
      rw [runConfig_add]
      unfold state100AfterMarkedWithTailCellsAndBase
      rw [show
          (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              (next :: rest).length).map some =
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
                some)
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                rest.length).map some) by
        simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
          DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits,
          encodeCodeSymbolAsInput]]
      change
        ASM.runConfig recSteps
            (ASM.runConfig 4
              (config 100
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishLengthPrefixRev
                    processed.length)
                  leftTail)
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.tickBits.map
                    some)
                  (List.append
                    ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                      rest.length).map some)
                    (List.append
                      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
                        processed).map some)
                      (List.append
                        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellBits
                          b).map some)
                        (List.append
                          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                            (next :: rest)).map some)
                          tailCells))))))) =
          finishStartConfigWithTailCellsAndBase
            (List.append processed (b :: next :: rest)) tailCells leftTail
      rw [assemblySkeletonDescription_run_state100_tick]
      unfold markingState120WithTailCellsAndBase at hrec
      rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits_append_single_map] at hrec
      simpa [DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRev_succ,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits_cons,
        List.length_append, List.map_append, List.append_assoc] using hrec

theorem assemblySkeletonDescription_run_state120_bool_tail_to_finish_withBase
    (b : Bool) (rest tailBits : Word Bool)
    (leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (config 120
            (List.append [none, some true, none, some false] leftTail)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                rest.length).map some)
              (List.append
                ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
                  b).map some)
                (List.append
                  ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                    rest).map some)
                  (tailBits.map some))))) =
        finishStartConfigWithTailBitsAndBase
          (b :: rest) tailBits leftTail := by
  rcases assemblySkeletonDescription_run_marking_loop_from_state120_withBase
      ([] : Word Bool) b rest tailBits leftTail with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [markingState120WithTailBitsAndBase,
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRev_zero]
    using hsteps

theorem assemblySkeletonDescription_run_state120_bool_tail_to_finish_withBase_cells
    (b : Bool) (rest : Word Bool) (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (config 120
            (List.append [none, some true, none, some false] leftTail)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                rest.length).map some)
              (List.append
                ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
                  b).map some)
                (List.append
                  ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                    rest).map some)
                  tailCells)))) =
        finishStartConfigWithTailCellsAndBase
          (b :: rest) tailCells leftTail := by
  rcases assemblySkeletonDescription_run_marking_loop_from_state120_withBase_cells
      ([] : Word Bool) b rest tailCells leftTail with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  simpa [markingState120WithTailCellsAndBase,
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.activeLengthPrefixRev_zero]
    using hsteps

def state160AfterRestoreWithTailBitsAndBase
    (w tailBits : Word Bool) (leftTail : List (Option Bool)) :
    Configuration :=
  config 160
    (List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
        w).reverse.map some)
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishStartLeft
          w)
        leftTail))
    (some false :: none :: tailBits.map some)

def appendBlankStartConfigWithTailBitsAndBase
    (w tailBits : Word Bool) (leftTail : List (Option Bool)) :
    Configuration :=
  config 180 (List.append [none, some false] leftTail)
    (List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
        w).map some)
      (some false :: none :: tailBits.map some))

def state160AfterRestoreWithTailCellsAndBase
    (w : Word Bool) (tailCells leftTail : List (Option Bool)) :
    Configuration :=
  config 160
    (List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
        w).reverse.map some)
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishStartLeft
          w)
        leftTail))
    (some false :: none :: tailCells)

def appendBlankStartConfigWithTailCellsAndBase
    (w : Word Bool) (tailCells leftTail : List (Option Bool)) :
    Configuration :=
  config 180 (List.append [none, some false] leftTail)
    (List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
        w).map some)
      (some false :: none :: tailCells))

theorem assemblySkeletonDescription_run_finish_restore_cells_tailBits_withBase
    (w tailBits : Word Bool) (leftTail : List (Option Bool)) :
    ASM.runConfig (4 * w.length + 2)
        (finishStartConfigWithTailBitsAndBase w
          (false :: false :: tailBits) leftTail) =
      state160AfterRestoreWithTailBitsAndBase w tailBits leftTail := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · rw [runConfig_add]
    change
      SIMS.runConfig 2
          (SIMS.runConfig (4 * w.length)
            (config 150
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishStartLeft
                  w)
                leftTail)
              (List.append
                ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
                  w).map some)
                (some false :: some false :: tailBits.map some)))) =
        state160AfterRestoreWithTailBitsAndBase w tailBits leftTail
    rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state150_markedCells]
    rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state150_to_state160]
    simp [state160AfterRestoreWithTailBitsAndBase]
  · simp [finishStartConfigWithTailBitsAndBase, config, SIMS,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_finish_restore_cells_tailCells_withBase
    (w : Word Bool) (tailCells leftTail : List (Option Bool)) :
    ASM.runConfig (4 * w.length + 2)
        (finishStartConfigWithTailCellsAndBase w
          (some false :: some false :: tailCells) leftTail) =
      state160AfterRestoreWithTailCellsAndBase w tailCells leftTail := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · rw [runConfig_add]
    change
      SIMS.runConfig 2
          (SIMS.runConfig (4 * w.length)
            (config 150
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishStartLeft
                  w)
                leftTail)
              (List.append
                ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.markedCellsBits
                  w).map some)
                (some false :: some false :: tailCells)))) =
        state160AfterRestoreWithTailCellsAndBase w tailCells leftTail
    rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state150_markedCells]
    rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state150_to_state160]
    simp [state160AfterRestoreWithTailCellsAndBase]
  · simp [finishStartConfigWithTailCellsAndBase, config, SIMS,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_state160_bits_to_boundary
    (bitsToRight : Word Bool) (boundary : Option Bool)
    (leftTail right : List (Option Bool)) :
    ASM.runConfig bitsToRight.length
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.state160ScanConfig
          bitsToRight boundary leftTail right) =
      config 160 leftTail
        (boundary ::
          List.append (bitsToRight.reverse.map some) right) := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · exact
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state160_bits_to_boundary
        bitsToRight boundary leftTail right
  · cases bitsToRight <;>
      simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.state160ScanConfig,
        config, SIMS,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_state160_none_to_state161
    (cell : Option Bool) (left right : List (Option Bool)) :
    ASM.runConfig 1
        (config 160 (cell :: left) (none :: right)) =
      config 161 left (cell :: none :: right) := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · exact
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state160_none_to_state161
        cell left right
  · simp [config, SIMS,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_state161_false_to_state170_withBase
    (left right : List (Option Bool)) :
    ASM.runConfig 1
        (config 161 left (some false :: right)) =
      config 170 (some false :: left) right := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · cases right <;>
      simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
        config, tapeAtCells,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  · simp [config, SIMS,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_state170_none_to_state180_withBase
    (left right : List (Option Bool)) :
    ASM.runConfig 1
        (config 170 (some false :: left) (none :: right)) =
      config 180 (none :: some false :: left) right := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · cases right <;>
      simp [DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription,
        config, tapeAtCells,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.keep,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.keepMove,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.writeMove,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelRestart,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.scanLeftToSentinelHalt,
        runConfig, stepConfig, lookupTransition, Matches, transition,
        Tape.read, Tape.write, Tape.move, Tape.moveRight]
  · simp [config, SIMS,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_finish_scan_left_to_append_tailBits_withBase
    (b : Bool) (rest tailBits : Word Bool)
    (leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (state160AfterRestoreWithTailBitsAndBase
            (b :: rest) tailBits leftTail) =
        appendBlankStartConfigWithTailBitsAndBase
          (b :: rest) tailBits leftTail := by
  let bits :=
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishScanBits
      (b :: rest)
  let scanRight := none :: tailBits.map some
  have hstart :
      state160AfterRestoreWithTailBitsAndBase
          (b :: rest) tailBits leftTail =
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.state160ScanConfig
          bits none (some false :: leftTail) scanRight := by
    cases b <;>
    simp [bits, scanRight,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishScanBits,
      state160AfterRestoreWithTailBitsAndBase,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishStartLeft,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishLengthPrefixRev_eq_scanBits,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.state160ScanConfig,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits_cons,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits,
      List.map_append, List.reverse_append, List.append_assoc]
  refine ⟨bits.length + 3, ?_⟩
  rw [show bits.length + 3 = bits.length + (1 + (1 + 1)) by
    omega]
  rw [runConfig_add]
  rw [hstart]
  rw [assemblySkeletonDescription_run_state160_bits_to_boundary]
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_state160_none_to_state161]
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_state161_false_to_state170_withBase]
  rw [assemblySkeletonDescription_run_state170_none_to_state180_withBase]
  simp [appendBlankStartConfigWithTailBitsAndBase, bits, scanRight,
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishScanBits_reverse_nonempty,
    List.map_append, List.append_assoc]

theorem assemblySkeletonDescription_run_finish_scan_left_to_append_tailCells_withBase
    (b : Bool) (rest : Word Bool) (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (state160AfterRestoreWithTailCellsAndBase
            (b :: rest) tailCells leftTail) =
        appendBlankStartConfigWithTailCellsAndBase
          (b :: rest) tailCells leftTail := by
  let bits :=
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishScanBits
      (b :: rest)
  let scanRight := none :: tailCells
  have hstart :
      state160AfterRestoreWithTailCellsAndBase
          (b :: rest) tailCells leftTail =
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.state160ScanConfig
          bits none (some false :: leftTail) scanRight := by
    cases b <;>
    simp [bits, scanRight,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishScanBits,
      state160AfterRestoreWithTailCellsAndBase,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishStartLeft,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishLengthPrefixRev_eq_scanBits,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.state160ScanConfig,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits_cons,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits,
      List.map_append, List.reverse_append, List.append_assoc]
  refine ⟨bits.length + 3, ?_⟩
  rw [show bits.length + 3 = bits.length + (1 + (1 + 1)) by
    omega]
  rw [runConfig_add]
  rw [hstart]
  rw [assemblySkeletonDescription_run_state160_bits_to_boundary]
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_state160_none_to_state161]
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_state161_false_to_state170_withBase]
  rw [assemblySkeletonDescription_run_state170_none_to_state180_withBase]
  simp [appendBlankStartConfigWithTailCellsAndBase, bits, scanRight,
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.finishScanBits_reverse_nonempty,
    List.map_append, List.append_assoc]

theorem assemblySkeletonDescription_run_state180_some
    (b : Bool) (left right : List (Option Bool)) :
    ASM.runConfig 1
        (config 180 left (some b :: right)) =
      config 180 (some b :: left) right := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · exact
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state180_some
        b left right
  · simp [config, SIMS,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_state180_bits
    (bits : Word Bool) (left right : List (Option Bool)) :
    ASM.runConfig bits.length
        (config 180 left (List.append (bits.map some) right)) =
      config 180
        (List.append (bits.reverse.map some) left) right := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · exact
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state180_bits
        bits left right
  · cases bits <;>
      simp [config, SIMS,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_state180_none_cons
    (cell : Option Bool) (left right : List (Option Bool)) :
    ASM.runConfig 1
        (config 180 (cell :: left) (none :: right)) =
      config 200 left (cell :: some false :: right) := by
  rw [assemblySkeletonDescription_runConfig_eq_scanner]
  · exact
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.run_state180_none_cons
        cell left right
  · simp [config, SIMS,
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.StageInputMarkedScannerDescription]

theorem assemblySkeletonDescription_run_append_blank_to_state200_tailBits_withBase
    (b : Bool) (rest tailBits : Word Bool)
    (leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (appendBlankStartConfigWithTailBitsAndBase
            (b :: rest) tailBits leftTail) =
        config 200
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
              (b :: rest)).reverse.map some)
            (none :: some false :: leftTail))
          (some false :: some false :: tailBits.map some) := by
  let tailPrefix :=
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
      (b :: rest)
  refine ⟨tailPrefix.length + 2, ?_⟩
  rw [show tailPrefix.length + 2 = tailPrefix.length + (1 + 1) by
    omega]
  rw [runConfig_add]
  unfold appendBlankStartConfigWithTailBitsAndBase
  change
    ASM.runConfig (1 + 1)
        (ASM.runConfig tailPrefix.length
          (config 180 (List.append [none, some false] leftTail)
            (List.append (tailPrefix.map some)
              (some false :: none :: tailBits.map some)))) =
      config 200
        (List.append (tailPrefix.reverse.map some)
          (none :: some false :: leftTail))
        (some false :: some false :: tailBits.map some)
  rw [assemblySkeletonDescription_run_state180_bits]
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_state180_some]
  rw [assemblySkeletonDescription_run_state180_none_cons]
  simp

theorem assemblySkeletonDescription_run_append_blank_to_state200_tailCells_withBase
    (b : Bool) (rest : Word Bool) (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (appendBlankStartConfigWithTailCellsAndBase
            (b :: rest) tailCells leftTail) =
        config 200
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
              (b :: rest)).reverse.map some)
            (none :: some false :: leftTail))
          (some false :: some false :: tailCells) := by
  let tailPrefix :=
    DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
      (b :: rest)
  refine ⟨tailPrefix.length + 2, ?_⟩
  rw [show tailPrefix.length + 2 = tailPrefix.length + (1 + 1) by
    omega]
  rw [runConfig_add]
  unfold appendBlankStartConfigWithTailCellsAndBase
  change
    ASM.runConfig (1 + 1)
        (ASM.runConfig tailPrefix.length
          (config 180 (List.append [none, some false] leftTail)
            (List.append (tailPrefix.map some)
              (some false :: none :: tailCells)))) =
      config 200
        (List.append (tailPrefix.reverse.map some)
          (none :: some false :: leftTail))
        (some false :: some false :: tailCells)
  rw [assemblySkeletonDescription_run_state180_bits]
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_state180_some]
  rw [assemblySkeletonDescription_run_state180_none_cons]
  simp

theorem assemblySkeletonDescription_run_finish_tail_false_false_to_state200_withBase
    (b : Bool) (rest tailBits : Word Bool)
    (leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (finishStartConfigWithTailBitsAndBase
            (b :: rest) (false :: false :: tailBits) leftTail) =
        config 200
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
              (b :: rest)).reverse.map some)
            (none :: some false :: leftTail))
          (some false :: some false :: tailBits.map some) := by
  rcases assemblySkeletonDescription_run_finish_scan_left_to_append_tailBits_withBase
      b rest tailBits leftTail with
    ⟨scanSteps, hscan⟩
  rcases assemblySkeletonDescription_run_append_blank_to_state200_tailBits_withBase
      b rest tailBits leftTail with
    ⟨appendSteps, happend⟩
  refine
    ⟨(4 * (b :: rest).length + 2) + scanSteps + appendSteps, ?_⟩
  rw [show
      (4 * (b :: rest).length + 2) + scanSteps + appendSteps =
        (4 * (b :: rest).length + 2) +
          (scanSteps + appendSteps) by
    omega]
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_finish_restore_cells_tailBits_withBase]
  rw [runConfig_add]
  rw [hscan]
  exact happend

theorem assemblySkeletonDescription_run_finish_cells_false_false_to_state200_withBase
    (b : Bool) (rest : Word Bool) (tailCells leftTail : List (Option Bool)) :
    exists steps : Nat,
      ASM.runConfig steps
          (finishStartConfigWithTailCellsAndBase
            (b :: rest) (some false :: some false :: tailCells) leftTail) =
        config 200
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
              (b :: rest)).reverse.map some)
            (none :: some false :: leftTail))
          (some false :: some false :: tailCells) := by
  rcases assemblySkeletonDescription_run_finish_scan_left_to_append_tailCells_withBase
      b rest tailCells leftTail with
    ⟨scanSteps, hscan⟩
  rcases assemblySkeletonDescription_run_append_blank_to_state200_tailCells_withBase
      b rest tailCells leftTail with
    ⟨appendSteps, happend⟩
  refine
    ⟨(4 * (b :: rest).length + 2) + scanSteps + appendSteps, ?_⟩
  rw [show
      (4 * (b :: rest).length + 2) + scanSteps + appendSteps =
        (4 * (b :: rest).length + 2) +
          (scanSteps + appendSteps) by
    omega]
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_finish_restore_cells_tailCells_withBase]
  rw [runConfig_add]
  rw [hscan]
  exact happend

theorem assemblySkeletonDescription_run_empty_stageInput_to_sourceRest_boundary
    (stage : Nat) (sourceRestBits : Word Bool) :
    exists steps : Nat,
      ASM.runConfig steps
          (config ASM.start []
            (List.append
              (List.map some
                (List.append
                  (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                  (DovetailInitialLayoutInitializer.stageInputBits
                    ([] : Word Bool) stage)))
              (sourceRestBits.map some))) =
        config 210
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).reverse.map some)
            (List.append [some true, some true, none, some false]
              transitionPrefixLeftTail))
          (sourceRestBits.map some) := by
  refine ⟨6 + (18 + (4 * stage + 4)), ?_⟩
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_prefix_to_stageInput_tail]
  rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTail_nil]
  change
    ASM.runConfig (18 + (4 * stage + 4))
        (markedTailStartConfigWithBase transitionPrefixLeftTail
          (true :: true ::
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage)
              sourceRestBits)) =
      config 210
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).reverse.map some)
          (List.append [some true, some true, none, some false]
            transitionPrefixLeftTail))
        (sourceRestBits.map some)
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_marked_tail_done_stageNat_to_state200_withBase]
  rw [assemblySkeletonDescription_run_state200_stageNat_to_state210]

theorem assemblyPrefixDescription_run_empty_stageInput_to_sourceRest_boundary
    (stage : Nat) (sourceRestBits : Word Bool) :
    exists steps : Nat,
      AP.runConfig steps
          (config AP.start []
            (List.append
              (List.map some
                (List.append
                  (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                  (DovetailInitialLayoutInitializer.stageInputBits
                    ([] : Word Bool) stage)))
              (sourceRestBits.map some))) =
        config 210
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).reverse.map some)
            (List.append [some true, some true, none, some false]
              transitionPrefixLeftTail))
          (sourceRestBits.map some) := by
  refine ⟨6 + (18 + (4 * stage + 4)), ?_⟩
  rw [runConfig_add]
  rw [assemblyPrefixDescription_run_prefix_to_stageInput_tail]
  rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTail_nil]
  change
    AP.runConfig (18 + (4 * stage + 4))
        (markedTailStartConfigWithBase transitionPrefixLeftTail
          (true :: true ::
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage)
              sourceRestBits)) =
      config 210
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).reverse.map some)
          (List.append [some true, some true, none, some false]
            transitionPrefixLeftTail))
        (sourceRestBits.map some)
  rw [runConfig_add]
  rw [assemblyPrefixDescription_run_marked_tail_done_stageNat_to_state200_withBase]
  rw [assemblyPrefixDescription_run_state200_stageNat_to_state210]

theorem assemblyPrefixDescription_run_empty_stageInput_to_sourceRest_boundary_cells
    (stage : Nat) (sourceRestCells : List (Option Bool)) :
    exists steps : Nat,
      AP.runConfig steps
          (config AP.start []
            (List.append
              (List.map some
                (List.append
                  (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                  (DovetailInitialLayoutInitializer.stageInputBits
                    ([] : Word Bool) stage)))
              sourceRestCells)) =
        config 210
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).reverse.map some)
            (List.append [some true, some true, none, some false]
              transitionPrefixLeftTail))
          sourceRestCells := by
  refine ⟨6 + (18 + (4 * stage + 4)), ?_⟩
  rw [runConfig_add]
  rw [assemblyPrefixDescription_run_prefix_to_stageInput_tail_cells]
  rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTail_nil]
  change
    AP.runConfig (18 + (4 * stage + 4))
        (markedTailStartConfigWithBaseCells transitionPrefixLeftTail
          (List.append
            ((true :: true ::
              DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                stage).map some)
            sourceRestCells)) =
      config 210
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).reverse.map some)
          (List.append [some true, some true, none, some false]
            transitionPrefixLeftTail))
        sourceRestCells
  rw [runConfig_add]
  rw [assemblyPrefixDescription_run_marked_tail_done_stageNat_to_state200_withBase_cells]
  rw [assemblyPrefixDescription_run_state200_stageNat_to_state210]

theorem assemblySkeletonDescription_run_nonempty_stageInput_to_sourceRest_boundary
    (b : Bool) (rest : Word Bool) (stage : Nat)
    (sourceRestBits : Word Bool) :
    exists steps : Nat,
      ASM.runConfig steps
          (config ASM.start []
            (List.append
              (List.map some
                (List.append
                  (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                  (DovetailInitialLayoutInitializer.stageInputBits
                    (b :: rest) stage)))
              (sourceRestBits.map some))) =
        config 210
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              stage).reverse.map some)
            (List.append
              ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
                (b :: rest)).reverse.map some)
              (List.append [none, some false] transitionPrefixLeftTail)))
          (sourceRestBits.map some) := by
  rcases
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_false_false_tail
        stage with
    ⟨stageTail, hstageTail⟩
  rcases assemblySkeletonDescription_run_state120_bool_tail_to_finish_withBase
      b rest
      (List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage)
        sourceRestBits)
      transitionPrefixLeftTail with
    ⟨markSteps, hmark⟩
  rcases assemblySkeletonDescription_run_finish_tail_false_false_to_state200_withBase
      b rest
      (List.append stageTail sourceRestBits)
      transitionPrefixLeftTail with
    ⟨finishSteps, hfinish⟩
  refine
    ⟨6 + (6 + (markSteps + finishSteps + (4 * stage + 4))), ?_⟩
  rw [show
      6 + (6 + (markSteps + finishSteps + (4 * stage + 4))) =
        6 + (6 + (markSteps + (finishSteps + (4 * stage + 4)))) by
    omega]
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_prefix_to_stageInput_tail]
  rw [DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTail_cons]
  rw [show
      List.append
          (true :: false ::
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                rest.length)
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
                  b)
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                    rest)
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    stage))))
          sourceRestBits =
        true :: false ::
          List.append
            (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
              rest.length)
            (List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
                b)
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                  rest)
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                    stage)
                  sourceRestBits))) by
    simp [List.append_assoc]]
  change
    ASM.runConfig (6 + (markSteps + (finishSteps + (4 * stage + 4))))
        (markedTailStartConfigWithBase transitionPrefixLeftTail
          (true :: false ::
            List.append
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                rest.length)
              (List.append
                (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellBits
                  b)
                (List.append
                  (DovetailInitialLayoutInitializer.StageInputMarkedScanner.cellsBits
                    rest)
                  (List.append
                    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
                      stage)
                    sourceRestBits))))) =
      config 210
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).reverse.map some)
          (List.append
            ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
              (b :: rest)).reverse.map some)
            (List.append [none, some false] transitionPrefixLeftTail)))
        (sourceRestBits.map some)
  rw [runConfig_add]
  rw [assemblySkeletonDescription_run_marked_tail_tick_to_state120_withBase]
  rw [runConfig_add]
  simp [List.map_append] at hmark ⊢
  rw [hmark]
  rw [hstageTail]
  rw [runConfig_add]
  change
    ASM.runConfig (4 * stage + 4)
        (ASM.runConfig finishSteps
          (finishStartConfigWithTailBitsAndBase
            (b :: rest) (false :: false :: List.append stageTail sourceRestBits)
            transitionPrefixLeftTail)) =
      config 210
        (List.append
          ((List.map some (false :: false :: stageTail)).reverse)
          (List.append
            ((List.map some
              (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageInputSecondBitTailPrefix
                (b :: rest))).reverse)
            (none :: some false :: transitionPrefixLeftTail)))
        (sourceRestBits.map some)
  rw [hfinish]
  rw [← hstageTail]
  have hright :
      some false :: some false ::
          List.map some (List.append stageTail sourceRestBits) =
        List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            stage).map some)
          (sourceRestBits.map some) := by
    rw [hstageTail]
    simp [List.map_append]
  rw [hright]
  rw [assemblySkeletonDescription_run_state200_stageNat_to_state210]
  simp

theorem assemblySkeletonDescription_run_stageInput_to_sourceRest_boundary
    (w : Word Bool) (stage : Nat) (sourceRestBits : Word Bool) :
    exists steps : Nat,
      ASM.runConfig steps
          (config ASM.start []
            (List.append
              (List.map some
                (List.append
                  (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                  (DovetailInitialLayoutInitializer.stageInputBits
                    w stage)))
              (sourceRestBits.map some))) =
        config 210
          (assemblySourceRestBoundaryLeftRev w stage)
          (sourceRestBits.map some) := by
  cases w with
  | nil =>
      simpa [assemblySourceRestBoundaryLeftRev] using
        assemblySkeletonDescription_run_empty_stageInput_to_sourceRest_boundary
          stage sourceRestBits
  | cons b rest =>
      simpa [assemblySourceRestBoundaryLeftRev] using
        assemblySkeletonDescription_run_nonempty_stageInput_to_sourceRest_boundary
          b rest stage sourceRestBits

end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
