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

theorem assemblySkeletonDescription_run_prefix_to_marked_tail_cells_withBase
    (leftBase tailCells : List (Option Bool)) :
    ASM.runConfig 6
        (config ASM.start leftBase
          (List.append
            (List.map some
              (List.append
                (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                [false, false]))
            tailCells)) =
      markedTailStartConfigWithBaseCells
        (List.append transitionPrefixLeftTail leftBase)
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

theorem assemblySkeletonDescription_run_prefix_to_stageInput_tail_cells_withBase
    (leftBase : List (Option Bool))
    (w : Word Bool) (stage : Nat)
    (sourceRestCells : List (Option Bool)) :
    ASM.runConfig 6
        (config ASM.start leftBase
          (List.append
            (List.map some
              (List.append
                (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                (DovetailInitialLayoutInitializer.stageInputBits
                  w stage)))
            sourceRestCells)) =
      markedTailStartConfigWithBaseCells
        (List.append transitionPrefixLeftTail leftBase)
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
    assemblySkeletonDescription_run_prefix_to_marked_tail_cells_withBase
      leftBase
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

theorem assemblyPrefixDescription_run_prefix_to_marked_tail_cells_withBase
    (leftBase tailCells : List (Option Bool)) :
    AP.runConfig 6
        (config AP.start leftBase
          (List.append
            (List.map some
              (List.append
                (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                [false, false]))
            tailCells)) =
      markedTailStartConfigWithBaseCells
        (List.append transitionPrefixLeftTail leftBase)
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

theorem assemblyPrefixDescription_run_prefix_to_stageInput_tail_cells_withBase
    (leftBase : List (Option Bool))
    (w : Word Bool) (stage : Nat)
    (sourceRestCells : List (Option Bool)) :
    AP.runConfig 6
        (config AP.start leftBase
          (List.append
            (List.map some
              (List.append
                (encodeCodeSymbolAsInput MachineCodeSymbol.transition)
                (DovetailInitialLayoutInitializer.stageInputBits
                  w stage)))
            sourceRestCells)) =
      markedTailStartConfigWithBaseCells
        (List.append transitionPrefixLeftTail leftBase)
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
    assemblyPrefixDescription_run_prefix_to_marked_tail_cells_withBase
      leftBase
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


end SelectedProjectionInputQuoterFiniteLeaf

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
