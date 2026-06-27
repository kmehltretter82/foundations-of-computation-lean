import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.TaggedBrancher

set_option doc.verso true

/-!
# HeadRouter

Router for the append-input head position and its dispatcher adapter.
-/


namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace DovetailInitialLayoutInitializer

def appendInputTapeHeadRouterTaggedTape
    (tag : Option Bool) (w : Word Bool) (stage : Nat)
    (suffixBits : Word Bool) : Tape Bool :=
  tapeAtCells [tag]
    (some false ::
      ((List.append [false, true]
        (List.append (stageInputBits w stage)
          suffixBits)).map some))

def AppendInputTapeHeadRouterDescription :
    MachineDescription where
  stateCount := 32
  start := 0
  halt := 31
  transitions :=
    [ transition
        0 (some false) none Direction.right 1
    , transition
        1 (some false) (some false) Direction.right 2
    , transition
        2 (some false) (some false) Direction.right 3
    , transition
        3 (some true) (some true) Direction.right 4
    , transition
        4 (some false) (some false) Direction.right 5
    , transition
        5 (some false) (some false) Direction.right 6
    , transition
        6 (some true) (some true) Direction.right 7
    , transition
        7 (some true) (some true) Direction.left 20
    , transition
        7 (some false) (some false) Direction.right 8
    , transition
        8 (some false) (some false) Direction.right 9
    , transition
        9 (some false) (some false) Direction.right 10
    , transition
        10 (some true) (some true) Direction.right 11
    , transition
        11 (some false) (some false) Direction.right 8
    , transition
        11 (some true) (some true) Direction.right 12
    , transition
        12 (some false) (some false) Direction.right 13
    , transition
        13 (some true) (some true) Direction.right 14
    , transition
        14 (some false) (some false) Direction.left 21
    , transition
        14 (some true) (some true) Direction.left 22
    , transition
        20 (some false) (some false) Direction.left 20
    , transition
        20 (some true) (some true) Direction.left 20
    , transition
        20 none none Direction.right 31
    , transition
        21 (some false) (some false) Direction.left 21
    , transition
        21 (some true) (some true) Direction.left 21
    , transition
        21 none (some false) Direction.right 31
    , transition
        22 (some false) (some false) Direction.left 22
    , transition
        22 (some true) (some true) Direction.left 22
    , transition
        22 none (some true) Direction.right 31
    , transition
        23 (some false) none Direction.right 31
    , transition
        24 (some false) (some false) Direction.right 31
    , transition
        25 (some false) (some true) Direction.right 31
    ]

theorem appendInputTapeHeadRouterDescription_wellFormed :
    AppendInputTapeHeadRouterDescription.WellFormed := by
  refine ⟨by native_decide, by native_decide, by native_decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := AppendInputTapeHeadRouterDescription.transitions)
      (stateCount :=
        AppendInputTapeHeadRouterDescription.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := AppendInputTapeHeadRouterDescription.transitions)
      (by native_decide)

theorem appendInputTapeHeadRouterDescription_haltTransitionFree :
    AppendInputTapeHeadRouterDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := AppendInputTapeHeadRouterDescription.transitions)
    (state := AppendInputTapeHeadRouterDescription.halt)
    (by native_decide)

theorem appendInputTapeHeadRouterDescription_subroutineReady :
    AppendInputTapeHeadRouterDescription.SubroutineReady :=
  ⟨appendInputTapeHeadRouterDescription_wellFormed,
    appendInputTapeHeadRouterDescription_haltTransitionFree⟩

theorem appendInputTapeHeadRouterDescription_run_return20
    (beforeRevBits : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    AppendInputTapeHeadRouterDescription.runConfig
        (beforeRevBits.length + 3)
        (config 20
          (List.append (beforeRevBits.map some)
            [some false, none])
          (some current :: right)) =
      config 31 [none]
        (some false ::
          List.append (beforeRevBits.reverse.map some)
            (some current :: right)) := by
  induction beforeRevBits generalizing current right with
  | nil =>
      cases current <;>
        simp [AppendInputTapeHeadRouterDescription,
          config, tapeAtCells,
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]
  | cons bit rest ih =>
      cases current
      · simpa [runConfig, config,
          tapeAtCells,
          AppendInputTapeHeadRouterDescription,
          stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, List.append_assoc] using
          ih bit (some false :: right)
      · simpa [runConfig, config,
          tapeAtCells,
          AppendInputTapeHeadRouterDescription,
          stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, List.append_assoc] using
          ih bit (some true :: right)
theorem appendInputTapeHeadRouterDescription_run_return21
    (beforeRevBits : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    AppendInputTapeHeadRouterDescription.runConfig
        (beforeRevBits.length + 3)
        (config 21
          (List.append (beforeRevBits.map some)
            [some false, none])
          (some current :: right)) =
      config 31 [some false]
        (some false ::
          List.append (beforeRevBits.reverse.map some)
            (some current :: right)) := by
  induction beforeRevBits generalizing current right with
  | nil =>
      cases current <;>
        simp [AppendInputTapeHeadRouterDescription,
          config, tapeAtCells,
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]
  | cons bit rest ih =>
      cases current
      · simpa [runConfig, config,
          tapeAtCells,
          AppendInputTapeHeadRouterDescription,
          stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, List.append_assoc] using
          ih bit (some false :: right)
      · simpa [runConfig, config,
          tapeAtCells,
          AppendInputTapeHeadRouterDescription,
          stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, List.append_assoc] using
          ih bit (some true :: right)
theorem appendInputTapeHeadRouterDescription_run_return22
    (beforeRevBits : Word Bool) (current : Bool)
    (right : List (Option Bool)) :
    AppendInputTapeHeadRouterDescription.runConfig
        (beforeRevBits.length + 3)
        (config 22
          (List.append (beforeRevBits.map some)
            [some false, none])
          (some current :: right)) =
      config 31 [some true]
        (some false ::
          List.append (beforeRevBits.reverse.map some)
            (some current :: right)) := by
  induction beforeRevBits generalizing current right with
  | nil =>
      cases current <;>
        simp [AppendInputTapeHeadRouterDescription,
          config, tapeAtCells,
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]
  | cons bit rest ih =>
      cases current
      · simpa [runConfig, config,
          tapeAtCells,
          AppendInputTapeHeadRouterDescription,
          stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, List.append_assoc] using
          ih bit (some false :: right)
      · simpa [runConfig, config,
          tapeAtCells,
          AppendInputTapeHeadRouterDescription,
          stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, List.append_assoc] using
          ih bit (some true :: right)

theorem appendInputTapeHeadRouterDescription_run_state8_false
    (n : Nat) (beforeRevBits tailBits : Word Bool) :
    AppendInputTapeHeadRouterDescription.runConfig
        (beforeRevBits.length + 8 * n + 15)
        (config 8
          (List.append (beforeRevBits.map some)
            [some false, none])
          ((List.append (natBits n)
            (false :: true :: false :: true :: tailBits)).map some)) =
      config 31 [some false]
        (some false ::
          (List.append beforeRevBits.reverse
            (List.append (natBits n)
              (false :: true :: false :: true :: tailBits))).map some) := by
  induction n generalizing beforeRevBits with
  | zero =>
      let nextBefore : Word Bool :=
        List.append [false, true, true, false, false] beforeRevBits
      have hprefix :
          AppendInputTapeHeadRouterDescription.runConfig 7
              (config 8
                (List.append (beforeRevBits.map some)
                  [some false, none])
                ((List.append (natBits 0)
                  (false :: true :: false :: true :: tailBits)).map some)) =
            config 21
              (List.append (nextBefore.map some) [some false, none])
              (some true :: some false :: some true ::
                tailBits.map some) := by
        simp [nextBefore,
          AppendInputTapeHeadRouterDescription,
          config, tapeAtCells,
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]
      rw [show beforeRevBits.length + 8 * 0 + 15 =
        7 + (nextBefore.length + 3) by
          simp [nextBefore]
          omega]
      rw [runConfig_add]
      rw [hprefix]
      simpa [nextBefore,
        List.map_append, List.reverse_append, List.append_assoc] using
        appendInputTapeHeadRouterDescription_run_return21
          nextBefore true (some false :: some true :: tailBits.map some)
  | succ n ih =>
      let nextBefore : Word Bool :=
        List.append [false, true, false, false] beforeRevBits
      have hprefix :
          AppendInputTapeHeadRouterDescription.runConfig 4
              (config 8
                (List.append (beforeRevBits.map some)
                  [some false, none])
                ((List.append (natBits (n + 1))
                  (false :: true :: false :: true :: tailBits)).map some)) =
            config 8
              (List.append (nextBefore.map some) [some false, none])
              ((List.append (natBits n)
                (false :: true :: false :: true :: tailBits)).map some) := by
        simp [nextBefore,
          AppendInputTapeHeadRouterDescription,
          config, tapeAtCells,
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight, List.map_append]
        cases
          List.map some (natBits n) ++
            some false :: some true :: some false :: some true ::
              List.map some tailBits <;>
          rfl
      rw [show beforeRevBits.length + 8 * (n + 1) + 15 =
        4 + (nextBefore.length + 8 * n + 15) by
          simp [nextBefore]
          omega]
      rw [runConfig_add]
      rw [hprefix]
      simpa [nextBefore,
        List.map_append, List.reverse_append, List.append_assoc,
        Nat.mul_succ] using
        ih nextBefore

theorem appendInputTapeHeadRouterDescription_run_state8_true
    (n : Nat) (beforeRevBits tailBits : Word Bool) :
    AppendInputTapeHeadRouterDescription.runConfig
        (beforeRevBits.length + 8 * n + 15)
        (config 8
          (List.append (beforeRevBits.map some)
            [some false, none])
          ((List.append (natBits n)
            (false :: true :: true :: false :: tailBits)).map some)) =
      config 31 [some true]
        (some false ::
          (List.append beforeRevBits.reverse
            (List.append (natBits n)
              (false :: true :: true :: false :: tailBits))).map some) := by
  induction n generalizing beforeRevBits with
  | zero =>
      let nextBefore : Word Bool :=
        List.append [false, true, true, false, false] beforeRevBits
      have hprefix :
          AppendInputTapeHeadRouterDescription.runConfig 7
              (config 8
                (List.append (beforeRevBits.map some)
                  [some false, none])
                ((List.append (natBits 0)
                  (false :: true :: true :: false :: tailBits)).map some)) =
            config 22
              (List.append (nextBefore.map some) [some false, none])
              (some true :: some true :: some false ::
                tailBits.map some) := by
        simp [nextBefore,
          AppendInputTapeHeadRouterDescription,
          config, tapeAtCells,
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]
      rw [show beforeRevBits.length + 8 * 0 + 15 =
        7 + (nextBefore.length + 3) by
          simp [nextBefore]
          omega]
      rw [runConfig_add]
      rw [hprefix]
      simpa [nextBefore,
        List.map_append, List.reverse_append, List.append_assoc] using
        appendInputTapeHeadRouterDescription_run_return22
          nextBefore true (some true :: some false :: tailBits.map some)
  | succ n ih =>
      let nextBefore : Word Bool :=
        List.append [false, true, false, false] beforeRevBits
      have hprefix :
          AppendInputTapeHeadRouterDescription.runConfig 4
              (config 8
                (List.append (beforeRevBits.map some)
                  [some false, none])
                ((List.append (natBits (n + 1))
                  (false :: true :: true :: false :: tailBits)).map some)) =
            config 8
              (List.append (nextBefore.map some) [some false, none])
              ((List.append (natBits n)
                (false :: true :: true :: false :: tailBits)).map some) := by
        simp [nextBefore,
          AppendInputTapeHeadRouterDescription,
          config, tapeAtCells,
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight, List.map_append]
        cases
          List.map some (natBits n) ++
            some false :: some true :: some true :: some false ::
              List.map some tailBits <;>
          rfl
      rw [show beforeRevBits.length + 8 * (n + 1) + 15 =
        4 + (nextBefore.length + 8 * n + 15) by
          simp [nextBefore]
          omega]
      rw [runConfig_add]
      rw [hprefix]
      simpa [nextBefore,
        List.map_append, List.reverse_append, List.append_assoc,
        Nat.mul_succ] using
        ih nextBefore

def AppendInputTapeHeadRouterSpec
    (router : MachineDescription) : Prop :=
  router.SubroutineReady ∧
    (forall stage : Nat,
     forall suffixBits : Word Bool,
      exists steps : Nat,
        router.runConfig steps
            { state := router.start
              tape :=
                tapeAtCells []
                  (some false :: some false ::
                    ((List.append [false, true]
                      (List.append
                        (stageInputBits ([] : Word Bool) stage)
                        suffixBits)).map some)) } =
          { state := router.halt
            tape :=
              appendInputTapeHeadRouterTaggedTape
                none ([] : Word Bool) stage suffixBits }) ∧
    (forall b : Bool,
     forall rest : Word Bool,
     forall stage : Nat,
     forall suffixBits : Word Bool,
      exists steps : Nat,
        router.runConfig steps
            { state := router.start
              tape :=
                tapeAtCells []
                  (some false :: some false ::
                    ((List.append [false, true]
                      (List.append
                        (stageInputBits (b :: rest) stage)
                        suffixBits)).map some)) } =
          { state := router.halt
            tape :=
              appendInputTapeHeadRouterTaggedTape
                (some b) (b :: rest) stage suffixBits })
theorem appendInputTapeHeadRouterDescription_spec :
    AppendInputTapeHeadRouterSpec
      AppendInputTapeHeadRouterDescription := by
  constructor
  · exact appendInputTapeHeadRouterDescription_subroutineReady
  constructor
  · intro stage suffixBits
    refine ⟨15, ?_⟩
    simp [appendInputTapeHeadRouterTaggedTape,
      stageInputBits, PairedRecognizerDovetailStageInputCode,
      DovetailLayout.stageInputCode,
      DovetailLayout.stageInputCodeAppend,
      encodeBoolWordAppend,
      encodeCellListAppend,
      encodeNatAppend,
      encodeNat,
      encodeCellsAppend,
      encodeCodeWordAsInput,
      encodeCodeSymbolAsInput,
      AppendInputTapeHeadRouterDescription,
      tapeAtCells,
      runConfig, stepConfig,
      lookupTransition, Matches,
      transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]
  · intro b rest stage suffixBits
    cases b
    · let beforeRevBits : Word Bool :=
        [false, true, false, false, true, false]
      let tailBits : Word Bool :=
        List.append
          (encodeCodeWordAsInput
            (encodeCellsAppend (rest.map some)
              (encodeNatAppend stage [])))
          suffixBits
      let rawCells : List (Option Bool) :=
        List.append
          (List.map some
            (encodeCodeWordAsInput
              (List.append (encodeNat rest.length)
                (MachineCodeSymbol.zero ::
                  encodeCellsAppend (rest.map some)
                    (encodeNat stage)))))
          (List.map some suffixBits)
      refine ⟨8 * rest.length + 29, ?_⟩
      have hprefix :
          AppendInputTapeHeadRouterDescription.runConfig 8
              { state := AppendInputTapeHeadRouterDescription.start
                tape :=
                  tapeAtCells []
                    (some false :: some false ::
                      ((List.append [false, true]
                        (List.append
                          (stageInputBits (false :: rest) stage)
                          suffixBits)).map some)) } =
            config 8
              (List.append (beforeRevBits.map some) [some false, none])
              rawCells := by
        simp [beforeRevBits, rawCells,
          stageInputBits, PairedRecognizerDovetailStageInputCode,
          DovetailLayout.stageInputCode,
          DovetailLayout.stageInputCodeAppend,
          encodeBoolWordAppend,
          encodeCellListAppend,
          encodeNatAppend,
          encodeNat,
          encodeCellsAppend,
          encodeCellAppend,
          encodeCell,
          AppendInputTapeHeadRouterDescription,
          config, tapeAtCells,
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight, List.map_append]
        cases
          (List.map some
            (encodeCodeWordAsInput
              (List.append (encodeNat rest.length)
                (MachineCodeSymbol.zero ::
                  encodeCellsAppend (rest.map some)
                    (encodeNat stage)))) ++
            List.map some suffixBits) <;>
          rfl
      have hcells :
          rawCells =
            ((List.append (natBits rest.length)
              (false :: true :: false :: true :: tailBits)).map some) := by
        simpa [rawCells, tailBits, encodeNatAppend,
          List.map_append, List.append_assoc] using
          natBits_map_append_cell_false rest.length
            (encodeCellsAppend (rest.map some)
              (encodeNat stage))
            suffixBits
      rw [show 8 * rest.length + 29 =
        8 + (beforeRevBits.length + 8 * rest.length + 15) by
          simp [beforeRevBits]
          omega]
      rw [runConfig_add]
      rw [hprefix]
      have hscan :=
        appendInputTapeHeadRouterDescription_run_state8_false
          rest.length beforeRevBits tailBits
      rw [← hcells] at hscan
      have htailRaw :
          List.map some (natBits rest.length) ++
              some false :: some true :: some false :: some true ::
                List.map some tailBits =
            rawCells := by
        simpa [List.map_append, List.append_assoc] using hcells.symm
      simpa [beforeRevBits, rawCells, htailRaw,
        appendInputTapeHeadRouterTaggedTape,
        stageInputBits, PairedRecognizerDovetailStageInputCode,
        DovetailLayout.stageInputCode,
        DovetailLayout.stageInputCodeAppend,
        encodeBoolWordAppend,
        encodeCellListAppend,
        encodeNatAppend,
        encodeNat,
        encodeCellsAppend,
        encodeCellAppend,
        encodeCell,
        List.map_append, List.reverse_append, List.append_assoc] using
        hscan
    · let beforeRevBits : Word Bool :=
        [false, true, false, false, true, false]
      let tailBits : Word Bool :=
        List.append
          (encodeCodeWordAsInput
            (encodeCellsAppend (rest.map some)
              (encodeNatAppend stage [])))
          suffixBits
      let rawCells : List (Option Bool) :=
        List.append
          (List.map some
            (encodeCodeWordAsInput
              (List.append (encodeNat rest.length)
                (MachineCodeSymbol.one ::
                  encodeCellsAppend (rest.map some)
                    (encodeNat stage)))))
          (List.map some suffixBits)
      refine ⟨8 * rest.length + 29, ?_⟩
      have hprefix :
          AppendInputTapeHeadRouterDescription.runConfig 8
              { state := AppendInputTapeHeadRouterDescription.start
                tape :=
                  tapeAtCells []
                    (some false :: some false ::
                      ((List.append [false, true]
                        (List.append
                          (stageInputBits (true :: rest) stage)
                          suffixBits)).map some)) } =
            config 8
              (List.append (beforeRevBits.map some) [some false, none])
              rawCells := by
        simp [beforeRevBits, rawCells,
          stageInputBits, PairedRecognizerDovetailStageInputCode,
          DovetailLayout.stageInputCode,
          DovetailLayout.stageInputCodeAppend,
          encodeBoolWordAppend,
          encodeCellListAppend,
          encodeNatAppend,
          encodeNat,
          encodeCellsAppend,
          encodeCellAppend,
          encodeCell,
          AppendInputTapeHeadRouterDescription,
          config, tapeAtCells,
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight, List.map_append]
        cases
          (List.map some
            (encodeCodeWordAsInput
              (List.append (encodeNat rest.length)
                (MachineCodeSymbol.one ::
                  encodeCellsAppend (rest.map some)
                    (encodeNat stage)))) ++
            List.map some suffixBits) <;>
          rfl
      have hcells :
          rawCells =
            ((List.append (natBits rest.length)
              (false :: true :: true :: false :: tailBits)).map some) := by
        simpa [rawCells, tailBits, encodeNatAppend,
          List.map_append, List.append_assoc] using
          natBits_map_append_cell_true rest.length
            (encodeCellsAppend (rest.map some)
              (encodeNat stage))
            suffixBits
      rw [show 8 * rest.length + 29 =
        8 + (beforeRevBits.length + 8 * rest.length + 15) by
          simp [beforeRevBits]
          omega]
      rw [runConfig_add]
      rw [hprefix]
      have hscan :=
        appendInputTapeHeadRouterDescription_run_state8_true
          rest.length beforeRevBits tailBits
      rw [← hcells] at hscan
      have htailRaw :
          List.map some (natBits rest.length) ++
              some false :: some true :: some true :: some false ::
                List.map some tailBits =
            rawCells := by
        simpa [List.map_append, List.append_assoc] using hcells.symm
      simpa [beforeRevBits, rawCells, htailRaw,
        appendInputTapeHeadRouterTaggedTape,
        stageInputBits, PairedRecognizerDovetailStageInputCode,
        DovetailLayout.stageInputCode,
        DovetailLayout.stageInputCodeAppend,
        encodeBoolWordAppend,
        encodeCellListAppend,
        encodeNatAppend,
        encodeNat,
        encodeCellsAppend,
        encodeCellAppend,
        encodeCell,
        List.map_append, List.reverse_append, List.append_assoc] using
        hscan

def AppendInputTapeHeadTaggedBrancherSpec
    (brancher : MachineDescription) : Prop :=
  brancher.SubroutineReady ∧
    (forall stage : Nat,
     forall suffixBits : Word Bool,
      exists steps : Nat,
        brancher.runConfig steps
            { state := brancher.start
              tape :=
                Tape.move Direction.left
                  (appendInputTapeHeadRouterTaggedTape
                    none ([] : Word Bool) stage suffixBits) } =
          { state := brancher.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits ([] : Word Bool) stage)
                      (List.append suffixBits
                        (inputTapeBits ([] : Word Bool))))).map
                    some)) }) ∧
    (forall b : Bool,
     forall rest : Word Bool,
     forall stage : Nat,
     forall suffixBits : Word Bool,
      exists steps : Nat,
        brancher.runConfig steps
            { state := brancher.start
              tape :=
                Tape.move Direction.left
                  (appendInputTapeHeadRouterTaggedTape
                    (some b) (b :: rest) stage suffixBits) } =
          { state := brancher.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits (b :: rest) stage)
                      (List.append suffixBits
                        (inputTapeBits (b :: rest))))).map
                    some)) })

def AppendInputTapeHeadTaggedBrancherConstruction :
    Prop :=
  forall rightCopier : MachineDescription,
    AppendInputTapeRightCellsReturnSpec rightCopier ->
      exists brancher : MachineDescription,
        AppendInputTapeHeadTaggedBrancherSpec brancher

def AppendInputTapeHeadDispatcherSpec
    (dispatcher : MachineDescription) : Prop :=
  dispatcher.SubroutineReady ∧
    (forall stage : Nat,
     forall suffixBits : Word Bool,
      exists steps : Nat,
        dispatcher.runConfig steps
            { state := dispatcher.start
              tape :=
                tapeAtCells []
                  (some false :: some false ::
                    ((List.append [false, true]
                      (List.append
                        (stageInputBits ([] : Word Bool) stage)
                        suffixBits)).map some)) } =
          { state := dispatcher.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits ([] : Word Bool) stage)
                      (List.append suffixBits
                        (inputTapeBits ([] : Word Bool))))).map
                    some)) }) ∧
    (forall b : Bool,
     forall rest : Word Bool,
     forall stage : Nat,
     forall suffixBits : Word Bool,
      exists steps : Nat,
        dispatcher.runConfig steps
            { state := dispatcher.start
              tape :=
                tapeAtCells []
                  (some false :: some false ::
                    ((List.append [false, true]
                      (List.append
                        (stageInputBits (b :: rest) stage)
                        suffixBits)).map some)) } =
          { state := dispatcher.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                    (List.append
                      (stageInputBits (b :: rest) stage)
                      (List.append suffixBits
                        (inputTapeBits (b :: rest))))).map
                    some)) })

def AppendInputTapeHeadDispatcherConstruction :
    Prop :=
  forall rightCopier : MachineDescription,
    AppendInputTapeRightCellsReturnSpec rightCopier ->
      exists dispatcher : MachineDescription,
        AppendInputTapeHeadDispatcherSpec dispatcher

def AppendInputTapeHeadDispatcherDescription
    (router brancher : MachineDescription) : MachineDescription :=
  seqSubroutine router brancher Direction.left
theorem appendInputTapeHeadDispatcherSpec_of_router_brancher
    {router brancher : MachineDescription}
    (hrouter : AppendInputTapeHeadRouterSpec router)
    (hbrancher :
      AppendInputTapeHeadTaggedBrancherSpec brancher) :
    AppendInputTapeHeadDispatcherSpec
      (AppendInputTapeHeadDispatcherDescription
        router brancher) := by
  constructor
  · exact seqSubroutine_subroutineReady
      hrouter.left hbrancher.left
  constructor
  · intro stage suffixBits
    let A := router
    let B := brancher
    let Tmid :=
      appendInputTapeHeadRouterTaggedTape
        none ([] : Word Bool) stage suffixBits
    have hAready : A.SubroutineReady := hrouter.left
    have hBready : B.SubroutineReady := hbrancher.left
    rcases hrouter.right.left stage suffixBits with ⟨nA, hA⟩
    have hArun :
        A.runConfig nA
            { state := A.start
              tape :=
                tapeAtCells []
                  (some false :: some false ::
                    ((List.append [false, true]
                      (List.append
                        (stageInputBits ([] : Word Bool) stage)
                        suffixBits)).map some)) } =
          { state := A.halt, tape := Tmid } := by
      simpa [A, Tmid] using hA
    have hBReach :
        exists nB : Nat,
          B.runConfig nB
              { state := B.start
                tape := Tape.move Direction.left Tmid } =
            { state := B.halt
              tape :=
                tapeAtCells [some false]
                  (some false ::
                    ((List.append [false, true]
                      (List.append
                        (stageInputBits ([] : Word Bool) stage)
                        (List.append suffixBits
                          (inputTapeBits ([] : Word Bool))))).map
                      some)) } := by
      rcases hbrancher.right.left stage suffixBits with ⟨nB, hB⟩
      exact ⟨nB, by simpa [B, Tmid] using hB⟩
    rcases
        seqSubroutine_reaches_of_runConfig_eq
          (A := A) (B := B) (handoffMove := Direction.left)
          hAready hBready hArun hBReach with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [AppendInputTapeHeadDispatcherDescription,
      A, B] using hn
  · intro b rest stage suffixBits
    let A := router
    let B := brancher
    let Tmid :=
      appendInputTapeHeadRouterTaggedTape
        (some b) (b :: rest) stage suffixBits
    have hAready : A.SubroutineReady := hrouter.left
    have hBready : B.SubroutineReady := hbrancher.left
    rcases hrouter.right.right b rest stage suffixBits with ⟨nA, hA⟩
    have hArun :
        A.runConfig nA
            { state := A.start
              tape :=
                tapeAtCells []
                  (some false :: some false ::
                    ((List.append [false, true]
                      (List.append
                        (stageInputBits (b :: rest) stage)
                        suffixBits)).map some)) } =
          { state := A.halt, tape := Tmid } := by
      simpa [A, Tmid] using hA
    have hBReach :
        exists nB : Nat,
          B.runConfig nB
              { state := B.start
                tape := Tape.move Direction.left Tmid } =
            { state := B.halt
              tape :=
                tapeAtCells [some false]
                  (some false ::
                    ((List.append [false, true]
                      (List.append
                        (stageInputBits (b :: rest) stage)
                        (List.append suffixBits
                          (inputTapeBits (b :: rest))))).map
                      some)) } := by
      rcases hbrancher.right.right b rest stage suffixBits with ⟨nB, hB⟩
      exact ⟨nB, by simpa [B, Tmid] using hB⟩
    rcases
        seqSubroutine_reaches_of_runConfig_eq
          (A := A) (B := B) (handoffMove := Direction.left)
          hAready hBready hArun hBReach with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [AppendInputTapeHeadDispatcherDescription,
      A, B] using hn

def AppendInputTapeReturnForwardSpec
    (copier : MachineDescription) : Prop :=
    forall w : Word Bool,
    forall stage : Nat,
    forall suffixBits : Word Bool,
      exists steps : Nat,
        copier.runConfig steps
            { state := copier.start
              tape :=
                tapeAtCells []
                  (some false :: some false ::
                    ((List.append [false, true]
                      (List.append
                        (stageInputBits w stage)
                        suffixBits)).map some)) } =
          { state := copier.halt
            tape :=
              tapeAtCells [some false]
                (some false ::
                  ((List.append [false, true]
                      (List.append
                        (stageInputBits w stage)
                        (List.append suffixBits
                          (inputTapeBits w)))).map some)) }

def AppendInputTapeReturnSpec
    (copier : MachineDescription) : Prop :=
  copier.SubroutineReady ∧
    AppendInputTapeReturnForwardSpec copier

def AppendInputTapeRightCellsReturnConstruction : Prop :=
  exists rightCopier : MachineDescription,
    AppendInputTapeRightCellsReturnSpec rightCopier

theorem appendInputTapeReturnSpec_of_headDispatcher
    {dispatcher : MachineDescription}
    (hdispatcher :
      AppendInputTapeHeadDispatcherSpec dispatcher) :
    AppendInputTapeReturnSpec dispatcher := by
  constructor
  · exact hdispatcher.left
  intro w stage suffixBits
  cases w with
  | nil =>
      exact hdispatcher.right.left stage suffixBits
  | cons b rest =>
      exact hdispatcher.right.right b rest stage suffixBits


end DovetailInitialLayoutInitializer
end Computability
end FoC
