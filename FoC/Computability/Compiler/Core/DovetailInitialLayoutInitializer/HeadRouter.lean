import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.TaggedBrancher

set_option doc.verso true

/-!
# HeadRouter

Supporting declarations and helper lemmas for Computability Compiler Core DovetailInitialLayoutInitializer HeadRouter.
-/


namespace FoC
namespace Computability

open Languages

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
    [ MachineDescription.transition
        0 (some false) none Direction.right 1
    , MachineDescription.transition
        1 (some false) (some false) Direction.right 2
    , MachineDescription.transition
        2 (some false) (some false) Direction.right 3
    , MachineDescription.transition
        3 (some true) (some true) Direction.right 4
    , MachineDescription.transition
        4 (some false) (some false) Direction.right 5
    , MachineDescription.transition
        5 (some false) (some false) Direction.right 6
    , MachineDescription.transition
        6 (some true) (some true) Direction.right 7
    , MachineDescription.transition
        7 (some true) (some true) Direction.left 20
    , MachineDescription.transition
        7 (some false) (some false) Direction.right 8
    , MachineDescription.transition
        8 (some false) (some false) Direction.right 9
    , MachineDescription.transition
        9 (some false) (some false) Direction.right 10
    , MachineDescription.transition
        10 (some true) (some true) Direction.right 11
    , MachineDescription.transition
        11 (some false) (some false) Direction.right 8
    , MachineDescription.transition
        11 (some true) (some true) Direction.right 12
    , MachineDescription.transition
        12 (some false) (some false) Direction.right 13
    , MachineDescription.transition
        13 (some true) (some true) Direction.right 14
    , MachineDescription.transition
        14 (some false) (some false) Direction.left 21
    , MachineDescription.transition
        14 (some true) (some true) Direction.left 22
    , MachineDescription.transition
        20 (some false) (some false) Direction.left 20
    , MachineDescription.transition
        20 (some true) (some true) Direction.left 20
    , MachineDescription.transition
        20 none none Direction.right 31
    , MachineDescription.transition
        21 (some false) (some false) Direction.left 21
    , MachineDescription.transition
        21 (some true) (some true) Direction.left 21
    , MachineDescription.transition
        21 none (some false) Direction.right 31
    , MachineDescription.transition
        22 (some false) (some false) Direction.left 22
    , MachineDescription.transition
        22 (some true) (some true) Direction.left 22
    , MachineDescription.transition
        22 none (some true) Direction.right 31
    , MachineDescription.transition
        23 (some false) none Direction.right 31
    , MachineDescription.transition
        24 (some false) (some false) Direction.right 31
    , MachineDescription.transition
        25 (some false) (some true) Direction.right 31
    ]

 /-- `appendInputTapeHeadRouterDescription_wellFormed` describes append/fold behavior used by later composition. -/
theorem appendInputTapeHeadRouterDescription_wellFormed :
    AppendInputTapeHeadRouterDescription.WellFormed := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := AppendInputTapeHeadRouterDescription.transitions)
      (stateCount :=
        AppendInputTapeHeadRouterDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := AppendInputTapeHeadRouterDescription.transitions)
      (by
        native_decide) t u ht hu hkey
     /-- `appendInputTapeHeadRouterDescription_haltTransitionFree` describes append/fold behavior used by later composition. -/

theorem
    appendInputTapeHeadRouterDescription_haltTransitionFree :
    AppendInputTapeHeadRouterDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := AppendInputTapeHeadRouterDescription.transitions)
    (state := AppendInputTapeHeadRouterDescription.halt)
    (by
      native_decide) t ht

 /-- `appendInputTapeHeadRouterDescription_subroutineReady` packages a subroutine-ready composition step. -/
theorem appendInputTapeHeadRouterDescription_subroutineReady :
    AppendInputTapeHeadRouterDescription.SubroutineReady :=
  ⟨appendInputTapeHeadRouterDescription_wellFormed,
    appendInputTapeHeadRouterDescription_haltTransitionFree⟩

 /-- `appendInputTapeHeadRouterDescription_run_return20` states the corresponding theorem run form. -/
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
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]
  | cons bit rest ih =>
      cases current
      · simpa [MachineDescription.runConfig, config,
          tapeAtCells,
          AppendInputTapeHeadRouterDescription,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, List.append_assoc] using
          ih bit (some false :: right)
      · simpa [MachineDescription.runConfig, config,
          tapeAtCells,
          AppendInputTapeHeadRouterDescription,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, List.append_assoc] using
          ih bit (some true :: right)

 /-- `appendInputTapeHeadRouterDescription_run_return21` states the corresponding theorem run form. -/
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
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]
  | cons bit rest ih =>
      cases current
      · simpa [MachineDescription.runConfig, config,
          tapeAtCells,
          AppendInputTapeHeadRouterDescription,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, List.append_assoc] using
          ih bit (some false :: right)
      · simpa [MachineDescription.runConfig, config,
          tapeAtCells,
          AppendInputTapeHeadRouterDescription,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, List.append_assoc] using
          ih bit (some true :: right)

 /-- `appendInputTapeHeadRouterDescription_run_return22` states the corresponding theorem run form. -/
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
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]
  | cons bit rest ih =>
      cases current
      · simpa [MachineDescription.runConfig, config,
          tapeAtCells,
          AppendInputTapeHeadRouterDescription,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, List.append_assoc] using
          ih bit (some false :: right)
      · simpa [MachineDescription.runConfig, config,
          tapeAtCells,
          AppendInputTapeHeadRouterDescription,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, List.append_assoc] using
          ih bit (some true :: right)
     /-- `appendInputTapeHeadRouterDescription_run_state8_false` states the corresponding theorem run form. -/

theorem
    appendInputTapeHeadRouterDescription_run_state8_false
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
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]
      rw [show beforeRevBits.length + 8 * 0 + 15 =
        7 + (nextBefore.length + 3) by
          simp [nextBefore]
          omega]
      rw [MachineDescription.runConfig_add]
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
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
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
      rw [MachineDescription.runConfig_add]
      rw [hprefix]
      simpa [nextBefore,
        List.map_append, List.reverse_append, List.append_assoc,
        Nat.mul_succ] using
        ih nextBefore
     /-- `appendInputTapeHeadRouterDescription_run_state8_true` states the corresponding theorem run form. -/

theorem
    appendInputTapeHeadRouterDescription_run_state8_true
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
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveLeft, Tape.moveRight]
      rw [show beforeRevBits.length + 8 * 0 + 15 =
        7 + (nextBefore.length + 3) by
          simp [nextBefore]
          omega]
      rw [MachineDescription.runConfig_add]
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
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
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
      rw [MachineDescription.runConfig_add]
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

 /-- `appendInputTapeHeadRouterDescription_spec` states the finite-machine specification. -/
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
      MachineDescription.DovetailLayout.stageInputCode,
      MachineDescription.DovetailLayout.stageInputCodeAppend,
      MachineDescription.encodeBoolWordAppend,
      MachineDescription.encodeCellListAppend,
      MachineDescription.encodeNatAppend,
      MachineDescription.encodeNat,
      MachineDescription.encodeCellsAppend,
      MachineDescription.encodeCodeWordAsInput,
      MachineDescription.encodeCodeSymbolAsInput,
      AppendInputTapeHeadRouterDescription,
      tapeAtCells,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]
  · intro b rest stage suffixBits
    cases b
    · let beforeRevBits : Word Bool :=
        [false, true, false, false, true, false]
      let tailBits : Word Bool :=
        List.append
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.encodeCellsAppend (rest.map some)
              (MachineDescription.encodeNatAppend stage [])))
          suffixBits
      let rawCells : List (Option Bool) :=
        List.append
          (List.map some
            (MachineDescription.encodeCodeWordAsInput
              (List.append (MachineDescription.encodeNat rest.length)
                (MachineCodeSymbol.zero ::
                  MachineDescription.encodeCellsAppend (rest.map some)
                    (MachineDescription.encodeNat stage)))))
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
          MachineDescription.DovetailLayout.stageInputCode,
          MachineDescription.DovetailLayout.stageInputCodeAppend,
          MachineDescription.encodeBoolWordAppend,
          MachineDescription.encodeCellListAppend,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat,
          MachineDescription.encodeCellsAppend,
          MachineDescription.encodeCellAppend,
          MachineDescription.encodeCell,
          AppendInputTapeHeadRouterDescription,
          config, tapeAtCells,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight, List.map_append]
        cases
          (List.map some
            (MachineDescription.encodeCodeWordAsInput
              (List.append (MachineDescription.encodeNat rest.length)
                (MachineCodeSymbol.zero ::
                  MachineDescription.encodeCellsAppend (rest.map some)
                    (MachineDescription.encodeNat stage)))) ++
            List.map some suffixBits) <;>
          rfl
      have hcells :
          rawCells =
            ((List.append (natBits rest.length)
              (false :: true :: false :: true :: tailBits)).map some) := by
        simpa [rawCells, tailBits, MachineDescription.encodeNatAppend,
          List.map_append, List.append_assoc] using
          natBits_map_append_cell_false rest.length
            (MachineDescription.encodeCellsAppend (rest.map some)
              (MachineDescription.encodeNat stage))
            suffixBits
      rw [show 8 * rest.length + 29 =
        8 + (beforeRevBits.length + 8 * rest.length + 15) by
          simp [beforeRevBits]
          omega]
      rw [MachineDescription.runConfig_add]
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
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        MachineDescription.encodeCellsAppend,
        MachineDescription.encodeCellAppend,
        MachineDescription.encodeCell,
        List.map_append, List.reverse_append, List.append_assoc] using
        hscan
    · let beforeRevBits : Word Bool :=
        [false, true, false, false, true, false]
      let tailBits : Word Bool :=
        List.append
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.encodeCellsAppend (rest.map some)
              (MachineDescription.encodeNatAppend stage [])))
          suffixBits
      let rawCells : List (Option Bool) :=
        List.append
          (List.map some
            (MachineDescription.encodeCodeWordAsInput
              (List.append (MachineDescription.encodeNat rest.length)
                (MachineCodeSymbol.one ::
                  MachineDescription.encodeCellsAppend (rest.map some)
                    (MachineDescription.encodeNat stage)))))
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
          MachineDescription.DovetailLayout.stageInputCode,
          MachineDescription.DovetailLayout.stageInputCodeAppend,
          MachineDescription.encodeBoolWordAppend,
          MachineDescription.encodeCellListAppend,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat,
          MachineDescription.encodeCellsAppend,
          MachineDescription.encodeCellAppend,
          MachineDescription.encodeCell,
          AppendInputTapeHeadRouterDescription,
          config, tapeAtCells,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight, List.map_append]
        cases
          (List.map some
            (MachineDescription.encodeCodeWordAsInput
              (List.append (MachineDescription.encodeNat rest.length)
                (MachineCodeSymbol.one ::
                  MachineDescription.encodeCellsAppend (rest.map some)
                    (MachineDescription.encodeNat stage)))) ++
            List.map some suffixBits) <;>
          rfl
      have hcells :
          rawCells =
            ((List.append (natBits rest.length)
              (false :: true :: true :: false :: tailBits)).map some) := by
        simpa [rawCells, tailBits, MachineDescription.encodeNatAppend,
          List.map_append, List.append_assoc] using
          natBits_map_append_cell_true rest.length
            (MachineDescription.encodeCellsAppend (rest.map some)
              (MachineDescription.encodeNat stage))
            suffixBits
      rw [show 8 * rest.length + 29 =
        8 + (beforeRevBits.length + 8 * rest.length + 15) by
          simp [beforeRevBits]
          omega]
      rw [MachineDescription.runConfig_add]
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
        MachineDescription.DovetailLayout.stageInputCode,
        MachineDescription.DovetailLayout.stageInputCodeAppend,
        MachineDescription.encodeBoolWordAppend,
        MachineDescription.encodeCellListAppend,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat,
        MachineDescription.encodeCellsAppend,
        MachineDescription.encodeCellAppend,
        MachineDescription.encodeCell,
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
  MachineDescription.seqSubroutine router brancher Direction.left

 /-- `appendInputTapeHeadDispatcherSpec_of_router_brancher` states the finite-machine specification. -/
theorem appendInputTapeHeadDispatcherSpec_of_router_brancher
    {router brancher : MachineDescription}
    (hrouter : AppendInputTapeHeadRouterSpec router)
    (hbrancher :
      AppendInputTapeHeadTaggedBrancherSpec brancher) :
    AppendInputTapeHeadDispatcherSpec
      (AppendInputTapeHeadDispatcherDescription
        router brancher) := by
  constructor
  · exact MachineDescription.seqSubroutine_subroutineReady
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
        MachineDescription.seqSubroutine_reaches_of_runConfig_eq
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
        MachineDescription.seqSubroutine_reaches_of_runConfig_eq
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

 /-- `appendInputTapeReturnSpec_of_headDispatcher` states the finite-machine specification. -/
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
