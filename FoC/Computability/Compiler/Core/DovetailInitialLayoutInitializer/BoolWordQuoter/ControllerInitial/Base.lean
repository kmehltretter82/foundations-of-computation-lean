import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.BoolWordQuoter.Basic

set_option doc.verso true

/-!
# Controller initial raw Bool-word header emitter

This module contains the direct finite-table proof work for the reusable
controller-initial raw Bool-word header emitter.
-/

namespace FoC
namespace Computability

open Languages

namespace DovetailInitialLayoutInitializer

def controllerInitialRawBoolWordHeaderEmitterSuffix :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend 0
    (MachineDescription.encodeBoolWordAppend [] [])

def ControllerInitialRawBoolWordHeaderEmitterDescription :
    MachineDescription where
  stateCount := 71
  start := 0
  halt := 70
  transitions :=
    [ MachineDescription.transition 0 (some false) (some false) Direction.right 0
    , MachineDescription.transition 0 (some true) (some true) Direction.right 0
    , MachineDescription.transition 0 none none Direction.right 1
    , MachineDescription.transition 1 (some false) (some false) Direction.right 1
    , MachineDescription.transition 1 (some true) (some true) Direction.right 1
    , MachineDescription.transition 1 none (some false) Direction.right 2
    , MachineDescription.transition 2 none (some false) Direction.right 3
    , MachineDescription.transition 3 none (some false) Direction.right 4
    , MachineDescription.transition 4 none (some false) Direction.right 5
    , MachineDescription.transition 5 none none Direction.left 8
    , MachineDescription.transition 8 (some false) (some false) Direction.left 8
    , MachineDescription.transition 8 (some true) (some true) Direction.left 8
    , MachineDescription.transition 8 none none Direction.left 6
    , MachineDescription.transition 6 (some false) (some false) Direction.left 6
    , MachineDescription.transition 6 (some true) (some true) Direction.left 6
    , MachineDescription.transition 6 none none Direction.right 7
    , MachineDescription.transition 7 (some false) none Direction.right 10
    , MachineDescription.transition 7 (some true) none Direction.right 20
    , MachineDescription.transition 7 none none Direction.right 30
    , MachineDescription.transition 10 (some false) (some false) Direction.right 10
    , MachineDescription.transition 10 (some true) (some true) Direction.right 10
    , MachineDescription.transition 10 none none Direction.right 11
    , MachineDescription.transition 11 (some false) (some false) Direction.right 11
    , MachineDescription.transition 11 (some true) (some true) Direction.right 11
    , MachineDescription.transition 11 none (some false) Direction.right 12
    , MachineDescription.transition 12 none (some false) Direction.right 13
    , MachineDescription.transition 13 none (some true) Direction.right 14
    , MachineDescription.transition 14 none (some false) Direction.right 15
    , MachineDescription.transition 15 none none Direction.left 17
    , MachineDescription.transition 17 (some false) (some false) Direction.left 17
    , MachineDescription.transition 17 (some true) (some true) Direction.left 17
    , MachineDescription.transition 17 none none Direction.left 16
    , MachineDescription.transition 16 (some false) (some false) Direction.left 16
    , MachineDescription.transition 16 (some true) (some true) Direction.left 16
    , MachineDescription.transition 16 none (some false) Direction.right 7
    , MachineDescription.transition 20 (some false) (some false) Direction.right 20
    , MachineDescription.transition 20 (some true) (some true) Direction.right 20
    , MachineDescription.transition 20 none none Direction.right 21
    , MachineDescription.transition 21 (some false) (some false) Direction.right 21
    , MachineDescription.transition 21 (some true) (some true) Direction.right 21
    , MachineDescription.transition 21 none (some false) Direction.right 22
    , MachineDescription.transition 22 none (some false) Direction.right 23
    , MachineDescription.transition 23 none (some true) Direction.right 24
    , MachineDescription.transition 24 none (some false) Direction.right 25
    , MachineDescription.transition 25 none none Direction.left 27
    , MachineDescription.transition 27 (some false) (some false) Direction.left 27
    , MachineDescription.transition 27 (some true) (some true) Direction.left 27
    , MachineDescription.transition 27 none none Direction.left 26
    , MachineDescription.transition 26 (some false) (some false) Direction.left 26
    , MachineDescription.transition 26 (some true) (some true) Direction.left 26
    , MachineDescription.transition 26 none (some true) Direction.right 7
    , MachineDescription.transition 30 (some false) (some false) Direction.right 30
    , MachineDescription.transition 30 (some true) (some true) Direction.right 30
    , MachineDescription.transition 30 none (some false) Direction.right 31
    , MachineDescription.transition 31 none (some false) Direction.right 32
    , MachineDescription.transition 32 none (some true) Direction.right 33
    , MachineDescription.transition 33 none (some true) Direction.right 34
    , MachineDescription.transition 34 none none Direction.left 37
    , MachineDescription.transition 37 (some false) (some false) Direction.left 37
    , MachineDescription.transition 37 (some true) (some true) Direction.left 37
    , MachineDescription.transition 37 none none Direction.left 35
    , MachineDescription.transition 35 (some false) (some false) Direction.left 35
    , MachineDescription.transition 35 (some true) (some true) Direction.left 35
    , MachineDescription.transition 35 none none Direction.right 36
    , MachineDescription.transition 36 (some false) none Direction.right 40
    , MachineDescription.transition 36 (some true) none Direction.right 50
    , MachineDescription.transition 36 none none Direction.right 60
    , MachineDescription.transition 40 (some false) (some false) Direction.right 40
    , MachineDescription.transition 40 (some true) (some true) Direction.right 40
    , MachineDescription.transition 40 none none Direction.right 41
    , MachineDescription.transition 41 (some false) (some false) Direction.right 41
    , MachineDescription.transition 41 (some true) (some true) Direction.right 41
    , MachineDescription.transition 41 none (some false) Direction.right 42
    , MachineDescription.transition 42 none (some true) Direction.right 43
    , MachineDescription.transition 43 none (some false) Direction.right 44
    , MachineDescription.transition 44 none (some true) Direction.right 45
    , MachineDescription.transition 45 none none Direction.left 47
    , MachineDescription.transition 47 (some false) (some false) Direction.left 47
    , MachineDescription.transition 47 (some true) (some true) Direction.left 47
    , MachineDescription.transition 47 none none Direction.left 46
    , MachineDescription.transition 46 (some false) (some false) Direction.left 46
    , MachineDescription.transition 46 (some true) (some true) Direction.left 46
    , MachineDescription.transition 46 none none Direction.right 36
    , MachineDescription.transition 50 (some false) (some false) Direction.right 50
    , MachineDescription.transition 50 (some true) (some true) Direction.right 50
    , MachineDescription.transition 50 none none Direction.right 51
    , MachineDescription.transition 51 (some false) (some false) Direction.right 51
    , MachineDescription.transition 51 (some true) (some true) Direction.right 51
    , MachineDescription.transition 51 none (some false) Direction.right 52
    , MachineDescription.transition 52 none (some true) Direction.right 53
    , MachineDescription.transition 53 none (some true) Direction.right 54
    , MachineDescription.transition 54 none (some false) Direction.right 55
    , MachineDescription.transition 55 none none Direction.left 57
    , MachineDescription.transition 57 (some false) (some false) Direction.left 57
    , MachineDescription.transition 57 (some true) (some true) Direction.left 57
    , MachineDescription.transition 57 none none Direction.left 56
    , MachineDescription.transition 56 (some false) (some false) Direction.left 56
    , MachineDescription.transition 56 (some true) (some true) Direction.left 56
    , MachineDescription.transition 56 none none Direction.right 36
    , MachineDescription.transition 60 (some false) (some false) Direction.right 60
    , MachineDescription.transition 60 (some true) (some true) Direction.right 60
    , MachineDescription.transition 60 none (some false) Direction.right 61
    , MachineDescription.transition 61 none (some false) Direction.right 62
    , MachineDescription.transition 62 none (some true) Direction.right 63
    , MachineDescription.transition 63 none (some true) Direction.right 64
    , MachineDescription.transition 64 none (some false) Direction.right 65
    , MachineDescription.transition 65 none (some false) Direction.right 66
    , MachineDescription.transition 66 none (some true) Direction.right 67
    , MachineDescription.transition 67 none (some true) Direction.right 70
    ]

theorem controllerInitialRawBoolWordHeaderEmitterDescription_wellFormed :
    ControllerInitialRawBoolWordHeaderEmitterDescription.WellFormed := by
  refine ⟨by native_decide, by native_decide, by native_decide, ?_, ?_⟩
  · exact transition_wellFormed_of_all
      (l := ControllerInitialRawBoolWordHeaderEmitterDescription.transitions)
      (stateCount :=
        ControllerInitialRawBoolWordHeaderEmitterDescription.stateCount)
      (by native_decide)
  · exact transition_deterministic_of_all
      (l := ControllerInitialRawBoolWordHeaderEmitterDescription.transitions)
      (by native_decide)

theorem
    controllerInitialRawBoolWordHeaderEmitterDescription_haltTransitionFree :
    ControllerInitialRawBoolWordHeaderEmitterDescription.HaltTransitionFree :=
  transition_notFrom_of_all
    (l := ControllerInitialRawBoolWordHeaderEmitterDescription.transitions)
    (state := ControllerInitialRawBoolWordHeaderEmitterDescription.halt)
    (by native_decide)

theorem controllerInitialRawBoolWordHeaderEmitterDescription_subroutineReady :
    ControllerInitialRawBoolWordHeaderEmitterDescription.SubroutineReady :=
  ⟨controllerInitialRawBoolWordHeaderEmitterDescription_wellFormed,
    controllerInitialRawBoolWordHeaderEmitterDescription_haltTransitionFree⟩

def controllerInitialRawBoolWordHeaderEmitterOutput
    (w : Word Bool) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput
    (MachineCodeSymbol.header ::
      MachineDescription.encodeBoolWordAppend w
        controllerInitialRawBoolWordHeaderEmitterSuffix)

def controllerInitialRawBoolWordHeaderEmitterFinalTape
    (w : Word Bool) : Tape Bool :=
  tapeAtCells
    (List.append
      ((controllerInitialRawBoolWordHeaderEmitterOutput w).reverse.map some)
      (List.replicate (w.length + 2) none))
    []

theorem controllerInitialRawBoolWordHeaderEmitterFinalTape_normalizedOutput
    (w : Word Bool) :
    Tape.normalizedOutput
        (controllerInitialRawBoolWordHeaderEmitterFinalTape w) =
      controllerInitialRawBoolWordHeaderEmitterOutput w := by
  rw [Tape.normalizedOutput]
  simp [controllerInitialRawBoolWordHeaderEmitterFinalTape,
    Tape.cells, tapeAtCells, List.filterMap_append,
    List.map_reverse]
  induction controllerInitialRawBoolWordHeaderEmitterOutput w with
  | nil => rfl
  | cons b rest ih => simp [ih]

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan0
    (leftRev : List (Option Bool)) (w : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (w.length + 1)
        (config 0 leftRev (w.map some)) =
      config 1
        (none :: List.append (w.reverse.map some) leftRev)
        [] := by
  induction w generalizing leftRev with
  | nil =>
      simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
        config, tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 0 leftRev ((false :: rest).map some)) =
            config 0 (some false :: leftRev) (rest.map some) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 0 leftRev ((true :: rest).map some)) =
            config 0 (some true :: leftRev) (rest.map some) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan10
    (leftRev : List (Option Bool)) (rest output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (rest.length + 1)
        (config 10 leftRev
          (List.append (rest.map some)
            (none :: List.append (output.map some) [none]))) =
      config 11
        (none :: List.append (rest.reverse.map some) leftRev)
        (List.append (output.map some) [none]) := by
  induction rest generalizing leftRev with
  | nil =>
      simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
        config, tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]
      cases output <;> rfl
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 10 leftRev
                (List.append ((false :: rest).map some)
                  (none :: List.append (output.map some) [none]))) =
            config 10 (some false :: leftRev)
              (List.append (rest.map some)
                (none :: List.append (output.map some) [none])) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 10 leftRev
                (List.append ((true :: rest).map some)
                  (none :: List.append (output.map some) [none]))) =
            config 10 (some true :: leftRev)
              (List.append (rest.map some)
                (none :: List.append (output.map some) [none])) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan20
    (leftRev : List (Option Bool)) (rest output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (rest.length + 1)
        (config 20 leftRev
          (List.append (rest.map some)
            (none :: List.append (output.map some) [none]))) =
      config 21
        (none :: List.append (rest.reverse.map some) leftRev)
        (List.append (output.map some) [none]) := by
  induction rest generalizing leftRev with
  | nil =>
      simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
        config, tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]
      cases output <;> rfl
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 20 leftRev
                (List.append ((false :: rest).map some)
                  (none :: List.append (output.map some) [none]))) =
            config 20 (some false :: leftRev)
              (List.append (rest.map some)
                (none :: List.append (output.map some) [none])) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 20 leftRev
                (List.append ((true :: rest).map some)
                  (none :: List.append (output.map some) [none]))) =
            config 20 (some true :: leftRev)
              (List.append (rest.map some)
                (none :: List.append (output.map some) [none])) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan11
    (leftRev : List (Option Bool)) (output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (output.length + 1)
        (config 11 leftRev (List.append (output.map some) [none])) =
      config 12
        (some false :: List.append (output.reverse.map some) leftRev)
        [] := by
  induction output generalizing leftRev with
  | nil =>
      simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
        config, tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 11 leftRev
                (List.append ((false :: rest).map some) [none])) =
            config 11 (some false :: leftRev)
              (List.append (rest.map some) [none]) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 11 leftRev
                (List.append ((true :: rest).map some) [none])) =
            config 11 (some true :: leftRev)
              (List.append (rest.map some) [none]) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan21
    (leftRev : List (Option Bool)) (output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (output.length + 1)
        (config 21 leftRev (List.append (output.map some) [none])) =
      config 22
        (some false :: List.append (output.reverse.map some) leftRev)
        [] := by
  induction output generalizing leftRev with
  | nil =>
      simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
        config, tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 21 leftRev
                (List.append ((false :: rest).map some) [none])) =
            config 21 (some false :: leftRev)
              (List.append (rest.map some) [none]) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 21 leftRev
                (List.append ((true :: rest).map some) [none])) =
            config 21 (some true :: leftRev)
              (List.append (rest.map some) [none]) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]

def controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
    (rawLeft : List (Option Bool)) (scanRev : Word Bool)
    (right : List (Option Bool)) : Tape Bool :=
  match scanRev with
  | [] => tapeAtCells rawLeft (none :: right)
  | b :: rest =>
      { left := List.append (rest.map some) (none :: rawLeft)
        head := some b
        right := right }

def controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
    (leftRev : List (Option Bool)) (scanRev : Word Bool)
    (right : List (Option Bool)) : Tape Bool :=
  match scanRev with
  | [] => tapeAtCells leftRev (none :: right)
  | b :: rest =>
      { left := List.append (rest.map some) (none :: leftRev)
        head := some b
        right := right }

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan17
    (leftRev : List (Option Bool)) (rawRev outputRev : Word Bool)
    (right : List (Option Bool)) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (outputRev.length + 1)
        { state := 17
          tape :=
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
              (List.append (rawRev.map some) (none :: leftRev))
              outputRev right } =
      { state := 16
        tape :=
          controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
            leftRev rawRev
            (none :: List.append (outputRev.reverse.map some) right) } := by
  induction outputRev generalizing right with
  | nil =>
      simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
        controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
        ControllerInitialRawBoolWordHeaderEmitterDescription,
        tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveLeft]
      cases rawRev <;> rfl
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              { state := 17
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                    (List.append (rawRev.map some) (none :: leftRev))
                    (false :: rest) right } =
            { state := 17
              tape :=
                controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                  (List.append (rawRev.map some) (none :: leftRev))
                  rest (some false :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
            ControllerInitialRawBoolWordHeaderEmitterDescription,
            tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: right)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              { state := 17
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                    (List.append (rawRev.map some) (none :: leftRev))
                    (true :: rest) right } =
            { state := 17
              tape :=
                controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                  (List.append (rawRev.map some) (none :: leftRev))
                  rest (some true :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
            ControllerInitialRawBoolWordHeaderEmitterDescription,
            tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: right)]
        simp [List.reverse_cons, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan27
    (leftRev : List (Option Bool)) (rawRev outputRev : Word Bool)
    (right : List (Option Bool)) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (outputRev.length + 1)
        { state := 27
          tape :=
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
              (List.append (rawRev.map some) (none :: leftRev))
              outputRev right } =
      { state := 26
        tape :=
          controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
            leftRev rawRev
            (none :: List.append (outputRev.reverse.map some) right) } := by
  induction outputRev generalizing right with
  | nil =>
      simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
        controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
        ControllerInitialRawBoolWordHeaderEmitterDescription,
        tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveLeft]
      cases rawRev <;> rfl
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              { state := 27
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                    (List.append (rawRev.map some) (none :: leftRev))
                    (false :: rest) right } =
            { state := 27
              tape :=
                controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                  (List.append (rawRev.map some) (none :: leftRev))
                  rest (some false :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
            ControllerInitialRawBoolWordHeaderEmitterDescription,
            tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: right)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              { state := 27
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                    (List.append (rawRev.map some) (none :: leftRev))
                    (true :: rest) right } =
            { state := 27
              tape :=
                controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                  (List.append (rawRev.map some) (none :: leftRev))
                  rest (some true :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
            ControllerInitialRawBoolWordHeaderEmitterDescription,
            tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: right)]
        simp [List.reverse_cons, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_return16
    (leftRev : List (Option Bool)) (scanRev : Word Bool)
    (right : List (Option Bool)) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (scanRev.length + 1)
        { state := 16
          tape :=
            controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
              leftRev scanRev right } =
      config 7 (some false :: leftRev)
        (List.append (scanRev.reverse.map some) right) := by
  induction scanRev generalizing right with
  | nil =>
      simp [controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
        ControllerInitialRawBoolWordHeaderEmitterDescription,
        config, tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]
      cases right <;> rfl
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              { state := 16
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                    leftRev (false :: rest) right } =
            { state := 16
              tape :=
                controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                  leftRev rest (some false :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
            ControllerInitialRawBoolWordHeaderEmitterDescription,
            tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: right)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              { state := 16
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                    leftRev (true :: rest) right } =
            { state := 16
              tape :=
                controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                  leftRev rest (some true :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
            ControllerInitialRawBoolWordHeaderEmitterDescription,
            tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: right)]
        simp [List.reverse_cons, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_return26
    (leftRev : List (Option Bool)) (scanRev : Word Bool)
    (right : List (Option Bool)) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (scanRev.length + 1)
        { state := 26
          tape :=
            controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
              leftRev scanRev right } =
      config 7 (some true :: leftRev)
        (List.append (scanRev.reverse.map some) right) := by
  induction scanRev generalizing right with
  | nil =>
      simp [controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
        ControllerInitialRawBoolWordHeaderEmitterDescription,
        config, tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]
      cases right <;> rfl
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              { state := 26
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                    leftRev (false :: rest) right } =
            { state := 26
              tape :=
                controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                  leftRev rest (some false :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
            ControllerInitialRawBoolWordHeaderEmitterDescription,
            tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: right)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              { state := 26
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                    leftRev (true :: rest) right } =
            { state := 26
              tape :=
                controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                  leftRev rest (some true :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev,
            ControllerInitialRawBoolWordHeaderEmitterDescription,
            tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: right)]
        simp [List.reverse_cons, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_writeTick12
    (leftRev : List (Option Bool)) (rawRev output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 4
        (config 12
          (some false ::
            List.append (output.reverse.map some)
              (none :: List.append (rawRev.map some) (none :: leftRev)))
          []) =
      { state := 17
        tape :=
          controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
            (List.append (rawRev.map some) (none :: leftRev))
            (List.append [false, true, false, false] output.reverse)
            [none] } := by
  simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
    ControllerInitialRawBoolWordHeaderEmitterDescription,
    config, tapeAtCells, MachineDescription.runConfig,
    MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem controllerInitialRawBoolWordHeaderEmitter_run_writeTick22
    (leftRev : List (Option Bool)) (rawRev output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 4
        (config 22
          (some false ::
            List.append (output.reverse.map some)
              (none :: List.append (rawRev.map some) (none :: leftRev)))
          []) =
      { state := 27
        tape :=
          controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
            (List.append (rawRev.map some) (none :: leftRev))
            (List.append [false, true, false, false] output.reverse)
            [none] } := by
  simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
    ControllerInitialRawBoolWordHeaderEmitterDescription,
    config, tapeAtCells, MachineDescription.runConfig,
    MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem controllerInitialRawBoolWordHeaderEmitter_run_count_false
    (leftRev : List (Option Bool)) (rest output : Word Bool) :
    ∃ steps : Nat,
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig steps
        (config 7 leftRev
          (some false ::
            List.append (rest.map some)
              (none :: List.append (output.map some) [none]))) =
        config 7 (some false :: leftRev)
          (List.append (rest.map some)
            (none :: List.append
              ((List.append output [false, false, true, false]).map some)
              [none])) := by
  let outputRev : Word Bool :=
    List.append [false, true, false, false] output.reverse
  refine
    ⟨1 +
      ((rest.length + 1) +
        ((output.length + 1) +
          (4 + ((outputRev.length + 1) + (rest.reverse.length + 1))))),
      ?_⟩
  rw [MachineDescription.runConfig_add]
  have hfirst :
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
        (config 7 leftRev
          (some false ::
            List.append (rest.map some)
              (none :: List.append (output.map some) [none]))) =
        config 10 (none :: leftRev)
          (List.append (rest.map some)
            (none :: List.append (output.map some) [none])) := by
    simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
      config, tapeAtCells, MachineDescription.runConfig,
      MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]
    cases rest <;> rfl
  rw [hfirst]
  rw [MachineDescription.runConfig_add]
  rw [controllerInitialRawBoolWordHeaderEmitter_run_scan10]
  rw [MachineDescription.runConfig_add]
  rw [controllerInitialRawBoolWordHeaderEmitter_run_scan11]
  rw [MachineDescription.runConfig_add]
  change
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
      ((outputRev.length + 1) + (rest.reverse.length + 1))
      (ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 4
        (config 12
          (some false ::
            List.append (output.reverse.map some)
              (none :: List.append (rest.reverse.map some)
                (none :: leftRev))) [])) =
        config 7 (some false :: leftRev)
          (List.append (rest.map some)
            (none :: List.append
              ((List.append output [false, false, true, false]).map some)
              [none]))
  rw [controllerInitialRawBoolWordHeaderEmitter_run_writeTick12]
  rw [MachineDescription.runConfig_add]
  change
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
      (rest.reverse.length + 1)
      (ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (outputRev.length + 1)
        { state := 17
          tape :=
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
              (List.append (rest.reverse.map some) (none :: leftRev))
              (List.append [false, true, false, false] output.reverse)
              [none] }) =
      config 7 (some false :: leftRev)
        (List.append (rest.map some)
          (none :: List.append
            ((List.append output [false, false, true, false]).map some)
            [none]))
  rw [controllerInitialRawBoolWordHeaderEmitter_run_scan17]
  rw [controllerInitialRawBoolWordHeaderEmitter_run_return16]
  simp [outputRev, List.map_append, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_count_true
    (leftRev : List (Option Bool)) (rest output : Word Bool) :
    ∃ steps : Nat,
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig steps
        (config 7 leftRev
          (some true ::
            List.append (rest.map some)
              (none :: List.append (output.map some) [none]))) =
        config 7 (some true :: leftRev)
          (List.append (rest.map some)
            (none :: List.append
              ((List.append output [false, false, true, false]).map some)
              [none])) := by
  let outputRev : Word Bool :=
    List.append [false, true, false, false] output.reverse
  refine
    ⟨1 +
      ((rest.length + 1) +
        ((output.length + 1) +
          (4 + ((outputRev.length + 1) + (rest.reverse.length + 1))))),
      ?_⟩
  rw [MachineDescription.runConfig_add]
  have hfirst :
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
        (config 7 leftRev
          (some true ::
            List.append (rest.map some)
              (none :: List.append (output.map some) [none]))) =
        config 20 (none :: leftRev)
          (List.append (rest.map some)
            (none :: List.append (output.map some) [none])) := by
    simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
      config, tapeAtCells, MachineDescription.runConfig,
      MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]
    cases rest <;> rfl
  rw [hfirst]
  rw [MachineDescription.runConfig_add]
  rw [controllerInitialRawBoolWordHeaderEmitter_run_scan20]
  rw [MachineDescription.runConfig_add]
  rw [controllerInitialRawBoolWordHeaderEmitter_run_scan21]
  rw [MachineDescription.runConfig_add]
  change
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
      ((outputRev.length + 1) + (rest.reverse.length + 1))
      (ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 4
        (config 22
          (some false ::
            List.append (output.reverse.map some)
              (none :: List.append (rest.reverse.map some)
                (none :: leftRev))) [])) =
        config 7 (some true :: leftRev)
          (List.append (rest.map some)
            (none :: List.append
              ((List.append output [false, false, true, false]).map some)
              [none]))
  rw [controllerInitialRawBoolWordHeaderEmitter_run_writeTick22]
  rw [MachineDescription.runConfig_add]
  change
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
      (rest.reverse.length + 1)
      (ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (outputRev.length + 1)
        { state := 27
          tape :=
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
              (List.append (rest.reverse.map some) (none :: leftRev))
              (List.append [false, true, false, false] output.reverse)
              [none] }) =
      config 7 (some true :: leftRev)
        (List.append (rest.map some)
          (none :: List.append
            ((List.append output [false, false, true, false]).map some)
            [none]))
  rw [controllerInitialRawBoolWordHeaderEmitter_run_scan27]
  rw [controllerInitialRawBoolWordHeaderEmitter_run_return26]
  simp [outputRev, List.map_append, List.append_assoc]

def controllerInitialRawBoolWordHeaderEmitterCountTicksBits :
    Word Bool -> Word Bool
  | [] => []
  | _ :: rest =>
      List.append [false, false, true, false]
        (controllerInitialRawBoolWordHeaderEmitterCountTicksBits rest)

theorem controllerInitialRawBoolWordHeaderEmitter_run_countPass
    (leftRev : List (Option Bool)) (w output : Word Bool) :
    ∃ steps : Nat,
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig steps
        (config 7 leftRev
          (List.append (w.map some)
            (none :: List.append (output.map some) [none]))) =
        config 7 (List.append (w.reverse.map some) leftRev)
          (none :: List.append
            ((List.append output
              (controllerInitialRawBoolWordHeaderEmitterCountTicksBits
                w)).map some) [none]) := by
  induction w generalizing leftRev output with
  | nil =>
      refine ⟨0, ?_⟩
      simp [controllerInitialRawBoolWordHeaderEmitterCountTicksBits,
        config, tapeAtCells]
      rfl
  | cons b rest ih =>
      cases b
      · rcases controllerInitialRawBoolWordHeaderEmitter_run_count_false
          leftRev rest output with ⟨stepsHead, hhead⟩
        rcases ih (some false :: leftRev)
            (List.append output [false, false, true, false]) with
          ⟨stepsTail, htail⟩
        refine ⟨stepsHead + stepsTail, ?_⟩
        rw [MachineDescription.runConfig_add]
        have hhead' :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
              stepsHead
              (config 7 leftRev
                (List.append ((false :: rest).map some)
                  (none :: List.append (output.map some) [none]))) =
              config 7 (some false :: leftRev)
                (List.append (rest.map some)
                  (none :: List.append
                    ((List.append output [false, false, true, false]).map
                      some) [none])) := by
          simpa [List.map_cons] using hhead
        rw [hhead', htail]
        simp [controllerInitialRawBoolWordHeaderEmitterCountTicksBits,
          List.map_append, List.reverse_cons, List.append_assoc]
      · rcases controllerInitialRawBoolWordHeaderEmitter_run_count_true
          leftRev rest output with ⟨stepsHead, hhead⟩
        rcases ih (some true :: leftRev)
            (List.append output [false, false, true, false]) with
          ⟨stepsTail, htail⟩
        refine ⟨stepsHead + stepsTail, ?_⟩
        rw [MachineDescription.runConfig_add]
        have hhead' :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
              stepsHead
              (config 7 leftRev
                (List.append ((true :: rest).map some)
                  (none :: List.append (output.map some) [none]))) =
              config 7 (some true :: leftRev)
                (List.append (rest.map some)
                  (none :: List.append
                    ((List.append output [false, false, true, false]).map
                      some) [none])) := by
          simpa [List.map_cons] using hhead
        rw [hhead', htail]
        simp [controllerInitialRawBoolWordHeaderEmitterCountTicksBits,
          List.map_append, List.reverse_cons, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan30
    (leftRev : List (Option Bool)) (output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (output.length + 1)
        (config 30 leftRev (List.append (output.map some) [none])) =
      config 31
        (some false :: List.append (output.reverse.map some) leftRev)
        [] := by
  induction output generalizing leftRev with
  | nil =>
      simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
        config, tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 30 leftRev
                (List.append ((false :: rest).map some) [none])) =
            config 30 (some false :: leftRev)
              (List.append (rest.map some) [none]) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              (config 30 leftRev
                (List.append ((true :: rest).map some) [none])) =
            config 30 (some true :: leftRev)
              (List.append (rest.map some) [none]) := by
          simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
            config, tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveRight]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: leftRev)]
        simp [List.reverse_cons, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_writeDone31
    (rawRev output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 4
        (config 31
          (some false ::
            List.append (output.reverse.map some)
              (none :: rawRev.map some))
          []) =
      { state := 37
        tape :=
          controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
            (rawRev.map some)
            (List.append [true, true, false, false] output.reverse)
            [none] } := by
  simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
    ControllerInitialRawBoolWordHeaderEmitterDescription,
    config, tapeAtCells, MachineDescription.runConfig,
    MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

def controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTape
    (scanRev : Word Bool) (right : List (Option Bool)) : Tape Bool :=
  match scanRev with
  | [] => tapeAtCells [] (none :: right)
  | b :: rest =>
      { left := rest.map some
        head := some b
        right := right }

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan37
    (rawRev outputRev : Word Bool) (right : List (Option Bool)) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (outputRev.length + 1)
        { state := 37
          tape :=
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
              (rawRev.map some) outputRev right } =
      { state := 35
        tape :=
          controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTape rawRev
            (none :: List.append (outputRev.reverse.map some) right) } := by
  induction outputRev generalizing right with
  | nil =>
      simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
        controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTape,
        ControllerInitialRawBoolWordHeaderEmitterDescription,
        tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveLeft]
      cases rawRev <;> rfl
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              { state := 37
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                    (rawRev.map some)
                    (false :: rest) right } =
            { state := 37
              tape :=
                controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                  (rawRev.map some)
                  rest (some false :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
            ControllerInitialRawBoolWordHeaderEmitterDescription,
            tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: right)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              { state := 37
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                    (rawRev.map some)
                    (true :: rest) right } =
            { state := 37
              tape :=
                controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                  (rawRev.map some)
                  rest (some true :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
            ControllerInitialRawBoolWordHeaderEmitterDescription,
            tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: right)]
        simp [List.reverse_cons, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_return35
    (scanRev : Word Bool) (right : List (Option Bool)) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (scanRev.length + 1)
        { state := 35
          tape :=
            controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTape
              scanRev right } =
      config 36 [none]
        (List.append (scanRev.reverse.map some) right) := by
  induction scanRev generalizing right with
  | nil =>
      simp [controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTape,
        ControllerInitialRawBoolWordHeaderEmitterDescription,
        config, tapeAtCells, MachineDescription.runConfig,
        MachineDescription.stepConfig,
        MachineDescription.lookupTransition, MachineDescription.Matches,
        MachineDescription.transition, Tape.read, Tape.write,
        Tape.move, Tape.moveRight]
      cases right <;> rfl
  | cons b rest ih =>
      cases b
      · rw [show (false :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              { state := 35
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTape
                    (false :: rest) right } =
            { state := 35
              tape :=
                controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTape
                  rest (some false :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTape,
            ControllerInitialRawBoolWordHeaderEmitterDescription,
            tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some false :: right)]
        simp [List.reverse_cons, List.append_assoc]
      · rw [show (true :: rest).length + 1 = 1 + (rest.length + 1) by
          simp [Nat.add_comm, Nat.add_left_comm]]
        rw [MachineDescription.runConfig_add]
        have hfirst :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
              { state := 35
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTape
                    (true :: rest) right } =
            { state := 35
              tape :=
                controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTape
                  rest (some true :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTape,
            ControllerInitialRawBoolWordHeaderEmitterDescription,
            tapeAtCells, MachineDescription.runConfig,
            MachineDescription.stepConfig,
            MachineDescription.lookupTransition, MachineDescription.Matches,
            MachineDescription.transition, Tape.read, Tape.write,
            Tape.move, Tape.moveLeft]
          cases rest <;> rfl
        rw [hfirst]
        rw [ih (some true :: right)]
        simp [List.reverse_cons, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_doneSeparator
    (rawRev output : Word Bool) :
    ∃ steps : Nat,
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig steps
        (config 7 (rawRev.map some)
          (none :: List.append (output.map some) [none])) =
      config 36 [none]
        (List.append (rawRev.reverse.map some)
          (none :: List.append
            ((List.append output [false, false, true, true]).map some)
            [none])) := by
  let outputRev : Word Bool :=
    List.append [true, true, false, false] output.reverse
  refine
    ⟨1 +
      ((output.length + 1) +
        (4 + ((outputRev.length + 1) + (rawRev.length + 1)))),
      ?_⟩
  rw [MachineDescription.runConfig_add]
  have hfirst :
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
        (config 7 (rawRev.map some)
          (none :: List.append (output.map some) [none])) =
      config 30 (none :: rawRev.map some)
        (List.append (output.map some) [none]) := by
    simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
      config, tapeAtCells, MachineDescription.runConfig,
      MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write,
      Tape.move, Tape.moveRight]
    cases output <;> rfl
  rw [hfirst]
  rw [MachineDescription.runConfig_add]
  rw [controllerInitialRawBoolWordHeaderEmitter_run_scan30]
  rw [MachineDescription.runConfig_add]
  change
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
      ((outputRev.length + 1) + (rawRev.length + 1))
      (ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 4
        (config 31
          (some false ::
            List.append (output.reverse.map some)
              (none :: rawRev.map some)) [])) =
      config 36 [none]
        (List.append (rawRev.reverse.map some)
          (none :: List.append
            ((List.append output [false, false, true, true]).map some)
            [none]))
  rw [controllerInitialRawBoolWordHeaderEmitter_run_writeDone31]
  rw [MachineDescription.runConfig_add]
  change
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
      (rawRev.length + 1)
      (ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (outputRev.length + 1)
        { state := 37
          tape :=
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
              (rawRev.map some)
              (List.append [true, true, false, false] output.reverse)
              [none] }) =
      config 36 [none]
        (List.append (rawRev.reverse.map some)
          (none :: List.append
            ((List.append output [false, false, true, true]).map some)
            [none]))
  rw [controllerInitialRawBoolWordHeaderEmitter_run_scan37]
  rw [controllerInitialRawBoolWordHeaderEmitter_run_return35]
  simp [outputRev, List.map_append, List.append_assoc]


end DovetailInitialLayoutInitializer
end Computability
end FoC
