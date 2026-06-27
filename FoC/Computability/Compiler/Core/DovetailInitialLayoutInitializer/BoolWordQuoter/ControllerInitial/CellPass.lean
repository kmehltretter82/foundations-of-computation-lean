import FoC.Computability.Compiler.Core.DovetailInitialLayoutInitializer.BoolWordQuoter.ControllerInitial.Base

set_option doc.verso true

/-!
# Controller initial raw Bool-word header emitter cell pass

This module contains the state-36 cell pass and final assembly for the
controller-initial raw Bool-word header emitter.
-/

namespace FoC
namespace Computability

open Languages

namespace DovetailInitialLayoutInitializer

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan40
    (leftRev : List (Option Bool)) (rest output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (rest.length + 1)
        (config 40 leftRev
          (List.append (rest.map some)
            (none :: List.append (output.map some) [none]))) =
      config 41
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
              (config 40 leftRev
                (List.append ((false :: rest).map some)
                  (none :: List.append (output.map some) [none]))) =
            config 40 (some false :: leftRev)
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
              (config 40 leftRev
                (List.append ((true :: rest).map some)
                  (none :: List.append (output.map some) [none]))) =
            config 40 (some true :: leftRev)
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

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan50
    (leftRev : List (Option Bool)) (rest output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (rest.length + 1)
        (config 50 leftRev
          (List.append (rest.map some)
            (none :: List.append (output.map some) [none]))) =
      config 51
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
              (config 50 leftRev
                (List.append ((false :: rest).map some)
                  (none :: List.append (output.map some) [none]))) =
            config 50 (some false :: leftRev)
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
              (config 50 leftRev
                (List.append ((true :: rest).map some)
                  (none :: List.append (output.map some) [none]))) =
            config 50 (some true :: leftRev)
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

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan41
    (leftRev : List (Option Bool)) (output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (output.length + 1)
        (config 41 leftRev (List.append (output.map some) [none])) =
      config 42
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
              (config 41 leftRev
                (List.append ((false :: rest).map some) [none])) =
            config 41 (some false :: leftRev)
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
              (config 41 leftRev
                (List.append ((true :: rest).map some) [none])) =
            config 41 (some true :: leftRev)
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

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan51
    (leftRev : List (Option Bool)) (output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (output.length + 1)
        (config 51 leftRev (List.append (output.map some) [none])) =
      config 52
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
              (config 51 leftRev
                (List.append ((false :: rest).map some) [none])) =
            config 51 (some false :: leftRev)
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
              (config 51 leftRev
                (List.append ((true :: rest).map some) [none])) =
            config 51 (some true :: leftRev)
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

theorem controllerInitialRawBoolWordHeaderEmitter_run_writeZero42
    (leftRev : List (Option Bool)) (rawRev output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 4
        (config 42
          (some false ::
            List.append (output.reverse.map some)
              (none :: List.append (rawRev.map some) (none :: leftRev)))
          []) =
      { state := 47
        tape :=
          controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
            (List.append (rawRev.map some) (none :: leftRev))
            (List.append [true, false, true, false] output.reverse)
            [none] } := by
  simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
    ControllerInitialRawBoolWordHeaderEmitterDescription,
    config, tapeAtCells, MachineDescription.runConfig,
    MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem controllerInitialRawBoolWordHeaderEmitter_run_writeOne52
    (leftRev : List (Option Bool)) (rawRev output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 4
        (config 52
          (some false ::
            List.append (output.reverse.map some)
              (none :: List.append (rawRev.map some) (none :: leftRev)))
          []) =
      { state := 57
        tape :=
          controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
            (List.append (rawRev.map some) (none :: leftRev))
            (List.append [false, true, true, false] output.reverse)
            [none] } := by
  simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
    ControllerInitialRawBoolWordHeaderEmitterDescription,
    config, tapeAtCells, MachineDescription.runConfig,
    MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan47
    (leftRev : List (Option Bool)) (rawRev outputRev : Word Bool)
    (right : List (Option Bool)) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (outputRev.length + 1)
        { state := 47
          tape :=
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
              (List.append (rawRev.map some) (none :: leftRev))
              outputRev right } =
      { state := 46
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
              { state := 47
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                    (List.append (rawRev.map some) (none :: leftRev))
                    (false :: rest) right } =
            { state := 47
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
              { state := 47
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                    (List.append (rawRev.map some) (none :: leftRev))
                    (true :: rest) right } =
            { state := 47
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

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan57
    (leftRev : List (Option Bool)) (rawRev outputRev : Word Bool)
    (right : List (Option Bool)) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (outputRev.length + 1)
        { state := 57
          tape :=
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
              (List.append (rawRev.map some) (none :: leftRev))
              outputRev right } =
      { state := 56
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
              { state := 57
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                    (List.append (rawRev.map some) (none :: leftRev))
                    (false :: rest) right } =
            { state := 57
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
              { state := 57
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                    (List.append (rawRev.map some) (none :: leftRev))
                    (true :: rest) right } =
            { state := 57
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

theorem controllerInitialRawBoolWordHeaderEmitter_run_return46
    (leftRev : List (Option Bool)) (scanRev : Word Bool)
    (right : List (Option Bool)) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (scanRev.length + 1)
        { state := 46
          tape :=
            controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
              leftRev scanRev right } =
      config 36 (none :: leftRev)
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
              { state := 46
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                    leftRev (false :: rest) right } =
            { state := 46
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
              { state := 46
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                    leftRev (true :: rest) right } =
            { state := 46
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

theorem controllerInitialRawBoolWordHeaderEmitter_run_return56
    (leftRev : List (Option Bool)) (scanRev : Word Bool)
    (right : List (Option Bool)) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (scanRev.length + 1)
        { state := 56
          tape :=
            controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
              leftRev scanRev right } =
      config 36 (none :: leftRev)
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
              { state := 56
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                    leftRev (false :: rest) right } =
            { state := 56
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
              { state := 56
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterRawReturnTapeRev
                    leftRev (true :: rest) right } =
            { state := 56
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

theorem controllerInitialRawBoolWordHeaderEmitter_run_cell_false
    (leftRev : List (Option Bool)) (rest output : Word Bool) :
    ∃ steps : Nat,
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig steps
        (config 36 leftRev
          (some false ::
            List.append (rest.map some)
              (none :: List.append (output.map some) [none]))) =
        config 36 (none :: leftRev)
          (List.append (rest.map some)
            (none :: List.append
              ((List.append output [false, true, false, true]).map some)
              [none])) := by
  let outputRev : Word Bool :=
    List.append [true, false, true, false] output.reverse
  refine
    ⟨1 +
      ((rest.length + 1) +
        ((output.length + 1) +
          (4 + ((outputRev.length + 1) + (rest.reverse.length + 1))))),
      ?_⟩
  rw [MachineDescription.runConfig_add]
  have hfirst :
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
        (config 36 leftRev
          (some false ::
            List.append (rest.map some)
              (none :: List.append (output.map some) [none]))) =
        config 40 (none :: leftRev)
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
  rw [controllerInitialRawBoolWordHeaderEmitter_run_scan40]
  rw [MachineDescription.runConfig_add]
  rw [controllerInitialRawBoolWordHeaderEmitter_run_scan41]
  rw [MachineDescription.runConfig_add]
  change
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
      ((outputRev.length + 1) + (rest.reverse.length + 1))
      (ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 4
        (config 42
          (some false ::
            List.append (output.reverse.map some)
              (none :: List.append (rest.reverse.map some)
                (none :: leftRev))) [])) =
        config 36 (none :: leftRev)
          (List.append (rest.map some)
            (none :: List.append
              ((List.append output [false, true, false, true]).map some)
              [none]))
  rw [controllerInitialRawBoolWordHeaderEmitter_run_writeZero42]
  rw [MachineDescription.runConfig_add]
  change
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
      (rest.reverse.length + 1)
      (ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (outputRev.length + 1)
        { state := 47
          tape :=
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
              (List.append (rest.reverse.map some) (none :: leftRev))
              (List.append [true, false, true, false] output.reverse)
              [none] }) =
      config 36 (none :: leftRev)
        (List.append (rest.map some)
          (none :: List.append
            ((List.append output [false, true, false, true]).map some)
            [none]))
  rw [controllerInitialRawBoolWordHeaderEmitter_run_scan47]
  rw [controllerInitialRawBoolWordHeaderEmitter_run_return46]
  simp [outputRev, List.map_append, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_cell_true
    (leftRev : List (Option Bool)) (rest output : Word Bool) :
    ∃ steps : Nat,
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig steps
        (config 36 leftRev
          (some true ::
            List.append (rest.map some)
              (none :: List.append (output.map some) [none]))) =
        config 36 (none :: leftRev)
          (List.append (rest.map some)
            (none :: List.append
              ((List.append output [false, true, true, false]).map some)
              [none])) := by
  let outputRev : Word Bool :=
    List.append [false, true, true, false] output.reverse
  refine
    ⟨1 +
      ((rest.length + 1) +
        ((output.length + 1) +
          (4 + ((outputRev.length + 1) + (rest.reverse.length + 1))))),
      ?_⟩
  rw [MachineDescription.runConfig_add]
  have hfirst :
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
        (config 36 leftRev
          (some true ::
            List.append (rest.map some)
              (none :: List.append (output.map some) [none]))) =
        config 50 (none :: leftRev)
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
  rw [controllerInitialRawBoolWordHeaderEmitter_run_scan50]
  rw [MachineDescription.runConfig_add]
  rw [controllerInitialRawBoolWordHeaderEmitter_run_scan51]
  rw [MachineDescription.runConfig_add]
  change
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
      ((outputRev.length + 1) + (rest.reverse.length + 1))
      (ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 4
        (config 52
          (some false ::
            List.append (output.reverse.map some)
              (none :: List.append (rest.reverse.map some)
                (none :: leftRev))) [])) =
        config 36 (none :: leftRev)
          (List.append (rest.map some)
            (none :: List.append
              ((List.append output [false, true, true, false]).map some)
              [none]))
  rw [controllerInitialRawBoolWordHeaderEmitter_run_writeOne52]
  rw [MachineDescription.runConfig_add]
  change
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
      (rest.reverse.length + 1)
      (ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (outputRev.length + 1)
        { state := 57
          tape :=
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
              (List.append (rest.reverse.map some) (none :: leftRev))
              (List.append [false, true, true, false] output.reverse)
              [none] }) =
      config 36 (none :: leftRev)
        (List.append (rest.map some)
          (none :: List.append
            ((List.append output [false, true, true, false]).map some)
            [none]))
  rw [controllerInitialRawBoolWordHeaderEmitter_run_scan57]
  rw [controllerInitialRawBoolWordHeaderEmitter_run_return56]
  simp [outputRev, List.map_append, List.append_assoc]

def controllerInitialRawBoolWordHeaderEmitterCellBits :
    Word Bool -> Word Bool
  | [] => []
  | false :: rest =>
      List.append [false, true, false, true]
        (controllerInitialRawBoolWordHeaderEmitterCellBits rest)
  | true :: rest =>
      List.append [false, true, true, false]
        (controllerInitialRawBoolWordHeaderEmitterCellBits rest)

theorem controllerInitialRawBoolWordHeaderEmitter_replicate_none_append_cons
    (n : Nat) (tail : List (Option Bool)) :
    List.append (List.replicate n none) (none :: tail) =
      none :: List.append (List.replicate n none) tail := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [List.replicate_succ] using ih

theorem controllerInitialRawBoolWordHeaderEmitter_twoBlankPadding
    (n : Nat) :
    (none : Option Bool) ::
        List.append (List.replicate n (none : Option Bool)) [none] =
      none :: none :: List.replicate n (none : Option Bool) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simpa [List.replicate_succ, List.append_assoc] using
        congrArg
          (fun tail : List (Option Bool) => (none : Option Bool) :: tail)
          ih

theorem controllerInitialRawBoolWordHeaderEmitter_run_cellPass
    (leftRev : List (Option Bool)) (w output : Word Bool) :
    ∃ steps : Nat,
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig steps
        (config 36 leftRev
          (List.append (w.map some)
            (none :: List.append (output.map some) [none]))) =
        config 36 (List.append (List.replicate w.length none) leftRev)
          (none :: List.append
            ((List.append output
              (controllerInitialRawBoolWordHeaderEmitterCellBits w)).map
              some) [none]) := by
  induction w generalizing leftRev output with
  | nil =>
      refine ⟨0, ?_⟩
      simp [controllerInitialRawBoolWordHeaderEmitterCellBits,
        config, tapeAtCells]
      rfl
  | cons b rest ih =>
      cases b
      · rcases controllerInitialRawBoolWordHeaderEmitter_run_cell_false
          leftRev rest output with ⟨stepsHead, hhead⟩
        rcases ih (none :: leftRev)
            (List.append output [false, true, false, true]) with
          ⟨stepsTail, htail⟩
        refine ⟨stepsHead + stepsTail, ?_⟩
        rw [MachineDescription.runConfig_add]
        have hhead' :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
              stepsHead
              (config 36 leftRev
                (List.append ((false :: rest).map some)
                  (none :: List.append (output.map some) [none]))) =
              config 36 (none :: leftRev)
                (List.append (rest.map some)
                  (none :: List.append
                    ((List.append output [false, true, false, true]).map
                      some) [none])) := by
          simpa [List.map_cons] using hhead
        rw [hhead', htail]
        rw [controllerInitialRawBoolWordHeaderEmitter_replicate_none_append_cons]
        simp [controllerInitialRawBoolWordHeaderEmitterCellBits,
          List.map_append, List.replicate_succ, List.append_assoc]
      · rcases controllerInitialRawBoolWordHeaderEmitter_run_cell_true
          leftRev rest output with ⟨stepsHead, hhead⟩
        rcases ih (none :: leftRev)
            (List.append output [false, true, true, false]) with
          ⟨stepsTail, htail⟩
        refine ⟨stepsHead + stepsTail, ?_⟩
        rw [MachineDescription.runConfig_add]
        have hhead' :
            ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
              stepsHead
              (config 36 leftRev
                (List.append ((true :: rest).map some)
                  (none :: List.append (output.map some) [none]))) =
              config 36 (none :: leftRev)
                (List.append (rest.map some)
                  (none :: List.append
                    ((List.append output [false, true, true, false]).map
                      some) [none])) := by
          simpa [List.map_cons] using hhead
        rw [hhead', htail]
        rw [controllerInitialRawBoolWordHeaderEmitter_replicate_none_append_cons]
        simp [controllerInitialRawBoolWordHeaderEmitterCellBits,
          List.map_append, List.replicate_succ, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan8
    (rawRev outputRev : Word Bool) (right : List (Option Bool)) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (outputRev.length + 1)
        { state := 8
          tape :=
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
              (rawRev.map some) outputRev right } =
      { state := 6
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
              { state := 8
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                    (rawRev.map some) (false :: rest) right } =
            { state := 8
              tape :=
                controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                  (rawRev.map some) rest (some false :: right) } := by
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
              { state := 8
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                    (rawRev.map some) (true :: rest) right } =
            { state := 8
              tape :=
                controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                  (rawRev.map some) rest (some true :: right) } := by
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

theorem controllerInitialRawBoolWordHeaderEmitter_run_return6
    (scanRev : Word Bool) (right : List (Option Bool)) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (scanRev.length + 1)
        { state := 6
          tape :=
            controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTape
              scanRev right } =
      config 7 [none]
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
              { state := 6
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTape
                    (false :: rest) right } =
            { state := 6
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
              { state := 6
                tape :=
                  controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTape
                    (true :: rest) right } =
            { state := 6
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

theorem controllerInitialRawBoolWordHeaderEmitter_run_headerPrelude
    (w : Word Bool) :
    ∃ steps : Nat,
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig steps
          (ControllerInitialRawBoolWordHeaderEmitterDescription.initial w) =
        config 7 [none]
          (List.append (w.map some)
            (none :: List.append
              ([false, false, false, false].map some) [none])) := by
  refine
    ⟨(w.length + 1) +
      (5 + (([false, false, false, false] : Word Bool).length + 1) +
        (w.reverse.length + 1)),
      ?_⟩
  rw [MachineDescription.runConfig_add]
  have hinitial :
      ControllerInitialRawBoolWordHeaderEmitterDescription.initial w =
        config 0 [] (w.map some) := by
    cases w <;>
      rfl
  rw [hinitial]
  rw [controllerInitialRawBoolWordHeaderEmitter_run_scan0]
  rw [MachineDescription.runConfig_add]
  have hwriteHeader :
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 5
        (config 1 (none :: List.append (w.reverse.map some) []) []) =
      { state := 8
        tape :=
          controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
            (w.reverse.map some) [false, false, false, false] [none] } := by
    simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
      ControllerInitialRawBoolWordHeaderEmitterDescription,
      config, tapeAtCells, MachineDescription.runConfig,
      MachineDescription.stepConfig,
      MachineDescription.lookupTransition, MachineDescription.Matches,
      MachineDescription.transition, Tape.read, Tape.write,
      Tape.move, Tape.moveLeft, Tape.moveRight]
  have hwriteHeaderScan :
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (5 + (([false, false, false, false] : Word Bool).length + 1))
        (config 1 (none :: List.append (w.reverse.map some) []) []) =
      { state := 6
        tape :=
          controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTape
            w.reverse
            (none ::
              List.append
                (([false, false, false, false] : Word Bool).reverse.map some)
                [none]) } := by
    rw [MachineDescription.runConfig_add]
    rw [hwriteHeader]
    rw [controllerInitialRawBoolWordHeaderEmitter_run_scan8]
  rw [hwriteHeaderScan]
  rw [controllerInitialRawBoolWordHeaderEmitter_run_return6]
  simp

def controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTapeWithSentinel
    (scanRev : Word Bool) (right : List (Option Bool)) : Tape Bool :=
  match scanRev with
  | [] => tapeAtCells [] (none :: right)
  | b :: rest =>
      { left := List.append (rest.map some) [none]
        head := some b
        right := right }

theorem controllerInitialRawBoolWordHeaderEmitter_run_writeDone31_sentinel
    (rawLeft : List (Option Bool)) (output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 4
        (config 31
          (some false ::
            List.append (output.reverse.map some) (none :: rawLeft))
          []) =
      { state := 37
        tape :=
          controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
            rawLeft
            (List.append [true, true, false, false] output.reverse)
            [none] } := by
  simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
    ControllerInitialRawBoolWordHeaderEmitterDescription,
    config, tapeAtCells, MachineDescription.runConfig,
    MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write,
    Tape.move, Tape.moveLeft, Tape.moveRight]

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan37_sentinel
    (rawRev outputRev : Word Bool) (right : List (Option Bool)) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (outputRev.length + 1)
        { state := 37
          tape :=
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
              (List.append (rawRev.map some) [none]) outputRev right } =
      { state := 35
        tape :=
          controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTapeWithSentinel
            rawRev
            (none :: List.append (outputRev.reverse.map some) right) } := by
  induction outputRev generalizing right with
  | nil =>
      simp [controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev,
        controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTapeWithSentinel,
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
                    (List.append (rawRev.map some) [none])
                    (false :: rest) right } =
            { state := 37
              tape :=
                controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                  (List.append (rawRev.map some) [none])
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
                    (List.append (rawRev.map some) [none])
                    (true :: rest) right } =
            { state := 37
              tape :=
                controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
                  (List.append (rawRev.map some) [none])
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

theorem controllerInitialRawBoolWordHeaderEmitter_run_return35_sentinel
    (scanRev : Word Bool) (right : List (Option Bool)) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (scanRev.length + 1)
        { state := 35
          tape :=
            controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTapeWithSentinel
              scanRev right } =
      config 36 [none]
        (List.append (scanRev.reverse.map some) right) := by
  induction scanRev generalizing right with
  | nil =>
      simp [controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTapeWithSentinel,
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
                  controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTapeWithSentinel
                    (false :: rest) right } =
            { state := 35
              tape :=
                controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTapeWithSentinel
                  rest (some false :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTapeWithSentinel,
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
                  controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTapeWithSentinel
                    (true :: rest) right } =
            { state := 35
              tape :=
                controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTapeWithSentinel
                  rest (some true :: right) } := by
          simp [controllerInitialRawBoolWordHeaderEmitterBoundaryReturnTapeWithSentinel,
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

theorem controllerInitialRawBoolWordHeaderEmitter_run_doneSeparator_sentinel
    (rawRev output : Word Bool) :
    ∃ steps : Nat,
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig steps
        (config 7 (List.append (rawRev.map some) [none])
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
        (config 7 (List.append (rawRev.map some) [none])
          (none :: List.append (output.map some) [none])) =
      config 30 (none :: List.append (rawRev.map some) [none])
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
              (none :: List.append (rawRev.map some) [none])) [])) =
      config 36 [none]
        (List.append (rawRev.reverse.map some)
          (none :: List.append
            ((List.append output [false, false, true, true]).map some)
            [none]))
  rw [controllerInitialRawBoolWordHeaderEmitter_run_writeDone31_sentinel]
  rw [MachineDescription.runConfig_add]
  change
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
      (rawRev.length + 1)
      (ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (outputRev.length + 1)
        { state := 37
          tape :=
            controllerInitialRawBoolWordHeaderEmitterOutputLeftScanTapeRev
              (List.append (rawRev.map some) [none])
              (List.append [true, true, false, false] output.reverse)
              [none] }) =
      config 36 [none]
        (List.append (rawRev.reverse.map some)
          (none :: List.append
            ((List.append output [false, false, true, true]).map some)
            [none]))
  rw [controllerInitialRawBoolWordHeaderEmitter_run_scan37_sentinel]
  rw [controllerInitialRawBoolWordHeaderEmitter_run_return35_sentinel]
  simp [outputRev, List.map_append, List.append_assoc]

theorem controllerInitialRawBoolWordHeaderEmitter_run_scan60
    (leftRev : List (Option Bool)) (output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (output.length + 1)
        (config 60 leftRev (List.append (output.map some) [none])) =
      config 61
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
              (config 60 leftRev
                (List.append ((false :: rest).map some) [none])) =
            config 60 (some false :: leftRev)
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
              (config 60 leftRev
                (List.append ((true :: rest).map some) [none])) =
            config 60 (some true :: leftRev)
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

theorem controllerInitialRawBoolWordHeaderEmitter_run_writeSuffix61
    (leftRev : List (Option Bool)) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 7
        (config 61 leftRev []) =
      { state := ControllerInitialRawBoolWordHeaderEmitterDescription.halt
        tape :=
          tapeAtCells
            (List.append
              ([true, true, false, false, true, true, false].map some)
              leftRev)
            [] } := by
  simp [ControllerInitialRawBoolWordHeaderEmitterDescription,
    config, tapeAtCells, MachineDescription.runConfig,
    MachineDescription.stepConfig,
    MachineDescription.lookupTransition, MachineDescription.Matches,
    MachineDescription.transition, Tape.read, Tape.write,
    Tape.move, Tape.moveRight]

theorem controllerInitialRawBoolWordHeaderEmitter_run_finishSuffix
    (leftRev : List (Option Bool)) (output : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        (1 + ((output.length + 1) + 7))
        (config 36 leftRev
          (none :: List.append (output.map some) [none])) =
      { state := ControllerInitialRawBoolWordHeaderEmitterDescription.halt
        tape :=
          tapeAtCells
            (List.append
              ((List.append output
                (MachineDescription.encodeCodeWordAsInput
                  controllerInitialRawBoolWordHeaderEmitterSuffix)).reverse.map
                some)
              (none :: leftRev))
            [] } := by
  rw [MachineDescription.runConfig_add]
  have hfirst :
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig 1
        (config 36 leftRev
          (none :: List.append (output.map some) [none])) =
      config 60 (none :: leftRev)
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
  rw [controllerInitialRawBoolWordHeaderEmitter_run_scan60]
  rw [controllerInitialRawBoolWordHeaderEmitter_run_writeSuffix61]
  simp [controllerInitialRawBoolWordHeaderEmitterSuffix,
    MachineDescription.encodeNat,
    MachineDescription.encodeNatAppend,
    MachineDescription.encodeBoolWordAppend,
    MachineDescription.encodeCellListAppend,
    MachineDescription.encodeCellsAppend,
    MachineDescription.encodeCodeWordAsInput,
    MachineDescription.encodeCodeSymbolAsInput,
    List.reverse_append]

theorem controllerInitialRawBoolWordHeaderEmitterCountTicksBits_append_done
    (w : Word Bool) :
    List.append (controllerInitialRawBoolWordHeaderEmitterCountTicksBits w)
        [false, false, true, true] =
      MachineDescription.encodeCodeWordAsInput
        (MachineDescription.encodeNat w.length) := by
  induction w with
  | nil =>
      rfl
  | cons b rest ih =>
      cases b <;>
        simpa [controllerInitialRawBoolWordHeaderEmitterCountTicksBits,
          MachineDescription.encodeNat,
          MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput,
          List.append_assoc] using ih

theorem controllerInitialRawBoolWordHeaderEmitterCellBits_append_suffix
    (w : Word Bool) (suffix : Word MachineCodeSymbol) :
    List.append (controllerInitialRawBoolWordHeaderEmitterCellBits w)
        (MachineDescription.encodeCodeWordAsInput suffix) =
      MachineDescription.encodeCodeWordAsInput
        (MachineDescription.encodeCellsAppend (w.map some) suffix) := by
  induction w with
  | nil =>
      rfl
  | cons b rest ih =>
      cases b <;>
        simpa [controllerInitialRawBoolWordHeaderEmitterCellBits,
          MachineDescription.encodeCellsAppend,
          MachineDescription.encodeCellAppend,
          MachineDescription.encodeCell,
          MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput,
          List.append_assoc] using ih

theorem controllerInitialRawBoolWordHeaderEmitterOutput_bits_eq
    (w : Word Bool) :
    List.append
        (List.append
          (List.append
            (List.append [false, false, false, false]
              (controllerInitialRawBoolWordHeaderEmitterCountTicksBits w))
            [false, false, true, true])
          (controllerInitialRawBoolWordHeaderEmitterCellBits w))
        (MachineDescription.encodeCodeWordAsInput
          controllerInitialRawBoolWordHeaderEmitterSuffix) =
      controllerInitialRawBoolWordHeaderEmitterOutput w := by
  rw [show
      List.append
          (List.append
            (List.append
              (List.append [false, false, false, false]
                (controllerInitialRawBoolWordHeaderEmitterCountTicksBits w))
              [false, false, true, true])
            (controllerInitialRawBoolWordHeaderEmitterCellBits w))
          (MachineDescription.encodeCodeWordAsInput
            controllerInitialRawBoolWordHeaderEmitterSuffix) =
        List.append [false, false, false, false]
          (List.append
            (List.append
              (controllerInitialRawBoolWordHeaderEmitterCountTicksBits w)
              [false, false, true, true])
            (List.append
              (controllerInitialRawBoolWordHeaderEmitterCellBits w)
              (MachineDescription.encodeCodeWordAsInput
                controllerInitialRawBoolWordHeaderEmitterSuffix))) by
    simp [List.append_assoc]]
  rw [controllerInitialRawBoolWordHeaderEmitterCountTicksBits_append_done]
  rw [controllerInitialRawBoolWordHeaderEmitterCellBits_append_suffix]
  rw [← MachineDescription.encodeCodeWordAsInput_append]
  simp [controllerInitialRawBoolWordHeaderEmitterOutput,
    MachineDescription.encodeBoolWordAppend,
    MachineDescription.encodeCellListAppend,
    MachineDescription.encodeNatAppend,
    MachineDescription.encodeCodeWordAsInput,
    MachineDescription.encodeCodeSymbolAsInput]

theorem controllerInitialRawBoolWordHeaderEmitterDescription_run
    (w : Word Bool) :
    exists steps : Nat,
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig steps
          (ControllerInitialRawBoolWordHeaderEmitterDescription.initial w) =
        { state := ControllerInitialRawBoolWordHeaderEmitterDescription.halt
          tape := controllerInitialRawBoolWordHeaderEmitterFinalTape w } := by
  let headerBits : Word Bool := [false, false, false, false]
  let countBits : Word Bool :=
    controllerInitialRawBoolWordHeaderEmitterCountTicksBits w
  let doneBits : Word Bool := [false, false, true, true]
  let cellBits : Word Bool :=
    controllerInitialRawBoolWordHeaderEmitterCellBits w
  let outputBeforeCells : Word Bool :=
    List.append (List.append headerBits countBits) doneBits
  let outputBits : Word Bool := List.append outputBeforeCells cellBits
  rcases controllerInitialRawBoolWordHeaderEmitter_run_headerPrelude w with
    ⟨headerSteps, hheader⟩
  rcases
      controllerInitialRawBoolWordHeaderEmitter_run_countPass
        [none] w headerBits with
    ⟨countSteps, hcount⟩
  rcases
      controllerInitialRawBoolWordHeaderEmitter_run_doneSeparator_sentinel
        w.reverse (List.append headerBits countBits) with
    ⟨doneSteps, hdone⟩
  rcases
      controllerInitialRawBoolWordHeaderEmitter_run_cellPass
        [none] w outputBeforeCells with
    ⟨cellSteps, hcell⟩
  refine
    ⟨headerSteps + countSteps + doneSteps + cellSteps +
      (1 + ((outputBits.length + 1) + 7)), ?_⟩
  rw [show headerSteps + countSteps + doneSteps + cellSteps +
        (1 + ((outputBits.length + 1) + 7)) =
      headerSteps + (countSteps + (doneSteps + (cellSteps +
        (1 + ((outputBits.length + 1) + 7))))) by
      omega]
  rw [MachineDescription.runConfig_add]
  rw [hheader]
  rw [MachineDescription.runConfig_add]
  have hcount' :
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        countSteps
          (config 7 [none]
            (List.append (w.map some)
              (none :: List.append (headerBits.map some) [none]))) =
        config 7 (List.append (w.reverse.map some) [none])
          (none :: List.append
            ((List.append headerBits countBits).map some) [none]) := by
    simpa [headerBits, countBits] using hcount
  rw [hcount']
  rw [MachineDescription.runConfig_add]
  have hdone' :
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        doneSteps
          (config 7 (List.append (w.reverse.map some) [none])
            (none :: List.append
              ((List.append headerBits countBits).map some) [none])) =
        config 36 [none]
          (List.append (w.map some)
            (none :: List.append (outputBeforeCells.map some) [none])) := by
    simpa [headerBits, countBits, doneBits, outputBeforeCells,
      List.map_append, List.append_assoc] using hdone
  rw [hdone']
  rw [MachineDescription.runConfig_add]
  have hcell' :
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
        cellSteps
          (config 36 [none]
            (List.append (w.map some)
              (none :: List.append (outputBeforeCells.map some) [none]))) =
        config 36 (List.append (List.replicate w.length none) [none])
          (none :: List.append (outputBits.map some) [none]) := by
    simpa [outputBits, outputBeforeCells, cellBits] using hcell
  rw [hcell']
  rw [controllerInitialRawBoolWordHeaderEmitter_run_finishSuffix]
  have houtputBits :
      List.append outputBits
          (MachineDescription.encodeCodeWordAsInput
            controllerInitialRawBoolWordHeaderEmitterSuffix) =
        controllerInitialRawBoolWordHeaderEmitterOutput w := by
    simpa [outputBits, outputBeforeCells, headerBits, countBits, doneBits,
      cellBits, List.append_assoc] using
      controllerInitialRawBoolWordHeaderEmitterOutput_bits_eq w
  rw [houtputBits]
  simp [controllerInitialRawBoolWordHeaderEmitterFinalTape,
    List.replicate_succ]
  exact
    congrArg
      (fun pad : List (Option Bool) =>
        tapeAtCells
          (List.append
            ((controllerInitialRawBoolWordHeaderEmitterOutput w).map
              some).reverse
            pad)
          [])
      (controllerInitialRawBoolWordHeaderEmitter_twoBlankPadding w.length)

theorem controllerInitialRawBoolWordHeaderEmitterDescription_haltsWithOutput
    (w : Word Bool) :
    ControllerInitialRawBoolWordHeaderEmitterDescription.HaltsWithOutput w
      (controllerInitialRawBoolWordHeaderEmitterOutput w) := by
  rcases
      controllerInitialRawBoolWordHeaderEmitterDescription_run w with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  constructor
  · simpa [MachineDescription.HaltsWithOutputIn] using
      congrArg MachineDescription.Configuration.state hsteps
  · rw [show
        (ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig
          steps
          (ControllerInitialRawBoolWordHeaderEmitterDescription.initial
            w)).tape =
          controllerInitialRawBoolWordHeaderEmitterFinalTape w by
        simpa [MachineDescription.HaltsWithOutputIn] using
          congrArg MachineDescription.Configuration.tape hsteps]
    exact
      controllerInitialRawBoolWordHeaderEmitterFinalTape_normalizedOutput w

end DovetailInitialLayoutInitializer
end Computability
end FoC
