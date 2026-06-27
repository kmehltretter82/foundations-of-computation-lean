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

theorem controllerInitialRawBoolWordHeaderEmitterDescription_run
    (w : Word Bool) :
    exists steps : Nat,
      ControllerInitialRawBoolWordHeaderEmitterDescription.runConfig steps
          (ControllerInitialRawBoolWordHeaderEmitterDescription.initial w) =
        { state := ControllerInitialRawBoolWordHeaderEmitterDescription.halt
          tape := controllerInitialRawBoolWordHeaderEmitterFinalTape w } := by
  sorry

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
