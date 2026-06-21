import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.Basic

set_option doc.verso true

/-!
# Primitive closed facts for dovetail-layout scanners

This module contains closed-direction facts for the primitive field scanners.
It is deliberately separate from the large composed closed proof so the
field-level inversions can be developed and reused one scanner at a time.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace CanonicalLayouts
namespace DovetailLayoutScanner

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

theorem boolSuffixScannerDescription_runConfig_suffix_inv
    (flag : Bool) (baseLeft suffixCells : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (h :
      BoolSuffixScannerDescription.runConfig n
          { state := BoolSuffixScannerDescription.start
            tape := tapeAtCells baseLeft
              (List.append ((cellCodeBits (some flag)).map some)
                suffixCells) } =
        { state := BoolSuffixScannerDescription.halt
          tape := Tout }) :
    exists b : Bool,
    exists suffixTail : List (Option Bool),
      suffixCells = some b :: suffixTail ∧
        Tout = Tape.move Direction.left
          (tapeAtCells
            (List.append ((cellCodeBits (some flag)).reverse.map some)
              baseLeft)
            (some b :: suffixTail)) := by
  cases hflag : flag <;> cases n with
  | zero =>
      simp [BoolSuffixScannerDescription, MachineDescription.runConfig] at h
  | succ n1 =>
      cases n1 with
      | zero =>
          simp [hflag, BoolSuffixScannerDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches, MachineDescription.transition,
            keepMove, cellCodeBits, MachineDescription.encodeCell,
            MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight] at h
      | succ n2 =>
        cases n2 with
        | zero =>
          simp [hflag, BoolSuffixScannerDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches, MachineDescription.transition,
            keepMove, cellCodeBits, MachineDescription.encodeCell,
            MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight] at h
        | succ n3 =>
          cases n3 with
          | zero =>
            simp [hflag, BoolSuffixScannerDescription,
              MachineDescription.runConfig, MachineDescription.stepConfig,
              MachineDescription.lookupTransition,
              MachineDescription.Matches, MachineDescription.transition,
              keepMove, cellCodeBits, MachineDescription.encodeCell,
              MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput,
              tapeAtCells, Tape.read, Tape.write, Tape.move,
              Tape.moveRight] at h
          | succ n4 =>
            cases n4 with
            | zero =>
              simp [hflag, BoolSuffixScannerDescription,
                MachineDescription.runConfig, MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches, MachineDescription.transition,
                keepMove, cellCodeBits, MachineDescription.encodeCell,
                MachineDescription.encodeCodeWordAsInput,
                MachineDescription.encodeCodeSymbolAsInput,
                tapeAtCells, Tape.read, Tape.write, Tape.move,
                Tape.moveRight] at h
            | succ n5 =>
              cases suffixCells with
              | nil =>
                simp [hflag, BoolSuffixScannerDescription,
                  MachineDescription.runConfig, MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches, MachineDescription.transition,
                  keepMove, cellCodeBits, MachineDescription.encodeCell,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  tapeAtCells, Tape.read, Tape.write, Tape.move,
                  Tape.moveRight] at h
              | cons term rest =>
                cases term with
                | none =>
                  simp [hflag, BoolSuffixScannerDescription,
                    MachineDescription.runConfig, MachineDescription.stepConfig,
                    MachineDescription.lookupTransition,
                    MachineDescription.Matches, MachineDescription.transition,
                    keepMove, cellCodeBits, MachineDescription.encodeCell,
                    MachineDescription.encodeCodeWordAsInput,
                    MachineDescription.encodeCodeSymbolAsInput,
                    tapeAtCells, Tape.read, Tape.write, Tape.move,
                    Tape.moveRight] at h
                | some b =>
                  cases b
                  · refine ⟨false, rest, rfl, ?_⟩
                    let Tfinal : Tape Bool :=
                      Tape.move Direction.left
                        (tapeAtCells
                          (List.append
                            ((cellCodeBits (some flag)).reverse.map some)
                            baseLeft)
                          (some false :: rest))
                    have hsimp :
                        BoolSuffixScannerDescription.runConfig n5
                            { state := BoolSuffixScannerDescription.halt
                              tape := Tfinal } =
                          { state := BoolSuffixScannerDescription.halt
                            tape := Tout } := by
                      simpa [Tfinal, hflag, BoolSuffixScannerDescription,
                        MachineDescription.runConfig,
                        MachineDescription.stepConfig,
                        MachineDescription.lookupTransition,
                        MachineDescription.Matches,
                        MachineDescription.transition, keepMove, cellCodeBits,
                        MachineDescription.encodeCell,
                        MachineDescription.encodeCodeWordAsInput,
                        MachineDescription.encodeCodeSymbolAsInput,
                        tapeAtCells, Tape.read, Tape.write, Tape.move,
                        Tape.moveLeft, Tape.moveRight] using h
                    have hstay :=
                      MachineDescription.runConfig_halt
                        boolSuffixScannerDescription_haltTransitionFree
                        Tfinal n5
                    simpa [Tfinal, hflag] using
                      (congrArg MachineDescription.Configuration.tape
                        (hstay.symm.trans hsimp)).symm
                  · refine ⟨true, rest, rfl, ?_⟩
                    let Tfinal : Tape Bool :=
                      Tape.move Direction.left
                        (tapeAtCells
                          (List.append
                            ((cellCodeBits (some flag)).reverse.map some)
                            baseLeft)
                          (some true :: rest))
                    have hsimp :
                        BoolSuffixScannerDescription.runConfig n5
                            { state := BoolSuffixScannerDescription.halt
                              tape := Tfinal } =
                          { state := BoolSuffixScannerDescription.halt
                            tape := Tout } := by
                      simpa [Tfinal, hflag, BoolSuffixScannerDescription,
                        MachineDescription.runConfig,
                        MachineDescription.stepConfig,
                        MachineDescription.lookupTransition,
                        MachineDescription.Matches,
                        MachineDescription.transition, keepMove, cellCodeBits,
                        MachineDescription.encodeCell,
                        MachineDescription.encodeCodeWordAsInput,
                        MachineDescription.encodeCodeSymbolAsInput,
                        tapeAtCells, Tape.read, Tape.write, Tape.move,
                        Tape.moveLeft, Tape.moveRight] using h
                    have hstay :=
                      MachineDescription.runConfig_halt
                        boolSuffixScannerDescription_haltTransitionFree
                        Tfinal n5
                    simpa [Tfinal, hflag] using
                      (congrArg MachineDescription.Configuration.tape
                        (hstay.symm.trans hsimp)).symm

theorem boolFinalScannerDescription_runConfig_terminal_inv
    (flag : Bool) (baseLeft terminalCells : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (h :
      BoolFinalScannerDescription.runConfig n
          { state := BoolFinalScannerDescription.start
            tape := tapeAtCells baseLeft
              (List.append ((cellCodeBits (some flag)).map some)
                terminalCells) } =
        { state := BoolFinalScannerDescription.halt
          tape := Tout }) :
    (terminalCells = [] ∨
      exists rest : List (Option Bool), terminalCells = none :: rest) ∧
      Tout = Tape.move Direction.left
        (tapeAtCells
          (List.append ((cellCodeBits (some flag)).reverse.map some)
            baseLeft)
          terminalCells) := by
  cases hflag : flag <;> cases n with
  | zero =>
      simp [BoolFinalScannerDescription, MachineDescription.runConfig] at h
  | succ n1 =>
      cases n1 with
      | zero =>
          simp [hflag, BoolFinalScannerDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches, MachineDescription.transition,
            keepMove, cellCodeBits, MachineDescription.encodeCell,
            MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight] at h
      | succ n2 =>
        cases n2 with
        | zero =>
          simp [hflag, BoolFinalScannerDescription,
            MachineDescription.runConfig, MachineDescription.stepConfig,
            MachineDescription.lookupTransition,
            MachineDescription.Matches, MachineDescription.transition,
            keepMove, cellCodeBits, MachineDescription.encodeCell,
            MachineDescription.encodeCodeWordAsInput,
            MachineDescription.encodeCodeSymbolAsInput,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight] at h
        | succ n3 =>
          cases n3 with
          | zero =>
            simp [hflag, BoolFinalScannerDescription,
              MachineDescription.runConfig, MachineDescription.stepConfig,
              MachineDescription.lookupTransition,
              MachineDescription.Matches, MachineDescription.transition,
              keepMove, cellCodeBits, MachineDescription.encodeCell,
              MachineDescription.encodeCodeWordAsInput,
              MachineDescription.encodeCodeSymbolAsInput,
              tapeAtCells, Tape.read, Tape.write, Tape.move,
              Tape.moveRight] at h
          | succ n4 =>
            cases n4 with
            | zero =>
              simp [hflag, BoolFinalScannerDescription,
                MachineDescription.runConfig, MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches, MachineDescription.transition,
                keepMove, cellCodeBits, MachineDescription.encodeCell,
                MachineDescription.encodeCodeWordAsInput,
                MachineDescription.encodeCodeSymbolAsInput,
                tapeAtCells, Tape.read, Tape.write, Tape.move,
                Tape.moveRight] at h
            | succ n5 =>
              cases terminalCells with
              | nil =>
                constructor
                · exact Or.inl rfl
                · let Tfinal : Tape Bool :=
                    Tape.move Direction.left
                      (tapeAtCells
                        (List.append
                          ((cellCodeBits (some flag)).reverse.map some)
                          baseLeft)
                        [])
                  have hsimp :
                      BoolFinalScannerDescription.runConfig n5
                          { state := BoolFinalScannerDescription.halt
                            tape := Tfinal } =
                        { state := BoolFinalScannerDescription.halt
                          tape := Tout } := by
                    simpa [Tfinal, hflag, BoolFinalScannerDescription,
                      MachineDescription.runConfig,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches, MachineDescription.transition,
                      keepMove, cellCodeBits, MachineDescription.encodeCell,
                      MachineDescription.encodeCodeWordAsInput,
                      MachineDescription.encodeCodeSymbolAsInput,
                      tapeAtCells, Tape.read, Tape.write, Tape.move,
                      Tape.moveLeft, Tape.moveRight] using h
                  have hstay :=
                    MachineDescription.runConfig_halt
                      boolFinalScannerDescription_haltTransitionFree
                      Tfinal n5
                  simpa [Tfinal, hflag] using
                    (congrArg MachineDescription.Configuration.tape
                      (hstay.symm.trans hsimp)).symm
              | cons term rest =>
                cases term with
                | none =>
                  constructor
                  · exact Or.inr ⟨rest, rfl⟩
                  · let Tfinal : Tape Bool :=
                      Tape.move Direction.left
                        (tapeAtCells
                          (List.append
                            ((cellCodeBits (some flag)).reverse.map some)
                            baseLeft)
                          (none :: rest))
                    have hsimp :
                        BoolFinalScannerDescription.runConfig n5
                            { state := BoolFinalScannerDescription.halt
                              tape := Tfinal } =
                          { state := BoolFinalScannerDescription.halt
                            tape := Tout } := by
                      simpa [Tfinal, hflag, BoolFinalScannerDescription,
                        MachineDescription.runConfig,
                        MachineDescription.stepConfig,
                        MachineDescription.lookupTransition,
                        MachineDescription.Matches,
                        MachineDescription.transition, keepMove, cellCodeBits,
                        MachineDescription.encodeCell,
                        MachineDescription.encodeCodeWordAsInput,
                        MachineDescription.encodeCodeSymbolAsInput,
                        tapeAtCells, Tape.read, Tape.write, Tape.move,
                        Tape.moveLeft, Tape.moveRight] using h
                    have hstay :=
                      MachineDescription.runConfig_halt
                        boolFinalScannerDescription_haltTransitionFree
                        Tfinal n5
                    simpa [Tfinal, hflag] using
                      (congrArg MachineDescription.Configuration.tape
                        (hstay.symm.trans hsimp)).symm
                | some bit =>
                  cases bit <;>
                    simp [hflag, BoolFinalScannerDescription,
                      MachineDescription.runConfig,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches,
                      MachineDescription.transition, keepMove, cellCodeBits,
                      MachineDescription.encodeCell,
                      MachineDescription.encodeCodeWordAsInput,
                      MachineDescription.encodeCodeSymbolAsInput,
                      tapeAtCells, Tape.read, Tape.write, Tape.move,
                      Tape.moveRight] at h

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
