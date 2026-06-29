import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.PrimitiveClosed.Basic

set_option doc.verso true

/-!
# Primitive closed bool-suffix scanner facts

Late closed-direction facts for the primitive dovetail-layout scanners.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace CanonicalLayouts
namespace DovetailLayoutScanner

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

private abbrev BSS := BoolSuffixScannerDescription
private abbrev BFS := BoolFinalScannerDescription

theorem boolSuffixScannerDescription_runConfig_suffix_inv
    (flag : Bool) (baseLeft suffixCells : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (h :
      BSS.runConfig n
          { state := BSS.start
            tape := tapeAtCells baseLeft
              (List.append ((cellCodeBits (some flag)).map some)
                suffixCells) } =
        { state := BSS.halt
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
      simp [BoolSuffixScannerDescription, runConfig] at h
  | succ n1 =>
      cases n1 with
      | zero =>
          simp [hflag, BoolSuffixScannerDescription,
            runConfig, stepConfig,
            lookupTransition,
            Matches, transition,
            keepMove, cellCodeBits, encodeCell,
            encodeCodeWordAsInput,
            encodeCodeSymbolAsInput,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight] at h
      | succ n2 =>
        cases n2 with
        | zero =>
          simp [hflag, BoolSuffixScannerDescription,
            runConfig, stepConfig,
            lookupTransition,
            Matches, transition,
            keepMove, cellCodeBits, encodeCell,
            encodeCodeWordAsInput,
            encodeCodeSymbolAsInput,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight] at h
        | succ n3 =>
          cases n3 with
          | zero =>
            simp [hflag, BoolSuffixScannerDescription,
              runConfig, stepConfig,
              lookupTransition,
              Matches, transition,
              keepMove, cellCodeBits, encodeCell,
              encodeCodeWordAsInput,
              encodeCodeSymbolAsInput,
              tapeAtCells, Tape.read, Tape.write, Tape.move,
              Tape.moveRight] at h
          | succ n4 =>
            cases n4 with
            | zero =>
              simp [hflag, BoolSuffixScannerDescription,
                runConfig, stepConfig,
                lookupTransition,
                Matches, transition,
                keepMove, cellCodeBits, encodeCell,
                encodeCodeWordAsInput,
                encodeCodeSymbolAsInput,
                tapeAtCells, Tape.read, Tape.write, Tape.move,
                Tape.moveRight] at h
            | succ n5 =>
              cases suffixCells with
              | nil =>
                simp [hflag, BoolSuffixScannerDescription,
                  runConfig, stepConfig,
                  lookupTransition,
                  Matches, transition,
                  keepMove, cellCodeBits, encodeCell,
                  encodeCodeWordAsInput,
                  encodeCodeSymbolAsInput,
                  tapeAtCells, Tape.read, Tape.write, Tape.move,
                  Tape.moveRight] at h
              | cons term rest =>
                cases term with
                | none =>
                  simp [hflag, BoolSuffixScannerDescription,
                    runConfig, stepConfig,
                    lookupTransition,
                    Matches, transition,
                    keepMove, cellCodeBits, encodeCell,
                    encodeCodeWordAsInput,
                    encodeCodeSymbolAsInput,
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
                        BSS.runConfig n5
                            { state := BSS.halt
                              tape := Tfinal } =
                          { state := BSS.halt
                            tape := Tout } := by
                      simpa [Tfinal, hflag, BoolSuffixScannerDescription,
                        runConfig,
                        stepConfig,
                        lookupTransition,
                        Matches,
                        transition, keepMove, cellCodeBits,
                        encodeCell,
                        encodeCodeWordAsInput,
                        encodeCodeSymbolAsInput,
                        tapeAtCells, Tape.read, Tape.write, Tape.move,
                        Tape.moveLeft, Tape.moveRight] using h
                    have hstay :=
                      runConfig_halt
                        boolSuffixScannerDescription_haltTransitionFree
                        Tfinal n5
                    simpa [Tfinal, hflag] using
                      (congrArg Configuration.tape
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
                        BSS.runConfig n5
                            { state := BSS.halt
                              tape := Tfinal } =
                          { state := BSS.halt
                            tape := Tout } := by
                      simpa [Tfinal, hflag, BoolSuffixScannerDescription,
                        runConfig,
                        stepConfig,
                        lookupTransition,
                        Matches,
                        transition, keepMove, cellCodeBits,
                        encodeCell,
                        encodeCodeWordAsInput,
                        encodeCodeSymbolAsInput,
                        tapeAtCells, Tape.read, Tape.write, Tape.move,
                        Tape.moveLeft, Tape.moveRight] using h
                    have hstay :=
                      runConfig_halt
                        boolSuffixScannerDescription_haltTransitionFree
                        Tfinal n5
                    simpa [Tfinal, hflag] using
                      (congrArg Configuration.tape
                        (hstay.symm.trans hsimp)).symm

theorem boolFinalScannerDescription_runConfig_terminal_inv
    (flag : Bool) (baseLeft terminalCells : List (Option Bool))
    {Tout : Tape Bool} {n : Nat}
    (h :
      BFS.runConfig n
          { state := BFS.start
            tape := tapeAtCells baseLeft
              (List.append ((cellCodeBits (some flag)).map some)
                terminalCells) } =
        { state := BFS.halt
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
      simp [BoolFinalScannerDescription, runConfig] at h
  | succ n1 =>
      cases n1 with
      | zero =>
          simp [hflag, BoolFinalScannerDescription,
            runConfig, stepConfig,
            lookupTransition,
            Matches, transition,
            keepMove, cellCodeBits, encodeCell,
            encodeCodeWordAsInput,
            encodeCodeSymbolAsInput,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight] at h
      | succ n2 =>
        cases n2 with
        | zero =>
          simp [hflag, BoolFinalScannerDescription,
            runConfig, stepConfig,
            lookupTransition,
            Matches, transition,
            keepMove, cellCodeBits, encodeCell,
            encodeCodeWordAsInput,
            encodeCodeSymbolAsInput,
            tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight] at h
        | succ n3 =>
          cases n3 with
          | zero =>
            simp [hflag, BoolFinalScannerDescription,
              runConfig, stepConfig,
              lookupTransition,
              Matches, transition,
              keepMove, cellCodeBits, encodeCell,
              encodeCodeWordAsInput,
              encodeCodeSymbolAsInput,
              tapeAtCells, Tape.read, Tape.write, Tape.move,
              Tape.moveRight] at h
          | succ n4 =>
            cases n4 with
            | zero =>
              simp [hflag, BoolFinalScannerDescription,
                runConfig, stepConfig,
                lookupTransition,
                Matches, transition,
                keepMove, cellCodeBits, encodeCell,
                encodeCodeWordAsInput,
                encodeCodeSymbolAsInput,
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
                      BFS.runConfig n5
                          { state := BFS.halt
                            tape := Tfinal } =
                        { state := BFS.halt
                          tape := Tout } := by
                    simpa [Tfinal, hflag, BoolFinalScannerDescription,
                      runConfig,
                      stepConfig,
                      lookupTransition,
                      Matches, transition,
                      keepMove, cellCodeBits, encodeCell,
                      encodeCodeWordAsInput,
                      encodeCodeSymbolAsInput,
                      tapeAtCells, Tape.read, Tape.write, Tape.move,
                      Tape.moveLeft, Tape.moveRight] using h
                  have hstay :=
                    runConfig_halt
                      boolFinalScannerDescription_haltTransitionFree
                      Tfinal n5
                  simpa [Tfinal, hflag] using
                    (congrArg Configuration.tape
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
                        BFS.runConfig n5
                            { state := BFS.halt
                              tape := Tfinal } =
                          { state := BFS.halt
                            tape := Tout } := by
                      simpa [Tfinal, hflag, BoolFinalScannerDescription,
                        runConfig,
                        stepConfig,
                        lookupTransition,
                        Matches,
                        transition, keepMove, cellCodeBits,
                        encodeCell,
                        encodeCodeWordAsInput,
                        encodeCodeSymbolAsInput,
                        tapeAtCells, Tape.read, Tape.write, Tape.move,
                        Tape.moveLeft, Tape.moveRight] using h
                    have hstay :=
                      runConfig_halt
                        boolFinalScannerDescription_haltTransitionFree
                        Tfinal n5
                    simpa [Tfinal, hflag] using
                      (congrArg Configuration.tape
                        (hstay.symm.trans hsimp)).symm
                | some bit =>
                  cases bit <;>
                    simp [hflag, BoolFinalScannerDescription,
                      runConfig,
                      stepConfig,
                      lookupTransition,
                      Matches,
                      transition, keepMove, cellCodeBits,
                      encodeCell,
                      encodeCodeWordAsInput,
                      encodeCodeSymbolAsInput,
                      tapeAtCells, Tape.read, Tape.write, Tape.move,
                      Tape.moveRight] at h

private theorem encodeCodeWordAsInput_map_some_cons_inv
    {suffix : Word MachineCodeSymbol} {b : Bool}
    {suffixCellsTail : List (Option Bool)}
    (h :
      (encodeCodeWordAsInput suffix).map some =
        some b :: suffixCellsTail) :
    exists suffixTail : Word Bool,
      encodeCodeWordAsInput suffix = b :: suffixTail ∧
        suffixCellsTail = suffixTail.map some := by
  cases hbits : encodeCodeWordAsInput suffix with
  | nil =>
      simp [hbits] at h
  | cons bit suffixTail =>
      have hcons :
          some bit :: suffixTail.map some =
            some b :: suffixCellsTail := by
        simpa [hbits] using h
      injection hcons with hbit htail
      injection hbit with hbit'
      subst b
      subst suffixCellsTail
      exact ⟨suffixTail, rfl, rfl⟩

private theorem encodeCodeWordAsInput_map_some_eq_nil
    {code : Word MachineCodeSymbol}
    (h : (encodeCodeWordAsInput code).map some = []) :
    code = [] := by
  cases code with
  | nil =>
      rfl
  | cons symbol rest =>
      cases symbol <;>
        simp [encodeCodeWordAsInput,
          encodeCodeSymbolAsInput] at h

private theorem encodeCodeWordAsInput_map_some_ne_none_cons
    (code : Word MachineCodeSymbol) (rest : List (Option Bool)) :
    (encodeCodeWordAsInput code).map some ≠
      none :: rest := by
  intro h
  cases code with
  | nil =>
      simp [encodeCodeWordAsInput] at h
  | cons symbol suffix =>
      cases symbol <;>
        simp [encodeCodeWordAsInput,
          encodeCodeSymbolAsInput] at h

private theorem boolSuffixScannerDescription_runConfig_nil_ne_halt
    (baseLeft : List (Option Bool)) (n : Nat) :
    (BSS.runConfig n
      (config BSS.start baseLeft
        ([] : List (Option Bool)))).state ≠
      BSS.halt := by
  exact
    primitive_runConfig_state_ne_halt_of_reaches_stuck
      boolSuffixScannerDescription_haltTransitionFree
      (D := BSS)
      (c :=
        config BSS.start baseLeft
          ([] : List (Option Bool)))
      (stuck :=
        config BSS.start baseLeft
          ([] : List (Option Bool)))
      (k := 0) (n := n)
      rfl
      (by
        have hlookup :
            BSS.lookupTransition
              BSS.start none = none := by
          decide
        simp [config, tapeAtCells, stepConfig,
          hlookup, Tape.read])
      (by
        change (10 : Nat) ≠ 99
        omega)

private theorem boolSuffixScannerDescription_runConfig_true_start_ne_halt
    (baseLeft rest : List (Option Bool)) (n : Nat) :
    (BSS.runConfig n
      (config BSS.start baseLeft
        (some true :: rest))).state ≠
      BSS.halt := by
  exact
    primitive_runConfig_state_ne_halt_of_reaches_stuck
      boolSuffixScannerDescription_haltTransitionFree
      (D := BSS)
      (c :=
        config BSS.start baseLeft
          (some true :: rest))
      (stuck :=
        config BSS.start baseLeft
          (some true :: rest))
      (k := 0) (n := n)
      rfl
      (by
        have hlookup :
            BSS.lookupTransition
              BSS.start (some true) = none := by
          decide
        simp [config, tapeAtCells, stepConfig,
          hlookup, Tape.read])
      (by
        change (10 : Nat) ≠ 99
        omega)

private theorem boolSuffixScannerDescription_runConfig_false_false_ne_halt
    (baseLeft rest : List (Option Bool)) (n : Nat) :
    (BSS.runConfig n
      (config BSS.start baseLeft
        (some false :: some false :: rest))).state ≠
      BSS.halt := by
  let start : Configuration :=
    config BSS.start baseLeft
      (some false :: some false :: rest)
  let stuck : Configuration :=
    BSS.runConfig 1 start
  exact
    primitive_runConfig_state_ne_halt_of_reaches_stuck
      boolSuffixScannerDescription_haltTransitionFree
      (D := BSS)
      (c := start) (stuck := stuck) (k := 1) (n := n)
      rfl
      (by
        simp [stuck, start, BoolSuffixScannerDescription, config,
          tapeAtCells, keepMove, runConfig,
          stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight])
      (by
        simp [stuck, start, BoolSuffixScannerDescription, config,
          tapeAtCells, keepMove, runConfig,
          stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight])

private theorem boolSuffixScannerDescription_runConfig_false_true_false_false_ne_halt
    (baseLeft rest : List (Option Bool)) (n : Nat) :
    (BSS.runConfig n
      (config BSS.start baseLeft
        (some false :: some true :: some false :: some false :: rest))).state ≠
      BSS.halt := by
  let start : Configuration :=
    config BSS.start baseLeft
      (some false :: some true :: some false :: some false :: rest)
  let stuck : Configuration :=
    BSS.runConfig 3 start
  exact
    primitive_runConfig_state_ne_halt_of_reaches_stuck
      boolSuffixScannerDescription_haltTransitionFree
      (D := BSS)
      (c := start) (stuck := stuck) (k := 3) (n := n)
      rfl
      (by
        simp [stuck, start, BoolSuffixScannerDescription, config,
          tapeAtCells, keepMove, runConfig,
          stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight])
      (by
        simp [stuck, start, BoolSuffixScannerDescription, config,
          tapeAtCells, keepMove, runConfig,
          stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight])

private theorem boolSuffixScannerDescription_runConfig_false_true_true_true_ne_halt
    (baseLeft rest : List (Option Bool)) (n : Nat) :
    (BSS.runConfig n
      (config BSS.start baseLeft
        (some false :: some true :: some true :: some true :: rest))).state ≠
      BSS.halt := by
  let start : Configuration :=
    config BSS.start baseLeft
      (some false :: some true :: some true :: some true :: rest)
  let stuck : Configuration :=
    BSS.runConfig 3 start
  exact
    primitive_runConfig_state_ne_halt_of_reaches_stuck
      boolSuffixScannerDescription_haltTransitionFree
      (D := BSS)
      (c := start) (stuck := stuck) (k := 3) (n := n)
      rfl
      (by
        simp [stuck, start, BoolSuffixScannerDescription, config,
          tapeAtCells, keepMove, runConfig,
          stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight])
      (by
        simp [stuck, start, BoolSuffixScannerDescription, config,
          tapeAtCells, keepMove, runConfig,
          stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight])

theorem boolSuffixScannerDescription_runConfig_encodeBoolAppend_handoff
    (baseLeft : List (Option Bool)) (flag : Bool)
    (suffix : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      BSS.runConfig n
          (config BSS.start baseLeft
            ((encodeCodeWordAsInput
              (encodeBoolAppend flag suffix)).map
              some)) =
        { state := BSS.halt
          tape := Tout }) :
    exists b : Bool,
    exists suffixTail : Word Bool,
    exists baseAfter : List (Option Bool),
      encodeCodeWordAsInput suffix = b :: suffixTail ∧
        Tape.move Direction.right Tout =
          tapeAtCells baseAfter
            ((encodeCodeWordAsInput suffix).map some) := by
  have hraw :
      BSS.runConfig n
          { state := BSS.start
            tape := tapeAtCells baseLeft
              (List.append ((cellCodeBits (some flag)).map some)
                ((encodeCodeWordAsInput suffix).map
                  some)) } =
        { state := BSS.halt
          tape := Tout } := by
    simpa [config, boolBits_eq_encodeBoolAppend, List.map_append] using h
  rcases
      boolSuffixScannerDescription_runConfig_suffix_inv
        flag baseLeft
        ((encodeCodeWordAsInput suffix).map some)
        hraw with
    ⟨b, suffixCellsTail, hsuffixCells, hTout⟩
  rcases encodeCodeWordAsInput_map_some_cons_inv hsuffixCells with
    ⟨suffixTail, hsuffixBits, hsuffixCellsTail⟩
  refine
    ⟨b, suffixTail,
      List.append ((cellCodeBits (some flag)).reverse.map some) baseLeft,
      hsuffixBits, ?_⟩
  rw [hTout, hsuffixCellsTail]
  simpa [boolOnlySuffixHandoffConfigWithBase, hsuffixBits] using
    boolOnlySuffixHandoffConfigWithBase_move_right
      flag baseLeft b suffixTail

theorem boolSuffixScannerDescription_runConfig_code_handoff
    (baseLeft : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      BSS.runConfig n
          (config BSS.start baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state := BSS.halt
          tape := Tout }) :
    exists flag : Bool,
    exists suffix : Word MachineCodeSymbol,
    exists baseAfter : List (Option Bool),
      code = encodeBoolAppend flag suffix ∧
        Tape.move Direction.right Tout =
          tapeAtCells baseAfter
            ((encodeCodeWordAsInput suffix).map some) := by
  cases code with
  | nil =>
      have hstate :
          (BSS.runConfig n
            (config BSS.start baseLeft
              ([] : List (Option Bool)))).state =
            BSS.halt := by
        simpa [encodeCodeWordAsInput] using
          congrArg Configuration.state h
      exact False.elim
        ((boolSuffixScannerDescription_runConfig_nil_ne_halt
          baseLeft n) hstate)
  | cons symbol rest =>
      cases symbol with
      | header =>
          have hstate :
              (BSS.runConfig n
                (config BSS.start baseLeft
                  (some false :: some false :: some false :: some false ::
                    (encodeCodeWordAsInput rest).map
                      some))).state =
                BSS.halt := by
            simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              congrArg Configuration.state h
          exact False.elim
            ((boolSuffixScannerDescription_runConfig_false_false_ne_halt
              baseLeft
              (some false :: some false ::
                (encodeCodeWordAsInput rest).map some)
              n) hstate)
      | transition =>
          have hstate :
              (BSS.runConfig n
                (config BSS.start baseLeft
                  (some false :: some false :: some false :: some true ::
                    (encodeCodeWordAsInput rest).map
                      some))).state =
                BSS.halt := by
            simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              congrArg Configuration.state h
          exact False.elim
            ((boolSuffixScannerDescription_runConfig_false_false_ne_halt
              baseLeft
              (some false :: some true ::
                (encodeCodeWordAsInput rest).map some)
              n) hstate)
      | tick =>
          have hstate :
              (BSS.runConfig n
                (config BSS.start baseLeft
                  (some false :: some false :: some true :: some false ::
                    (encodeCodeWordAsInput rest).map
                      some))).state =
                BSS.halt := by
            simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              congrArg Configuration.state h
          exact False.elim
            ((boolSuffixScannerDescription_runConfig_false_false_ne_halt
              baseLeft
              (some true :: some false ::
                (encodeCodeWordAsInput rest).map some)
              n) hstate)
      | done =>
          have hstate :
              (BSS.runConfig n
                (config BSS.start baseLeft
                  (some false :: some false :: some true :: some true ::
                    (encodeCodeWordAsInput rest).map
                      some))).state =
                BSS.halt := by
            simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              congrArg Configuration.state h
          exact False.elim
            ((boolSuffixScannerDescription_runConfig_false_false_ne_halt
              baseLeft
              (some true :: some true ::
                (encodeCodeWordAsInput rest).map some)
              n) hstate)
      | blank =>
          have hstate :
              (BSS.runConfig n
                (config BSS.start baseLeft
                  (some false :: some true :: some false :: some false ::
                    (encodeCodeWordAsInput rest).map
                      some))).state =
                BSS.halt := by
            simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              congrArg Configuration.state h
          exact False.elim
            ((boolSuffixScannerDescription_runConfig_false_true_false_false_ne_halt
              baseLeft ((encodeCodeWordAsInput rest).map some)
              n) hstate)
      | zero =>
          rcases
              boolSuffixScannerDescription_runConfig_encodeBoolAppend_handoff
                baseLeft false rest
                (by
                  simpa [encodeBoolAppend,
                    encodeCellAppend] using h) with
            ⟨_b, _suffixTail, baseAfter, _hsuffixBits, hmove⟩
          exact ⟨false, rest, baseAfter, rfl, hmove⟩
      | one =>
          rcases
              boolSuffixScannerDescription_runConfig_encodeBoolAppend_handoff
                baseLeft true rest
                (by
                  simpa [encodeBoolAppend,
                    encodeCellAppend] using h) with
            ⟨_b, _suffixTail, baseAfter, _hsuffixBits, hmove⟩
          exact ⟨true, rest, baseAfter, rfl, hmove⟩
      | moveLeft =>
          have hstate :
              (BSS.runConfig n
                (config BSS.start baseLeft
                  (some false :: some true :: some true :: some true ::
                    (encodeCodeWordAsInput rest).map
                      some))).state =
                BSS.halt := by
            simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              congrArg Configuration.state h
          exact False.elim
            ((boolSuffixScannerDescription_runConfig_false_true_true_true_ne_halt
              baseLeft ((encodeCodeWordAsInput rest).map some)
              n) hstate)
      | moveRight =>
          have hstate :
              (BSS.runConfig n
                (config BSS.start baseLeft
                  (some true :: some false :: some false :: some false ::
                    (encodeCodeWordAsInput rest).map
                      some))).state =
                BSS.halt := by
            simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              congrArg Configuration.state h
          exact False.elim
            ((boolSuffixScannerDescription_runConfig_true_start_ne_halt
              baseLeft
              (some false :: some false :: some false ::
                (encodeCodeWordAsInput rest).map some)
              n) hstate)

theorem boolFinalScannerDescription_runConfig_encodeBoolAppend_terminal_inv
    (baseLeft : List (Option Bool)) (flag : Bool)
    (suffix : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      BFS.runConfig n
          (config BFS.start baseLeft
            ((encodeCodeWordAsInput
              (encodeBoolAppend flag suffix)).map
              some)) =
        { state := BFS.halt
          tape := Tout }) :
    suffix = [] ∧
      Tape.move Direction.right Tout =
        tapeAtCells
          (List.append ((cellCodeBits (some flag)).reverse.map some)
            baseLeft)
          [] := by
  have hraw :
      BFS.runConfig n
          { state := BFS.start
            tape := tapeAtCells baseLeft
              (List.append ((cellCodeBits (some flag)).map some)
                ((encodeCodeWordAsInput suffix).map
                  some)) } =
        { state := BFS.halt
          tape := Tout } := by
    simpa [config, boolBits_eq_encodeBoolAppend, List.map_append] using h
  rcases
      boolFinalScannerDescription_runConfig_terminal_inv
        flag baseLeft
        ((encodeCodeWordAsInput suffix).map some)
        hraw with
    ⟨hterminal, hTout⟩
  have hsuffix : suffix = [] := by
    cases hterminal with
    | inl hnil =>
        exact encodeCodeWordAsInput_map_some_eq_nil hnil
    | inr hnone =>
        rcases hnone with ⟨rest, hnone⟩
        exact False.elim
          (encodeCodeWordAsInput_map_some_ne_none_cons suffix rest hnone)
  constructor
  · exact hsuffix
  · subst suffix
    rw [hTout]
    simpa [boolFinalHandoffConfigWithBase,
      encodeCodeWordAsInput] using
      boolFinalHandoffConfigWithBase_move_right flag baseLeft

private theorem boolFinalScannerDescription_runConfig_nil_ne_halt
    (baseLeft : List (Option Bool)) (n : Nat) :
    (BFS.runConfig n
      (config BFS.start baseLeft
        ([] : List (Option Bool)))).state ≠
      BFS.halt := by
  exact
    primitive_runConfig_state_ne_halt_of_reaches_stuck
      boolFinalScannerDescription_haltTransitionFree
      (D := BFS)
      (c :=
        config BFS.start baseLeft
          ([] : List (Option Bool)))
      (stuck :=
        config BFS.start baseLeft
          ([] : List (Option Bool)))
      (k := 0) (n := n)
      rfl
      (by
        have hlookup :
            BFS.lookupTransition
              BFS.start none = none := by
          decide
        simp [config, tapeAtCells, stepConfig,
          hlookup, Tape.read])
      (by
        change (10 : Nat) ≠ 99
        omega)

private theorem boolFinalScannerDescription_runConfig_true_start_ne_halt
    (baseLeft rest : List (Option Bool)) (n : Nat) :
    (BFS.runConfig n
      (config BFS.start baseLeft
        (some true :: rest))).state ≠
      BFS.halt := by
  exact
    primitive_runConfig_state_ne_halt_of_reaches_stuck
      boolFinalScannerDescription_haltTransitionFree
      (D := BFS)
      (c :=
        config BFS.start baseLeft
          (some true :: rest))
      (stuck :=
        config BFS.start baseLeft
          (some true :: rest))
      (k := 0) (n := n)
      rfl
      (by
        have hlookup :
            BFS.lookupTransition
              BFS.start (some true) = none := by
          decide
        simp [config, tapeAtCells, stepConfig,
          hlookup, Tape.read])
      (by
        change (10 : Nat) ≠ 99
        omega)

private theorem boolFinalScannerDescription_runConfig_false_false_ne_halt
    (baseLeft rest : List (Option Bool)) (n : Nat) :
    (BFS.runConfig n
      (config BFS.start baseLeft
        (some false :: some false :: rest))).state ≠
      BFS.halt := by
  let start : Configuration :=
    config BFS.start baseLeft
      (some false :: some false :: rest)
  let stuck : Configuration :=
    BFS.runConfig 1 start
  exact
    primitive_runConfig_state_ne_halt_of_reaches_stuck
      boolFinalScannerDescription_haltTransitionFree
      (D := BFS)
      (c := start) (stuck := stuck) (k := 1) (n := n)
      rfl
      (by
        simp [stuck, start, BoolFinalScannerDescription, config,
          tapeAtCells, keepMove, runConfig,
          stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight])
      (by
        simp [stuck, start, BoolFinalScannerDescription, config,
          tapeAtCells, keepMove, runConfig,
          stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight])

private theorem boolFinalScannerDescription_runConfig_false_true_false_false_ne_halt
    (baseLeft rest : List (Option Bool)) (n : Nat) :
    (BFS.runConfig n
      (config BFS.start baseLeft
        (some false :: some true :: some false :: some false :: rest))).state ≠
      BFS.halt := by
  let start : Configuration :=
    config BFS.start baseLeft
      (some false :: some true :: some false :: some false :: rest)
  let stuck : Configuration :=
    BFS.runConfig 3 start
  exact
    primitive_runConfig_state_ne_halt_of_reaches_stuck
      boolFinalScannerDescription_haltTransitionFree
      (D := BFS)
      (c := start) (stuck := stuck) (k := 3) (n := n)
      rfl
      (by
        simp [stuck, start, BoolFinalScannerDescription, config,
          tapeAtCells, keepMove, runConfig,
          stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight])
      (by
        simp [stuck, start, BoolFinalScannerDescription, config,
          tapeAtCells, keepMove, runConfig,
          stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight])

private theorem boolFinalScannerDescription_runConfig_false_true_true_true_ne_halt
    (baseLeft rest : List (Option Bool)) (n : Nat) :
    (BFS.runConfig n
      (config BFS.start baseLeft
        (some false :: some true :: some true :: some true :: rest))).state ≠
      BFS.halt := by
  let start : Configuration :=
    config BFS.start baseLeft
      (some false :: some true :: some true :: some true :: rest)
  let stuck : Configuration :=
    BFS.runConfig 3 start
  exact
    primitive_runConfig_state_ne_halt_of_reaches_stuck
      boolFinalScannerDescription_haltTransitionFree
      (D := BFS)
      (c := start) (stuck := stuck) (k := 3) (n := n)
      rfl
      (by
        simp [stuck, start, BoolFinalScannerDescription, config,
          tapeAtCells, keepMove, runConfig,
          stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight])
      (by
        simp [stuck, start, BoolFinalScannerDescription, config,
          tapeAtCells, keepMove, runConfig,
          stepConfig,
          lookupTransition, Matches,
          transition, Tape.read, Tape.write, Tape.move,
          Tape.moveRight])

theorem boolFinalScannerDescription_runConfig_code_terminal_inv
    (baseLeft : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      BFS.runConfig n
          (config BFS.start baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state := BFS.halt
          tape := Tout }) :
    exists flag : Bool,
      code = encodeBoolAppend flag [] ∧
        Tape.move Direction.right Tout =
          tapeAtCells
            (List.append ((cellCodeBits (some flag)).reverse.map some)
              baseLeft)
            [] := by
  cases code with
  | nil =>
      have hstate :
          (BFS.runConfig n
            (config BFS.start baseLeft
              ([] : List (Option Bool)))).state =
            BFS.halt := by
        simpa [encodeCodeWordAsInput] using
          congrArg Configuration.state h
      exact False.elim
        ((boolFinalScannerDescription_runConfig_nil_ne_halt
          baseLeft n) hstate)
  | cons symbol rest =>
      cases symbol with
      | header =>
          have hstate :
              (BFS.runConfig n
                (config BFS.start baseLeft
                  (some false :: some false :: some false :: some false ::
                    (encodeCodeWordAsInput rest).map
                      some))).state =
                BFS.halt := by
            simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              congrArg Configuration.state h
          exact False.elim
            ((boolFinalScannerDescription_runConfig_false_false_ne_halt
              baseLeft
              (some false :: some false ::
                (encodeCodeWordAsInput rest).map some)
              n) hstate)
      | transition =>
          have hstate :
              (BFS.runConfig n
                (config BFS.start baseLeft
                  (some false :: some false :: some false :: some true ::
                    (encodeCodeWordAsInput rest).map
                      some))).state =
                BFS.halt := by
            simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              congrArg Configuration.state h
          exact False.elim
            ((boolFinalScannerDescription_runConfig_false_false_ne_halt
              baseLeft
              (some false :: some true ::
                (encodeCodeWordAsInput rest).map some)
              n) hstate)
      | tick =>
          have hstate :
              (BFS.runConfig n
                (config BFS.start baseLeft
                  (some false :: some false :: some true :: some false ::
                    (encodeCodeWordAsInput rest).map
                      some))).state =
                BFS.halt := by
            simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              congrArg Configuration.state h
          exact False.elim
            ((boolFinalScannerDescription_runConfig_false_false_ne_halt
              baseLeft
              (some true :: some false ::
                (encodeCodeWordAsInput rest).map some)
              n) hstate)
      | done =>
          have hstate :
              (BFS.runConfig n
                (config BFS.start baseLeft
                  (some false :: some false :: some true :: some true ::
                    (encodeCodeWordAsInput rest).map
                      some))).state =
                BFS.halt := by
            simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              congrArg Configuration.state h
          exact False.elim
            ((boolFinalScannerDescription_runConfig_false_false_ne_halt
              baseLeft
              (some true :: some true ::
                (encodeCodeWordAsInput rest).map some)
              n) hstate)
      | blank =>
          have hstate :
              (BFS.runConfig n
                (config BFS.start baseLeft
                  (some false :: some true :: some false :: some false ::
                    (encodeCodeWordAsInput rest).map
                      some))).state =
                BFS.halt := by
            simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              congrArg Configuration.state h
          exact False.elim
            ((boolFinalScannerDescription_runConfig_false_true_false_false_ne_halt
              baseLeft ((encodeCodeWordAsInput rest).map some)
              n) hstate)
      | zero =>
          rcases
              boolFinalScannerDescription_runConfig_encodeBoolAppend_terminal_inv
                baseLeft false rest
                (by
                  simpa [encodeBoolAppend,
                    encodeCellAppend] using h) with
            ⟨hrest, hmove⟩
          subst rest
          exact ⟨false, rfl, hmove⟩
      | one =>
          rcases
              boolFinalScannerDescription_runConfig_encodeBoolAppend_terminal_inv
                baseLeft true rest
                (by
                  simpa [encodeBoolAppend,
                    encodeCellAppend] using h) with
            ⟨hrest, hmove⟩
          subst rest
          exact ⟨true, rfl, hmove⟩
      | moveLeft =>
          have hstate :
              (BFS.runConfig n
                (config BFS.start baseLeft
                  (some false :: some true :: some true :: some true ::
                    (encodeCodeWordAsInput rest).map
                      some))).state =
                BFS.halt := by
            simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              congrArg Configuration.state h
          exact False.elim
            ((boolFinalScannerDescription_runConfig_false_true_true_true_ne_halt
              baseLeft ((encodeCodeWordAsInput rest).map some)
              n) hstate)
      | moveRight =>
          have hstate :
              (BFS.runConfig n
                (config BFS.start baseLeft
                  (some true :: some false :: some false :: some false ::
                    (encodeCodeWordAsInput rest).map
                      some))).state =
                BFS.halt := by
            simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              congrArg Configuration.state h
          exact False.elim
            ((boolFinalScannerDescription_runConfig_true_start_ne_halt
              baseLeft
              (some false :: some false :: some false ::
                (encodeCodeWordAsInput rest).map some)
              n) hstate)

theorem finalHitFlagsScannerDescription_runConfig_encodeBoolAppend_terminal_inv
    (baseLeft : List (Option Bool))
    (acceptHit rejectHit : Bool)
    (suffix : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      FinalHitFlagsScannerDescription.runConfig n
          (config FinalHitFlagsScannerDescription.start baseLeft
            ((encodeCodeWordAsInput
              (encodeBoolAppend acceptHit
                (encodeBoolAppend rejectHit
                  suffix))).map some)) =
        { state := FinalHitFlagsScannerDescription.halt
          tape := Tout }) :
    suffix = [] ∧
      exists baseAfter : List (Option Bool),
        Tape.move Direction.right Tout = tapeAtCells baseAfter [] := by
  have hseq :
      (seqSubroutine
        BSS
        BFS
        Direction.right).runConfig n
          (config
            (seqSubroutine
              BSS
              BFS
              Direction.right).start
            baseLeft
            ((encodeCodeWordAsInput
              (encodeBoolAppend acceptHit
                (encodeBoolAppend rejectHit
                  suffix))).map some)) =
        { state :=
            (seqSubroutine
              BSS
              BFS
              Direction.right).halt
          tape := Tout } := by
    simpa [FinalHitFlagsScannerDescription, config] using h
  rcases
      seqSubroutine_runConfig_inv
        (A := BSS)
        (B := BFS)
        (handoffMove := Direction.right)
        boolSuffixScannerDescription_subroutineReady
        boolFinalScannerDescription_subroutineReady
        hseq with
    ⟨TacceptHit, hacceptHit, hrejectHit⟩
  rcases hacceptHit with ⟨nAcceptHit, hacceptHitRun, _hacceptHitFirst⟩
  rcases
      boolSuffixScannerDescription_runConfig_encodeBoolAppend_handoff
        baseLeft acceptHit
        (encodeBoolAppend rejectHit suffix)
        (by simpa [config] using hacceptHitRun) with
    ⟨_rejectFirstBit, _rejectSuffixTail, baseAfterAcceptHit,
      _hrejectBits, hacceptHitMove⟩
  rcases hrejectHit with ⟨nRejectHit, hrejectHitRun⟩
  have hrejectHitCodeRun :
      BFS.runConfig nRejectHit
          (config BFS.start baseAfterAcceptHit
            ((encodeCodeWordAsInput
              (encodeBoolAppend rejectHit suffix)).map
              some)) =
        { state := BFS.halt
          tape := Tout } := by
    simpa [config, hacceptHitMove] using hrejectHitRun
  rcases
      boolFinalScannerDescription_runConfig_encodeBoolAppend_terminal_inv
        baseAfterAcceptHit rejectHit suffix hrejectHitCodeRun with
    ⟨hsuffix, hmove⟩
  exact
    ⟨hsuffix,
      List.append ((cellCodeBits (some rejectHit)).reverse.map some)
        baseAfterAcceptHit,
      hmove⟩

theorem finalHitFlagsScannerDescription_runConfig_code_inv
    (baseLeft : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      FinalHitFlagsScannerDescription.runConfig n
          (config FinalHitFlagsScannerDescription.start baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state := FinalHitFlagsScannerDescription.halt
          tape := Tout }) :
    exists acceptHit : Bool,
    exists rejectHit : Bool,
    exists baseAfter : List (Option Bool),
      code =
        encodeBoolAppend acceptHit
          (encodeBoolAppend rejectHit []) ∧
        Tape.move Direction.right Tout =
          tapeAtCells baseAfter [] := by
  have hseq :
      (seqSubroutine
        BSS
        BFS
        Direction.right).runConfig n
          (config
            (seqSubroutine
              BSS
              BFS
              Direction.right).start
            baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state :=
            (seqSubroutine
              BSS
              BFS
              Direction.right).halt
          tape := Tout } := by
    simpa [FinalHitFlagsScannerDescription, config] using h
  rcases
      seqSubroutine_runConfig_inv
        (A := BSS)
        (B := BFS)
        (handoffMove := Direction.right)
        boolSuffixScannerDescription_subroutineReady
        boolFinalScannerDescription_subroutineReady
        hseq with
    ⟨TacceptHit, hacceptHit, hrejectHit⟩
  rcases hacceptHit with ⟨nAcceptHit, hacceptHitRun, _hacceptHitFirst⟩
  rcases
      boolSuffixScannerDescription_runConfig_code_handoff
        baseLeft code (by simpa [config] using hacceptHitRun) with
    ⟨acceptHit, rejectCode, baseAfterAcceptHit, hcode,
      hacceptHitMove⟩
  rcases hrejectHit with ⟨nRejectHit, hrejectHitRun⟩
  have hrejectHitCodeRun :
      BFS.runConfig nRejectHit
          (config BFS.start baseAfterAcceptHit
            ((encodeCodeWordAsInput rejectCode).map
              some)) =
        { state := BFS.halt
          tape := Tout } := by
    simpa [config, hacceptHitMove] using hrejectHitRun
  rcases
      boolFinalScannerDescription_runConfig_code_terminal_inv
        baseAfterAcceptHit rejectCode hrejectHitCodeRun with
    ⟨rejectHit, hrejectCode, hmove⟩
  refine
    ⟨acceptHit, rejectHit,
      List.append ((cellCodeBits (some rejectHit)).reverse.map some)
        baseAfterAcceptHit,
      ?_, hmove⟩
  simp [hcode, hrejectCode]


end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
