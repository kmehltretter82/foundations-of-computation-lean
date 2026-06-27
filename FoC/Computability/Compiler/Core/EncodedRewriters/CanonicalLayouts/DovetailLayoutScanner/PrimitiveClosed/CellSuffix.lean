import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.BoolWordClosed
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.CellListClosed

set_option doc.verso true

/-!
# Closed cell- and tape-suffix scanner facts

These are closed-direction contracts for the single-cell scanner and the
composed tape scanner.  They live with the scanner implementation so parser
proofs can consume a stable CommonGround contract instead of unpacking the
finite machines locally.
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

private theorem cellSuffixScannerDescription_runConfig_nil_ne_halt
    (baseLeft : List (Option Bool)) (n : Nat) :
    (CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
      n
      (config
        CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
        baseLeft ([] : List (Option Bool)))).state ≠
      CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.halt := by
  exact
    CanonicalLayouts.DovetailLayoutScanner.primitive_runConfig_state_ne_halt_of_reaches_stuck
      CanonicalLayouts.DovetailLayoutScanner.cellSuffixScannerDescription_haltTransitionFree
      (D := CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription)
      (c :=
        config
          CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
          baseLeft ([] : List (Option Bool)))
      (stuck :=
        config
          CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
          baseLeft ([] : List (Option Bool)))
      (k := 0) (n := n)
      rfl
      (by
        have hlookup :
            CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.lookupTransition
              CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
              none = none := by
          native_decide
        simp [config, tapeAtCells, stepConfig,
          hlookup, Tape.read])
      (by
        change (10 : Nat) ≠ 99
        omega)

private theorem cellSuffixScannerDescription_runConfig_true_start_ne_halt
    (baseLeft rest : List (Option Bool)) (n : Nat) :
    (CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
      n
      (config
        CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
        baseLeft (some true :: rest))).state ≠
      CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.halt := by
  exact
    CanonicalLayouts.DovetailLayoutScanner.primitive_runConfig_state_ne_halt_of_reaches_stuck
      CanonicalLayouts.DovetailLayoutScanner.cellSuffixScannerDescription_haltTransitionFree
      (D := CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription)
      (c :=
        config
          CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
          baseLeft (some true :: rest))
      (stuck :=
        config
          CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
          baseLeft (some true :: rest))
      (k := 0) (n := n)
      rfl
      (by
        have hlookup :
            CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.lookupTransition
              CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
              (some true) = none := by
          native_decide
        simp [config, tapeAtCells, stepConfig,
          hlookup, Tape.read])
      (by
        change (10 : Nat) ≠ 99
        omega)

private theorem cellSuffixScannerDescription_runConfig_false_false_ne_halt
    (baseLeft rest : List (Option Bool)) (n : Nat) :
    (CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
      n
      (config
        CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
        baseLeft (some false :: some false :: rest))).state ≠
      CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.halt := by
  let start : Configuration :=
    config
      CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
      baseLeft (some false :: some false :: rest)
  let stuck : Configuration :=
    CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
      1 start
  exact
    CanonicalLayouts.DovetailLayoutScanner.primitive_runConfig_state_ne_halt_of_reaches_stuck
      CanonicalLayouts.DovetailLayoutScanner.cellSuffixScannerDescription_haltTransitionFree
      (D := CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription)
      (c := start) (stuck := stuck) (k := 1) (n := n)
      rfl
      (by
        simp [stuck, start,
          CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription,
          config, tapeAtCells, keepMove,
          runConfig,
          stepConfig,
          lookupTransition,
          Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveRight])
      (by
        simp [stuck, start,
          CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription,
          config, tapeAtCells, keepMove,
          runConfig,
          stepConfig,
          lookupTransition,
          Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveRight])

private theorem cellSuffixScannerDescription_runConfig_false_true_true_ne_halt
    (baseLeft rest : List (Option Bool)) (n : Nat) :
    (CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
      n
      (config
        CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
        baseLeft
        (some false :: some true :: some true :: some true :: rest))).state ≠
      CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.halt := by
  let start : Configuration :=
    config
      CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
      baseLeft
      (some false :: some true :: some true :: some true :: rest)
  let stuck : Configuration :=
    CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
      3 start
  exact
    CanonicalLayouts.DovetailLayoutScanner.primitive_runConfig_state_ne_halt_of_reaches_stuck
      CanonicalLayouts.DovetailLayoutScanner.cellSuffixScannerDescription_haltTransitionFree
      (D := CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription)
      (c := start) (stuck := stuck) (k := 3) (n := n)
      rfl
      (by
        simp [stuck, start,
          CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription,
          config, tapeAtCells, keepMove,
          runConfig,
          stepConfig,
          lookupTransition,
          Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveRight])
      (by
        simp [stuck, start,
          CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription,
          config, tapeAtCells, keepMove,
          runConfig,
          stepConfig,
          lookupTransition,
          Matches, transition,
          Tape.read, Tape.write, Tape.move, Tape.moveRight])

theorem cellSuffixScannerDescription_runConfig_code_inv
    (baseLeft : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
          n
          (config
            CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
            baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state :=
            CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.halt
          tape := Tout }) :
    exists cell : Option Bool,
    exists suffix : Word MachineCodeSymbol,
      code = encodeCellAppend cell suffix := by
  cases code with
  | nil =>
      have hstate :
          (CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
            n
            (config
              CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
              baseLeft ([] : List (Option Bool)))).state =
            CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.halt := by
        simpa [encodeCodeWordAsInput] using
          congrArg Configuration.state h
      exact False.elim
        ((cellSuffixScannerDescription_runConfig_nil_ne_halt
          baseLeft n) hstate)
  | cons symbol rest =>
      cases symbol with
      | header =>
          have hstate :
              (CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
                n
                (config
                  CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
                  baseLeft
                  (some false :: some false :: some false :: some false ::
                    (encodeCodeWordAsInput rest).map
                      some))).state =
                CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.halt := by
            simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              congrArg Configuration.state h
          exact False.elim
            ((cellSuffixScannerDescription_runConfig_false_false_ne_halt
              baseLeft
              (some false :: some false ::
                (encodeCodeWordAsInput rest).map some)
              n) hstate)
      | transition =>
          have hstate :
              (CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
                n
                (config
                  CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
                  baseLeft
                  (some false :: some false :: some false :: some true ::
                    (encodeCodeWordAsInput rest).map
                      some))).state =
                CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.halt := by
            simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              congrArg Configuration.state h
          exact False.elim
            ((cellSuffixScannerDescription_runConfig_false_false_ne_halt
              baseLeft
              (some false :: some true ::
                (encodeCodeWordAsInput rest).map some)
              n) hstate)
      | tick =>
          have hstate :
              (CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
                n
                (config
                  CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
                  baseLeft
                  (some false :: some false :: some true :: some false ::
                    (encodeCodeWordAsInput rest).map
                      some))).state =
                CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.halt := by
            simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              congrArg Configuration.state h
          exact False.elim
            ((cellSuffixScannerDescription_runConfig_false_false_ne_halt
              baseLeft
              (some true :: some false ::
                (encodeCodeWordAsInput rest).map some)
              n) hstate)
      | done =>
          have hstate :
              (CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
                n
                (config
                  CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
                  baseLeft
                  (some false :: some false :: some true :: some true ::
                    (encodeCodeWordAsInput rest).map
                      some))).state =
                CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.halt := by
            simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              congrArg Configuration.state h
          exact False.elim
            ((cellSuffixScannerDescription_runConfig_false_false_ne_halt
              baseLeft
              (some true :: some true ::
                (encodeCodeWordAsInput rest).map some)
              n) hstate)
      | blank =>
          exact ⟨none, rest, rfl⟩
      | zero =>
          exact ⟨some false, rest, rfl⟩
      | one =>
          exact ⟨some true, rest, rfl⟩
      | moveLeft =>
          have hstate :
              (CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
                n
                (config
                  CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
                  baseLeft
                  (some false :: some true :: some true :: some true ::
                    (encodeCodeWordAsInput rest).map
                      some))).state =
                CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.halt := by
            simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              congrArg Configuration.state h
          exact False.elim
            ((cellSuffixScannerDescription_runConfig_false_true_true_ne_halt
              baseLeft
              ((encodeCodeWordAsInput rest).map some)
              n) hstate)
      | moveRight =>
          have hstate :
              (CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
                n
                (config
                  CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
                  baseLeft
                  (some true :: some false :: some false :: some false ::
                    (encodeCodeWordAsInput rest).map
                      some))).state =
                CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.halt := by
            simpa [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput] using
              congrArg Configuration.state h
          exact False.elim
            ((cellSuffixScannerDescription_runConfig_true_start_ne_halt
              baseLeft
              (some false :: some false :: some false ::
                (encodeCodeWordAsInput rest).map some)
              n) hstate)

theorem encodeCodeWordAsInput_cons_bits
    (symbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    exists b : Bool,
    exists tail : Word Bool,
      encodeCodeWordAsInput (symbol :: rest) =
        b :: tail := by
  cases symbol
  · refine ⟨false, List.append [false, false, false]
      (encodeCodeWordAsInput rest), ?_⟩
    simp [encodeCodeWordAsInput,
      encodeCodeSymbolAsInput]
  · refine ⟨false, List.append [false, false, true]
      (encodeCodeWordAsInput rest), ?_⟩
    simp [encodeCodeWordAsInput,
      encodeCodeSymbolAsInput]
  · refine ⟨false, List.append [false, true, false]
      (encodeCodeWordAsInput rest), ?_⟩
    simp [encodeCodeWordAsInput,
      encodeCodeSymbolAsInput]
  · refine ⟨false, List.append [false, true, true]
      (encodeCodeWordAsInput rest), ?_⟩
    simp [encodeCodeWordAsInput,
      encodeCodeSymbolAsInput]
  · refine ⟨false, List.append [true, false, false]
      (encodeCodeWordAsInput rest), ?_⟩
    simp [encodeCodeWordAsInput,
      encodeCodeSymbolAsInput]
  · refine ⟨false, List.append [true, false, true]
      (encodeCodeWordAsInput rest), ?_⟩
    simp [encodeCodeWordAsInput,
      encodeCodeSymbolAsInput]
  · refine ⟨false, List.append [true, true, false]
      (encodeCodeWordAsInput rest), ?_⟩
    simp [encodeCodeWordAsInput,
      encodeCodeSymbolAsInput]
  · refine ⟨false, List.append [true, true, true]
      (encodeCodeWordAsInput rest), ?_⟩
    simp [encodeCodeWordAsInput,
      encodeCodeSymbolAsInput]
  · refine ⟨true, List.append [false, false, false]
      (encodeCodeWordAsInput rest), ?_⟩
    simp [encodeCodeWordAsInput,
      encodeCodeSymbolAsInput]

private theorem cellSuffixScannerDescription_runConfig_encodeCellAppend_nil_ne_halt
    (cell : Option Bool) (baseLeft : List (Option Bool)) (n : Nat) :
    (CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
      n
      (config
        CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
        baseLeft
        ((encodeCodeWordAsInput
          (encodeCellAppend cell [])).map some))).state ≠
      CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.halt := by
  cases cell with
  | none =>
      exact
        CanonicalLayouts.DovetailLayoutScanner.primitive_runConfig_state_ne_halt_of_reaches_stuck
          CanonicalLayouts.DovetailLayoutScanner.cellSuffixScannerDescription_haltTransitionFree
          (D := CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription)
          (c :=
            config
              CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
              baseLeft
              ((encodeCodeWordAsInput
                (encodeCellAppend none [])).map some))
          (stuck :=
            CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
              4
              (config
                CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
                baseLeft
                ((encodeCodeWordAsInput
                  (encodeCellAppend none [])).map some)))
          (k := 4) (n := n)
          rfl
          (by
            simp [CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription,
              config, tapeAtCells, keepMove,
              runConfig, stepConfig,
              lookupTransition, Matches,
              transition, encodeCellAppend,
              encodeCell,
              encodeCodeWordAsInput,
              encodeCodeSymbolAsInput, Tape.read,
              Tape.write, Tape.move, Tape.moveRight])
          (by
            simp [CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription,
              config, tapeAtCells, keepMove,
              runConfig, stepConfig,
              lookupTransition, Matches,
              transition, encodeCellAppend,
              encodeCell,
              encodeCodeWordAsInput,
              encodeCodeSymbolAsInput, Tape.read,
              Tape.write, Tape.move, Tape.moveRight])
  | some b =>
      cases b
      · exact
          CanonicalLayouts.DovetailLayoutScanner.primitive_runConfig_state_ne_halt_of_reaches_stuck
            CanonicalLayouts.DovetailLayoutScanner.cellSuffixScannerDescription_haltTransitionFree
            (D := CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription)
            (c :=
              config
                CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
                baseLeft
                ((encodeCodeWordAsInput
                  (encodeCellAppend (some false) [])).map
                  some))
            (stuck :=
              CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
                4
                (config
                  CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
                  baseLeft
                  ((encodeCodeWordAsInput
                    (encodeCellAppend (some false) [])).map
                    some)))
            (k := 4) (n := n)
            rfl
            (by
              simp [CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription,
                config, tapeAtCells, keepMove,
                runConfig, stepConfig,
                lookupTransition, Matches,
                transition,
                encodeCellAppend,
                encodeCell,
                encodeCodeWordAsInput,
                encodeCodeSymbolAsInput, Tape.read,
                Tape.write, Tape.move, Tape.moveRight])
            (by
              simp [CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription,
                config, tapeAtCells, keepMove,
                runConfig, stepConfig,
                lookupTransition, Matches,
                transition,
                encodeCellAppend,
                encodeCell,
                encodeCodeWordAsInput,
                encodeCodeSymbolAsInput, Tape.read,
                Tape.write, Tape.move, Tape.moveRight])
      · exact
          CanonicalLayouts.DovetailLayoutScanner.primitive_runConfig_state_ne_halt_of_reaches_stuck
            CanonicalLayouts.DovetailLayoutScanner.cellSuffixScannerDescription_haltTransitionFree
            (D := CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription)
            (c :=
              config
                CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
                baseLeft
                ((encodeCodeWordAsInput
                  (encodeCellAppend (some true) [])).map
                  some))
            (stuck :=
              CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
                4
                (config
                  CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
                  baseLeft
                  ((encodeCodeWordAsInput
                    (encodeCellAppend (some true) [])).map
                    some)))
            (k := 4) (n := n)
            rfl
            (by
              simp [CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription,
                config, tapeAtCells, keepMove,
                runConfig, stepConfig,
                lookupTransition, Matches,
                transition,
                encodeCellAppend,
                encodeCell,
                encodeCodeWordAsInput,
                encodeCodeSymbolAsInput, Tape.read,
                Tape.write, Tape.move, Tape.moveRight])
            (by
              simp [CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription,
                config, tapeAtCells, keepMove,
                runConfig, stepConfig,
                lookupTransition, Matches,
                transition,
                encodeCellAppend,
                encodeCell,
                encodeCodeWordAsInput,
                encodeCodeSymbolAsInput, Tape.read,
                Tape.write, Tape.move, Tape.moveRight])

theorem cellSuffixScannerDescription_runConfig_encodeCellAppend_handoff
    (baseLeft : List (Option Bool)) (cell : Option Bool)
    (suffix : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
          n
          (config
            CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
            baseLeft
            ((encodeCodeWordAsInput
              (encodeCellAppend cell suffix)).map some)) =
        { state :=
            CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.halt
          tape := Tout }) :
    exists b : Bool,
    exists suffixTail : Word Bool,
      encodeCodeWordAsInput suffix = b :: suffixTail ∧
        Tout =
          (CanonicalLayouts.DovetailLayoutScanner.cellSuffixHandoffConfigWithBase
            cell baseLeft (b :: suffixTail)).tape := by
  cases suffix with
  | nil =>
      have hstate :
          (CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
            n
            (config
              CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
              baseLeft
              ((encodeCodeWordAsInput
                (encodeCellAppend cell [])).map
                some))).state =
            CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.halt := by
        simpa using congrArg Configuration.state h
      exact False.elim
        ((cellSuffixScannerDescription_runConfig_encodeCellAppend_nil_ne_halt
          cell baseLeft n) hstate)
  | cons symbol rest =>
      rcases encodeCodeWordAsInput_cons_bits symbol rest with
        ⟨b, suffixTail, hsuffix⟩
      refine ⟨b, suffixTail, hsuffix, ?_⟩
      let c0 : Configuration :=
        config
          CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.start
          baseLeft
          ((encodeCodeWordAsInput
            (encodeCellAppend cell (symbol :: rest))).map
            some)
      rcases
          CanonicalLayouts.DovetailLayoutScanner.run_cellSuffix_raw_to_handoff_withBase
            cell baseLeft b suffixTail with
        ⟨steps, hforward⟩
      have hforwardCode :
          CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription.runConfig
              steps c0 =
            CanonicalLayouts.DovetailLayoutScanner.cellSuffixHandoffConfigWithBase
              cell baseLeft (b :: suffixTail) := by
        have hbits :=
          CanonicalLayouts.DovetailLayoutScanner.cellBits_eq_encodeCellAppend
            cell (symbol :: rest)
        simpa [c0, hbits, hsuffix, List.map_append] using hforward
      exact
        (MachineDescription.runConfig_halt_tape_functional_of_haltTransitionFree
          CanonicalLayouts.DovetailLayoutScanner.cellSuffixScannerDescription_haltTransitionFree
          hforwardCode
          (by simpa [c0] using h)).symm

theorem tapeSuffixScannerDescription_runConfig_code_handoff
    (baseLeft : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      CanonicalLayouts.DovetailLayoutScanner.TapeSuffixScannerDescription.runConfig
          n
          (config
            CanonicalLayouts.DovetailLayoutScanner.TapeSuffixScannerDescription.start
            baseLeft
            ((encodeCodeWordAsInput code).map some)) =
        { state :=
            CanonicalLayouts.DovetailLayoutScanner.TapeSuffixScannerDescription.halt
          tape := Tout }) :
    exists T : Tape Bool,
    exists suffix : Word MachineCodeSymbol,
    exists baseAfter : List (Option Bool),
      code = encodeTapeAppend T suffix ∧
        Tape.move Direction.right Tout =
          tapeAtCells baseAfter
            ((encodeCodeWordAsInput suffix).map
              some) := by
  have hseq :
      (seqSubroutine
        CanonicalLayouts.DovetailLayoutScanner.CellListSuffixScannerDescription
        (seqSubroutine
          CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription
          CanonicalLayouts.DovetailLayoutScanner.CellListSuffixScannerDescription
          Direction.right)
        Direction.right).runConfig n
          { state :=
              (seqSubroutine
                CanonicalLayouts.DovetailLayoutScanner.CellListSuffixScannerDescription
                (seqSubroutine
                  CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription
                  CanonicalLayouts.DovetailLayoutScanner.CellListSuffixScannerDescription
                  Direction.right)
                Direction.right).start
            tape :=
              tapeAtCells baseLeft
                ((encodeCodeWordAsInput code).map
                  some) } =
        { state :=
            (seqSubroutine
              CanonicalLayouts.DovetailLayoutScanner.CellListSuffixScannerDescription
              (seqSubroutine
                CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription
                CanonicalLayouts.DovetailLayoutScanner.CellListSuffixScannerDescription
                Direction.right)
              Direction.right).halt
          tape := Tout } := by
    simpa [CanonicalLayouts.DovetailLayoutScanner.TapeSuffixScannerDescription,
      config] using h
  rcases
      seqSubroutine_runConfig_inv
        (A := CanonicalLayouts.DovetailLayoutScanner.CellListSuffixScannerDescription)
        (B := seqSubroutine
          CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription
          CanonicalLayouts.DovetailLayoutScanner.CellListSuffixScannerDescription
          Direction.right)
        (handoffMove := Direction.right)
        CanonicalLayouts.DovetailLayoutScanner.cellListSuffixScannerDescription_subroutineReady
        (seqSubroutine_subroutineReady
          CanonicalLayouts.DovetailLayoutScanner.cellSuffixScannerDescription_subroutineReady
          CanonicalLayouts.DovetailLayoutScanner.cellListSuffixScannerDescription_subroutineReady)
        hseq with
    ⟨Tleft, hleft, hheadRight⟩
  rcases hleft with ⟨nLeft, hleftRun, _hleftFirst⟩
  rcases
      CanonicalLayouts.DovetailLayoutScanner.cellListSuffixScannerDescription_runConfig_code_inv
        baseLeft code (by simpa [config] using hleftRun) with
    ⟨leftCells, afterLeft, hcodeLeft⟩
  rcases
      CanonicalLayouts.DovetailLayoutScanner.cellListSuffixScannerDescription_runConfig_encodeCellListAppend_suffix_false
        baseLeft leftCells afterLeft
        (by simpa [config, hcodeLeft] using hleftRun) with
    ⟨afterLeftTail, hafterLeftBits⟩
  have hleftMove :
      Tape.move Direction.right Tleft =
        tapeAtCells
          (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
            leftCells baseLeft)
          ((encodeCodeWordAsInput afterLeft).map
            some) := by
    have hleftTape :=
      CanonicalLayouts.DovetailLayoutScanner.cellListSuffixScannerDescription_runConfig_encodeCellListAppend_handoff_false
        baseLeft leftCells afterLeft afterLeftTail hafterLeftBits
        (by simpa [config, hcodeLeft] using hleftRun)
    rw [hleftTape]
    simpa [hafterLeftBits] using
      CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalHandoffConfigWithBase_move_right_all
        leftCells baseLeft (false :: afterLeftTail)
  rcases hheadRight with ⟨nHeadRight, hheadRightRun⟩
  have hheadRightCode :
      (seqSubroutine
          CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription
          CanonicalLayouts.DovetailLayoutScanner.CellListSuffixScannerDescription
          Direction.right).runConfig nHeadRight
        (config
          (seqSubroutine
            CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription
            CanonicalLayouts.DovetailLayoutScanner.CellListSuffixScannerDescription
            Direction.right).start
          (CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
            leftCells baseLeft)
          ((encodeCodeWordAsInput afterLeft).map
            some)) =
        { state :=
            (seqSubroutine
              CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription
              CanonicalLayouts.DovetailLayoutScanner.CellListSuffixScannerDescription
              Direction.right).halt
          tape := Tout } := by
    simpa [config, hleftMove] using hheadRightRun
  rcases
      seqSubroutine_runConfig_inv
        (A := CanonicalLayouts.DovetailLayoutScanner.CellSuffixScannerDescription)
        (B := CanonicalLayouts.DovetailLayoutScanner.CellListSuffixScannerDescription)
        (handoffMove := Direction.right)
        CanonicalLayouts.DovetailLayoutScanner.cellSuffixScannerDescription_subroutineReady
        CanonicalLayouts.DovetailLayoutScanner.cellListSuffixScannerDescription_subroutineReady
        hheadRightCode with
    ⟨Thead, hhead, hright⟩
  rcases hhead with ⟨nHead, hheadRun, _hheadFirst⟩
  let baseAfterLeft :=
    CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
      leftCells baseLeft
  rcases
      cellSuffixScannerDescription_runConfig_code_inv
        baseAfterLeft afterLeft (by simpa [baseAfterLeft, config] using hheadRun) with
    ⟨headCell, afterHead, hafterLeft⟩
  rcases
      cellSuffixScannerDescription_runConfig_encodeCellAppend_handoff
        baseAfterLeft headCell afterHead
        (by simpa [baseAfterLeft, config, hafterLeft] using hheadRun) with
    ⟨headSuffixBit, headSuffixTail, hafterHeadBits, hheadTape⟩
  have hheadMove :
      Tape.move Direction.right Thead =
        tapeAtCells
          (List.append
            ((CanonicalLayouts.DovetailLayoutScanner.cellCodeBits headCell).reverse.map
              some)
            baseAfterLeft)
          ((encodeCodeWordAsInput afterHead).map
            some) := by
    rw [hheadTape]
    simpa [hafterHeadBits] using
      CanonicalLayouts.DovetailLayoutScanner.cellSuffixHandoffConfigWithBase_move_right
        headCell baseAfterLeft headSuffixBit headSuffixTail
  rcases hright with ⟨nRight, hrightRun⟩
  let baseAfterHead :=
    List.append
      ((CanonicalLayouts.DovetailLayoutScanner.cellCodeBits headCell).reverse.map
        some)
      baseAfterLeft
  have hrightCodeRun :
      CanonicalLayouts.DovetailLayoutScanner.CellListSuffixScannerDescription.runConfig
          nRight
          (config
            CanonicalLayouts.DovetailLayoutScanner.CellListSuffixScannerDescription.start
            baseAfterHead
            ((encodeCodeWordAsInput afterHead).map
              some)) =
        { state :=
            CanonicalLayouts.DovetailLayoutScanner.CellListSuffixScannerDescription.halt
          tape := Tout } := by
    simpa [baseAfterHead, config, hheadMove] using hrightRun
  rcases
      CanonicalLayouts.DovetailLayoutScanner.cellListSuffixScannerDescription_runConfig_code_inv
        baseAfterHead afterHead hrightCodeRun with
    ⟨rightCells, suffix, hafterHead⟩
  rcases
      CanonicalLayouts.DovetailLayoutScanner.cellListSuffixScannerDescription_runConfig_encodeCellListAppend_suffix_false
        baseAfterHead rightCells suffix
        (by simpa [hafterHead] using hrightCodeRun) with
    ⟨suffixTail, hsuffixBits⟩
  have hrightTape :=
    CanonicalLayouts.DovetailLayoutScanner.cellListSuffixScannerDescription_runConfig_encodeCellListAppend_handoff_false
      baseAfterHead rightCells suffix suffixTail hsuffixBits
      (by simpa [hafterHead] using hrightCodeRun)
  let T : Tape Bool :=
    { left := leftCells, head := headCell, right := rightCells }
  refine
    ⟨T, suffix,
      CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalRestoredLeftWithBase
        rightCells baseAfterHead,
      ?_, ?_⟩
  · simp [T, encodeTapeAppend, hcodeLeft,
      hafterLeft, hafterHead]
  · rw [hrightTape]
    simpa [hsuffixBits] using
      CanonicalLayouts.DovetailLayoutScanner.cellListCanonicalHandoffConfigWithBase_move_right_all
        rightCells baseAfterHead (false :: suffixTail)

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
