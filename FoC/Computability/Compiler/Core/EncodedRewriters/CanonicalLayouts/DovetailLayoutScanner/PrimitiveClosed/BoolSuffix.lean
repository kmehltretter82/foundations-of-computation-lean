import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.PrimitiveClosed.Basic

set_option doc.verso true

/-!
# Primitive closed bool-suffix scanner facts

Late closed-direction facts for the primitive dovetail-layout scanners.
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

private theorem encodeCodeWordAsInput_map_some_cons_inv
    {suffix : Word MachineCodeSymbol} {b : Bool}
    {suffixCellsTail : List (Option Bool)}
    (h :
      (MachineDescription.encodeCodeWordAsInput suffix).map some =
        some b :: suffixCellsTail) :
    exists suffixTail : Word Bool,
      MachineDescription.encodeCodeWordAsInput suffix = b :: suffixTail ∧
        suffixCellsTail = suffixTail.map some := by
  cases hbits : MachineDescription.encodeCodeWordAsInput suffix with
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
    (h : (MachineDescription.encodeCodeWordAsInput code).map some = []) :
    code = [] := by
  cases code with
  | nil =>
      rfl
  | cons symbol rest =>
      cases symbol <;>
        simp [MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput] at h

private theorem encodeCodeWordAsInput_map_some_ne_none_cons
    (code : Word MachineCodeSymbol) (rest : List (Option Bool)) :
    (MachineDescription.encodeCodeWordAsInput code).map some ≠
      none :: rest := by
  intro h
  cases code with
  | nil =>
      simp [MachineDescription.encodeCodeWordAsInput] at h
  | cons symbol suffix =>
      cases symbol <;>
        simp [MachineDescription.encodeCodeWordAsInput,
          MachineDescription.encodeCodeSymbolAsInput] at h

theorem boolSuffixScannerDescription_runConfig_encodeBoolAppend_handoff
    (baseLeft : List (Option Bool)) (flag : Bool)
    (suffix : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      BoolSuffixScannerDescription.runConfig n
          (config BoolSuffixScannerDescription.start baseLeft
            ((MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolAppend flag suffix)).map
              some)) =
        { state := BoolSuffixScannerDescription.halt
          tape := Tout }) :
    exists b : Bool,
    exists suffixTail : Word Bool,
    exists baseAfter : List (Option Bool),
      MachineDescription.encodeCodeWordAsInput suffix = b :: suffixTail ∧
        Tape.move Direction.right Tout =
          tapeAtCells baseAfter
            ((MachineDescription.encodeCodeWordAsInput suffix).map some) := by
  have hraw :
      BoolSuffixScannerDescription.runConfig n
          { state := BoolSuffixScannerDescription.start
            tape := tapeAtCells baseLeft
              (List.append ((cellCodeBits (some flag)).map some)
                ((MachineDescription.encodeCodeWordAsInput suffix).map
                  some)) } =
        { state := BoolSuffixScannerDescription.halt
          tape := Tout } := by
    simpa [config, boolBits_eq_encodeBoolAppend, List.map_append] using h
  rcases
      boolSuffixScannerDescription_runConfig_suffix_inv
        flag baseLeft
        ((MachineDescription.encodeCodeWordAsInput suffix).map some)
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

theorem boolFinalScannerDescription_runConfig_encodeBoolAppend_terminal_inv
    (baseLeft : List (Option Bool)) (flag : Bool)
    (suffix : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      BoolFinalScannerDescription.runConfig n
          (config BoolFinalScannerDescription.start baseLeft
            ((MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolAppend flag suffix)).map
              some)) =
        { state := BoolFinalScannerDescription.halt
          tape := Tout }) :
    suffix = [] ∧
      Tape.move Direction.right Tout =
        tapeAtCells
          (List.append ((cellCodeBits (some flag)).reverse.map some)
            baseLeft)
          [] := by
  have hraw :
      BoolFinalScannerDescription.runConfig n
          { state := BoolFinalScannerDescription.start
            tape := tapeAtCells baseLeft
              (List.append ((cellCodeBits (some flag)).map some)
                ((MachineDescription.encodeCodeWordAsInput suffix).map
                  some)) } =
        { state := BoolFinalScannerDescription.halt
          tape := Tout } := by
    simpa [config, boolBits_eq_encodeBoolAppend, List.map_append] using h
  rcases
      boolFinalScannerDescription_runConfig_terminal_inv
        flag baseLeft
        ((MachineDescription.encodeCodeWordAsInput suffix).map some)
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
      MachineDescription.encodeCodeWordAsInput] using
      boolFinalHandoffConfigWithBase_move_right flag baseLeft

theorem finalHitFlagsScannerDescription_runConfig_encodeBoolAppend_terminal_inv
    (baseLeft : List (Option Bool))
    (acceptHit rejectHit : Bool)
    (suffix : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      FinalHitFlagsScannerDescription.runConfig n
          (config FinalHitFlagsScannerDescription.start baseLeft
            ((MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolAppend acceptHit
                (MachineDescription.encodeBoolAppend rejectHit
                  suffix))).map some)) =
        { state := FinalHitFlagsScannerDescription.halt
          tape := Tout }) :
    suffix = [] ∧
      exists baseAfter : List (Option Bool),
        Tape.move Direction.right Tout = tapeAtCells baseAfter [] := by
  have hseq :
      (MachineDescription.seqSubroutine
        BoolSuffixScannerDescription
        BoolFinalScannerDescription
        Direction.right).runConfig n
          (config
            (MachineDescription.seqSubroutine
              BoolSuffixScannerDescription
              BoolFinalScannerDescription
              Direction.right).start
            baseLeft
            ((MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolAppend acceptHit
                (MachineDescription.encodeBoolAppend rejectHit
                  suffix))).map some)) =
        { state :=
            (MachineDescription.seqSubroutine
              BoolSuffixScannerDescription
              BoolFinalScannerDescription
              Direction.right).halt
          tape := Tout } := by
    simpa [FinalHitFlagsScannerDescription, config] using h
  rcases
      MachineDescription.seqSubroutine_runConfig_inv
        (A := BoolSuffixScannerDescription)
        (B := BoolFinalScannerDescription)
        (handoffMove := Direction.right)
        boolSuffixScannerDescription_subroutineReady
        boolFinalScannerDescription_subroutineReady
        hseq with
    ⟨TacceptHit, hacceptHit, hrejectHit⟩
  rcases hacceptHit with ⟨nAcceptHit, hacceptHitRun, _hacceptHitFirst⟩
  rcases
      boolSuffixScannerDescription_runConfig_encodeBoolAppend_handoff
        baseLeft acceptHit
        (MachineDescription.encodeBoolAppend rejectHit suffix)
        (by simpa [config] using hacceptHitRun) with
    ⟨_rejectFirstBit, _rejectSuffixTail, baseAfterAcceptHit,
      _hrejectBits, hacceptHitMove⟩
  rcases hrejectHit with ⟨nRejectHit, hrejectHitRun⟩
  have hrejectHitCodeRun :
      BoolFinalScannerDescription.runConfig nRejectHit
          (config BoolFinalScannerDescription.start baseAfterAcceptHit
            ((MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolAppend rejectHit suffix)).map
              some)) =
        { state := BoolFinalScannerDescription.halt
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

theorem runConfig_forward_inv
    (D : MachineDescription) (c0 c1 : MachineDescription.Configuration)
    (n k : Nat) {Tout : Tape Bool}
    (h_halt : D.runConfig n c0 = { state := D.halt, tape := Tout })
    (h_forward : D.runConfig k c0 = c1)
    (h_free : D.HaltTransitionFree) :
    exists m, m ≤ n ∧ D.runConfig m c1 = { state := D.halt, tape := Tout } := by
  by_cases h_le : k ≤ n
  · exists n - k
    constructor
    · omega
    · have h_add : n = k + (n - k) := by omega
      rw [h_add, MachineDescription.runConfig_add] at h_halt
      rw [h_forward] at h_halt
      exact h_halt
  · exists 0
    constructor
    · omega
    · have h_add : k = n + (k - n) := by omega
      rw [h_add, MachineDescription.runConfig_add] at h_forward
      rw [h_halt] at h_forward
      have h_halt2 := MachineDescription.runConfig_halt h_free Tout (k - n)
      rw [h_halt2] at h_forward
      rw [← h_forward]
      rfl

theorem runConfig_halt_extend
    (D : MachineDescription) (c : MachineDescription.Configuration)
    (m n : Nat) {Tout : Tape Bool}
    (h_free : D.HaltTransitionFree)
    (hmn : m ≤ n)
    (h_halt : D.runConfig m c = { state := D.halt, tape := Tout }) :
    D.runConfig n c = { state := D.halt, tape := Tout } := by
  let rem := n - m
  have hn : n = m + rem := by
    omega
  rw [hn, MachineDescription.runConfig_add, h_halt]
  exact MachineDescription.runConfig_halt h_free Tout rem

theorem run_boolWordSuffix_state130_markedCell
    (cell : Option Bool) (left right : List (Option Bool)) :
    BoolWordSuffixScannerDescription.runConfig 4
        (config 130 left
          (List.append ((markedCellCodeBits cell).map some) right)) =
      config 130
        (List.append ((markedCellCodeBits cell).reverse.map some) left)
        right := by
  cases cell with
  | none =>
      cases right <;>
        simp [BoolWordSuffixScannerDescription, markedCellCodeBits,
          config, tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition,
          Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | some bit =>
      simpa using run_boolWordSuffix_state130_markedBit bit left right

theorem runConfig_forward_inv_lt
    (D : MachineDescription) (c0 c1 : MachineDescription.Configuration)
    (n k : Nat) {Tout : Tape Bool}
    (h_halt : D.runConfig n c0 = { state := D.halt, tape := Tout })
    (h_forward : D.runConfig k c0 = c1)
    (h_free : D.HaltTransitionFree)
    (hc1 : c1.state ≠ D.halt) (hk : 0 < k) :
    exists m, m < n ∧
      D.runConfig m c1 = { state := D.halt, tape := Tout } := by
  rcases MachineDescription.firstReaches_halt_of_runConfig_eq
      h_free h_halt with
    ⟨first, hfirst_le, hfirst, _hminimal⟩
  have hk_le_first : k ≤ first := by
    by_cases hle : k ≤ first
    · exact hle
    · have hlt : first < k := Nat.lt_of_not_ge hle
      let rem := k - first
      have hk_eq : k = first + rem := by
        omega
      have hhalt_at_k :
          D.runConfig k c0 = { state := D.halt, tape := Tout } := by
        rw [hk_eq, MachineDescription.runConfig_add, hfirst]
        exact MachineDescription.runConfig_halt h_free Tout rem
      have hstate : c1.state = D.halt := by
        have hc1eq :
            c1 = { state := D.halt, tape := Tout } :=
          h_forward.symm.trans hhalt_at_k
        simp [hc1eq]
      exact False.elim (hc1 hstate)
  refine ⟨first - k, ?_, ?_⟩
  · omega
  · have hfirst_eq : first = k + (first - k) := by
      omega
    rw [hfirst_eq, MachineDescription.runConfig_add] at hfirst
    rw [h_forward] at hfirst
    exact hfirst

theorem boolWordSuffixScannerDescription_runConfig_120_nat_prefix_inv
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (h : BoolWordSuffixScannerDescription.runConfig n (config 120 baseLeft (bits.map some)) = { state := BoolWordSuffixScannerDescription.halt, tape := Tout }) :
    exists doneBit tail, bits = false :: false :: true :: doneBit :: tail := by
  let c0 : MachineDescription.Configuration :=
    config 120 baseLeft (bits.map some)
  have hhaltState :
      (BoolWordSuffixScannerDescription.runConfig n c0).state =
        BoolWordSuffixScannerDescription.halt := by
    simpa [c0] using congrArg MachineDescription.Configuration.state h
  cases bits with
  | nil =>
      let stuck : MachineDescription.Configuration := c0
      have hstep :
          BoolWordSuffixScannerDescription.stepConfig stuck = none := by
        simp [stuck, c0, BoolWordSuffixScannerDescription, config,
          tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read]
      have hstuck :
          stuck.state ≠ BoolWordSuffixScannerDescription.halt := by
        simp [stuck, c0, BoolWordSuffixScannerDescription, config]
      exact False.elim
        (primitive_runConfig_state_ne_halt_of_reaches_stuck
          boolWordSuffixScannerDescription_haltTransitionFree
          (D := BoolWordSuffixScannerDescription)
          (c := c0) (stuck := stuck) (k := 0) (n := n)
          rfl hstep hstuck hhaltState)
  | cons first rest =>
      cases first
      · cases rest with
        | nil =>
            let stuck :=
              BoolWordSuffixScannerDescription.runConfig 1 c0
            have hstep :
                BoolWordSuffixScannerDescription.stepConfig stuck = none := by
              simp [stuck, c0, BoolWordSuffixScannerDescription, config,
                tapeAtCells, keep, keepMove, writeMove,
                scanLeftToSentinelRestart, MachineDescription.runConfig,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches,
                MachineDescription.transition, Tape.read, Tape.write,
                Tape.move, Tape.moveRight]
            have hstuck :
                stuck.state ≠ BoolWordSuffixScannerDescription.halt := by
              simp [stuck, c0, BoolWordSuffixScannerDescription, config,
                tapeAtCells, keep, keepMove, writeMove,
                scanLeftToSentinelRestart, MachineDescription.runConfig,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches,
                MachineDescription.transition, Tape.read, Tape.write,
                Tape.move, Tape.moveRight]
            exact False.elim
              (primitive_runConfig_state_ne_halt_of_reaches_stuck
                boolWordSuffixScannerDescription_haltTransitionFree
                (D := BoolWordSuffixScannerDescription)
                (c := c0) (stuck := stuck) (k := 1) (n := n)
                rfl hstep hstuck hhaltState)
        | cons second restTail =>
            cases second
            · cases restTail with
              | nil =>
                  let stuck :=
                    BoolWordSuffixScannerDescription.runConfig 2 c0
                  have hstep :
                      BoolWordSuffixScannerDescription.stepConfig stuck =
                        none := by
                    simp [stuck, c0, BoolWordSuffixScannerDescription,
                      config, tapeAtCells, keep, keepMove, writeMove,
                      scanLeftToSentinelRestart,
                      MachineDescription.runConfig,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches,
                      MachineDescription.transition, Tape.read, Tape.write,
                      Tape.move, Tape.moveRight]
                  have hstuck :
                      stuck.state ≠
                        BoolWordSuffixScannerDescription.halt := by
                    simp [stuck, c0, BoolWordSuffixScannerDescription,
                      config, tapeAtCells, keep, keepMove, writeMove,
                      scanLeftToSentinelRestart,
                      MachineDescription.runConfig,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches,
                      MachineDescription.transition, Tape.read, Tape.write,
                      Tape.move, Tape.moveRight]
                  exact False.elim
                    (primitive_runConfig_state_ne_halt_of_reaches_stuck
                      boolWordSuffixScannerDescription_haltTransitionFree
                      (D := BoolWordSuffixScannerDescription)
                      (c := c0) (stuck := stuck) (k := 2) (n := n)
                      rfl hstep hstuck hhaltState)
              | cons third tail =>
                  cases third
                  · let stuck :=
                        BoolWordSuffixScannerDescription.runConfig 2 c0
                    have hstep :
                        BoolWordSuffixScannerDescription.stepConfig stuck =
                          none := by
                      cases tail <;>
                        simp [stuck, c0,
                          BoolWordSuffixScannerDescription, config,
                          tapeAtCells, keep, keepMove, writeMove,
                          scanLeftToSentinelRestart,
                          MachineDescription.runConfig,
                          MachineDescription.stepConfig,
                          MachineDescription.lookupTransition,
                          MachineDescription.Matches,
                          MachineDescription.transition, Tape.read,
                          Tape.write, Tape.move, Tape.moveRight]
                    have hstuck :
                        stuck.state ≠
                          BoolWordSuffixScannerDescription.halt := by
                      cases tail <;>
                        simp [stuck, c0,
                          BoolWordSuffixScannerDescription, config,
                          tapeAtCells, keep, keepMove, writeMove,
                          scanLeftToSentinelRestart,
                          MachineDescription.runConfig,
                          MachineDescription.stepConfig,
                          MachineDescription.lookupTransition,
                          MachineDescription.Matches,
                          MachineDescription.transition, Tape.read,
                          Tape.write, Tape.move, Tape.moveRight]
                    exact False.elim
                      (primitive_runConfig_state_ne_halt_of_reaches_stuck
                        boolWordSuffixScannerDescription_haltTransitionFree
                        (D := BoolWordSuffixScannerDescription)
                        (c := c0) (stuck := stuck) (k := 2) (n := n)
                        rfl hstep hstuck hhaltState)
                  · cases tail with
                    | nil =>
                        let stuck :=
                          BoolWordSuffixScannerDescription.runConfig 4 c0
                        have hstep :
                            BoolWordSuffixScannerDescription.stepConfig
                                stuck = none := by
                          simp [stuck, c0,
                            BoolWordSuffixScannerDescription, config,
                            tapeAtCells, keep, keepMove, writeMove,
                            scanLeftToSentinelRestart,
                            MachineDescription.runConfig,
                            MachineDescription.stepConfig,
                            MachineDescription.lookupTransition,
                            MachineDescription.Matches,
                            MachineDescription.transition, Tape.read,
                            Tape.write, Tape.move, Tape.moveRight]
                        have hstuck :
                            stuck.state ≠
                              BoolWordSuffixScannerDescription.halt := by
                          simp [stuck, c0,
                            BoolWordSuffixScannerDescription, config,
                            tapeAtCells, keep, keepMove, writeMove,
                            scanLeftToSentinelRestart,
                            MachineDescription.runConfig,
                            MachineDescription.stepConfig,
                            MachineDescription.lookupTransition,
                            MachineDescription.Matches,
                            MachineDescription.transition, Tape.read,
                            Tape.write, Tape.move, Tape.moveRight]
                        exact False.elim
                          (primitive_runConfig_state_ne_halt_of_reaches_stuck
                            boolWordSuffixScannerDescription_haltTransitionFree
                            (D := BoolWordSuffixScannerDescription)
                            (c := c0) (stuck := stuck) (k := 4)
                            (n := n) rfl hstep hstuck hhaltState)
                    | cons doneBit tailRest =>
                        exact ⟨doneBit, tailRest, rfl⟩
            · let stuck :=
                BoolWordSuffixScannerDescription.runConfig 1 c0
              have hstep :
                  BoolWordSuffixScannerDescription.stepConfig stuck = none := by
                cases restTail <;>
                  simp [stuck, c0, BoolWordSuffixScannerDescription, config,
                    tapeAtCells, keep, keepMove, writeMove,
                    scanLeftToSentinelRestart,
                    MachineDescription.runConfig,
                    MachineDescription.stepConfig,
                    MachineDescription.lookupTransition,
                    MachineDescription.Matches,
                    MachineDescription.transition, Tape.read, Tape.write,
                    Tape.move, Tape.moveRight]
              have hstuck :
                  stuck.state ≠ BoolWordSuffixScannerDescription.halt := by
                cases restTail <;>
                  simp [stuck, c0, BoolWordSuffixScannerDescription, config,
                    tapeAtCells, keep, keepMove, writeMove,
                    scanLeftToSentinelRestart,
                    MachineDescription.runConfig,
                    MachineDescription.stepConfig,
                    MachineDescription.lookupTransition,
                    MachineDescription.Matches,
                    MachineDescription.transition, Tape.read, Tape.write,
                    Tape.move, Tape.moveRight]
              exact False.elim
                (primitive_runConfig_state_ne_halt_of_reaches_stuck
                  boolWordSuffixScannerDescription_haltTransitionFree
                  (D := BoolWordSuffixScannerDescription)
                  (c := c0) (stuck := stuck) (k := 1) (n := n)
                  rfl hstep hstuck hhaltState)
      · -- first bit is true: state 120 has no transition for true → stuck at step 0
        let stuck : MachineDescription.Configuration := c0
        have hstep :
            BoolWordSuffixScannerDescription.stepConfig stuck = none := by
          cases rest <;>
            simp [stuck, c0, BoolWordSuffixScannerDescription, config,
              tapeAtCells, keep, keepMove, writeMove,
              scanLeftToSentinelRestart, MachineDescription.stepConfig,
              MachineDescription.lookupTransition,
              MachineDescription.Matches,
              MachineDescription.transition, Tape.read]
        have hstuck :
            stuck.state ≠ BoolWordSuffixScannerDescription.halt := by
          simp [stuck, c0, BoolWordSuffixScannerDescription, config]
        exact False.elim
          (primitive_runConfig_state_ne_halt_of_reaches_stuck
            boolWordSuffixScannerDescription_haltTransitionFree
            (D := BoolWordSuffixScannerDescription)
            (c := c0) (stuck := stuck) (k := 0) (n := n)
            rfl hstep hstuck hhaltState)

theorem boolWordSuffixScannerDescription_runConfig_120_inv
    (n : Nat) (baseLeft : List (Option Bool)) (tail : Word Bool)
    {Tout : Tape Bool}
    (h : BoolWordSuffixScannerDescription.runConfig n (config 120 baseLeft (tail.map some)) = { state := BoolWordSuffixScannerDescription.halt, tape := Tout }) :
    exists stage : Nat, exists tail' : Word Bool, tail = List.append (stageNatBits stage) tail' ∧
      BoolWordSuffixScannerDescription.runConfig n (config 130 (List.append ((stageNatBits stage).reverse.map some) baseLeft) (tail'.map some)) = { state := BoolWordSuffixScannerDescription.halt, tape := Tout } := by
  revert baseLeft tail Tout
  exact
    Nat.strongRecOn
      (motive := fun n =>
        forall baseLeft : List (Option Bool),
        forall tail : Word Bool,
        forall {Tout : Tape Bool},
          BoolWordSuffixScannerDescription.runConfig n
              (config 120 baseLeft (tail.map some)) =
            { state := BoolWordSuffixScannerDescription.halt
              tape := Tout } ->
            exists stage : Nat, exists tail' : Word Bool,
              tail = List.append (stageNatBits stage) tail' ∧
                BoolWordSuffixScannerDescription.runConfig n
                  (config 130
                    (List.append ((stageNatBits stage).reverse.map some)
                      baseLeft)
                    (tail'.map some)) =
                  { state := BoolWordSuffixScannerDescription.halt
                    tape := Tout })
      n
      (fun n ih => by
        intro baseLeft tail Tout h
        rcases
            boolWordSuffixScannerDescription_runConfig_120_nat_prefix_inv
              baseLeft tail h with
          ⟨doneBit, tailRest, htail⟩
        let c0 : MachineDescription.Configuration :=
          config 120 baseLeft (tail.map some)
        cases doneBit
        · let c1 : MachineDescription.Configuration :=
            config 120
              (List.append (tickBits.reverse.map some) baseLeft)
              (tailRest.map some)
          have hprefix : BoolWordSuffixScannerDescription.runConfig 4 c0 = c1 := by
            dsimp [c0, c1]
            rw [htail]
            simpa [c0, c1, tickBits,
              MachineDescription.encodeCodeSymbolAsInput] using
              run_boolWordSuffix_state120_tick baseLeft
                (tailRest.map some)
          have hc1 :
              c1.state ≠ BoolWordSuffixScannerDescription.halt := by
            simp [c1, config, BoolWordSuffixScannerDescription]
          rcases
              runConfig_forward_inv_lt BoolWordSuffixScannerDescription
                c0 c1 n 4 h hprefix
                boolWordSuffixScannerDescription_haltTransitionFree
                hc1 (by omega) with
            ⟨m, hm_lt, hm_halt⟩
          rcases ih m hm_lt
              (List.append (tickBits.reverse.map some) baseLeft)
              tailRest hm_halt with
            ⟨stage, tail', hstage, hrun⟩
          exists stage + 1, tail'
          constructor
          · rw [htail, hstage]
            simp [stageNatBits_succ]
          · have hrun_n :
                BoolWordSuffixScannerDescription.runConfig n
                    (config 130
                      (List.append ((stageNatBits stage).reverse.map some)
                        (List.append (tickBits.reverse.map some) baseLeft))
                      (tail'.map some)) =
                  { state := BoolWordSuffixScannerDescription.halt
                    tape := Tout } :=
              runConfig_halt_extend BoolWordSuffixScannerDescription
                (config 130
                  (List.append ((stageNatBits stage).reverse.map some)
                    (List.append (tickBits.reverse.map some) baseLeft))
                  (tail'.map some))
                m n
                boolWordSuffixScannerDescription_haltTransitionFree
                (by omega) hrun
            simpa [stageNatBits_succ, tickBits,
              MachineDescription.encodeCodeSymbolAsInput, List.reverse_append,
              List.map_append, List.append_assoc] using hrun_n
        · let c1 : MachineDescription.Configuration :=
            config 130
              (List.append (doneBits.reverse.map some) baseLeft)
              (tailRest.map some)
          have hprefix : BoolWordSuffixScannerDescription.runConfig 4 c0 = c1 := by
            dsimp [c0, c1]
            rw [htail]
            simpa [c0, c1, doneBits,
              MachineDescription.encodeCodeSymbolAsInput] using
              run_boolWordSuffix_state120_done baseLeft
                (tailRest.map some)
          rcases
              runConfig_forward_inv BoolWordSuffixScannerDescription
                c0 c1 n 4 h hprefix
                boolWordSuffixScannerDescription_haltTransitionFree with
            ⟨m, hm_le, hm_halt⟩
          exists 0, tailRest
          constructor
          · rw [htail]
            simp [stageNatBits_zero]
          · have hrun_n :
                BoolWordSuffixScannerDescription.runConfig n c1 =
                  { state := BoolWordSuffixScannerDescription.halt
                    tape := Tout } :=
              runConfig_halt_extend BoolWordSuffixScannerDescription c1 m n
                boolWordSuffixScannerDescription_haltTransitionFree
                hm_le hm_halt
            simpa [c1, stageNatBits_zero, doneBits,
              MachineDescription.encodeCodeSymbolAsInput] using hrun_n)

theorem boolWordSuffixScannerDescription_runConfig_130_marked_prefix_inv
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (h : BoolWordSuffixScannerDescription.runConfig n (config 130 baseLeft (bits.map some)) = { state := BoolWordSuffixScannerDescription.halt, tape := Tout }) :
    (exists tail, bits = false :: tail) ∨
    (exists cell tailRest, bits = List.append (markedCellCodeBits cell) tailRest) := by
  let c0 : MachineDescription.Configuration :=
    config 130 baseLeft (bits.map some)
  have hhaltState :
      (BoolWordSuffixScannerDescription.runConfig n c0).state =
        BoolWordSuffixScannerDescription.halt := by
    simpa [c0] using
      congrArg MachineDescription.Configuration.state h
  cases bits with
  | nil =>
      let stuck : MachineDescription.Configuration := c0
      have hstep :
          BoolWordSuffixScannerDescription.stepConfig stuck = none := by
        simp [stuck, c0, BoolWordSuffixScannerDescription, config,
          tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart, MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          MachineDescription.transition, Tape.read]
      have hstuck :
          stuck.state ≠ BoolWordSuffixScannerDescription.halt := by
        simp [stuck, c0, config, BoolWordSuffixScannerDescription]
      exact False.elim
        (primitive_runConfig_state_ne_halt_of_reaches_stuck
          boolWordSuffixScannerDescription_haltTransitionFree
          (D := BoolWordSuffixScannerDescription)
          (c := c0) (stuck := stuck) (k := 0) (n := n)
          rfl hstep hstuck hhaltState)
  | cons first rest =>
      cases first
      · exact Or.inl ⟨rest, rfl⟩
      · cases rest with
        | nil =>
            let stuck :=
              BoolWordSuffixScannerDescription.runConfig 1 c0
            have hstep :
                BoolWordSuffixScannerDescription.stepConfig stuck = none := by
              simp [stuck, c0, BoolWordSuffixScannerDescription, config,
                tapeAtCells, keep, keepMove, writeMove,
                scanLeftToSentinelRestart, MachineDescription.runConfig,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches,
                MachineDescription.transition, Tape.read, Tape.write,
                Tape.move, Tape.moveRight]
            have hstuck :
                stuck.state ≠ BoolWordSuffixScannerDescription.halt := by
              simp [stuck, c0, BoolWordSuffixScannerDescription, config,
                tapeAtCells, keep, keepMove, writeMove,
                scanLeftToSentinelRestart, MachineDescription.runConfig,
                MachineDescription.stepConfig,
                MachineDescription.lookupTransition,
                MachineDescription.Matches,
                MachineDescription.transition, Tape.read, Tape.write,
                Tape.move, Tape.moveRight]
            exact False.elim
              (primitive_runConfig_state_ne_halt_of_reaches_stuck
                boolWordSuffixScannerDescription_haltTransitionFree
                (D := BoolWordSuffixScannerDescription)
                (c := c0) (stuck := stuck) (k := 1) (n := n)
                rfl hstep hstuck hhaltState)
        | cons second restTail =>
            cases second
            · let stuck :=
                BoolWordSuffixScannerDescription.runConfig 1 c0
              have hstep :
                  BoolWordSuffixScannerDescription.stepConfig stuck = none := by
                cases restTail <;>
                  simp [stuck, c0, BoolWordSuffixScannerDescription, config,
                    tapeAtCells, keep, keepMove, writeMove,
                    scanLeftToSentinelRestart,
                    MachineDescription.runConfig,
                    MachineDescription.stepConfig,
                    MachineDescription.lookupTransition,
                    MachineDescription.Matches,
                    MachineDescription.transition, Tape.read, Tape.write,
                    Tape.move, Tape.moveRight]
              have hstuck :
                  stuck.state ≠ BoolWordSuffixScannerDescription.halt := by
                cases restTail <;>
                  simp [stuck, c0, BoolWordSuffixScannerDescription, config,
                    tapeAtCells, keep, keepMove, writeMove,
                    scanLeftToSentinelRestart,
                    MachineDescription.runConfig,
                    MachineDescription.stepConfig,
                    MachineDescription.lookupTransition,
                    MachineDescription.Matches,
                    MachineDescription.transition, Tape.read, Tape.write,
                    Tape.move, Tape.moveRight]
              exact False.elim
                (primitive_runConfig_state_ne_halt_of_reaches_stuck
                  boolWordSuffixScannerDescription_haltTransitionFree
                  (D := BoolWordSuffixScannerDescription)
                  (c := c0) (stuck := stuck) (k := 1) (n := n)
                  rfl hstep hstuck hhaltState)
            · cases restTail with
              | nil =>
                  let stuck :=
                    BoolWordSuffixScannerDescription.runConfig 2 c0
                  have hstep :
                      BoolWordSuffixScannerDescription.stepConfig stuck =
                        none := by
                    simp [stuck, c0, BoolWordSuffixScannerDescription,
                      config, tapeAtCells, keep, keepMove, writeMove,
                      scanLeftToSentinelRestart,
                      MachineDescription.runConfig,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches,
                      MachineDescription.transition, Tape.read, Tape.write,
                      Tape.move, Tape.moveRight]
                  have hstuck :
                      stuck.state ≠ BoolWordSuffixScannerDescription.halt := by
                    simp [stuck, c0, BoolWordSuffixScannerDescription,
                      config, tapeAtCells, keep, keepMove, writeMove,
                      scanLeftToSentinelRestart,
                      MachineDescription.runConfig,
                      MachineDescription.stepConfig,
                      MachineDescription.lookupTransition,
                      MachineDescription.Matches,
                      MachineDescription.transition, Tape.read, Tape.write,
                      Tape.move, Tape.moveRight]
                  exact False.elim
                    (primitive_runConfig_state_ne_halt_of_reaches_stuck
                      boolWordSuffixScannerDescription_haltTransitionFree
                      (D := BoolWordSuffixScannerDescription)
                      (c := c0) (stuck := stuck) (k := 2) (n := n)
                      rfl hstep hstuck hhaltState)
              | cons third restAfterThird =>
                  cases restAfterThird with
                  | nil =>
                      let stuck :=
                        BoolWordSuffixScannerDescription.runConfig 3 c0
                      have hstep :
                          BoolWordSuffixScannerDescription.stepConfig
                              stuck = none := by
                        cases third <;>
                          simp [stuck, c0,
                            BoolWordSuffixScannerDescription, config,
                            tapeAtCells, keep, keepMove, writeMove,
                            scanLeftToSentinelRestart,
                            MachineDescription.runConfig,
                            MachineDescription.stepConfig,
                            MachineDescription.lookupTransition,
                            MachineDescription.Matches,
                            MachineDescription.transition, Tape.read,
                            Tape.write, Tape.move, Tape.moveRight]
                      have hstuck :
                          stuck.state ≠
                            BoolWordSuffixScannerDescription.halt := by
                        cases third <;>
                          simp [stuck, c0,
                            BoolWordSuffixScannerDescription, config,
                            tapeAtCells, keep, keepMove, writeMove,
                            scanLeftToSentinelRestart,
                            MachineDescription.runConfig,
                            MachineDescription.stepConfig,
                            MachineDescription.lookupTransition,
                            MachineDescription.Matches,
                            MachineDescription.transition, Tape.read,
                            Tape.write, Tape.move, Tape.moveRight]
                      exact False.elim
                        (primitive_runConfig_state_ne_halt_of_reaches_stuck
                          boolWordSuffixScannerDescription_haltTransitionFree
                          (D := BoolWordSuffixScannerDescription)
                          (c := c0) (stuck := stuck) (k := 3) (n := n)
                          rfl hstep hstuck hhaltState)
                  | cons fourth tailRest =>
                      cases third
                      · cases fourth
                        · right
                          exact ⟨none, tailRest, rfl⟩
                        · right
                          exact ⟨some false, tailRest, rfl⟩
                      · cases fourth
                        · right
                          exact ⟨some true, tailRest, rfl⟩
                        · let stuck :=
                            BoolWordSuffixScannerDescription.runConfig 3 c0
                          have hstep :
                              BoolWordSuffixScannerDescription.stepConfig
                                  stuck = none := by
                            simp [stuck, c0,
                              BoolWordSuffixScannerDescription, config,
                              tapeAtCells, keep, keepMove, writeMove,
                              scanLeftToSentinelRestart,
                              MachineDescription.runConfig,
                              MachineDescription.stepConfig,
                              MachineDescription.lookupTransition,
                              MachineDescription.Matches,
                              MachineDescription.transition, Tape.read,
                              Tape.write, Tape.move, Tape.moveRight]
                          have hstuck :
                              stuck.state ≠
                                BoolWordSuffixScannerDescription.halt := by
                            simp [stuck, c0,
                              BoolWordSuffixScannerDescription, config,
                              tapeAtCells, keep, keepMove, writeMove,
                              scanLeftToSentinelRestart,
                              MachineDescription.runConfig,
                              MachineDescription.stepConfig,
                              MachineDescription.lookupTransition,
                              MachineDescription.Matches,
                              MachineDescription.transition, Tape.read,
                              Tape.write, Tape.move, Tape.moveRight]
                          exact False.elim
                            (primitive_runConfig_state_ne_halt_of_reaches_stuck
                              boolWordSuffixScannerDescription_haltTransitionFree
                              (D := BoolWordSuffixScannerDescription)
                              (c := c0) (stuck := stuck) (k := 3) (n := n)
                              rfl hstep hstuck hhaltState)

theorem boolWordSuffixScannerDescription_runConfig_130_inv
    (n : Nat) (baseLeft : List (Option Bool)) (tail : Word Bool)
    {Tout : Tape Bool}
    (h : BoolWordSuffixScannerDescription.runConfig n (config 130 baseLeft (tail.map some)) = { state := BoolWordSuffixScannerDescription.halt, tape := Tout }) :
    exists processed : List (Option Bool), exists tail' : Word Bool, tail = List.append (markedCellsCodeBits processed) tail' ∧
      (tail' = [] ∨ exists suffixTail, tail' = false :: suffixTail) ∧
      BoolWordSuffixScannerDescription.runConfig n (config 130 (List.append ((markedCellsCodeBits processed).reverse.map some) baseLeft) (tail'.map some)) = { state := BoolWordSuffixScannerDescription.halt, tape := Tout } := by
  revert baseLeft tail Tout
  exact
    Nat.strongRecOn
      (motive := fun n =>
        forall baseLeft : List (Option Bool),
        forall tail : Word Bool,
        forall {Tout : Tape Bool},
          BoolWordSuffixScannerDescription.runConfig n
              (config 130 baseLeft (tail.map some)) =
            { state := BoolWordSuffixScannerDescription.halt
              tape := Tout } ->
            exists processed : List (Option Bool),
            exists tail' : Word Bool,
              tail = List.append (markedCellsCodeBits processed) tail' ∧
                (tail' = [] ∨
                  exists suffixTail, tail' = false :: suffixTail) ∧
                BoolWordSuffixScannerDescription.runConfig n
                  (config 130
                    (List.append
                      ((markedCellsCodeBits processed).reverse.map some)
                      baseLeft)
                    (tail'.map some)) =
                  { state := BoolWordSuffixScannerDescription.halt
                    tape := Tout })
      n
      (fun n ih => by
        intro baseLeft tail Tout h
        rcases
            boolWordSuffixScannerDescription_runConfig_130_marked_prefix_inv
              baseLeft tail h with
          (⟨tailRest, htail⟩ | ⟨cell, tailRest, htail⟩)
        · exists [], tail
          constructor
          · simp [markedCellsCodeBits]
          constructor
          · right
            exact ⟨tailRest, htail⟩
          · simpa [markedCellsCodeBits] using h
        · let c0 : MachineDescription.Configuration :=
            config 130 baseLeft (tail.map some)
          let c1 : MachineDescription.Configuration :=
            config 130
              (List.append ((markedCellCodeBits cell).reverse.map some)
                baseLeft)
              (tailRest.map some)
          have hprefix : BoolWordSuffixScannerDescription.runConfig 4 c0 = c1 := by
            dsimp [c0, c1]
            rw [htail]
            simpa [List.map_append] using
              run_boolWordSuffix_state130_markedCell cell baseLeft
                (tailRest.map some)
          have hc1 :
              c1.state ≠ BoolWordSuffixScannerDescription.halt := by
            simp [c1, config, BoolWordSuffixScannerDescription]
          rcases
              runConfig_forward_inv_lt BoolWordSuffixScannerDescription
                c0 c1 n 4 h hprefix
                boolWordSuffixScannerDescription_haltTransitionFree
                hc1 (by omega) with
            ⟨m, hm_lt, hm_halt⟩
          rcases ih m hm_lt
              (List.append ((markedCellCodeBits cell).reverse.map some)
                baseLeft)
              tailRest hm_halt with
            ⟨processed, tail', hprocessed, hrest, hrun⟩
          exists cell :: processed, tail'
          constructor
          · rw [htail, hprocessed]
            simp [markedCellsCodeBits, List.append_assoc]
          constructor
          · exact hrest
          · have hrun_n :
                BoolWordSuffixScannerDescription.runConfig n
                    (config 130
                      (List.append
                        ((markedCellsCodeBits processed).reverse.map some)
                        (List.append
                          ((markedCellCodeBits cell).reverse.map some)
                          baseLeft))
                      (tail'.map some)) =
                  { state := BoolWordSuffixScannerDescription.halt
                    tape := Tout } :=
              runConfig_halt_extend BoolWordSuffixScannerDescription
                (config 130
                  (List.append
                    ((markedCellsCodeBits processed).reverse.map some)
                    (List.append
                      ((markedCellCodeBits cell).reverse.map some)
                      baseLeft))
                  (tail'.map some))
                m n
                boolWordSuffixScannerDescription_haltTransitionFree
                (by omega) hrun
            simpa [markedCellsCodeBits, List.reverse_append,
              List.map_append, List.append_assoc] using hrun_n)

end DovetailLayoutScanner
end CanonicalLayouts
end EncodedRewriters

end Computability
end FoC
