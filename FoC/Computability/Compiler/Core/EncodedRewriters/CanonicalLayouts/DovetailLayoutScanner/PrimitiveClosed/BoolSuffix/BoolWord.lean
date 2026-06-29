import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner.PrimitiveClosed.BoolSuffix.Primitive

set_option doc.verso true

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncodedRewriters
namespace CanonicalLayouts
namespace DovetailLayoutScanner

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner
theorem runConfig_forward_inv
    (D : MachineDescription) (c0 c1 : Configuration)
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
      rw [h_add, runConfig_add] at h_halt
      rw [h_forward] at h_halt
      exact h_halt
  · exists 0
    constructor
    · omega
    · have h_add : k = n + (k - n) := by omega
      rw [h_add, runConfig_add] at h_forward
      rw [h_halt] at h_forward
      have h_halt2 := runConfig_halt h_free Tout (k - n)
      rw [h_halt2] at h_forward
      rw [← h_forward]
      rfl

theorem runConfig_halt_extend
    (D : MachineDescription) (c : Configuration)
    (m n : Nat) {Tout : Tape Bool}
    (h_free : D.HaltTransitionFree)
    (hmn : m ≤ n)
    (h_halt : D.runConfig m c = { state := D.halt, tape := Tout }) :
    D.runConfig n c = { state := D.halt, tape := Tout } := by
  let rem := n - m
  have hn : n = m + rem := by
    omega
  rw [hn, runConfig_add, h_halt]
  exact runConfig_halt h_free Tout rem

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
          runConfig, stepConfig,
          lookupTransition, Matches,
          transition,
          Tape.read, Tape.write, Tape.move, Tape.moveRight]
  | some bit =>
      simpa using run_boolWordSuffix_state130_markedBit bit left right

theorem runConfig_forward_inv_lt
    (D : MachineDescription) (c0 c1 : Configuration)
    (n k : Nat) {Tout : Tape Bool}
    (h_halt : D.runConfig n c0 = { state := D.halt, tape := Tout })
    (h_forward : D.runConfig k c0 = c1)
    (h_free : D.HaltTransitionFree)
    (hc1 : c1.state ≠ D.halt) (hk : 0 < k) :
    exists m, m < n ∧
      D.runConfig m c1 = { state := D.halt, tape := Tout } := by
  rcases firstReaches_halt_of_runConfig_eq
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
        rw [hk_eq, runConfig_add, hfirst]
        exact runConfig_halt h_free Tout rem
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
    rw [hfirst_eq, runConfig_add] at hfirst
    rw [h_forward] at hfirst
    exact hfirst

theorem boolWordSuffixScannerDescription_runConfig_120_nat_prefix_inv
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (h : BoolWordSuffixScannerDescription.runConfig n (config 120 baseLeft (bits.map some)) = { state := BoolWordSuffixScannerDescription.halt, tape := Tout }) :
    exists doneBit tail, bits = false :: false :: true :: doneBit :: tail := by
  let c0 : Configuration :=
    config 120 baseLeft (bits.map some)
  have hhaltState :
      (BoolWordSuffixScannerDescription.runConfig n c0).state =
        BoolWordSuffixScannerDescription.halt := by
    simpa [c0] using congrArg Configuration.state h
  cases bits with
  | nil =>
      let stuck : Configuration := c0
      have hstep :
          BoolWordSuffixScannerDescription.stepConfig stuck = none := by
        simp [stuck, c0, BoolWordSuffixScannerDescription, config,
          tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart, stepConfig,
          lookupTransition, Matches,
          transition, Tape.read]
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
                scanLeftToSentinelRestart, runConfig,
                stepConfig,
                lookupTransition,
                Matches,
                transition, Tape.read, Tape.write,
                Tape.move, Tape.moveRight]
            have hstuck :
                stuck.state ≠ BoolWordSuffixScannerDescription.halt := by
              simp [stuck, c0, BoolWordSuffixScannerDescription, config,
                tapeAtCells, keep, keepMove, writeMove,
                scanLeftToSentinelRestart, runConfig,
                stepConfig,
                lookupTransition,
                Matches,
                transition, Tape.read, Tape.write,
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
                      runConfig,
                      stepConfig,
                      lookupTransition,
                      Matches,
                      transition, Tape.read, Tape.write,
                      Tape.move, Tape.moveRight]
                  have hstuck :
                      stuck.state ≠
                        BoolWordSuffixScannerDescription.halt := by
                    simp [stuck, c0, BoolWordSuffixScannerDescription,
                      config, tapeAtCells, keep, keepMove, writeMove,
                      scanLeftToSentinelRestart,
                      runConfig,
                      stepConfig,
                      lookupTransition,
                      Matches,
                      transition, Tape.read, Tape.write,
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
                          runConfig,
                          stepConfig,
                          lookupTransition,
                          Matches,
                          transition, Tape.read,
                          Tape.write, Tape.move, Tape.moveRight]
                    have hstuck :
                        stuck.state ≠
                          BoolWordSuffixScannerDescription.halt := by
                      cases tail <;>
                        simp [stuck, c0,
                          BoolWordSuffixScannerDescription, config,
                          tapeAtCells, keep, keepMove, writeMove,
                          scanLeftToSentinelRestart,
                          runConfig,
                          stepConfig,
                          lookupTransition,
                          Matches,
                          transition, Tape.read,
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
                            runConfig,
                            stepConfig,
                            lookupTransition,
                            Matches,
                            transition, Tape.read,
                            Tape.write, Tape.move, Tape.moveRight]
                        have hstuck :
                            stuck.state ≠
                              BoolWordSuffixScannerDescription.halt := by
                          simp [stuck, c0,
                            BoolWordSuffixScannerDescription, config,
                            tapeAtCells, keep, keepMove, writeMove,
                            scanLeftToSentinelRestart,
                            runConfig,
                            stepConfig,
                            lookupTransition,
                            Matches,
                            transition, Tape.read,
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
                    runConfig,
                    stepConfig,
                    lookupTransition,
                    Matches,
                    transition, Tape.read, Tape.write,
                    Tape.move, Tape.moveRight]
              have hstuck :
                  stuck.state ≠ BoolWordSuffixScannerDescription.halt := by
                cases restTail <;>
                  simp [stuck, c0, BoolWordSuffixScannerDescription, config,
                    tapeAtCells, keep, keepMove, writeMove,
                    scanLeftToSentinelRestart,
                    runConfig,
                    stepConfig,
                    lookupTransition,
                    Matches,
                    transition, Tape.read, Tape.write,
                    Tape.move, Tape.moveRight]
              exact False.elim
                (primitive_runConfig_state_ne_halt_of_reaches_stuck
                  boolWordSuffixScannerDescription_haltTransitionFree
                  (D := BoolWordSuffixScannerDescription)
                  (c := c0) (stuck := stuck) (k := 1) (n := n)
                  rfl hstep hstuck hhaltState)
      · -- first bit is true: state 120 has no transition for true → stuck at step 0
        let stuck : Configuration := c0
        have hstep :
            BoolWordSuffixScannerDescription.stepConfig stuck = none := by
          cases rest <;>
            simp [stuck, c0, BoolWordSuffixScannerDescription, config,
              tapeAtCells, keep, keepMove, writeMove,
              scanLeftToSentinelRestart, stepConfig,
              lookupTransition,
              Matches,
              transition, Tape.read]
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
        let c0 : Configuration :=
          config 120 baseLeft (tail.map some)
        cases doneBit
        · let c1 : Configuration :=
            config 120
              (List.append (tickBits.reverse.map some) baseLeft)
              (tailRest.map some)
          have hprefix : BoolWordSuffixScannerDescription.runConfig 4 c0 = c1 := by
            dsimp [c0, c1]
            rw [htail]
            simpa [c0, c1, tickBits,
              encodeCodeSymbolAsInput] using
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
              encodeCodeSymbolAsInput, List.reverse_append,
              List.map_append, List.append_assoc] using hrun_n
        · let c1 : Configuration :=
            config 130
              (List.append (doneBits.reverse.map some) baseLeft)
              (tailRest.map some)
          have hprefix : BoolWordSuffixScannerDescription.runConfig 4 c0 = c1 := by
            dsimp [c0, c1]
            rw [htail]
            simpa [c0, c1, doneBits,
              encodeCodeSymbolAsInput] using
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
              encodeCodeSymbolAsInput] using hrun_n)

theorem boolWordSuffixScannerDescription_runConfig_130_marked_prefix_inv
    (baseLeft : List (Option Bool)) (bits : Word Bool)
    {Tout : Tape Bool} {n : Nat}
    (h : BoolWordSuffixScannerDescription.runConfig n (config 130 baseLeft (bits.map some)) = { state := BoolWordSuffixScannerDescription.halt, tape := Tout }) :
    (exists tail, bits = false :: tail) ∨
    (exists cell tailRest, bits = List.append (markedCellCodeBits cell) tailRest) := by
  let c0 : Configuration :=
    config 130 baseLeft (bits.map some)
  have hhaltState :
      (BoolWordSuffixScannerDescription.runConfig n c0).state =
        BoolWordSuffixScannerDescription.halt := by
    simpa [c0] using
      congrArg Configuration.state h
  cases bits with
  | nil =>
      let stuck : Configuration := c0
      have hstep :
          BoolWordSuffixScannerDescription.stepConfig stuck = none := by
        simp [stuck, c0, BoolWordSuffixScannerDescription, config,
          tapeAtCells, keep, keepMove, writeMove,
          scanLeftToSentinelRestart, stepConfig,
          lookupTransition, Matches,
          transition, Tape.read]
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
                scanLeftToSentinelRestart, runConfig,
                stepConfig,
                lookupTransition,
                Matches,
                transition, Tape.read, Tape.write,
                Tape.move, Tape.moveRight]
            have hstuck :
                stuck.state ≠ BoolWordSuffixScannerDescription.halt := by
              simp [stuck, c0, BoolWordSuffixScannerDescription, config,
                tapeAtCells, keep, keepMove, writeMove,
                scanLeftToSentinelRestart, runConfig,
                stepConfig,
                lookupTransition,
                Matches,
                transition, Tape.read, Tape.write,
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
                    runConfig,
                    stepConfig,
                    lookupTransition,
                    Matches,
                    transition, Tape.read, Tape.write,
                    Tape.move, Tape.moveRight]
              have hstuck :
                  stuck.state ≠ BoolWordSuffixScannerDescription.halt := by
                cases restTail <;>
                  simp [stuck, c0, BoolWordSuffixScannerDescription, config,
                    tapeAtCells, keep, keepMove, writeMove,
                    scanLeftToSentinelRestart,
                    runConfig,
                    stepConfig,
                    lookupTransition,
                    Matches,
                    transition, Tape.read, Tape.write,
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
                      runConfig,
                      stepConfig,
                      lookupTransition,
                      Matches,
                      transition, Tape.read, Tape.write,
                      Tape.move, Tape.moveRight]
                  have hstuck :
                      stuck.state ≠ BoolWordSuffixScannerDescription.halt := by
                    simp [stuck, c0, BoolWordSuffixScannerDescription,
                      config, tapeAtCells, keep, keepMove, writeMove,
                      scanLeftToSentinelRestart,
                      runConfig,
                      stepConfig,
                      lookupTransition,
                      Matches,
                      transition, Tape.read, Tape.write,
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
                            runConfig,
                            stepConfig,
                            lookupTransition,
                            Matches,
                            transition, Tape.read,
                            Tape.write, Tape.move, Tape.moveRight]
                      have hstuck :
                          stuck.state ≠
                            BoolWordSuffixScannerDescription.halt := by
                        cases third <;>
                          simp [stuck, c0,
                            BoolWordSuffixScannerDescription, config,
                            tapeAtCells, keep, keepMove, writeMove,
                            scanLeftToSentinelRestart,
                            runConfig,
                            stepConfig,
                            lookupTransition,
                            Matches,
                            transition, Tape.read,
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
                              runConfig,
                              stepConfig,
                              lookupTransition,
                              Matches,
                              transition, Tape.read,
                              Tape.write, Tape.move, Tape.moveRight]
                          have hstuck :
                              stuck.state ≠
                                BoolWordSuffixScannerDescription.halt := by
                            simp [stuck, c0,
                              BoolWordSuffixScannerDescription, config,
                              tapeAtCells, keep, keepMove, writeMove,
                              scanLeftToSentinelRestart,
                              runConfig,
                              stepConfig,
                              lookupTransition,
                              Matches,
                              transition, Tape.read,
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
        · let c0 : Configuration :=
            config 130 baseLeft (tail.map some)
          let c1 : Configuration :=
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
