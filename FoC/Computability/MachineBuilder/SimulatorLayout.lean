import FoC.Computability.MachineBuilder.TapeCode

set_option doc.verso true

/-!
# Machine-builder simulator layouts
-/

namespace FoC
namespace Computability

open Languages

namespace MachineDescription

structure SimulatorLayout where
  input : Word Bool
  stage : Nat
  config : Configuration
  hit : Bool


namespace SimulatorLayout

def encodeAppend (L : SimulatorLayout)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    encodeBoolWordAppend L.input
      (encodeNatAppend L.stage
        (encodeConfigurationAppend L.config
          (encodeBoolAppend L.hit suffix)))

def encode (L : SimulatorLayout) : Word MachineCodeSymbol :=
  encodeAppend L []

def decode (tokens : Word MachineCodeSymbol) :
    Option (SimulatorLayout × Word MachineCodeSymbol) :=
  match tokens with
  | MachineCodeSymbol.header :: rest =>
      match decodeBoolWord rest with
      | none => none
      | some (input, rest) =>
          match decodeNat rest with
          | none => none
          | some (stage, rest) =>
              match decodeConfiguration rest with
              | none => none
              | some (config, rest) =>
                  match decodeBool rest with
                  | none => none
                  | some (hit, suffix) =>
                      some ({ input := input
                              stage := stage
                              config := config
                              hit := hit }, suffix)
  | _ => none

theorem decode_encodeAppend
    (L : SimulatorLayout) (suffix : Word MachineCodeSymbol) :
    decode (encodeAppend L suffix) = some (L, suffix) := by
  cases L
  simp [encodeAppend, decode, decodeBoolWord_encodeBoolWordAppend,
    decodeNat_encodeNatAppend, decodeConfiguration_encodeConfigurationAppend,
    decodeBool_encodeBoolAppend]

theorem decode_encode (L : SimulatorLayout) :
    decode (encode L) = some (L, []) :=
  decode_encodeAppend L []

def decodeComplete (tokens : Word MachineCodeSymbol) :
    Option SimulatorLayout :=
  match decode tokens with
  | some (L, []) => some L
  | _ => none

theorem decodeComplete_encode (L : SimulatorLayout) :
    decodeComplete (encode L) = some L := by
  simp [decodeComplete, decode_encode]

def normalizeCode (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodeComplete tokens with
  | none => none
  | some L => some (encode L)

theorem normalizeCode_encode (L : SimulatorLayout) :
    normalizeCode (encode L) = some (encode L) := by
  simp [normalizeCode, decodeComplete_encode]

def normalizeCodePrimitive : TapeCodePrimitive where
  transform := normalizeCode

theorem normalizeCodePrimitive_encode (L : SimulatorLayout) :
    normalizeCodePrimitive.transform (encode L) =
      some (encode L) :=
  normalizeCode_encode L

def asBoolInput (L : SimulatorLayout) : Word Bool :=
  encodeCodeWordAsInput (encode L)

def tape (L : SimulatorLayout) : Tape Bool :=
  Tape.input (asBoolInput L)

theorem tape_normalizedOutput (L : SimulatorLayout) :
    Tape.normalizedOutput (tape L) = asBoolInput L := by
  simpa [tape, asBoolInput] using
    (Tape.normalizedOutput_output (encodeCodeWordAsInput (encode L)))

def initial (D : MachineDescription) (w : Word Bool)
    (stage : Nat) : SimulatorLayout where
  input := w
  stage := stage
  config := D.initial w
  hit := false

def nextConfig (D : MachineDescription)
    (c : Configuration) : Configuration :=
  match D.stepConfig c with
  | none => c
  | some next => next

theorem nextConfig_eq_runConfig_one
    (D : MachineDescription) (c : Configuration) :
    nextConfig D c = D.runConfig 1 c := by
  cases hstep : D.stepConfig c <;>
    simp [nextConfig, runConfig, hstep]

def haltedConfigBool (D : MachineDescription)
    (c : Configuration) : Bool :=
  c.state == D.halt

theorem haltedConfigBool_eq_true_iff
    (D : MachineDescription) (c : Configuration) :
    haltedConfigBool D c = true <-> c.state = D.halt := by
  simp [haltedConfigBool]

def step (D : MachineDescription)
    (L : SimulatorLayout) : SimulatorLayout :=
  let next := nextConfig D L.config
  { L with
    config := next
    hit := L.hit || haltedConfigBool D next }

theorem step_config
    (D : MachineDescription) (L : SimulatorLayout) :
    (step D L).config = D.runConfig 1 L.config := by
  simp [step, nextConfig_eq_runConfig_one]

theorem step_input
    (D : MachineDescription) (L : SimulatorLayout) :
    (step D L).input = L.input :=
  rfl

theorem step_stage
    (D : MachineDescription) (L : SimulatorLayout) :
    (step D L).stage = L.stage :=
  rfl

theorem step_hit_eq_true_iff
    (D : MachineDescription) (L : SimulatorLayout) :
    (step D L).hit = true <->
      L.hit = true ∨ (D.runConfig 1 L.config).state = D.halt := by
  simp [step, nextConfig_eq_runConfig_one, haltedConfigBool_eq_true_iff]

def haltedFromConfigInBool (D : MachineDescription)
    (c : Configuration) (n : Nat) : Bool :=
  (D.runConfig n c).state == D.halt

theorem haltedFromConfigInBool_eq_true_iff
    (D : MachineDescription) (c : Configuration) (n : Nat) :
    haltedFromConfigInBool D c n = true <->
      (D.runConfig n c).state = D.halt := by
  simp [haltedFromConfigInBool]

def hitsFromConfigByBool (D : MachineDescription)
    (c : Configuration) : Nat -> Bool
  | 0 => haltedFromConfigInBool D c 0
  | limit + 1 =>
      hitsFromConfigByBool D c limit ||
        haltedFromConfigInBool D c (limit + 1)

theorem hitsFromConfigByBool_eq_true_iff
    (D : MachineDescription) (c : Configuration) (limit : Nat) :
    hitsFromConfigByBool D c limit = true <->
      exists n : Nat, n ≤ limit ∧
        (D.runConfig n c).state = D.halt := by
  induction limit with
  | zero =>
      constructor
      · intro h
        exact ⟨0, Nat.le_refl 0,
          (haltedFromConfigInBool_eq_true_iff D c 0).mp h⟩
      · intro h
        rcases h with ⟨n, hnle, hhalt⟩
        have hn : n = 0 := by omega
        cases hn
        exact (haltedFromConfigInBool_eq_true_iff D c 0).mpr hhalt
  | succ limit ih =>
      constructor
      · intro h
        have hcases :
            hitsFromConfigByBool D c limit = true ∨
              haltedFromConfigInBool D c (limit + 1) = true := by
          simpa [hitsFromConfigByBool] using h
        cases hcases with
        | inl hprev =>
            rcases ih.mp hprev with ⟨n, hnle, hhalt⟩
            exact ⟨n, Nat.le_trans hnle (Nat.le_succ limit), hhalt⟩
        | inr hnow =>
            exact ⟨limit + 1, Nat.le_refl (limit + 1),
              (haltedFromConfigInBool_eq_true_iff
                D c (limit + 1)).mp hnow⟩
      · intro h
        rcases h with ⟨n, hnle, hhalt⟩
        by_cases hn : n ≤ limit
        · have hprev : hitsFromConfigByBool D c limit = true :=
            ih.mpr ⟨n, hn, hhalt⟩
          simp [hitsFromConfigByBool, hprev]
        · have hnEq : n = limit + 1 := by omega
          cases hnEq
          have hnow :
              haltedFromConfigInBool D c (limit + 1) = true :=
            (haltedFromConfigInBool_eq_true_iff
              D c (limit + 1)).mpr hhalt
          simp [hitsFromConfigByBool, hnow]

def run (D : MachineDescription)
    (steps : Nat) (L : SimulatorLayout) : SimulatorLayout :=
  { L with
    config := D.runConfig steps L.config
    hit := L.hit || hitsFromConfigByBool D L.config steps }

theorem run_config
    (D : MachineDescription) (steps : Nat) (L : SimulatorLayout) :
    (run D steps L).config = D.runConfig steps L.config :=
  rfl

theorem run_input
    (D : MachineDescription) (steps : Nat) (L : SimulatorLayout) :
    (run D steps L).input = L.input :=
  rfl

theorem run_stage
    (D : MachineDescription) (steps : Nat) (L : SimulatorLayout) :
    (run D steps L).stage = L.stage :=
  rfl

theorem run_hit_eq_true_iff
    (D : MachineDescription) (steps : Nat) (L : SimulatorLayout) :
    (run D steps L).hit = true <->
      L.hit = true ∨
        exists n : Nat, n ≤ steps ∧
          (D.runConfig n L.config).state = D.halt := by
  simp [run, hitsFromConfigByBool_eq_true_iff]

theorem run_initial_hit_eq_true_iff
    (D : MachineDescription) (w : Word Bool) (steps : Nat) :
    (run D steps (initial D w steps)).hit = true <->
      exists n : Nat, n ≤ steps ∧ D.HaltsIn n w := by
  simp [run_hit_eq_true_iff, initial, HaltsIn]

def runCode (D : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodeComplete tokens with
  | none => none
  | some L => some (encode (run D L.stage L))

theorem runCode_encode
    (D : MachineDescription) (L : SimulatorLayout) :
    runCode D (encode L) = some (encode (run D L.stage L)) := by
  simp [runCode, decodeComplete_encode]

def runCodePrimitive (D : MachineDescription) : TapeCodePrimitive where
  transform := runCode D

theorem runCodePrimitive_encode
    (D : MachineDescription) (L : SimulatorLayout) :
    (runCodePrimitive D).transform (encode L) =
      some (encode (run D L.stage L)) :=
  runCode_encode D L

def afterRun (D : MachineDescription)
    (L : SimulatorLayout) (steps : Nat) : SimulatorLayout :=
  { L with
    config := D.runConfig steps L.config
    hit := L.hit ||
      ((D.runConfig steps L.config).state == D.halt) }

theorem afterRun_config
    (D : MachineDescription) (L : SimulatorLayout) (steps : Nat) :
    (afterRun D L steps).config = D.runConfig steps L.config :=
  rfl

end SimulatorLayout

end MachineDescription

end Computability
end FoC
