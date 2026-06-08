import FoC.Computability.Encoding
import FoC.Computability.MachineBuilder
import FoC.Computability.Program

set_option doc.verso true

/-!
# Description-backed program compilation

This module connects the concrete machine descriptions from
{module}`FoC.Computability.Encoding` with the staged-program layer from
{module}`FoC.Computability.Program`.

The compiler predicates here are deliberately explicit.  A staged program is
compiled only when a finite {lit}`MachineDescription` is supplied and proved
to realize the same halting or output behavior.  This avoids treating arbitrary
Lean functions as finitely encodable programs.

## Book coordinates

Used by:
- Chapter 5, Section 5.2: compiler principles for acceptors, Boolean deciders,
  and partial unary range/program descriptions.
- Chapter 5, Section 5.3: exact simulation between decoded descriptions and
  their compiled one-tape Turing machines.
-/

namespace FoC
namespace Computability

open Languages

namespace MachineDescription

/-!
## Exact simulation for compiled descriptions

Well-formed transition tables run in lockstep with their compiled
{name}`TuringMachine`.  The first direction follows the functional
interpreter; the reverse direction says a compiled transition step can only
come from a description-table transition.
-/

theorem lookupTransition_mem {D : MachineDescription}
    {source : Nat} {read : Option Bool} {t : TransitionDescription}
    (h : D.lookupTransition source read = some t) :
    t ∈ D.transitions := by
  unfold lookupTransition at h
  let p := Matches source read
  have hmem :
      forall l : List TransitionDescription,
        l.find? p = some t -> t ∈ l := by
    intro l
    induction l with
    | nil =>
        intro hnil
        simp at hnil
    | cons a rest ih =>
        intro hfind
        rw [List.find?_cons] at hfind
        cases hm : p a
        · simp [hm] at hfind
          have ht : t ∈ rest := ih hfind
          simp [ht]
        · simp [hm] at hfind
          cases hfind
          simp
  exact hmem D.transitions h

theorem stepConfig_state_bound {D : MachineDescription}
    {c d : Configuration}
    (hD : D.WellFormed)
    (hstep : D.stepConfig c = some d) :
    d.state < D.stateCount := by
  unfold stepConfig at hstep
  cases hlookup : D.lookupTransition c.state (Tape.read c.tape) with
  | none =>
      rw [hlookup] at hstep
      cases hstep
  | some t =>
      rw [hlookup] at hstep
      cases hstep
      have htmem : t ∈ D.transitions := lookupTransition_mem hlookup
      exact (hD.right.right.right.left t htmem).right

theorem runConfig_state_bound {D : MachineDescription}
    (hD : D.WellFormed) {n : Nat} {c : Configuration}
    (hc : c.state < D.stateCount) :
    (D.runConfig n c).state < D.stateCount := by
  induction n generalizing c with
  | zero =>
      exact hc
  | succ n ih =>
      change
        (match D.stepConfig c with
        | none => c
        | some next => D.runConfig n next).state < D.stateCount
      cases hstep : D.stepConfig c with
      | none =>
          exact hc
      | some _ =>
          exact ih (stepConfig_state_bound hD hstep)

theorem runConfig_toTuringMachine_computes {D : MachineDescription}
    (hD : D.WellFormed) {n : Nat} {c : Configuration}
    (hc : c.state < D.stateCount) :
    TuringMachine.Computes D.toTuringMachine
      (D.toTMConfig c) (D.toTMConfig (D.runConfig n c)) := by
  induction n generalizing c with
  | zero =>
      exact TuringMachine.Computes.refl (D.toTMConfig c)
  | succ n ih =>
      change TuringMachine.Computes D.toTuringMachine (D.toTMConfig c)
        (D.toTMConfig
          (match D.stepConfig c with
          | none => c
          | some next => D.runConfig n next))
      cases hstep : D.stepConfig c with
      | none =>
          exact TuringMachine.Computes.refl (D.toTMConfig c)
      | some _ =>
          exact TuringMachine.Computes.step
            (MachineDescription.toTuringMachine_step_of_stepConfig
              (D := D)
              (hsource := Nat.lt_trans hc
                (Nat.lt_succ_self D.stateCount))
              hstep)
            (ih (stepConfig_state_bound hD hstep))

theorem toTuringMachine_step_to_stepConfig {D : MachineDescription}
    {c : Configuration}
    {e : TuringMachine.Configuration Bool (Fin (D.stateCount + 1))}
    (hc : c.state < D.stateCount)
    (hstep : TuringMachine.Step D.toTuringMachine (D.toTMConfig c) e) :
    exists d : Configuration, D.stepConfig c = some d ∧ e = D.toTMConfig d := by
  cases hstep with
  | mk haction =>
      change
        (match
          D.lookupTransition (D.stateOfNat c.state).val (Tape.read c.tape)
        with
        | none => none
        | some t => some (t.write, t.move, D.stateOfNat t.target)) =
          some _ at haction
      rw [stateOfNat_val_of_lt
        (Nat.lt_trans hc (Nat.lt_succ_self D.stateCount))] at haction
      cases hlookup : D.lookupTransition c.state (Tape.read c.tape) with
      | none =>
          rw [hlookup] at haction
          cases haction
      | some t =>
          rw [hlookup] at haction
          cases haction
          exists
            { state := t.target
              tape := Tape.move t.move (Tape.write t.write c.tape) }
          constructor
          · simp [stepConfig, hlookup]
          · rfl

theorem toTuringMachine_computesIn_to_runConfig {D : MachineDescription}
    (hD : D.WellFormed) {n : Nat} {c : Configuration}
    (hc : c.state < D.stateCount)
    {e : TuringMachine.Configuration Bool (Fin (D.stateCount + 1))}
    (hcomp : TuringMachine.ComputesIn D.toTuringMachine n (D.toTMConfig c) e) :
    e = D.toTMConfig (D.runConfig n c) := by
  induction n generalizing c e with
  | zero =>
      cases hcomp
      rfl
  | succ n ih =>
      cases hcomp with
      | succ hstep hrest =>
          cases toTuringMachine_step_to_stepConfig hc hstep with
          | intro d hd =>
              cases hd.right
              have hdBound : d.state < D.stateCount :=
                stepConfig_state_bound hD hd.left
              have ihd := ih hdBound hrest
              change _ = D.toTMConfig
                (match D.stepConfig c with
                | none => c
                | some next => D.runConfig n next)
              rw [hd.left]
              exact ihd

/-!
## Output semantics for descriptions
-/

def HaltsWithOutputIn (D : MachineDescription)
    (n : Nat) (w out : Word Bool) : Prop :=
  let final := D.runConfig n (D.initial w)
  final.state = D.halt ∧ Tape.normalizedOutput final.tape = out

def HaltsWithExactOutputIn (D : MachineDescription)
    (n : Nat) (w out : Word Bool) : Prop :=
  let final := D.runConfig n (D.initial w)
  final.state = D.halt ∧ final.tape = Tape.output out

def HaltsWithTapeIn (D : MachineDescription)
    (n : Nat) (w : Word Bool) (T : Tape Bool) : Prop :=
  let final := D.runConfig n (D.initial w)
  final.state = D.halt ∧ final.tape = T

def HaltsWithOutput (D : MachineDescription)
    (w out : Word Bool) : Prop :=
  exists n : Nat, D.HaltsWithOutputIn n w out

def HaltsWithExactOutput (D : MachineDescription)
    (w out : Word Bool) : Prop :=
  exists n : Nat, D.HaltsWithExactOutputIn n w out

def HaltsWithTape (D : MachineDescription)
    (w : Word Bool) (T : Tape Bool) : Prop :=
  exists n : Nat, D.HaltsWithTapeIn n w T

theorem haltsWithExactOutputIn_iff_haltsWithTapeIn_output
    {D : MachineDescription} {n : Nat} {w out : Word Bool} :
    D.HaltsWithExactOutputIn n w out <->
      D.HaltsWithTapeIn n w (Tape.output out) := by
  rfl

theorem haltsWithExactOutput_iff_haltsWithTape_output
    {D : MachineDescription} {w out : Word Bool} :
    D.HaltsWithExactOutput w out <->
      D.HaltsWithTape w (Tape.output out) := by
  rfl

theorem haltsWithOutputIn_of_haltsWithExactOutputIn
    {D : MachineDescription} {n : Nat} {w out : Word Bool}
    (h : D.HaltsWithExactOutputIn n w out) :
    D.HaltsWithOutputIn n w out := by
  rcases h with ⟨hhalt, htape⟩
  exact ⟨hhalt, Tape.normalizedOutput_of_eq_output htape⟩

theorem haltsWithOutput_of_haltsWithExactOutput
    {D : MachineDescription} {w out : Word Bool}
    (h : D.HaltsWithExactOutput w out) :
    D.HaltsWithOutput w out := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, haltsWithOutputIn_of_haltsWithExactOutputIn hn⟩

def ExactOutputRealizes
    (D : MachineDescription) (f : Word Bool -> Word Bool) : Prop :=
  D.WellFormed ∧ forall w : Word Bool, D.HaltsWithExactOutput w (f w)

def ExactOutputComposable
    (A B C : MachineDescription) : Prop :=
  C.WellFormed ∧
    forall w mid out : Word Bool,
      A.HaltsWithExactOutput w mid ->
      B.HaltsWithExactOutput mid out ->
        C.HaltsWithExactOutput w out

theorem ExactOutputRealizes.toOutputRealizes
    {D : MachineDescription} {f : Word Bool -> Word Bool}
    (h : D.ExactOutputRealizes f) :
    D.WellFormed ∧ forall w : Word Bool, D.HaltsWithOutput w (f w) := by
  constructor
  · exact h.left
  · intro w
    exact haltsWithOutput_of_haltsWithExactOutput (h.right w)

theorem ExactOutputComposable.realizes_comp
    {A B C : MachineDescription}
    {f g : Word Bool -> Word Bool}
    (hcomp : ExactOutputComposable A B C)
    (hA : A.ExactOutputRealizes f)
    (hB : B.ExactOutputRealizes g) :
    C.ExactOutputRealizes (fun w => g (f w)) := by
  constructor
  · exact hcomp.left
  · intro w
    exact hcomp.right w (f w) (g (f w)) (hA.right w)
      (hB.right (f w))

def ExactIdentityDescription : MachineDescription where
  stateCount := 1
  start := 0
  halt := 0
  transitions := []

theorem exactIdentityDescription_wellFormed :
    ExactIdentityDescription.WellFormed := by
  simp [ExactIdentityDescription, WellFormed, Deterministic]

theorem exactIdentityDescription_haltsWithExactOutputIn
    (w : Word Bool) :
    ExactIdentityDescription.HaltsWithExactOutputIn 0 w w := by
  constructor
  · rfl
  · rfl

theorem exactIdentityDescription_exactOutputRealizes :
    ExactIdentityDescription.ExactOutputRealizes id := by
  constructor
  · exact exactIdentityDescription_wellFormed
  · intro w
    exact ⟨0, exactIdentityDescription_haltsWithExactOutputIn w⟩

theorem exactIdentityDescription_runConfig_initial
    (n : Nat) (w : Word Bool) :
    ExactIdentityDescription.runConfig n
        (ExactIdentityDescription.initial w) =
      ExactIdentityDescription.initial w := by
  cases n <;>
    simp [runConfig, stepConfig, lookupTransition,
      ExactIdentityDescription]

theorem exactIdentityDescription_haltsWithExactOutput_iff
    (w out : Word Bool) :
    ExactIdentityDescription.HaltsWithExactOutput w out <-> out = w := by
  constructor
  · intro h
    rcases h with ⟨n, hn⟩
    have htape : Tape.input w = Tape.output out := by
      simpa [HaltsWithExactOutputIn,
        exactIdentityDescription_runConfig_initial] using hn.right
    have hw : w = out := Tape.input_injective
      (by simpa [Tape.output] using htape)
    exact hw.symm
  · intro h
    rw [h]
    exact ⟨0, exactIdentityDescription_haltsWithExactOutputIn w⟩

theorem toTuringMachine_haltsOnInput_iff {D : MachineDescription}
    (hD : D.WellFormed) (w : Word Bool) :
    TuringMachine.HaltsOnInput D.toTuringMachine w <-> D.HaltsOnInput w := by
  constructor
  · intro htm
    cases htm with
    | intro final hfinal =>
        cases TuringMachine.computes_to_computesIn hfinal.left with
        | intro n hn =>
            have hrun := toTuringMachine_computesIn_to_runConfig
              (D := D) hD (n := n) (c := D.initial w)
              hD.right.left hn
            have hhalt := hfinal.right
            rw [hrun] at hhalt
            change D.stateOfNat (D.runConfig n (D.initial w)).state =
              D.stateOfNat D.halt at hhalt
            have hval := congrArg Fin.val hhalt
            rw [stateOfNat_val_of_lt
                (Nat.lt_trans
                  (runConfig_state_bound hD hD.right.left)
                  (Nat.lt_succ_self D.stateCount)),
              stateOfNat_val_of_lt
                (Nat.lt_trans hD.right.right.left
                  (Nat.lt_succ_self D.stateCount))] at hval
            exact Exists.intro n hval
  · intro hd
    cases hd with
    | intro n hn =>
        let final := D.runConfig n (D.initial w)
        exists D.toTMConfig final
        constructor
        · exact runConfig_toTuringMachine_computes
            (D := D) hD (n := n) (c := D.initial w) hD.right.left
        · change D.stateOfNat final.state = D.stateOfNat D.halt
          rw [hn]

theorem toTuringMachine_haltsWithOutput_iff {D : MachineDescription}
    (hD : D.WellFormed) (w out : Word Bool) :
    TuringMachine.HaltsWithOutput D.toTuringMachine w out <->
      D.HaltsWithOutput w out := by
  constructor
  · intro htm
    cases htm with
    | intro final hfinal =>
        cases TuringMachine.computes_to_computesIn hfinal.left with
        | intro n hn =>
            have hrun := toTuringMachine_computesIn_to_runConfig
              (D := D) hD (n := n) (c := D.initial w)
              hD.right.left hn
            have hhalt := hfinal.right.left
            have htape := hfinal.right.right
            rw [hrun] at hhalt htape
            change D.stateOfNat (D.runConfig n (D.initial w)).state =
              D.stateOfNat D.halt at hhalt
            have hval := congrArg Fin.val hhalt
            rw [stateOfNat_val_of_lt
                (Nat.lt_trans
                  (runConfig_state_bound hD hD.right.left)
                  (Nat.lt_succ_self D.stateCount)),
              stateOfNat_val_of_lt
                (Nat.lt_trans hD.right.right.left
                  (Nat.lt_succ_self D.stateCount))] at hval
            exact Exists.intro n (And.intro hval htape)
  · intro hd
    cases hd with
    | intro n hn =>
        let final := D.runConfig n (D.initial w)
        exists D.toTMConfig final
        constructor
        · exact runConfig_toTuringMachine_computes
            (D := D) hD (n := n) (c := D.initial w) hD.right.left
        · constructor
          · change D.stateOfNat final.state = D.stateOfNat D.halt
            rw [hn.left]
          · change Tape.normalizedOutput final.tape = out
            exact hn.right

end MachineDescription

/-!
## Description-backed language recognition and decision
-/

def MachineDescriptionAcceptsLanguage
    (D : MachineDescription) (L : Language Bool) : Prop :=
  D.WellFormed ∧ forall w : Word Bool, D.HaltsOnInput w <-> w ∈ L

def MachineDescriptionDecidesLanguage
    (D : MachineDescription) (L : Language Bool) : Prop :=
  D.WellFormed ∧
    forall w : Word Bool,
      (w ∈ L -> D.HaltsWithOutput w [true]) ∧
        (¬ w ∈ L -> D.HaltsWithOutput w [false])

theorem machineDescriptionAcceptsLanguage_turingAcceptable
    {D : MachineDescription} {L : Language Bool}
    (h : MachineDescriptionAcceptsLanguage D L) :
    TuringAcceptable L := by
  exists Bool
  exists Fin (D.stateCount + 1)
  exists D.toTuringMachine
  exists fun b : Bool => b
  intro w
  rw [encodeWord_id]
  exact Iff.trans (MachineDescription.toTuringMachine_haltsOnInput_iff
    h.left w) (h.right w)

theorem machineDescriptionDecidesLanguage_turingDecidable
    {D : MachineDescription} {L : Language Bool}
    (h : MachineDescriptionDecidesLanguage D L) :
    TuringDecidable L := by
  exists Bool
  exists Fin (D.stateCount + 1)
  exists D.toTuringMachine
  exists fun b : Bool => b
  exists false
  exists true
  intro w
  constructor
  · intro hw
    rw [encodeWord_id]
    exact (MachineDescription.toTuringMachine_haltsWithOutput_iff
      h.left w [true]).mpr ((h.right w).left hw)
  · intro hw
    rw [encodeWord_id]
    exact (MachineDescription.toTuringMachine_haltsWithOutput_iff
      h.left w [false]).mpr ((h.right w).right hw)

/-!
## Staged-program compiler predicates
-/

def ProgramCompiledByDescription
    (P : StagedProgram Bool Unit) (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall w : Word Bool,
      D.HaltsOnInput w <-> ProgramHaltsWithOutput P w []

def BoolProgramCompiledByDescription
    (P : StagedProgram Bool Bool) (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      D.HaltsWithOutput w [b] <-> ProgramHaltsWithOutput P w [b]

def ProgramAcceptableByDescription (L : Language Bool) : Prop :=
  exists P : StagedProgram Bool Unit, exists D : MachineDescription,
    ProgramAcceptsLanguage P L ∧ ProgramCompiledByDescription P D

def ProgramBoolDecidableByDescription (L : Language Bool) : Prop :=
  exists P : StagedProgram Bool Bool, exists D : MachineDescription,
    ProgramBoolDecides P L ∧ BoolProgramCompiledByDescription P D

theorem programCompiledByDescription_acceptsLanguage
    {P : StagedProgram Bool Unit} {D : MachineDescription}
    {L : Language Bool}
    (hP : ProgramAcceptsLanguage P L)
    (hcompile : ProgramCompiledByDescription P D) :
    MachineDescriptionAcceptsLanguage D L := by
  constructor
  · exact hcompile.left
  · intro w
    exact Iff.trans (hcompile.right w) (hP w)

theorem boolProgramCompiledByDescription_decidesLanguage
    {P : StagedProgram Bool Bool} {D : MachineDescription}
    {L : Language Bool}
    (hP : ProgramBoolDecides P L)
    (hcompile : BoolProgramCompiledByDescription P D) :
    MachineDescriptionDecidesLanguage D L := by
  constructor
  · exact hcompile.left
  · intro w
    constructor
    · intro hw
      exact (hcompile.right w true).mpr ((hP.left w).mpr hw)
    · intro hw
      exact (hcompile.right w false).mpr ((hP.right w).mpr hw)

theorem programAcceptableByDescription_turingAcceptable
    {L : Language Bool}
    (h : ProgramAcceptableByDescription L) :
    TuringAcceptable L := by
  cases h with
  | intro P hP =>
      cases hP with
      | intro D hD =>
          exact machineDescriptionAcceptsLanguage_turingAcceptable
            (programCompiledByDescription_acceptsLanguage hD.left hD.right)

theorem programBoolDecidableByDescription_turingDecidable
    {L : Language Bool}
    (h : ProgramBoolDecidableByDescription L) :
    TuringDecidable L := by
  cases h with
  | intro P hP =>
      cases hP with
      | intro D hD =>
          exact machineDescriptionDecidesLanguage_turingDecidable
            (boolProgramCompiledByDescription_decidesLanguage hD.left hD.right)

def DescriptionProgramAcceptorCompilationPrinciple : Prop :=
  forall P : StagedProgram Bool Unit,
    exists D : MachineDescription, ProgramCompiledByDescription P D

def DescriptionProgramBoolDeciderCompilationPrinciple : Prop :=
  forall P : StagedProgram Bool Bool,
    exists D : MachineDescription, BoolProgramCompiledByDescription P D

def DovetailDescriptionCompilerPrinciple : Prop :=
  forall accept reject : Word Bool -> Nat -> Prop,
    exists D : MachineDescription,
      BoolProgramCompiledByDescription (DovetailProgram accept reject) D

/-
The broad dovetail compiler above talks about arbitrary Lean traces.  The
paired-recognizer version below is the concrete Section 5.2 transition-level
handoff: both traces come from finite `MachineDescription` interpreters.
It is still a construction principle, but it names the exact uniform machine
description that a real dovetailing compiler must build.
-/

def PairedRecognizerDovetailDescriptionCompilerPrinciple : Prop :=
  forall accept reject : MachineDescription,
    exists D : MachineDescription,
      BoolProgramCompiledByDescription
        (DovetailProgram
          (fun w n => accept.HaltsIn n w)
          (fun w n => reject.HaltsIn n w)) D

def PairedRecognizerBoundedDovetailTableRealizes
    (accept reject decider : MachineDescription) : Prop :=
  decider.WellFormed ∧
    forall w : Word Bool, forall b : Bool,
      decider.HaltsWithOutput w [b] <->
        exists limit : Nat,
          MachineDescription.boundedDovetailOutput
            accept reject w limit = some [b]

def PairedRecognizerBoundedDovetailTableCompilerConstruction : Prop :=
  forall accept reject : MachineDescription,
    exists decider : MachineDescription,
      PairedRecognizerBoundedDovetailTableRealizes accept reject decider

def FixedDescriptionBoundedSimulatorInput
    (L : MachineDescription.SimulatorLayout) : Word Bool :=
  MachineDescription.SimulatorLayout.asBoolInput L

def FixedDescriptionBoundedSimulatorOutput
    (D : MachineDescription)
    (L : MachineDescription.SimulatorLayout) : Word Bool :=
  MachineDescription.SimulatorLayout.asBoolInput
    (MachineDescription.SimulatorLayout.run D L.stage L)

def FixedDescriptionBoundedSimulatorTableRealizes
    (D simulator : MachineDescription) : Prop :=
  simulator.WellFormed ∧
    forall L : MachineDescription.SimulatorLayout,
      simulator.HaltsWithOutput
        (FixedDescriptionBoundedSimulatorInput L)
        (FixedDescriptionBoundedSimulatorOutput D L)

def FixedDescriptionBoundedSimulatorTableCompilerConstruction : Prop :=
  forall D : MachineDescription,
    exists simulator : MachineDescription,
      FixedDescriptionBoundedSimulatorTableRealizes D simulator

theorem fixedDescriptionBoundedSimulatorTableRealizes_wellFormed
    {D simulator : MachineDescription}
    (h : FixedDescriptionBoundedSimulatorTableRealizes D simulator) :
    simulator.WellFormed :=
  h.left

theorem fixedDescriptionBoundedSimulatorTableRealizes_output
    {D simulator : MachineDescription}
    (h : FixedDescriptionBoundedSimulatorTableRealizes D simulator)
    (L : MachineDescription.SimulatorLayout) :
    simulator.HaltsWithOutput
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorOutput D L) :=
  h.right L

theorem fixedDescriptionBoundedSimulatorOutput_run_hit
    (D : MachineDescription) (L : MachineDescription.SimulatorLayout) :
    (MachineDescription.SimulatorLayout.run D L.stage L).hit = true <->
      L.hit = true ∨
        exists n : Nat, n ≤ L.stage ∧
          (D.runConfig n L.config).state = D.halt :=
  MachineDescription.SimulatorLayout.run_hit_eq_true_iff D L.stage L

def FixedDescriptionBoundedSimulatorCode
    (D : MachineDescription) : MachineDescription.TapeCodePrimitive :=
  MachineDescription.SimulatorLayout.runCodePrimitive D

def FixedDescriptionBoundedSimulatorCodeRealizes
    (D : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall L : MachineDescription.SimulatorLayout,
    P.transform (MachineDescription.SimulatorLayout.encode L) =
      some
        (MachineDescription.SimulatorLayout.encode
          (MachineDescription.SimulatorLayout.run D L.stage L))

theorem fixedDescriptionBoundedSimulatorCode_encode
    (D : MachineDescription) (L : MachineDescription.SimulatorLayout) :
    (FixedDescriptionBoundedSimulatorCode D).transform
        (MachineDescription.SimulatorLayout.encode L) =
      some
        (MachineDescription.SimulatorLayout.encode
          (MachineDescription.SimulatorLayout.run D L.stage L)) :=
  MachineDescription.SimulatorLayout.runCodePrimitive_encode D L

theorem fixedDescriptionBoundedSimulatorCode_realizes
    (D : MachineDescription) :
    FixedDescriptionBoundedSimulatorCodeRealizes
      D (FixedDescriptionBoundedSimulatorCode D) := by
  intro L
  exact fixedDescriptionBoundedSimulatorCode_encode D L

theorem fixedDescriptionBoundedSimulatorCode_boolOutput
    (D : MachineDescription) (L : MachineDescription.SimulatorLayout) :
    Option.map MachineDescription.encodeCodeWordAsInput
        ((FixedDescriptionBoundedSimulatorCode D).transform
          (MachineDescription.SimulatorLayout.encode L)) =
      some (FixedDescriptionBoundedSimulatorOutput D L) := by
  simp [fixedDescriptionBoundedSimulatorCode_encode,
    FixedDescriptionBoundedSimulatorOutput,
    MachineDescription.SimulatorLayout.asBoolInput]

def FixedDescriptionStepCode
    (D : MachineDescription) : MachineDescription.TapeCodePrimitive :=
  MachineDescription.stepConfigurationCodePrimitive D

def FixedDescriptionStepCodeRealizes
    (D : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall c : MachineDescription.Configuration,
    P.transform (MachineDescription.encodeConfiguration c) =
      some (MachineDescription.encodeConfiguration (D.runConfig 1 c))

theorem fixedDescriptionStepCode_encode
    (D : MachineDescription) (c : MachineDescription.Configuration) :
    (FixedDescriptionStepCode D).transform
        (MachineDescription.encodeConfiguration c) =
      some (MachineDescription.encodeConfiguration (D.runConfig 1 c)) :=
  MachineDescription.stepConfigurationCodePrimitive_encodeConfiguration D c

theorem fixedDescriptionStepCode_realizes
    (D : MachineDescription) :
    FixedDescriptionStepCodeRealizes D (FixedDescriptionStepCode D) := by
  intro c
  exact fixedDescriptionStepCode_encode D c

def PairedRecognizerDovetailLayoutCode
    (accept reject : MachineDescription) :
    MachineDescription.TapeCodePrimitive :=
  MachineDescription.DovetailLayout.runCodePrimitive accept reject

def PairedRecognizerDovetailLayoutCodeRealizes
    (accept reject : MachineDescription)
    (P : MachineDescription.TapeCodePrimitive) : Prop :=
  forall L : MachineDescription.DovetailLayout,
    P.transform (MachineDescription.DovetailLayout.encode L) =
      some
        (MachineDescription.DovetailLayout.encode
          (MachineDescription.DovetailLayout.run
            accept reject L.stage L))

theorem pairedRecognizerDovetailLayoutCode_encode
    (accept reject : MachineDescription)
    (L : MachineDescription.DovetailLayout) :
    (PairedRecognizerDovetailLayoutCode accept reject).transform
        (MachineDescription.DovetailLayout.encode L) =
      some
        (MachineDescription.DovetailLayout.encode
          (MachineDescription.DovetailLayout.run
            accept reject L.stage L)) :=
  MachineDescription.DovetailLayout.runCodePrimitive_encode
    accept reject L

theorem pairedRecognizerDovetailLayoutCode_realizes
    (accept reject : MachineDescription) :
    PairedRecognizerDovetailLayoutCodeRealizes
      accept reject
      (PairedRecognizerDovetailLayoutCode accept reject) := by
  intro L
  exact pairedRecognizerDovetailLayoutCode_encode accept reject L

theorem pairedRecognizerDovetailLayout_initial_output
    (accept reject : MachineDescription)
    (w : Word Bool) (limit : Nat) :
    MachineDescription.DovetailLayout.outputFromHits
        (MachineDescription.DovetailLayout.run accept reject limit
          (MachineDescription.DovetailLayout.initial
            accept reject w limit)) =
      MachineDescription.boundedDovetailOutput accept reject w limit :=
  MachineDescription.DovetailLayout.outputFromHits_run_initial_eq_boundedDovetailOutput
    accept reject w limit

def TapeCodePrimitiveCompiledByDescription
    (P : MachineDescription.TapeCodePrimitive)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall code out : Word MachineCodeSymbol,
      D.HaltsWithExactOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
          P.transform code = some out

theorem tapeCodePrimitiveCompiledByDescription_identity :
    TapeCodePrimitiveCompiledByDescription
      MachineDescription.TapeCodePrimitive.identity
      MachineDescription.ExactIdentityDescription := by
  constructor
  · exact MachineDescription.exactIdentityDescription_wellFormed
  · intro code out
    constructor
    · intro h
      have hbool :
          MachineDescription.encodeCodeWordAsInput out =
            MachineDescription.encodeCodeWordAsInput code :=
        (MachineDescription.exactIdentityDescription_haltsWithExactOutput_iff
          (MachineDescription.encodeCodeWordAsInput code)
          (MachineDescription.encodeCodeWordAsInput out)).mp h
      have hout : out = code :=
        MachineDescription.encodeCodeWordAsInput_injective hbool
      simp [MachineDescription.TapeCodePrimitive.identity, hout]
    · intro h
      simp [MachineDescription.TapeCodePrimitive.identity] at h
      rw [← h]
      exact
        (MachineDescription.exactIdentityDescription_haltsWithExactOutput_iff
          (MachineDescription.encodeCodeWordAsInput code)
          (MachineDescription.encodeCodeWordAsInput code)).mpr rfl

def TapeCodePrimitiveCodeComposition
    (A B C : MachineDescription) : Prop :=
  C.WellFormed ∧
    forall code out : Word MachineCodeSymbol,
      C.HaltsWithExactOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
        exists mid : Word MachineCodeSymbol,
          A.HaltsWithExactOutput
              (MachineDescription.encodeCodeWordAsInput code)
              (MachineDescription.encodeCodeWordAsInput mid) ∧
            B.HaltsWithExactOutput
              (MachineDescription.encodeCodeWordAsInput mid)
              (MachineDescription.encodeCodeWordAsInput out)

theorem tapeCodePrimitiveCompiledByDescription_compose
    {P Q : MachineDescription.TapeCodePrimitive}
    {A B C : MachineDescription}
    (hcomp : TapeCodePrimitiveCodeComposition A B C)
    (hP : TapeCodePrimitiveCompiledByDescription P A)
    (hQ : TapeCodePrimitiveCompiledByDescription Q B) :
    TapeCodePrimitiveCompiledByDescription
      (MachineDescription.TapeCodePrimitive.compose P Q) C := by
  constructor
  · exact hcomp.left
  · intro code out
    constructor
    · intro h
      rcases (hcomp.right code out).mp h with
        ⟨mid, hA, hB⟩
      have hPmid : P.transform code = some mid :=
        (hP.right code mid).mp hA
      have hQout : Q.transform mid = some out :=
        (hQ.right mid out).mp hB
      exact
        MachineDescription.TapeCodePrimitive.compose_transform_some
          hPmid hQout
    · intro h
      unfold MachineDescription.TapeCodePrimitive.compose at h
      cases hPcode : P.transform code with
      | none =>
          simp [hPcode] at h
      | some mid =>
          have hQout : Q.transform mid = some out := by
            simpa [hPcode] using h
          apply (hcomp.right code out).mpr
          exists mid
          constructor
          · exact (hP.right code mid).mpr hPcode
          · exact (hQ.right mid out).mpr hQout

def FixedDescriptionBoundedSimulatorCodeCompilerConstruction : Prop :=
  forall D : MachineDescription,
    exists simulator : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        (FixedDescriptionBoundedSimulatorCode D) simulator

def FixedDescriptionStepCodeCompilerConstruction : Prop :=
  forall D : MachineDescription,
    exists stepper : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        (FixedDescriptionStepCode D) stepper

def PairedRecognizerDovetailLayoutCodeCompilerConstruction : Prop :=
  forall accept reject : MachineDescription,
    exists runner : MachineDescription,
      TapeCodePrimitiveCompiledByDescription
        (PairedRecognizerDovetailLayoutCode accept reject) runner

theorem fixedDescriptionBoundedSimulatorTableRealizes_of_codeCompiler
    {D simulator : MachineDescription}
    (hcompile : TapeCodePrimitiveCompiledByDescription
      (FixedDescriptionBoundedSimulatorCode D) simulator) :
    FixedDescriptionBoundedSimulatorTableRealizes D simulator := by
  constructor
  · exact hcompile.left
  · intro L
    have hExact :
        simulator.HaltsWithExactOutput
          (FixedDescriptionBoundedSimulatorInput L)
          (FixedDescriptionBoundedSimulatorOutput D L) := by
      have hcode := (hcompile.right
        (MachineDescription.SimulatorLayout.encode L)
        (MachineDescription.SimulatorLayout.encode
          (MachineDescription.SimulatorLayout.run D L.stage L))).mpr
          (fixedDescriptionBoundedSimulatorCode_encode D L)
      simpa [FixedDescriptionBoundedSimulatorInput,
        FixedDescriptionBoundedSimulatorOutput,
        MachineDescription.SimulatorLayout.asBoolInput] using hcode
    exact MachineDescription.haltsWithOutput_of_haltsWithExactOutput hExact

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_codeCompiler
    (hcompile :
      FixedDescriptionBoundedSimulatorCodeCompilerConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction := by
  intro D
  rcases hcompile D with ⟨simulator, hsimulator⟩
  exact ⟨simulator,
    fixedDescriptionBoundedSimulatorTableRealizes_of_codeCompiler
      hsimulator⟩

structure FixedDescriptionBoundedSimulatorPhaseTargets
    (D : MachineDescription) where
  decodeLayout :
    MachineDescription.SimulatorLayout ->
      MachineDescription.SimulatorLayout
  simulateStep :
    MachineDescription.SimulatorLayout ->
      MachineDescription.SimulatorLayout
  repeatControl :
    MachineDescription.SimulatorLayout ->
      MachineDescription.SimulatorLayout
  emitLayout :
    MachineDescription.SimulatorLayout ->
      MachineDescription.SimulatorLayout
  pipeline_correct :
    forall L : MachineDescription.SimulatorLayout,
      emitLayout (repeatControl (simulateStep (decodeLayout L))) =
        MachineDescription.SimulatorLayout.run D L.stage L

namespace FixedDescriptionBoundedSimulatorPhaseTargets

def canonical (D : MachineDescription) :
    FixedDescriptionBoundedSimulatorPhaseTargets D where
  decodeLayout := id
  simulateStep := fun L =>
    MachineDescription.SimulatorLayout.run D L.stage L
  repeatControl := id
  emitLayout := id
  pipeline_correct := by
    intro L
    rfl

theorem canonical_pipeline_correct
    (D : MachineDescription) (L : MachineDescription.SimulatorLayout) :
    (canonical D).emitLayout
        ((canonical D).repeatControl
          ((canonical D).simulateStep ((canonical D).decodeLayout L))) =
      MachineDescription.SimulatorLayout.run D L.stage L :=
  (canonical D).pipeline_correct L

end FixedDescriptionBoundedSimulatorPhaseTargets

def FixedDescriptionBoundedSimulatorPhaseRealizes
    (phase :
      MachineDescription.SimulatorLayout ->
        MachineDescription.SimulatorLayout)
    (fragment : MachineDescription.Fragment) : Prop :=
  fragment.WellFormed ∧
    forall L : MachineDescription.SimulatorLayout,
      fragment.toDescription.HaltsWithExactOutput
        (FixedDescriptionBoundedSimulatorInput L)
        (FixedDescriptionBoundedSimulatorInput (phase L))

theorem fixedDescriptionBoundedSimulatorPhaseRealizes_output
    {phase :
      MachineDescription.SimulatorLayout ->
        MachineDescription.SimulatorLayout}
    {fragment : MachineDescription.Fragment}
    (h : FixedDescriptionBoundedSimulatorPhaseRealizes phase fragment) :
    fragment.WellFormed ∧
      forall L : MachineDescription.SimulatorLayout,
        fragment.toDescription.HaltsWithOutput
          (FixedDescriptionBoundedSimulatorInput L)
          (FixedDescriptionBoundedSimulatorInput (phase L)) := by
  constructor
  · exact h.left
  · intro L
    exact MachineDescription.haltsWithOutput_of_haltsWithExactOutput
      (h.right L)

structure FixedDescriptionBoundedSimulatorSkeletonPhaseRealizes
    (D : MachineDescription)
    (S : MachineDescription.FixedSimulatorTableSkeleton)
    (targets : FixedDescriptionBoundedSimulatorPhaseTargets D) :
    Prop where
  decodeLayout :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      targets.decodeLayout S.decodeLayout
  simulateStep :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      targets.simulateStep S.simulateStep
  repeatControl :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      targets.repeatControl S.repeatControl
  emitLayout :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      targets.emitLayout S.emitLayout

def FixedDescriptionBoundedSimulatorSkeletonRealizes
    (D : MachineDescription)
    (S : MachineDescription.FixedSimulatorTableSkeleton)
    (handoffMove : Direction) : Prop :=
  forall L : MachineDescription.SimulatorLayout,
    (S.toDescription handoffMove).HaltsWithOutput
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorOutput D L)

def FixedDescriptionBoundedSimulatorSkeletonRealizesExact
    (D : MachineDescription)
    (S : MachineDescription.FixedSimulatorTableSkeleton)
    (handoffMove : Direction) : Prop :=
  forall L : MachineDescription.SimulatorLayout,
    (S.toDescription handoffMove).HaltsWithExactOutput
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorOutput D L)

theorem fixedDescriptionBoundedSimulatorSkeletonRealizes_of_exact
    {D : MachineDescription}
    {S : MachineDescription.FixedSimulatorTableSkeleton}
    {handoffMove : Direction}
    (h : FixedDescriptionBoundedSimulatorSkeletonRealizesExact
      D S handoffMove) :
    FixedDescriptionBoundedSimulatorSkeletonRealizes D S handoffMove := by
  intro L
  exact MachineDescription.haltsWithOutput_of_haltsWithExactOutput
    (h L)

theorem fixedDescriptionBoundedSimulatorTableRealizes_of_skeletonRealizes
    {D : MachineDescription}
    {S : MachineDescription.FixedSimulatorTableSkeleton}
    {handoffMove : Direction}
    (h : FixedDescriptionBoundedSimulatorSkeletonRealizes
      D S handoffMove) :
    FixedDescriptionBoundedSimulatorTableRealizes
      D (S.toDescription handoffMove) := by
  constructor
  · exact
      MachineDescription.FixedSimulatorTableSkeleton.toDescription_wellFormed
        S handoffMove
  · exact h

theorem fixedDescriptionBoundedSimulatorSkeletonRealizes_output
    {D : MachineDescription}
    {S : MachineDescription.FixedSimulatorTableSkeleton}
    {handoffMove : Direction}
    (h : FixedDescriptionBoundedSimulatorSkeletonRealizes
      D S handoffMove)
    (L : MachineDescription.SimulatorLayout) :
    (S.toDescription handoffMove).HaltsWithOutput
      (FixedDescriptionBoundedSimulatorInput L)
      (FixedDescriptionBoundedSimulatorOutput D L) :=
  h L

def FixedDescriptionBoundedSimulatorSkeletonCompilerConstruction : Prop :=
  forall D : MachineDescription,
    exists S : MachineDescription.FixedSimulatorTableSkeleton,
      exists handoffMove : Direction,
        FixedDescriptionBoundedSimulatorSkeletonRealizes D S handoffMove

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_skeletonCompiler
    (hcompile :
      FixedDescriptionBoundedSimulatorSkeletonCompilerConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction := by
  intro D
  rcases hcompile D with ⟨S, handoffMove, hS⟩
  exact ⟨S.toDescription handoffMove,
    fixedDescriptionBoundedSimulatorTableRealizes_of_skeletonRealizes hS⟩

def FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction : Prop :=
  forall D : MachineDescription,
    exists S : MachineDescription.FixedSimulatorTableSkeleton,
      exists targets : FixedDescriptionBoundedSimulatorPhaseTargets D,
        FixedDescriptionBoundedSimulatorSkeletonPhaseRealizes
          D S targets

def FixedDescriptionBoundedSimulatorSkeletonPhaseSoundness : Prop :=
  forall D : MachineDescription,
    forall S : MachineDescription.FixedSimulatorTableSkeleton,
    forall handoffMove : Direction,
    forall targets : FixedDescriptionBoundedSimulatorPhaseTargets D,
      FixedDescriptionBoundedSimulatorSkeletonPhaseRealizes
        D S targets ->
      FixedDescriptionBoundedSimulatorSkeletonRealizes D S handoffMove

theorem fixedDescriptionBoundedSimulatorSkeletonCompiler_of_phaseCompiler
    (hsound : FixedDescriptionBoundedSimulatorSkeletonPhaseSoundness)
    (hcompile :
      FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction) :
      FixedDescriptionBoundedSimulatorSkeletonCompilerConstruction := by
  intro D
  rcases hcompile D with ⟨S, targets, htargets⟩
  exact ⟨S, Direction.right,
    hsound D S Direction.right targets htargets⟩

theorem fixedDescriptionBoundedSimulatorTableCompiler_of_phaseCompiler
    (hsound : FixedDescriptionBoundedSimulatorSkeletonPhaseSoundness)
    (hcompile :
      FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction) :
    FixedDescriptionBoundedSimulatorTableCompilerConstruction :=
  fixedDescriptionBoundedSimulatorTableCompiler_of_skeletonCompiler
    (fixedDescriptionBoundedSimulatorSkeletonCompiler_of_phaseCompiler
      hsound hcompile)

theorem pairedRecognizerDovetailDescriptionCompiler_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple := by
  intro accept reject
  exact hcompile
    (fun w n => accept.HaltsIn n w)
    (fun w n => reject.HaltsIn n w)

theorem pairedRecognizerDovetailDescriptionCompiler_of_boundedDovetailTableCompiler
    (hcompile :
      PairedRecognizerBoundedDovetailTableCompilerConstruction) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple := by
  intro accept reject
  cases hcompile accept reject with
  | intro decider hdecider =>
      exists decider
      constructor
      · exact hdecider.left
      · intro w b
        constructor
        · intro hhalt
          cases (hdecider.right w b).mp hhalt with
          | intro limit hlimit =>
              exists limit
              rwa [MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run]
                at hlimit
        · intro hprog
          cases hprog with
          | intro limit hlimit =>
              apply (hdecider.right w b).mpr
              exists limit
              rwa [MachineDescription.boundedDovetailOutput_eq_dovetailProgram_run]

theorem dovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    DovetailDescriptionCompilerPrinciple := by
  intro accept reject
  exact hcompile (DovetailProgram accept reject)

theorem pairedRecognizerDovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    PairedRecognizerDovetailDescriptionCompilerPrinciple :=
  pairedRecognizerDovetailDescriptionCompiler_of_dovetailDescriptionCompiler
    (dovetailDescriptionCompiler_of_descriptionBoolDeciderCompiler hcompile)

theorem programAcceptorCompilationPrinciple_of_descriptionCompiler
    (hcompile : DescriptionProgramAcceptorCompilationPrinciple) :
    ProgramAcceptorCompilationPrinciple Bool := by
  intro L hL
  cases hL with
  | intro P hP =>
      cases hcompile P with
      | intro D hD =>
          exact programAcceptableByDescription_turingAcceptable
            (Exists.intro P (Exists.intro D (And.intro hP hD)))

theorem programBoolDeciderCompilationPrinciple_of_descriptionCompiler
    (hcompile : DescriptionProgramBoolDeciderCompilationPrinciple) :
    ProgramBoolDeciderCompilationPrinciple Bool := by
  intro L hL
  cases hL with
  | intro P hP =>
      cases hcompile P with
      | intro D hD =>
          exact programBoolDecidableByDescription_turingDecidable
            (Exists.intro P (Exists.intro D (And.intro hP hD)))

theorem complementaryTraces_turingDecidable_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple)
    {L : Language Bool}
    {accept reject : Word Bool -> Nat -> Prop}
    (htraces : ComplementaryAcceptanceTraces accept reject L) :
    TuringDecidable L := by
  cases hcompile accept reject with
  | intro D hD =>
      exact programBoolDecidableByDescription_turingDecidable
        (Exists.intro (DovetailProgram accept reject)
          (Exists.intro D (And.intro (dovetailProgram_decides htraces) hD)))

theorem reCoRe_turingDecidable_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple)
    {L : Language Bool}
    (h : RecursivelyEnumerableWithComplement L) :
    TuringDecidable L := by
  cases recursivelyEnumerable_with_complement_has_complementaryTraces h with
  | intro accept haccept =>
      cases haccept with
      | intro reject htraces =>
          exact complementaryTraces_turingDecidable_of_dovetailDescriptionCompiler
            hcompile htraces

theorem reCoReToDecidablePrinciple_of_dovetailDescriptionCompiler
    (hcompile : DovetailDescriptionCompilerPrinciple) :
    ReCoReToDecidablePrinciple Bool := by
  intro L h
  exact reCoRe_turingDecidable_of_dovetailDescriptionCompiler hcompile h

/-!
## Encoded input languages and universal runners

Section 5.3 encodes machine descriptions and their inputs over the common
{name}`MachineCodeSymbol` alphabet, while concrete descriptions still execute
on Boolean tapes. The next predicates isolate the exact compiler and runner
obligations needed for a concrete universal machine.
-/

def MachineDescriptionAcceptsEncodedInputLanguage
    (D : MachineDescription)
    (L : Language MachineCodeSymbol) : Prop :=
  D.WellFormed ∧ Language.Equal (MachineDescription.EncodedInputLanguage D) L

def EncodedInputProgramCompiledByDescription
    (P : StagedProgram MachineCodeSymbol Unit)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall w : Word MachineCodeSymbol,
      D.HaltsOnInput (MachineDescription.encodeCodeWordAsInput w) <->
        ProgramHaltsWithOutput P w []

def EncodedInputProgramAcceptorCompilationPrinciple : Prop :=
  forall P : StagedProgram MachineCodeSymbol Unit,
    exists D : MachineDescription,
      EncodedInputProgramCompiledByDescription P D

def EncodedInputDescriptionCompilerPrinciple : Prop :=
  forall L : Language MachineCodeSymbol,
    RecursivelyEnumerable L ->
      exists D : MachineDescription,
        MachineDescriptionAcceptsEncodedInputLanguage D L

def CodeUniversalMachineSpec
    (universal : TuringMachine MachineCodeSymbol state) : Prop :=
  forall machine input : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput universal
      (Languages.Word.Concat machine input) <->
        MachineDescription.CodeAccepts machine input

def ImmediateHaltingDescription : MachineDescription where
  stateCount := 1
  start := 0
  halt := 0
  transitions := []

theorem immediateHaltingDescription_haltsOnInput
    (input : Word Bool) :
    ImmediateHaltingDescription.HaltsOnInput input := by
  exact ⟨0, rfl⟩

theorem codeAccepts_empty_false
    (input : Word MachineCodeSymbol) :
    ¬ MachineDescription.CodeAccepts [] input := by
  intro h
  rcases h with ⟨D, hdecode, _⟩
  simp [MachineDescription.decodeDescription] at hdecode

theorem codeUniversalMachineSpec_rawConcat_inconsistent
    (universal : TuringMachine MachineCodeSymbol state) :
    ¬ CodeUniversalMachineSpec universal := by
  intro hspec
  let D := ImmediateHaltingDescription
  have haccept :
      MachineDescription.CodeAccepts
        (MachineDescription.encodeDescription D) [] :=
    MachineDescription.codeAccepts_of_encodeDescription
      (immediateHaltingDescription_haltsOnInput [])
  have hhalts :
      TuringMachine.HaltsOnInput universal
        (Languages.Word.Concat (MachineDescription.encodeDescription D) []) :=
    (hspec (MachineDescription.encodeDescription D) []).mpr haccept
  have hhaltsEmpty :
      TuringMachine.HaltsOnInput universal
        (Languages.Word.Concat [] (MachineDescription.encodeDescription D)) := by
    simpa [Languages.Word.Concat] using hhalts
  have hfalse :
      MachineDescription.CodeAccepts []
        (MachineDescription.encodeDescription D) :=
    (hspec [] (MachineDescription.encodeDescription D)).mp hhaltsEmpty
  exact codeAccepts_empty_false (MachineDescription.encodeDescription D) hfalse

def CodeUniversalPrefixMachineSpec
    (universal : TuringMachine MachineCodeSymbol state) : Prop :=
  forall encoded : Word MachineCodeSymbol,
    TuringMachine.HaltsOnInput universal encoded <->
      MachineDescription.CodePrefixAccepts encoded

def CodeUniversalPrefixMachineRowLanguage
    (universal : TuringMachine MachineCodeSymbol state)
    (machine : Word MachineCodeSymbol) : Language MachineCodeSymbol :=
  fun input => TuringMachine.HaltsOnInput universal
    (Languages.Word.Concat machine input)

def CodeUniversalPrefixRowsCoverAcceptableLanguages
    (universal : TuringMachine MachineCodeSymbol state) : Prop :=
  forall L : Language MachineCodeSymbol, RecursivelyEnumerable L ->
    exists machine : Word MachineCodeSymbol,
      Language.Equal
        (CodeUniversalPrefixMachineRowLanguage universal machine) L

def CodeUniversalPrefixRunnerConstruction : Prop :=
  exists state : Type,
    exists universal : TuringMachine MachineCodeSymbol state,
      CodeUniversalPrefixMachineSpec universal

def CodeUniversalPrefixRowsCoverConstruction : Prop :=
  exists state : Type,
    exists universal : TuringMachine MachineCodeSymbol state,
      CodeUniversalPrefixMachineSpec universal ∧
        CodeUniversalPrefixRowsCoverAcceptableLanguages universal

structure CodeUniversalPrefixSection53Closeout where
  encodedInputProgramCompiler : EncodedInputProgramAcceptorCompilationPrinciple
  universalRunner : CodeUniversalPrefixRunnerConstruction

theorem codeUniversalPrefixMachine_halts_on_encoded_description_iff
    {universal : TuringMachine MachineCodeSymbol state}
    (hspec : CodeUniversalPrefixMachineSpec universal)
    (D : MachineDescription)
    (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsOnInput universal
      (Languages.Word.Concat (MachineDescription.encodeDescription D) input) <->
        D.HaltsOnInput (MachineDescription.encodeCodeWordAsInput input) := by
  exact Iff.trans
    (hspec (Languages.Word.Concat (MachineDescription.encodeDescription D) input))
    (MachineDescription.codePrefixAccepts_encodeDescription_append_iff D input)

theorem codeUniversalPrefixMachine_rowLanguage_equal_encodedInputLanguage
    {universal : TuringMachine MachineCodeSymbol state}
    (hspec : CodeUniversalPrefixMachineSpec universal)
    (D : MachineDescription) :
    Language.Equal
      (CodeUniversalPrefixMachineRowLanguage universal
        (MachineDescription.encodeDescription D))
      (MachineDescription.EncodedInputLanguage D) :=
  codeUniversalPrefixMachine_halts_on_encoded_description_iff hspec D

theorem codeUniversalPrefixRowsCoverAcceptableLanguages_of_encodedInputDescriptionCompiler
    {universal : TuringMachine MachineCodeSymbol state}
    (hspec : CodeUniversalPrefixMachineSpec universal)
    (hcompile : EncodedInputDescriptionCompilerPrinciple) :
    CodeUniversalPrefixRowsCoverAcceptableLanguages universal := by
  intro L hL
  cases hcompile L hL with
  | intro D hD =>
      exists MachineDescription.encodeDescription D
      exact Language.equal_trans
        (codeUniversalPrefixMachine_rowLanguage_equal_encodedInputLanguage
          hspec D)
        hD.right

theorem codeUniversalPrefixRowsCoverConstruction_of_constructions
    (hcompile : EncodedInputDescriptionCompilerPrinciple)
    (hrunner : CodeUniversalPrefixRunnerConstruction) :
    CodeUniversalPrefixRowsCoverConstruction := by
  unfold CodeUniversalPrefixRunnerConstruction at hrunner
  rcases hrunner with ⟨state, universal, hspec⟩
  exact
    ⟨state, universal,
      hspec,
      codeUniversalPrefixRowsCoverAcceptableLanguages_of_encodedInputDescriptionCompiler
        hspec hcompile⟩

def CodeUniversalMachineRowLanguage
    (universal : TuringMachine MachineCodeSymbol state)
    (machine : Word MachineCodeSymbol) : Language MachineCodeSymbol :=
  fun input => TuringMachine.HaltsOnInput universal
    (Languages.Word.Concat machine input)

def CodeUniversalRowsCoverAcceptableLanguages
    (universal : TuringMachine MachineCodeSymbol state) : Prop :=
  forall L : Language MachineCodeSymbol, RecursivelyEnumerable L ->
    exists machine : Word MachineCodeSymbol,
      Language.Equal (CodeUniversalMachineRowLanguage universal machine) L

def CodeUniversalRunnerConstruction : Prop :=
  exists state : Type,
    exists universal : TuringMachine MachineCodeSymbol state,
      CodeUniversalMachineSpec universal

theorem not_codeUniversalRunnerConstruction :
    ¬ CodeUniversalRunnerConstruction := by
  intro h
  unfold CodeUniversalRunnerConstruction at h
  rcases h with ⟨state, universal, hspec⟩
  exact codeUniversalMachineSpec_rawConcat_inconsistent universal hspec

def CodeUniversalRowsCoverConstruction : Prop :=
  exists state : Type,
    exists universal : TuringMachine MachineCodeSymbol state,
      CodeUniversalMachineSpec universal ∧
        CodeUniversalRowsCoverAcceptableLanguages universal

structure CodeUniversalSection53Closeout where
  encodedInputProgramCompiler : EncodedInputProgramAcceptorCompilationPrinciple
  universalRunner : CodeUniversalRunnerConstruction

theorem not_codeUniversalSection53Closeout :
    ¬ CodeUniversalSection53Closeout := by
  intro hclose
  exact not_codeUniversalRunnerConstruction hclose.universalRunner

theorem encodedInputProgramCompiledByDescription_acceptsLanguage
    {P : StagedProgram MachineCodeSymbol Unit}
    {D : MachineDescription}
    {L : Language MachineCodeSymbol}
    (hP : ProgramAcceptsLanguage P L)
    (hcompile : EncodedInputProgramCompiledByDescription P D) :
    MachineDescriptionAcceptsEncodedInputLanguage D L := by
  constructor
  · exact hcompile.left
  · intro w
    exact Iff.trans (hcompile.right w) (hP w)

theorem encodedInputDescriptionCompilerPrinciple_of_programCompiler
    (hcompile : EncodedInputProgramAcceptorCompilationPrinciple) :
    EncodedInputDescriptionCompilerPrinciple := by
  intro L hL
  cases recursivelyEnumerable_has_acceptanceTrace hL with
  | intro trace htrace =>
      cases hcompile (TraceRecognizerProgram trace) with
      | intro D hD =>
          exists D
          exact encodedInputProgramCompiledByDescription_acceptsLanguage
            (traceRecognizerProgram_acceptsLanguage htrace) hD

theorem codeUniversalMachineRowLanguage_equal_codeAcceptedLanguage
    {universal : TuringMachine MachineCodeSymbol state}
    (hspec : CodeUniversalMachineSpec universal)
    (machine : Word MachineCodeSymbol) :
    Language.Equal
      (CodeUniversalMachineRowLanguage universal machine)
      (MachineDescription.CodeAcceptedLanguage machine) :=
  hspec machine

theorem codeUniversalMachineRowLanguage_equal_encodedInputLanguage
    {universal : TuringMachine MachineCodeSymbol state}
    (hspec : CodeUniversalMachineSpec universal)
    (D : MachineDescription) :
    Language.Equal
      (CodeUniversalMachineRowLanguage universal
        (MachineDescription.encodeDescription D))
      (MachineDescription.EncodedInputLanguage D) := by
  intro input
  exact Iff.trans
    (codeUniversalMachineRowLanguage_equal_codeAcceptedLanguage
      hspec (MachineDescription.encodeDescription D) input)
    (MachineDescription.codeAccepts_encodeDescription_iff D input)

theorem codeUniversalRowsCoverAcceptableLanguages_of_encodedInputDescriptionCompiler
    {universal : TuringMachine MachineCodeSymbol state}
    (hspec : CodeUniversalMachineSpec universal)
    (hcompile : EncodedInputDescriptionCompilerPrinciple) :
    CodeUniversalRowsCoverAcceptableLanguages universal := by
  intro L hL
  cases hcompile L hL with
  | intro D hD =>
      exists MachineDescription.encodeDescription D
      exact Language.equal_trans
        (codeUniversalMachineRowLanguage_equal_encodedInputLanguage hspec D)
        hD.right

theorem codeUniversalRowsCoverConstruction_of_constructions
    (hcompile : EncodedInputDescriptionCompilerPrinciple)
    (hrunner : CodeUniversalRunnerConstruction) :
    CodeUniversalRowsCoverConstruction := by
  cases hrunner with
  | intro state hstate =>
      cases hstate with
      | intro universal hspec =>
          exact
            Exists.intro state
              (Exists.intro universal
                (And.intro hspec
                  (codeUniversalRowsCoverAcceptableLanguages_of_encodedInputDescriptionCompiler
                    hspec hcompile)))

theorem encodedInputDescriptionCompilerPrinciple_of_section53Closeout
    (hclose : CodeUniversalSection53Closeout) :
    EncodedInputDescriptionCompilerPrinciple :=
  encodedInputDescriptionCompilerPrinciple_of_programCompiler
    hclose.encodedInputProgramCompiler

theorem codeUniversalPrefixRowsCoverConstruction_of_section53Closeout
    (hclose : CodeUniversalPrefixSection53Closeout) :
    CodeUniversalPrefixRowsCoverConstruction :=
  codeUniversalPrefixRowsCoverConstruction_of_constructions
    (encodedInputDescriptionCompilerPrinciple_of_programCompiler
      hclose.encodedInputProgramCompiler)
    hclose.universalRunner

theorem codeUniversalRowsCoverConstruction_of_section53Closeout
    (hclose : CodeUniversalSection53Closeout) :
    CodeUniversalRowsCoverConstruction :=
  codeUniversalRowsCoverConstruction_of_constructions
    (encodedInputDescriptionCompilerPrinciple_of_section53Closeout hclose)
    hclose.universalRunner

/-!
## Compiled partial-function ranges
-/

def PartialFunctionCompiledByDescription
    (f : Word input -> Option (Word Bool))
    (encodeInput : input -> Bool)
    (D : MachineDescription) : Prop :=
  D.WellFormed ∧
    forall w : Word input,
      match f w with
      | some out => D.HaltsWithOutput (EncodeWord encodeInput w) out
      | none => ¬ D.HaltsOnInput (EncodeWord encodeInput w)

theorem partialFunctionCompiledByDescription_turingComputablePartial
    {f : Word input -> Option (Word Bool)}
    {encodeInput : input -> Bool}
    {D : MachineDescription}
    (h : PartialFunctionCompiledByDescription f encodeInput D) :
    TuringComputablePartial f := by
  exists Bool
  exists Fin (D.stateCount + 1)
  exists D.toTuringMachine
  exists encodeInput
  exists fun b : Bool => b
  intro w
  cases hf : f w with
  | none =>
      have hnone := h.right w
      rw [hf] at hnone
      intro hhalt
      exact hnone ((MachineDescription.toTuringMachine_haltsOnInput_iff
        h.left (EncodeWord encodeInput w)).mp hhalt)
  | some out =>
      have hsome := h.right w
      rw [hf] at hsome
      simp at hsome
      simpa [encodeWord_id] using
        (MachineDescription.toTuringMachine_haltsWithOutput_iff
          h.left (EncodeWord encodeInput w) out).mpr hsome

def PartialUnaryTuringComputableRange (L : Language Bool) : Prop :=
  exists f : Word Unit -> Option (Word Bool),
    TuringComputablePartial f ∧ Language.Equal (PartialRangeLanguage f) L

def CompiledPartialUnaryRange (L : Language Bool) : Prop :=
  exists f : Word Unit -> Option (Word Bool), exists D : MachineDescription,
    PartialFunctionCompiledByDescription f (fun _ : Unit => true) D ∧
      Language.Equal (PartialRangeLanguage f) L

def CompiledPartialUnaryFunctionProgramRange (L : Language Bool) : Prop :=
  exists f : Word Unit -> Option (Word Bool), exists D : MachineDescription,
    PartialFunctionCompiledByDescription f (fun _ : Unit => true) D ∧
      Language.Equal (ProgramRangeLanguage (PartialFunctionProgram f)) L

def PartialUnaryRangeDescriptionCompilerPrinciple : Prop :=
  forall f : Word Unit -> Option (Word Bool),
    exists D : MachineDescription,
      PartialFunctionCompiledByDescription f (fun _ : Unit => true) D

theorem compiledPartialUnaryRange_partialRangeOfUnaryFunction
    {L : Language Bool}
    (h : CompiledPartialUnaryRange L) :
    PartialRangeOfUnaryFunction L := by
  cases h with
  | intro f hf =>
      cases hf with
      | intro _ hD =>
          exists f
          exact hD.right

theorem compiledPartialUnaryRange_turingComputableRange
    {L : Language Bool}
    (h : CompiledPartialUnaryRange L) :
    PartialUnaryTuringComputableRange L := by
  cases h with
  | intro f hf =>
      cases hf with
      | intro D hD =>
          exists f
          constructor
          · exact partialFunctionCompiledByDescription_turingComputablePartial
              hD.left
          · exact hD.right

theorem compiledPartialUnaryFunctionProgramRange_compiledRange
    {L : Language Bool}
    (h : CompiledPartialUnaryFunctionProgramRange L) :
    CompiledPartialUnaryRange L := by
  cases h with
  | intro f hf =>
      cases hf with
      | intro D hD =>
          exists f
          exists D
          constructor
          · exact hD.left
          · exact Language.equal_trans
              (Language.equal_symm (partialFunctionProgram_range f))
              hD.right

theorem compiledPartialUnaryFunctionProgramRange_turingComputableRange
    {L : Language Bool}
    (h : CompiledPartialUnaryFunctionProgramRange L) :
    PartialUnaryTuringComputableRange L :=
  compiledPartialUnaryRange_turingComputableRange
    (compiledPartialUnaryFunctionProgramRange_compiledRange h)

theorem compiledPartialUnaryFunctionProgramRange_partialRange
    {L : Language Bool}
    (h : CompiledPartialUnaryFunctionProgramRange L) :
    PartialRangeOfUnaryFunction L :=
  compiledPartialUnaryRange_partialRangeOfUnaryFunction
    (compiledPartialUnaryFunctionProgramRange_compiledRange h)

theorem compiledPartialUnaryRange_of_partialRangeOfUnaryFunction
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    {L : Language Bool}
    (h : PartialRangeOfUnaryFunction L) :
    CompiledPartialUnaryRange L := by
  cases h with
  | intro f hf =>
      cases hcompile f with
      | intro D hD =>
          exact Exists.intro f (Exists.intro D (And.intro hD hf))

theorem compiledPartialUnaryRange_of_partiallyListable
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    {L : Language Bool}
    (h : PartiallyListable L) :
    CompiledPartialUnaryRange L :=
  compiledPartialUnaryRange_of_partialRangeOfUnaryFunction
    hcompile (partiallyListable_partialRangeOfUnaryFunction h)

theorem compiledPartialUnaryFunctionProgramRange_of_partialRangeOfUnaryFunction
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    {L : Language Bool}
    (h : PartialRangeOfUnaryFunction L) :
    CompiledPartialUnaryFunctionProgramRange L := by
  cases h with
  | intro f hf =>
      cases hcompile f with
      | intro D hD =>
          exact Exists.intro f
            (Exists.intro D
              (And.intro hD
                (Language.equal_trans (partialFunctionProgram_range f) hf)))

theorem compiledPartialUnaryFunctionProgramRange_of_partiallyListable
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    {L : Language Bool}
    (h : PartiallyListable L) :
    CompiledPartialUnaryFunctionProgramRange L :=
  compiledPartialUnaryFunctionProgramRange_of_partialRangeOfUnaryFunction
    hcompile (partiallyListable_partialRangeOfUnaryFunction h)

theorem compiledPartialUnaryRange_of_unaryProgramRange
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    (P : StagedProgram Unit Bool) :
    CompiledPartialUnaryRange (ProgramRangeLanguage P) :=
  compiledPartialUnaryRange_of_partialRangeOfUnaryFunction
    hcompile (programRange_partialRangeOfUnaryFunction P)

theorem compiledPartialUnaryFunctionProgramRange_of_unaryProgramRange
    (hcompile : PartialUnaryRangeDescriptionCompilerPrinciple)
    (P : StagedProgram Unit Bool) :
    CompiledPartialUnaryFunctionProgramRange (ProgramRangeLanguage P) :=
  compiledPartialUnaryFunctionProgramRange_of_partialRangeOfUnaryFunction
    hcompile (programRange_partialRangeOfUnaryFunction P)

end Computability
end FoC
