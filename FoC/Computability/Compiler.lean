import FoC.Computability.Encoding
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
  final.state = D.halt ∧ final.tape = Tape.output out

def HaltsWithOutput (D : MachineDescription)
    (w out : Word Bool) : Prop :=
  exists n : Nat, D.HaltsWithOutputIn n w out

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
          · change final.tape = Tape.output out
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

end Computability
end FoC
