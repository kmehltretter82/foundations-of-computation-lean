import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.RightFieldLocator
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Dispatch.RightFirstCell
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Edits.MarkedPrefixRestorer
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseEmbedding
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseRetarget

set_option doc.verso true

/-!
# Nonempty-right removal

A finite exact-fuel machine that removes the first right cell, restores the
serialized frame prefix, and decrements the right-cell count.
-/

namespace FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.Update.RightRemoval

open Languages
open SerializedFieldComposer
open Dispatch.RightFirstCell
open Edits.MarkedPrefixRestorer

inductive Control where
  | core (inner : Dispatch.RightFirstCell.CombinedMachine.Control)
  | restore (head nextHead : Option MachineCodeSymbol)
      (inner : Edits.MarkedPrefixRestorer.Control)
  | count (head nextHead : Option MachineCodeSymbol)
      (inner : DeleteRestagedMachine.Control)
deriving DecidableEq
namespace Control
def optionalFinite : Foundation.FiniteType (Option MachineCodeSymbol) :=
  Foundation.FiniteType.option MachineCodeSymbol.finite
def pairFinite : Foundation.FiniteType (Option MachineCodeSymbol × Option MachineCodeSymbol) :=
  Foundation.FiniteType.prod optionalFinite optionalFinite
def restoreFinite : Foundation.FiniteType ((Option MachineCodeSymbol × Option MachineCodeSymbol) ×
      Edits.MarkedPrefixRestorer.Control) :=
  Foundation.FiniteType.prod pairFinite Edits.MarkedPrefixRestorer.Control.finite
def countFinite : Foundation.FiniteType ((Option MachineCodeSymbol × Option MachineCodeSymbol) ×
      DeleteRestagedMachine.Control) :=
  Foundation.FiniteType.prod pairFinite DeleteRestagedMachine.Control.finite
def elems : List Control :=
  List.append (Dispatch.RightFirstCell.CombinedMachine.Control.elems.map Control.core) (List.append
      (restoreFinite.elems.map fun p => Control.restore p.1.1 p.1.2 p.2)
      (countFinite.elems.map fun p => Control.count p.1.1 p.1.2 p.2))
def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro c
    cases c with
    | core inner =>
        have h := Dispatch.RightFirstCell.CombinedMachine.Control.finite.complete inner
        change inner ∈ Dispatch.RightFirstCell.CombinedMachine.Control.elems at h
        simp [elems, h]
    | restore head nextHead inner =>
        have h := restoreFinite.complete ((head, nextHead), inner)
        simp [elems]
        exact ⟨head, nextHead, inner, h, rfl, rfl, rfl⟩
    | count head nextHead inner =>
        have h := countFinite.complete ((head, nextHead), inner)
        simp [elems]
        exact ⟨head, nextHead, inner, h, rfl, rfl, rfl⟩
end Control
def coreEmbed : Dispatch.RightFirstCell.CombinedMachine.Control -> Control
  | .tail (.delete head nextHead (.rewind .gate)) => .restore head nextHead .header
  | inner => .core inner
def restoreEmbed (head nextHead : Option MachineCodeSymbol) :
    Edits.MarkedPrefixRestorer.Control -> Control
  | .gate => .count head nextHead (.edit (.erase (DeleteBlock.optionalGap none)))
  | inner => .restore head nextHead inner
def countEmbed (head nextHead : Option MachineCodeSymbol) :
    DeleteRestagedMachine.Control -> Control := Control.count head nextHead
def transition : Control -> Option MachineCodeSymbol ->
    Option (Option MachineCodeSymbol × Direction × Control)
  | .core inner, read =>
      match Dispatch.RightFirstCell.CombinedMachine.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, coreEmbed target)
  | .restore head nextHead inner, read =>
      match Edits.MarkedPrefixRestorer.transition inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, restoreEmbed head nextHead target)
  | .count head nextHead inner, read =>
      match DeleteRestagedMachine.transition none inner read with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, countEmbed head nextHead target)
def machine : TuringMachine MachineCodeSymbol Control where
  start := coreEmbed Dispatch.RightFirstCell.CombinedMachine.machine.start
  halt := .count none none (.rewind .gate)
  transition := transition
  statesFinite := Control.finite
def coreConfig (c : TuringMachine.Configuration MachineCodeSymbol
    Dispatch.RightFirstCell.CombinedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig coreEmbed c
private def restoreConfig (head nextHead : Option MachineCodeSymbol) (c : TuringMachine.Configuration MachineCodeSymbol
      Edits.MarkedPrefixRestorer.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig (restoreEmbed head nextHead) c
private def countConfig (head nextHead : Option MachineCodeSymbol) (c : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  TuringMachine.PhaseEmbedding.liftConfig (countEmbed head nextHead) c
theorem lift_step_of_transition
    {innerState outerState : Type} (inner : TuringMachine MachineCodeSymbol innerState) (outer : TuringMachine MachineCodeSymbol outerState) (embed : innerState -> outerState) (htransition : ∀ state read write direction target,
      inner.transition state read = some (write, direction, target) ->
      outer.transition (embed state) read =
        some (write, direction, embed target)) (c d : TuringMachine.Configuration MachineCodeSymbol innerState) (hstep : inner.stepConfig c = some d) :
    outer.stepConfig (TuringMachine.PhaseEmbedding.liftConfig embed c) =
      some (TuringMachine.PhaseEmbedding.liftConfig embed d) := by
  cases c with
  | mk state tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      cases hinner : inner.transition state (Tape.read tape) with
      | none => simp_all
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [hinner] at hstep
          simp only at hstep
          cases hstep
          simp only [TuringMachine.PhaseEmbedding.liftConfig]
          rw [htransition state (Tape.read tape) write direction target hinner]
theorem lift_run_of_transition
    {innerState outerState : Type} (inner : TuringMachine MachineCodeSymbol innerState) (outer : TuringMachine MachineCodeSymbol outerState) (embed : innerState -> outerState) (htransition : ∀ state read write direction target,
      inner.transition state read = some (write, direction, target) ->
      outer.transition (embed state) read = some (write, direction, embed target))
    {steps : Nat} {source target : TuringMachine.Configuration MachineCodeSymbol innerState} (hrun : inner.runConfigExact? steps source = some target) :
    outer.runConfigExact? steps
      (TuringMachine.PhaseEmbedding.liftConfig embed source) =
      some (TuringMachine.PhaseEmbedding.liftConfig embed target) := by
  apply TuringMachine.PhaseRetarget.runConfigExact?_lift_active_of_eq_some embed
  · intro c d hstep
    exact lift_step_of_transition inner outer embed htransition c d hstep
  · exact hrun
private theorem core_run_of_some {steps : Nat}
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Dispatch.RightFirstCell.CombinedMachine.Control} (hrun : Dispatch.RightFirstCell.CombinedMachine.machine.runConfigExact?
      steps source = some target) :
    machine.runConfigExact? steps (coreConfig source) = some (coreConfig target) := by
  apply lift_run_of_transition
    Dispatch.RightFirstCell.CombinedMachine.machine machine coreEmbed ?_ hrun
  ·
    intro state read write direction target htransition
    cases state with
    | locate inner | locateReturn inner =>
        simp_all [Dispatch.RightFirstCell.CombinedMachine.machine,
          Dispatch.RightFirstCell.CombinedMachine.transition,
          machine, transition, coreEmbed]
    | tail inner =>
        cases inner with
        | delete head nextHead inner =>
            cases inner with
            | edit edit =>
                simp_all [Dispatch.RightFirstCell.CombinedMachine.machine,
                  Dispatch.RightFirstCell.CombinedMachine.transition,
                  machine, transition, coreEmbed]
            | rewind inner =>
                cases inner <;>
                  simp_all [Dispatch.RightFirstCell.CombinedMachine.machine,
                    Dispatch.RightFirstCell.CombinedMachine.transition,
                    Dispatch.RightFirstCell.TailMachine.transition,
                    DeleteRestagedMachine.transition, DeleteEndpointRewind.transition,
                    machine, transition, coreEmbed]
        | _ =>
            simp_all [Dispatch.RightFirstCell.CombinedMachine.machine,
              Dispatch.RightFirstCell.CombinedMachine.transition,
              machine, transition, coreEmbed]
private theorem restore_run_of_some (head nextHead : Option MachineCodeSymbol)
    {steps : Nat} {source target : TuringMachine.Configuration MachineCodeSymbol
      Edits.MarkedPrefixRestorer.Control} (hrun : Edits.MarkedPrefixRestorer.machine.runConfigExact?
      steps source = some target) :
    machine.runConfigExact? steps (restoreConfig head nextHead source) =
      some (restoreConfig head nextHead target) := by
  apply lift_run_of_transition Edits.MarkedPrefixRestorer.machine machine (restoreEmbed head nextHead) ?_ hrun
  ·
    intro inner read write direction target htransition
    cases inner <;> simp_all [Edits.MarkedPrefixRestorer.machine,
      Edits.MarkedPrefixRestorer.transition, machine, transition, restoreEmbed]
private theorem count_run_of_some (head nextHead : Option MachineCodeSymbol)
    {steps : Nat} {source target : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control} (hrun : (DeleteRestagedMachine.machine none).runConfigExact?
      steps source = some target) :
    machine.runConfigExact? steps (countConfig head nextHead source) =
      some (countConfig head nextHead target) := by
  apply lift_run_of_transition (DeleteRestagedMachine.machine none) machine (countEmbed head nextHead) ?_ hrun
  ·
    intro state read write direction target htransition
    simp_all [DeleteRestagedMachine.machine, machine, transition, countEmbed]
private theorem runConfigExact_trans {first second : Nat}
    {a b c : TuringMachine.Configuration MachineCodeSymbol Control} (hab : machine.runConfigExact? first a = some b) (hbc : machine.runConfigExact? second b = some c) :
    machine.runConfigExact? (first + second) a = some c := by
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr
  exact TuringMachine.computesIn_trans (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hab) (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hbc)
def runSteps {stateCount : Nat} (L : Layout stateCount) (nextHead : Option MachineCodeSymbol) (remainingRight : List (Option MachineCodeSymbol)) (callerData : Word MachineCodeSymbol) : Nat :=
  (Dispatch.RightFirstCell.CombinedMachine.runSteps
      L nextHead remainingRight callerData + Edits.MarkedPrefixRestorer.runSteps L) +
    Edits.MarkedPrefixRestorer.CountDecrement.runSteps L remainingRight callerData
theorem run_exact {stateCount : Nat} (L : Layout stateCount) (nextHead : Option MachineCodeSymbol) (remainingRight : List (Option MachineCodeSymbol)) (callerData : Word MachineCodeSymbol) (hright : L.right = nextHead :: remainingRight) :
    ∃ endpoint,
      machine.runConfigExact? (runSteps L nextHead remainingRight callerData)
          (coreConfig (Dispatch.RightFirstCell.CombinedMachine.locateConfig
            (Dispatch.RightFieldLocator.OuterLocator.locateConfig
              (FieldLocator.startConfig L callerData)))) = some endpoint ∧
      endpoint.state = Control.count L.head nextHead
        (Edits.MarkedPrefixRestorer.CountDecrement.targetConfig
          L remainingRight callerData).state ∧
      Tape.Equiv (Edits.MarkedPrefixRestorer.CountDecrement.targetConfig
        L remainingRight callerData).tape endpoint.tape := by
  have hcore := core_run_of_some (Dispatch.RightFirstCell.CombinedMachine.run_exact
      L nextHead remainingRight callerData hright)
  have hcoreTarget :
      coreConfig (Dispatch.RightFirstCell.CombinedMachine.tailConfig
        (Dispatch.RightFirstCell.TailMachine.deleteConfig L.head nextHead
          (Dispatch.RightFirstCell.deleteGateConfig
            L nextHead remainingRight callerData))) =
      restoreConfig L.head nextHead
        { state := Edits.MarkedPrefixRestorer.Control.header
          tape := (Dispatch.RightFirstCell.deleteGateConfig
            L nextHead remainingRight callerData).tape } := rfl
  rw [hcoreTarget] at hcore
  rcases Edits.MarkedPrefixRestorer.run_exact_from_deleteGate
      L nextHead remainingRight callerData with
    ⟨restoreEndpoint, hrestoreInner, hrestoreState, hrestoreTape⟩
  have hrestore := restore_run_of_some L.head nextHead hrestoreInner
  have hactualCountSource : restoreConfig L.head nextHead restoreEndpoint =
      countConfig L.head nextHead
        { state := (Edits.MarkedPrefixRestorer.CountDecrement.sourceConfig
            L remainingRight callerData).state
          tape := restoreEndpoint.tape } := by
    cases restoreEndpoint with
    | mk actualState tape =>
        simp only at hrestoreState
        subst actualState
        rfl
  rw [hactualCountSource] at hrestore
  have hcountTape : Tape.Equiv
      (Edits.MarkedPrefixRestorer.CountDecrement.sourceConfig
        L remainingRight callerData).tape restoreEndpoint.tape := by
    rw [Edits.MarkedPrefixRestorer.CountDecrement.source_tape_eq_restoreGate
      L nextHead remainingRight callerData hright]
    exact hrestoreTape
  rcases Edits.MarkedPrefixRestorer.CountDecrement.run_exact_of_tape_equiv
      L remainingRight callerData restoreEndpoint.tape hcountTape with
    ⟨countEndpoint, hcountInner, hcountState, hcountTapeFinal⟩
  have hcount := count_run_of_some L.head nextHead hcountInner
  have hrun := runConfigExact_trans (runConfigExact_trans hcore hrestore) hcount
  refine ⟨countConfig L.head nextHead countEndpoint, ?_, ?_, hcountTapeFinal⟩
  · simpa [runSteps, Nat.add_assoc] using hrun
  · simpa [countConfig, countEmbed,
      TuringMachine.PhaseEmbedding.liftConfig] using hcountState

end FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe.Update.RightRemoval
