import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.FieldDecomposition
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.EgressSemantics
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.PipelineContracts
import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.LoopDispatcher

set_option doc.verso true

/-!
# Exact guarded egress for #18

This module starts from the real post-dispatch data currency.  Logical tape 0
contains the exact final tape window, logical tape 1 is the consumed stage
counter, and logical tape 2 contains compact source metadata, the original
scratch-width markers, and the live final hit bit.  A known dispatcher branch
also carries the final state in finite control; an unmatched branch recovers
that state from the compact metadata.

The branch witness must be materialized before a uniform tape-only serializer
can run.  The committed dispatcher closeout appends its self-delimiting witness
to logical tape 2, after the live hit and its separating blank; logical tape 1
remains the consumed counter.  This makes the semantic target a function of
the physical source and therefore meets the determinism guardrail for the
repaired equivalence-output contract.

The checked serializer chain consumes this witness-materialized source
directly. The former standalone executable decoder and semantic-assembly
prototype had no consumer after that chain became the live implementation and
has been retired.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace EncRewriters
namespace BoundedLayoutRunner
namespace RunConfigEmitterCore
namespace GuardedEgress

open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

/-!
## Exact post-dispatch and witness-materialized sources
-/

/-- Complete semantic index for one guarded egress. -/
structure Index where
  description : MachineDescription
  sourceLayout : SimulatorLayout

def Index.finalLayout (i : Index) : SimulatorLayout :=
  SimulatorLayout.run i.description i.sourceLayout.stage i.sourceLayout

def Index.finalTape (i : Index) : Tape Bool :=
  i.finalLayout.config.tape

def Index.finalHit (i : Index) : Bool :=
  i.finalLayout.hit

def Index.finalState (i : Index) : Nat :=
  i.finalLayout.config.state

theorem Index.finalState_eq (i : Index) :
    i.finalState = i.finalLayout.config.state := by
  rfl

/-- Exhausted logical tape 1 before the branch witness is written. -/
def Index.consumedStageTape (i : Index) : Tape Bool :=
  loopDispatcherConsumedStageCounterTape i.sourceLayout.stage

/-! The definitions below deliberately alias the committed dispatcher
closeout API.  There is no second witness encoding in this module. -/

/-- Logical tape 2 after the dispatcher appends the branch witness. -/
def Index.doneWitnessTape (i : Index) : Tape Bool :=
  loopDispatcherDoneWitnessTape i.description i.sourceLayout

/-- Exact logical source of the uniform guarded serializer. -/
def Index.logicalTapes (i : Index) : List (Tape Bool) :=
  loopDispatcherDoneWitnessTapes i.description i.sourceLayout
/-- Canonical guarded physical source after branch-witness materialization. -/
def Index.source (i : Index) : Tape Bool :=
  encodedGuardedStructuredTapes i.logicalTapes

/-- Scratch width recovered from the unary marker block. -/
def Index.scratchWidth (i : Index) : Nat :=
  (RunConfigEmitterTheory.scratchWidthMarkers i.sourceLayout).length

/-- Exact four semantic fields assembled from the physical currencies. -/
def Index.fields (i : Index) : ExactCloseout.Fields :=
  EgressSemantics.fieldsFromParts
    (FieldDecomposition.metadata i.sourceLayout)
    i.finalState i.finalTape i.finalHit

/-- Exact right-shifted target expected by the final one-cell parking phase. -/
def Index.target (i : Index) : Tape Bool :=
  i.fields.rightScratchTape i.scratchWidth

theorem Index.fields_eq_semantic (i : Index) :
    i.fields = ExactCloseout.semanticFields i.description i.sourceLayout := by
  rw [Index.fields, i.finalState_eq]
  exact EgressSemantics.fieldsFromParts_semantic
    i.description i.sourceLayout

theorem Index.scratchWidth_eq_semantic (i : Index) :
    i.scratchWidth =
      FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
        i.sourceLayout := by
  exact EgressSemantics.scratchWidth_of_markers i.sourceLayout

theorem Index.target_eq_semantic (i : Index) :
    i.target =
      (ExactCloseout.semanticFields i.description i.sourceLayout).rightScratchTape
        (FixedDescriptionBoundedSimulatorPaddedEmitterScratchWidth_configRunner
          i.sourceLayout) := by
  rw [Index.target, i.fields_eq_semantic, i.scratchWidth_eq_semantic]

/-!
## Honest equivalence-output contract
-/

/-- The former all-equivalent-input/exact-tape contract is impossible even
for this target-functional source family, because an equivalent source can
carry arbitrarily much invisible far-edge padding. -/
theorem exactOutputConstruction_impossible (i : Index) :
    ¬ PipelineContracts.EquivInputExactOutputConstruction
        Index.source Index.target :=
  PipelineContracts.equivInputExactOutputConstruction_impossible
    i Index.source Index.target

/-- The final normalizer accepts every far-edge-padded representative of the
guarded source and produces a tape equivalent to the exact right-scratch
target.  Equivalence retains the exact normalized output and head split while
allowing the represented blank window to remain large enough for monotonicity. -/
def Spec (normalizer : MachineDescription) : Prop :=
  PipelineContracts.EquivInputEquivOutputSpec
    Index.source Index.target normalizer

def Construction : Prop :=
  PipelineContracts.EquivInputEquivOutputConstruction
    Index.source Index.target

end GuardedEgress
end RunConfigEmitterCore
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
