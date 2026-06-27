import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Construction.PhaseAdapters
import FoC.Computability.Compiler.Core.FixedDescriptionBoundedSimulator.Spec

set_option doc.verso true

/-!
# Bounded runner phase sequencing
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

def AcceptProjectionSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    (forall L : MachineDescription.DovetailLayout,
      projector.HaltsFromTapeEquiv
        (ParsedLayoutCheckedTape L)
        (MachineDescription.SimulatorLayout.tape
          (AcceptSimulatorLayout L))) ∧
    (forall L : MachineDescription.DovetailLayout,
      projector.ClosedFromTapeEquiv
        (ParsedLayoutCheckedTape L)
        (MachineDescription.SimulatorLayout.tape
          (AcceptSimulatorLayout L)))

def RejectProjectionSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    (forall L : MachineDescription.DovetailLayout,
      projector.HaltsFromTapeEquiv
        (ParsedLayoutTape L)
        (MachineDescription.SimulatorLayout.tape
          (RejectSimulatorLayout L))) ∧
    (forall L : MachineDescription.DovetailLayout,
      projector.ClosedFromTapeEquiv
        (ParsedLayoutTape L)
        (MachineDescription.SimulatorLayout.tape
          (RejectSimulatorLayout L)))

def SelectedProjectionPhaseFromOutputTape
    (runner : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine runner
    MachineDescription.ExactIdentityDescription Direction.left

theorem selectedProjectionOutputTape_move_left_equiv_simulator_tape
    {useAccept : Bool} {L : MachineDescription.DovetailLayout}
    {T : Tape Bool}
    (hT : Tape.Equiv T (SelectedProjectionOutputTape useAccept L)) :
    Tape.Equiv (Tape.move Direction.left T)
      (MachineDescription.SimulatorLayout.tape
        (SelectedProjectionSimulatorLayout useAccept L)) := by
  have hmove := Tape.Equiv.move hT Direction.left
  have htarget :
      Tape.move Direction.left (SelectedProjectionOutputTape useAccept L) =
        MachineDescription.SimulatorLayout.tape
          (SelectedProjectionSimulatorLayout useAccept L) := by
    have houtput :
        SelectedProjectionOutputTape useAccept L =
          Tape.move Direction.right
            (MachineDescription.SimulatorLayout.tape
              (SelectedProjectionSimulatorLayout useAccept L)) := by
      cases useAccept <;>
        rfl
    rw [houtput]
    exact simulatorLayoutTape_move_left_move_right
      (SelectedProjectionSimulatorLayout useAccept L)
  simpa [htarget] using hmove

theorem selectedProjectionPhaseFromOutputTape_forward
    {useAccept : Bool} {runner : MachineDescription}
    (hrunner : SelectedProjectionSpec useAccept runner)
    {Tin : Tape Bool} (L : MachineDescription.DovetailLayout)
    (hinput :
      Tape.Equiv (Tape.input (ParsedLayoutBits L)) Tin) :
    (SelectedProjectionPhaseFromOutputTape runner).HaltsFromTapeEquiv
      Tin
      (MachineDescription.SimulatorLayout.tape
        (SelectedProjectionSimulatorLayout useAccept L)) := by
  let identity := MachineDescription.ExactIdentityDescription
  have hid : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  rcases hrunner.right.left L with ⟨Tmid, hmid, hTmid⟩
  have hmidFromInput :
      runner.HaltsFromTapeEquiv Tin Tmid :=
    MachineDescription.HaltsFromTapeEquiv_of_input_equiv hinput hmid
  rcases hmidFromInput with ⟨Tactual, hactual, hTactualMid⟩
  have hTactual :
      Tape.Equiv Tactual (SelectedProjectionOutputTape useAccept L) :=
    Tape.Equiv.trans hTactualMid hTmid
  have hidentityReach :
      exists nB : Nat,
        identity.runConfig nB
            { state := identity.start
              tape := Tape.move Direction.left Tactual } =
          { state := identity.halt
            tape := Tape.move Direction.left Tactual } :=
    CommonGround.Identity.exactIdentityDescription_run_from_start
      (Tape.move Direction.left Tactual)
  have hseq :
      (SelectedProjectionPhaseFromOutputTape runner).HaltsFromTape
        Tin (Tape.move Direction.left Tactual) := by
    simpa [SelectedProjectionPhaseFromOutputTape, identity] using
      MachineDescription.seqSubroutine_haltsFromTape_of_haltsFromTape
        (A := runner) (B := identity) (handoffMove := Direction.left)
        hrunner.left hid hactual hidentityReach
  exact
    ⟨Tape.move Direction.left Tactual, hseq,
      selectedProjectionOutputTape_move_left_equiv_simulator_tape
        hTactual⟩

theorem selectedProjectionPhaseFromOutputTape_closed
    {useAccept : Bool} {runner : MachineDescription}
    (hrunner : SelectedProjectionSpec useAccept runner)
    {Tin : Tape Bool} (L : MachineDescription.DovetailLayout)
    (hinput :
      Tape.Equiv (Tape.input (ParsedLayoutBits L)) Tin) :
    (SelectedProjectionPhaseFromOutputTape runner).ClosedFromTapeEquiv
      Tin
      (MachineDescription.SimulatorLayout.tape
        (SelectedProjectionSimulatorLayout useAccept L)) := by
  intro T hhalt
  let identity := MachineDescription.ExactIdentityDescription
  have hid : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  have hready :
      (SelectedProjectionPhaseFromOutputTape runner).SubroutineReady := by
    simpa [SelectedProjectionPhaseFromOutputTape, identity] using
      MachineDescription.seqSubroutine_subroutineReady
        hrunner.left hid
  rcases
      selectedProjectionPhaseFromOutputTape_forward
        hrunner L hinput with
    ⟨Tactual, hactual, hTactual⟩
  have hT : T = Tactual :=
    MachineDescription.haltsFromTape_functional_of_haltTransitionFree
      hready.right hhalt hactual
  rw [hT]
  exact hTactual

theorem AcceptProjectionSpec_of_selected
    {runner : MachineDescription}
    (hrunner : SelectedProjectionSpec true runner) :
    AcceptProjectionSpec
      (SelectedProjectionPhaseFromOutputTape runner) := by
  constructor
  · have hid :
        MachineDescription.ExactIdentityDescription.SubroutineReady :=
      CommonGround.Identity.exactIdentityDescription_subroutineReady
    exact
      MachineDescription.seqSubroutine_subroutineReady
        hrunner.left hid
  constructor
  · intro L
    simpa [SelectedProjectionSimulatorLayout] using
      selectedProjectionPhaseFromOutputTape_forward
        hrunner L
        (Tape.Equiv.symm (checkedInputTape_equiv_input _))
  · intro L
    simpa [SelectedProjectionSimulatorLayout] using
      selectedProjectionPhaseFromOutputTape_closed
        hrunner L
        (Tape.Equiv.symm (checkedInputTape_equiv_input _))

theorem RejectProjectionSpec_of_selected
    {runner : MachineDescription}
    (hrunner : SelectedProjectionSpec false runner) :
    RejectProjectionSpec
      (SelectedProjectionPhaseFromOutputTape runner) := by
  constructor
  · have hid :
        MachineDescription.ExactIdentityDescription.SubroutineReady :=
      CommonGround.Identity.exactIdentityDescription_subroutineReady
    exact
      MachineDescription.seqSubroutine_subroutineReady
        hrunner.left hid
  constructor
  · intro L
    simpa [SelectedProjectionSimulatorLayout, ParsedLayoutTape] using
      selectedProjectionPhaseFromOutputTape_forward
        hrunner L (Tape.Equiv.refl _)
  · intro L
    simpa [SelectedProjectionSimulatorLayout, ParsedLayoutTape] using
      selectedProjectionPhaseFromOutputTape_closed
        hrunner L (Tape.Equiv.refl _)

def AcceptMergeSpec
    (accept merger : MachineDescription) : Prop :=
  merger.SubroutineReady ∧
    (forall L : MachineDescription.DovetailLayout,
      merger.HaltsWithTape
        (MachineDescription.SimulatorLayout.asBoolInput
          (MachineDescription.SimulatorLayout.run
            accept L.stage (AcceptSimulatorLayout L)))
        (ParsedLayoutTape (ConfigRunnerAfterAccept accept L))) ∧
    (forall L : MachineDescription.DovetailLayout,
     forall T : Tape Bool,
      merger.HaltsWithTape
        (MachineDescription.SimulatorLayout.asBoolInput
          (MachineDescription.SimulatorLayout.run
            accept L.stage (AcceptSimulatorLayout L))) T ->
        T = ParsedLayoutTape (ConfigRunnerAfterAccept accept L))

def RejectMergeSpec
    (reject merger : MachineDescription) : Prop :=
  merger.SubroutineReady ∧
    (forall L : MachineDescription.DovetailLayout,
      merger.HaltsWithTape
        (MachineDescription.SimulatorLayout.asBoolInput
          (MachineDescription.SimulatorLayout.run
            reject L.stage (RejectSimulatorLayout L)))
        (ParsedLayoutTape (ConfigRunnerAfterReject reject L))) ∧
    (forall L : MachineDescription.DovetailLayout,
     forall T : Tape Bool,
      merger.HaltsWithTape
        (MachineDescription.SimulatorLayout.asBoolInput
          (MachineDescription.SimulatorLayout.run
            reject L.stage (RejectSimulatorLayout L))) T ->
        T = ParsedLayoutTape (ConfigRunnerAfterReject reject L))

def AcceptMergeEquivSpec
    (accept merger : MachineDescription) : Prop :=
  merger.SubroutineReady ∧
    (forall L : MachineDescription.DovetailLayout,
      merger.HaltsFromTapeEquiv
        (MachineDescription.SimulatorLayout.tape
          (MachineDescription.SimulatorLayout.run
            accept L.stage (AcceptSimulatorLayout L)))
        (ParsedLayoutTape (ConfigRunnerAfterAccept accept L))) ∧
    (forall L : MachineDescription.DovetailLayout,
      merger.ClosedFromTapeEquiv
        (MachineDescription.SimulatorLayout.tape
          (MachineDescription.SimulatorLayout.run
            accept L.stage (AcceptSimulatorLayout L)))
        (ParsedLayoutTape (ConfigRunnerAfterAccept accept L)))

def RejectMergeEquivSpec
    (reject merger : MachineDescription) : Prop :=
  merger.SubroutineReady ∧
    (forall L : MachineDescription.DovetailLayout,
      merger.HaltsFromTapeEquiv
        (MachineDescription.SimulatorLayout.tape
          (MachineDescription.SimulatorLayout.run
            reject L.stage (RejectSimulatorLayout L)))
        (ParsedLayoutTape (ConfigRunnerAfterReject reject L))) ∧
    (forall L : MachineDescription.DovetailLayout,
      merger.ClosedFromTapeEquiv
        (MachineDescription.SimulatorLayout.tape
          (MachineDescription.SimulatorLayout.run
            reject L.stage (RejectSimulatorLayout L)))
        (ParsedLayoutTape (ConfigRunnerAfterReject reject L)))

def SelectedMergeEquivOutputTape
    (useAccept : Bool)
    (S : MachineDescription.SimulatorLayout)
    (L : MachineDescription.DovetailLayout) : Tape Bool :=
  Tape.input
    (MachineDescription.encodeCodeWordAsInput
      (SelectedMergeOutputCode useAccept S L))

def SelectedMergeEquivSpec
    (useAccept : Bool)
    (merger : MachineDescription) : Prop :=
  merger.SubroutineReady ∧
    (forall S : MachineDescription.SimulatorLayout,
     forall L : MachineDescription.DovetailLayout,
      MachineDescription.decodeCodeWordAsInput S.input =
        some (MachineDescription.DovetailLayout.encode L) ->
      merger.HaltsFromTapeEquiv
        (MachineDescription.SimulatorLayout.tape S)
        (SelectedMergeEquivOutputTape useAccept S L)) ∧
    forall S : MachineDescription.SimulatorLayout,
    forall L : MachineDescription.DovetailLayout,
      MachineDescription.decodeCodeWordAsInput S.input =
        some (MachineDescription.DovetailLayout.encode L) ->
      merger.ClosedFromTapeEquiv
        (MachineDescription.SimulatorLayout.tape S)
        (SelectedMergeEquivOutputTape useAccept S L)

def SelectedMergeEquivConstruction : Prop :=
  forall useAccept : Bool,
    exists merger : MachineDescription,
      SelectedMergeEquivSpec useAccept merger

theorem selectedMergeEquivOutputTape_accept_run
    (accept : MachineDescription) (L : MachineDescription.DovetailLayout) :
    SelectedMergeEquivOutputTape true
        (MachineDescription.SimulatorLayout.run
          accept L.stage (AcceptSimulatorLayout L)) L =
      ParsedLayoutTape (ConfigRunnerAfterAccept accept L) := by
  simp [SelectedMergeEquivOutputTape, SelectedMergeOutputCode,
    ParsedLayoutTape, ParsedLayoutBits, ConfigRunnerAfterAccept,
    AcceptSimulatorLayout, MachineDescription.SimulatorLayout.run]

theorem selectedMergeEquivOutputTape_reject_run
    (reject : MachineDescription) (L : MachineDescription.DovetailLayout) :
    SelectedMergeEquivOutputTape false
        (MachineDescription.SimulatorLayout.run
          reject L.stage (RejectSimulatorLayout L)) L =
      ParsedLayoutTape (ConfigRunnerAfterReject reject L) := by
  simp [SelectedMergeEquivOutputTape, SelectedMergeOutputCode,
    ParsedLayoutTape, ParsedLayoutBits, ConfigRunnerAfterReject,
    RejectSimulatorLayout, MachineDescription.SimulatorLayout.run]

theorem acceptMergeEquivSpec_of_selected
    {accept merger : MachineDescription}
    (h : SelectedMergeEquivSpec true merger) :
    AcceptMergeEquivSpec accept merger := by
  constructor
  · exact h.left
  constructor
  · intro L
    have hinput :
        MachineDescription.decodeCodeWordAsInput
            (MachineDescription.SimulatorLayout.run
              accept L.stage (AcceptSimulatorLayout L)).input =
          some (MachineDescription.DovetailLayout.encode L) := by
      simpa [MachineDescription.SimulatorLayout.run, AcceptSimulatorLayout]
        using decodeCodeWordAsInput_parsedLayoutBits L
    have hrun := h.right.left
      (MachineDescription.SimulatorLayout.run
        accept L.stage (AcceptSimulatorLayout L)) L hinput
    simpa [selectedMergeEquivOutputTape_accept_run accept L] using hrun
  · intro L T hhalt
    have hinput :
        MachineDescription.decodeCodeWordAsInput
            (MachineDescription.SimulatorLayout.run
              accept L.stage (AcceptSimulatorLayout L)).input =
          some (MachineDescription.DovetailLayout.encode L) := by
      simpa [MachineDescription.SimulatorLayout.run, AcceptSimulatorLayout]
        using decodeCodeWordAsInput_parsedLayoutBits L
    have hclosed := h.right.right
      (MachineDescription.SimulatorLayout.run
        accept L.stage (AcceptSimulatorLayout L)) L hinput
    simpa [selectedMergeEquivOutputTape_accept_run accept L] using
      hclosed T hhalt

theorem rejectMergeEquivSpec_of_selected
    {reject merger : MachineDescription}
    (h : SelectedMergeEquivSpec false merger) :
    RejectMergeEquivSpec reject merger := by
  constructor
  · exact h.left
  constructor
  · intro L
    have hinput :
        MachineDescription.decodeCodeWordAsInput
            (MachineDescription.SimulatorLayout.run
              reject L.stage (RejectSimulatorLayout L)).input =
          some (MachineDescription.DovetailLayout.encode L) := by
      simpa [MachineDescription.SimulatorLayout.run, RejectSimulatorLayout]
        using decodeCodeWordAsInput_parsedLayoutBits L
    have hrun := h.right.left
      (MachineDescription.SimulatorLayout.run
        reject L.stage (RejectSimulatorLayout L)) L hinput
    simpa [selectedMergeEquivOutputTape_reject_run reject L] using hrun
  · intro L T hhalt
    have hinput :
        MachineDescription.decodeCodeWordAsInput
            (MachineDescription.SimulatorLayout.run
              reject L.stage (RejectSimulatorLayout L)).input =
          some (MachineDescription.DovetailLayout.encode L) := by
      simpa [MachineDescription.SimulatorLayout.run, RejectSimulatorLayout]
        using decodeCodeWordAsInput_parsedLayoutBits L
    have hclosed := h.right.right
      (MachineDescription.SimulatorLayout.run
        reject L.stage (RejectSimulatorLayout L)) L hinput
    simpa [selectedMergeEquivOutputTape_reject_run reject L] using
      hclosed T hhalt

theorem acceptMergeEquivSpec_of_exact
    {accept merger : MachineDescription}
    (h : AcceptMergeSpec accept merger) :
    AcceptMergeEquivSpec accept merger := by
  constructor
  · exact h.left
  constructor
  · intro L
    have hrun :
        merger.HaltsFromTape
          (MachineDescription.SimulatorLayout.tape
            (MachineDescription.SimulatorLayout.run
              accept L.stage (AcceptSimulatorLayout L)))
          (ParsedLayoutTape (ConfigRunnerAfterAccept accept L)) := by
      simpa [MachineDescription.SimulatorLayout.tape] using h.right.left L
    exact MachineDescription.HaltsFromTape.toEquiv hrun
  · intro L T hhalt
    have hhaltWith :
        merger.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput
            (MachineDescription.SimulatorLayout.run
              accept L.stage (AcceptSimulatorLayout L))) T := by
      simpa [MachineDescription.SimulatorLayout.tape,
        MachineDescription.HaltsWithTape, MachineDescription.HaltsFromTape,
        MachineDescription.HaltsWithTapeIn,
        MachineDescription.HaltsFromTapeIn,
        MachineDescription.initial] using hhalt
    rw [h.right.right L T hhaltWith]
    exact Tape.Equiv.refl _

theorem rejectMergeEquivSpec_of_exact
    {reject merger : MachineDescription}
    (h : RejectMergeSpec reject merger) :
    RejectMergeEquivSpec reject merger := by
  constructor
  · exact h.left
  constructor
  · intro L
    have hrun :
        merger.HaltsFromTape
          (MachineDescription.SimulatorLayout.tape
            (MachineDescription.SimulatorLayout.run
              reject L.stage (RejectSimulatorLayout L)))
          (ParsedLayoutTape (ConfigRunnerAfterReject reject L)) := by
      simpa [MachineDescription.SimulatorLayout.tape] using h.right.left L
    exact MachineDescription.HaltsFromTape.toEquiv hrun
  · intro L T hhalt
    have hhaltWith :
        merger.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput
            (MachineDescription.SimulatorLayout.run
              reject L.stage (RejectSimulatorLayout L))) T := by
      simpa [MachineDescription.SimulatorLayout.tape,
        MachineDescription.HaltsWithTape, MachineDescription.HaltsFromTape,
        MachineDescription.HaltsWithTapeIn,
        MachineDescription.HaltsFromTapeIn,
        MachineDescription.initial] using hhalt
    rw [h.right.right L T hhaltWith]
    exact Tape.Equiv.refl _

def ConfigRunnerPhaseConstructionData
    (accept reject : MachineDescription) : Prop :=
  exists acceptProject acceptSim acceptMerge
    rejectProject rejectSim rejectMerge : MachineDescription,
    AcceptProjectionSpec acceptProject ∧
      FixedDescriptionBoundedSimulatorCanonicalSpec accept acceptSim ∧
      AcceptMergeSpec accept acceptMerge ∧
      RejectProjectionSpec rejectProject ∧
      FixedDescriptionBoundedSimulatorCanonicalSpec reject rejectSim ∧
      RejectMergeSpec reject rejectMerge

def ConfigRunnerPhaseConstruction : Prop :=
  forall accept reject : MachineDescription,
    ConfigRunnerPhaseConstructionData accept reject

def ConfigRunnerPhaseEquivConstructionData
    (accept reject : MachineDescription) : Prop :=
  exists acceptProject acceptSim acceptMerge
    rejectProject rejectSim rejectMerge : MachineDescription,
    AcceptProjectionSpec acceptProject ∧
      FixedDescriptionBoundedSimulatorEquivSpec accept acceptSim ∧
      AcceptMergeEquivSpec accept acceptMerge ∧
      RejectProjectionSpec rejectProject ∧
      FixedDescriptionBoundedSimulatorEquivSpec reject rejectSim ∧
      RejectMergeEquivSpec reject rejectMerge

def ConfigRunnerPhaseEquivConstruction : Prop :=
  forall accept reject : MachineDescription,
    ConfigRunnerPhaseEquivConstructionData accept reject

theorem configRunnerPhaseEquivConstruction_of_exact
    (h : ConfigRunnerPhaseConstruction) :
    ConfigRunnerPhaseEquivConstruction := by
  intro accept reject
  rcases h accept reject with
    ⟨acceptProject, acceptSim, acceptMerge,
      rejectProject, rejectSim, rejectMerge,
      hacceptProject, hacceptSim, hacceptMerge,
      hrejectProject, hrejectSim, hrejectMerge⟩
  exact
    ⟨acceptProject, acceptSim, acceptMerge,
      rejectProject, rejectSim, rejectMerge,
      hacceptProject,
      fixedDescriptionBoundedSimulatorEquivSpec_of_canonicalSpec
        hacceptSim,
      acceptMergeEquivSpec_of_exact hacceptMerge,
      hrejectProject,
      fixedDescriptionBoundedSimulatorEquivSpec_of_canonicalSpec
        hrejectSim,
      rejectMergeEquivSpec_of_exact hrejectMerge⟩

def ConfigRunnerPrimitiveClosedHandoffConstruction : Prop :=
  exists acceptProject acceptMerge
    rejectProject rejectMerge : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      AcceptProjectionPrimitive
      acceptProject tapeCodePrimitiveCodeWordHandoffMove ∧
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      AcceptMergePrimitive
      acceptMerge tapeCodePrimitiveCodeWordHandoffMove ∧
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      RejectProjectionPrimitive
      rejectProject tapeCodePrimitiveCodeWordHandoffMove ∧
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      RejectMergePrimitive
      rejectMerge tapeCodePrimitiveCodeWordHandoffMove

def AcceptProjectionPrimitiveClosedHandoffConstruction : Prop :=
  exists closed : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      AcceptProjectionPrimitive
      closed tapeCodePrimitiveCodeWordHandoffMove

def AcceptMergePrimitiveClosedHandoffConstruction : Prop :=
  exists closed : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      AcceptMergePrimitive
      closed tapeCodePrimitiveCodeWordHandoffMove

def RejectProjectionPrimitiveClosedHandoffConstruction : Prop :=
  exists closed : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      RejectProjectionPrimitive
      closed tapeCodePrimitiveCodeWordHandoffMove

def RejectMergePrimitiveClosedHandoffConstruction : Prop :=
  exists closed : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      RejectMergePrimitive
      closed tapeCodePrimitiveCodeWordHandoffMove

def SelectedProjectionPrimitiveClosedHandoffConstruction : Prop :=
  forall useAccept : Bool,
    exists closed : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (SelectedProjectionPrimitive useAccept)
        closed tapeCodePrimitiveCodeWordHandoffMove

def SelectedMergePrimitiveClosedHandoffConstruction : Prop :=
  forall useAccept : Bool,
    exists closed : MachineDescription,
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        (SelectedMergePrimitive useAccept)
        closed tapeCodePrimitiveCodeWordHandoffMove

theorem acceptProjectionPrimitiveClosedHandoffConstruction_of_selected
    (h : SelectedProjectionPrimitiveClosedHandoffConstruction) :
    AcceptProjectionPrimitiveClosedHandoffConstruction := by
  rcases h true with ⟨closed, hclosed⟩
  refine ⟨closed, ?_⟩
  exact
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_congr
      (P := SelectedProjectionPrimitive true)
      (Q := AcceptProjectionPrimitive)
      (D := closed)
      (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
      (by
        intro code
        rfl)
      hclosed

theorem rejectProjectionPrimitiveClosedHandoffConstruction_of_selected
    (h : SelectedProjectionPrimitiveClosedHandoffConstruction) :
    RejectProjectionPrimitiveClosedHandoffConstruction := by
  rcases h false with ⟨closed, hclosed⟩
  refine ⟨closed, ?_⟩
  exact
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_congr
      (P := SelectedProjectionPrimitive false)
      (Q := RejectProjectionPrimitive)
      (D := closed)
      (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
      (by
        intro code
        rfl)
      hclosed

theorem acceptMergePrimitiveClosedHandoffConstruction_of_selected
    (h : SelectedMergePrimitiveClosedHandoffConstruction) :
    AcceptMergePrimitiveClosedHandoffConstruction := by
  rcases h true with ⟨closed, hclosed⟩
  refine ⟨closed, ?_⟩
  exact
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_congr
      (P := SelectedMergePrimitive true)
      (Q := AcceptMergePrimitive)
      (D := closed)
      (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
      (by
        intro code
        rfl)
      hclosed

theorem rejectMergePrimitiveClosedHandoffConstruction_of_selected
    (h : SelectedMergePrimitiveClosedHandoffConstruction) :
    RejectMergePrimitiveClosedHandoffConstruction := by
  rcases h false with ⟨closed, hclosed⟩
  refine ⟨closed, ?_⟩
  exact
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_congr
      (P := SelectedMergePrimitive false)
      (Q := RejectMergePrimitive)
      (D := closed)
      (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
      (by
        intro code
        rfl)
      hclosed

theorem configRunnerPrimitiveClosedHandoffConstruction_of_parts
    (hacceptProject : AcceptProjectionPrimitiveClosedHandoffConstruction)
    (hacceptMerge : AcceptMergePrimitiveClosedHandoffConstruction)
    (hrejectProject : RejectProjectionPrimitiveClosedHandoffConstruction)
    (hrejectMerge : RejectMergePrimitiveClosedHandoffConstruction) :
    ConfigRunnerPrimitiveClosedHandoffConstruction := by
  rcases hacceptProject with ⟨acceptProject, hacceptProject⟩
  rcases hacceptMerge with ⟨acceptMerge, hacceptMerge⟩
  rcases hrejectProject with ⟨rejectProject, hrejectProject⟩
  rcases hrejectMerge with ⟨rejectMerge, hrejectMerge⟩
  exact
    ⟨acceptProject, acceptMerge, rejectProject, rejectMerge,
      hacceptProject, hacceptMerge, hrejectProject, hrejectMerge⟩

theorem AcceptProjectionSpec_of_closedHandoff
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        AcceptProjectionPrimitive
        closed tapeCodePrimitiveCodeWordHandoffMove) :
    AcceptProjectionSpec
      (TapeCodeCheckedPhaseFromClosedHandoff closed) := by
  constructor
  · exact TapeCodeCheckedPhaseFromClosedHandoff_subroutineReady hclosed
  constructor
  · intro L
    simpa [ParsedLayoutCheckedTape,
      MachineDescription.SimulatorLayout.tape,
      MachineDescription.SimulatorLayout.asBoolInput] using
      TapeCodeCheckedPhaseFromClosedHandoff_forward
        hclosed (AcceptProjectionPrimitive_encode L)
  · intro L T hhalt
    have hhalt' :
        (TapeCodeCheckedPhaseFromClosedHandoff closed).HaltsFromTape
          (checkedInputTape (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailLayout.encode L))) T := by
      simpa [ParsedLayoutCheckedTape] using hhalt
    have hT :=
      TapeCodeCheckedPhaseFromClosedHandoff_closed_equiv
        hclosed (AcceptProjectionPrimitive_encode L) hhalt'
    simpa [MachineDescription.SimulatorLayout.tape,
      MachineDescription.SimulatorLayout.asBoolInput] using hT

theorem RejectProjectionSpec_of_closedHandoff
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        RejectProjectionPrimitive
        closed tapeCodePrimitiveCodeWordHandoffMove) :
    RejectProjectionSpec
      (TapeCodeExactPhaseFromClosedHandoff closed) := by
  constructor
  · exact TapeCodeExactPhaseFromClosedHandoff_subroutineReady hclosed
  constructor
  · intro L
    have hrun :
        (TapeCodeExactPhaseFromClosedHandoff closed).HaltsFromTape
          (ParsedLayoutTape L)
          (MachineDescription.SimulatorLayout.tape
            (RejectSimulatorLayout L)) := by
      simpa [ParsedLayoutTape, ParsedLayoutBits,
        MachineDescription.SimulatorLayout.tape,
        MachineDescription.SimulatorLayout.asBoolInput] using
        TapeCodeExactPhaseFromClosedHandoff_forward
          hclosed (RejectProjectionPrimitive_encode L)
    exact MachineDescription.HaltsFromTape.toEquiv hrun
  · intro L T hhalt
    have hhalt' :
        (TapeCodeExactPhaseFromClosedHandoff closed).HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailLayout.encode L)) T := by
      simpa [ParsedLayoutTape, ParsedLayoutBits] using hhalt
    have hT :=
      TapeCodeExactPhaseFromClosedHandoff_closed_eq
        hclosed (RejectProjectionPrimitive_encode L) hhalt'
    rw [hT]
    exact Tape.Equiv.refl _

theorem AcceptMergeSpec_of_closedHandoff
    (accept : MachineDescription)
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        AcceptMergePrimitive
        closed tapeCodePrimitiveCodeWordHandoffMove) :
    AcceptMergeSpec accept
      (TapeCodeExactPhaseFromClosedHandoff closed) := by
  constructor
  · exact TapeCodeExactPhaseFromClosedHandoff_subroutineReady hclosed
  constructor
  · intro L
    simpa [MachineDescription.SimulatorLayout.asBoolInput,
      ParsedLayoutTape, ParsedLayoutBits] using
      TapeCodeExactPhaseFromClosedHandoff_forward
        hclosed (AcceptMergePrimitive_encode_run accept L)
  · intro L T hhalt
    have hhalt' :
        (TapeCodeExactPhaseFromClosedHandoff closed).HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.SimulatorLayout.encode
              (MachineDescription.SimulatorLayout.run
                accept L.stage (AcceptSimulatorLayout L)))) T := by
      simpa [MachineDescription.SimulatorLayout.asBoolInput] using hhalt
    have hT :=
      TapeCodeExactPhaseFromClosedHandoff_closed_eq
        hclosed (AcceptMergePrimitive_encode_run accept L) hhalt'
    simpa [ParsedLayoutTape, ParsedLayoutBits] using hT

theorem RejectMergeSpec_of_closedHandoff
    (reject : MachineDescription)
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        RejectMergePrimitive
        closed tapeCodePrimitiveCodeWordHandoffMove) :
    RejectMergeSpec reject
      (TapeCodeExactPhaseFromClosedHandoff closed) := by
  constructor
  · exact TapeCodeExactPhaseFromClosedHandoff_subroutineReady hclosed
  constructor
  · intro L
    simpa [MachineDescription.SimulatorLayout.asBoolInput,
      ParsedLayoutTape, ParsedLayoutBits] using
      TapeCodeExactPhaseFromClosedHandoff_forward
        hclosed (RejectMergePrimitive_encode_run reject L)
  · intro L T hhalt
    have hhalt' :
        (TapeCodeExactPhaseFromClosedHandoff closed).HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.SimulatorLayout.encode
              (MachineDescription.SimulatorLayout.run
                reject L.stage (RejectSimulatorLayout L)))) T := by
      simpa [MachineDescription.SimulatorLayout.asBoolInput] using hhalt
    have hT :=
      TapeCodeExactPhaseFromClosedHandoff_closed_eq
        hclosed (RejectMergePrimitive_encode_run reject L) hhalt'
    simpa [ParsedLayoutTape, ParsedLayoutBits] using hT

theorem configRunnerPhaseConstruction_of_primitiveClosedHandoff
    (hsim : FixedDescriptionBoundedSimulatorCanonicalConstruction)
    (hprimitive : ConfigRunnerPrimitiveClosedHandoffConstruction) :
    ConfigRunnerPhaseConstruction := by
  intro accept reject
  rcases hprimitive with
    ⟨acceptProject, acceptMerge, rejectProject, rejectMerge,
      hacceptProject, hacceptMerge, hrejectProject, hrejectMerge⟩
  rcases hsim accept with ⟨acceptSim, hacceptSim⟩
  rcases hsim reject with ⟨rejectSim, hrejectSim⟩
  exact
    ⟨TapeCodeExactPhaseFromClosedHandoff acceptProject,
      acceptSim,
      TapeCodeExactPhaseFromClosedHandoff acceptMerge,
      TapeCodeExactPhaseFromClosedHandoff rejectProject,
      rejectSim,
      TapeCodeExactPhaseFromClosedHandoff rejectMerge,
      AcceptProjectionSpec_of_closedHandoff hacceptProject,
      hacceptSim,
      AcceptMergeSpec_of_closedHandoff accept hacceptMerge,
      RejectProjectionSpec_of_closedHandoff hrejectProject,
      hrejectSim,
      RejectMergeSpec_of_closedHandoff reject hrejectMerge⟩

theorem fixedDescriptionBoundedSimulatorEquivSpec_closedFromTapeEquiv
    {D sim : MachineDescription}
    (hsim : FixedDescriptionBoundedSimulatorEquivSpec D sim)
    (L : MachineDescription.SimulatorLayout) :
    sim.ClosedFromTapeEquiv
      (MachineDescription.SimulatorLayout.tape L)
      (FixedDescriptionBoundedSimulatorCanonicalOutputTape D L) := by
  intro T hhalt
  rcases hhalt with ⟨n, hn⟩
  have hwith :
      sim.HaltsWithTape (FixedDescriptionBoundedSimulatorInput L) T := by
    exact ⟨n, by
      simpa [MachineDescription.HaltsWithTapeIn,
        MachineDescription.HaltsFromTapeIn,
        MachineDescription.initial,
        FixedDescriptionBoundedSimulatorInput,
        MachineDescription.SimulatorLayout.tape] using hn⟩
  exact hsim.right.right L T hwith

structure PhaseChainSpec
    {ι : Type} (phase : MachineDescription)
    (input output : ι -> Tape Bool) : Prop where
  ready : phase.SubroutineReady
  forward :
    forall i : ι, phase.HaltsFromTapeEquiv (input i) (output i)
  closed :
    forall i : ι, phase.ClosedFromTapeEquiv (input i) (output i)

namespace PhaseChain

def append (A B : MachineDescription) : MachineDescription :=
  SeqViaCanonical A B

theorem forward
    {ι : Type} {A B : MachineDescription}
    {input middle inputB output : ι -> Tape Bool}
    (hA : PhaseChainSpec A input middle)
    (hB : PhaseChainSpec B inputB output)
    (hbridge :
      forall i : ι,
        Tape.Equiv
          (Tape.move Direction.left (Tape.move Direction.right (middle i)))
          (inputB i))
    (i : ι) :
    (append A B).HaltsFromTapeEquiv (input i) (output i) :=
  SeqViaCanonical_haltsFromTapeEquiv_of_tapeEquiv
    hA.ready hB.ready (hA.forward i) (hbridge i) (hB.forward i)

theorem closed
    {ι : Type} {A B : MachineDescription}
    {input middle inputB output : ι -> Tape Bool}
    (hA : PhaseChainSpec A input middle)
    (hB : PhaseChainSpec B inputB output)
    (hbridge :
      forall i : ι,
        Tape.Equiv
          (Tape.move Direction.left (Tape.move Direction.right (middle i)))
          (inputB i))
    (i : ι) :
    (append A B).ClosedFromTapeEquiv (input i) (output i) := by
  intro T hhalt
  rcases SeqViaCanonical_haltsFromTape_inv
      hA.ready hB.ready hhalt with
    ⟨Tmid, hArun, hBrun⟩
  have hmid : Tape.Equiv Tmid (middle i) :=
    hA.closed i Tmid hArun
  have hbridgeActual :
      Tape.Equiv
        (Tape.move Direction.left (Tape.move Direction.right Tmid))
        (inputB i) := by
    exact
      Tape.Equiv.trans
        (Tape.Equiv.move
          (Tape.Equiv.move hmid Direction.right) Direction.left)
        (hbridge i)
  rcases
      MachineDescription.HaltsFromTapeEquiv_of_input_equiv
        (D := B)
        hbridgeActual hBrun with
    ⟨Tactual, hBactual, hTactual⟩
  have hout : Tape.Equiv Tactual (output i) :=
    hB.closed i Tactual hBactual
  exact Tape.Equiv.trans (Tape.Equiv.symm hTactual) hout

theorem spec
    {ι : Type} {A B : MachineDescription}
    {input middle inputB output : ι -> Tape Bool}
    (hA : PhaseChainSpec A input middle)
    (hB : PhaseChainSpec B inputB output)
    (hbridge :
      forall i : ι,
        Tape.Equiv
          (Tape.move Direction.left (Tape.move Direction.right (middle i)))
          (inputB i)) :
    PhaseChainSpec (append A B) input output := by
  constructor
  · exact SeqViaCanonical_subroutineReady hA.ready hB.ready
  · exact forward hA hB hbridge
  · exact closed hA hB hbridge

end PhaseChain

def ConfigRunnerPhaseRunner
    (acceptProject acceptSim acceptMerge
      rejectProject rejectSim rejectMerge : MachineDescription) :
    MachineDescription :=
  SeqViaCanonical
    (SeqViaCanonical
      (SeqViaCanonical
        (SeqViaCanonical
          (SeqViaCanonical acceptProject acceptSim)
          acceptMerge)
        rejectProject)
      rejectSim)
    rejectMerge

theorem configRunnerPhaseRunner_spec
    {accept reject : MachineDescription}
    {acceptProject acceptSim acceptMerge
      rejectProject rejectSim rejectMerge : MachineDescription}
    (hacceptProject : AcceptProjectionSpec acceptProject)
    (hacceptSim :
      FixedDescriptionBoundedSimulatorEquivSpec accept acceptSim)
    (hacceptMerge : AcceptMergeEquivSpec accept acceptMerge)
    (hrejectProject : RejectProjectionSpec rejectProject)
    (hrejectSim :
      FixedDescriptionBoundedSimulatorEquivSpec reject rejectSim)
    (hrejectMerge : RejectMergeEquivSpec reject rejectMerge) :
    AcceptRejectConfigRunnerSpec accept reject
      (ConfigRunnerPhaseRunner
        acceptProject acceptSim acceptMerge
        rejectProject rejectSim rejectMerge) := by
  let acceptInput : MachineDescription.DovetailLayout -> Tape Bool :=
    fun L => ParsedLayoutCheckedTape L
  let acceptProjected : MachineDescription.DovetailLayout -> Tape Bool :=
    fun L =>
      MachineDescription.SimulatorLayout.tape
        (AcceptSimulatorLayout L)
  let acceptSimulated : MachineDescription.DovetailLayout -> Tape Bool :=
    fun L =>
      MachineDescription.SimulatorLayout.tape
        (MachineDescription.SimulatorLayout.run
          accept L.stage (AcceptSimulatorLayout L))
  let afterAccept : MachineDescription.DovetailLayout -> Tape Bool :=
    fun L => ParsedLayoutTape (ConfigRunnerAfterAccept accept L)
  let rejectProjected : MachineDescription.DovetailLayout -> Tape Bool :=
    fun L =>
      MachineDescription.SimulatorLayout.tape
        (RejectSimulatorLayout (ConfigRunnerAfterAccept accept L))
  let rejectSimulated : MachineDescription.DovetailLayout -> Tape Bool :=
    fun L =>
      MachineDescription.SimulatorLayout.tape
        (MachineDescription.SimulatorLayout.run
          reject (ConfigRunnerAfterAccept accept L).stage
          (RejectSimulatorLayout (ConfigRunnerAfterAccept accept L)))
  let runnerOutput : MachineDescription.DovetailLayout -> Tape Bool :=
    fun L => ConfigRunnerOutputTape accept reject L
  have hAcceptProjectSpec :
      PhaseChainSpec acceptProject acceptInput acceptProjected := by
    constructor
    · exact hacceptProject.left
    · intro L
      simpa [acceptInput, acceptProjected] using
        hacceptProject.right.left L
    · intro L
      simpa [acceptInput, acceptProjected] using
        hacceptProject.right.right L
  have hAcceptSimSpec :
      PhaseChainSpec acceptSim acceptProjected acceptSimulated := by
    constructor
    · exact hacceptSim.left
    · intro L
      simpa [acceptProjected, acceptSimulated,
        FixedDescriptionBoundedSimulatorCanonicalOutputTape,
        AcceptSimulatorLayout] using
        hacceptSim.haltsFromTapeEquiv (AcceptSimulatorLayout L)
    · intro L
      simpa [acceptProjected, acceptSimulated,
        FixedDescriptionBoundedSimulatorCanonicalOutputTape,
        AcceptSimulatorLayout] using
        fixedDescriptionBoundedSimulatorEquivSpec_closedFromTapeEquiv
          hacceptSim (AcceptSimulatorLayout L)
  have hAcceptMergeSpec :
      PhaseChainSpec acceptMerge acceptSimulated afterAccept := by
    constructor
    · exact hacceptMerge.left
    · intro L
      simpa [acceptSimulated, afterAccept] using
        hacceptMerge.right.left L
    · intro L
      simpa [acceptSimulated, afterAccept] using
        hacceptMerge.right.right L
  have hRejectProjectSpec :
      PhaseChainSpec rejectProject afterAccept rejectProjected := by
    constructor
    · exact hrejectProject.left
    · intro L
      simpa [afterAccept, rejectProjected] using
        hrejectProject.right.left (ConfigRunnerAfterAccept accept L)
    · intro L
      simpa [afterAccept, rejectProjected] using
        hrejectProject.right.right (ConfigRunnerAfterAccept accept L)
  have hRejectSimSpec :
      PhaseChainSpec rejectSim rejectProjected rejectSimulated := by
    constructor
    · exact hrejectSim.left
    · intro L
      simpa [rejectProjected, rejectSimulated,
        FixedDescriptionBoundedSimulatorCanonicalOutputTape] using
        hrejectSim.haltsFromTapeEquiv
          (RejectSimulatorLayout (ConfigRunnerAfterAccept accept L))
    · intro L
      simpa [rejectProjected, rejectSimulated,
        FixedDescriptionBoundedSimulatorCanonicalOutputTape] using
        fixedDescriptionBoundedSimulatorEquivSpec_closedFromTapeEquiv
          hrejectSim
          (RejectSimulatorLayout (ConfigRunnerAfterAccept accept L))
  have hRejectMergeSpec :
      PhaseChainSpec rejectMerge rejectSimulated runnerOutput := by
    constructor
    · exact hrejectMerge.left
    · intro L
      simpa [rejectSimulated, runnerOutput, ConfigRunnerOutputTape,
        ConfigRunnerAfterReject_afterAccept] using
        hrejectMerge.right.left (ConfigRunnerAfterAccept accept L)
    · intro L
      simpa [rejectSimulated, runnerOutput, ConfigRunnerOutputTape,
        ConfigRunnerAfterReject_afterAccept] using
        hrejectMerge.right.right (ConfigRunnerAfterAccept accept L)
  have hAcceptProjectBridge :
      forall L : MachineDescription.DovetailLayout,
        Tape.Equiv
          (Tape.move Direction.left
            (Tape.move Direction.right (acceptProjected L)))
          (acceptProjected L) := by
    intro L
    rw [show
        Tape.move Direction.left
            (Tape.move Direction.right (acceptProjected L)) =
          acceptProjected L by
        simpa [acceptProjected] using
          simulatorLayoutTape_move_left_move_right
            (AcceptSimulatorLayout L)]
    exact Tape.Equiv.refl _
  have hAcceptSimBridge :
      forall L : MachineDescription.DovetailLayout,
        Tape.Equiv
          (Tape.move Direction.left
            (Tape.move Direction.right (acceptSimulated L)))
          (acceptSimulated L) := by
    intro L
    rw [show
        Tape.move Direction.left
            (Tape.move Direction.right (acceptSimulated L)) =
          acceptSimulated L by
        simpa [acceptSimulated] using
          simulatorLayoutTape_move_left_move_right
            (MachineDescription.SimulatorLayout.run
              accept L.stage (AcceptSimulatorLayout L))]
    exact Tape.Equiv.refl _
  have hAcceptMergeBridge :
      forall L : MachineDescription.DovetailLayout,
        Tape.Equiv
          (Tape.move Direction.left
            (Tape.move Direction.right (afterAccept L)))
          (afterAccept L) := by
    intro L
    rw [show
        Tape.move Direction.left
            (Tape.move Direction.right (afterAccept L)) =
          afterAccept L by
        simpa [afterAccept] using
          parsedLayoutTape_move_left_move_right_configRunner
            (ConfigRunnerAfterAccept accept L)]
    exact Tape.Equiv.refl _
  have hRejectProjectBridge :
      forall L : MachineDescription.DovetailLayout,
        Tape.Equiv
          (Tape.move Direction.left
            (Tape.move Direction.right (rejectProjected L)))
          (rejectProjected L) := by
    intro L
    rw [show
        Tape.move Direction.left
            (Tape.move Direction.right (rejectProjected L)) =
          rejectProjected L by
        simpa [rejectProjected] using
          simulatorLayoutTape_move_left_move_right
            (RejectSimulatorLayout (ConfigRunnerAfterAccept accept L))]
    exact Tape.Equiv.refl _
  have hRejectSimBridge :
      forall L : MachineDescription.DovetailLayout,
        Tape.Equiv
          (Tape.move Direction.left
            (Tape.move Direction.right (rejectSimulated L)))
          (rejectSimulated L) := by
    intro L
    rw [show
        Tape.move Direction.left
            (Tape.move Direction.right (rejectSimulated L)) =
          rejectSimulated L by
        simpa [rejectSimulated] using
          simulatorLayoutTape_move_left_move_right
            (MachineDescription.SimulatorLayout.run
              reject (ConfigRunnerAfterAccept accept L).stage
              (RejectSimulatorLayout (ConfigRunnerAfterAccept accept L)))]
    exact Tape.Equiv.refl _
  have hAPASpec :
      PhaseChainSpec
        (PhaseChain.append acceptProject acceptSim)
        acceptInput acceptSimulated :=
    PhaseChain.spec
      hAcceptProjectSpec hAcceptSimSpec hAcceptProjectBridge
  have hAPASMSpec :
      PhaseChainSpec
        (PhaseChain.append
          (PhaseChain.append acceptProject acceptSim)
          acceptMerge)
        acceptInput afterAccept :=
    PhaseChain.spec hAPASpec hAcceptMergeSpec hAcceptSimBridge
  have hAPASMRPSpec :
      PhaseChainSpec
        (PhaseChain.append
          (PhaseChain.append
            (PhaseChain.append acceptProject acceptSim)
            acceptMerge)
          rejectProject)
        acceptInput rejectProjected :=
    PhaseChain.spec hAPASMSpec hRejectProjectSpec
      hAcceptMergeBridge
  have hAPASMRPRSSpec :
      PhaseChainSpec
        (PhaseChain.append
          (PhaseChain.append
            (PhaseChain.append
              (PhaseChain.append acceptProject acceptSim)
              acceptMerge)
            rejectProject)
          rejectSim)
        acceptInput rejectSimulated :=
    PhaseChain.spec hAPASMRPSpec hRejectSimSpec
      hRejectProjectBridge
  have hrunnerSpec :
      PhaseChainSpec
        (PhaseChain.append
          (PhaseChain.append
            (PhaseChain.append
              (PhaseChain.append
                (PhaseChain.append acceptProject acceptSim)
                acceptMerge)
              rejectProject)
            rejectSim)
          rejectMerge)
        acceptInput runnerOutput :=
    PhaseChain.spec hAPASMRPRSSpec hRejectMergeSpec
      hRejectSimBridge
  constructor
  · simpa [ConfigRunnerPhaseRunner, PhaseChain.append] using
      hrunnerSpec.ready
  constructor
  · intro L
    simpa [ConfigRunnerPhaseRunner, PhaseChain.append, acceptInput,
      runnerOutput] using
      hrunnerSpec.forward L
  · intro L T hhalt
    simpa [ConfigRunnerPhaseRunner, PhaseChain.append, acceptInput,
      runnerOutput] using
      hrunnerSpec.closed L T hhalt

theorem acceptRejectConfigRunnerConstruction_of_phaseEquivConstruction
    (h : ConfigRunnerPhaseEquivConstruction) :
    AcceptRejectConfigRunnerConstruction := by
  intro accept reject
  rcases h accept reject with
    ⟨acceptProject, acceptSim, acceptMerge,
      rejectProject, rejectSim, rejectMerge,
      hacceptProject, hacceptSim, hacceptMerge,
      hrejectProject, hrejectSim, hrejectMerge⟩
  exact
    ⟨ConfigRunnerPhaseRunner
        acceptProject acceptSim acceptMerge
        rejectProject rejectSim rejectMerge,
      configRunnerPhaseRunner_spec
        hacceptProject hacceptSim hacceptMerge
        hrejectProject hrejectSim hrejectMerge⟩

theorem acceptRejectConfigRunnerConstruction_of_phaseConstruction
    (h : ConfigRunnerPhaseConstruction) :
    AcceptRejectConfigRunnerConstruction :=
  acceptRejectConfigRunnerConstruction_of_phaseEquivConstruction
    (configRunnerPhaseEquivConstruction_of_exact h)


end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
