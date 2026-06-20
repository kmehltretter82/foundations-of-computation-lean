import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed.Primitives

set_option doc.verso true

/-!
# Bounded recognizer-configuration runner phase construction

This module contains the finite-machine phase contracts and the sequencing
adapters for the bounded recognizer-configuration runner.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

def SeqViaCanonical
    (A B : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine
    (MachineDescription.seqSubroutine A
      MachineDescription.ExactIdentityDescription Direction.right)
    B Direction.left

theorem SeqViaCanonical_subroutineReady
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady) :
    (SeqViaCanonical A B).SubroutineReady := by
  have hid : MachineDescription.ExactIdentityDescription.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  exact
    MachineDescription.seqSubroutine_subroutineReady
      (MachineDescription.seqSubroutine_subroutineReady hA hid)
      hB

theorem SeqViaCanonical_haltsWithTape_of_haltsWithTape
    {A B : MachineDescription}
    (hA : A.SubroutineReady) (hB : B.SubroutineReady)
    {input midInput : Word Bool} {Tmid Tout : Tape Bool}
    (hAmid : A.HaltsWithTape input Tmid)
    (hbridge :
      Tape.move Direction.left (Tape.move Direction.right Tmid) =
        Tape.input midInput)
    (hBout : B.HaltsWithTape midInput Tout) :
    (SeqViaCanonical A B).HaltsWithTape input Tout := by
  let identity := MachineDescription.ExactIdentityDescription
  have hid : identity.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  have hAid :
      (MachineDescription.seqSubroutine A identity Direction.right).HaltsWithTape
        input (Tape.move Direction.right Tmid) := by
    exact
      MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
        (A := A) (B := identity) (handoffMove := Direction.right)
        hA hid hAmid
        ⟨0, rfl⟩
  have hBReach :
      exists nB : Nat,
        B.runConfig nB
            { state := B.start
              tape :=
                Tape.move Direction.left
                  (Tape.move Direction.right Tmid) } =
          { state := B.halt
            tape := Tout } := by
    rcases
        MachineDescription.runConfig_eq_halt_of_haltsWithTape
          hBout with
      ⟨nB, hBRun⟩
    refine ⟨nB, ?_⟩
    simpa [hbridge] using hBRun
  simpa [SeqViaCanonical, identity] using
    MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
      (A := MachineDescription.seqSubroutine A identity Direction.right)
      (B := B) (handoffMove := Direction.left)
      (MachineDescription.seqSubroutine_subroutineReady hA hid)
      hB hAid hBReach

def TapeCodeExactPhaseFromClosedHandoff
    (closed : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine closed
    MachineDescription.ExactIdentityDescription
    tapeCodePrimitiveCodeWordHandoffMove

theorem TapeCodeExactPhaseFromClosedHandoff_subroutineReady
    {P : MachineDescription.TapeCodePrimitive}
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        P closed tapeCodePrimitiveCodeWordHandoffMove) :
    (TapeCodeExactPhaseFromClosedHandoff closed).SubroutineReady := by
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
      hclosed
  have hid : MachineDescription.ExactIdentityDescription.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  exact
    MachineDescription.seqSubroutine_subroutineReady
      hclosedReady hid

theorem TapeCodeExactPhaseFromClosedHandoff_forward
    {P : MachineDescription.TapeCodePrimitive}
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        P closed tapeCodePrimitiveCodeWordHandoffMove)
    {code out : Word MachineCodeSymbol}
    (htransform : P.transform code = some out) :
    (TapeCodeExactPhaseFromClosedHandoff closed).HaltsWithTape
      (MachineDescription.encodeCodeWordAsInput code)
      (Tape.input (MachineDescription.encodeCodeWordAsInput out)) := by
  let identity := MachineDescription.ExactIdentityDescription
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
      hclosed
  have hid : identity.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  rcases
      (tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffRealized
        hclosed).right code out htransform with
    ⟨Tmid, hclosedHalt, hhandoff⟩
  have hidentityReach :
      exists nB : Nat,
        identity.runConfig nB
            { state := identity.start
              tape := Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid } =
          { state := identity.halt
            tape := Tape.input (MachineDescription.encodeCodeWordAsInput out) } := by
    refine ⟨0, ?_⟩
    rw [hhandoff]
    rfl
  simpa [TapeCodeExactPhaseFromClosedHandoff, identity,
    tapeCodePrimitiveCodeWordHandoffMove] using
    MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
      (A := closed) (B := identity)
      (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
      hclosedReady hid hclosedHalt hidentityReach

theorem TapeCodeExactPhaseFromClosedHandoff_closed_eq
    {P : MachineDescription.TapeCodePrimitive}
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        P closed tapeCodePrimitiveCodeWordHandoffMove)
    {code out : Word MachineCodeSymbol}
    (htransform : P.transform code = some out)
    {T : Tape Bool}
    (hhalt :
      (TapeCodeExactPhaseFromClosedHandoff closed).HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T) :
    T = Tape.input (MachineDescription.encodeCodeWordAsInput out) := by
  let identity := MachineDescription.ExactIdentityDescription
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
      hclosed
  have hid : identity.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  rcases
      MachineDescription.seqSubroutine_haltsWithTape_inv
        (A := closed) (B := identity)
        (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
        hclosedReady hid
        (by
          simpa [TapeCodeExactPhaseFromClosedHandoff, identity] using hhalt) with
    ⟨Tmid, hclosedHalt, hidentityReach⟩
  rcases hclosed.right code Tmid hclosedHalt with
    ⟨actual, hactual, _hnormalized, hhandoff⟩
  have hactualOut : actual = out := by
    rw [htransform] at hactual
    cases hactual
    rfl
  rcases hidentityReach with ⟨nB, hidentityRun⟩
  have hT :
      T = Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid := by
    have hidentityStart :
        identity.runConfig nB
            { state := identity.start
              tape := Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid } =
          { state := identity.halt
            tape := Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid } := by
      cases nB <;>
        simp [identity, MachineDescription.ExactIdentityDescription,
          MachineDescription.runConfig, MachineDescription.stepConfig,
          MachineDescription.lookupTransition]
    have hcfg :
        ({ state := identity.halt
           tape := Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid } :
          MachineDescription.Configuration) =
        { state := identity.halt, tape := T } := by
      simpa [identity] using
        (hidentityStart.symm.trans hidentityRun)
    exact (congrArg MachineDescription.Configuration.tape hcfg).symm
  rw [hT]
  simpa [hactualOut] using hhandoff

def AcceptProjectionSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    (forall L : MachineDescription.DovetailLayout,
      projector.HaltsWithTape
        (ParsedLayoutBits L)
        (MachineDescription.SimulatorLayout.tape
          (AcceptSimulatorLayout L))) ∧
    (forall L : MachineDescription.DovetailLayout,
     forall T : Tape Bool,
      projector.HaltsWithTape (ParsedLayoutBits L) T ->
        T =
          MachineDescription.SimulatorLayout.tape
            (AcceptSimulatorLayout L))

def RejectProjectionSpec
    (projector : MachineDescription) : Prop :=
  projector.SubroutineReady ∧
    (forall L : MachineDescription.DovetailLayout,
      projector.HaltsWithTape
        (ParsedLayoutBits L)
        (MachineDescription.SimulatorLayout.tape
          (RejectSimulatorLayout L))) ∧
    (forall L : MachineDescription.DovetailLayout,
     forall T : Tape Bool,
      projector.HaltsWithTape (ParsedLayoutBits L) T ->
        T =
          MachineDescription.SimulatorLayout.tape
            (RejectSimulatorLayout L))

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
      (TapeCodeExactPhaseFromClosedHandoff closed) := by
  constructor
  · exact TapeCodeExactPhaseFromClosedHandoff_subroutineReady hclosed
  constructor
  · intro L
    simpa [ParsedLayoutBits,
      MachineDescription.SimulatorLayout.tape,
      MachineDescription.SimulatorLayout.asBoolInput] using
      TapeCodeExactPhaseFromClosedHandoff_forward
        hclosed (AcceptProjectionPrimitive_encode L)
  · intro L T hhalt
    have hhalt' :
        (TapeCodeExactPhaseFromClosedHandoff closed).HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailLayout.encode L)) T := by
      simpa [ParsedLayoutBits] using hhalt
    have hT :=
      TapeCodeExactPhaseFromClosedHandoff_closed_eq
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
    simpa [ParsedLayoutBits,
      MachineDescription.SimulatorLayout.tape,
      MachineDescription.SimulatorLayout.asBoolInput] using
      TapeCodeExactPhaseFromClosedHandoff_forward
        hclosed (RejectProjectionPrimitive_encode L)
  · intro L T hhalt
    have hhalt' :
        (TapeCodeExactPhaseFromClosedHandoff closed).HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput
            (MachineDescription.DovetailLayout.encode L)) T := by
      simpa [ParsedLayoutBits] using hhalt
    have hT :=
      TapeCodeExactPhaseFromClosedHandoff_closed_eq
        hclosed (RejectProjectionPrimitive_encode L) hhalt'
    simpa [MachineDescription.SimulatorLayout.tape,
      MachineDescription.SimulatorLayout.asBoolInput] using hT

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
      FixedDescriptionBoundedSimulatorCanonicalSpec accept acceptSim)
    (hacceptMerge : AcceptMergeSpec accept acceptMerge)
    (hrejectProject : RejectProjectionSpec rejectProject)
    (hrejectSim :
      FixedDescriptionBoundedSimulatorCanonicalSpec reject rejectSim)
    (hrejectMerge : RejectMergeSpec reject rejectMerge) :
    AcceptRejectConfigRunnerSpec accept reject
      (ConfigRunnerPhaseRunner
        acceptProject acceptSim acceptMerge
        rejectProject rejectSim rejectMerge) := by
  let APAS := SeqViaCanonical acceptProject acceptSim
  let APASM := SeqViaCanonical APAS acceptMerge
  let APASMRP := SeqViaCanonical APASM rejectProject
  let APASMRPRS := SeqViaCanonical APASMRP rejectSim
  let runner := SeqViaCanonical APASMRPRS rejectMerge
  have hAcceptProjectReady : acceptProject.SubroutineReady :=
    hacceptProject.left
  have hAcceptSimReady : acceptSim.SubroutineReady :=
    hacceptSim.left
  have hAcceptMergeReady : acceptMerge.SubroutineReady :=
    hacceptMerge.left
  have hRejectProjectReady : rejectProject.SubroutineReady :=
    hrejectProject.left
  have hRejectSimReady : rejectSim.SubroutineReady :=
    hrejectSim.left
  have hRejectMergeReady : rejectMerge.SubroutineReady :=
    hrejectMerge.left
  have hAPASReady : APAS.SubroutineReady := by
    exact SeqViaCanonical_subroutineReady
      hAcceptProjectReady hAcceptSimReady
  have hAPASMReady : APASM.SubroutineReady := by
    exact SeqViaCanonical_subroutineReady
      hAPASReady hAcceptMergeReady
  have hAPASMRPReady : APASMRP.SubroutineReady := by
    exact SeqViaCanonical_subroutineReady
      hAPASMReady hRejectProjectReady
  have hAPASMRPRSReady : APASMRPRS.SubroutineReady := by
    exact SeqViaCanonical_subroutineReady
      hAPASMRPReady hRejectSimReady
  have hrunnerReady : runner.SubroutineReady := by
    exact SeqViaCanonical_subroutineReady
      hAPASMRPRSReady hRejectMergeReady
  have hforward :
      AcceptRejectConfigRunnerForwardSpec accept reject runner := by
    intro L
    have hAcceptProjectRun :
        acceptProject.HaltsWithTape
          (ParsedLayoutBits L)
          (MachineDescription.SimulatorLayout.tape
            (AcceptSimulatorLayout L)) :=
      hacceptProject.right.left L
    have hAcceptSimRun :
        acceptSim.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput
            (AcceptSimulatorLayout L))
          (MachineDescription.SimulatorLayout.tape
            (MachineDescription.SimulatorLayout.run
              accept L.stage (AcceptSimulatorLayout L))) := by
      simpa [FixedDescriptionBoundedSimulatorInput,
        FixedDescriptionBoundedSimulatorCanonicalOutputTape,
        AcceptSimulatorLayout] using
        hacceptSim.right.left (AcceptSimulatorLayout L)
    have hAPASRun :
        APAS.HaltsWithTape
          (ParsedLayoutBits L)
          (MachineDescription.SimulatorLayout.tape
            (MachineDescription.SimulatorLayout.run
              accept L.stage (AcceptSimulatorLayout L))) := by
      exact
        SeqViaCanonical_haltsWithTape_of_haltsWithTape
          hAcceptProjectReady hAcceptSimReady
          hAcceptProjectRun
          (by
            simpa [MachineDescription.SimulatorLayout.tape] using
              simulatorLayoutTape_move_left_move_right
                (AcceptSimulatorLayout L))
          hAcceptSimRun
    have hAcceptMergeRun :
        acceptMerge.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput
            (MachineDescription.SimulatorLayout.run
              accept L.stage (AcceptSimulatorLayout L)))
          (ParsedLayoutTape (ConfigRunnerAfterAccept accept L)) :=
      hacceptMerge.right.left L
    have hAPASMRun :
        APASM.HaltsWithTape
          (ParsedLayoutBits L)
          (ParsedLayoutTape (ConfigRunnerAfterAccept accept L)) := by
      exact
        SeqViaCanonical_haltsWithTape_of_haltsWithTape
          hAPASReady hAcceptMergeReady
          hAPASRun
          (by
            simpa [MachineDescription.SimulatorLayout.tape] using
              simulatorLayoutTape_move_left_move_right
                (MachineDescription.SimulatorLayout.run
                  accept L.stage (AcceptSimulatorLayout L)))
          hAcceptMergeRun
    have hRejectProjectRun :
        rejectProject.HaltsWithTape
          (ParsedLayoutBits (ConfigRunnerAfterAccept accept L))
          (MachineDescription.SimulatorLayout.tape
            (RejectSimulatorLayout
              (ConfigRunnerAfterAccept accept L))) :=
      hrejectProject.right.left (ConfigRunnerAfterAccept accept L)
    have hAPASMRPRun :
        APASMRP.HaltsWithTape
          (ParsedLayoutBits L)
          (MachineDescription.SimulatorLayout.tape
            (RejectSimulatorLayout
              (ConfigRunnerAfterAccept accept L))) := by
      exact
        SeqViaCanonical_haltsWithTape_of_haltsWithTape
          hAPASMReady hRejectProjectReady
          hAPASMRun
          (by
            simpa [ParsedLayoutTape] using
              parsedLayoutTape_move_left_move_right_configRunner
                (ConfigRunnerAfterAccept accept L))
          hRejectProjectRun
    have hRejectSimRun :
        rejectSim.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput
            (RejectSimulatorLayout
              (ConfigRunnerAfterAccept accept L)))
          (MachineDescription.SimulatorLayout.tape
            (MachineDescription.SimulatorLayout.run
              reject (ConfigRunnerAfterAccept accept L).stage
              (RejectSimulatorLayout
                (ConfigRunnerAfterAccept accept L)))) := by
      simpa [FixedDescriptionBoundedSimulatorInput,
        FixedDescriptionBoundedSimulatorCanonicalOutputTape] using
        hrejectSim.right.left
          (RejectSimulatorLayout (ConfigRunnerAfterAccept accept L))
    have hAPASMRPRSRun :
        APASMRPRS.HaltsWithTape
          (ParsedLayoutBits L)
          (MachineDescription.SimulatorLayout.tape
            (MachineDescription.SimulatorLayout.run
              reject (ConfigRunnerAfterAccept accept L).stage
              (RejectSimulatorLayout
                (ConfigRunnerAfterAccept accept L)))) := by
      exact
        SeqViaCanonical_haltsWithTape_of_haltsWithTape
          hAPASMRPReady hRejectSimReady
          hAPASMRPRun
          (by
            simpa [MachineDescription.SimulatorLayout.tape] using
              simulatorLayoutTape_move_left_move_right
                (RejectSimulatorLayout
                  (ConfigRunnerAfterAccept accept L)))
          hRejectSimRun
    have hRejectMergeRun :
        rejectMerge.HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput
            (MachineDescription.SimulatorLayout.run
              reject (ConfigRunnerAfterAccept accept L).stage
              (RejectSimulatorLayout
                (ConfigRunnerAfterAccept accept L))))
          (ParsedLayoutTape
            (ConfigRunnerAfterReject reject
              (ConfigRunnerAfterAccept accept L))) :=
      hrejectMerge.right.left (ConfigRunnerAfterAccept accept L)
    have hRunner :
        runner.HaltsWithTape
          (ParsedLayoutBits L)
          (ParsedLayoutTape
            (ConfigRunnerAfterReject reject
              (ConfigRunnerAfterAccept accept L))) := by
      exact
        SeqViaCanonical_haltsWithTape_of_haltsWithTape
          hAPASMRPRSReady hRejectMergeReady
          hAPASMRPRSRun
          (by
            simpa [MachineDescription.SimulatorLayout.tape] using
              simulatorLayoutTape_move_left_move_right
                (MachineDescription.SimulatorLayout.run
                  reject (ConfigRunnerAfterAccept accept L).stage
                  (RejectSimulatorLayout
                    (ConfigRunnerAfterAccept accept L))))
          hRejectMergeRun
    have hOutput :
        ParsedLayoutTape
            (ConfigRunnerAfterReject reject
              (ConfigRunnerAfterAccept accept L)) =
          ConfigRunnerOutputTape accept reject L := by
      rw [ConfigRunnerAfterReject_afterAccept]
      rfl
    simpa [hOutput] using hRunner
  have hrunnerReady' :
      (ConfigRunnerPhaseRunner
        acceptProject acceptSim acceptMerge
        rejectProject rejectSim rejectMerge).SubroutineReady := by
    simpa [ConfigRunnerPhaseRunner, runner, APAS, APASM,
      APASMRP, APASMRPRS] using hrunnerReady
  have hforward' :
      AcceptRejectConfigRunnerForwardSpec accept reject
        (ConfigRunnerPhaseRunner
          acceptProject acceptSim acceptMerge
          rejectProject rejectSim rejectMerge) := by
    simpa [ConfigRunnerPhaseRunner, runner, APAS, APASM,
      APASMRP, APASMRPRS] using hforward
  constructor
  · exact hrunnerReady'
  constructor
  · exact hforward'
  · intro L T hhalt
    exact
      MachineDescription.haltsWithTape_functional_of_haltTransitionFree
        hrunnerReady'.right hhalt (hforward' L)

theorem acceptRejectConfigRunnerConstruction_of_phaseConstruction
    (h : ConfigRunnerPhaseConstruction) :
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

def SelectedProjectionEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  ReadySpec emitter ∧
    (forall L : MachineDescription.DovetailLayout,
      emitter.HaltsWithTape
        (ParsedLayoutBits L)
        (SelectedProjectionOutputTape useAccept L)) ∧
      forall L : MachineDescription.DovetailLayout,
      forall T : Tape Bool,
        emitter.HaltsWithTape (ParsedLayoutBits L) T ->
          T = SelectedProjectionOutputTape useAccept L

def SelectedProjectionEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedProjectionEmitterSpec useAccept emitter

theorem selectedProjectionSpec_of_parser_emitter
    {useAccept : Bool} {parser emitter : MachineDescription}
    (hparser : LayoutParserSpec parser)
    (hemitter : SelectedProjectionEmitterSpec useAccept emitter) :
    SelectedProjectionSpec useAccept
      (SeqViaCanonical parser emitter) := by
  have hrunnerReady :
      (SeqViaCanonical parser emitter).SubroutineReady :=
    SeqViaCanonical_subroutineReady hparser.left hemitter.left
  constructor
  · exact hrunnerReady
  constructor
  · intro L
    exact
      SeqViaCanonical_haltsWithTape_of_haltsWithTape
        hparser.left hemitter.left
        (hparser.right.left L)
        (parsedLayoutTape_move_left_move_right_configRunner L)
        (hemitter.right.left L)
  · intro code T hhalt
    let identity := MachineDescription.ExactIdentityDescription
    have hid : identity.SubroutineReady :=
      ⟨MachineDescription.exactIdentityDescription_wellFormed,
        MachineDescription.exactIdentityDescription_haltTransitionFree⟩
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          (A := MachineDescription.seqSubroutine
            parser identity Direction.right)
          (B := emitter)
          (handoffMove := Direction.left)
          (MachineDescription.seqSubroutine_subroutineReady
            hparser.left hid)
          hemitter.left
          (by simpa [SeqViaCanonical, identity] using hhalt) with
      ⟨Tmid, hparserIdHalt, _hemitterReach⟩
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          (A := parser) (B := identity)
          (handoffMove := Direction.right)
          hparser.left hid
          (by simpa [identity] using hparserIdHalt) with
      ⟨Tparser, hparserHalt, _hidentityReach⟩
    rcases hparser.right.right code Tparser hparserHalt with
      ⟨L, hdecode, _hTparser⟩
    have hcode :
        code = MachineDescription.DovetailLayout.encode L :=
      MachineDescription.DovetailLayout.decodeComplete_eq_some_encode
        hdecode
    refine ⟨L, hcode, ?_⟩
    have hhalt' :
        (SeqViaCanonical parser emitter).HaltsWithTape
          (ParsedLayoutBits L) T := by
      simpa [ParsedLayoutBits, hcode] using hhalt
    have hforwardL :
        (SeqViaCanonical parser emitter).HaltsWithTape
          (ParsedLayoutBits L)
          (SelectedProjectionOutputTape useAccept L) :=
      SeqViaCanonical_haltsWithTape_of_haltsWithTape
        hparser.left hemitter.left
        (hparser.right.left L)
        (parsedLayoutTape_move_left_move_right_configRunner L)
        (hemitter.right.left L)
    exact
      MachineDescription.haltsWithTape_functional_of_haltTransitionFree
        hrunnerReady.right hhalt' hforwardL

theorem selectedProjectionFiniteDescriptionConstruction_of_emitter
    (hemitter : SelectedProjectionEmitterConstruction) :
    SelectedProjectionFiniteDescriptionConstruction := by
  intro useAccept
  rcases layoutParserConstruction_scaffold with ⟨parser, hparser⟩
  rcases hemitter useAccept with ⟨emitter, hemits⟩
  exact
    ⟨SeqViaCanonical parser emitter,
      selectedProjectionSpec_of_parser_emitter hparser hemits⟩

theorem selectedProjectionEmitterConstruction_scaffold :
    SelectedProjectionEmitterConstruction := by
  sorry

def SelectedMergeParserSpec
    (parser : MachineDescription) : Prop :=
  ReadySpec parser ∧
    (forall S : MachineDescription.SimulatorLayout,
     forall L : MachineDescription.DovetailLayout,
      MachineDescription.decodeCodeWordAsInput S.input =
        some (MachineDescription.DovetailLayout.encode L) ->
      parser.HaltsWithTape
        (MachineDescription.SimulatorLayout.asBoolInput S)
        (MachineDescription.SimulatorLayout.tape S)) ∧
      forall code : Word MachineCodeSymbol,
      forall T : Tape Bool,
        parser.HaltsWithTape
            (MachineDescription.encodeCodeWordAsInput code) T ->
          exists S : MachineDescription.SimulatorLayout,
          exists L : MachineDescription.DovetailLayout,
            code = MachineDescription.SimulatorLayout.encode S ∧
              MachineDescription.decodeCodeWordAsInput S.input =
                some (MachineDescription.DovetailLayout.encode L) ∧
              T = MachineDescription.SimulatorLayout.tape S

def SelectedMergeParserConstruction : Prop :=
  exists parser : MachineDescription,
    SelectedMergeParserSpec parser

def SelectedMergeEmitterSpec
    (useAccept : Bool)
    (emitter : MachineDescription) : Prop :=
  ReadySpec emitter ∧
    (forall S : MachineDescription.SimulatorLayout,
     forall L : MachineDescription.DovetailLayout,
      MachineDescription.decodeCodeWordAsInput S.input =
        some (MachineDescription.DovetailLayout.encode L) ->
      emitter.HaltsWithTape
        (MachineDescription.SimulatorLayout.asBoolInput S)
        (SelectedMergeOutputTape useAccept S L)) ∧
      forall S : MachineDescription.SimulatorLayout,
      forall L : MachineDescription.DovetailLayout,
      forall T : Tape Bool,
        MachineDescription.decodeCodeWordAsInput S.input =
          some (MachineDescription.DovetailLayout.encode L) ->
        emitter.HaltsWithTape
            (MachineDescription.SimulatorLayout.asBoolInput S) T ->
          T = SelectedMergeOutputTape useAccept S L

def SelectedMergeEmitterConstruction : Prop :=
  forall useAccept : Bool,
    exists emitter : MachineDescription,
      SelectedMergeEmitterSpec useAccept emitter

theorem selectedMergeSpec_of_parser_emitter
    {useAccept : Bool} {parser emitter : MachineDescription}
    (hparser : SelectedMergeParserSpec parser)
    (hemitter : SelectedMergeEmitterSpec useAccept emitter) :
    SelectedMergeSpec useAccept
      (SeqViaCanonical parser emitter) := by
  have hrunnerReady :
      (SeqViaCanonical parser emitter).SubroutineReady :=
    SeqViaCanonical_subroutineReady hparser.left hemitter.left
  constructor
  · exact hrunnerReady
  constructor
  · intro S L hinput
    exact
      SeqViaCanonical_haltsWithTape_of_haltsWithTape
        hparser.left hemitter.left
        (hparser.right.left S L hinput)
        (simulatorLayoutTape_move_left_move_right S)
        (hemitter.right.left S L hinput)
  · intro code T hhalt
    let identity := MachineDescription.ExactIdentityDescription
    have hid : identity.SubroutineReady :=
      ⟨MachineDescription.exactIdentityDescription_wellFormed,
        MachineDescription.exactIdentityDescription_haltTransitionFree⟩
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          (A := MachineDescription.seqSubroutine
            parser identity Direction.right)
          (B := emitter)
          (handoffMove := Direction.left)
          (MachineDescription.seqSubroutine_subroutineReady
            hparser.left hid)
          hemitter.left
          (by simpa [SeqViaCanonical, identity] using hhalt) with
      ⟨Tmid, hparserIdHalt, _hemitterReach⟩
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          (A := parser) (B := identity)
          (handoffMove := Direction.right)
          hparser.left hid
          (by simpa [identity] using hparserIdHalt) with
      ⟨Tparser, hparserHalt, _hidentityReach⟩
    rcases hparser.right.right code Tparser hparserHalt with
      ⟨S, L, hcode, hinput, _hTparser⟩
    refine ⟨S, L, hcode, hinput, ?_⟩
    have hhalt' :
        (SeqViaCanonical parser emitter).HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput S) T := by
      simpa [MachineDescription.SimulatorLayout.asBoolInput, hcode] using
        hhalt
    have hforward :
        (SeqViaCanonical parser emitter).HaltsWithTape
          (MachineDescription.SimulatorLayout.asBoolInput S)
          (SelectedMergeOutputTape useAccept S L) :=
      SeqViaCanonical_haltsWithTape_of_haltsWithTape
        hparser.left hemitter.left
        (hparser.right.left S L hinput)
        (simulatorLayoutTape_move_left_move_right S)
        (hemitter.right.left S L hinput)
    exact
      MachineDescription.haltsWithTape_functional_of_haltTransitionFree
        hrunnerReady.right hhalt' hforward

theorem selectedMergeFiniteDescriptionConstruction_of_parser_emitter
    (hparser : SelectedMergeParserConstruction)
    (hemitter : SelectedMergeEmitterConstruction) :
    SelectedMergeFiniteDescriptionConstruction := by
  intro useAccept
  rcases hparser with ⟨parser, hparser⟩
  rcases hemitter useAccept with ⟨emitter, hemits⟩
  exact
    ⟨SeqViaCanonical parser emitter,
      selectedMergeSpec_of_parser_emitter hparser hemits⟩

theorem selectedMergeParserConstruction_scaffold :
    SelectedMergeParserConstruction := by
  sorry

theorem selectedMergeEmitterConstruction_scaffold :
    SelectedMergeEmitterConstruction := by
  sorry

def FixedDescriptionBoundedSimulatorStepPhaseConstruction_configRunner :
    Prop :=
  forall D : MachineDescription,
    exists simulateStep : MachineDescription.Fragment,
      FixedDescriptionBoundedSimulatorPhaseRealizes
        (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
        FixedDescriptionBoundedSimulatorLayoutTape
        (fun L => MachineDescription.SimulatorLayout.run D L.stage L)
        simulateStep

theorem fixedDescriptionBoundedSimulatorReturnFromRightPhaseRealizes_configRunner :
    FixedDescriptionBoundedSimulatorPhaseRealizes
      (FixedDescriptionBoundedSimulatorHandoffTape Direction.right)
      FixedDescriptionBoundedSimulatorLayoutTape
      id
      (MachineDescription.Fragment.handoff Direction.left) := by
  constructor
  · exact MachineDescription.Fragment.handoff_wellFormed Direction.left
  · intro L
    rcases
        MachineDescription.Fragment.handoff_firstReaches Direction.left
          (FixedDescriptionBoundedSimulatorHandoffTape Direction.right L) with
      ⟨n, hn, hminimal⟩
    refine ⟨n, ?_, hminimal⟩
    simpa [FixedDescriptionBoundedSimulatorHandoffTape,
      FixedDescriptionBoundedSimulatorLayoutTape] using hn

theorem fixedDescriptionBoundedSimulatorSkeletonPhaseConstruction_of_stepPhase_configRunner
    (hstep :
      FixedDescriptionBoundedSimulatorStepPhaseConstruction_configRunner) :
    FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction := by
  intro D
  rcases hstep D with ⟨simulateStep, hsimulateStep⟩
  let S : MachineDescription.FixedSimulatorTableSkeleton :=
    { decodeLayout := MachineDescription.Fragment.halt
      simulateStep := simulateStep
      repeatControl := MachineDescription.Fragment.handoff Direction.left
      emitLayout := MachineDescription.Fragment.handoff Direction.left
      decodeLayout_wellFormed :=
        MachineDescription.Fragment.halt_wellFormed
      simulateStep_wellFormed := hsimulateStep.left
      repeatControl_wellFormed :=
        MachineDescription.Fragment.handoff_wellFormed Direction.left
      emitLayout_wellFormed :=
        MachineDescription.Fragment.handoff_wellFormed Direction.left }
  refine
    ⟨S, Direction.right,
      FixedDescriptionBoundedSimulatorPhaseTargets.canonical D, ?_⟩
  refine
    { decodeLayout := ?_
      simulateStep := ?_
      repeatControl := ?_
      emitLayout := ?_ }
  · simpa [S, FixedDescriptionBoundedSimulatorPhaseTargets.canonical] using
      fixedDescriptionBoundedSimulatorHaltPhaseRealizes
        FixedDescriptionBoundedSimulatorLayoutTape
  · simpa [S, FixedDescriptionBoundedSimulatorPhaseTargets.canonical] using
      hsimulateStep
  · simpa [S, FixedDescriptionBoundedSimulatorPhaseTargets.canonical] using
      fixedDescriptionBoundedSimulatorReturnFromRightPhaseRealizes_configRunner
  · simpa [S, FixedDescriptionBoundedSimulatorPhaseTargets.canonical] using
      fixedDescriptionBoundedSimulatorReturnFromRightPhaseRealizes_configRunner

theorem fixedDescriptionBoundedSimulatorStepPhaseConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorStepPhaseConstruction_configRunner := by
  sorry

theorem fixedDescriptionBoundedSimulatorSkeletonPhaseConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorSkeletonPhaseConstruction :=
  fixedDescriptionBoundedSimulatorSkeletonPhaseConstruction_of_stepPhase_configRunner
    fixedDescriptionBoundedSimulatorStepPhaseConstruction_scaffold_configRunner

theorem fixedDescriptionBoundedSimulatorCanonicalConstruction_scaffold_configRunner :
    FixedDescriptionBoundedSimulatorCanonicalConstruction :=
  fixedDescriptionBoundedSimulatorCanonicalConstruction_of_phaseConstruction
    fixedDescriptionBoundedSimulatorSkeletonPhaseConstruction_scaffold_configRunner

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
