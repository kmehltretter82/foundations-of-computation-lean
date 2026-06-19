import FoC.Computability.Compiler.SeqSubroutineSemantics
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.Parser.Basic

set_option doc.verso true

/-!
# Bounded-layout parser construction

This is the leaf for the complete-layout parser.  The corrected dependency
plan keeps this proof local to the parser phase: it should recognize exactly
complete canonical
{name (full := FoC.Computability.MachineDescription.DovetailLayout)}`MachineDescription.DovetailLayout`
encodings and preserve the input tape.

This leaf is a genuine finite-parser construction, not a small semantic
adapter.  It needs to validate the full
{name (full := FoC.Computability.MachineDescription.DovetailLayout)}`MachineDescription.DovetailLayout`
grammar, including counted cell lists inside the two encoded
{name (full := FoC.Computability.MachineDescription.Configuration)}`MachineDescription.Configuration`
values, and then restore the tape to
{name (full := FoC.Computability.Tape.input)}`Tape.input`.
-/

namespace FoC
namespace Computability

open Languages

namespace EncodedRewriters
namespace BoundedLayoutRunner

def LayoutIdentityPrimitive :
    MachineDescription.TapeCodePrimitive where
  transform := fun code =>
    match MachineDescription.DovetailLayout.decodeComplete code with
    | none => none
    | some _ => some code

theorem layoutIdentityPrimitive_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    LayoutIdentityPrimitive.transform code = some out <->
      exists L : MachineDescription.DovetailLayout,
        code = MachineDescription.DovetailLayout.encode L ∧
          out = MachineDescription.DovetailLayout.encode L := by
  constructor
  · intro h
    unfold LayoutIdentityPrimitive at h
    cases hdecode :
        MachineDescription.DovetailLayout.decodeComplete code with
    | none =>
        simp [hdecode] at h
    | some L =>
        simp [hdecode] at h
        cases h
        exact
          ⟨L,
            MachineDescription.DovetailLayout.decodeComplete_eq_some_encode
              hdecode,
            MachineDescription.DovetailLayout.decodeComplete_eq_some_encode
              hdecode⟩
  · intro h
    rcases h with ⟨L, rfl, rfl⟩
    simp [LayoutIdentityPrimitive,
      MachineDescription.DovetailLayout.decodeComplete_encode]

theorem layoutIdentityPrimitive_encode
    (L : MachineDescription.DovetailLayout) :
    LayoutIdentityPrimitive.transform
        (MachineDescription.DovetailLayout.encode L) =
      some (MachineDescription.DovetailLayout.encode L) := by
  simp [LayoutIdentityPrimitive,
    MachineDescription.DovetailLayout.decodeComplete_encode]

def LayoutIdentityClosedHandoffConstruction : Prop :=
  exists closed : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      LayoutIdentityPrimitive
      closed tapeCodePrimitiveCodeWordHandoffMove

def LayoutParserFromClosedHandoff
    (closed : MachineDescription) : MachineDescription :=
  MachineDescription.seqSubroutine closed
    MachineDescription.ExactIdentityDescription
    tapeCodePrimitiveCodeWordHandoffMove

theorem exactIdentityDescription_runConfig_from_start_layoutParser
    (n : Nat) (T : Tape Bool) :
    MachineDescription.ExactIdentityDescription.runConfig n
        { state := MachineDescription.ExactIdentityDescription.start
          tape := T } =
      { state := MachineDescription.ExactIdentityDescription.halt
        tape := T } := by
  cases n <;>
    simp [MachineDescription.ExactIdentityDescription,
      MachineDescription.runConfig, MachineDescription.stepConfig,
      MachineDescription.lookupTransition]

theorem layoutParserFromClosedHandoff_spec
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        LayoutIdentityPrimitive
        closed tapeCodePrimitiveCodeWordHandoffMove) :
    LayoutParserSpec (LayoutParserFromClosedHandoff closed) := by
  let identity := MachineDescription.ExactIdentityDescription
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
      hclosed
  have hidentityReady : identity.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  constructor
  · exact
      MachineDescription.seqSubroutine_subroutineReady
        hclosedReady hidentityReady
  constructor
  · intro L
    have htransform :
        LayoutIdentityPrimitive.transform
            (MachineDescription.DovetailLayout.encode L) =
          some (MachineDescription.DovetailLayout.encode L) := by
      exact layoutIdentityPrimitive_encode L
    rcases
        (tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffRealized
          hclosed).right
          (MachineDescription.DovetailLayout.encode L)
          (MachineDescription.DovetailLayout.encode L)
          htransform with
      ⟨Tmid, hclosedHalt, hhandoff⟩
    have hidentityReach :
        exists nB : Nat,
          identity.runConfig nB
              { state := identity.start
                tape := Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid } =
            { state := identity.halt
              tape := ParsedLayoutTape L } := by
      refine ⟨0, ?_⟩
      have hinput :
          Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid =
            ParsedLayoutTape L := by
        simpa [ParsedLayoutTape, ParsedLayoutBits] using hhandoff
      rw [hinput]
      rfl
    simpa [LayoutParserFromClosedHandoff, identity,
      ParsedLayoutBits, tapeCodePrimitiveCodeWordHandoffMove] using
      MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
        (A := closed) (B := identity)
        (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
        hclosedReady hidentityReady hclosedHalt hidentityReach
  · intro code T hhalt
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
          (A := closed) (B := identity)
          (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
          hclosedReady hidentityReady
          (by simpa [LayoutParserFromClosedHandoff, identity] using hhalt) with
      ⟨Tmid, hclosedHalt, hidentityReach⟩
    rcases
        hclosed.right code Tmid hclosedHalt with
      ⟨out, htransform, _hnormalized, hhandoff⟩
    rcases
        (layoutIdentityPrimitive_transform_eq_some_iff code out).mp
          htransform with
      ⟨L, hcode, hout⟩
    rcases hidentityReach with ⟨nB, hidentityRun⟩
    have hT :
        T = Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid := by
      have hcfg :
          ({ state := identity.halt
             tape := Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid } :
            MachineDescription.Configuration) =
          { state := identity.halt, tape := T } := by
        simpa [identity] using
          ((exactIdentityDescription_runConfig_from_start_layoutParser
              nB (Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid)).symm.trans
            hidentityRun)
      exact (congrArg MachineDescription.Configuration.tape hcfg).symm
    refine ⟨L, ?_, ?_⟩
    · rw [hcode]
      exact MachineDescription.DovetailLayout.decodeComplete_encode L
    · rw [hT]
      simpa [hout, ParsedLayoutTape, ParsedLayoutBits] using hhandoff

theorem layoutParserConstruction_of_closedHandoffConstruction
    (h : LayoutIdentityClosedHandoffConstruction) :
    LayoutParserConstruction := by
  rcases h with ⟨closed, hclosed⟩
  exact
    ⟨LayoutParserFromClosedHandoff closed,
      layoutParserFromClosedHandoff_spec hclosed⟩

theorem layoutIdentityClosedHandoffConstruction_scaffold :
    LayoutIdentityClosedHandoffConstruction := by
  sorry

theorem layoutParserConstruction_scaffold :
    LayoutParserConstruction := by
  exact
    layoutParserConstruction_of_closedHandoffConstruction
      layoutIdentityClosedHandoffConstruction_scaffold

end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
