import FoC.Computability.DescriptionPairHalting
import FoC.Computability.Compiler.Core.PairHaltingReduction.MissingRejectCompletion
import FoC.Computability.Compiler.Core.PairHaltingReduction.SelfAppendMaterializer
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.Construction
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind
import FoC.Computability.Compiler.Core.CommonGround.SameHeadComposition

set_option doc.verso true

/-!
# Checked pair-halting reduction

The reduction validates one complete finite description, rewinds its canonical
Boolean code, materializes two copies, and invokes the supplied stopped decider
for the self-delimiting pair-halting language.  A missing-only completion turns
malformed validator endpoints into the supplied reject bit while preserving
every normal decider output.
-/

namespace FoC
namespace Computability
namespace PairHaltingReduction

open Languages
open MachineDescription

def GateRewindDescription : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    SelfHaltingRecognizer.ExactCodeValidator.GateDescription
    CommonGround.FiniteTransducers.rightEdgeRewindDescription

def MaterializedDescription : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    GateRewindDescription SelfAppendMaterializer.Description

def BaseDescription (pairDecider : MachineDescription) : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    MaterializedDescription pairDecider

def Description (pairDecider : MachineDescription) (reject : Bool) :
    MachineDescription :=
  MissingRejectCompletion.Description (BaseDescription pairDecider) reject

theorem gateRewindDescription_subroutineReady :
    GateRewindDescription.SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    SelfHaltingRecognizer.ExactCodeValidator.gateDescription_subroutineReady
    CommonGround.FiniteTransducers.rightEdgeRewindDescription_subroutineReady

theorem materializedDescription_subroutineReady :
    MaterializedDescription.SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    gateRewindDescription_subroutineReady
    SelfAppendMaterializer.description_subroutineReady

theorem baseDescription_subroutineReady
    {pairDecider : MachineDescription}
    (hpair : pairDecider.SubroutineReady) :
    (BaseDescription pairDecider).SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    materializedDescription_subroutineReady hpair

theorem description_subroutineReady
    {pairDecider : MachineDescription}
    (_hpair : pairDecider.SubroutineReady) (reject : Bool) :
    (Description pairDecider reject).SubroutineReady :=
  MissingRejectCompletion.description_subroutineReady
    (BaseDescription pairDecider) reject

private theorem haltsFromTapeEquiv_of_input_equiv
    {D : MachineDescription} {source source' target : Tape Bool}
    (hsource : Tape.Equiv source source')
    (hhalts : D.HaltsFromTapeEquiv source target) :
    D.HaltsFromTapeEquiv source' target := by
  rcases hhalts with ⟨actual, hactual, htarget⟩
  rcases MachineDescription.HaltsFromTapeEquiv_of_input_equiv
      hsource hactual with ⟨transported, htransported, hequiv⟩
  exact ⟨transported, htransported, Tape.Equiv.trans hequiv htarget⟩

private theorem exists_haltsFromTape_of_haltsFromTapeWithOutput
    {D : MachineDescription} {input : Tape Bool} {out : Word Bool}
    (hhalts : D.HaltsFromTapeWithOutput input out) :
    exists output : Tape Bool,
      D.HaltsFromTape input output ∧
        Tape.normalizedOutput output = out := by
  rcases hhalts with ⟨steps, hstate, houtput⟩
  let output :=
    (D.runConfig steps { state := D.start, tape := input }).tape
  exact ⟨output, ⟨steps, hstate, rfl⟩, houtput⟩

private theorem haltsFromTapeWithOutput_of_haltsWithOutput
    {D : MachineDescription} {input out : Word Bool}
    (hhalts : D.HaltsWithOutput input out) :
    D.HaltsFromTapeWithOutput (Tape.input input) out := by
  simpa only [MachineDescription.HaltsFromTapeWithOutput,
    MachineDescription.HaltsFromTapeWithOutputIn,
    MachineDescription.HaltsWithOutput,
    MachineDescription.HaltsWithOutputIn,
    MachineDescription.initial] using hhalts

private theorem haltsWithOutput_of_haltsFromTapeWithOutput
    {D : MachineDescription} {input out : Word Bool}
    (hhalts : D.HaltsFromTapeWithOutput (Tape.input input) out) :
    D.HaltsWithOutput input out := by
  simpa only [MachineDescription.HaltsFromTapeWithOutput,
    MachineDescription.HaltsFromTapeWithOutputIn,
    MachineDescription.HaltsWithOutput,
    MachineDescription.HaltsWithOutputIn,
    MachineDescription.initial] using hhalts

private theorem moveRight_moveLeft_equiv_self (tape : Tape Bool) :
    Tape.Equiv
      (Tape.move Direction.right (Tape.move Direction.left tape)) tape := by
  cases tape with
  | mk left head right =>
      simp [Tape.Equiv, Tape.move, Tape.moveLeft, Tape.moveRight]
      cases left <;> simp [Tape.dropTrailingNone]

private theorem gateRewindDescription_haltsFromTape
    {code : Word MachineCodeSymbol}
    (hvalid : MachineDescription.DescriptionCodeValid code) :
    GateRewindDescription.HaltsFromTape
      (Tape.input (encodeCodeWordAsInput code))
      (CommonGround.FiniteTransducers.rightEdgeRewindTargetTape
        (encodeCodeWordAsInput code) []) := by
  have hcode :=
    SelfHaltingRecognizer.ConcreteRecognizer.valid_code_ne_nil hvalid
  have hbits :=
    SelfHaltingRecognizer.ConcreteRecognizer.encoded_code_ne_nil_of_code_ne_nil
      hcode
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
      SelfHaltingRecognizer.ExactCodeValidator.gateDescription_subroutineReady
      CommonGround.FiniteTransducers.rightEdgeRewindDescription_subroutineReady
      ((SelfHaltingRecognizer.ConcreteRecognizer.gate_haltsTo_validatedBoundary_iff
        code).2 hvalid)
      (SelfHaltingRecognizer.ConcreteRecognizer.validatedBoundaryTape_bounce
        _ hbits)
      (SelfHaltingRecognizer.ConcreteRecognizer.rewind_haltsFrom_validatedBoundary
        _ hbits)

private theorem materializedDescription_haltsFromTapeEquiv
    {code : Word MachineCodeSymbol}
    (hvalid : MachineDescription.DescriptionCodeValid code) :
    MaterializedDescription.HaltsFromTapeEquiv
      (Tape.input (encodeCodeWordAsInput code))
      (Tape.input (encodeCodeWordAsInput (List.append code code))) := by
  cases code with
  | nil =>
      exact False.elim
        (SelfHaltingRecognizer.ConcreteRecognizer.valid_code_ne_nil
          hvalid rfl)
  | cons first rest =>
      have hfront := gateRewindDescription_haltsFromTape hvalid
      have hmaterialize :=
        SelfAppendMaterializer.description_haltsFromTapeEquiv first rest
      have hmaterialize' := haltsFromTapeEquiv_of_input_equiv
        (Tape.Equiv.symm
          (SelfHaltingRecognizer.ConcreteRecognizer.rewindTargetTape_equiv_input
            (encodeCodeWordAsInput (first :: rest))))
        hmaterialize
      exact
        CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTape
          gateRewindDescription_subroutineReady
          SelfAppendMaterializer.description_subroutineReady
          hfront
          (SelfHaltingRecognizer.ConcreteRecognizer.rewindTargetTape_bounce
            (encodeCodeWordAsInput (first :: rest)))
          hmaterialize'

private theorem baseDescription_haltsFromTapeWithOutput
    {pairDecider : MachineDescription}
    (hpair : pairDecider.SubroutineReady)
    {code : Word MachineCodeSymbol}
    (hvalid : MachineDescription.DescriptionCodeValid code)
    {out : Word Bool}
    (hhalts : pairDecider.HaltsWithOutput
      (encodeCodeWordAsInput (List.append code code)) out) :
    (BaseDescription pairDecider).HaltsFromTapeWithOutput
      (Tape.input (encodeCodeWordAsInput code)) out := by
  let duplicatedTape : Tape Bool :=
    Tape.input (encodeCodeWordAsInput (List.append code code))
  let bouncedTape : Tape Bool :=
    Tape.move Direction.right (Tape.move Direction.left duplicatedTape)
  have hmaterialized := materializedDescription_haltsFromTapeEquiv hvalid
  have hpairFromTape : pairDecider.HaltsFromTapeWithOutput
      duplicatedTape out := by
    exact haltsFromTapeWithOutput_of_haltsWithOutput hhalts
  have hpairFromBounce : pairDecider.HaltsFromTapeWithOutput
      bouncedTape out := by
    exact MachineDescription.haltsFromTapeWithOutput_of_input_equiv
      (Tape.Equiv.symm (moveRight_moveLeft_equiv_self duplicatedTape))
      hpairFromTape
  rcases exists_haltsFromTape_of_haltsFromTapeWithOutput hpairFromBounce with
    ⟨output, hpairExact, houtput⟩
  have hbaseEquiv : (BaseDescription pairDecider).HaltsFromTapeEquiv
      (Tape.input (encodeCodeWordAsInput code)) output :=
    CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTapeEquiv_of_haltsFromTapeEquiv_haltsFromTape
      materializedDescription_subroutineReady hpair
      hmaterialized rfl hpairExact
  have hbase :=
    MachineDescription.haltsFromTapeWithOutput_of_haltsFromTapeEquiv hbaseEquiv
  rw [houtput] at hbase
  exact hbase

private theorem baseDescription_contiguousStuck_of_not_valid
    {pairDecider : MachineDescription}
    (hpair : pairDecider.SubroutineReady)
    {code : Word MachineCodeSymbol}
    (hnot : ¬ MachineDescription.DescriptionCodeValid code) :
    exists stuck : Tape Bool,
      (BaseDescription pairDecider).StuckFromTape
          (Tape.input (encodeCodeWordAsInput code)) stuck ∧
        ContiguousTape stuck := by
  rcases
      SelfHaltingRecognizer.ExactCodeValidator.gateDescription_haltsOrContiguousStuckFromCode
        code with
    hgate | hgate
  · rcases hgate with ⟨output, houtput⟩
    exact False.elim
      (hnot
        ((SelfHaltingRecognizer.ExactCodeValidator.gateDescription_exists_haltsFromCode_iff_descriptionCodeValid
          code).1 ⟨output, houtput⟩))
  · rcases hgate with ⟨stuck, hstuck, hcontiguous⟩
    have hgateRewind :=
      CommonGround.SameHeadComposition.leftRightSeqDescription_stuckFromTape_of_left
        SelfHaltingRecognizer.ExactCodeValidator.gateDescription_subroutineReady
        CommonGround.FiniteTransducers.rightEdgeRewindDescription_subroutineReady
        hstuck
    have hmaterialized :=
      CommonGround.SameHeadComposition.leftRightSeqDescription_stuckFromTape_of_left
        gateRewindDescription_subroutineReady
        SelfAppendMaterializer.description_subroutineReady
        hgateRewind
    have hbase :=
      CommonGround.SameHeadComposition.leftRightSeqDescription_stuckFromTape_of_left
        materializedDescription_subroutineReady hpair hmaterialized
    exact ⟨stuck, hbase, hcontiguous⟩

private theorem description_haltsWithOutput_of_valid
    {pairDecider : MachineDescription}
    (hpair : pairDecider.SubroutineReady) (reject : Bool)
    {code : Word MachineCodeSymbol}
    (hvalid : MachineDescription.DescriptionCodeValid code)
    {out : Word Bool}
    (hhalts : pairDecider.HaltsWithOutput
      (encodeCodeWordAsInput (List.append code code)) out) :
    (Description pairDecider reject).HaltsWithOutput
      (encodeCodeWordAsInput code) out := by
  apply haltsWithOutput_of_haltsFromTapeWithOutput
  exact
    MissingRejectCompletion.description_haltsFromTapeWithOutput_of_haltsFromTapeWithOutput
      (baseDescription_subroutineReady hpair) reject
      (baseDescription_haltsFromTapeWithOutput hpair hvalid hhalts)

/-- Every stopped decider for self-delimiting pair halting yields a checked
stopped decider for valid self-halting by finite self-append.  Malformed input
codes follow only the missing-transition completion and return the original
reject answer. -/
theorem stoppedDecidesCodeSelfHalting_of_stoppedDecidesCodePairHalting
    {pairDecider : MachineDescription} {reject accept : Bool}
    (hpair : StoppedDescriptionDecidesCodeLanguage
      pairDecider reject accept CodePairHaltingLanguage) :
    StoppedDescriptionDecidesCodeLanguage
      (Description pairDecider reject) reject accept
      CodeSelfHaltingLanguage := by
  have hpairReady : pairDecider.SubroutineReady :=
    ⟨hpair.wellFormed, hpair.haltTransitionFree⟩
  have hbaseReady := baseDescription_subroutineReady hpairReady
  have hdescriptionReady := description_subroutineReady hpairReady reject
  refine ⟨hdescriptionReady.2, hdescriptionReady.1, hpair.answers_ne, ?_⟩
  intro code
  constructor
  · intro hself
    have haccepts : MachineDescription.CodeAccepts code code :=
      (mem_codeSelfHaltingLanguage_iff code).1 hself
    rcases haccepts with ⟨decoded, hdecode, hwell, hhalt⟩
    have hvalid : MachineDescription.DescriptionCodeValid code :=
      ⟨decoded, hdecode, hwell⟩
    have hpairMem : List.append code code ∈ CodePairHaltingLanguage :=
      (selfAppend_mem_codePairHaltingLanguage_iff_codeAccepts hvalid).2
        ⟨decoded, hdecode, hwell, hhalt⟩
    exact description_haltsWithOutput_of_valid hpairReady reject hvalid
      ((hpair.correct (List.append code code)).1 hpairMem)
  · intro hnotSelf
    by_cases hvalid : MachineDescription.DescriptionCodeValid code
    · have hnotPair : ¬ List.append code code ∈ CodePairHaltingLanguage := by
        intro hpairMem
        have haccepts :=
          (selfAppend_mem_codePairHaltingLanguage_iff_codeAccepts hvalid).1
            hpairMem
        exact hnotSelf ((mem_codeSelfHaltingLanguage_iff code).2 haccepts)
      exact description_haltsWithOutput_of_valid hpairReady reject hvalid
        ((hpair.correct (List.append code code)).2 hnotPair)
    · rcases baseDescription_contiguousStuck_of_not_valid
          hpairReady hvalid with ⟨stuck, hstuck, hcontiguous⟩
      apply haltsWithOutput_of_haltsFromTapeWithOutput
      exact MissingRejectCompletion.description_haltsFromTapeWithOutput_reject_of_stuck
        hbaseReady reject hstuck hcontiguous

end PairHaltingReduction
end Computability
end FoC
