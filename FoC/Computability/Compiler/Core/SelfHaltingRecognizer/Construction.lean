import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.CodeAlphabetLowering
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.SelfAppendRunner
import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorConstruction
import FoC.Computability.Compiler.Core.CommonGround.FiniteTransducers.RightEdgeRewind
import FoC.Computability.Compiler.Core.CommonGround.SameHeadComposition
import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource
import FoC.Computability.SelfHaltingReferenceSpec

set_option doc.verso true

/-!
# Concrete finite self-halting recognizer

The exact validator rejects incomplete codes and prefix-plus-junk words.  A
right-edge rewind then restores the canonical encoded input, and the lowered
self-append runner invokes the unconditional finite universal-prefix machine
on {lit}`w ++ w`.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ConcreteRecognizer

open Languages
open MachineDescription

def codeRunner [DecidableEq state]
    (universal : TuringMachine MachineCodeSymbol state) :=
  SelfAppendRunner.machine (haltStoppedMachine universal)

def LoweredDescription [DecidableEq state]
    (universal : TuringMachine MachineCodeSymbol state) : MachineDescription :=
  CodeAlphabetLowering.lowerCodeAlphabetMachineDescription
    (codeRunner universal)

def TailDescription [DecidableEq state]
    (universal : TuringMachine MachineCodeSymbol state) : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    CommonGround.FiniteTransducers.rightEdgeRewindDescription
    (LoweredDescription universal)

def Description [DecidableEq state]
    (universal : TuringMachine MachineCodeSymbol state) : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    ExactCodeValidator.GateDescription (TailDescription universal)

theorem codeRunner_haltingTransitionsDisabled [DecidableEq state]
    (universal : TuringMachine MachineCodeSymbol state) :
    TuringMachine.HaltingTransitionsDisabled (codeRunner universal) :=
  SelfAppendRunner.machine_haltingTransitionsDisabled
    (haltStoppedMachine universal)
    (haltStoppedMachine_haltingTransitionsDisabled universal)

theorem loweredDescription_subroutineReady [DecidableEq state]
    (universal : TuringMachine MachineCodeSymbol state) :
    (LoweredDescription universal).SubroutineReady :=
  CodeAlphabetLowering.lowerCodeAlphabetMachineDescription_subroutineReady
    (codeRunner universal)

theorem tailDescription_subroutineReady [DecidableEq state]
    (universal : TuringMachine MachineCodeSymbol state) :
    (TailDescription universal).SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    CommonGround.FiniteTransducers.rightEdgeRewindDescription_subroutineReady
    (loweredDescription_subroutineReady universal)

theorem description_subroutineReady [DecidableEq state]
    (universal : TuringMachine MachineCodeSymbol state) :
    (Description universal).SubroutineReady :=
  CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
    ExactCodeValidator.gateDescription_subroutineReady
    (tailDescription_subroutineReady universal)

def validatedBoundaryTape (bits : Word Bool) : Tape Bool :=
  CommonGround.FiniteTransducers.tapeAtCells
    (bits.reverse.map some ++ [none]) [none]

private theorem validatorTarget_eq_validatedBoundary
    (stateCount start halt transitionCount : Nat)
    (rows : List TransitionDescription) :
    ValidatorDeterminismGate.targetTape
        stateCount start halt transitionCount rows =
      validatedBoundaryTape
        (encodeCodeWordAsInput
          (validatorHeaderFieldsCode stateCount start halt transitionCount
            (encodeTransitionsAppend rows []))) := by
  simp [validatedBoundaryTape, ValidatorDeterminismGate.targetTape,
    ValidatorDeterminismGate.sourceTape,
    validatorTransitionScannerHandoffTape,
    validatorTransitionScannerPrefix,
    validatorHeaderFieldsCode_eq_prefix_append,
    encodeTransitions, encodeCodeWordAsInput,
    DovetailInitialLayoutInitializer.tapeAtCells,
    CommonGround.FiniteTransducers.tapeAtCells]

private theorem gate_output_eq_validatedBoundary
    (code : Word MachineCodeSymbol) (output : Tape Bool)
    (hgate : ExactCodeValidator.GateDescription.HaltsFromTape
      (Tape.input (encodeCodeWordAsInput code)) output) :
    output = validatedBoundaryTape (encodeCodeWordAsInput code) := by
  rcases (ExactCodeValidator.gateDescription_haltsFromCode_iff
      code output).mp hgate with
    ⟨stateCount, start, halt, transitionCount, rows,
      hcode, _hcount, _hbounds, _hupper, houtput⟩
  calc
    output = ValidatorDeterminismGate.targetTape
        stateCount start halt transitionCount rows := houtput
    _ = validatedBoundaryTape
        (encodeCodeWordAsInput
          (validatorHeaderFieldsCode stateCount start halt transitionCount
            (encodeTransitionsAppend rows []))) :=
      validatorTarget_eq_validatedBoundary
        stateCount start halt transitionCount rows
    _ = validatedBoundaryTape (encodeCodeWordAsInput code) := by rw [hcode]

private theorem gate_haltsTo_validatedBoundary_iff
    (code : Word MachineCodeSymbol) :
    ExactCodeValidator.GateDescription.HaltsFromTape
        (Tape.input (encodeCodeWordAsInput code))
        (validatedBoundaryTape (encodeCodeWordAsInput code)) <->
      MachineDescription.DescriptionCodeValid code := by
  constructor
  · intro hgate
    exact
      (ExactCodeValidator.gateDescription_exists_haltsFromCode_iff_descriptionCodeValid
        code).mp
        ⟨_, hgate⟩
  · intro hvalid
    rcases
        (ExactCodeValidator.gateDescription_exists_haltsFromCode_iff_descriptionCodeValid
          code).mpr
          hvalid with
      ⟨output, hgate⟩
    have houtput := gate_output_eq_validatedBoundary code output hgate
    subst output
    exact hgate

private theorem valid_code_ne_nil
    {code : Word MachineCodeSymbol}
    (hvalid : MachineDescription.DescriptionCodeValid code) :
    code ≠ [] := by
  intro hnil
  subst code
  exact MachineDescription.not_descriptionCodeValid_nil hvalid

private theorem encoded_code_ne_nil_of_code_ne_nil
    {code : Word MachineCodeSymbol} (hcode : code ≠ []) :
    encodeCodeWordAsInput code ≠ [] := by
  cases code with
  | nil => contradiction
  | cons symbol rest =>
      cases symbol <;> simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput]

private theorem validatedBoundaryTape_bounce
    (bits : Word Bool) (hbits : bits ≠ []) :
    Tape.move Direction.right
        (Tape.move Direction.left (validatedBoundaryTape bits)) =
      validatedBoundaryTape bits := by
  rcases list_exists_append_singleton_of_ne_nil bits hbits with
    ⟨init, last, rfl⟩
  cases last <;>
    simp [validatedBoundaryTape,
      CommonGround.FiniteTransducers.tapeAtCells,
      List.reverse_append, Tape.move, Tape.moveLeft, Tape.moveRight]

private theorem rewind_haltsFrom_validatedBoundary
    (bits : Word Bool) (hbits : bits ≠ []) :
    CommonGround.FiniteTransducers.rightEdgeRewindDescription.HaltsFromTape
      (validatedBoundaryTape bits)
      (CommonGround.FiniteTransducers.rightEdgeRewindTargetTape bits []) := by
  rcases list_exists_append_singleton_of_ne_nil bits hbits with
    ⟨init, last, rfl⟩
  simpa [validatedBoundaryTape,
    CommonGround.FiniteTransducers.rightEdgeRewindTargetTape,
    List.reverse_append, List.map_append, List.append_assoc] using
    (CommonGround.FiniteTransducers.rightEdgeRewindDescription_haltsFrom_rightBoundaryBase_noDelimiter
        ([] : List (Option Bool)) init.reverse last
        ([] : List (Option Bool)))

private theorem rewindTargetTape_bounce (bits : Word Bool) :
    Tape.move Direction.right
        (Tape.move Direction.left
          (CommonGround.FiniteTransducers.rightEdgeRewindTargetTape bits [])) =
      CommonGround.FiniteTransducers.rightEdgeRewindTargetTape bits [] := by
  cases bits <;>
    simp [CommonGround.FiniteTransducers.rightEdgeRewindTargetTape,
      CommonGround.FiniteTransducers.tapeAtCells, Tape.move,
      Tape.moveLeft, Tape.moveRight]

private theorem rewindTargetTape_equiv_input (bits : Word Bool) :
    Tape.Equiv
      (CommonGround.FiniteTransducers.rightEdgeRewindTargetTape bits [])
      (Tape.input bits) := by
  cases bits <;>
    simp [CommonGround.FiniteTransducers.rightEdgeRewindTargetTape,
      CommonGround.FiniteTransducers.tapeAtCells, Tape.input,
      Tape.blank, Tape.Equiv, Tape.dropTrailingNone,
      FoC.Computability.dropTrailingNone_append_none]

private theorem haltsOnInput_iff_exists_haltsFromTape
    (D : MachineDescription) (input : Word Bool) :
    D.HaltsOnInput input <->
      exists output : Tape Bool,
        D.HaltsFromTape (Tape.input input) output := by
  constructor
  · rintro ⟨steps, hhalt⟩
    let output := (D.runConfig steps (D.initial input)).tape
    refine ⟨output, steps, ?_, rfl⟩
    simpa [MachineDescription.HaltsIn, MachineDescription.initial] using hhalt
  · rintro ⟨output, steps, hhalt, _houtput⟩
    exact ⟨steps, by
      simpa [MachineDescription.HaltsIn, MachineDescription.initial] using
        hhalt⟩

private theorem loweredDescription_haltsOnInput_iff
    [DecidableEq state]
    (universal : TuringMachine MachineCodeSymbol state)
    (code : Word MachineCodeSymbol) (hcode : code ≠ []) :
    (LoweredDescription universal).HaltsOnInput
        (encodeCodeWordAsInput code) <->
      universal.HaltsOnInput (Languages.Word.Concat code code) := by
  change
    (CodeAlphabetLowering.lowerCodeAlphabetMachineDescription
      (codeRunner universal)).HaltsOnInput
        (encodeCodeWordAsInput code) <->
      universal.HaltsOnInput (Languages.Word.Concat code code)
  rw [CodeAlphabetLowering.lowerCodeAlphabetMachineDescription_haltsOnInput_iff
      (codeRunner universal)
      (codeRunner_haltingTransitionsDisabled universal) code]
  cases code with
  | nil => contradiction
  | cons first rest =>
      exact SelfAppendRunner.haltedRunner_haltsOnInput_iff
        universal first rest

theorem description_haltsOnInput_iff [DecidableEq state]
    (universal : TuringMachine MachineCodeSymbol state)
    (code : Word MachineCodeSymbol) :
    (Description universal).HaltsOnInput (encodeCodeWordAsInput code) <->
      MachineDescription.DescriptionCodeValid code ∧
        universal.HaltsOnInput (Languages.Word.Concat code code) := by
  rw [haltsOnInput_iff_exists_haltsFromTape]
  constructor
  · rintro ⟨output, hdescription⟩
    rcases
        CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_inv
          ExactCodeValidator.gateDescription_subroutineReady
          (tailDescription_subroutineReady universal) hdescription with
      ⟨gateOutput, hgate, htail⟩
    have hvalid :=
      (ExactCodeValidator.gateDescription_exists_haltsFromCode_iff_descriptionCodeValid
        code).mp
        ⟨gateOutput, hgate⟩
    have hgateOutput := gate_output_eq_validatedBoundary code gateOutput hgate
    subst gateOutput
    have hcode := valid_code_ne_nil hvalid
    have hbits := encoded_code_ne_nil_of_code_ne_nil hcode
    rw [validatedBoundaryTape_bounce _ hbits] at htail
    rcases
        CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_inv
          CommonGround.FiniteTransducers.rightEdgeRewindDescription_subroutineReady
          (loweredDescription_subroutineReady universal) htail with
      ⟨rewindOutput, hrewind, hlower⟩
    have hrewindCanonical :=
      rewind_haltsFrom_validatedBoundary _ hbits
    have hrewindOutput : rewindOutput =
        CommonGround.FiniteTransducers.rightEdgeRewindTargetTape
          (encodeCodeWordAsInput code) [] :=
      MachineDescription.haltsFromTape_functional_of_haltTransitionFree
        CommonGround.FiniteTransducers.rightEdgeRewindDescription_subroutineReady.2
        hrewind hrewindCanonical
    subst rewindOutput
    rw [rewindTargetTape_bounce] at hlower
    rcases MachineDescription.HaltsFromTapeEquiv_of_input_equiv
        (rewindTargetTape_equiv_input (encodeCodeWordAsInput code))
        hlower with
      ⟨lowerOutput, hlowerCanonical, _hlowerOutput⟩
    have hlowerInput : (LoweredDescription universal).HaltsOnInput
        (encodeCodeWordAsInput code) :=
      (haltsOnInput_iff_exists_haltsFromTape _ _).mpr
        ⟨lowerOutput, hlowerCanonical⟩
    exact ⟨hvalid,
      (loweredDescription_haltsOnInput_iff universal code hcode).mp
        hlowerInput⟩
  · rintro ⟨hvalid, huniversal⟩
    have hcode := valid_code_ne_nil hvalid
    have hbits := encoded_code_ne_nil_of_code_ne_nil hcode
    have hlowerInput : (LoweredDescription universal).HaltsOnInput
        (encodeCodeWordAsInput code) :=
      (loweredDescription_haltsOnInput_iff universal code hcode).mpr
        huniversal
    rcases (haltsOnInput_iff_exists_haltsFromTape _ _).mp hlowerInput with
      ⟨lowerOutput, hlowerCanonical⟩
    rcases MachineDescription.HaltsFromTapeEquiv_of_input_equiv
        (Tape.Equiv.symm
          (rewindTargetTape_equiv_input (encodeCodeWordAsInput code)))
        hlowerCanonical with
      ⟨lowerOutput', hlowerTarget, _hlowerOutput⟩
    have hrewind := rewind_haltsFrom_validatedBoundary _ hbits
    have htail : (TailDescription universal).HaltsFromTape
        (validatedBoundaryTape (encodeCodeWordAsInput code)) lowerOutput' :=
      CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
          CommonGround.FiniteTransducers.rightEdgeRewindDescription_subroutineReady
          (loweredDescription_subroutineReady universal)
          hrewind (rewindTargetTape_bounce _) hlowerTarget
    have hgate :=
      (gate_haltsTo_validatedBoundary_iff code).mpr hvalid
    refine ⟨lowerOutput', ?_⟩
    exact CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
        ExactCodeValidator.gateDescription_subroutineReady
        (tailDescription_subroutineReady universal)
        hgate (validatedBoundaryTape_bounce _ hbits) htail

theorem recognizesCodeSelfHalting [DecidableEq state]
    (universal : TuringMachine MachineCodeSymbol state)
    (hspec : CodeUniversalPrefixMachineSpec universal) :
    DescriptionRecognizesCodeLanguage
      (Description universal) CodeSelfHaltingLanguage := by
  refine ⟨(description_subroutineReady universal).1, ?_⟩
  intro code
  change (Description universal).HaltsOnInput
      (encodeCodeWordAsInput code) <-> code ∈ CodeSelfHaltingLanguage
  rw [description_haltsOnInput_iff universal code, hspec]
  exact (mem_codeSelfHalting_iff_valid_and_codePrefixAccepts_selfAppend
    code).symm

end ConcreteRecognizer

/-- Unconditional M7 frontier: the exact valid self-halting code language has
a concrete well-formed finite Boolean description recognizer. -/
theorem concreteSelfHaltingRecognizerConstruction :
    DescriptionRecognizableCodeLanguage CodeSelfHaltingLanguage := by
  rcases codeUniversalPrefixRunnerConstruction with
    ⟨state, universal, huniversal⟩
  let indexed := TuringMachine.indexed universal
  have hindexed : CodeUniversalPrefixMachineSpec indexed := by
    intro encoded
    exact (TuringMachine.indexed_haltsOnInput_iff universal encoded).trans
      (huniversal encoded)
  exact ⟨ConcreteRecognizer.Description indexed,
    ConcreteRecognizer.recognizesCodeSelfHalting indexed hindexed⟩

end SelfHaltingRecognizer
end Computability
end FoC
