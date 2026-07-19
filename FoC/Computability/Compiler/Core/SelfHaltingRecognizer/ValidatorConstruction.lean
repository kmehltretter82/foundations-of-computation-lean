import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorBooleanCloseout

set_option doc.verso true

/-!
# Exact-code validator construction

The five recognition gates are composed in their exact physical currencies:
token alignment hands left to the fixed-header parser, and the parser,
transition scanner, suffix check, and determinism check use same-head
left/right bounces.  The generic Boolean closeout then maps the successful
recognizer halt to {lit}`true` and every concrete contiguous stuck endpoint to
{lit}`false`.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ExactCodeValidator

open Languages
open MachineDescription

open EncRewriters.CanonicalLayouts.DovetailLayoutScanner
open DovetailInitialLayoutInitializer

/-- Token alignment followed by the fixed header and unary-field parser. -/
def TokenHeaderDescription : MachineDescription :=
  seqSubroutine ExactCodeValidatorTokenGateDescription
    ValidatorHeaderParserDescription Direction.left

/-- Add the complete transition scanner at the exact header handoff. -/
def ThroughScannerDescription : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    TokenHeaderDescription ValidatorTransitionScannerConstruction.Description

/-- Add the exact-suffix gate. -/
def ThroughSuffixDescription : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    ThroughScannerDescription ExactCodeValidatorSuffixGateDescription

/-- Five-gate recognizer for complete well-formed description codes. -/
def GateDescription : MachineDescription :=
  CommonGround.SameHeadComposition.leftRightSeqDescription
    ThroughSuffixDescription ValidatorDeterminismGate.Description

/-- Public Boolean decider: success emits {lit}`true`, every rejected finite
path emits {lit}`false`. -/
def Description : MachineDescription :=
  ValidatorBooleanCloseout.Description GateDescription

theorem tokenHeaderDescription_subroutineReady :
    TokenHeaderDescription.SubroutineReady := by
  exact seqSubroutine_subroutineReady
    exactCodeValidatorTokenGateDescription_subroutineReady
    validatorHeaderParserDescription_subroutineReady

theorem throughScannerDescription_subroutineReady :
    ThroughScannerDescription.SubroutineReady := by
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
      tokenHeaderDescription_subroutineReady
      ValidatorTransitionScannerConstruction.description_subroutineReady

theorem throughSuffixDescription_subroutineReady :
    ThroughSuffixDescription.SubroutineReady := by
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
      throughScannerDescription_subroutineReady
      exactCodeValidatorSuffixGateDescription_subroutineReady

theorem gateDescription_subroutineReady : GateDescription.SubroutineReady := by
  exact
    CommonGround.SameHeadComposition.leftRightSeqDescription_subroutineReady
      throughSuffixDescription_subroutineReady
      ValidatorDeterminismGate.description_subroutineReady

theorem description_subroutineReady : Description.SubroutineReady := by
  exact ValidatorBooleanCloseout.description_subroutineReady
    gateDescription_subroutineReady

/-- The token-gate left handoff is exactly the padded header-parser source. -/
theorem tokenHandoff_move_left_eq_headerStart
    (symbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    Tape.move Direction.left
        (codeWordAlignedHandoffTape
          (encodeCodeWordAsInput (symbol :: rest))) =
      validatorHeaderCodePaddedStartTape (symbol :: rest) := by
  cases symbol <;>
    simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput,
      validatorHeaderCodePaddedStartTape, validatorHeaderCodeCells,
      move_left_codeWordAlignedHandoffTape_cons]

/-- The first two phases either parse the fixed header exactly or stop at a
contiguous rejecting endpoint. -/
theorem tokenHeaderDescription_haltsOrContiguousStuckFromCode
    (code : Word MachineCodeSymbol) :
    (exists output : Tape Bool,
      TokenHeaderDescription.HaltsFromTape
        (Tape.input (encodeCodeWordAsInput code)) output) ∨
    (exists stuck : Tape Bool,
      TokenHeaderDescription.StuckFromTape
          (Tape.input (encodeCodeWordAsInput code)) stuck ∧
        ContiguousTape stuck) := by
  cases code with
  | nil =>
      let stuck : Tape Bool := Tape.move Direction.right
        (Tape.move Direction.left (Tape.input ([] : Word Bool)))
      have htoken : ExactCodeValidatorTokenGateDescription.StuckFromTape
          (Tape.input []) stuck := by
        exact exactCodeValidatorTokenGateDescription_stuckFromTape_nil
      exact Or.inr ⟨stuck, by
        simpa [TokenHeaderDescription, encodeCodeWordAsInput] using
          seqSubroutine_stuckFromTape_of_left
            exactCodeValidatorTokenGateDescription_subroutineReady
            validatorHeaderParserDescription_subroutineReady htoken,
        exactCodeValidatorTokenGateDescription_stuckTape_nil_contiguous⟩
  | cons symbol rest =>
      let bits := encodeCodeWordAsInput (symbol :: rest)
      let middle := codeWordAlignedHandoffTape bits
      have htoken : ExactCodeValidatorTokenGateDescription.HaltsFromTape
          (Tape.input bits) middle := by
        exact codeWordAlignedPreScannerDescription_haltsFromTape symbol rest
      have hbridge : Tape.move Direction.left middle =
          validatorHeaderCodePaddedStartTape (symbol :: rest) := by
        exact tokenHandoff_move_left_eq_headerStart symbol rest
      rcases validatorHeaderParserDescription_haltsOrStuckFromCode
          (symbol :: rest) with hheader | hheader
      · rcases hheader with ⟨output, hheader⟩
        exact Or.inl ⟨output,
          CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
            exactCodeValidatorTokenGateDescription_subroutineReady
            validatorHeaderParserDescription_subroutineReady
            htoken hbridge hheader⟩
      · rcases hheader with ⟨stuck, hheader⟩
        have hheader' : ValidatorHeaderParserDescription.StuckFromTape
            (Tape.move Direction.left middle) stuck := by
          simpa [hbridge] using hheader
        exact Or.inr ⟨stuck,
          seqSubroutine_stuckFromTape_of_right
            exactCodeValidatorTokenGateDescription_subroutineReady
            validatorHeaderParserDescription_subroutineReady
            htoken hheader',
          validatorHeaderParserDescription_contiguous_of_stuckFromCode
            (symbol :: rest) stuck hheader⟩

/-- Exact closed characterization of the two-phase header front end. -/
theorem tokenHeaderDescription_haltsFromCode_iff
    (code : Word MachineCodeSymbol) (output : Tape Bool) :
    TokenHeaderDescription.HaltsFromTape
        (Tape.input (encodeCodeWordAsInput code)) output <->
      exists stateCount start halt transitionCount : Nat,
      exists suffix : Word MachineCodeSymbol,
        code = validatorHeaderFieldsCode
            stateCount start halt transitionCount suffix ∧
          output = validatorHeaderFieldsHandoffTape
            stateCount start halt transitionCount suffix := by
  constructor
  · intro hhalts
    rcases seqSubroutine_haltsFromTape_closed_exists_mid
        exactCodeValidatorTokenGateDescription_subroutineReady
        validatorHeaderParserDescription_subroutineReady hhalts with
      ⟨middle, htoken, hheader⟩
    rcases
        (exactCodeValidatorTokenGateDescription_haltsFromTape_iff
          (encodeCodeWordAsInput code) middle).1 htoken with
      ⟨symbol, rest, hbits, hmiddle⟩
    have hcode : code = symbol :: rest :=
      encodeCodeWordAsInput_injective hbits
    subst code
    subst middle
    rw [tokenHandoff_move_left_eq_headerStart] at hheader
    exact
      (validatorHeaderParserDescription_haltsFromCode_iff
        (symbol :: rest) output).1 hheader
  · rintro
      ⟨stateCount, start, halt, transitionCount, suffix, rfl, rfl⟩
    let code := validatorHeaderFieldsCode
      stateCount start halt transitionCount suffix
    have hcode : exists rest : Word MachineCodeSymbol,
        code = MachineCodeSymbol.header :: rest := by
      exact ⟨_, rfl⟩
    rcases hcode with ⟨rest, hcode⟩
    have htoken : ExactCodeValidatorTokenGateDescription.HaltsFromTape
        (Tape.input (encodeCodeWordAsInput code))
        (codeWordAlignedHandoffTape (encodeCodeWordAsInput code)) := by
      rw [hcode]
      exact codeWordAlignedPreScannerDescription_haltsFromTape .header rest
    have hbridge :
        Tape.move Direction.left
            (codeWordAlignedHandoffTape (encodeCodeWordAsInput code)) =
          validatorHeaderFieldsPaddedStartTape
            stateCount start halt transitionCount suffix := by
      calc
        Tape.move Direction.left
              (codeWordAlignedHandoffTape (encodeCodeWordAsInput code)) =
            validatorHeaderCodePaddedStartTape (.header :: rest) := by
          rw [hcode]
          exact tokenHandoff_move_left_eq_headerStart .header rest
        _ = validatorHeaderCodePaddedStartTape code := by rw [hcode]
        _ = validatorHeaderFieldsPaddedStartTape
              stateCount start halt transitionCount suffix := by
          dsimp [code]
          exact validatorHeaderCodePaddedStartTape_fields
            stateCount start halt transitionCount suffix
    exact
      CommonGround.SeqComposition.seqSubroutine_haltsFromTape_of_haltsFromTape_eq
        exactCodeValidatorTokenGateDescription_subroutineReady
        validatorHeaderParserDescription_subroutineReady
        htoken hbridge
        (validatorHeaderParserDescription_haltsFromTape
          stateCount start halt transitionCount suffix)

/-- Adding the transition scanner preserves the total halt-or-contiguous-stuck
outcome on every canonical code word. -/
theorem throughScannerDescription_haltsOrContiguousStuckFromCode
    (code : Word MachineCodeSymbol) :
    (exists output : Tape Bool,
      ThroughScannerDescription.HaltsFromTape
        (Tape.input (encodeCodeWordAsInput code)) output) ∨
    (exists stuck : Tape Bool,
      ThroughScannerDescription.StuckFromTape
          (Tape.input (encodeCodeWordAsInput code)) stuck ∧
        ContiguousTape stuck) := by
  rcases tokenHeaderDescription_haltsOrContiguousStuckFromCode code with
    hfront | hfront
  · rcases hfront with ⟨middle, hfront⟩
    rcases (tokenHeaderDescription_haltsFromCode_iff code middle).1 hfront with
      ⟨stateCount, start, halt, transitionCount, tokens, hcode, hmiddle⟩
    have hfrontExact : TokenHeaderDescription.HaltsFromTape
        (Tape.input (encodeCodeWordAsInput code))
        (validatorTransitionScannerStartTape
          stateCount start halt transitionCount tokens) := by
      simpa [validatorTransitionScannerStartTape, hmiddle] using hfront
    rcases ValidatorTransitionScannerConstruction.haltsOrContiguousStuckFromTape
        stateCount start halt transitionCount tokens with hscanner | hscanner
    · rcases hscanner with ⟨output, hscanner⟩
      exact Or.inl ⟨output,
        CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
          tokenHeaderDescription_subroutineReady
          ValidatorTransitionScannerConstruction.description_subroutineReady
          hfrontExact
          (ValidatorTransitionScannerConstruction.scannerStartTape_move_right_left
            stateCount start halt transitionCount tokens)
          hscanner⟩
    · rcases hscanner with ⟨stuck, hscanner, hcontiguous⟩
      exact Or.inr ⟨stuck,
        CommonGround.SameHeadComposition.leftRightSeqDescription_stuckFromTape_of_right
          tokenHeaderDescription_subroutineReady
          ValidatorTransitionScannerConstruction.description_subroutineReady
          hfrontExact
          (ValidatorTransitionScannerConstruction.scannerStartTape_move_right_left
            stateCount start halt transitionCount tokens)
          hscanner,
        hcontiguous⟩
  · rcases hfront with ⟨stuck, hfront, hcontiguous⟩
    exact Or.inr ⟨stuck,
      CommonGround.SameHeadComposition.leftRightSeqDescription_stuckFromTape_of_left
        tokenHeaderDescription_subroutineReady
        ValidatorTransitionScannerConstruction.description_subroutineReady
        hfront,
      hcontiguous⟩

/-- Exact closed characterization after parsing and checking the counted
transition prefix. -/
theorem throughScannerDescription_haltsFromCode_iff
    (code : Word MachineCodeSymbol) (output : Tape Bool) :
    ThroughScannerDescription.HaltsFromTape
        (Tape.input (encodeCodeWordAsInput code)) output <->
      exists stateCount start halt transitionCount : Nat,
      exists rows : List TransitionDescription,
      exists suffix : Word MachineCodeSymbol,
        code = validatorHeaderFieldsCode stateCount start halt
            transitionCount (encodeTransitionsAppend rows suffix) ∧
          transitionCount = rows.length ∧
          validatorStateBoundsBool stateCount start halt rows = true ∧
          output = validatorTransitionScannerHandoffTape
            stateCount start halt transitionCount rows suffix := by
  constructor
  · intro hhalts
    rcases
        CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_inv
          tokenHeaderDescription_subroutineReady
          ValidatorTransitionScannerConstruction.description_subroutineReady
          hhalts with
      ⟨middle, hfront, hscanner⟩
    rcases (tokenHeaderDescription_haltsFromCode_iff code middle).1 hfront with
      ⟨stateCount, start, halt, transitionCount, tokens, hcode, hmiddle⟩
    subst middle
    change ValidatorTransitionScannerConstruction.Description.HaltsFromTape
      (Tape.move Direction.right
        (Tape.move Direction.left
          (validatorTransitionScannerStartTape
            stateCount start halt transitionCount tokens))) output at hscanner
    rw [ValidatorTransitionScannerConstruction.scannerStartTape_move_right_left]
      at hscanner
    have haccept :=
      ValidatorTransitionScannerConstruction.accepts_of_haltsFromTape
        stateCount start halt transitionCount tokens hscanner
    rcases haccept with ⟨rows, suffix, hdecode, hboundsBool⟩
    rcases decodeTransitions_eq_some_encodeTransitionsAppend hdecode with
      ⟨hcount, htokens⟩
    have hbounds := (validatorStateBoundsBool_eq_true_iff
      stateCount start halt rows).1 hboundsBool
    have hcanonical :
        ValidatorTransitionScannerConstruction.Description.HaltsFromTape
          (validatorTransitionScannerStartTape
            stateCount start halt transitionCount tokens)
          (validatorTransitionScannerHandoffTape
            stateCount start halt transitionCount rows suffix) := by
      rw [htokens]
      exact ValidatorTransitionScannerConstruction.haltsFromTape_encoded
        stateCount start halt transitionCount rows suffix
        hbounds.1 hbounds.2.1 hbounds.2.2.1 hcount hbounds.2.2.2
    have houtput : output = validatorTransitionScannerHandoffTape
        stateCount start halt transitionCount rows suffix :=
      MachineDescription.haltsFromTape_functional_of_haltTransitionFree
        ValidatorTransitionScannerConstruction.description_subroutineReady.2
        hscanner hcanonical
    refine ⟨stateCount, start, halt, transitionCount, rows, suffix, ?_,
      hcount, hboundsBool, houtput⟩
    rw [hcode, htokens]
  · rintro ⟨stateCount, start, halt, transitionCount, rows, suffix,
      rfl, hcount, hbounds, rfl⟩
    have hfront := (tokenHeaderDescription_haltsFromCode_iff
      (validatorHeaderFieldsCode stateCount start halt transitionCount
        (encodeTransitionsAppend rows suffix))
      (validatorTransitionScannerStartTape
        stateCount start halt transitionCount
          (encodeTransitionsAppend rows suffix))).2
      ⟨stateCount, start, halt, transitionCount,
        encodeTransitionsAppend rows suffix, rfl, rfl⟩
    have hbounds := (validatorStateBoundsBool_eq_true_iff
      stateCount start halt rows).1 hbounds
    exact
      CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
        tokenHeaderDescription_subroutineReady
        ValidatorTransitionScannerConstruction.description_subroutineReady
        hfront
        (ValidatorTransitionScannerConstruction.scannerStartTape_move_right_left
          stateCount start halt transitionCount
            (encodeTransitionsAppend rows suffix))
        (ValidatorTransitionScannerConstruction.haltsFromTape_encoded
          stateCount start halt transitionCount rows suffix
          hbounds.1 hbounds.2.1 hbounds.2.2.1 hcount hbounds.2.2.2)

/-- Adding the exact-suffix gate preserves total halt-or-contiguous-stuck
behavior. -/
theorem throughSuffixDescription_haltsOrContiguousStuckFromCode
    (code : Word MachineCodeSymbol) :
    (exists output : Tape Bool,
      ThroughSuffixDescription.HaltsFromTape
        (Tape.input (encodeCodeWordAsInput code)) output) ∨
    (exists stuck : Tape Bool,
      ThroughSuffixDescription.StuckFromTape
          (Tape.input (encodeCodeWordAsInput code)) stuck ∧
        ContiguousTape stuck) := by
  rcases throughScannerDescription_haltsOrContiguousStuckFromCode code with
    hfront | hfront
  · rcases hfront with ⟨middle, hfront⟩
    rcases (throughScannerDescription_haltsFromCode_iff code middle).1 hfront
        with
      ⟨stateCount, start, halt, transitionCount, rows, suffix,
        _hcode, _hcount, _hbounds, hmiddle⟩
    have hfrontExact : ThroughScannerDescription.HaltsFromTape
        (Tape.input (encodeCodeWordAsInput code))
        (validatorTransitionScannerHandoffTape
          stateCount start halt transitionCount rows suffix) := by
      simpa [hmiddle] using hfront
    rcases
        exactCodeValidatorSuffixGateDescription_haltsOrContiguousStuckFromTape
          stateCount start halt transitionCount rows suffix with
      hsuffix | hsuffix
    · rcases hsuffix with ⟨output, hsuffix⟩
      exact Or.inl ⟨output,
        CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
          throughScannerDescription_subroutineReady
          exactCodeValidatorSuffixGateDescription_subroutineReady
          hfrontExact
          (validatorTransitionScannerHandoffTape_move_right_left
            stateCount start halt transitionCount rows suffix)
          hsuffix⟩
    · rcases hsuffix with ⟨stuck, hsuffix, hcontiguous⟩
      exact Or.inr ⟨stuck,
        CommonGround.SameHeadComposition.leftRightSeqDescription_stuckFromTape_of_right
          throughScannerDescription_subroutineReady
          exactCodeValidatorSuffixGateDescription_subroutineReady
          hfrontExact
          (validatorTransitionScannerHandoffTape_move_right_left
            stateCount start halt transitionCount rows suffix)
          hsuffix,
        hcontiguous⟩
  · rcases hfront with ⟨stuck, hfront, hcontiguous⟩
    exact Or.inr ⟨stuck,
      CommonGround.SameHeadComposition.leftRightSeqDescription_stuckFromTape_of_left
        throughScannerDescription_subroutineReady
        exactCodeValidatorSuffixGateDescription_subroutineReady hfront,
      hcontiguous⟩

/-- Exact closed characterization after enforcing an empty decoded suffix. -/
theorem throughSuffixDescription_haltsFromCode_iff
    (code : Word MachineCodeSymbol) (output : Tape Bool) :
    ThroughSuffixDescription.HaltsFromTape
        (Tape.input (encodeCodeWordAsInput code)) output <->
      exists stateCount start halt transitionCount : Nat,
      exists rows : List TransitionDescription,
        code = validatorHeaderFieldsCode stateCount start halt
            transitionCount (encodeTransitionsAppend rows []) ∧
          transitionCount = rows.length ∧
          validatorStateBoundsBool stateCount start halt rows = true ∧
          output = validatorTransitionScannerHandoffTape
            stateCount start halt transitionCount rows [] := by
  constructor
  · intro hhalts
    rcases
        CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_inv
          throughScannerDescription_subroutineReady
          exactCodeValidatorSuffixGateDescription_subroutineReady hhalts with
      ⟨middle, hfront, hsuffix⟩
    rcases (throughScannerDescription_haltsFromCode_iff code middle).1 hfront
        with
      ⟨stateCount, start, halt, transitionCount, rows, suffix,
        hcode, hcount, hbounds, hmiddle⟩
    subst middle
    change ExactCodeValidatorSuffixGateDescription.HaltsFromTape
      (Tape.move Direction.right
        (Tape.move Direction.left
          (validatorTransitionScannerHandoffTape
            stateCount start halt transitionCount rows suffix))) output
      at hsuffix
    rw [validatorTransitionScannerHandoffTape_move_right_left] at hsuffix
    rcases
        (exactCodeValidatorSuffixGateDescription_haltsFromTape_iff
          stateCount start halt transitionCount rows suffix output).1
          hsuffix with
      ⟨hsuffixNil, houtput⟩
    subst suffix
    exact ⟨stateCount, start, halt, transitionCount, rows,
      hcode, hcount, hbounds, houtput⟩
  · rintro ⟨stateCount, start, halt, transitionCount, rows,
      rfl, hcount, hbounds, rfl⟩
    have hfront := (throughScannerDescription_haltsFromCode_iff
      (validatorHeaderFieldsCode stateCount start halt transitionCount
        (encodeTransitionsAppend rows []))
      (validatorTransitionScannerHandoffTape
        stateCount start halt transitionCount rows [])).2
      ⟨stateCount, start, halt, transitionCount, rows, [],
        rfl, hcount, hbounds, rfl⟩
    exact
      CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
        throughScannerDescription_subroutineReady
        exactCodeValidatorSuffixGateDescription_subroutineReady
        hfront
        (validatorTransitionScannerHandoffTape_move_right_left
          stateCount start halt transitionCount rows [])
        (exactCodeValidatorSuffixGateDescription_haltsFromTape_nil
          stateCount start halt transitionCount rows)

/-- The full five-gate recognizer is total up to a contiguous stuck endpoint
on every canonical code word. -/
theorem gateDescription_haltsOrContiguousStuckFromCode
    (code : Word MachineCodeSymbol) :
    (exists output : Tape Bool,
      GateDescription.HaltsFromTape
        (Tape.input (encodeCodeWordAsInput code)) output) ∨
    (exists stuck : Tape Bool,
      GateDescription.StuckFromTape
          (Tape.input (encodeCodeWordAsInput code)) stuck ∧
        ContiguousTape stuck) := by
  rcases throughSuffixDescription_haltsOrContiguousStuckFromCode code with
    hfront | hfront
  · rcases hfront with ⟨middle, hfront⟩
    rcases (throughSuffixDescription_haltsFromCode_iff code middle).1 hfront
        with
      ⟨stateCount, start, halt, transitionCount, rows,
        _hcode, _hcount, _hbounds, hmiddle⟩
    have hfrontExact : ThroughSuffixDescription.HaltsFromTape
        (Tape.input (encodeCodeWordAsInput code))
        (ValidatorDeterminismGate.sourceTape
          stateCount start halt transitionCount rows) := by
      simpa [ValidatorDeterminismGate.sourceTape, hmiddle] using hfront
    rcases ValidatorDeterminismGate.haltsOrContiguousStuckFromTape
        stateCount start halt transitionCount rows with
      hdet | hdet
    · rcases hdet with ⟨output, hdet⟩
      exact Or.inl ⟨output,
        CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
          throughSuffixDescription_subroutineReady
          ValidatorDeterminismGate.description_subroutineReady
          hfrontExact
          (by
            simpa [ValidatorDeterminismGate.sourceTape] using
              validatorTransitionScannerHandoffTape_move_right_left
                stateCount start halt transitionCount rows [])
          hdet⟩
    · rcases hdet with ⟨stuck, hdet, hcontiguous⟩
      exact Or.inr ⟨stuck,
        CommonGround.SameHeadComposition.leftRightSeqDescription_stuckFromTape_of_right
          throughSuffixDescription_subroutineReady
          ValidatorDeterminismGate.description_subroutineReady
          hfrontExact
          (by
            simpa [ValidatorDeterminismGate.sourceTape] using
              validatorTransitionScannerHandoffTape_move_right_left
                stateCount start halt transitionCount rows [])
          hdet,
        hcontiguous⟩
  · rcases hfront with ⟨stuck, hfront, hcontiguous⟩
    exact Or.inr ⟨stuck,
      CommonGround.SameHeadComposition.leftRightSeqDescription_stuckFromTape_of_left
        throughSuffixDescription_subroutineReady
        ValidatorDeterminismGate.description_subroutineReady hfront,
      hcontiguous⟩

/-- Exact closed characterization of the five-gate recognizer. -/
theorem gateDescription_haltsFromCode_iff
    (code : Word MachineCodeSymbol) (output : Tape Bool) :
    GateDescription.HaltsFromTape
        (Tape.input (encodeCodeWordAsInput code)) output <->
      exists stateCount start halt transitionCount : Nat,
      exists rows : List TransitionDescription,
        code = validatorHeaderFieldsCode stateCount start halt
            transitionCount (encodeTransitionsAppend rows []) ∧
          transitionCount = rows.length ∧
          validatorStateBoundsBool stateCount start halt rows = true ∧
          ValidatorDeterminismGate.transitionUpperPairsBool rows = true ∧
          output = ValidatorDeterminismGate.targetTape
            stateCount start halt transitionCount rows := by
  constructor
  · intro hhalts
    rcases
        CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_inv
          throughSuffixDescription_subroutineReady
          ValidatorDeterminismGate.description_subroutineReady hhalts with
      ⟨middle, hfront, hdet⟩
    rcases (throughSuffixDescription_haltsFromCode_iff code middle).1 hfront
        with
      ⟨stateCount, start, halt, transitionCount, rows,
        hcode, hcount, hbounds, hmiddle⟩
    subst middle
    change ValidatorDeterminismGate.Description.HaltsFromTape
      (Tape.move Direction.right
        (Tape.move Direction.left
          (ValidatorDeterminismGate.sourceTape
            stateCount start halt transitionCount rows))) output at hdet
    rw [show Tape.move Direction.right
          (Tape.move Direction.left
            (ValidatorDeterminismGate.sourceTape
              stateCount start halt transitionCount rows)) =
        ValidatorDeterminismGate.sourceTape
          stateCount start halt transitionCount rows by
      simpa [ValidatorDeterminismGate.sourceTape] using
        validatorTransitionScannerHandoffTape_move_right_left
          stateCount start halt transitionCount rows []] at hdet
    rcases
        (ValidatorDeterminismGate.haltsFromTape_iff_upperPairs_and_target
          stateCount start halt transitionCount rows output).1 hdet with
      ⟨hupper, houtput⟩
    exact ⟨stateCount, start, halt, transitionCount, rows,
      hcode, hcount, hbounds, hupper, houtput⟩
  · rintro ⟨stateCount, start, halt, transitionCount, rows,
      rfl, hcount, hbounds, hupper, rfl⟩
    have hfront := (throughSuffixDescription_haltsFromCode_iff
      (validatorHeaderFieldsCode stateCount start halt transitionCount
        (encodeTransitionsAppend rows []))
      (ValidatorDeterminismGate.sourceTape
        stateCount start halt transitionCount rows)).2
      ⟨stateCount, start, halt, transitionCount, rows,
        rfl, hcount, hbounds, rfl⟩
    exact
      CommonGround.SameHeadComposition.leftRightSeqDescription_haltsFromTape_of_haltsFromTape
        throughSuffixDescription_subroutineReady
        ValidatorDeterminismGate.description_subroutineReady
        hfront
        (by
          simpa [ValidatorDeterminismGate.sourceTape] using
            validatorTransitionScannerHandoffTape_move_right_left
              stateCount start halt transitionCount rows [])
        (ValidatorDeterminismGate.haltsFromTape_of_upperPairs
          stateCount start halt transitionCount rows hupper)

private theorem transitionUpperPairsBool_eq_true_of_deterministic
    (rows : List TransitionDescription)
    (hdet : forall left right : TransitionDescription,
      left ∈ rows -> right ∈ rows ->
        TransitionDescription.SameKey left right ->
          TransitionDescription.SameAction left right) :
    ValidatorDeterminismGate.transitionUpperPairsBool rows = true := by
  apply
    (ValidatorDeterminismGate.transitionUpperPairsBool_eq_true_iff rows).2
  apply List.all_eq_true.mpr
  intro left hleft
  apply List.all_eq_true.mpr
  intro right hright
  exact (transitionDeterministicPairBool_eq_true_iff left right).2
    (hdet left right hleft hright)

/-- The five-gate recognizer halts on exactly the complete well-formed
description codes. -/
theorem gateDescription_exists_haltsFromCode_iff_descriptionCodeValid
    (code : Word MachineCodeSymbol) :
    (exists output : Tape Bool,
      GateDescription.HaltsFromTape
        (Tape.input (encodeCodeWordAsInput code)) output) <->
      MachineDescription.DescriptionCodeValid code := by
  constructor
  · rintro ⟨output, hhalts⟩
    rcases (gateDescription_haltsFromCode_iff code output).1 hhalts with
      ⟨stateCount, start, halt, transitionCount, rows,
        hcode, hcount, hboundsBool, hupper, _houtput⟩
    subst transitionCount
    let decoded : MachineDescription :=
      { stateCount := stateCount
        start := start
        halt := halt
        transitions := rows }
    have hcodeDecoded : code = MachineDescription.encodeDescription decoded := by
      rw [hcode]
      simp [decoded, validatorHeaderFieldsCode,
        MachineDescription.encodeDescription,
        MachineDescription.encodeDescriptionAppend]
    have hbounds := (validatorStateBoundsBool_eq_true_iff
      stateCount start halt rows).1 hboundsBool
    have hdet := transition_deterministic_of_all
      ((ValidatorDeterminismGate.transitionUpperPairsBool_eq_true_iff rows).1
        hupper)
    have hwell : decoded.WellFormed := by
      exact ⟨hbounds.1, hbounds.2.1, hbounds.2.2.1,
        hbounds.2.2.2, hdet⟩
    exact
      (MachineDescription.descriptionCodeValid_iff_exists_encodeDescription_wellFormed
        code).2 ⟨decoded, hcodeDecoded, hwell⟩
  · intro hvalid
    rcases
        (MachineDescription.descriptionCodeValid_iff_exists_encodeDescription_wellFormed
          code).1 hvalid with
      ⟨decoded, hcode, hwell⟩
    let stateCount := decoded.stateCount
    let start := decoded.start
    let halt := decoded.halt
    let rows := decoded.transitions
    have hbounds : validatorStateBoundsBool
        stateCount start halt rows = true := by
      apply (validatorStateBoundsBool_eq_true_iff
        stateCount start halt rows).2
      exact ⟨hwell.1, hwell.2.1, hwell.2.2.1, hwell.2.2.2.1⟩
    have hupper : ValidatorDeterminismGate.transitionUpperPairsBool rows =
        true :=
      transitionUpperPairsBool_eq_true_of_deterministic rows hwell.2.2.2.2
    have hcodeShape : code = validatorHeaderFieldsCode
        stateCount start halt rows.length
          (encodeTransitionsAppend rows []) := by
      rw [hcode]
      simp [stateCount, start, halt, rows,
        validatorHeaderFieldsCode, MachineDescription.encodeDescription,
        MachineDescription.encodeDescriptionAppend]
    exact ⟨ValidatorDeterminismGate.targetTape
        stateCount start halt rows.length rows,
      (gateDescription_haltsFromCode_iff code _).2
        ⟨stateCount, start, halt, rows.length, rows,
          hcodeShape, rfl, hbounds, hupper, rfl⟩⟩

/-- Every successful five-gate run ends on a contiguous physical window, so
the Boolean closeout can rewind it without imposing a canonical tape
representative. -/
theorem gateDescription_contiguous_of_haltsFromCode
    (code : Word MachineCodeSymbol) (output : Tape Bool)
    (hhalts : GateDescription.HaltsFromTape
      (Tape.input (encodeCodeWordAsInput code)) output) :
    ContiguousTape output := by
  rcases (gateDescription_haltsFromCode_iff code output).1 hhalts with
    ⟨stateCount, start, halt, transitionCount, rows,
      _hcode, _hcount, _hbounds, _hupper, houtput⟩
  subst output
  simpa [ValidatorDeterminismGate.targetTape,
    ValidatorDeterminismGate.sourceTape] using
      validatorTransitionScannerHandoffTape_contiguous
        stateCount start halt transitionCount rows []

private theorem haltsWithOutput_of_haltsFromTapeWithOutput
    {D : MachineDescription} {input out : Word Bool}
    (hhalts : D.HaltsFromTapeWithOutput (Tape.input input) out) :
    D.HaltsWithOutput input out := by
  simpa only [MachineDescription.HaltsFromTapeWithOutput,
    MachineDescription.HaltsFromTapeWithOutputIn,
    MachineDescription.HaltsWithOutput,
    MachineDescription.HaltsWithOutputIn,
    MachineDescription.initial] using hhalts

/-- Valid description codes take the accepting Boolean closeout branch. -/
theorem description_haltsWithOutput_true_of_valid
    (code : Word MachineCodeSymbol)
    (hvalid : MachineDescription.DescriptionCodeValid code) :
    Description.HaltsWithOutput (encodeCodeWordAsInput code) [true] := by
  rcases
      (gateDescription_exists_haltsFromCode_iff_descriptionCodeValid code).2
        hvalid with
    ⟨output, hhalts⟩
  rcases gateDescription_contiguous_of_haltsFromCode code output hhalts with
    ⟨leftRev, right, padding, houtput⟩
  subst output
  apply haltsWithOutput_of_haltsFromTapeWithOutput
  exact ValidatorBooleanCloseout.haltsFromTapeWithOutput_accept
    gateDescription_subroutineReady leftRev right padding hhalts

/-- Invalid description codes take the rejecting Boolean closeout branch. -/
theorem description_haltsWithOutput_false_of_not_valid
    (code : Word MachineCodeSymbol)
    (hnotValid : ¬ MachineDescription.DescriptionCodeValid code) :
    Description.HaltsWithOutput (encodeCodeWordAsInput code) [false] := by
  rcases gateDescription_haltsOrContiguousStuckFromCode code with
    hhalts | hstuck
  · rcases hhalts with ⟨output, hhalts⟩
    exact False.elim (hnotValid
      ((gateDescription_exists_haltsFromCode_iff_descriptionCodeValid code).1
        ⟨output, hhalts⟩))
  · rcases hstuck with ⟨stuck, hstuck, hcontiguous⟩
    rcases hcontiguous with ⟨leftRev, right, padding, hstuckTape⟩
    subst stuck
    apply haltsWithOutput_of_haltsFromTapeWithOutput
    exact ValidatorBooleanCloseout.haltsFromTapeWithOutput_reject_of_stuck
      gateDescription_subroutineReady leftRev right padding hstuck

/-- The concrete Boolean validator satisfies the stopped two-answer decision
contract for exact description-code validity. -/
theorem stoppedDescriptionDecidesValidCodeLanguage :
    StoppedDescriptionDecidesCodeLanguage
      Description false true ValidCodeLanguage := by
  refine ⟨description_subroutineReady.2,
    description_subroutineReady.1, by decide, ?_⟩
  intro code
  exact ⟨description_haltsWithOutput_true_of_valid code,
    description_haltsWithOutput_false_of_not_valid code⟩

/-- Standalone finite-description decidability of the valid-code language.
This is the validator API's second construction-family consumer. -/
theorem construction : ExactCodeValidatorConstruction := by
  exact ⟨Description, false, true,
    stoppedDescriptionDecidesValidCodeLanguage⟩

end ExactCodeValidator
end SelfHaltingRecognizer
end Computability
end FoC
