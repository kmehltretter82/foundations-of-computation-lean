import FoC.Computability.Compiler.SeqSubroutineSemantics
import FoC.Computability.Compiler.Core.EncodingLemmas
import FoC.Computability.Compiler.Core.CommonGround.Identity
import FoC.Computability.Compiler.Core.CommonGround.Layouts
import FoC.Computability.Compiler.Core.CommonGround.Scanners
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.Dovetail
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.Parser.Basic

set_option doc.verso true

/-!
# Bounded-layout parser construction

This is the leaf for the complete-layout parser.  The corrected dependency
plan keeps this proof local to the parser phase: it should recognize exactly
complete canonical
{name (full := FoC.Computability.MachineDescription.DovetailLayout)}`DovetailLayout`
encodings and preserve the input contents.

This leaf is a genuine finite-parser construction, not a small semantic
adapter.  It needs to validate the full
{name (full := FoC.Computability.MachineDescription.DovetailLayout)}`DovetailLayout`
grammar, including counted cell lists inside the two encoded
{name (full := FoC.Computability.MachineDescription.Configuration)}`Configuration`
values.  A complete final empty-suffix check reads the physical blank and
therefore records it in the exact tape window; the checked parser contract uses
that tape shape instead of pretending the exact
{name (full := FoC.Computability.Tape.input)}`Tape.input` window can be
recovered.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription
open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

namespace EncodedRewriters
namespace BoundedLayoutRunner

abbrev LayoutIdentityPrimitive :
    TapeCodePrimitive :=
  CommonGround.DovetailLayouts.identityPrimitive

theorem layoutIdentityPrimitive_transform_eq_some_iff
    (code out : Word MachineCodeSymbol) :
    LayoutIdentityPrimitive.transform code = some out <->
      exists L : DovetailLayout,
        code = DovetailLayout.encode L ∧
          out = DovetailLayout.encode L := by
  simpa [LayoutIdentityPrimitive] using
    CommonGround.DovetailLayouts.identityPrimitive_transform_eq_some_iff
      code out

theorem layoutIdentityPrimitive_encode
    (L : DovetailLayout) :
    LayoutIdentityPrimitive.transform
        (DovetailLayout.encode L) =
      some (DovetailLayout.encode L) := by
  simpa [LayoutIdentityPrimitive] using
    CommonGround.DovetailLayouts.identityPrimitive_encode L

def ParsedLayoutHandoffTape
    (L : DovetailLayout) : Tape Bool :=
  Tape.move Direction.right (ParsedLayoutTape L)

theorem parsedLayoutHandoffTape_normalizedOutput
    (L : DovetailLayout) :
    Tape.normalizedOutput (ParsedLayoutHandoffTape L) =
      ParsedLayoutBits L := by
  simpa [ParsedLayoutHandoffTape, ParsedLayoutTape] using
    EncodedRewriters.tape_normalizedOutput_move_right_input
      (ParsedLayoutBits L)

theorem parsedLayoutHandoffTape_handoff
    (L : DovetailLayout) :
    Tape.move tapeCodePrimitiveCodeWordHandoffMove
        (ParsedLayoutHandoffTape L) =
      ParsedLayoutTape L := by
  rcases EncodedRewriters.dovetailLayout_encode_cons L with
    ⟨tail, htail⟩
  simpa [ParsedLayoutHandoffTape, ParsedLayoutTape, ParsedLayoutBits,
    htail, tapeCodePrimitiveCodeWordHandoffMove] using
    EncodedRewriters.tape_move_left_move_right_input_encodeCodeWordAsInput_cons
      MachineCodeSymbol.transition tail

def LayoutClosedRecognizerSpec
    (recognizer : MachineDescription) : Prop :=
  recognizer.SubroutineReady ∧
    (forall L : DovetailLayout,
      recognizer.HaltsWithTape
        (ParsedLayoutBits L)
        (ParsedLayoutHandoffTape L)) ∧
      forall code : Word MachineCodeSymbol,
      forall T : Tape Bool,
        recognizer.HaltsWithTape
            (encodeCodeWordAsInput code) T ->
          exists L : DovetailLayout,
            DovetailLayout.decodeComplete code =
              some L ∧
            T = ParsedLayoutHandoffTape L

def LayoutClosedRecognizerConstruction : Prop :=
  exists recognizer : MachineDescription,
    LayoutClosedRecognizerSpec recognizer

def LayoutCheckedClosedRecognizerSpec
    (recognizer : MachineDescription) : Prop :=
  recognizer.SubroutineReady ∧
    (forall L : DovetailLayout,
      recognizer.HaltsWithTape
        (ParsedLayoutBits L)
        (ParsedLayoutCheckedHandoffTape L)) ∧
      forall code : Word MachineCodeSymbol,
      forall T : Tape Bool,
        recognizer.HaltsWithTape
            (encodeCodeWordAsInput code) T ->
          exists L : DovetailLayout,
            DovetailLayout.decodeComplete code =
              some L ∧
            Tape.move tapeCodePrimitiveCodeWordHandoffMove T =
              ParsedLayoutCheckedTape L

def LayoutCheckedClosedRecognizerConstruction : Prop :=
  exists recognizer : MachineDescription,
    LayoutCheckedClosedRecognizerSpec recognizer

theorem parsedLayoutBits_eq_dovetailLayoutFieldBits_nil
    (L : DovetailLayout) :
    ParsedLayoutBits L =
      CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits L [] := by
  simpa [ParsedLayoutBits, DovetailLayout.encode] using
    CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits_eq_encodeAppend
      L []

theorem parsedLayoutCheckedHandoffTape_eq_scanner_handoff
    (L : DovetailLayout) :
    ParsedLayoutCheckedHandoffTape L =
      CanonicalLayouts.DovetailLayoutScanner.restoredCheckedHandoffTapeFromTail
        (CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyRestoredBitsRev
          L).reverse := by
  have hbits :
      ParsedLayoutBits L =
        false ::
          CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits
            L := by
    calc
      ParsedLayoutBits L =
          CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits
            L [] :=
        parsedLayoutBits_eq_dovetailLayoutFieldBits_nil L
      _ = false ::
          CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyBits
            L :=
        CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits_nil_eq_first_body
          L
  simp [ParsedLayoutCheckedHandoffTape, ParsedLayoutCheckedTape,
    checkedInputTape, hbits,
    CanonicalLayouts.DovetailLayoutScanner.restoredCheckedHandoffTapeFromTail,
    CanonicalLayouts.DovetailLayoutScanner.markedDovetailLayoutBodyRestoredBitsRev_reverse,
    Tape.move, Tape.moveRight]

theorem checkedDovetailLayoutScannerDescription_haltsWithTape
    (L : DovetailLayout) :
    CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.HaltsWithTape
      (ParsedLayoutBits L) (ParsedLayoutCheckedHandoffTape L) := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.run_checkedDovetailLayoutScanner_raw_to_checkedHandoff
        L with
    ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  have hrun :
      CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.runConfig steps
          (CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.initial
            (ParsedLayoutBits L)) =
        { state :=
            CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.halt
          tape := ParsedLayoutCheckedHandoffTape L } := by
    rw [parsedLayoutBits_eq_dovetailLayoutFieldBits_nil L]
    rw [parsedLayoutCheckedHandoffTape_eq_scanner_handoff L]
    simpa [initial,
      DovetailInitialLayoutInitializer.tapeAtCells] using hsteps
  constructor
  · simpa using congrArg Configuration.state hrun
  · simpa using congrArg Configuration.tape hrun

def LayoutIdentityRightShiftedConstruction : Prop :=
  exists runner : MachineDescription,
    RightShiftedOutputCompiledSubroutineByDescription
      LayoutIdentityPrimitive runner

def LayoutIdentityClosedHandoffConstruction : Prop :=
  exists closed : MachineDescription,
    TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
      LayoutIdentityPrimitive
      closed tapeCodePrimitiveCodeWordHandoffMove

theorem layoutIdentityPrimitive_transform_eq_some_cons
    {code out : Word MachineCodeSymbol}
    (h : LayoutIdentityPrimitive.transform code = some out) :
    exists symbol : MachineCodeSymbol,
    exists tail : Word MachineCodeSymbol,
      out = symbol :: tail := by
  exact
    CommonGround.DovetailLayouts.identityPrimitive_transform_eq_some_cons h

theorem layoutIdentityClosedHandoffConstruction_of_rightShifted
    (h : LayoutIdentityRightShiftedConstruction) :
    LayoutIdentityClosedHandoffConstruction := by
  exact
    CommonGround.DovetailLayouts.identityClosedHandoffConstruction_of_rightShifted
      h

theorem layoutIdentityClosedHandoffConstruction_of_closedRecognizer
    (h : LayoutClosedRecognizerConstruction) :
    LayoutIdentityClosedHandoffConstruction := by
  rcases h with ⟨recognizer, hrecognizer⟩
  have hcanonical :
      CanonicalLayouts.Dovetail.ClosedRecognizerConstruction := by
    refine ⟨recognizer, ?_⟩
    constructor
    · exact hrecognizer.left
    constructor
    · intro L
      simpa [CanonicalLayouts.Dovetail.bits,
        CanonicalLayouts.Dovetail.handoffTape,
        CanonicalLayouts.Bits, CanonicalLayouts.HandoffTape,
        CanonicalLayouts.InputTape, ParsedLayoutBits,
        ParsedLayoutHandoffTape, ParsedLayoutTape] using
        hrecognizer.right.left L
    · intro code T hhalt
      rcases hrecognizer.right.right code T hhalt with
        ⟨L, hdecode, hT⟩
      refine ⟨L, hdecode, ?_⟩
      simpa [CanonicalLayouts.Dovetail.handoffTape,
        CanonicalLayouts.HandoffTape, CanonicalLayouts.InputTape,
        CanonicalLayouts.Bits, ParsedLayoutHandoffTape, ParsedLayoutTape,
        ParsedLayoutBits] using hT
  exact
    CommonGround.DovetailLayouts.identityClosedHandoffConstruction_of_closedRecognizer
      hcanonical

theorem layoutIdentityRightShiftedConstruction_of_closedRecognizer
    (h : LayoutClosedRecognizerConstruction) :
    LayoutIdentityRightShiftedConstruction := by
  rcases h with ⟨recognizer, hrecognizer⟩
  refine ⟨recognizer, ?_⟩
  constructor
  · exact hrecognizer.left.left
  constructor
  · exact hrecognizer.left.right
  constructor
  · intro code out
    constructor
    · intro hhalt
      rcases hhalt with ⟨n, hn⟩
      let T : Tape Bool :=
        (recognizer.runConfig n
          (recognizer.initial
            (encodeCodeWordAsInput code))).tape
      have hTape :
          recognizer.HaltsWithTape
              (encodeCodeWordAsInput code) T := by
        refine ⟨n, ?_⟩
        exact ⟨hn.left, rfl⟩
      rcases hrecognizer.right.right code T hTape with
        ⟨L, hdecode, hT⟩
      have hcode :
          code = DovetailLayout.encode L :=
        DovetailLayout.decodeComplete_eq_some_encode
          hdecode
      have houtBits :
          encodeCodeWordAsInput out =
            encodeCodeWordAsInput
              (DovetailLayout.encode L) := by
        calc
          encodeCodeWordAsInput out =
              Tape.normalizedOutput T := by
                simpa [T] using hn.right.symm
          _ =
              encodeCodeWordAsInput
                (DovetailLayout.encode L) := by
                rw [hT]
                simpa [ParsedLayoutHandoffTape, ParsedLayoutBits] using
                  parsedLayoutHandoffTape_normalizedOutput L
      have hout :
          out = DovetailLayout.encode L :=
        encodeCodeWordAsInput_injective houtBits
      rw [hcode, hout]
      exact layoutIdentityPrimitive_encode L
    · intro htransform
      rcases
          (layoutIdentityPrimitive_transform_eq_some_iff code out).mp
            htransform with
        ⟨L, hcode, hout⟩
      subst code
      subst out
      have hhaltTape :
          recognizer.HaltsWithTape
            (ParsedLayoutBits L)
            (ParsedLayoutHandoffTape L) :=
        hrecognizer.right.left L
      have houtput :=
        haltsWithOutput_of_haltsWithTape hhaltTape
      simpa [ParsedLayoutBits,
        parsedLayoutHandoffTape_normalizedOutput L] using houtput
  · intro code T hhalt
    rcases hrecognizer.right.right code T hhalt with
      ⟨L, hdecode, hT⟩
    refine ⟨DovetailLayout.encode L, ?_, ?_⟩
    · have hcode :
          code = DovetailLayout.encode L :=
        DovetailLayout.decodeComplete_eq_some_encode
          hdecode
      subst code
      exact layoutIdentityPrimitive_encode L
    · simp [hT, ParsedLayoutHandoffTape, ParsedLayoutBits,
        ParsedLayoutTape]

def LayoutParserFromClosedHandoff
    (closed : MachineDescription) : MachineDescription :=
  seqSubroutine closed
    ExactIdentityDescription
    tapeCodePrimitiveCodeWordHandoffMove

theorem layoutCheckedParserFromClosedRecognizer_spec
    {recognizer : MachineDescription}
    (hrecognizer : LayoutCheckedClosedRecognizerSpec recognizer) :
    LayoutCheckedParserSpec (LayoutParserFromClosedHandoff recognizer) := by
  let identity := ExactIdentityDescription
  have hrecognizerReady : recognizer.SubroutineReady :=
    hrecognizer.left
  have hidentityReady : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  constructor
  · exact
      seqSubroutine_subroutineReady
        hrecognizerReady hidentityReady
  constructor
  · intro L
    have hidentityReach :
        exists nB : Nat,
          identity.runConfig nB
              { state := identity.start
                tape :=
                  Tape.move tapeCodePrimitiveCodeWordHandoffMove
                    (ParsedLayoutCheckedHandoffTape L) } =
            { state := identity.halt
              tape := ParsedLayoutCheckedTape L } := by
      refine ⟨0, ?_⟩
      have hmove :
          Tape.move tapeCodePrimitiveCodeWordHandoffMove
              (ParsedLayoutCheckedHandoffTape L) =
            ParsedLayoutCheckedTape L := by
        simpa [tapeCodePrimitiveCodeWordHandoffMove] using
          parsedLayoutCheckedHandoffTape_move_left L
      rw [hmove]
      rfl
    simpa [LayoutParserFromClosedHandoff, identity,
      ParsedLayoutBits, tapeCodePrimitiveCodeWordHandoffMove] using
      seqSubroutine_haltsWithTape_of_haltsWithTape
        (A := recognizer) (B := identity)
        (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
        hrecognizerReady hidentityReady
        (hrecognizer.right.left L) hidentityReach
  · intro code T hhalt
    rcases
        seqSubroutine_haltsWithTape_inv
          (A := recognizer) (B := identity)
          (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
          hrecognizerReady hidentityReady
          (by simpa [LayoutParserFromClosedHandoff, identity] using hhalt) with
      ⟨Tmid, hrecognizerHalt, hidentityReach⟩
    rcases hrecognizer.right.right code Tmid hrecognizerHalt with
      ⟨L, hdecode, hhandoff⟩
    rcases hidentityReach with ⟨nB, hidentityRun⟩
    have hT :
        T = Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid := by
      have hcfg :
          ({ state := identity.halt
             tape := Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid } :
            Configuration) =
          { state := identity.halt, tape := T } := by
        simpa [identity] using
          ((CommonGround.Identity.exactIdentityDescription_runConfig_from_start
              nB
              (Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid)).symm.trans
            hidentityRun)
      exact (congrArg Configuration.tape hcfg).symm
    refine ⟨L, hdecode, ?_⟩
    rw [hT]
    exact hhandoff

theorem layoutCheckedParserConstruction_of_closedRecognizer
    (h : LayoutCheckedClosedRecognizerConstruction) :
    LayoutCheckedParserConstruction := by
  rcases h with ⟨recognizer, hrecognizer⟩
  exact
    ⟨LayoutParserFromClosedHandoff recognizer,
      layoutCheckedParserFromClosedRecognizer_spec hrecognizer⟩

theorem layoutParserFromClosedHandoff_spec
    {closed : MachineDescription}
    (hclosed :
      TapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription
        LayoutIdentityPrimitive
        closed tapeCodePrimitiveCodeWordHandoffMove) :
    LayoutParserSpec (LayoutParserFromClosedHandoff closed) := by
  let identity := ExactIdentityDescription
  have hclosedReady : closed.SubroutineReady :=
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_subroutineReady
      hclosed
  have hidentityReady : identity.SubroutineReady :=
    CommonGround.Identity.exactIdentityDescription_subroutineReady
  constructor
  · exact
      seqSubroutine_subroutineReady
        hclosedReady hidentityReady
  constructor
  · intro L
    have htransform :
        LayoutIdentityPrimitive.transform
            (DovetailLayout.encode L) =
          some (DovetailLayout.encode L) := by
      exact layoutIdentityPrimitive_encode L
    rcases
        (tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_handoffRealized
          hclosed).right
          (DovetailLayout.encode L)
          (DovetailLayout.encode L)
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
      seqSubroutine_haltsWithTape_of_haltsWithTape
        (A := closed) (B := identity)
        (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
        hclosedReady hidentityReady hclosedHalt hidentityReach
  · intro code T hhalt
    rcases
        seqSubroutine_haltsWithTape_inv
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
            Configuration) =
          { state := identity.halt, tape := T } := by
        simpa [identity] using
          ((CommonGround.Identity.exactIdentityDescription_runConfig_from_start
              nB (Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid)).symm.trans
            hidentityRun)
      exact (congrArg Configuration.tape hcfg).symm
    refine ⟨L, ?_, ?_⟩
    · rw [hcode]
      exact DovetailLayout.decodeComplete_encode L
    · rw [hT]
      simpa [hout, ParsedLayoutTape, ParsedLayoutBits] using hhandoff

theorem layoutParserConstruction_of_closedHandoffConstruction
    (h : LayoutIdentityClosedHandoffConstruction) :
    LayoutParserConstruction := by
  rcases h with ⟨closed, hclosed⟩
  exact
    ⟨LayoutParserFromClosedHandoff closed,
      layoutParserFromClosedHandoff_spec hclosed⟩

theorem layoutParserConstruction_of_closedRecognizer
    (h : LayoutClosedRecognizerConstruction) :
    LayoutParserConstruction :=
  layoutParserConstruction_of_closedHandoffConstruction
    (layoutIdentityClosedHandoffConstruction_of_closedRecognizer h)

theorem layoutParserConstruction_of_rightShifted
    (h : LayoutIdentityRightShiftedConstruction) :
    LayoutParserConstruction :=
  layoutParserConstruction_of_closedHandoffConstruction
    (layoutIdentityClosedHandoffConstruction_of_rightShifted h)

/-!
**Parser field inversions.**  The checked layout scanner already exposes the
subscanner runs for the input word, stage number, configurations, and final
flags.  The parser closed proof still needs code-origin wrappers: from an
accepted canonical code word, each subscanner run forces the next suffix to be
the corresponding
{name (full := FoC.Computability.MachineDescription.DovetailLayout)}`DovetailLayout`
field.
-/

theorem boolWordSuffixScannerDescription_runConfig_encodeBoolWordAppend_stage_handoff
    (baseLeft : List (Option Bool)) (inputWord : Word Bool)
    (stageRest : Word MachineCodeSymbol)
    {Tinput Tstage : Tape Bool} {nInput nStage : Nat}
    (hinput :
      CommonGround.ScannerInversions.BoolWordSuffixScannerDescription.runConfig
          nInput
          (config
            CommonGround.ScannerInversions.BoolWordSuffixScannerDescription.start
            baseLeft
            ((encodeCodeWordAsInput
              (encodeBoolWordAppend inputWord
                stageRest)).map some)) =
        { state :=
            CommonGround.ScannerInversions.BoolWordSuffixScannerDescription.halt
          tape := Tinput })
    (_hstage :
      CommonGround.ScannerInversions.NonemptyNatSuffixScannerDescription.runConfig
          nStage
          { state :=
              CommonGround.ScannerInversions.NonemptyNatSuffixScannerDescription.start
            tape := Tape.move Direction.right Tinput } =
        { state :=
            CommonGround.ScannerInversions.NonemptyNatSuffixScannerDescription.halt
          tape := Tstage }) :
    exists baseAfterInput : List (Option Bool),
      Tape.move Direction.right Tinput =
        tapeAtCells baseAfterInput
          ((encodeCodeWordAsInput stageRest).map some) := by
  rcases
      CommonGround.ScannerInversions.boolWordSuffixScannerDescription_runConfig_encodeBoolWordAppend_handoff
        baseLeft inputWord stageRest hinput with
    ⟨suffixTail, hstageRestBits, hTinput⟩
  refine
    ⟨CommonGround.ScannerInversions.cellListCanonicalRestoredLeftWithBase
      (inputWord.map some) baseLeft, ?_⟩
  rw [hTinput]
  have hmove :=
    CommonGround.ScannerInversions.boolWordCanonicalHandoffConfigWithBase_move_right_all
      inputWord baseLeft (false :: suffixTail)
  rw [hmove, hstageRestBits]

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_stage_inv
    {code : Word MachineCodeSymbol} {Tout : Tape Bool}
    {inputWord : Word Bool} {stageRest : Word MachineCodeSymbol}
    (h : CommonGround.ScannerInversions.CheckedDovetailLayoutScannerDescription.HaltsWithTape
          (encodeCodeWordAsInput code) Tout)
    (h_input : code = MachineCodeSymbol.transition :: encodeBoolWordAppend inputWord stageRest) :
    exists stage : Nat,
    exists acceptRest : Word MachineCodeSymbol,
      stageRest = encodeNatAppend stage acceptRest := by
  rcases
      CommonGround.ScannerInversions.checkedDovetailLayoutScannerDescription_haltsWithTape_stageField_inv
        h with
    ⟨b, suffixTail, Tinput, Tstage, _Tbody, nInput, nStage,
      _nConfigs, _nReturn, hbits, hinputRun, hstageRun, _hconfigsRun,
      _hreturnRun⟩
  rcases
      CommonGround.ScannerInversions.encodeCodeWordAsInput_transition_prefix_inv
        hbits with
    ⟨inputCode, hcode, hinputBits⟩
  have hinputCode :
      inputCode =
        encodeBoolWordAppend inputWord stageRest := by
    have hcons :
        MachineCodeSymbol.transition :: inputCode =
          MachineCodeSymbol.transition ::
            encodeBoolWordAppend inputWord
              stageRest :=
      hcode.symm.trans h_input
    simpa using congrArg List.tail hcons
  have hinputRunCode :
      CommonGround.ScannerInversions.BoolWordSuffixScannerDescription.runConfig
          nInput
          (config
            CommonGround.ScannerInversions.BoolWordSuffixScannerDescription.start
            (List.append
              (CommonGround.ScannerInversions.transitionRemainderBits.reverse.map
                some)
              [none])
            ((encodeCodeWordAsInput
              (encodeBoolWordAppend inputWord
                stageRest)).map some)) =
        { state :=
            CommonGround.ScannerInversions.BoolWordSuffixScannerDescription.halt
          tape := Tinput } := by
    rw [← hinputCode, hinputBits]
    simpa [config] using hinputRun
  rcases
      boolWordSuffixScannerDescription_runConfig_encodeBoolWordAppend_stage_handoff
        (List.append
          (CommonGround.ScannerInversions.transitionRemainderBits.reverse.map
            some)
          [none])
        inputWord stageRest hinputRunCode hstageRun with
    ⟨baseAfterInput, hmove⟩
  have hstageRunCode :
      CommonGround.ScannerInversions.NonemptyNatSuffixScannerDescription.runConfig
          nStage
          (config
            CommonGround.ScannerInversions.NonemptyNatSuffixScannerDescription.start
            baseAfterInput
            ((encodeCodeWordAsInput stageRest).map
              some)) =
        { state :=
            CommonGround.ScannerInversions.NonemptyNatSuffixScannerDescription.halt
          tape := Tstage } := by
    simpa [config, hmove] using hstageRun
  rcases
      CommonGround.ScannerInversions.nonemptyNatSuffixScannerDescription_runConfig_code_inv
        baseAfterInput stageRest hstageRunCode with
    ⟨stage, symbol, suffix, hstageRest⟩
  exact ⟨stage, symbol :: suffix, hstageRest⟩

/-!
The three field-level inversions below all depend on the same remaining
closed-body fact: after the input word and stage have been accepted, the
scanner must consume two encoded configurations and the two final hit flags,
then return to the checked input tape.  Keeping that as one named obligation
avoids proving the same handoff chain separately for the accept config, reject
config, and final flags.
-/

/--
Remaining closed-body scanner inversion: once the input word and stage prefix
have been accepted, the scanner must validate the two configurations and final
hit flags.
-/
theorem checkedDovetailLayoutScannerDescription_haltsWithTape_body_fields_inv
    {code : Word MachineCodeSymbol} {Tout : Tape Bool}
    {inputWord : Word Bool} {stage : Nat}
    {bodyRest : Word MachineCodeSymbol}
    (h : CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.HaltsWithTape
          (encodeCodeWordAsInput code) Tout)
    (h_input : code =
      MachineCodeSymbol.transition ::
        encodeBoolWordAppend inputWord
          (encodeNatAppend stage bodyRest)) :
    exists acceptConfig : Configuration,
    exists rejectConfig : Configuration,
    exists acceptHit : Bool,
    exists rejectHit : Bool,
      bodyRest =
        encodeConfigurationAppend acceptConfig
          (encodeConfigurationAppend rejectConfig
            (encodeBoolAppend acceptHit
              (encodeBoolAppend rejectHit []))) := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.checkedDovetailLayoutScannerDescription_haltsWithTape_rejectConfig_inv
        h with
    ⟨b, suffixTail, Tinput, Tstage, Taccept, Treject, Tbody,
      nInput, nStage, nAccept, nReject, nFinalFlags, _nReturn,
      hbits, hinputRun, hstageRun, hacceptRun, hrejectRun,
      hfinalFlagsRun, _hreturnRun⟩
  rcases
      CommonGround.ScannerInversions.encodeCodeWordAsInput_transition_prefix_inv
        hbits with
    ⟨inputCode, hcode, hinputBits⟩
  have hinputCode :
      inputCode =
        encodeBoolWordAppend inputWord
          (encodeNatAppend stage bodyRest) := by
    have hcons :
        MachineCodeSymbol.transition :: inputCode =
          MachineCodeSymbol.transition ::
            encodeBoolWordAppend inputWord
              (encodeNatAppend stage bodyRest) :=
      hcode.symm.trans h_input
    simpa using congrArg List.tail hcons
  have hinputRunCode :
      CommonGround.ScannerInversions.BoolWordSuffixScannerDescription.runConfig
          nInput
          (config
            CommonGround.ScannerInversions.BoolWordSuffixScannerDescription.start
            (List.append
              (CommonGround.ScannerInversions.transitionRemainderBits.reverse.map
                some)
              [none])
            ((encodeCodeWordAsInput
              (encodeBoolWordAppend inputWord
                (encodeNatAppend stage bodyRest))).map
              some)) =
        { state :=
            CommonGround.ScannerInversions.BoolWordSuffixScannerDescription.halt
          tape := Tinput } := by
    rw [← hinputCode, hinputBits]
    simpa [config] using hinputRun
  rcases
      boolWordSuffixScannerDescription_runConfig_encodeBoolWordAppend_stage_handoff
        (List.append
          (CommonGround.ScannerInversions.transitionRemainderBits.reverse.map
            some)
          [none])
        inputWord (encodeNatAppend stage bodyRest)
        hinputRunCode hstageRun with
    ⟨baseAfterInput, hinputMove⟩
  have hstageRunCode :
      CommonGround.ScannerInversions.NonemptyNatSuffixScannerDescription.runConfig
          nStage
          (config
            CommonGround.ScannerInversions.NonemptyNatSuffixScannerDescription.start
            baseAfterInput
            ((encodeCodeWordAsInput
              (encodeNatAppend stage bodyRest)).map
              some)) =
        { state :=
            CommonGround.ScannerInversions.NonemptyNatSuffixScannerDescription.halt
          tape := Tstage } := by
    simpa [config, hinputMove] using hstageRun
  rcases
      CommonGround.ScannerInversions.nonemptyNatSuffixScannerDescription_runConfig_code_inv
        baseAfterInput (encodeNatAppend stage bodyRest)
        hstageRunCode with
    ⟨stage', bodyFirst, bodyTail, hstageCode⟩
  rcases encodeNatAppend_inj hstageCode with ⟨_hstageEq, hbodyCons⟩
  rcases
      CommonGround.ScannerInversions.encodeCodeWordAsInput_cons_bits
        bodyFirst bodyTail with
    ⟨bodyBit, bodyBitsTail, hbodyBits⟩
  have hbodyBits' :
      encodeCodeWordAsInput bodyRest =
        bodyBit :: bodyBitsTail := by
    rw [hbodyCons]
    exact hbodyBits
  rcases
      CommonGround.ScannerInversions.nonemptyNatSuffixScannerDescription_runConfig_encodeNatAppend_handoff
        baseAfterInput stage bodyRest bodyBit bodyBitsTail hbodyBits'
        hstageRunCode with
    ⟨baseAfterStage, hstageMove⟩
  have hacceptRunCode :
      CanonicalLayouts.DovetailLayoutScanner.ConfigurationSuffixScannerDescription.runConfig
          nAccept
          (config
            CanonicalLayouts.DovetailLayoutScanner.ConfigurationSuffixScannerDescription.start
            baseAfterStage
            ((encodeCodeWordAsInput bodyRest).map
              some)) =
        { state :=
            CanonicalLayouts.DovetailLayoutScanner.ConfigurationSuffixScannerDescription.halt
          tape := Taccept } := by
    simpa [config, hstageMove] using hacceptRun
  rcases
      CommonGround.ScannerInversions.configurationSuffixScannerDescription_runConfig_code_handoff
        baseAfterStage bodyRest hacceptRunCode with
    ⟨acceptConfig, rejectRest, baseAfterAccept, hbodyAccept,
      hacceptMove⟩
  have hrejectRunCode :
      CanonicalLayouts.DovetailLayoutScanner.ConfigurationSuffixScannerDescription.runConfig
          nReject
          (config
            CanonicalLayouts.DovetailLayoutScanner.ConfigurationSuffixScannerDescription.start
            baseAfterAccept
            ((encodeCodeWordAsInput rejectRest).map
              some)) =
        { state :=
            CanonicalLayouts.DovetailLayoutScanner.ConfigurationSuffixScannerDescription.halt
          tape := Treject } := by
    simpa [config, hacceptMove] using hrejectRun
  rcases
      CommonGround.ScannerInversions.configurationSuffixScannerDescription_runConfig_code_handoff
        baseAfterAccept rejectRest hrejectRunCode with
    ⟨rejectConfig, flagsRest, baseAfterReject, hrejectRest,
      hrejectMove⟩
  have hfinalFlagsRunCode :
      CanonicalLayouts.DovetailLayoutScanner.FinalHitFlagsScannerDescription.runConfig
          nFinalFlags
          (config
            CanonicalLayouts.DovetailLayoutScanner.FinalHitFlagsScannerDescription.start
            baseAfterReject
            ((encodeCodeWordAsInput flagsRest).map
              some)) =
        { state :=
            CanonicalLayouts.DovetailLayoutScanner.FinalHitFlagsScannerDescription.halt
          tape := Tbody } := by
    simpa [config, hrejectMove] using hfinalFlagsRun
  rcases
      CommonGround.ScannerInversions.finalHitFlagsScannerDescription_runConfig_code_inv
        baseAfterReject flagsRest hfinalFlagsRunCode with
    ⟨acceptHit, rejectHit, _baseAfterFlags, hflags, _hflagsMove⟩
  exact
    ⟨acceptConfig, rejectConfig, acceptHit, rejectHit,
      by rw [hbodyAccept, hrejectRest, hflags]⟩

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_body_tape_inv
    {code : Word MachineCodeSymbol} {Tout : Tape Bool}
    {inputWord : Word Bool} {stage : Nat}
    {bodyRest : Word MachineCodeSymbol}
    {acceptConfig rejectConfig : Configuration}
    {acceptHit rejectHit : Bool}
    (h : CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.HaltsWithTape
          (encodeCodeWordAsInput code) Tout)
    (h_input : code =
      MachineCodeSymbol.transition ::
        encodeBoolWordAppend inputWord
          (encodeNatAppend stage bodyRest))
    (h_body :
      bodyRest =
        encodeConfigurationAppend acceptConfig
          (encodeConfigurationAppend rejectConfig
            (encodeBoolAppend acceptHit
              (encodeBoolAppend rejectHit [])))) :
      Tape.move tapeCodePrimitiveCodeWordHandoffMove Tout =
        ParsedLayoutCheckedTape
          { input := inputWord
            stage := stage
            acceptConfig := acceptConfig
            rejectConfig := rejectConfig
            acceptHit := acceptHit
            rejectHit := rejectHit } := by
  let L : DovetailLayout :=
    { input := inputWord
      stage := stage
      acceptConfig := acceptConfig
      rejectConfig := rejectConfig
      acceptHit := acceptHit
      rejectHit := rejectHit }
  have hcode : code = DovetailLayout.encode L := by
    rw [h_input, h_body]
    rfl
  have hbits :
      encodeCodeWordAsInput code =
        ParsedLayoutBits L := by
    rw [hcode]
    rfl
  have hforward :
      CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.HaltsWithTape
        (encodeCodeWordAsInput code)
        (ParsedLayoutCheckedHandoffTape L) := by
    rw [hbits]
    exact checkedDovetailLayoutScannerDescription_haltsWithTape L
  have hTout :
      Tout = ParsedLayoutCheckedHandoffTape L :=
    MachineDescription.haltsWithTape_functional_of_haltTransitionFree
      CanonicalLayouts.DovetailLayoutScanner.checkedDovetailLayoutScannerDescription_subroutineReady.right
      h hforward
  rw [hTout]
  simpa [L, tapeCodePrimitiveCodeWordHandoffMove] using
    parsedLayoutCheckedHandoffTape_move_left L

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_body_inv
    {code : Word MachineCodeSymbol} {Tout : Tape Bool}
    {inputWord : Word Bool} {stage : Nat}
    {bodyRest : Word MachineCodeSymbol}
    (h : CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.HaltsWithTape
          (encodeCodeWordAsInput code) Tout)
    (h_input : code =
      MachineCodeSymbol.transition ::
        encodeBoolWordAppend inputWord
          (encodeNatAppend stage bodyRest)) :
    exists acceptConfig : Configuration,
    exists rejectConfig : Configuration,
    exists acceptHit : Bool,
    exists rejectHit : Bool,
      bodyRest =
        encodeConfigurationAppend acceptConfig
          (encodeConfigurationAppend rejectConfig
            (encodeBoolAppend acceptHit
              (encodeBoolAppend rejectHit []))) ∧
      Tape.move tapeCodePrimitiveCodeWordHandoffMove Tout =
        ParsedLayoutCheckedTape
          { input := inputWord
            stage := stage
            acceptConfig := acceptConfig
            rejectConfig := rejectConfig
            acceptHit := acceptHit
            rejectHit := rejectHit } := by
  rcases
      checkedDovetailLayoutScannerDescription_haltsWithTape_body_fields_inv
        h h_input with
    ⟨acceptConfig, rejectConfig, acceptHit, rejectHit, h_body⟩
  exact
    ⟨acceptConfig, rejectConfig, acceptHit, rejectHit, h_body,
      checkedDovetailLayoutScannerDescription_haltsWithTape_body_tape_inv
        h h_input h_body⟩

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_acceptConfig_inv
    {code : Word MachineCodeSymbol} {Tout : Tape Bool}
    {inputWord : Word Bool} {stage : Nat} {acceptRest : Word MachineCodeSymbol}
    (h : CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.HaltsWithTape
          (encodeCodeWordAsInput code) Tout)
    (h_input : code =
      MachineCodeSymbol.transition ::
        encodeBoolWordAppend inputWord
          (encodeNatAppend stage acceptRest)) :
    exists acceptConfig : Configuration,
    exists rejectRest : Word MachineCodeSymbol,
      acceptRest =
        encodeConfigurationAppend acceptConfig rejectRest := by
  rcases
      checkedDovetailLayoutScannerDescription_haltsWithTape_body_inv
        h h_input with
    ⟨acceptConfig, rejectConfig, acceptHit, rejectHit, hbody, _hT⟩
  exact
    ⟨acceptConfig,
      encodeConfigurationAppend rejectConfig
        (encodeBoolAppend acceptHit
          (encodeBoolAppend rejectHit [])),
      hbody⟩

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_rejectConfig_inv
    {code : Word MachineCodeSymbol} {Tout : Tape Bool}
    {inputWord : Word Bool} {stage : Nat}
    {acceptConfig : Configuration}
    {rejectRest : Word MachineCodeSymbol}
    (h : CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.HaltsWithTape
          (encodeCodeWordAsInput code) Tout)
    (h_input : code =
      MachineCodeSymbol.transition ::
        encodeBoolWordAppend inputWord
          (encodeNatAppend stage
            (encodeConfigurationAppend acceptConfig
              rejectRest))) :
    exists rejectConfig : Configuration,
    exists flagsRest : Word MachineCodeSymbol,
      rejectRest =
        encodeConfigurationAppend rejectConfig flagsRest := by
  rcases
      checkedDovetailLayoutScannerDescription_haltsWithTape_body_inv
        h h_input with
    ⟨acceptConfig', rejectConfig, acceptHit, rejectHit, hbody, _hT⟩
  let flagsRest :=
    encodeBoolAppend acceptHit
      (encodeBoolAppend rejectHit [])
  rcases encodeConfigurationAppend_inj hbody with
    ⟨_haccept, hrest⟩
  exact
    ⟨rejectConfig, flagsRest,
      hrest⟩

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_flags_body_inv
    {code : Word MachineCodeSymbol} {Tout : Tape Bool}
    {inputWord : Word Bool} {stage : Nat}
    {acceptConfig : Configuration}
    {rejectConfig : Configuration}
    {flagsRest : Word MachineCodeSymbol}
    (h : CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.HaltsWithTape
          (encodeCodeWordAsInput code) Tout)
    (h_input : code =
      MachineCodeSymbol.transition ::
        encodeBoolWordAppend inputWord
          (encodeNatAppend stage
            (encodeConfigurationAppend acceptConfig
              (encodeConfigurationAppend rejectConfig
                flagsRest)))) :
    exists acceptHit : Bool,
    exists rejectHit : Bool,
      flagsRest =
        encodeBoolAppend acceptHit
          (encodeBoolAppend rejectHit []) ∧
      Tape.move tapeCodePrimitiveCodeWordHandoffMove Tout =
        ParsedLayoutCheckedTape
          { input := inputWord
            stage := stage
            acceptConfig := acceptConfig
            rejectConfig := rejectConfig
            acceptHit := acceptHit
            rejectHit := rejectHit } := by
  rcases
      checkedDovetailLayoutScannerDescription_haltsWithTape_body_inv
        h h_input with
    ⟨acceptConfig', rejectConfig', acceptHit, rejectHit, hbody, hT⟩
  let flagsRest' :=
    encodeBoolAppend acceptHit
      (encodeBoolAppend rejectHit [])
  rcases encodeConfigurationAppend_inj hbody with
    ⟨haccept, hrejectCode⟩
  rcases encodeConfigurationAppend_inj hrejectCode with
    ⟨hreject, hflags⟩
  subst acceptConfig'
  subst rejectConfig'
  exact ⟨acceptHit, rejectHit, hflags, hT⟩

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_decodeComplete_inv
    (code : Word MachineCodeSymbol) (T : Tape Bool)
    (h :
      CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.HaltsWithTape
        (encodeCodeWordAsInput code) T) :
    exists L : DovetailLayout,
      DovetailLayout.decodeComplete code = some L ∧
      Tape.move tapeCodePrimitiveCodeWordHandoffMove T =
        ParsedLayoutCheckedTape L := by
  rcases CanonicalLayouts.DovetailLayoutScanner.checkedDovetailLayoutScannerDescription_haltsWithTape_inputBoolWord_inv h with
    ⟨inputWord, inputRest, hcode1⟩
  rcases checkedDovetailLayoutScannerDescription_haltsWithTape_stage_inv h hcode1 with
    ⟨stage, stageRest, hcode2⟩
  have hcode12 : code = MachineCodeSymbol.transition :: encodeBoolWordAppend inputWord (encodeNatAppend stage stageRest) := by
    rw [hcode1, hcode2]
  rcases checkedDovetailLayoutScannerDescription_haltsWithTape_acceptConfig_inv h hcode12 with
    ⟨acceptConfig, acceptRest, hcode3⟩
  have hcode123 : code = MachineCodeSymbol.transition :: encodeBoolWordAppend inputWord (encodeNatAppend stage (encodeConfigurationAppend acceptConfig acceptRest)) := by
    rw [hcode12, hcode3]
  rcases checkedDovetailLayoutScannerDescription_haltsWithTape_rejectConfig_inv h hcode123 with
    ⟨rejectConfig, rejectRest, hcode4⟩
  have hcode1234 : code = MachineCodeSymbol.transition :: encodeBoolWordAppend inputWord (encodeNatAppend stage (encodeConfigurationAppend acceptConfig (encodeConfigurationAppend rejectConfig rejectRest))) := by
    rw [hcode123, hcode4]
  rcases checkedDovetailLayoutScannerDescription_haltsWithTape_flags_body_inv h hcode1234 with
    ⟨acceptHit, rejectHit, hcode5, hT⟩
  have hcode12345 : code = MachineCodeSymbol.transition :: encodeBoolWordAppend inputWord (encodeNatAppend stage (encodeConfigurationAppend acceptConfig (encodeConfigurationAppend rejectConfig (encodeBoolAppend acceptHit (encodeBoolAppend rejectHit []))))) := by
    rw [hcode1234, hcode5]
  let L : DovetailLayout := {
    input := inputWord
    stage := stage
    acceptConfig := acceptConfig
    rejectConfig := rejectConfig
    acceptHit := acceptHit
    rejectHit := rejectHit
  }
  refine ⟨L, ?_, hT⟩
  have henc : code = DovetailLayout.encode L := by
    exact hcode12345
  rw [henc]
  exact DovetailLayout.decodeComplete_encode L
theorem layoutCheckedClosedRecognizerConstruction_scaffold :
    LayoutCheckedClosedRecognizerConstruction := by
  refine ⟨CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription, ?_⟩
  constructor
  · exact CanonicalLayouts.DovetailLayoutScanner.checkedDovetailLayoutScannerDescription_subroutineReady
  constructor
  · intro L
    exact checkedDovetailLayoutScannerDescription_haltsWithTape L
  · intro code T h
    exact checkedDovetailLayoutScannerDescription_haltsWithTape_decodeComplete_inv code T h

theorem layoutCheckedParserConstruction_scaffold :
    LayoutCheckedParserConstruction := by
  exact
    layoutCheckedParserConstruction_of_closedRecognizer
      layoutCheckedClosedRecognizerConstruction_scaffold



end BoundedLayoutRunner
end EncodedRewriters

end Computability
end FoC
