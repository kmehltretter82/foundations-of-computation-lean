import FoC.Computability.Compiler.SeqSubroutineSemantics
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.Dovetail
import FoC.Computability.Compiler.Core.EncodedRewriters.CanonicalLayouts.DovetailLayoutScanner
import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.Parser.Basic

set_option doc.verso true

/-!
# Bounded-layout parser construction

This is the leaf for the complete-layout parser.  The corrected dependency
plan keeps this proof local to the parser phase: it should recognize exactly
complete canonical
{name (full := FoC.Computability.MachineDescription.DovetailLayout)}`MachineDescription.DovetailLayout`
encodings and preserve the input contents.

This leaf is a genuine finite-parser construction, not a small semantic
adapter.  It needs to validate the full
{name (full := FoC.Computability.MachineDescription.DovetailLayout)}`MachineDescription.DovetailLayout`
grammar, including counted cell lists inside the two encoded
{name (full := FoC.Computability.MachineDescription.Configuration)}`MachineDescription.Configuration`
values.  A complete final empty-suffix check reads the physical blank and
therefore records it in the exact tape window; the checked parser contract uses
that tape shape instead of pretending the exact
{name (full := FoC.Computability.Tape.input)}`Tape.input` window can be
recovered.
-/

namespace FoC
namespace Computability

open Languages
open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

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

def ParsedLayoutHandoffTape
    (L : MachineDescription.DovetailLayout) : Tape Bool :=
  Tape.move Direction.right (ParsedLayoutTape L)

theorem parsedLayoutHandoffTape_normalizedOutput
    (L : MachineDescription.DovetailLayout) :
    Tape.normalizedOutput (ParsedLayoutHandoffTape L) =
      ParsedLayoutBits L := by
  simpa [ParsedLayoutHandoffTape, ParsedLayoutTape] using
    EncodedRewriters.tape_normalizedOutput_move_right_input
      (ParsedLayoutBits L)

theorem parsedLayoutHandoffTape_handoff
    (L : MachineDescription.DovetailLayout) :
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
    (forall L : MachineDescription.DovetailLayout,
      recognizer.HaltsWithTape
        (ParsedLayoutBits L)
        (ParsedLayoutHandoffTape L)) ∧
      forall code : Word MachineCodeSymbol,
      forall T : Tape Bool,
        recognizer.HaltsWithTape
            (MachineDescription.encodeCodeWordAsInput code) T ->
          exists L : MachineDescription.DovetailLayout,
            MachineDescription.DovetailLayout.decodeComplete code =
              some L ∧
            T = ParsedLayoutHandoffTape L

def LayoutClosedRecognizerConstruction : Prop :=
  exists recognizer : MachineDescription,
    LayoutClosedRecognizerSpec recognizer

def LayoutCheckedClosedRecognizerSpec
    (recognizer : MachineDescription) : Prop :=
  recognizer.SubroutineReady ∧
    (forall L : MachineDescription.DovetailLayout,
      recognizer.HaltsWithTape
        (ParsedLayoutBits L)
        (ParsedLayoutCheckedHandoffTape L)) ∧
      forall code : Word MachineCodeSymbol,
      forall T : Tape Bool,
        recognizer.HaltsWithTape
            (MachineDescription.encodeCodeWordAsInput code) T ->
          exists L : MachineDescription.DovetailLayout,
            MachineDescription.DovetailLayout.decodeComplete code =
              some L ∧
            Tape.move tapeCodePrimitiveCodeWordHandoffMove T =
              ParsedLayoutCheckedTape L

def LayoutCheckedClosedRecognizerConstruction : Prop :=
  exists recognizer : MachineDescription,
    LayoutCheckedClosedRecognizerSpec recognizer

theorem parsedLayoutBits_eq_dovetailLayoutFieldBits_nil
    (L : MachineDescription.DovetailLayout) :
    ParsedLayoutBits L =
      CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits L [] := by
  simpa [ParsedLayoutBits, MachineDescription.DovetailLayout.encode] using
    CanonicalLayouts.DovetailLayoutScanner.dovetailLayoutFieldBits_eq_encodeAppend
      L []

theorem parsedLayoutCheckedHandoffTape_eq_scanner_handoff
    (L : MachineDescription.DovetailLayout) :
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
    (L : MachineDescription.DovetailLayout) :
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
    simpa [MachineDescription.initial,
      DovetailInitialLayoutInitializer.tapeAtCells] using hsteps
  constructor
  · simpa using congrArg MachineDescription.Configuration.state hrun
  · simpa using congrArg MachineDescription.Configuration.tape hrun

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
  rcases
      (layoutIdentityPrimitive_transform_eq_some_iff code out).mp h with
    ⟨L, _hcode, hout⟩
  rcases EncodedRewriters.dovetailLayout_encode_cons L with
    ⟨tail, htail⟩
  exact ⟨MachineCodeSymbol.transition, tail, by rw [hout, htail]⟩

theorem layoutIdentityClosedHandoffConstruction_of_rightShifted
    (h : LayoutIdentityRightShiftedConstruction) :
    LayoutIdentityClosedHandoffConstruction := by
  rcases h with ⟨runner, hrunner⟩
  exact
    ⟨runner,
      EncodedRewriters.closedHandoffCompiled_of_rightShiftedOutputCompiled
        hrunner
        (by
          intro code out htransform
          exact layoutIdentityPrimitive_transform_eq_some_cons htransform)⟩

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
  rcases
      CanonicalLayouts.Dovetail.identityClosedHandoffConstruction_of_closedRecognizer
        hcanonical with
    ⟨closed, hclosed⟩
  refine ⟨closed, ?_⟩
  exact
    tapeCodePrimitiveClosedHandoffCompiledSubroutineByDescription_congr
      (P := CanonicalLayouts.Dovetail.identityPrimitive)
      (Q := LayoutIdentityPrimitive)
      (D := closed)
      (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
      (by
        intro code
        simp [CanonicalLayouts.Dovetail.identityPrimitive,
          CanonicalLayouts.Dovetail.decode, CanonicalLayouts.IdentityPrimitive,
          LayoutIdentityPrimitive]
        cases MachineDescription.DovetailLayout.decodeComplete code <;>
          rfl)
      hclosed

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
            (MachineDescription.encodeCodeWordAsInput code))).tape
      have hTape :
          recognizer.HaltsWithTape
              (MachineDescription.encodeCodeWordAsInput code) T := by
        refine ⟨n, ?_⟩
        exact ⟨hn.left, rfl⟩
      rcases hrecognizer.right.right code T hTape with
        ⟨L, hdecode, hT⟩
      have hcode :
          code = MachineDescription.DovetailLayout.encode L :=
        MachineDescription.DovetailLayout.decodeComplete_eq_some_encode
          hdecode
      have houtBits :
          MachineDescription.encodeCodeWordAsInput out =
            MachineDescription.encodeCodeWordAsInput
              (MachineDescription.DovetailLayout.encode L) := by
        calc
          MachineDescription.encodeCodeWordAsInput out =
              Tape.normalizedOutput T := by
                simpa [T] using hn.right.symm
          _ =
              MachineDescription.encodeCodeWordAsInput
                (MachineDescription.DovetailLayout.encode L) := by
                rw [hT]
                simpa [ParsedLayoutHandoffTape, ParsedLayoutBits] using
                  parsedLayoutHandoffTape_normalizedOutput L
      have hout :
          out = MachineDescription.DovetailLayout.encode L :=
        MachineDescription.encodeCodeWordAsInput_injective houtBits
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
        MachineDescription.haltsWithOutput_of_haltsWithTape hhaltTape
      simpa [ParsedLayoutBits,
        parsedLayoutHandoffTape_normalizedOutput L] using houtput
  · intro code T hhalt
    rcases hrecognizer.right.right code T hhalt with
      ⟨L, hdecode, hT⟩
    refine ⟨MachineDescription.DovetailLayout.encode L, ?_, ?_⟩
    · have hcode :
          code = MachineDescription.DovetailLayout.encode L :=
        MachineDescription.DovetailLayout.decodeComplete_eq_some_encode
          hdecode
      subst code
      exact layoutIdentityPrimitive_encode L
    · simp [hT, ParsedLayoutHandoffTape, ParsedLayoutBits,
        ParsedLayoutTape]

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

theorem layoutCheckedParserFromClosedRecognizer_spec
    {recognizer : MachineDescription}
    (hrecognizer : LayoutCheckedClosedRecognizerSpec recognizer) :
    LayoutCheckedParserSpec (LayoutParserFromClosedHandoff recognizer) := by
  let identity := MachineDescription.ExactIdentityDescription
  have hrecognizerReady : recognizer.SubroutineReady :=
    hrecognizer.left
  have hidentityReady : identity.SubroutineReady :=
    ⟨MachineDescription.exactIdentityDescription_wellFormed,
      MachineDescription.exactIdentityDescription_haltTransitionFree⟩
  constructor
  · exact
      MachineDescription.seqSubroutine_subroutineReady
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
      MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
        (A := recognizer) (B := identity)
        (handoffMove := tapeCodePrimitiveCodeWordHandoffMove)
        hrecognizerReady hidentityReady
        (hrecognizer.right.left L) hidentityReach
  · intro code T hhalt
    rcases
        MachineDescription.seqSubroutine_haltsWithTape_inv
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
            MachineDescription.Configuration) =
          { state := identity.halt, tape := T } := by
        simpa [identity] using
          ((exactIdentityDescription_runConfig_from_start_layoutParser
              nB
              (Tape.move tapeCodePrimitiveCodeWordHandoffMove Tmid)).symm.trans
            hidentityRun)
      exact (congrArg MachineDescription.Configuration.tape hcfg).symm
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
{name (full := FoC.Computability.MachineDescription.DovetailLayout)}`MachineDescription.DovetailLayout`
field.
-/

theorem natSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
    {c mid : MachineDescription.Configuration} {k n : Nat}
    (hrun :
      CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.runConfig
          k c = mid)
    (hmid :
      forall m : Nat,
        (CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.runConfig
          m mid).state ≠
          CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.halt) :
    (CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.runConfig
      n c).state ≠
      CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.halt := by
  by_cases hle : n ≤ k
  · intro hhalt
    let rem := k - n
    have hk : k = n + rem := by
      omega
    have hcfg :
        CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.runConfig
            n c =
          { state :=
              CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.halt
            tape :=
              (CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.runConfig
                n c).tape } := by
      cases hrunN :
          CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.runConfig
            n c with
      | mk state tape =>
          simp [hrunN] at hhalt
          simp [hhalt]
    have hhaltAtK :
        (CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.runConfig
          k c).state =
          CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.halt := by
      rw [hk, MachineDescription.runConfig_add, hcfg,
        MachineDescription.runConfig_halt
          CanonicalLayouts.DovetailStagePrefix.natSuffixScannerDescription_haltTransitionFree]
    rw [hrun] at hhaltAtK
    exact hmid 0 hhaltAtK
  · have hn : n = k + (n - k) := by
      omega
    rw [hn, MachineDescription.runConfig_add, hrun]
    exact hmid (n - k)

theorem natSuffixScannerDescription_runConfig_decodeNat_none_ne_halt
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : MachineDescription.decodeNat tokens = none) (n : Nat) :
    (CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.runConfig
      n
      (config 200 leftRev
        ((MachineDescription.encodeCodeWordAsInput tokens).map some))).state ≠
      CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.halt := by
  induction tokens generalizing leftRev n with
  | nil =>
      exact
        CanonicalLayouts.DovetailLayoutScanner.primitive_runConfig_state_ne_halt_of_reaches_stuck
          CanonicalLayouts.DovetailStagePrefix.natSuffixScannerDescription_haltTransitionFree
          (D := CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription)
          (c :=
            config 200 leftRev
              ((MachineDescription.encodeCodeWordAsInput
                ([] : Word MachineCodeSymbol)).map some))
          (stuck :=
            config 200 leftRev
              ((MachineDescription.encodeCodeWordAsInput
                ([] : Word MachineCodeSymbol)).map some))
          (k := 0) (n := n)
          rfl
          (by rfl)
          (by
            change (200 : Nat) ≠ 999
            omega)
  | cons symbol rest ih =>
      cases symbol with
      | header =>
          exact
            CanonicalLayouts.DovetailLayoutScanner.primitive_runConfig_state_ne_halt_of_reaches_stuck
              CanonicalLayouts.DovetailStagePrefix.natSuffixScannerDescription_haltTransitionFree
              (D := CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.header :: rest)).map some))
              (stuck :=
                CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.runConfig
                  2
                  (config 200 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.header :: rest)).map some)))
              (k := 2) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription,
                  CanonicalLayouts.DovetailStagePrefix.MarkedPrefixScannerDescription,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (202 : Nat) ≠ 999
                omega)
      | transition =>
          exact
            CanonicalLayouts.DovetailLayoutScanner.primitive_runConfig_state_ne_halt_of_reaches_stuck
              CanonicalLayouts.DovetailStagePrefix.natSuffixScannerDescription_haltTransitionFree
              (D := CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.transition :: rest)).map some))
              (stuck :=
                CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.runConfig
                  2
                  (config 200 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.transition :: rest)).map some)))
              (k := 2) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription,
                  CanonicalLayouts.DovetailStagePrefix.MarkedPrefixScannerDescription,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (202 : Nat) ≠ 999
                omega)
      | tick =>
          simp [MachineDescription.decodeNat] at hdecode
          cases hrest : MachineDescription.decodeNat rest with
          | none =>
              simp [hrest] at hdecode
              apply
                natSuffixScannerDescription_ne_halt_of_reaches_ne_halt_region
                  (k := 4)
                  (mid :=
                    config 200
                      (List.append (tickBits.reverse.map some) leftRev)
                      ((MachineDescription.encodeCodeWordAsInput rest).map
                        some))
              · simpa [tickBits, MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription] using
                  run_state200_tick leftRev
                    ((MachineDescription.encodeCodeWordAsInput rest).map some)
              · intro m
                exact ih
                  (List.append (tickBits.reverse.map some) leftRev)
                  hrest m
          | some parsed =>
              simp [hrest] at hdecode
      | done =>
          simp [MachineDescription.decodeNat] at hdecode
      | blank =>
          exact
            CanonicalLayouts.DovetailLayoutScanner.primitive_runConfig_state_ne_halt_of_reaches_stuck
              CanonicalLayouts.DovetailStagePrefix.natSuffixScannerDescription_haltTransitionFree
              (D := CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.blank :: rest)).map some))
              (stuck :=
                CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.runConfig
                  1
                  (config 200 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.blank :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription,
                  CanonicalLayouts.DovetailStagePrefix.MarkedPrefixScannerDescription,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                omega)
      | zero =>
          exact
            CanonicalLayouts.DovetailLayoutScanner.primitive_runConfig_state_ne_halt_of_reaches_stuck
              CanonicalLayouts.DovetailStagePrefix.natSuffixScannerDescription_haltTransitionFree
              (D := CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.zero :: rest)).map some))
              (stuck :=
                CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.runConfig
                  1
                  (config 200 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.zero :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription,
                  CanonicalLayouts.DovetailStagePrefix.MarkedPrefixScannerDescription,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                omega)
      | one =>
          exact
            CanonicalLayouts.DovetailLayoutScanner.primitive_runConfig_state_ne_halt_of_reaches_stuck
              CanonicalLayouts.DovetailStagePrefix.natSuffixScannerDescription_haltTransitionFree
              (D := CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.one :: rest)).map some))
              (stuck :=
                CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.runConfig
                  1
                  (config 200 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.one :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription,
                  CanonicalLayouts.DovetailStagePrefix.MarkedPrefixScannerDescription,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                omega)
      | moveLeft =>
          exact
            CanonicalLayouts.DovetailLayoutScanner.primitive_runConfig_state_ne_halt_of_reaches_stuck
              CanonicalLayouts.DovetailStagePrefix.natSuffixScannerDescription_haltTransitionFree
              (D := CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.moveLeft :: rest)).map some))
              (stuck :=
                CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.runConfig
                  1
                  (config 200 leftRev
                    ((MachineDescription.encodeCodeWordAsInput
                      (MachineCodeSymbol.moveLeft :: rest)).map some)))
              (k := 1) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription,
                  CanonicalLayouts.DovetailStagePrefix.MarkedPrefixScannerDescription,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.runConfig,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read, Tape.write, Tape.move, Tape.moveRight])
              (by
                change (201 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            CanonicalLayouts.DovetailLayoutScanner.primitive_runConfig_state_ne_halt_of_reaches_stuck
              CanonicalLayouts.DovetailStagePrefix.natSuffixScannerDescription_haltTransitionFree
              (D := CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription)
              (c :=
                config 200 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.moveRight :: rest)).map some))
              (stuck :=
                config 200 leftRev
                  ((MachineDescription.encodeCodeWordAsInput
                    (MachineCodeSymbol.moveRight :: rest)).map some))
              (k := 0) (n := n)
              rfl
              (by
                cases rest <;>
                simp [CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription,
                  CanonicalLayouts.DovetailStagePrefix.MarkedPrefixScannerDescription,
                  StageInputMarkedScannerDescription,
                  config, tapeAtCells, keep, keepMove, writeMove,
                  scanLeftToSentinelRestart, scanLeftToSentinelHalt,
                  MachineDescription.stepConfig,
                  MachineDescription.lookupTransition,
                  MachineDescription.Matches,
                  MachineDescription.transition,
                  MachineDescription.encodeCodeWordAsInput,
                  MachineDescription.encodeCodeSymbolAsInput,
                  Tape.read])
              (by
                change (200 : Nat) ≠ 999
                omega)

theorem natSuffixScannerDescription_runConfig_code_inv
    (baseLeft : List (Option Bool)) (code : Word MachineCodeSymbol)
    {Tout : Tape Bool} {n : Nat}
    (h :
      CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.runConfig
          n
          (config
            CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.start
            baseLeft
            ((MachineDescription.encodeCodeWordAsInput code).map some)) =
        { state :=
            CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.halt
          tape := Tout }) :
    exists stage : Nat,
    exists suffix : Word MachineCodeSymbol,
      code = MachineDescription.encodeNatAppend stage suffix := by
  cases hdecode : MachineDescription.decodeNat code with
  | none =>
      have hne :=
        natSuffixScannerDescription_runConfig_decodeNat_none_ne_halt
          code baseLeft hdecode n
      have hstate :
          (CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.runConfig
            n
            (config
              CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.start
              baseLeft
              ((MachineDescription.encodeCodeWordAsInput code).map some))).state =
            CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.halt := by
        simpa using congrArg MachineDescription.Configuration.state h
      exact False.elim (hne hstate)
  | some parsed =>
      rcases parsed with ⟨stage, suffix⟩
      exact
        ⟨stage, suffix,
          MachineDescription.decodeNat_eq_some_encodeNatAppend hdecode⟩

theorem boolWordSuffixScannerDescription_runConfig_encodeBoolWordAppend_stage_handoff
    (baseLeft : List (Option Bool)) (inputWord : Word Bool)
    (stageRest : Word MachineCodeSymbol)
    {Tinput Tstage : Tape Bool} {nInput nStage : Nat}
    (hinput :
      CanonicalLayouts.DovetailLayoutScanner.BoolWordSuffixScannerDescription.runConfig
          nInput
          (config
            CanonicalLayouts.DovetailLayoutScanner.BoolWordSuffixScannerDescription.start
            baseLeft
            ((MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolWordAppend inputWord
                stageRest)).map some)) =
        { state :=
            CanonicalLayouts.DovetailLayoutScanner.BoolWordSuffixScannerDescription.halt
          tape := Tinput })
    (hstage :
      CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.runConfig
          nStage
          { state :=
              CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.start
            tape := Tape.move Direction.right Tinput } =
        { state :=
            CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.halt
          tape := Tstage }) :
    exists baseAfterInput : List (Option Bool),
      Tape.move Direction.right Tinput =
        tapeAtCells baseAfterInput
          ((MachineDescription.encodeCodeWordAsInput stageRest).map some) := by
  sorry

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_stage_inv
    {code : Word MachineCodeSymbol} {Tout : Tape Bool}
    {inputWord : Word Bool} {stageRest : Word MachineCodeSymbol}
    (h : CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) Tout)
    (h_input : code = MachineCodeSymbol.transition :: MachineDescription.encodeBoolWordAppend inputWord stageRest) :
    exists stage : Nat,
    exists acceptRest : Word MachineCodeSymbol,
      stageRest = MachineDescription.encodeNatAppend stage acceptRest := by
  rcases
      CanonicalLayouts.DovetailLayoutScanner.checkedDovetailLayoutScannerDescription_haltsWithTape_stageField_inv
        h with
    ⟨b, suffixTail, Tinput, Tstage, _Tbody, nInput, nStage,
      _nConfigs, _nReturn, hbits, hinputRun, hstageRun, _hconfigsRun,
      _hreturnRun⟩
  rcases
      CanonicalLayouts.DovetailLayoutScanner.encodeCodeWordAsInput_transition_prefix_inv
        hbits with
    ⟨inputCode, hcode, hinputBits⟩
  have hinputCode :
      inputCode =
        MachineDescription.encodeBoolWordAppend inputWord stageRest := by
    have hcons :
        MachineCodeSymbol.transition :: inputCode =
          MachineCodeSymbol.transition ::
            MachineDescription.encodeBoolWordAppend inputWord
              stageRest :=
      hcode.symm.trans h_input
    simpa using congrArg List.tail hcons
  have hinputRunCode :
      CanonicalLayouts.DovetailLayoutScanner.BoolWordSuffixScannerDescription.runConfig
          nInput
          (config
            CanonicalLayouts.DovetailLayoutScanner.BoolWordSuffixScannerDescription.start
            (List.append
              (CanonicalLayouts.DovetailLayoutScanner.transitionRemainderBits.reverse.map
                some)
              [none])
            ((MachineDescription.encodeCodeWordAsInput
              (MachineDescription.encodeBoolWordAppend inputWord
                stageRest)).map some)) =
        { state :=
            CanonicalLayouts.DovetailLayoutScanner.BoolWordSuffixScannerDescription.halt
          tape := Tinput } := by
    rw [← hinputCode, hinputBits]
    simpa [config] using hinputRun
  rcases
      boolWordSuffixScannerDescription_runConfig_encodeBoolWordAppend_stage_handoff
        (List.append
          (CanonicalLayouts.DovetailLayoutScanner.transitionRemainderBits.reverse.map
            some)
          [none])
        inputWord stageRest hinputRunCode hstageRun with
    ⟨baseAfterInput, hmove⟩
  have hstageRunCode :
      CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.runConfig
          nStage
          (config
            CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.start
            baseAfterInput
            ((MachineDescription.encodeCodeWordAsInput stageRest).map
              some)) =
        { state :=
            CanonicalLayouts.DovetailStagePrefix.NatSuffixScannerDescription.halt
          tape := Tstage } := by
    simpa [config, hmove] using hstageRun
  exact
    natSuffixScannerDescription_runConfig_code_inv
      baseAfterInput stageRest hstageRunCode

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_acceptConfig_inv
    {code : Word MachineCodeSymbol} {Tout : Tape Bool}
    {inputWord : Word Bool} {stage : Nat} {acceptRest : Word MachineCodeSymbol}
    (h : CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) Tout)
    (h_input : code = MachineCodeSymbol.transition :: MachineDescription.encodeBoolWordAppend inputWord (MachineDescription.encodeNatAppend stage acceptRest)) :
    exists acceptConfig : MachineDescription.Configuration,
    exists rejectRest : Word MachineCodeSymbol,
      acceptRest = MachineDescription.encodeConfigurationAppend acceptConfig rejectRest := by
  sorry

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_rejectConfig_inv
    {code : Word MachineCodeSymbol} {Tout : Tape Bool}
    {inputWord : Word Bool} {stage : Nat} {acceptConfig : MachineDescription.Configuration} {rejectRest : Word MachineCodeSymbol}
    (h : CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) Tout)
    (h_input : code = MachineCodeSymbol.transition :: MachineDescription.encodeBoolWordAppend inputWord (MachineDescription.encodeNatAppend stage (MachineDescription.encodeConfigurationAppend acceptConfig rejectRest))) :
    exists rejectConfig : MachineDescription.Configuration,
    exists flagsRest : Word MachineCodeSymbol,
      rejectRest = MachineDescription.encodeConfigurationAppend rejectConfig flagsRest := by
  sorry

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_flags_body_inv
    {code : Word MachineCodeSymbol} {Tout : Tape Bool}
    {inputWord : Word Bool} {stage : Nat} {acceptConfig : MachineDescription.Configuration} {rejectConfig : MachineDescription.Configuration} {flagsRest : Word MachineCodeSymbol}
    (h : CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.HaltsWithTape
          (MachineDescription.encodeCodeWordAsInput code) Tout)
    (h_input : code = MachineCodeSymbol.transition :: MachineDescription.encodeBoolWordAppend inputWord (MachineDescription.encodeNatAppend stage (MachineDescription.encodeConfigurationAppend acceptConfig (MachineDescription.encodeConfigurationAppend rejectConfig flagsRest)))) :
    exists acceptHit : Bool,
    exists rejectHit : Bool,
      flagsRest = MachineDescription.encodeBoolAppend acceptHit (MachineDescription.encodeBoolAppend rejectHit []) ∧
      Tape.move tapeCodePrimitiveCodeWordHandoffMove Tout =
        ParsedLayoutCheckedTape { input := inputWord, stage := stage, acceptConfig := acceptConfig, rejectConfig := rejectConfig, acceptHit := acceptHit, rejectHit := rejectHit } := by
  sorry

theorem checkedDovetailLayoutScannerDescription_haltsWithTape_decodeComplete_inv
    (code : Word MachineCodeSymbol) (T : Tape Bool)
    (h :
      CanonicalLayouts.DovetailLayoutScanner.CheckedDovetailLayoutScannerDescription.HaltsWithTape
        (MachineDescription.encodeCodeWordAsInput code) T) :
    exists L : MachineDescription.DovetailLayout,
      MachineDescription.DovetailLayout.decodeComplete code = some L ∧
      Tape.move tapeCodePrimitiveCodeWordHandoffMove T =
        ParsedLayoutCheckedTape L := by
  rcases CanonicalLayouts.DovetailLayoutScanner.checkedDovetailLayoutScannerDescription_haltsWithTape_inputBoolWord_inv h with
    ⟨inputWord, inputRest, hcode1⟩
  rcases checkedDovetailLayoutScannerDescription_haltsWithTape_stage_inv h hcode1 with
    ⟨stage, stageRest, hcode2⟩
  have hcode12 : code = MachineCodeSymbol.transition :: MachineDescription.encodeBoolWordAppend inputWord (MachineDescription.encodeNatAppend stage stageRest) := by
    rw [hcode1, hcode2]
  rcases checkedDovetailLayoutScannerDescription_haltsWithTape_acceptConfig_inv h hcode12 with
    ⟨acceptConfig, acceptRest, hcode3⟩
  have hcode123 : code = MachineCodeSymbol.transition :: MachineDescription.encodeBoolWordAppend inputWord (MachineDescription.encodeNatAppend stage (MachineDescription.encodeConfigurationAppend acceptConfig acceptRest)) := by
    rw [hcode12, hcode3]
  rcases checkedDovetailLayoutScannerDescription_haltsWithTape_rejectConfig_inv h hcode123 with
    ⟨rejectConfig, rejectRest, hcode4⟩
  have hcode1234 : code = MachineCodeSymbol.transition :: MachineDescription.encodeBoolWordAppend inputWord (MachineDescription.encodeNatAppend stage (MachineDescription.encodeConfigurationAppend acceptConfig (MachineDescription.encodeConfigurationAppend rejectConfig rejectRest))) := by
    rw [hcode123, hcode4]
  rcases checkedDovetailLayoutScannerDescription_haltsWithTape_flags_body_inv h hcode1234 with
    ⟨acceptHit, rejectHit, hcode5, hT⟩
  have hcode12345 : code = MachineCodeSymbol.transition :: MachineDescription.encodeBoolWordAppend inputWord (MachineDescription.encodeNatAppend stage (MachineDescription.encodeConfigurationAppend acceptConfig (MachineDescription.encodeConfigurationAppend rejectConfig (MachineDescription.encodeBoolAppend acceptHit (MachineDescription.encodeBoolAppend rejectHit []))))) := by
    rw [hcode1234, hcode5]
  let L : MachineDescription.DovetailLayout := {
    input := inputWord
    stage := stage
    acceptConfig := acceptConfig
    rejectConfig := rejectConfig
    acceptHit := acceptHit
    rejectHit := rejectHit
  }
  refine ⟨L, ?_, hT⟩
  have henc : code = MachineDescription.DovetailLayout.encode L := by
    exact hcode12345
  rw [henc]
  exact MachineDescription.DovetailLayout.decodeComplete_encode L
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
