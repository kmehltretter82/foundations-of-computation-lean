import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.Normalizer.Base

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

theorem codePrefixParserNormalizerMachine_haltsFromIn_needHeader_head
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.needHeader
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists suffix : Word MachineCodeSymbol,
      rest = MachineCodeSymbol.header :: suffix := by
  cases steps with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | header =>
                  exact ⟨suffix, rfl⟩
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | tick =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | done =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

theorem codePrefixParserNormalizerMachine_haltsFromIn_stateCount_nat
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.stateCount
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists n : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest = MachineDescription.encodeNatAppend n suffix := by
  induction steps generalizing leftRev rest with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps ih =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | tick =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_tick_stateCount
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.stateCount
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.tick :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases ih htail with
                    ⟨n, parsedSuffix, hsuffix⟩
                  exact
                    ⟨n + 1, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  exact
                    ⟨0, suffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat]⟩
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

theorem codePrefixParserNormalizerMachine_haltsFromIn_startField_nat
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.startField
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists n : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest = MachineDescription.encodeNatAppend n suffix := by
  induction steps generalizing leftRev rest with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps ih =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | tick =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_tick_startField
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.startField
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.tick :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases ih htail with
                    ⟨n, parsedSuffix, hsuffix⟩
                  exact
                    ⟨n + 1, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  exact
                    ⟨0, suffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat]⟩
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

theorem codePrefixParserNormalizerMachine_haltsFromIn_haltField_nat
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.haltField
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists n : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest = MachineDescription.encodeNatAppend n suffix := by
  induction steps generalizing leftRev rest with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps ih =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | tick =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_tick_haltField
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.haltField
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.tick :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases ih htail with
                    ⟨n, parsedSuffix, hsuffix⟩
                  exact
                    ⟨n + 1, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  exact
                    ⟨0, suffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat]⟩
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

theorem codePrefixParserNormalizerMachine_haltsFromIn_startField_fields
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.startField
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists start halt : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest =
        MachineDescription.encodeNatAppend start
          (MachineDescription.encodeNatAppend halt suffix) := by
  induction steps generalizing leftRev rest with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps ih =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | tick =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_tick_startField
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.startField
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.tick :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases ih htail with
                    ⟨start, halt, parsedSuffix, hsuffix⟩
                  exact
                    ⟨start + 1, halt, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_done_startField
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.haltField
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.done :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases
                    codePrefixParserNormalizerMachine_haltsFromIn_haltField_nat
                      htail with
                    ⟨halt, parsedSuffix, hsuffix⟩
                  exact
                    ⟨0, halt, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

theorem codePrefixParserNormalizerMachine_haltsFromIn_stateCount_fields
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.stateCount
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists stateCount start halt : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest =
        MachineDescription.encodeNatAppend stateCount
          (MachineDescription.encodeNatAppend start
            (MachineDescription.encodeNatAppend halt suffix)) := by
  induction steps generalizing leftRev rest with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps ih =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | tick =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_tick_stateCount
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.stateCount
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.tick :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases ih htail with
                    ⟨stateCount, start, halt, parsedSuffix, hsuffix⟩
                  exact
                    ⟨stateCount + 1, start, halt, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_done_stateCount
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.startField
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.done :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases
                    codePrefixParserNormalizerMachine_haltsFromIn_startField_fields
                      htail with
                    ⟨start, halt, parsedSuffix, hsuffix⟩
                  exact
                    ⟨0, start, halt, parsedSuffix,
                      by
                        simp [MachineDescription.encodeNatAppend,
                          MachineDescription.encodeNat, hsuffix]⟩
              | header =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

theorem codePrefixParserNormalizerMachine_haltsFromIn_needHeader_fields
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn
        codePrefixParserNormalizerMachine steps
        { state := CodePrefixParserNormalizerState.needHeader
          tape := codePrefixParserNormalizerTape leftRev rest }) :
    exists stateCount start halt : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt suffix)) := by
  cases steps with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      simp [TuringMachine.Halted,
        codePrefixParserNormalizerMachine] at hhalt
  | succ steps =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [codePrefixParserNormalizerMachine,
                    codePrefixParserNormalizerTape,
                    transitionListParserTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | header =>
                  have hnext :=
                    TuringMachine.step_deterministic hstep
                      (codePrefixParserNormalizer_step_header
                        leftRev suffix)
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        codePrefixParserNormalizerMachine steps
                        { state :=
                            CodePrefixParserNormalizerState.stateCount
                          tape :=
                            codePrefixParserNormalizerTape
                              (MachineCodeSymbol.header :: leftRev)
                              suffix } :=
                    ⟨final, hrest, hhalt⟩
                  rcases
                    codePrefixParserNormalizerMachine_haltsFromIn_stateCount_fields
                      htail with
                    ⟨stateCount, start, halt, parsedSuffix, hsuffix⟩
                  exact
                    ⟨stateCount, start, halt, parsedSuffix,
                      by simp [hsuffix]⟩
              | transition =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | tick =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | done =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | blank =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | zero =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | one =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveLeft =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction
              | moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [codePrefixParserNormalizerMachine,
                        codePrefixParserNormalizerTape,
                        transitionListParserTape, Tape.read] at haction

/-!
**Normalizer code-spec frontier.**  The concrete
{name}`codePrefixParserNormalizerMachine` is the finite-state witness used by
the first universal-prefix scaffold.  Its remaining correctness proof is split
into soundness and completeness directions; the packaged spec below keeps
downstream construction code independent of that split.
-/

theorem codePrefixParserNormalizerMachine_haltsWithOutputIn_needHeader_fields
    {steps : Nat} {tokens out : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsWithOutputIn
        codePrefixParserNormalizerMachine steps tokens out) :
    exists stateCount start halt : Nat,
    exists suffix : Word MachineCodeSymbol,
      tokens =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt suffix)) := by
  have hhalts :
      TuringMachine.HaltsOnInputIn
        codePrefixParserNormalizerMachine steps tokens :=
    TuringMachine.halts_with_output_in_implies_halts_in h
  exact
    codePrefixParserNormalizerMachine_haltsFromIn_needHeader_fields
      (steps := steps) (leftRev := []) (rest := tokens)
      (by
        simpa [TuringMachine.HaltsOnInputIn, TuringMachine.initial,
          codePrefixParserNormalizerMachine,
          codePrefixParserNormalizerTape_nil_eq_input] using hhalts)

theorem codePrefixParserNormalizerMachine_haltsWithOutput_needHeader_fields
    {tokens out : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsWithOutput
        codePrefixParserNormalizerMachine tokens out) :
    exists stateCount start halt : Nat,
    exists suffix : Word MachineCodeSymbol,
      tokens =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt suffix)) := by
  rcases
      TuringMachine.halts_with_output_to_halts_with_output_in h with
    ⟨steps, hsteps⟩
  exact
    codePrefixParserNormalizerMachine_haltsWithOutputIn_needHeader_fields
      hsteps

theorem decodeDescriptionPrefix_of_header_and_decodeTransitions
    {tokens rest : Word MachineCodeSymbol}
    {stateCount start halt transitionCount : Nat}
    {transitions : List TransitionDescription}
    {input : Word MachineCodeSymbol}
    (htokens :
      tokens =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt
                (MachineDescription.encodeNatAppend transitionCount rest))))
    (htrans :
      MachineDescription.decodeTransitions transitionCount rest =
        some (transitions, input)) :
    MachineDescription.decodeDescriptionPrefix tokens =
      some
        (({ stateCount := stateCount
            start := start
            halt := halt
            transitions := transitions } : MachineDescription),
          input) := by
  subst tokens
  simp [MachineDescription.decodeDescriptionPrefix,
    MachineDescription.decodeNat_encodeNatAppend, htrans]

theorem codePrefixParserNormalizerMachine_haltsWithOutput_decodeTransitions
    {tokens out transitionBlock : Word MachineCodeSymbol}
    {stateCount start halt : Nat}
    (h :
      TuringMachine.HaltsWithOutput
        codePrefixParserNormalizerMachine tokens out)
    (htokens :
      tokens =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt transitionBlock))) :
    exists transitionCount : Nat,
    exists rest : Word MachineCodeSymbol,
    exists transitions : List TransitionDescription,
    exists input : Word MachineCodeSymbol,
      transitionBlock =
          MachineDescription.encodeNatAppend transitionCount rest ∧
        MachineDescription.decodeTransitions transitionCount rest =
          some (transitions, input) := by
  sorry

theorem codePrefixParserNormalizerMachine_haltsWithOutput_decodePrefix
    (tokens out : Word MachineCodeSymbol)
    (h :
      TuringMachine.HaltsWithOutput
        codePrefixParserNormalizerMachine tokens out) :
    exists D : MachineDescription,
    exists input : Word MachineCodeSymbol,
      MachineDescription.decodeDescriptionPrefix tokens =
        some (D, input) := by
  rcases
      codePrefixParserNormalizerMachine_haltsWithOutput_needHeader_fields
        h with
    ⟨stateCount, start, halt, transitionBlock, htokens⟩
  rcases
      codePrefixParserNormalizerMachine_haltsWithOutput_decodeTransitions
        h htokens with
    ⟨transitionCount, rest, transitions, input, hblock, htrans⟩
  refine
    ⟨{ stateCount := stateCount
       start := start
       halt := halt
       transitions := transitions }, input, ?_⟩
  exact
    decodeDescriptionPrefix_of_header_and_decodeTransitions
      (stateCount := stateCount) (start := start) (halt := halt)
      (transitionCount := transitionCount) (rest := rest)
      (transitions := transitions) (input := input)
      (by simpa [hblock] using htokens)
      htrans

theorem codePrefixParserNormalizerMachine_haltsWithOutput_output_eq_input
    (tokens out : Word MachineCodeSymbol)
    (h :
      TuringMachine.HaltsWithOutput
        codePrefixParserNormalizerMachine tokens out) :
    out = tokens := by
  sorry

theorem codePrefixParserNormalizerMachine_haltsWithOutput_only_decode
    (tokens out : Word MachineCodeSymbol)
    (h :
      TuringMachine.HaltsWithOutput
        codePrefixParserNormalizerMachine tokens out) :
    out = tokens ∧
      exists D : MachineDescription,
      exists input : Word MachineCodeSymbol,
        MachineDescription.decodeDescriptionPrefix tokens =
          some (D, input) := by
  exact
    ⟨codePrefixParserNormalizerMachine_haltsWithOutput_output_eq_input
        tokens out h,
      codePrefixParserNormalizerMachine_haltsWithOutput_decodePrefix
        tokens out h⟩

theorem codePrefixParserNormalizerMachine_haltsWithOutput_encodeDescriptionAppend
    (D : MachineDescription) (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsWithOutput
      codePrefixParserNormalizerMachine
      (MachineDescription.encodeDescriptionAppend D input)
      (MachineDescription.encodeDescriptionAppend D input) := by
  sorry

theorem codePrefixParserNormalizerMachine_haltsWithOutput_encodeDescription_append
    (D : MachineDescription) (input : Word MachineCodeSymbol) :
    TuringMachine.HaltsWithOutput
      codePrefixParserNormalizerMachine
      (List.append (MachineDescription.encodeDescription D) input)
      (List.append (MachineDescription.encodeDescription D) input) := by
  rw [← MachineDescription.encodeDescriptionAppend_eq_encodeDescription_append
    D input]
  exact
    codePrefixParserNormalizerMachine_haltsWithOutput_encodeDescriptionAppend
      D input

theorem codePrefixParserNormalizerMachine_code_sound
    (tokens out : Word MachineCodeSymbol)
    (h :
      TuringMachine.HaltsWithOutput
        codePrefixParserNormalizerMachine tokens out) :
    CodePrefixParserNormalizerCode.transform tokens = some out := by
  rcases
      codePrefixParserNormalizerMachine_haltsWithOutput_only_decode
        tokens out h with
    ⟨hout, D, input, hdecode⟩
  exact
    (codePrefixParserNormalizerCode_transform_eq_some_iff
      tokens out).mpr
      ⟨D, input, hdecode,
        by
          rw [hout]
          exact
            MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
              hdecode⟩

theorem codePrefixParserNormalizerMachine_code_complete
    (tokens out : Word MachineCodeSymbol)
    (h : CodePrefixParserNormalizerCode.transform tokens = some out) :
    TuringMachine.HaltsWithOutput
      codePrefixParserNormalizerMachine tokens out := by
  rcases
      (codePrefixParserNormalizerCode_transform_eq_some_iff
        tokens out).mp h with
    ⟨D, input, hdecode, hout⟩
  have htokens :
      tokens = List.append (MachineDescription.encodeDescription D) input :=
    MachineDescription.decodeDescriptionPrefix_eq_some_encodeDescription_append
      hdecode
  rw [htokens, hout]
  exact
    codePrefixParserNormalizerMachine_haltsWithOutput_encodeDescription_append
      D input

theorem codePrefixParserNormalizerMachine_code_spec :
    CodePrefixParserNormalizerCodeMachineSpec
      codePrefixParserNormalizerMachine := by
  intro tokens out
  constructor
  · exact codePrefixParserNormalizerMachine_code_sound tokens out
  · exact codePrefixParserNormalizerMachine_code_complete tokens out


end Computability
end FoC
