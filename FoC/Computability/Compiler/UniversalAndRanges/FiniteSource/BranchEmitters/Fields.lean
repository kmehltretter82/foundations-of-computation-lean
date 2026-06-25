import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.BranchEmitters.Failure

set_option doc.verso true

/-!
# Branch emitter field-boundary cases

Continuation of the split finite-source branch emitter development.
-/

namespace FoC
namespace Computability

open Languages

theorem codePrefixParserBranch_failure_nat_noBoundary
    {current : CodePrefixParserNormalizerState}
    (hnotHalt : current ≠ CodePrefixParserNormalizerState.halt)
    (hboundary :
      codePrefixParserBranchFailureNeedsBoundary current = false)
    (htick :
      forall leftRev suffix : List (Option MachineCodeSymbol),
        TuringMachine.Step codePrefixParserNormalizerMachine
          { state := current
            tape :=
              transitionListParserOptionTape leftRev
                (some MachineCodeSymbol.tick :: suffix) }
          { state := current
            tape :=
              transitionListParserOptionTape
                (some MachineCodeSymbol.tick :: leftRev) suffix })
    (hstuck_empty :
      codePrefixParserNormalizerMachine.transition current none = none)
    (hstuck_bad :
      forall symbol : MachineCodeSymbol,
        symbol ≠ MachineCodeSymbol.tick ->
        symbol ≠ MachineCodeSymbol.done ->
          codePrefixParserNormalizerMachine.transition current
            (some symbol) = none)
    (leftRev tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeNat tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer current
        tape :=
          transitionListParserOptionTape (leftRev.map some)
            (tokens.map some) }
      codePrefixParserBranchFalseOutput := by
  induction tokens generalizing leftRev with
  | nil =>
      exact
        codePrefixParserBranch_failure_from_clean_stuck_noBoundary
          current hnotHalt hboundary leftRev [] (by
            simpa [transitionListParserOptionTape, Tape.read] using
              hstuck_empty)
  | cons symbol rest ih =>
      cases symbol with
      | tick =>
          simp [MachineDescription.decodeNat] at hdecode
          cases htail : MachineDescription.decodeNat rest with
          | none =>
              have hstep :
                  TuringMachine.Step codePrefixParserBranchMachine
                    { state := CodePrefixParserBranchState.normalizer current
                      tape :=
                        transitionListParserOptionTape (leftRev.map some)
                          ((MachineCodeSymbol.tick :: rest).map some) }
                    { state := CodePrefixParserBranchState.normalizer current
                      tape :=
                        transitionListParserOptionTape
                          ((MachineCodeSymbol.tick :: leftRev).map some)
                          (rest.map some) } := by
                simpa using
                  codePrefixParserBranchMachine_step_of_normalizer_step
                    (htick (leftRev.map some) (rest.map some))
              rcases ih (MachineCodeSymbol.tick :: leftRev) htail with
                ⟨final, hcomp, hhalt, hout⟩
              exact
                ⟨final, TuringMachine.Computes.step hstep hcomp,
                  hhalt, hout⟩
          | some parsed =>
              simp [htail] at hdecode
      | done =>
          simp [MachineDescription.decodeNat] at hdecode
      | header =>
          exact
            codePrefixParserBranch_failure_from_clean_stuck_noBoundary
              current hnotHalt hboundary leftRev
              (MachineCodeSymbol.header :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.header (by simp) (by simp))
      | transition =>
          exact
            codePrefixParserBranch_failure_from_clean_stuck_noBoundary
              current hnotHalt hboundary leftRev
              (MachineCodeSymbol.transition :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.transition (by simp) (by simp))
      | blank =>
          exact
            codePrefixParserBranch_failure_from_clean_stuck_noBoundary
              current hnotHalt hboundary leftRev
              (MachineCodeSymbol.blank :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.blank (by simp) (by simp))
      | zero =>
          exact
            codePrefixParserBranch_failure_from_clean_stuck_noBoundary
              current hnotHalt hboundary leftRev
              (MachineCodeSymbol.zero :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.zero (by simp) (by simp))
      | one =>
          exact
            codePrefixParserBranch_failure_from_clean_stuck_noBoundary
              current hnotHalt hboundary leftRev
              (MachineCodeSymbol.one :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.one (by simp) (by simp))
      | moveLeft =>
          exact
            codePrefixParserBranch_failure_from_clean_stuck_noBoundary
              current hnotHalt hboundary leftRev
              (MachineCodeSymbol.moveLeft :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.moveLeft (by simp) (by simp))
      | moveRight =>
          exact
            codePrefixParserBranch_failure_from_clean_stuck_noBoundary
              current hnotHalt hboundary leftRev
              (MachineCodeSymbol.moveRight :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.moveRight (by simp) (by simp))

theorem codePrefixParserBranch_failure_stateCount_noBoundary
    (leftRev tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeNat tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.stateCount
        tape :=
          transitionListParserOptionTape (leftRev.map some)
            (tokens.map some) }
      codePrefixParserBranchFalseOutput :=
  codePrefixParserBranch_failure_nat_noBoundary
    (by intro h; cases h)
    (by rfl)
    (by
      intro leftRev suffix
      exact
        codePrefixParserNormalizerMachine_step_keep_right
          (by simp [codePrefixParserNormalizerMachine,
            codePrefixParserNormalizerKeep]))
    (by simp [codePrefixParserNormalizerMachine])
    (by
      intro symbol htick hdone
      cases symbol <;>
        simp [codePrefixParserNormalizerMachine] at htick hdone ⊢)
    leftRev tokens hdecode

theorem codePrefixParserBranch_failure_startField_noBoundary
    (leftRev tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeNat tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.startField
        tape :=
          transitionListParserOptionTape (leftRev.map some)
            (tokens.map some) }
      codePrefixParserBranchFalseOutput :=
  codePrefixParserBranch_failure_nat_noBoundary
    (by intro h; cases h)
    (by rfl)
    (by
      intro leftRev suffix
      exact
        codePrefixParserNormalizerMachine_step_keep_right
          (by simp [codePrefixParserNormalizerMachine,
            codePrefixParserNormalizerKeep]))
    (by simp [codePrefixParserNormalizerMachine])
    (by
      intro symbol htick hdone
      cases symbol <;>
        simp [codePrefixParserNormalizerMachine] at htick hdone ⊢)
    leftRev tokens hdecode

theorem codePrefixParserBranch_failure_haltField_noBoundary
    (leftRev tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeNat tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.haltField
        tape :=
          transitionListParserOptionTape (leftRev.map some)
            (tokens.map some) }
      codePrefixParserBranchFalseOutput :=
  codePrefixParserBranch_failure_nat_noBoundary
    (by intro h; cases h)
    (by rfl)
    (by
      intro leftRev suffix
      exact
        codePrefixParserNormalizerMachine_step_keep_right
          (by simp [codePrefixParserNormalizerMachine,
            codePrefixParserNormalizerKeep]))
    (by simp [codePrefixParserNormalizerMachine])
      (by
        intro symbol htick hdone
        cases symbol <;>
          simp [codePrefixParserNormalizerMachine] at htick hdone ⊢)
    leftRev tokens hdecode

theorem codePrefixParserBranch_computes_nat_noBoundary
    {current next : CodePrefixParserNormalizerState}
    (htick :
      forall leftRev suffix : Word MachineCodeSymbol,
        TuringMachine.Step codePrefixParserNormalizerMachine
          { state := current
            tape :=
              codePrefixParserNormalizerTape leftRev
                (MachineCodeSymbol.tick :: suffix) }
          { state := current
            tape :=
              codePrefixParserNormalizerTape
                (MachineCodeSymbol.tick :: leftRev) suffix })
    (hdone :
      forall leftRev suffix : Word MachineCodeSymbol,
        TuringMachine.Step codePrefixParserNormalizerMachine
          { state := current
            tape :=
              codePrefixParserNormalizerTape leftRev
                (MachineCodeSymbol.done :: suffix) }
          { state := next
            tape :=
              codePrefixParserNormalizerTape
                (MachineCodeSymbol.done :: leftRev) suffix })
    (leftRev tokens suffix : Word MachineCodeSymbol)
    (n : Nat)
    (hdecode : MachineDescription.decodeNat tokens = some (n, suffix)) :
    TuringMachine.Computes codePrefixParserBranchMachine
      { state := CodePrefixParserBranchState.normalizer current
        tape :=
          transitionListParserOptionTape (leftRev.map some)
            (tokens.map some) }
      { state := CodePrefixParserBranchState.normalizer next
        tape :=
          transitionListParserOptionTape
            ((List.append (MachineDescription.encodeNat n).reverse
              leftRev).map some)
            (suffix.map some) } := by
  have htokens :
      tokens = MachineDescription.encodeNatAppend n suffix :=
    MachineDescription.decodeNat_eq_some_encodeNatAppend hdecode
  have hnorm :=
    codePrefixParserNormalizer_computes_nat'
      current next htick hdone leftRev n suffix
  have hbranch :=
    codePrefixParserBranchMachine_computes_of_normalizer_computes hnorm
  simpa [htokens, codePrefixParserBranchLiftConfig,
    codePrefixParserNormalizerTape,
    transitionListParserTape_eq_optionTape_map,
    List.map_append, List.map_reverse] using hbranch

theorem codePrefixParserBranch_failure_nat_boundary
    {current : CodePrefixParserNormalizerState}
    (hboundary :
      codePrefixParserBranchFailureNeedsBoundary current = true)
    (htick :
      forall leftRev suffix : List (Option MachineCodeSymbol),
        TuringMachine.Step codePrefixParserNormalizerMachine
          { state := current
            tape :=
              transitionListParserOptionTape leftRev
                (some MachineCodeSymbol.tick :: suffix) }
          { state := current
            tape :=
              transitionListParserOptionTape
                (some MachineCodeSymbol.tick :: leftRev) suffix })
    (hstuck_empty :
      codePrefixParserNormalizerMachine.transition current none = none)
    (hstuck_bad :
      forall symbol : MachineCodeSymbol,
        symbol ≠ MachineCodeSymbol.tick ->
        symbol ≠ MachineCodeSymbol.done ->
          codePrefixParserNormalizerMachine.transition current
            (some symbol) = none)
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeNat tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer current
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      codePrefixParserBranchFalseOutput := by
  induction tokens generalizing leftSymbols with
  | nil =>
      exact
        codePrefixParserBranch_failure_from_stuck_boundary
          current hboundary leftSymbols prefixLeft [] (by
            simpa [transitionListParserOptionTape, Tape.read] using
              hstuck_empty)
  | cons symbol rest ih =>
      cases symbol with
      | tick =>
          simp [MachineDescription.decodeNat] at hdecode
          cases htail : MachineDescription.decodeNat rest with
          | none =>
              have hstep :
                  TuringMachine.Step codePrefixParserBranchMachine
                    { state := CodePrefixParserBranchState.normalizer current
                      tape :=
                        transitionListParserOptionTape
                          (List.append (leftSymbols.map some)
                            (none :: prefixLeft.map some))
                          ((MachineCodeSymbol.tick :: rest).map some) }
                    { state := CodePrefixParserBranchState.normalizer current
                      tape :=
                        transitionListParserOptionTape
                          (List.append
                            ((MachineCodeSymbol.tick :: leftSymbols).map
                              some)
                            (none :: prefixLeft.map some))
                          (rest.map some) } := by
                simpa [List.append_assoc] using
                  codePrefixParserBranchMachine_step_of_normalizer_step
                    (htick
                      (List.append (leftSymbols.map some)
                        (none :: prefixLeft.map some))
                      (rest.map some))
              rcases ih (MachineCodeSymbol.tick :: leftSymbols) htail with
                ⟨final, hcomp, hhalt, hout⟩
              exact
                ⟨final, TuringMachine.Computes.step hstep hcomp,
                  hhalt, hout⟩
          | some parsed =>
              simp [htail] at hdecode
      | done =>
          simp [MachineDescription.decodeNat] at hdecode
      | header =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.header :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.header (by simp) (by simp))
      | transition =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.transition :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.transition (by simp) (by simp))
      | blank =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.blank :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.blank (by simp) (by simp))
      | zero =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.zero :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.zero (by simp) (by simp))
      | one =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.one :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.one (by simp) (by simp))
      | moveLeft =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.moveLeft :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.moveLeft (by simp) (by simp))
      | moveRight =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.moveRight :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.moveRight (by simp) (by simp))

theorem codePrefixParserBranch_failure_cell_boundary
    {current : CodePrefixParserNormalizerState}
    (hboundary :
      codePrefixParserBranchFailureNeedsBoundary current = true)
    (hstuck_empty :
      codePrefixParserNormalizerMachine.transition current none = none)
    (hstuck_bad :
      forall symbol : MachineCodeSymbol,
        symbol ≠ MachineCodeSymbol.blank ->
        symbol ≠ MachineCodeSymbol.zero ->
        symbol ≠ MachineCodeSymbol.one ->
          codePrefixParserNormalizerMachine.transition current
            (some symbol) = none)
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeCell tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer current
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      codePrefixParserBranchFalseOutput := by
  cases tokens with
  | nil =>
      exact
        codePrefixParserBranch_failure_from_stuck_boundary
          current hboundary leftSymbols prefixLeft [] (by
            simpa [transitionListParserOptionTape, Tape.read] using
              hstuck_empty)
  | cons symbol rest =>
      cases symbol with
      | blank =>
          simp [MachineDescription.decodeCell] at hdecode
      | zero =>
          simp [MachineDescription.decodeCell] at hdecode
      | one =>
          simp [MachineDescription.decodeCell] at hdecode
      | header =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.header :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.header
                    (by simp) (by simp) (by simp))
      | transition =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.transition :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.transition
                    (by simp) (by simp) (by simp))
      | tick =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.tick :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.tick
                    (by simp) (by simp) (by simp))
      | done =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.done :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.done
                    (by simp) (by simp) (by simp))
      | moveLeft =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.moveLeft :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.moveLeft
                    (by simp) (by simp) (by simp))
      | moveRight =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.moveRight :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.moveRight
                    (by simp) (by simp) (by simp))

theorem codePrefixParserBranch_failure_direction_boundary
    {current : CodePrefixParserNormalizerState}
    (hboundary :
      codePrefixParserBranchFailureNeedsBoundary current = true)
    (hstuck_empty :
      codePrefixParserNormalizerMachine.transition current none = none)
    (hstuck_bad :
      forall symbol : MachineCodeSymbol,
        symbol ≠ MachineCodeSymbol.moveLeft ->
        symbol ≠ MachineCodeSymbol.moveRight ->
          codePrefixParserNormalizerMachine.transition current
            (some symbol) = none)
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeDirection tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer current
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      codePrefixParserBranchFalseOutput := by
  cases tokens with
  | nil =>
      exact
        codePrefixParserBranch_failure_from_stuck_boundary
          current hboundary leftSymbols prefixLeft [] (by
            simpa [transitionListParserOptionTape, Tape.read] using
              hstuck_empty)
  | cons symbol rest =>
      cases symbol with
      | moveLeft =>
          simp [MachineDescription.decodeDirection] at hdecode
      | moveRight =>
          simp [MachineDescription.decodeDirection] at hdecode
      | header =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.header :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.header (by simp) (by simp))
      | transition =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.transition :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.transition
                    (by simp) (by simp))
      | tick =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.tick :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.tick (by simp) (by simp))
      | done =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.done :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.done (by simp) (by simp))
      | blank =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.blank :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.blank (by simp) (by simp))
      | zero =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.zero :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.zero (by simp) (by simp))
      | one =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              current hboundary leftSymbols prefixLeft
              (MachineCodeSymbol.one :: rest)
              (by
                simpa [transitionListParserOptionTape, Tape.read] using
                  hstuck_bad MachineCodeSymbol.one (by simp) (by simp))

theorem codePrefixParserBranch_failure_sourceNat_boundary
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeNat tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.sourceNat
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      codePrefixParserBranchFalseOutput :=
  codePrefixParserBranch_failure_nat_boundary
    (current := CodePrefixParserNormalizerState.sourceNat)
    (by rfl)
    codePrefixParserNormalizerMachine_step_sourceNat_tick
    (by simp [codePrefixParserNormalizerMachine])
    (by
      intro symbol htick hdone
      cases symbol <;>
        simp [codePrefixParserNormalizerMachine] at htick hdone ⊢)
      leftSymbols prefixLeft tokens hdecode

theorem codePrefixParserBranch_failure_seekCountDoneInitial_boundary
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeNat tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          (CodePrefixParserNormalizerState.seekCountDone
            TransitionListParserMarker.initial)
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      codePrefixParserBranchFalseOutput :=
  codePrefixParserBranch_failure_nat_boundary
    (current :=
      CodePrefixParserNormalizerState.seekCountDone
        TransitionListParserMarker.initial)
    (by rfl)
    codePrefixParserNormalizerMachine_step_seekCountDone_initial_tick
    (by simp [codePrefixParserNormalizerMachine])
    (by
      intro symbol htick hdone
      cases symbol <;>
        simp [codePrefixParserNormalizerMachine] at htick hdone ⊢)
    leftSymbols prefixLeft tokens hdecode

theorem codePrefixParserBranch_failure_findInitialCount_boundary
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeNat tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.findInitialCount
        tape :=
            transitionListParserOptionTape
              (List.append (leftSymbols.map some)
                (none :: prefixLeft.map some))
              (tokens.map some) }
      codePrefixParserBranchFalseOutput := by
  cases tokens with
  | nil =>
      exact
        codePrefixParserBranch_failure_from_stuck_boundary
          CodePrefixParserNormalizerState.findInitialCount
          (by rfl) leftSymbols prefixLeft [] (by
            simp [codePrefixParserNormalizerMachine,
              transitionListParserOptionTape, Tape.read])
  | cons symbol rest =>
      cases symbol with
      | tick =>
          simp [MachineDescription.decodeNat] at hdecode
          cases htail : MachineDescription.decodeNat rest with
          | none =>
              have hstep :
                  TuringMachine.Step codePrefixParserBranchMachine
                    { state := CodePrefixParserBranchState.normalizer
                        CodePrefixParserNormalizerState.findInitialCount
                      tape :=
                        transitionListParserOptionTape
                          (List.append (leftSymbols.map some)
                            (none :: prefixLeft.map some))
                          ((MachineCodeSymbol.tick :: rest).map some) }
                    { state := CodePrefixParserBranchState.normalizer
                        (CodePrefixParserNormalizerState.seekCountDone
                          TransitionListParserMarker.initial)
                      tape :=
                        transitionListParserOptionTape
                          (List.append
                            ((MachineCodeSymbol.blank :: leftSymbols).map
                              some)
                            (none :: prefixLeft.map some))
                          (rest.map some) } := by
                simpa [List.append_assoc] using
                  codePrefixParserBranchMachine_step_of_normalizer_step
                    (codePrefixParserNormalizerMachine_step_findInitialCount_tick
                      (List.append (leftSymbols.map some)
                        (none :: prefixLeft.map some))
                      (rest.map some))
              rcases
                  codePrefixParserBranch_failure_seekCountDoneInitial_boundary
                    (MachineCodeSymbol.blank :: leftSymbols)
                    prefixLeft rest htail with
                ⟨final, hcomp, hhalt, hout⟩
              exact
                ⟨final, TuringMachine.Computes.step hstep hcomp,
                  hhalt, hout⟩
          | some parsed =>
              simp [htail] at hdecode
      | done =>
          simp [MachineDescription.decodeNat] at hdecode
      | header =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.findInitialCount
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.header :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | transition =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.findInitialCount
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.transition :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | blank =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.findInitialCount
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.blank :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | zero =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.findInitialCount
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.zero :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | one =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.findInitialCount
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.one :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | moveLeft =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.findInitialCount
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.moveLeft :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])
      | moveRight =>
          exact
            codePrefixParserBranch_failure_from_stuck_boundary
              CodePrefixParserNormalizerState.findInitialCount
              (by rfl) leftSymbols prefixLeft
              (MachineCodeSymbol.moveRight :: rest) (by
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read])

theorem codePrefixParserBranch_failure_targetNat_boundary
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeNat tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.targetNat
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      codePrefixParserBranchFalseOutput :=
  codePrefixParserBranch_failure_nat_boundary
    (current := CodePrefixParserNormalizerState.targetNat)
    (by rfl)
    codePrefixParserNormalizerMachine_step_targetNat_tick
    (by simp [codePrefixParserNormalizerMachine])
    (by
      intro symbol htick hdone
      cases symbol <;>
        simp [codePrefixParserNormalizerMachine] at htick hdone ⊢)
    leftSymbols prefixLeft tokens hdecode

theorem codePrefixParserBranch_failure_readCell_boundary
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeCell tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.readCell
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      codePrefixParserBranchFalseOutput :=
  codePrefixParserBranch_failure_cell_boundary
    (current := CodePrefixParserNormalizerState.readCell)
    (by rfl)
    (by simp [codePrefixParserNormalizerMachine])
    (by
      intro symbol hblank hzero hone
      cases symbol <;>
        simp [codePrefixParserNormalizerMachine] at hblank hzero hone ⊢)
    leftSymbols prefixLeft tokens hdecode

theorem codePrefixParserBranch_failure_writeCell_boundary
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeCell tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.writeCell
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      codePrefixParserBranchFalseOutput :=
  codePrefixParserBranch_failure_cell_boundary
    (current := CodePrefixParserNormalizerState.writeCell)
    (by rfl)
    (by simp [codePrefixParserNormalizerMachine])
    (by
      intro symbol hblank hzero hone
      cases symbol <;>
        simp [codePrefixParserNormalizerMachine] at hblank hzero hone ⊢)
    leftSymbols prefixLeft tokens hdecode

theorem codePrefixParserBranch_failure_moveField_boundary
    (leftSymbols prefixLeft tokens : Word MachineCodeSymbol)
    (hdecode : MachineDescription.decodeDirection tokens = none) :
    codePrefixParserBranchHaltsFromWithOutput
      { state := CodePrefixParserBranchState.normalizer
          CodePrefixParserNormalizerState.moveField
        tape :=
          transitionListParserOptionTape
            (List.append (leftSymbols.map some)
              (none :: prefixLeft.map some))
            (tokens.map some) }
      codePrefixParserBranchFalseOutput :=
  codePrefixParserBranch_failure_direction_boundary
    (current := CodePrefixParserNormalizerState.moveField)
    (by rfl)
    (by simp [codePrefixParserNormalizerMachine])
    (by
      intro symbol hleft hright
      cases symbol <;>
        simp [codePrefixParserNormalizerMachine] at hleft hright ⊢)
    leftSymbols prefixLeft tokens hdecode

end Computability
end FoC
