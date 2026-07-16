import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Parser.Assembly

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.TotalInversion

open FiniteRecognizer.Interpreter.ParserAssembly

/-!
# Total input inversion boundary

This module isolates the closedness argument from the outer interpreter's
concrete control type. The outer machine supplies one exact phase-projection
contract: a halting outer run exposes the unary fuel prefix and induces
halting runs of the verified header and contextual transition-table parsers.
Their inversion theorems discharge the decomposition.

The malformed-input seams are covered as follows.

* A malformed or truncated outer unary field is discharged by
  `OuterParserPhaseEmbeddingContract.project` and
  `malformedOuterUnary_nonhalts`.
* A missing header, a non-header first token, or any truncated/malformed one
  of the four unary header fields is inverted by
  `headerFieldsParserMachine_haltsFromIn_only_header`; the public
  contrapositive is `FiniteRecognizer.Interpreter.ParserAssembly.headerFieldsParserMachine_nonhalts_of_malformed`.
* A missing transition marker at positive count is rejected directly by
  `transitionListParserMachine_not_haltsFrom_needTransition_empty`,
  `transitionListParserMachine_not_haltsFrom_needTransition_none`, or
  `transitionListParserMachine_not_haltsFrom_needTransition_nonTransition`.
* Within one row, malformed or truncated source unary, read cell, write cell,
  direction, and target unary fields are handled respectively by the private
  inversion chain
  `transitionListParserMachine_haltsFrom_sourceNat_inv`,
  `transitionListParserMachine_haltsFrom_readCell_inv`,
  `transitionListParserMachine_haltsFrom_writeCell_inv`,
  `transitionListParserMachine_haltsFrom_moveField_inv`, and
  `transitionListParserMachine_haltsFrom_targetNat_inv` in
  `TransitionListParser/Soundness.lean`.  Row-boundary return is handled by
  `transitionListParserMachine_haltsFrom_markPosition_context_inv`.
* That private chain is exposed by the authoritative public theorem
  `transitionListParserMachine_halts_encodeNatAppend_only_encodeTransitionsAppend`.
  Its clean and contextual contrapositives below cover every malformed or
  truncated row seam without duplicating the parser proof.
-/

/-- Exact parser evidence projected from a halting outer run. The source
equality inverts the outer unary field; the other fields are the hypotheses
consumed by the two-stage parser assembly inversion. -/
structure ParserPhaseWitness
    (tokens : Word MachineCodeSymbol) where
  fuel : Nat
  encoded : Word MachineCodeSymbol
  headerLeftRev : Word MachineCodeSymbol
  parserBaseLeftRev : Word MachineCodeSymbol
  headerSteps : Nat
  source_eq :
    tokens = MachineDescription.encodeNatAppend fuel encoded
  header_halts :
    TuringMachine.HaltsFromIn headerFieldsParserMachine headerSteps
      { state := HeaderFieldsParserState.needHeader
        tape := headerFieldsParserTape headerLeftRev encoded }
  table_halts :
    forall stateCount start halt count : Nat,
    forall rowTokens : Word MachineCodeSymbol,
      encoded =
          MachineCodeSymbol.header ::
            MachineDescription.encodeNatAppend stateCount
              (MachineDescription.encodeNatAppend start
                (MachineDescription.encodeNatAppend halt
                  (MachineDescription.encodeNatAppend count rowTokens))) ->
        TuringMachine.HaltsFrom transitionListParserMachine
          { state :=
              TransitionListParserState.findCount
                TransitionListParserMarker.initial
            tape :=
              transitionListParserOptionTape
                (none :: parserBaseLeftRev.map some)
                ((MachineDescription.encodeNatAppend count rowTokens).map
                  some) }

/-- The one outer-machine-specific parser obligation.  It is deliberately a
projection from an actual outer halting run, rather than a free-standing
decodability assumption. -/
structure OuterParserPhaseEmbeddingContract
    {outerState : Type}
    (outer : TuringMachine MachineCodeSymbol outerState) where
  project :
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput outer tokens ->
        ParserPhaseWitness tokens

/-- The designated outer halt is exactly the final equal-state accept gate,
and transitions out of it are disabled.  Since `TuringMachine.Halted` means
equality with the designated halt state, this is the precise unique-accept
contract needed by total inversion. -/
structure UniqueFinalEqualAcceptContract
    {outerState : Type}
    (outer : TuringMachine MachineCodeSymbol outerState)
    (finalEqualAccept : outerState) : Prop where
  halt_eq : outer.halt = finalEqualAccept
  transitions_disabled : TuringMachine.HaltingTransitionsDisabled outer

/-- The committed header and contextual table inversions turn a projected
parser witness into one exact encoded machine description and suffix. -/
theorem ParserPhaseWitness.encoded_eq_description
    {tokens : Word MachineCodeSymbol}
    (witness : ParserPhaseWitness tokens) :
    exists D : MachineDescription,
    exists input : Word MachineCodeSymbol,
      witness.encoded =
        MachineDescription.encodeDescriptionAppend D input := by
  exact
    canonicalDescriptionParserAssembly_halts_only_encoded
      witness.header_halts witness.table_halts

/-- Total source inversion, conditional only on the concrete outer phase
embedding. -/
theorem outerInterpreter_halts_only_decoded
    {outerState : Type}
    (outer : TuringMachine MachineCodeSymbol outerState)
    (phaseContract : OuterParserPhaseEmbeddingContract outer)
    {tokens : Word MachineCodeSymbol}
    (hhalts : TuringMachine.HaltsOnInput outer tokens) :
    exists fuel : Nat,
    exists D : MachineDescription,
    exists input : Word MachineCodeSymbol,
      MachineDescription.decodeNat tokens =
        some
          (fuel,
            List.append (MachineDescription.encodeDescription D) input) := by
  let witness := phaseContract.project tokens hhalts
  rcases witness.encoded_eq_description with
    ⟨D, input, hencoded⟩
  refine ⟨witness.fuel, D, input, ?_⟩
  exact
    (congrArg MachineDescription.decodeNat witness.source_eq).trans
      ((MachineDescription.decodeNat_encodeNatAppend
        witness.fuel witness.encoded).trans (by
          rw [hencoded,
            MachineDescription.encodeDescriptionAppend_eq_encodeDescription_append]
          rfl))

/-- Any halted configuration is the unique final equal-state accept gate. -/
theorem halted_only_finalEqualAccept
    {outerState : Type}
    (outer : TuringMachine MachineCodeSymbol outerState)
    (finalEqualAccept : outerState)
    (acceptContract :
      UniqueFinalEqualAcceptContract outer finalEqualAccept)
    {final : TuringMachine.Configuration MachineCodeSymbol outerState}
    (hhalted : TuringMachine.Halted outer final) :
    final.state = finalEqualAccept := by
  exact hhalted.trans acceptContract.halt_eq

/-- Every configuration outside the final equal-state gate is nonhalting in
the designated-state sense, even if its transition happens to be stuck. -/
theorem nonFinalEqualGate_not_halted
    {outerState : Type}
    (outer : TuringMachine MachineCodeSymbol outerState)
    (finalEqualAccept : outerState)
    (acceptContract :
      UniqueFinalEqualAcceptContract outer finalEqualAccept)
    {config : TuringMachine.Configuration MachineCodeSymbol outerState}
    (hne : config.state ≠ finalEqualAccept) :
    ¬ TuringMachine.Halted outer config := by
  intro hhalted
  exact hne
    (halted_only_finalEqualAccept outer finalEqualAccept
      acceptContract hhalted)

/-- The final equal-state gate is terminal for every tape symbol. -/
theorem finalEqualAccept_transition_none
    {outerState : Type}
    (outer : TuringMachine MachineCodeSymbol outerState)
    (finalEqualAccept : outerState)
    (acceptContract :
      UniqueFinalEqualAcceptContract outer finalEqualAccept)
    (cell : Option MachineCodeSymbol) :
    outer.transition finalEqualAccept cell = none := by
  rw [← acceptContract.halt_eq]
  exact acceptContract.transitions_disabled cell

/-- Combined outer closedness statement: one halting run reaches only the
unique equal-state gate and its original word has the canonical
fuel/description/input decomposition. -/
theorem outerInterpreter_halt_total_inversion
    {outerState : Type}
    (outer : TuringMachine MachineCodeSymbol outerState)
    (finalEqualAccept : outerState)
    (phaseContract : OuterParserPhaseEmbeddingContract outer)
    (acceptContract :
      UniqueFinalEqualAcceptContract outer finalEqualAccept)
    {tokens : Word MachineCodeSymbol}
    (hhalts : TuringMachine.HaltsOnInput outer tokens) :
    exists final :
        TuringMachine.Configuration MachineCodeSymbol outerState,
      TuringMachine.Computes outer
          (TuringMachine.initial outer tokens) final ∧
        final.state = finalEqualAccept ∧
        exists fuel : Nat,
        exists D : MachineDescription,
        exists input : Word MachineCodeSymbol,
          MachineDescription.decodeNat tokens =
            some
              (fuel,
                List.append
                  (MachineDescription.encodeDescription D) input) := by
  rcases hhalts with ⟨final, hrun, hhalted⟩
  refine ⟨final, hrun, ?_, ?_⟩
  · exact
      halted_only_finalEqualAccept outer finalEqualAccept
        acceptContract hhalted
  · exact
      outerInterpreter_halts_only_decoded outer phaseContract
        ⟨final, hrun, hhalted⟩

/-! ## Malformed-seam contrapositives -/

/-- Failure of the exact four-unary-field header shape. -/
def MalformedHeaderStream
    (rest : Word MachineCodeSymbol) : Prop :=
  ¬ exists stateCount start halt transitionCount : Nat,
    exists suffix : Word MachineCodeSymbol,
      rest =
        MachineCodeSymbol.header ::
          MachineDescription.encodeNatAppend stateCount
            (MachineDescription.encodeNatAppend start
              (MachineDescription.encodeNatAppend halt
                (MachineDescription.encodeNatAppend transitionCount
                  suffix)))

/-- Failure of exactly `count` complete encoded transition rows.  This
includes a truncated row at any of its five fields. -/
def MalformedTransitionRows
    (count : Nat) (tokens : Word MachineCodeSymbol) : Prop :=
  ¬ exists transitions : List TransitionDescription,
    exists suffix : Word MachineCodeSymbol,
      count = transitions.length ∧
        tokens =
          MachineDescription.encodeTransitionsAppend transitions suffix

/-- Header malformedness is already closed for arbitrary retained left
context. -/
theorem malformedHeaderStream_nonhalts
    {leftRev rest : Word MachineCodeSymbol}
    (hmalformed : MalformedHeaderStream rest) :
    forall steps : Nat,
      ¬ TuringMachine.HaltsFromIn headerFieldsParserMachine steps
        { state := HeaderFieldsParserState.needHeader
          tape := headerFieldsParserTape leftRev rest } := by
  exact headerFieldsParserMachine_nonhalts_of_malformed hmalformed

/-- The authoritative clean-source row inversion, exposed as a named seam
contrapositive. -/
theorem malformedTransitionRows_clean_nonhalts
    {count : Nat} {tokens : Word MachineCodeSymbol}
    (hmalformed : MalformedTransitionRows count tokens) :
    ¬ TuringMachine.HaltsOnInput transitionListParserMachine
      (MachineDescription.encodeNatAppend count tokens) := by
  exact transitionListParserMachine_nonhalts_of_malformed hmalformed

/-- The same malformed-row guarantee behind the real blank separator and
arbitrary retained fuel/header context. -/
theorem malformedTransitionRows_contextual_nonhalts
    (baseLeftRev : Word MachineCodeSymbol)
    {count : Nat} {tokens : Word MachineCodeSymbol}
    (hmalformed : MalformedTransitionRows count tokens) :
    ¬ TuringMachine.HaltsFrom transitionListParserMachine
      { state :=
          TransitionListParserState.findCount
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape
            (none :: baseLeftRev.map some)
            ((MachineDescription.encodeNatAppend count tokens).map some) } := by
  intro hhalts
  exact hmalformed
    (contextualTransitionParserHaltInversion
      baseLeftRev count tokens hhalts)

/-- Positive row count with no next tape cell is the empty-marker seam. -/
theorem missingTransitionMarker_empty_nonhalts
    (leftRev : List (Option MachineCodeSymbol)) :
    ¬ TuringMachine.HaltsFrom transitionListParserMachine
      { state := TransitionListParserState.needTransition
        tape := transitionListParserOptionTape leftRev [] } := by
  exact transitionListParserMachine_not_haltsFrom_needTransition_empty leftRev

/-- Positive row count with a physical blank under the cursor is the blank
marker seam. -/
theorem missingTransitionMarker_blank_nonhalts
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    ¬ TuringMachine.HaltsFrom transitionListParserMachine
      { state := TransitionListParserState.needTransition
        tape :=
          transitionListParserOptionTape leftRev (none :: suffix) } := by
  exact transitionListParserMachine_not_haltsFrom_needTransition_none
    leftRev suffix

/-- Positive row count with any encoded symbol other than `transition` is the
wrong-marker seam. -/
theorem wrongTransitionMarker_nonhalts
    {symbol : MachineCodeSymbol}
    (hsymbol : symbol ≠ MachineCodeSymbol.transition)
    (leftRev suffix : List (Option MachineCodeSymbol)) :
    ¬ TuringMachine.HaltsFrom transitionListParserMachine
      { state := TransitionListParserState.needTransition
        tape :=
          transitionListParserOptionTape leftRev
            (some symbol :: suffix) } := by
  exact transitionListParserMachine_not_haltsFrom_needTransition_nonTransition
    hsymbol leftRev suffix

/-- A semantic decoder failure is an exact certificate that some requested
row is malformed or truncated. -/
theorem malformedTransitionRows_of_decodeTransitions_none
    {count : Nat} {tokens : Word MachineCodeSymbol}
    (hdecode :
      MachineDescription.decodeTransitions count tokens = none) :
    MalformedTransitionRows count tokens := by
  intro hshape
  rcases hshape with ⟨transitions, suffix, hcount, htokens⟩
  rw [hcount, htokens,
    MachineDescription.decodeTransitions_encodeTransitions_append]
    at hdecode
  cases hdecode

/-- Decoder-level row truncation cannot halt the clean parser. -/
theorem decodeTransitions_none_clean_nonhalts
    {count : Nat} {tokens : Word MachineCodeSymbol}
    (hdecode :
      MachineDescription.decodeTransitions count tokens = none) :
    ¬ TuringMachine.HaltsOnInput transitionListParserMachine
      (MachineDescription.encodeNatAppend count tokens) := by
  exact malformedTransitionRows_clean_nonhalts
    (malformedTransitionRows_of_decodeTransitions_none hdecode)

/-- Decoder-level row truncation also cannot halt the contextual parser used
by the real assembly. -/
theorem decodeTransitions_none_contextual_nonhalts
    (baseLeftRev : Word MachineCodeSymbol)
    {count : Nat} {tokens : Word MachineCodeSymbol}
    (hdecode :
      MachineDescription.decodeTransitions count tokens = none) :
    ¬ TuringMachine.HaltsFrom transitionListParserMachine
      { state :=
          TransitionListParserState.findCount
            TransitionListParserMarker.initial
        tape :=
          transitionListParserOptionTape
            (none :: baseLeftRev.map some)
            ((MachineDescription.encodeNatAppend count tokens).map some) } := by
  exact malformedTransitionRows_contextual_nonhalts baseLeftRev
    (malformedTransitionRows_of_decodeTransitions_none hdecode)

/-- Once the outer phase embedding is supplied, a missing or truncated unary
fuel field is impossible on every halting input. -/
theorem malformedOuterUnary_nonhalts
    {outerState : Type}
    (outer : TuringMachine MachineCodeSymbol outerState)
    (phaseContract : OuterParserPhaseEmbeddingContract outer)
    {tokens : Word MachineCodeSymbol}
    (hdecode : MachineDescription.decodeNat tokens = none) :
    ¬ TuringMachine.HaltsOnInput outer tokens := by
  intro hhalts
  rcases outerInterpreter_halts_only_decoded outer phaseContract hhalts with
    ⟨fuel, D, input, hvalid⟩
  rw [hdecode] at hvalid
  cases hvalid

/-- If the unary fuel prefix decodes but the remaining description prefix does
not, the outer interpreter cannot halt.  This is the whole-input corollary
covering malformed headers and malformed/truncated table rows. -/
theorem malformedOuterDescription_nonhalts
    {outerState : Type}
    (outer : TuringMachine MachineCodeSymbol outerState)
    (phaseContract : OuterParserPhaseEmbeddingContract outer)
    {tokens encoded : Word MachineCodeSymbol}
    {fuel : Nat}
    (houter :
      MachineDescription.decodeNat tokens = some (fuel, encoded))
    (hdescription :
      MachineDescription.decodeDescriptionPrefix encoded = none) :
    ¬ TuringMachine.HaltsOnInput outer tokens := by
  intro hhalts
  rcases outerInterpreter_halts_only_decoded outer phaseContract hhalts with
    ⟨parsedFuel, D, input, hvalid⟩
  have hpairs :
      (fuel, encoded) =
        (parsedFuel,
          List.append (MachineDescription.encodeDescription D) input) :=
    Option.some.inj (houter.symm.trans hvalid)
  have hencoded :
      encoded =
        List.append (MachineDescription.encodeDescription D) input :=
    congrArg Prod.snd hpairs
  rw [hencoded,
    MachineDescription.decodeDescriptionPrefix_encodeDescription_append]
    at hdescription
  cases hdescription


end FiniteRecognizer.Interpreter.TotalInversion
end Computability
end FoC
