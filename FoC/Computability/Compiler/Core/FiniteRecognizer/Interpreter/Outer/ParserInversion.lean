import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Outer.TotalInversion

namespace FoC
namespace Computability

open Languages
open FiniteRecognizer ExactFuel StrictProbe

namespace Section53OuterParserInversion

open Section53ParserAssembly
open Section53TotalInversion

/-!
# Outer parser inversion

The outer interpreter retargets the first `PairFuelParser` transition from
inner control directly into the header phase. The terminal seam records
exactly the consumed outer unary field and cannot continue into the unused
second-field parser.
-/

def outerFuelRetargetTransition :
    ProductInput.PairFuelParser.Control -> Option MachineCodeSymbol ->
      Option
        (Option MachineCodeSymbol × Direction ×
          ProductInput.PairFuelParser.Control)
  | .outer, read =>
      ProductInput.PairFuelParser.transition .outer read
  | _, _ => none

def outerFuelRetargetMachine :
    TuringMachine MachineCodeSymbol ProductInput.PairFuelParser.Control where
  start := .outer
  halt := .inner
  transition := outerFuelRetargetTransition
  statesFinite := ProductInput.PairFuelParser.Control.finite

theorem outerFuelRetargetMachine_tick_step
    (leftRev suffix : Word MachineCodeSymbol) :
    outerFuelRetargetMachine.stepConfig
        (ProductInput.PairFuelParser.config .outer leftRev
          (MachineCodeSymbol.tick :: suffix)) =
      some
        (ProductInput.PairFuelParser.config .outer
          (MachineCodeSymbol.tick :: leftRev) suffix) := by
  cases suffix <;> rfl

theorem outerFuelRetargetMachine_done_step
    (leftRev suffix : Word MachineCodeSymbol) :
    outerFuelRetargetMachine.stepConfig
        (ProductInput.PairFuelParser.config .outer leftRev
          (MachineCodeSymbol.done :: suffix)) =
      some
        (ProductInput.PairFuelParser.config .inner
          (MachineCodeSymbol.done :: leftRev) suffix) := by
  cases suffix <;> rfl

/-- Exact forward execution of the terminally retargeted outer unary parser. -/
theorem outerFuelRetargetMachine_run_exact
    (fuel : Nat) (leftRev suffix : Word MachineCodeSymbol) :
    outerFuelRetargetMachine.runConfigExact? (fuel + 1)
        (ProductInput.PairFuelParser.config .outer leftRev
          (MachineDescription.encodeNatAppend fuel suffix)) =
      some
        (ProductInput.PairFuelParser.config .inner
          (List.append (MachineDescription.encodeNat fuel).reverse leftRev)
          suffix) := by
  induction fuel generalizing leftRev with
  | zero =>
      exact outerFuelRetargetMachine_done_step leftRev suffix
  | succ fuel ih =>
      change
        outerFuelRetargetMachine.runConfigExact? ((fuel + 1) + 1)
          (ProductInput.PairFuelParser.config .outer leftRev
            (MachineCodeSymbol.tick ::
              MachineDescription.encodeNatAppend fuel suffix)) = _
      rw [TuringMachine.runConfigExact?]
      rw [outerFuelRetargetMachine_tick_step]
      simp only
      rw [ih]
      simp [MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc]

/-- A terminal retarget into the header phase is possible only after one
complete canonical unary field. -/
theorem outerFuelRetargetMachine_haltsFromIn_only_encodeNatAppend
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn outerFuelRetargetMachine steps
        (ProductInput.PairFuelParser.config .outer leftRev rest)) :
    exists fuel : Nat,
    exists encoded : Word MachineCodeSymbol,
      rest = MachineDescription.encodeNatAppend fuel encoded := by
  induction steps generalizing leftRev rest with
  | zero =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp
      cases hhalt
  | succ steps ih =>
      rcases h with ⟨final, hcomp, hhalt⟩
      cases hcomp with
      | succ hstep hrest =>
          cases rest with
          | nil =>
              cases hstep with
              | mk haction =>
                  simp [outerFuelRetargetMachine,
                    outerFuelRetargetTransition,
                    ProductInput.PairFuelParser.transition,
                    ProductInput.PairFuelParser.config,
                    SerializedShift.cursorTape, Tape.read] at haction
          | cons symbol suffix =>
              cases symbol with
              | tick =>
                  cases hstep with
                  | mk haction =>
                      rename_i write direction nextState
                      cases write with
                      | none =>
                          simp [outerFuelRetargetMachine,
                            outerFuelRetargetTransition,
                            ProductInput.PairFuelParser.transition,
                            ProductInput.PairFuelParser.config,
                            SerializedShift.cursorTape, Tape.read] at haction
                      | some writeSymbol =>
                          cases writeSymbol <;>
                            cases direction <;>
                            cases nextState <;>
                              simp [outerFuelRetargetMachine,
                                outerFuelRetargetTransition,
                                ProductInput.PairFuelParser.transition,
                                ProductInput.PairFuelParser.config,
                                SerializedShift.cursorTape, Tape.read]
                                at haction
                          have htail :
                              TuringMachine.HaltsFromIn
                                outerFuelRetargetMachine steps
                                (ProductInput.PairFuelParser.config .outer
                                  (MachineCodeSymbol.tick :: leftRev)
                                  suffix) := by
                            refine ⟨final, ?_, hhalt⟩
                            cases suffix <;>
                              simpa [outerFuelRetargetMachine,
                                outerFuelRetargetTransition,
                                ProductInput.PairFuelParser.transition,
                                ProductInput.PairFuelParser.config,
                                SerializedShift.cursorTape,
                                Tape.write, Tape.move, Tape.moveRight]
                                using hrest
                          rcases ih htail with ⟨fuel, encoded, hsuffix⟩
                          exact ⟨fuel + 1, encoded, by
                            simp [MachineDescription.encodeNatAppend,
                              MachineDescription.encodeNat, hsuffix]⟩
              | done =>
                  exact ⟨0, suffix, by
                    simp [MachineDescription.encodeNatAppend,
                      MachineDescription.encodeNat]⟩
              | header | transition | blank | zero | one | moveLeft |
                  moveRight =>
                  cases hstep with
                  | mk haction =>
                      simp [outerFuelRetargetMachine,
                        outerFuelRetargetTransition,
                        ProductInput.PairFuelParser.transition,
                        ProductInput.PairFuelParser.config,
                        SerializedShift.cursorTape, Tape.read] at haction

/-- Besides recovering the source unary field, terminal retargeting fixes the
exact reached tape.  This is the concrete seam used to start the header
parser. -/
theorem outerFuelRetargetMachine_haltsFromIn_exact_endpoint
    {steps : Nat}
    {leftRev rest : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFromIn outerFuelRetargetMachine steps
        (ProductInput.PairFuelParser.config .outer leftRev rest)) :
    exists fuel : Nat,
    exists encoded : Word MachineCodeSymbol,
    exists final :
        TuringMachine.Configuration MachineCodeSymbol
          ProductInput.PairFuelParser.Control,
      rest = MachineDescription.encodeNatAppend fuel encoded ∧
      TuringMachine.ComputesIn outerFuelRetargetMachine steps
        (ProductInput.PairFuelParser.config .outer leftRev rest) final ∧
      final =
        ProductInput.PairFuelParser.config .inner
          (List.append (MachineDescription.encodeNat fuel).reverse leftRev)
          encoded := by
  rcases
      outerFuelRetargetMachine_haltsFromIn_only_encodeNatAppend h with
    ⟨fuel, encoded, hrest⟩
  rcases h with ⟨final, hcomp, hhalt⟩
  have hforwardIn :
      TuringMachine.ComputesIn outerFuelRetargetMachine (fuel + 1)
        (ProductInput.PairFuelParser.config .outer leftRev rest)
        (ProductInput.PairFuelParser.config .inner
          (List.append (MachineDescription.encodeNat fuel).reverse leftRev)
          encoded) := by
    apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
    rw [hrest]
    exact outerFuelRetargetMachine_run_exact fuel leftRev encoded
  have hstop :
      TuringMachine.HaltingTransitionsDisabled
        outerFuelRetargetMachine := by
    intro cell
    rfl
  have hforwardHalted :
      TuringMachine.Halted outerFuelRetargetMachine
        (ProductInput.PairFuelParser.config .inner
          (List.append (MachineDescription.encodeNat fuel).reverse leftRev)
          encoded) := by
    rfl
  have hfinal :
      final =
        ProductInput.PairFuelParser.config .inner
          (List.append (MachineDescription.encodeNat fuel).reverse leftRev)
          encoded :=
    TuringMachine.computes_to_halted_unique hstop
      (TuringMachine.computesIn_to_computes hcomp) hhalt
      (TuringMachine.computesIn_to_computes hforwardIn) hforwardHalted
  exact ⟨fuel, encoded, final, hrest, hcomp, hfinal⟩

/-! ## Concrete evidence projected by the runtime phase sum -/

/-- Per-run parser evidence in the exact currencies of the three committed
machines.  The runtime sum only has to project these actual phase runs.  Unary
source inversion is not an assumption: it follows from `fuel_halts` via the
terminal retarget theorem above.

The table run is stated after removal of the inert retained header/fuel
context, at the parser's single-blank padded source.  Consequently the
`ParserPhaseWitness` can use one fixed empty `parserBaseLeftRev`, independent
of the four header values recovered later by header inversion. -/
structure OuterParserPhaseEvidence
    (tokens : Word MachineCodeSymbol) where
  fuelSteps : Nat
  fuel_halts :
    TuringMachine.HaltsFromIn outerFuelRetargetMachine fuelSteps
      (ProductInput.PairFuelParser.config .outer [] tokens)
  header_halts :
    forall fuel : Nat,
    forall encoded : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeNatAppend fuel encoded ->
        exists headerSteps : Nat,
          TuringMachine.HaltsFromIn headerFieldsParserMachine headerSteps
            { state := HeaderFieldsParserState.needHeader
              tape :=
                headerFieldsParserTape
                  (MachineDescription.encodeNat fuel).reverse encoded }
  table_halts :
    forall fuel stateCount start halt count : Nat,
    forall encoded rowTokens : Word MachineCodeSymbol,
      tokens = MachineDescription.encodeNatAppend fuel encoded ->
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
              transitionListParserOptionTape [none]
                ((MachineDescription.encodeNatAppend count rowTokens).map
                  some) }

/-- The terminal fuel inversion plus the two projected parser runs produce
exactly the abstract witness consumed by total input inversion.  Choosing the
decoded field and the header run length is deliberately noncomputable: both
are recovered from propositional halting evidence. -/
noncomputable def OuterParserPhaseEvidence.toParserPhaseWitness
    {tokens : Word MachineCodeSymbol}
    (evidence : OuterParserPhaseEvidence tokens) :
    ParserPhaseWitness tokens := by
  let hdecoded :=
    outerFuelRetargetMachine_haltsFromIn_only_encodeNatAppend
      evidence.fuel_halts
  let fuel := Classical.choose hdecoded
  let hencodedExists := Classical.choose_spec hdecoded
  let encoded := Classical.choose hencodedExists
  let hsource := Classical.choose_spec hencodedExists
  let hheaderExists := evidence.header_halts fuel encoded hsource
  let headerSteps := Classical.choose hheaderExists
  let hheader := Classical.choose_spec hheaderExists
  refine
    { fuel := fuel
      encoded := encoded
      headerLeftRev := (MachineDescription.encodeNat fuel).reverse
      parserBaseLeftRev := []
      headerSteps := headerSteps
      source_eq := hsource
      header_halts := hheader
      table_halts := ?_ }
  intro stateCount start halt count rowTokens hencoded
  simpa using
    evidence.table_halts fuel stateCount start halt count encoded rowTokens
      hsource hencoded

/-- Concrete phase evidence projected from every halting run of an enclosing
machine. This contract supplies the parser projection used by the runtime
control sum. -/
structure OuterParserPhaseEvidenceContract
    {outerState : Type}
    (outer : TuringMachine MachineCodeSymbol outerState) where
  projectEvidence :
    forall tokens : Word MachineCodeSymbol,
      TuringMachine.HaltsOnInput outer tokens ->
        OuterParserPhaseEvidence tokens

/-- Package concrete phase evidence as the abstract total-inversion
contract.  This inherits the one explicit choice boundary from
`OuterParserPhaseEvidence.toParserPhaseWitness`. -/
noncomputable def OuterParserPhaseEvidenceContract.toPhaseEmbeddingContract
    {outerState : Type}
    {outer : TuringMachine MachineCodeSymbol outerState}
    (contract : OuterParserPhaseEvidenceContract outer) :
    OuterParserPhaseEmbeddingContract outer where
  project := fun tokens hhalts =>
    (contract.projectEvidence tokens hhalts).toParserPhaseWitness


end Section53OuterParserInversion
end Computability
end FoC
