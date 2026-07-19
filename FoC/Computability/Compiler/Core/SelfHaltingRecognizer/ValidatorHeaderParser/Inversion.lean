import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorHeaderParser.Runs

set_option doc.verso true

/-!
# Closed inversion of the Boolean header parser

The inversion works at four-bit token boundaries.  Any malformed token reaches
a stuck nonhalt configuration.  Header, {lit}`tick`, and {lit}`done` tokens use
the exact four-step runs from the forward module, so one unary-field induction
serves all four fixed natural-number fields.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer

open Languages
open MachineDescription

open FoC.Computability.DovetailInitialLayoutInitializer
open FoC.Computability.DovetailInitialLayoutInitializer.StageInputMarkedScanner

private abbrev VHP := ValidatorHeaderParserDescription

/-- Padded Boolean cells for an arbitrary canonical code word. -/
def validatorHeaderCodeCells
    (code : Word MachineCodeSymbol) : List (Option Bool) :=
  List.append ((encodeCodeWordAsInput code).map some) [none]
@[simp] theorem validatorHeaderCodeCells_nil :
    validatorHeaderCodeCells [] = [none] := rfl


/-- Padded token-boundary source tape for the leaf-2 parser. -/
def validatorHeaderCodePaddedStartTape
    (code : Word MachineCodeSymbol) : Tape Bool :=
  tapeAtCells [none] (validatorHeaderCodeCells code)

private theorem validatorHeaderMapSomeAppendInv
    (left right : Word Bool) :
    (List.append left right).map some =
      List.append (left.map some) (right.map some) := by
  induction left with
  | nil =>
      rfl
  | cons bit rest ih =>
      show some bit :: (List.append rest right).map some = _
      rw [ih]
      rfl

theorem validatorHeaderCodeCells_cons
    (symbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    validatorHeaderCodeCells (symbol :: rest) =
      List.append (validatorHeaderSymbolCells symbol)
        (validatorHeaderCodeCells rest) := by
  unfold validatorHeaderCodeCells validatorHeaderSymbolCells
  change
    List.append
        ((List.append (encodeCodeSymbolAsInput symbol)
          (encodeCodeWordAsInput rest)).map some)
        [none] = _
  rw [validatorHeaderMapSomeAppendInv]
  exact List.append_assoc _ _ _

private def validatorHeaderEventuallyHalts
    (c : Configuration) : Prop :=
  exists steps : Nat, (VHP.runConfig steps c).state = VHP.halt

private theorem validatorHeaderEventuallyHalts_runConfig
    (c : Configuration) (skip : Nat)
    (h : validatorHeaderEventuallyHalts c) :
    validatorHeaderEventuallyHalts (VHP.runConfig skip c) := by
  rcases h with ⟨steps, hsteps⟩
  refine ⟨steps, ?_⟩
  have hstable :
      VHP.runConfig skip (VHP.runConfig steps c) =
        VHP.runConfig steps c := by
    cases hconfig : VHP.runConfig steps c with
    | mk state tape =>
        simp [hconfig] at hsteps
        subst state
        exact MachineDescription.runConfig_halt
          validatorHeaderParserDescription_haltTransitionFree tape skip
  calc
    (VHP.runConfig steps (VHP.runConfig skip c)).state =
        (VHP.runConfig (skip + steps) c).state :=
      congrArg Configuration.state
        (MachineDescription.runConfig_add VHP skip steps c).symm
    _ = (VHP.runConfig (steps + skip) c).state := by
      rw [Nat.add_comm skip steps]
    _ = (VHP.runConfig skip (VHP.runConfig steps c)).state :=
      congrArg Configuration.state
        (MachineDescription.runConfig_add VHP steps skip c)
    _ = (VHP.runConfig steps c).state := by rw [hstable]
    _ = VHP.halt := hsteps

private theorem validatorHeaderNotEventuallyHaltsOfRunConfigStuck
    {c : Configuration} (skip : Nat)
    (hstate : (VHP.runConfig skip c).state ≠ VHP.halt)
    (hstuck : VHP.stepConfig (VHP.runConfig skip c) = none) :
    ¬ validatorHeaderEventuallyHalts c := by
  intro h
  rcases validatorHeaderEventuallyHalts_runConfig c skip h with
    ⟨steps, hsteps⟩
  have hsame :=
    MachineDescription.runConfig_of_stepConfig_none hstuck steps
  rw [hsame] at hsteps
  exact hstate hsteps

private theorem validatorHeader_header_symbol_only
    (symbol : MachineCodeSymbol)
    (leftRev restCells : List (Option Bool))
    (h : validatorHeaderEventuallyHalts
      (config 0 leftRev
        (List.append (validatorHeaderSymbolCells symbol) restCells))) :
    symbol = MachineCodeSymbol.header := by
  cases symbol <;> try rfl
  all_goals
    exfalso
    apply (validatorHeaderNotEventuallyHaltsOfRunConfigStuck
      (skip := 4) ?_ ?_) h
  all_goals
    simp [ValidatorHeaderParserDescription, validatorHeaderSymbolCells,
      encodeCodeSymbolAsInput, config, tapeAtCells, keepMove,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem validatorHeader_field_symbol_only
    (state : Nat)
    (hstate : state = 4 ∨ state = 8 ∨ state = 12 ∨ state = 16)
    (symbol : MachineCodeSymbol)
    (leftRev restCells : List (Option Bool))
    (h : validatorHeaderEventuallyHalts
      (config state leftRev
        (List.append (validatorHeaderSymbolCells symbol) restCells))) :
    symbol = MachineCodeSymbol.tick ∨ symbol = MachineCodeSymbol.done := by
  rcases hstate with rfl | rfl | rfl | rfl <;>
    cases symbol <;>
      try { exact Or.inl rfl } <;>
      try { exact Or.inr rfl }
  all_goals
    exfalso
    apply (validatorHeaderNotEventuallyHaltsOfRunConfigStuck
      (skip := 4) ?_ ?_) h
  all_goals
    simp [ValidatorHeaderParserDescription, validatorHeaderSymbolCells,
      encodeCodeSymbolAsInput, config, tapeAtCells, keepMove,
      runConfig, stepConfig, lookupTransition, Matches, transition,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

private theorem validatorHeaderFieldEventuallyInv
    (state nextState : Nat)
    (hstateNeHalt : state ≠ VHP.halt)
    (hblank : forall leftRev : List (Option Bool),
      VHP.stepConfig (config state leftRev [none]) = none)
    (hsymbolOnly : forall
      (symbol : MachineCodeSymbol)
      (leftRev restCells : List (Option Bool)),
      validatorHeaderEventuallyHalts
          (config state leftRev
            (List.append (validatorHeaderSymbolCells symbol) restCells)) ->
        symbol = MachineCodeSymbol.tick ∨
          symbol = MachineCodeSymbol.done)
    (hrunTick : forall leftRev restCells : List (Option Bool),
      VHP.runConfig 4
          (config state leftRev
            (List.append
              (validatorHeaderSymbolCells MachineCodeSymbol.tick)
              restCells)) =
        config state
          (List.append
            ((validatorHeaderSymbolCells MachineCodeSymbol.tick).reverse)
            leftRev)
          restCells)
    (hrunDone : forall leftRev restCells : List (Option Bool),
      VHP.runConfig 4
          (config state leftRev
            (List.append
              (validatorHeaderSymbolCells MachineCodeSymbol.done)
              restCells)) =
        config nextState
          (List.append
            ((validatorHeaderSymbolCells MachineCodeSymbol.done).reverse)
            leftRev)
          restCells)
    (code : Word MachineCodeSymbol)
    (leftRev : List (Option Bool))
    (h : validatorHeaderEventuallyHalts
      (config state leftRev (validatorHeaderCodeCells code))) :
    exists n : Nat,
    exists suffix : Word MachineCodeSymbol,
    exists nextLeftRev : List (Option Bool),
      code = encodeNatAppend n suffix ∧
        validatorHeaderEventuallyHalts
          (config nextState nextLeftRev
            (validatorHeaderCodeCells suffix)) := by
  induction code generalizing leftRev with
  | nil =>
      exfalso
      apply (validatorHeaderNotEventuallyHaltsOfRunConfigStuck
        (skip := 0) ?_ ?_) h
      · simpa [runConfig, config] using hstateNeHalt
      · change VHP.stepConfig
          (config state leftRev (validatorHeaderCodeCells [])) = none
        rw [validatorHeaderCodeCells_nil]
        exact hblank leftRev
  | cons symbol rest ih =>
      rw [validatorHeaderCodeCells_cons] at h
      rcases hsymbolOnly symbol leftRev
          (validatorHeaderCodeCells rest) h with
        htick | hdone
      · subst symbol
        have htail := validatorHeaderEventuallyHalts_runConfig
          (config state leftRev
            (List.append
              (validatorHeaderSymbolCells MachineCodeSymbol.tick)
              (validatorHeaderCodeCells rest))) 4 h
        rw [hrunTick] at htail
        rcases ih _ htail with
          ⟨n, suffix, nextLeftRev, hrest, hnext⟩
        refine ⟨n + 1, suffix, nextLeftRev, ?_, hnext⟩
        simp [encodeNatAppend, encodeNat, hrest]
      · subst symbol
        have htail := validatorHeaderEventuallyHalts_runConfig
          (config state leftRev
            (List.append
              (validatorHeaderSymbolCells MachineCodeSymbol.done)
              (validatorHeaderCodeCells rest))) 4 h
        rw [hrunDone] at htail
        exact
          ⟨0, rest,
            List.append
              ((validatorHeaderSymbolCells MachineCodeSymbol.done).reverse)
              leftRev,
            rfl, htail⟩

/-- At any unary-field entry, a blank head is a concrete missing parser row. -/
theorem validatorHeader_blank_stuck
    (state : Nat)
    (hstate :
      state = 0 ∨ state = 4 ∨ state = 8 ∨ state = 12 ∨ state = 16)
    (leftRev : List (Option Bool)) :
    VHP.stepConfig (config state leftRev [none]) = none := by
  rcases hstate with rfl | rfl | rfl | rfl | rfl <;>
    simp [ValidatorHeaderParserDescription, config, tapeAtCells,
      stepConfig, lookupTransition, Matches, transition, keepMove, Tape.read]


/-!
## Canonical-code inversion
-/

/--
If the physical parser halts on any canonical code-word encoding, that code has
exactly the header and four unary fields required by leaf 2.  The remaining
suffix begins at the transition-record boundary and is intentionally arbitrary.
-/
theorem validatorHeaderParserDescription_haltsFromCode_inv
    (code : Word MachineCodeSymbol) (T : Tape Bool)
    (h : VHP.HaltsFromTape
      (validatorHeaderCodePaddedStartTape code) T) :
    exists stateCount start halt transitionCount : Nat,
    exists suffix : Word MachineCodeSymbol,
      code =
        validatorHeaderFieldsCode stateCount start halt transitionCount
          suffix := by
  rcases h with ⟨steps, hstate, _htape⟩
  have hevent : validatorHeaderEventuallyHalts
      (config 0 [none] (validatorHeaderCodeCells code)) :=
    ⟨steps, hstate⟩
  cases code with
  | nil =>
      exfalso
      apply (validatorHeaderNotEventuallyHaltsOfRunConfigStuck
        (skip := 0) ?_ ?_) hevent
      · simp [runConfig, config, ValidatorHeaderParserDescription]
      · change VHP.stepConfig
          (config 0 [none] (validatorHeaderCodeCells [])) = none
        rw [validatorHeaderCodeCells_nil]
        exact validatorHeader_blank_stuck 0 (Or.inl rfl) [none]
  | cons symbol rest =>
      rw [validatorHeaderCodeCells_cons] at hevent
      have hheader := validatorHeader_header_symbol_only symbol [none]
        (validatorHeaderCodeCells rest) hevent
      subst symbol
      have hstateCount := validatorHeaderEventuallyHalts_runConfig
        (config 0 [none]
          (List.append
            (validatorHeaderSymbolCells MachineCodeSymbol.header)
            (validatorHeaderCodeCells rest))) 4 hevent
      rw [run_validatorHeader_header] at hstateCount
      rcases validatorHeaderFieldEventuallyInv 4 8 (by decide)
          (validatorHeader_blank_stuck 4 (Or.inr (Or.inl rfl)))
          (validatorHeader_field_symbol_only 4 (Or.inl rfl))
          run_validatorHeader_stateCount_tick
          run_validatorHeader_stateCount_done rest _ hstateCount with
        ⟨stateCount, afterStateCount, leftAfterStateCount,
          hStateCount, hstartEvent⟩
      rcases validatorHeaderFieldEventuallyInv 8 12 (by decide)
          (validatorHeader_blank_stuck 8 (Or.inr (Or.inr (Or.inl rfl))))
          (validatorHeader_field_symbol_only 8 (Or.inr (Or.inl rfl)))
          run_validatorHeader_start_tick
          run_validatorHeader_start_done afterStateCount _ hstartEvent with
        ⟨start, afterStart, leftAfterStart, hStart, hhaltEvent⟩
      rcases validatorHeaderFieldEventuallyInv 12 16 (by decide)
          (validatorHeader_blank_stuck 12
            (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
          (validatorHeader_field_symbol_only 12
            (Or.inr (Or.inr (Or.inl rfl))))
          run_validatorHeader_halt_tick
          run_validatorHeader_halt_done afterStart _ hhaltEvent with
        ⟨halt, afterHalt, leftAfterHalt, hHalt, hcountEvent⟩
      rcases validatorHeaderFieldEventuallyInv 16 20 (by decide)
          (validatorHeader_blank_stuck 16
            (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
          (validatorHeader_field_symbol_only 16
            (Or.inr (Or.inr (Or.inr rfl))))
          run_validatorHeader_transitionCount_tick
          run_validatorHeader_transitionCount_done afterHalt _ hcountEvent with
        ⟨transitionCount, suffix, _leftAfterCount, hCount, _hfinal⟩
      refine ⟨stateCount, start, halt, transitionCount, suffix, ?_⟩
      simp [validatorHeaderFieldsCode, hStateCount, hStart, hHalt, hCount]

theorem validatorHeaderCodePaddedStartTape_fields
    (stateCount start halt transitionCount : Nat)
    (suffix : Word MachineCodeSymbol) :
    validatorHeaderCodePaddedStartTape
        (validatorHeaderFieldsCode stateCount start halt transitionCount
          suffix) =
      validatorHeaderFieldsPaddedStartTape
        stateCount start halt transitionCount suffix := by
  rfl

/--
Exact canonical-input characterization of leaf 2: halting is equivalent to a
header plus four unary fields, and the final physical tape is the unique
transition-region handoff tape.
-/
theorem validatorHeaderParserDescription_haltsFromCode_iff
    (code : Word MachineCodeSymbol) (T : Tape Bool) :
    VHP.HaltsFromTape (validatorHeaderCodePaddedStartTape code) T <->
      exists stateCount start halt transitionCount : Nat,
      exists suffix : Word MachineCodeSymbol,
        code =
            validatorHeaderFieldsCode stateCount start halt transitionCount
              suffix ∧
          T =
            validatorHeaderFieldsHandoffTape
              stateCount start halt transitionCount suffix := by
  constructor
  · intro h
    rcases validatorHeaderParserDescription_haltsFromCode_inv code T h with
      ⟨stateCount, start, halt, transitionCount, suffix, hcode⟩
    have hcanonical : VHP.HaltsFromTape
        (validatorHeaderCodePaddedStartTape code)
        (validatorHeaderFieldsHandoffTape
          stateCount start halt transitionCount suffix) := by
      rw [hcode, validatorHeaderCodePaddedStartTape_fields]
      exact validatorHeaderParserDescription_haltsFromTape
        stateCount start halt transitionCount suffix
    have hT :=
      MachineDescription.haltsFromTape_functional_of_haltTransitionFree
        validatorHeaderParserDescription_haltTransitionFree h hcanonical
    exact
      ⟨stateCount, start, halt, transitionCount, suffix, hcode, hT⟩
  · rintro
      ⟨stateCount, start, halt, transitionCount, suffix, hcode, rfl⟩
    rw [hcode, validatorHeaderCodePaddedStartTape_fields]
    exact validatorHeaderParserDescription_haltsFromTape
      stateCount start halt transitionCount suffix

end SelfHaltingRecognizer
end Computability
end FoC
