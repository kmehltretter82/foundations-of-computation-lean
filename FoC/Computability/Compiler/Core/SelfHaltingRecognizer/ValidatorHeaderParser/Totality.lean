import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorHeaderParser.Inversion
import FoC.Computability.Compiler.StuckExecution

set_option doc.verso true

/-!
# Exact-code validator header-parser totality

Every canonical code word either supplies the header and four unary fields or
reaches a concrete missing parser row.  This is the rejection evidence needed
by the validator's structural Boolean closeout.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer

open Languages
open MachineDescription

open DovetailInitialLayoutInitializer
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

private abbrev VHP := ValidatorHeaderParserDescription

private theorem validatorHeaderParserDescription_row_scansRight
    {row : TransitionDescription} (hrow : row ∈ VHP.transitions) :
    exists bit : Bool,
      row.read = some bit ∧ row.write = some bit ∧
        row.move = Direction.right := by
  have hall : VHP.transitions.all (fun candidate =>
      match candidate.read, candidate.write, candidate.move with
      | some read, some write, Direction.right => read == write
      | _, _, _ => false) = true := by
    decide
  have hgood := List.all_eq_true.mp hall row hrow
  cases row with
  | mk source read write move target =>
      cases read <;> cases write <;> cases move <;>
        simp_all

/-- Every fuel-bounded header-parser run preserves the contiguous encoded
window shape needed by the validator's Boolean closeout. -/
theorem validatorHeaderParserDescription_runConfig_contiguous
    (steps state : Nat) (leftRev right : Word Bool) (padding : Nat) :
    ContiguousTape
      ((VHP.runConfig steps
        { state := state, tape := splitTape leftRev right padding }).tape) := by
  induction steps generalizing state leftRev right padding with
  | zero =>
      exact contiguousTape_splitTape leftRev right padding
  | succ steps ih =>
      cases hlookup : VHP.lookupTransition state
          (Tape.read (splitTape leftRev right padding)) with
      | none =>
          simpa [MachineDescription.runConfig,
            MachineDescription.stepConfig, hlookup] using
              contiguousTape_splitTape leftRev right padding
      | some row =>
          have hrow := MachineDescription.lookupTransition_mem hlookup
          have hmatches := MachineDescription.lookupTransition_matches hlookup
          rcases validatorHeaderParserDescription_row_scansRight hrow with
            ⟨bit, hread, hwrite, hmove⟩
          cases right with
          | nil =>
              have htapeRead :
                  Tape.read (splitTape leftRev [] padding) = none := rfl
              rw [htapeRead] at hmatches
              simp [hread] at hmatches
          | cons head tail =>
              have htapeRead :
                  Tape.read (splitTape leftRev (head :: tail) padding) =
                    some head := rfl
              rw [htapeRead, hread] at hmatches
              have hbit : bit = head := Option.some.inj hmatches.2
              subst bit
              have hnextTape :
                  Tape.move Direction.right
                      (Tape.write (some head)
                        (splitTape leftRev (head :: tail) padding)) =
                    splitTape (head :: leftRev) tail padding := by
                cases tail <;> cases padding <;>
                  rfl
              simpa [MachineDescription.runConfig,
                MachineDescription.stepConfig, hlookup, hwrite, hmove,
                hnextTape] using
                  ih row.target (head :: leftRev) tail padding

private theorem exists_reachesStuck_of_runConfig
    {source : Configuration} (steps : Nat)
    (hstep : VHP.stepConfig (VHP.runConfig steps source) = none)
    (hstate : (VHP.runConfig steps source).state ≠ VHP.halt) :
    exists stuck : Tape Bool, VHP.ReachesStuck source stuck := by
  refine ⟨(VHP.runConfig steps source).tape, steps,
    (VHP.runConfig steps source).state, ?_, hstep, hstate⟩
  cases VHP.runConfig steps source
  rfl

private theorem invalidFieldSymbol_reachesStuck
    (state : Nat)
    (hstate : state = 4 ∨ state = 8 ∨ state = 12 ∨ state = 16)
    (leftRev : List (Option Bool))
    (symbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (hnotTick : symbol ≠ .tick) (hnotDone : symbol ≠ .done) :
    exists stuck : Tape Bool,
      VHP.ReachesStuck
        (config state leftRev (validatorHeaderCodeCells (symbol :: rest)))
        stuck := by
  apply exists_reachesStuck_of_runConfig 4
  · rcases hstate with rfl | rfl | rfl | rfl <;>
      cases symbol <;>
      simp_all [validatorHeaderCodeCells_cons, validatorHeaderSymbolCells,
        encodeCodeSymbolAsInput, VHP, ValidatorHeaderParserDescription,
        runConfig, stepConfig, lookupTransition, Matches, keepMove,
        transition, config, tapeAtCells, Tape.read, Tape.write, Tape.move,
        Tape.moveRight]
  · rcases hstate with rfl | rfl | rfl | rfl <;>
      cases symbol <;>
      simp_all [validatorHeaderCodeCells_cons, validatorHeaderSymbolCells,
        encodeCodeSymbolAsInput, VHP, ValidatorHeaderParserDescription,
        runConfig, stepConfig, lookupTransition, Matches, keepMove,
        transition, config, tapeAtCells, Tape.read, Tape.write, Tape.move,
        Tape.moveRight]

private theorem invalidHeaderSymbol_reachesStuck
    (leftRev : List (Option Bool))
    (symbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (hnotHeader : symbol ≠ .header) :
    exists stuck : Tape Bool,
      VHP.ReachesStuck
        (config 0 leftRev (validatorHeaderCodeCells (symbol :: rest)))
        stuck := by
  apply exists_reachesStuck_of_runConfig 4
  · cases symbol <;>
      simp_all [validatorHeaderCodeCells_cons, validatorHeaderSymbolCells,
        encodeCodeSymbolAsInput, VHP, ValidatorHeaderParserDescription,
        runConfig, stepConfig, lookupTransition, Matches, keepMove,
        transition, config, tapeAtCells, Tape.read, Tape.write, Tape.move,
        Tape.moveRight]
  · cases symbol <;>
      simp_all [validatorHeaderCodeCells_cons, validatorHeaderSymbolCells,
        encodeCodeSymbolAsInput, VHP, ValidatorHeaderParserDescription,
        runConfig, stepConfig, lookupTransition, Matches, keepMove,
        transition, config, tapeAtCells, Tape.read, Tape.write, Tape.move,
        Tape.moveRight]

private theorem field_reachesStuck_of_decodeNat_none
    (state : Nat)
    (hstate : state = 4 ∨ state = 8 ∨ state = 12 ∨ state = 16)
    (runTick : forall leftRev restCells,
      VHP.runConfig 4
          (config state leftRev
            (List.append
              (validatorHeaderSymbolCells MachineCodeSymbol.tick)
              restCells)) =
        config state
          (List.append
            (validatorHeaderSymbolCells MachineCodeSymbol.tick).reverse
            leftRev)
          restCells)
    (tokens : Word MachineCodeSymbol) (leftRev : List (Option Bool))
    (hdecode : decodeNat tokens = none) :
    exists stuck : Tape Bool,
      VHP.ReachesStuck
        (config state leftRev (validatorHeaderCodeCells tokens)) stuck := by
  induction tokens generalizing leftRev with
  | nil =>
      apply exists_reachesStuck_of_runConfig 0
      · simpa [VHP, ValidatorHeaderParserDescription, runConfig] using
          validatorHeader_blank_stuck state (Or.inr hstate) leftRev
      · rcases hstate with rfl | rfl | rfl | rfl <;>
          simp [VHP, ValidatorHeaderParserDescription, runConfig, config]
  | cons symbol rest ih =>
      cases symbol with
      | tick =>
          cases hrest : decodeNat rest with
          | none =>
              let nextLeft := List.append
                (validatorHeaderSymbolCells MachineCodeSymbol.tick).reverse
                leftRev
              have htail := ih nextLeft hrest
              rcases htail with ⟨tailStuck, htailStuck⟩
              have hprefix : VHP.runConfig 4
                  (config state leftRev
                    (validatorHeaderCodeCells (.tick :: rest))) =
                  config state nextLeft (validatorHeaderCodeCells rest) := by
                rw [validatorHeaderCodeCells_cons]
                exact runTick leftRev (validatorHeaderCodeCells rest)
              exact ⟨tailStuck,
                MachineDescription.ReachesStuck.prepend hprefix htailStuck⟩
          | some parsed =>
              simp [decodeNat, hrest] at hdecode
      | done => simp [decodeNat] at hdecode
      | header =>
          exact invalidFieldSymbol_reachesStuck state hstate leftRev
            .header rest (by decide) (by decide)
      | transition =>
          exact invalidFieldSymbol_reachesStuck state hstate leftRev
            .transition rest (by decide) (by decide)
      | blank =>
          exact invalidFieldSymbol_reachesStuck state hstate leftRev
            .blank rest (by decide) (by decide)
      | zero =>
          exact invalidFieldSymbol_reachesStuck state hstate leftRev
            .zero rest (by decide) (by decide)
      | one =>
          exact invalidFieldSymbol_reachesStuck state hstate leftRev
            .one rest (by decide) (by decide)
      | moveLeft =>
          exact invalidFieldSymbol_reachesStuck state hstate leftRev
            .moveLeft rest (by decide) (by decide)
      | moveRight =>
          exact invalidFieldSymbol_reachesStuck state hstate leftRev
            .moveRight rest (by decide) (by decide)

private theorem validatorHeaderCodeCells_encodeNatAppend
    (n : Nat) (suffix : Word MachineCodeSymbol) :
    validatorHeaderCodeCells (encodeNatAppend n suffix) =
      List.append (validatorHeaderNatCells n)
        (validatorHeaderCodeCells suffix) := by
  unfold validatorHeaderCodeCells validatorHeaderNatCells encodeNatAppend
  rw [encodeCodeWordAsInput_append, validatorHeaderMapSomeAppend]
  simp [List.append_assoc]

private theorem header_nil_reachesStuck :
    exists stuck : Tape Bool,
      VHP.ReachesStuck (config 0 [none] (validatorHeaderCodeCells [])) stuck := by
  apply exists_reachesStuck_of_runConfig 0
  · simpa [runConfig, validatorHeaderCodeCells_nil] using
      validatorHeader_blank_stuck 0 (Or.inl rfl) [none]
  · simp [VHP, ValidatorHeaderParserDescription, runConfig, config]

/-- Every canonical code word either reaches the unique fixed-field handoff or
reaches a concrete missing parser transition. -/
theorem validatorHeaderParserDescription_haltsOrStuckFromCode
    (code : Word MachineCodeSymbol) :
    (exists output : Tape Bool,
      VHP.HaltsFromTape (validatorHeaderCodePaddedStartTape code) output) ∨
    (exists stuck : Tape Bool,
      VHP.StuckFromTape (validatorHeaderCodePaddedStartTape code) stuck) := by
  cases code with
  | nil =>
      exact Or.inr (by
        simpa [MachineDescription.StuckFromTape,
          validatorHeaderCodePaddedStartTape, VHP,
          ValidatorHeaderParserDescription, config] using
            header_nil_reachesStuck)
  | cons symbol rest =>
      by_cases hheader : symbol = .header
      · subst symbol
        cases hstateCount : decodeNat rest with
        | none =>
            let leftHeader := List.append
              (validatorHeaderSymbolCells MachineCodeSymbol.header).reverse
              [none]
            rcases field_reachesStuck_of_decodeNat_none 4 (Or.inl rfl)
                run_validatorHeader_stateCount_tick rest leftHeader
                hstateCount with ⟨stuck, hstuck⟩
            have hprefix : VHP.runConfig 4
                { state := VHP.start
                  tape := validatorHeaderCodePaddedStartTape (.header :: rest) } =
                config 4 leftHeader (validatorHeaderCodeCells rest) := by
              change VHP.runConfig 4
                (config 0 [none]
                  (validatorHeaderCodeCells (.header :: rest))) = _
              rw [validatorHeaderCodeCells_cons]
              exact run_validatorHeader_header [none]
                (validatorHeaderCodeCells rest)
            exact Or.inr ⟨stuck,
              MachineDescription.ReachesStuck.prepend hprefix hstuck⟩
        | some parsedStateCount =>
            rcases parsedStateCount with ⟨stateCount, afterStateCount⟩
            have hstateCountCode :=
              decodeNat_eq_some_encodeNatAppend hstateCount
            cases hstart : decodeNat afterStateCount with
            | none =>
                let leftHeader := List.append
                  (validatorHeaderSymbolCells MachineCodeSymbol.header).reverse
                  [none]
                let leftStateCount := List.append
                  (validatorHeaderNatCells stateCount).reverse leftHeader
                rcases field_reachesStuck_of_decodeNat_none 8
                    (Or.inr (Or.inl rfl)) run_validatorHeader_start_tick
                    afterStateCount leftStateCount hstart with
                  ⟨stuck, hstuck⟩
                have hprefix : VHP.runConfig
                    (4 + validatorHeaderFieldFuel stateCount)
                    { state := VHP.start
                      tape := validatorHeaderCodePaddedStartTape
                        (.header :: rest) } =
                    config 8 leftStateCount
                      (validatorHeaderCodeCells afterStateCount) := by
                  change VHP.runConfig _
                    (config 0 [none]
                      (validatorHeaderCodeCells (.header :: rest))) = _
                  rw [runConfig_add, validatorHeaderCodeCells_cons,
                    run_validatorHeader_header, hstateCountCode,
                    validatorHeaderCodeCells_encodeNatAppend,
                    run_validatorHeader_stateCount_nat]
                exact Or.inr ⟨stuck,
                  MachineDescription.ReachesStuck.prepend hprefix hstuck⟩
            | some parsedStart =>
                rcases parsedStart with ⟨start, afterStart⟩
                have hstartCode := decodeNat_eq_some_encodeNatAppend hstart
                cases hhalt : decodeNat afterStart with
                | none =>
                    let leftHeader := List.append
                      (validatorHeaderSymbolCells MachineCodeSymbol.header).reverse
                      [none]
                    let leftStateCount := List.append
                      (validatorHeaderNatCells stateCount).reverse leftHeader
                    let leftStart := List.append
                      (validatorHeaderNatCells start).reverse leftStateCount
                    rcases field_reachesStuck_of_decodeNat_none 12
                        (Or.inr (Or.inr (Or.inl rfl)))
                        run_validatorHeader_halt_tick afterStart leftStart hhalt
                        with ⟨stuck, hstuck⟩
                    have hprefix : VHP.runConfig
                        (4 + validatorHeaderFieldFuel stateCount +
                          validatorHeaderFieldFuel start)
                        { state := VHP.start
                          tape := validatorHeaderCodePaddedStartTape
                            (.header :: rest) } =
                        config 12 leftStart
                          (validatorHeaderCodeCells afterStart) := by
                      change VHP.runConfig _
                        (config 0 [none]
                          (validatorHeaderCodeCells (.header :: rest))) = _
                      rw [show 4 + validatorHeaderFieldFuel stateCount +
                            validatorHeaderFieldFuel start =
                          4 + (validatorHeaderFieldFuel stateCount +
                            validatorHeaderFieldFuel start) by lia,
                        runConfig_add, validatorHeaderCodeCells_cons,
                        run_validatorHeader_header, runConfig_add,
                        hstateCountCode,
                        validatorHeaderCodeCells_encodeNatAppend,
                        run_validatorHeader_stateCount_nat, hstartCode,
                        validatorHeaderCodeCells_encodeNatAppend,
                        run_validatorHeader_start_nat]
                    exact Or.inr ⟨stuck,
                      MachineDescription.ReachesStuck.prepend hprefix hstuck⟩
                | some parsedHalt =>
                    rcases parsedHalt with ⟨halt, afterHalt⟩
                    have hhaltCode := decodeNat_eq_some_encodeNatAppend hhalt
                    cases hcount : decodeNat afterHalt with
                    | none =>
                        let leftHeader := List.append
                          (validatorHeaderSymbolCells MachineCodeSymbol.header).reverse
                          [none]
                        let leftStateCount := List.append
                          (validatorHeaderNatCells stateCount).reverse leftHeader
                        let leftStart := List.append
                          (validatorHeaderNatCells start).reverse leftStateCount
                        let leftHalt := List.append
                          (validatorHeaderNatCells halt).reverse leftStart
                        rcases field_reachesStuck_of_decodeNat_none 16
                            (Or.inr (Or.inr (Or.inr rfl)))
                            run_validatorHeader_transitionCount_tick
                            afterHalt leftHalt hcount with ⟨stuck, hstuck⟩
                        have hprefix : VHP.runConfig
                            (4 + validatorHeaderFieldFuel stateCount +
                              validatorHeaderFieldFuel start +
                              validatorHeaderFieldFuel halt)
                            { state := VHP.start
                              tape := validatorHeaderCodePaddedStartTape
                                (.header :: rest) } =
                            config 16 leftHalt
                              (validatorHeaderCodeCells afterHalt) := by
                          change VHP.runConfig _
                            (config 0 [none]
                              (validatorHeaderCodeCells (.header :: rest))) = _
                          rw [show 4 + validatorHeaderFieldFuel stateCount +
                                validatorHeaderFieldFuel start +
                                validatorHeaderFieldFuel halt =
                              4 + (validatorHeaderFieldFuel stateCount +
                                (validatorHeaderFieldFuel start +
                                  validatorHeaderFieldFuel halt)) by lia,
                            runConfig_add, validatorHeaderCodeCells_cons,
                            run_validatorHeader_header, runConfig_add,
                            hstateCountCode,
                            validatorHeaderCodeCells_encodeNatAppend,
                            run_validatorHeader_stateCount_nat, runConfig_add,
                            hstartCode,
                            validatorHeaderCodeCells_encodeNatAppend,
                            run_validatorHeader_start_nat, hhaltCode,
                            validatorHeaderCodeCells_encodeNatAppend,
                            run_validatorHeader_halt_nat]
                        exact Or.inr ⟨stuck,
                          MachineDescription.ReachesStuck.prepend hprefix hstuck⟩
                    | some parsedCount =>
                        rcases parsedCount with ⟨transitionCount, suffix⟩
                        have hcountCode :=
                          decodeNat_eq_some_encodeNatAppend hcount
                        have hcode : .header :: rest =
                            validatorHeaderFieldsCode stateCount start halt
                              transitionCount suffix := by
                          simp [validatorHeaderFieldsCode, hstateCountCode,
                            hstartCode, hhaltCode, hcountCode]
                        exact Or.inl ⟨_, by
                          rw [hcode, validatorHeaderCodePaddedStartTape_fields]
                          exact validatorHeaderParserDescription_haltsFromTape
                            stateCount start halt transitionCount suffix⟩
      · exact Or.inr (by
          rcases invalidHeaderSymbol_reachesStuck [none] symbol rest hheader
              with ⟨stuck, hstuck⟩
          exact ⟨stuck, by
            simpa [MachineDescription.StuckFromTape,
              validatorHeaderCodePaddedStartTape, VHP,
              ValidatorHeaderParserDescription, config] using hstuck⟩)

/-- Every concrete parser rejection on a canonical code word remains within
the original contiguous encoded window. -/
theorem validatorHeaderParserDescription_contiguous_of_stuckFromCode
    (code : Word MachineCodeSymbol) (stuck : Tape Bool)
    (hstuck : VHP.StuckFromTape
      (validatorHeaderCodePaddedStartTape code) stuck) :
    ContiguousTape stuck := by
  have hsource :
      validatorHeaderCodePaddedStartTape code =
        splitTape [] (encodeCodeWordAsInput code) 0 := by
    unfold validatorHeaderCodePaddedStartTape validatorHeaderCodeCells
    cases encodeCodeWordAsInput code <;>
      rfl
  rcases hstuck with ⟨steps, state, hrun, _hstep, _hstate⟩
  have hshape := validatorHeaderParserDescription_runConfig_contiguous
    steps VHP.start [] (encodeCodeWordAsInput code) 0
  rw [← hsource, hrun] at hshape
  exact hshape

end SelfHaltingRecognizer
end Computability
end FoC
