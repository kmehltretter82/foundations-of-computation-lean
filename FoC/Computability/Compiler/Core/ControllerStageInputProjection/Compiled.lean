import FoC.Computability.Compiler.Core.ControllerStageInputProjection.Soundness

set_option doc.verso true

/-!
# Compiled

Supporting declarations and helper lemmas for Computability Compiler Core ControllerStageInputProjection Compiled.
-/


namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace ControllerStageInputProjection

 /-- {name}`run_result_marked_suffix_to_state350` states the corresponding theorem run form. -/
theorem run_result_marked_suffix_to_state350
    (marked : Word Bool) (symbol : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol)
    (baseLeftRev : List (Option Bool)) :
    Description.runConfig
        (8 * marked.length + 4)
        (projectionConfig 300
          (List.append [none, none, none, none] baseLeftRev)
          (projectionBoolWordWorkCells marked [] (symbol :: suffix))) =
      projectionConfig 350
        (List.append (projectionMarkedBoolPayloadCells marked).reverse
          (List.append projectionDoneCodeCells.reverse
            (List.append
              (projectionRepeatedCells projectionMarkedTickCodeCells
                marked.length).reverse
              (List.append [none, none, none, none] baseLeftRev))))
        (projectionCodeCells (symbol :: suffix)) := by
  have hsteps :
      8 * marked.length + 4 =
        4 * marked.length + (4 + 4 * marked.length) := by
    omega
  rw [hsteps, runConfig_add]
  simp only [projectionBoolWordWorkCells]
  rw [run_state300_marked_ticks]
  simp [List.length_nil, projectionBoolPayloadCells]
  rw [runConfig_add]
  change
    Description.runConfig
        (4 * marked.length)
        (Description.runConfig 4
          (projectionConfig 300
            (List.append
              (projectionRepeatedCells projectionMarkedTickCodeCells
                marked.length).reverse
              (List.append [none, none, none, none] baseLeftRev))
            (List.append projectionDoneCodeCells
              (List.append (projectionMarkedBoolPayloadCells marked)
                (projectionCodeCells (symbol :: suffix)))))) = _
  rw [run_state300_done]
  rw [run_state350_marked_payload]
  simp

def projectionResultSuffixRejectCost
    (marked rest : Word Bool) : Nat :=
  12 * rest.length * rest.length +
    16 * marked.length * rest.length +
    26 * rest.length + 8 * marked.length + 4

 /-- {name}`run_result_suffix_to_state350_acc` states the corresponding theorem run form. -/
theorem run_result_suffix_to_state350_acc
    (marked rest : Word Bool) (symbol : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol)
    (baseLeftRev : List (Option Bool)) :
    Description.runConfig
        (projectionResultSuffixRejectCost marked rest)
        (projectionConfig 300
          (List.append [none, none, none, none] baseLeftRev)
          (projectionBoolWordWorkCells marked rest (symbol :: suffix))) =
      projectionConfig 350
        (List.append
          (projectionMarkedBoolPayloadCells
            (List.append marked rest)).reverse
          (List.append projectionDoneCodeCells.reverse
            (List.append
              (projectionRepeatedCells projectionMarkedTickCodeCells
                (List.append marked rest).length).reverse
              (List.append [none, none, none, none] baseLeftRev))))
        (projectionCodeCells (symbol :: suffix)) := by
  induction rest generalizing marked baseLeftRev with
  | nil =>
      simp [projectionResultSuffixRejectCost]
      exact
        run_result_marked_suffix_to_state350
          marked symbol suffix baseLeftRev
  | cons b rest ih =>
      have hcost :
          projectionResultSuffixRejectCost marked (b :: rest) =
            projectionInputMarkStepCost marked rest +
              projectionResultSuffixRejectCost (List.append marked [b])
                rest := by
        simp [projectionResultSuffixRejectCost, projectionInputMarkStepCost,
          Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
        omega
      rw [hcost, runConfig_add]
      rw [run_result_mark_one]
      rw [ih]
      have hword :
          List.append (List.append marked [b]) rest =
            List.append marked (b :: rest) := by
        simp [List.append_assoc]
      rw [hword]

 /-- {name}`run_result_suffix_ne_halt` states the corresponding theorem run form. -/
theorem run_result_suffix_ne_halt
    (w : Word Bool) (symbol : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol)
    (baseLeftRev : List (Option Bool)) (n : Nat) :
    (Description.runConfig n
      (projectionConfig 300
        (List.append [none, none, none, none] baseLeftRev)
        (projectionCodeCells
          (encodeBoolWordAppend w
            (symbol :: suffix))))).state ≠
      Description.halt := by
  apply
    ne_halt_of_reaches_ne_halt_region
      (k := projectionResultSuffixRejectCost ([] : Word Bool) w)
      (mid :=
        projectionConfig 350
          (List.append (projectionMarkedBoolPayloadCells w).reverse
            (List.append projectionDoneCodeCells.reverse
              (List.append
                (projectionRepeatedCells projectionMarkedTickCodeCells
                  w.length).reverse
                (List.append [none, none, none, none] baseLeftRev))))
          (projectionCodeCells (symbol :: suffix)))
  · have h :=
      run_result_suffix_to_state350_acc
        ([] : Word Bool) w symbol suffix baseLeftRev
    simpa [projectionResultSuffixRejectCost,
      projectionBoolWordWorkCells_nil_eq_encodeBoolWordAppend] using h
  · intro m
    exact
      run_state350_code_symbol_ne_halt
        symbol suffix
        (List.append (projectionMarkedBoolPayloadCells w).reverse
          (List.append projectionDoneCodeCells.reverse
            (List.append
              (projectionRepeatedCells projectionMarkedTickCodeCells
                w.length).reverse
              (List.append [none, none, none, none] baseLeftRev))))
        m

 /-- {name}`encodeAppend_nonempty_suffix_ne_halt` establishes the halting condition in this construction. -/
theorem encodeAppend_nonempty_suffix_ne_halt
    (C : DovetailControllerLayout)
    (symbol : MachineCodeSymbol) (suffix : Word MachineCodeSymbol)
    (n : Nat) :
    (Description.runConfig n
      (Description.initial
        (encodeCodeWordAsInput
          (DovetailControllerLayout.encodeAppend C
            (symbol :: suffix))))).state ≠
      Description.halt := by
  rcases C with ⟨input, stage, result⟩
  let inputLeftRev :=
    List.append
      (projectionCodeCells (encodeBoolWord input)).reverse
      ([none, none, none, none] : List (Option Bool))
  let stageLeftRev :=
    List.append [none, none, none, none]
      (List.append (projectionStageTickCellsRev stage) inputLeftRev)
  apply
    ne_halt_of_reaches_ne_halt_region
      (k := 4 + projectionInputBoolWordCost input + (4 * stage + 12))
      (mid :=
        projectionConfig 300 stageLeftRev
          (projectionCodeCells
            (encodeBoolWordAppend result
              (symbol :: suffix))))
  · rw [show
        4 + projectionInputBoolWordCost input + (4 * stage + 12) =
          4 + (projectionInputBoolWordCost input + (4 * stage + 12)) by
        omega]
    rw [runConfig_add]
    change
      Description.runConfig
        (projectionInputBoolWordCost input + (4 * stage + 12))
        (Description.runConfig 4
          (Description.initial
            (encodeCodeWordAsInput
              (DovetailControllerLayout.encodeAppend
                { input := input, stage := stage, result := result }
                (symbol :: suffix))))) =
        projectionConfig 300 stageLeftRev
          (projectionCodeCells
            (encodeBoolWordAppend result
              (symbol :: suffix)))
    simp [DovetailControllerLayout.encodeAppend,
      encodeCodeWordAsInput,
      encodeCodeSymbolAsInput]
    change
      Description.runConfig
        (projectionInputBoolWordCost input + (4 * stage + 12))
        (Description.runConfig 4
          (Description.initial
            (List.append [false, false, false, false]
              (encodeCodeWordAsInput
                (DovetailLayout.stageInputCodeAppend input
                  stage
                  (encodeBoolWordAppend result
                    (symbol :: suffix))))))) =
        projectionConfig 300 stageLeftRev
          (projectionCodeCells
            (encodeBoolWordAppend result
              (symbol :: suffix)))
    rw [run_header]
    change
      Description.runConfig
        (projectionInputBoolWordCost input + (4 * stage + 12))
        (projectionConfig 100 [none, none, none, none]
          (projectionCodeCells
            (DovetailLayout.stageInputCodeAppend input stage
              (encodeBoolWordAppend result
                (symbol :: suffix))))) =
        projectionConfig 300 stageLeftRev
          (projectionCodeCells
            (encodeBoolWordAppend result
              (symbol :: suffix)))
    simp [DovetailLayout.stageInputCodeAppend]
    rw [runConfig_add]
    change
      Description.runConfig
        (4 * stage + 12)
        (Description.runConfig
          (projectionInputBoolWordCost input)
          (projectionConfig 100
            (List.append [none, none, none, none]
              ([] : List (Option Bool)))
            (projectionCodeCells
              (encodeBoolWordAppend input
                (encodeNatAppend stage
                  (encodeBoolWordAppend result
                    (symbol :: suffix))))))) =
        projectionConfig 300 stageLeftRev
          (projectionCodeCells
            (encodeBoolWordAppend result
              (symbol :: suffix)))
    rw [run_input_bool_word_suffix
      (stage := stage)
      (suffix := encodeBoolWordAppend result
        (symbol :: suffix))
      (baseLeftRev := [])]
    change
      Description.runConfig
        (4 * stage + 12)
        (projectionConfig 200 inputLeftRev
          (projectionCodeCells
            (encodeNatAppend stage
              (encodeBoolWordAppend result
                (symbol :: suffix))))) =
        projectionConfig 300 stageLeftRev
          (projectionCodeCells
            (encodeBoolWordAppend result
              (symbol :: suffix)))
    rw [run_stage_nat_bool_word_suffix]
  · intro m
    exact
      run_result_suffix_ne_halt
        result symbol suffix
        (List.append (projectionStageTickCellsRev stage) inputLeftRev) m

 /-- {name}`decode_none_ne_halt` establishes the halting condition in this construction. -/
theorem decode_none_ne_halt
    {code : Word MachineCodeSymbol}
    (hdecode :
      DovetailControllerLayout.decode code = none)
    (n : Nat) :
    (Description.runConfig n
      (Description.initial
        (encodeCodeWordAsInput code))).state ≠
      Description.halt := by
  cases code with
  | nil =>
      exact
        state_ne_halt_of_stepConfig_none
          (n := n) (by rfl) (by
            change (0 : Nat) ≠ 999
            omega)
  | cons symbol rest =>
      cases symbol with
      | header =>
          have hmid :
              forall m : Nat,
                (Description.runConfig m
                  (projectionConfig 100 [none, none, none, none]
                    (projectionCodeCells rest))).state ≠
                  Description.halt := by
            unfold DovetailControllerLayout.decode at hdecode
            cases hstage :
                DovetailLayout.decodeStageInput rest with
            | none =>
                unfold DovetailLayout.decodeStageInput at hstage
                cases hinput : decodeBoolWord rest with
                | none =>
                    intro m
                    exact
                      run_state100_decodeBoolWord_none_ne_halt
                        rest ([] : List (Option Bool)) hinput m
                | some parsedInput =>
                    rcases parsedInput with ⟨input, restAfterInput⟩
                    simp [hinput] at hstage
                    cases hnat : decodeNat restAfterInput with
                    | none =>
                        have hrest :
                            rest =
                              encodeBoolWordAppend input
                                restAfterInput :=
                          decodeBoolWord_eq_some_encodeBoolWordAppend
                            hinput
                        intro m
                        rw [hrest]
                        exact
                          run_state100_input_bool_word_stage_decodeNat_none_ne_halt
                            input restAfterInput ([] : List (Option Bool))
                            hnat m
                    | some parsedNat =>
                        simp [hnat] at hstage
            | some parsedStage =>
                rcases parsedStage with ⟨parsedInputStage, restAfterStage⟩
                rcases parsedInputStage with ⟨input, stage⟩
                cases hresult :
                    decodeBoolWord restAfterStage with
                | none =>
                    have hrest :
                        rest =
                          DovetailLayout.stageInputCodeAppend
                            input stage restAfterStage :=
                      DovetailLayout.decodeStageInput_eq_some_stageInputCodeAppend
                        hstage
                    intro m
                    rw [hrest]
                    apply
                      ne_halt_of_reaches_ne_halt_region
                        (k := projectionInputBoolWordCost input)
                        (mid :=
                          projectionConfig 200
                            (List.append
                              (projectionCodeCells
                                (encodeBoolWord input)).reverse
                              (List.append [none, none, none, none]
                                ([] : List (Option Bool))))
                            (projectionCodeCells
                              (encodeNatAppend stage
                                restAfterStage)))
                    · simp [DovetailLayout.stageInputCodeAppend]
                      exact
                        run_input_bool_word_suffix
                          input stage restAfterStage
                          ([] : List (Option Bool))
                    · intro t
                      exact
                        run_state200_stage_nat_result_decodeBoolWord_none_ne_halt
                          stage restAfterStage
                          (List.append
                            (projectionCodeCells
                              (encodeBoolWord input)).reverse
                            (List.append [none, none, none, none]
                              ([] : List (Option Bool))))
                          hresult t
                | some parsedResult =>
                    simp [hstage, hresult] at hdecode
          apply
            ne_halt_of_reaches_ne_halt_region
              (k := 4)
              (mid :=
                projectionConfig 100 [none, none, none, none]
                  (projectionCodeCells rest))
          · simp [encodeCodeWordAsInput,
              encodeCodeSymbolAsInput]
            change
              Description.runConfig 4
                (Description.initial
                  (List.append [false, false, false, false]
                    (encodeCodeWordAsInput rest))) =
                projectionConfig 100 [none, none, none, none]
                  (projectionCodeCells rest)
            rw [run_header]
            rfl
          · exact hmid
      | transition =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 3) (by rfl) (by
                change (3 : Nat) ≠ 999
                omega)
      | tick =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by rfl) (by
                change (2 : Nat) ≠ 999
                omega)
      | done =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 2) (by rfl) (by
                change (2 : Nat) ≠ 999
                omega)
      | blank =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (1 : Nat) ≠ 999
                omega)
      | zero =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (1 : Nat) ≠ 999
                omega)
      | one =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (1 : Nat) ≠ 999
                omega)
      | moveLeft =>
          exact
            ne_halt_of_reaches_stepConfig_none
              (k := 1) (by rfl) (by
                change (1 : Nat) ≠ 999
                omega)
      | moveRight =>
          exact
            state_ne_halt_of_stepConfig_none
              (n := n) (by rfl) (by
                change (0 : Nat) ≠ 999
                omega)

 /-- {name}`decodeComplete_of_halting_run` establishes the halting condition in this construction. -/
theorem decodeComplete_of_halting_run
    {code : Word MachineCodeSymbol} {n : Nat}
    (hstate :
      (Description.runConfig n
        (Description.initial
          (encodeCodeWordAsInput code))).state =
        Description.halt) :
    exists C : DovetailControllerLayout,
      DovetailControllerLayout.decodeComplete code =
        some C := by
  unfold DovetailControllerLayout.decodeComplete
  cases hdecode : DovetailControllerLayout.decode code with
  | none =>
      exfalso
      exact
        decode_none_ne_halt
          hdecode n hstate
  | some parsed =>
      rcases parsed with ⟨C, suffix⟩
      cases suffix with
      | nil =>
          exact ⟨C, rfl⟩
      | cons symbol rest =>
          exfalso
          have hcode :
              code =
                DovetailControllerLayout.encodeAppend C
                  (symbol :: rest) :=
            DovetailControllerLayout.decode_eq_some_encodeAppend
              hdecode
          subst code
          exact
            encodeAppend_nonempty_suffix_ne_halt
              C symbol rest n hstate

 /-- {name}`decodeComplete_of_haltsWithOutput` establishes the halting condition in this construction. -/
theorem decodeComplete_of_haltsWithOutput
    {code out : Word MachineCodeSymbol}
    (h :
      Description.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out)) :
    exists C : DovetailControllerLayout,
      DovetailControllerLayout.decodeComplete code =
        some C := by
  rcases h with ⟨n, hn⟩
  exact
    decodeComplete_of_halting_run
      (code := code) (n := n) hn.left

 /-- {name}`exists_layout_of_haltsWithOutput` establishes the halting condition in this construction. -/
theorem exists_layout_of_haltsWithOutput
    {code out : Word MachineCodeSymbol}
    (h :
      Description.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out)) :
    exists C : DovetailControllerLayout,
      code = DovetailControllerLayout.encode C ∧
        out = DovetailControllerLayout.stageInputCode C := by
  rcases
    decodeComplete_of_haltsWithOutput
      h with
    ⟨C, hdecode⟩
  have hcode :
      code = DovetailControllerLayout.encode C :=
    DovetailControllerLayout.decodeComplete_eq_some_encode
      hdecode
  subst code
  have hsuccess :=
    haltsWithOutput_encode C
  have hbits :
      encodeCodeWordAsInput out =
        encodeCodeWordAsInput
          (DovetailControllerLayout.stageInputCode C) :=
    haltsWithOutput_functional_of_haltTransitionFree
      haltTransitionFree
      h hsuccess
  have hout :
      out = DovetailControllerLayout.stageInputCode C :=
    encodeCodeWordAsInput_injective hbits
  exact ⟨C, rfl, hout⟩

 /-- {name}`haltsWithOutput_iff_exists_layout` provides an important equivalence or equality lemma. -/
theorem haltsWithOutput_iff_exists_layout
    (code out : Word MachineCodeSymbol) :
    Description.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out) <->
      exists C : DovetailControllerLayout,
        code = DovetailControllerLayout.encode C ∧
          out = DovetailControllerLayout.stageInputCode C := by
  constructor
  · intro h
    exact
      exists_layout_of_haltsWithOutput
        h
  · intro h
    rcases h with ⟨C, rfl, rfl⟩
    exact
      haltsWithOutput_encode C

 /-- {name}`haltsWithOutput_of_transform_eq_some` provides an important equivalence or equality lemma. -/
theorem haltsWithOutput_of_transform_eq_some
    {code out : Word MachineCodeSymbol}
    (h :
      PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
          code = some out) :
    Description.HaltsWithOutput
      (encodeCodeWordAsInput code)
      (encodeCodeWordAsInput out) := by
  have hparsed :=
    (pairedRecognizerDovetailControllerStageInputCode_transform_eq_some_iff
      code out).mp h
  exact
    (haltsWithOutput_iff_exists_layout
      code out).mpr hparsed

 /-- {name}`transform_eq_some_of_haltsWithOutput` provides an important equivalence or equality lemma. -/
theorem transform_eq_some_of_haltsWithOutput
    {code out : Word MachineCodeSymbol}
    (h :
      Description.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out)) :
    PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
        code = some out := by
  have hparsed :=
    (haltsWithOutput_iff_exists_layout
      code out).mp h
  exact
    (pairedRecognizerDovetailControllerStageInputCode_transform_eq_some_iff
      code out).mpr hparsed

 /-- {name}`haltsWithOutput_iff` provides an important equivalence or equality lemma. -/
theorem haltsWithOutput_iff
    (code out : Word MachineCodeSymbol) :
    Description.HaltsWithOutput
        (encodeCodeWordAsInput code)
        (encodeCodeWordAsInput out) <->
      PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
        code = some out := by
  constructor
  · exact
      transform_eq_some_of_haltsWithOutput
  · exact
      haltsWithOutput_of_transform_eq_some

 /-- {name}`outputCompiledSubroutine` captures the core lemma for this local construction. -/
theorem outputCompiledSubroutine :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      Description :=
  ⟨⟨wellFormed,
      haltsWithOutput_iff⟩,
    haltTransitionFree⟩

 /-- {name}`encodedControllerStageInputProjectionCodeWordSubroutineConstruction_scaffold` describes append/fold behavior used by later composition. -/
theorem encodedControllerStageInputProjectionCodeWordSubroutineConstruction_scaffold :
    EncodedControllerStageInputProjectionCodeWordSubroutineConstruction := by
  exact
    ⟨Description,
      outputCompiledSubroutine⟩

end ControllerStageInputProjection

end Computability
end FoC
