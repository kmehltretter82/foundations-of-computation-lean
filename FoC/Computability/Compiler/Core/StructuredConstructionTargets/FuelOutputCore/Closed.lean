import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelOutputCore.Runs
import FoC.Computability.Compiler.Structured.Lowering.DivergenceTransfer
import FoC.Computability.Compiler.Structured.Lowering.EncodedInjectivity

set_option doc.verso true

/-!
# Closed semantics of the fuel-output structured core

Forward transfer and semantic inversion for the lowered fuel-output core.
Rejected layouts reach the cursor-moving spin state; guarded-encoding
injectivity and the static divergence transfer then rule out a physical halt.
-/

namespace FoC.Computability.StructuredConstructionTargets.FuelOutputCore

open Languages
open MachineDescription
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

private theorem transition_action0_moves
    {n : Nat} {t : Transition}
    (ht : t ∈ (coreD n).transitions) :
    exists a0 a1 a2 : TapeAction,
      t.actions = [a0, a1, a2] ∧ a0.move ≠ HeadMove.stay := by
  change t ∈ (table n).description.transitions at ht
  rcases (table n).mem_transitions ht with ⟨s, hs, hrow⟩
  rcases (table n).mem_rowsFor hrow with
    ⟨r0, r1, r2, st, hnext, rfl⟩
  exact
    ⟨st.action0, st.action1, st.action2, rfl,
      next_action0_move_ne_stay n s r0 r1 r2 st hnext⟩

private theorem stepConfig_state_ne_or_tapes_ne
    {n : Nat}
    {c d : CommonGround.FiniteTransducers.Structured.Configuration}
    (hstep : (coreD n).stepConfig c = some d) :
    c.state ≠ d.state ∨ c.tapes ≠ d.tapes := by
  apply stepConfig_state_ne_or_tapes_ne_of_state_or_action_moves
    (D := coreD n) rfl ?_ hstep
  intro t ht
  rcases transition_action0_moves ht with
    ⟨a0, a1, a2, hactions, hmove⟩
  exact ⟨a0, a1, a2, hactions, Or.inr (Or.inl hmove)⟩

private theorem stepConfig_spin (n : Nat) (T0 T2 : Tape Bool) :
    (coreD n).stepConfig (coreCfg n CoreState.spin T0 T2) =
      some (coreCfg n CoreState.spin (keepR.apply T0) T2) := by
  change
    (table n).description.stepConfig
        (ThreeTape.config ((table n).stateId CoreState.spin)
          T0 Tape.blank T2) = _
  rw [(table n).stepConfig_config
    (s := CoreState.spin)
    (mem_coreStates_of_fixed (n := n) (s := CoreState.spin) (by decide))
    T0 Tape.blank T2]
  rw [show
    (table n).next CoreState.spin (Tape.read T0) (Tape.read Tape.blank)
        (Tape.read T2) =
      some ⟨CoreState.spin, keepR, keepS, keepS⟩ from rfl]
  simp [coreCfg, keepS, TapeAction.stay, TapeAction.apply, HeadMove.apply]

private theorem runConfig_spin (n k : Nat) (T0 T2 : Tape Bool) :
    exists T0' : Tape Bool,
      (coreD n).runConfig k (coreCfg n CoreState.spin T0 T2) =
        coreCfg n CoreState.spin T0' T2 := by
  induction k generalizing T0 with
  | zero => exact ⟨T0, rfl⟩
  | succ k ih =>
      change
        exists T0',
          (table n).description.runConfig (k + 1)
              (ThreeTape.config ((table n).stateId CoreState.spin)
                T0 Tape.blank T2) =
            coreCfg n CoreState.spin T0' T2
      rw [(table n).runConfig_succ_config
        (s := CoreState.spin)
        (mem_coreStates_of_fixed (n := n) (s := CoreState.spin) (by decide))
        (T0 := T0) (T1 := Tape.blank) (T2 := T2)
        (st := ⟨CoreState.spin, keepR, keepS, keepS⟩) rfl k]
      simpa [coreD, coreCfg, keepS, TapeAction.stay, TapeAction.apply,
        HeadMove.apply] using ih (keepR.apply T0)

private theorem leadsSpin_stepConfig_ne_none
    {n : Nat}
    {c : CommonGround.FiniteTransducers.Structured.Configuration}
    (hspin : LeadsSpin n c) (k : Nat) :
    (coreD n).stepConfig ((coreD n).runConfig k c) ≠ none := by
  rcases hspin with ⟨T0, T2, j, hj⟩
  intro hnone
  rcases runConfig_spin n k T0 T2 with ⟨U0, hU0⟩
  have hstay := Description.runConfig_of_stepConfig_none hnone j
  have hsplit := Description.runConfig_add (coreD n) k j c
  have hcfg :
      (coreD n).runConfig k c = coreCfg n CoreState.spin U0 T2 := by
    calc
      (coreD n).runConfig k c =
          (coreD n).runConfig j ((coreD n).runConfig k c) := hstay.symm
      _ = (coreD n).runConfig (k + j) c := hsplit.symm
      _ = (coreD n).runConfig k (coreCfg n CoreState.spin T0 T2) := hj k
      _ = coreCfg n CoreState.spin U0 T2 := hU0
  rw [hcfg, stepConfig_spin] at hnone
  cases hnone

private theorem leadsSpin_state_ne_halt
    {n : Nat}
    {c : CommonGround.FiniteTransducers.Structured.Configuration}
    (hspin : LeadsSpin n c) (k : Nat) :
    ((coreD n).runConfig k c).state ≠ (coreD n).halt := by
  intro hhalt
  have hnone := Description.stepConfig_halt_none
    (table n).description_haltTransitionFree
    ((coreD n).runConfig k c) hhalt
  exact leadsSpin_stepConfig_ne_none hspin k hnone

private theorem not_halts_of_leadsSpin
    {n : Nat}
    {c : CommonGround.FiniteTransducers.Structured.Configuration}
    (hcState : c.state = (coreD n).start)
    (hcTapes : c.tapes.length = (coreD n).tapeCount)
    (hspin : LeadsSpin n c) (T : Tape Bool) :
    ¬ (lowerStructured3Description (coreD n)).HaltsFromTape
      (encodedGuardedStructuredTapes c.tapes) T := by
  exact
    lowerStructured3Description_not_halts_of_state_or_tape_progress
      (table n).description_wellFormed
      (table n).description_haltTransitionFree
      (table n).description_supportsReadWriteRows3
      c hcState hcTapes
      (leadsSpin_stepConfig_ne_none hspin)
      (leadsSpin_state_ne_halt hspin)
      stepConfig_state_ne_or_tapes_ne
      T

private theorem leadsSpin_of_state_ne (n : Nat) (Lay : SimulatorLayout)
    (hstate : Lay.config.state ≠ n) :
    LeadsSpin n
      (coreCfg n CoreState.hdr0
        (CommonGround.FiniteTransducers.tapeAtCells []
          (codeBits (SimulatorLayout.encode Lay)))
        Tape.blank) := by
  rw [encode_decomp]
  rw [codeBits_cons]
  refine leadsSpin_of_leads (leads_header n [] _ Tape.blank) ?_
  rw [codeBits_append]
  refine leadsSpin_of_leads (leads_inLen n _ _ _ Tape.blank) ?_
  rw [codeBits_append]
  rw [codeBits_append]
  refine leadsSpin_of_leads
    (leads_inBits_stage n Lay.input Lay.stage _ _ Tape.blank) ?_
  rw [codeBits_append]
  exact leads_chk_reject n Lay.config.state 0
    (by simpa using hstate) (Nat.zero_le n) _ _ Tape.blank

private def rewindContext (Lay : SimulatorLayout) : List (Option Bool) :=
  List.append (markedBits Lay.config.tape.head).reverse
    (List.append (flatRevTokBits Lay.config.tape.left.reverse)
      (List.append
        (List.append doneRevBits
          (tickRevBits Lay.config.tape.left.length))
        (List.append
          (List.append doneRevBits (tickRevBits Lay.config.state))
          (List.append
            (List.append doneRevBits (tickRevBits Lay.stage))
            (List.append
              (flatRevTokBits (Lay.input.map some).reverse)
              (List.append
                (List.append doneRevBits
                  (tickRevBits (Lay.input.map some).length))
                (List.append
                  (tokBits MachineCodeSymbol.header).reverse [])))))))

private theorem leads_to_emission_start (n : Nat) (Lay : SimulatorLayout)
    (hstate : Lay.config.state = n) :
    Leads n
      (coreCfg n CoreState.hdr0
        (CommonGround.FiniteTransducers.tapeAtCells []
          (codeBits (SimulatorLayout.encode Lay)))
        Tape.blank)
      (coreCfg n (CoreState.re3 Emission.start)
        (headTape
          (List.append
            (flatRevTokBits Lay.config.tape.right.reverse)
            (List.append
              (List.append doneRevBits
                (tickRevBits Lay.config.tape.right.length))
              (rewindContext Lay)))
          (List.append (tokBits (cellTok (some Lay.hit))) [none]))
        (emissionTape [])) := by
  rw [encode_decomp]
  rw [codeBits_cons]
  refine Leads.trans (leads_header n [] _ Tape.blank) ?_
  rw [codeBits_append]
  refine Leads.trans (leads_inLen n _ _ _ Tape.blank) ?_
  rw [codeBits_append]
  rw [codeBits_append]
  refine Leads.trans
    (leads_inBits_stage n Lay.input Lay.stage _ _ Tape.blank) ?_
  rw [codeBits_append]
  have hstate' : 0 + Lay.config.state = n := by simpa using hstate
  refine Leads.trans
    (leads_chk_accept n Lay.config.state 0 hstate' _ _ Tape.blank) ?_
  rw [codeBits_append]
  refine Leads.trans
    (leads_lLen n Lay.config.tape.left.length _ _ Tape.blank) ?_
  rw [codeBits_append]
  refine Leads.trans
    (leads_lb n Lay.config.tape.left _ _ Tape.blank) ?_
  rw [codeBits_cons]
  refine Leads.trans
    (leads_lb_one n Lay.config.tape.head _ _ Tape.blank) ?_
  rw [codeBits_append]
  refine Leads.trans
    (leads_mark_rLen n Lay.config.tape.head
      Lay.config.tape.right.length _ _ Tape.blank) ?_
  rw [codeBits_append]
  refine Leads.trans
    (leads_rb n Lay.config.tape.right _ _ Tape.blank) ?_
  have hhit :
      List.append [cellTok (some Lay.hit)]
          ([] : Word MachineCodeSymbol) =
        [cellTok (some Lay.hit)] := by rfl
  rw [hhit, codeBits_cons, codeBits_nil]
  refine Leads.trans
    (leads_rb_one n (some Lay.hit) _ [] Tape.blank) ?_
  refine Leads.trans (leads_endTurn n Lay.hit _ Tape.blank) ?_
  have hmark :
      pushBits (markedBits Lay.config.tape.head)
          (pushBits (codeBits (Lay.config.tape.left.map cellTok))
            (pushBits (codeBits (encodeNat Lay.config.tape.left.length))
              (pushBits (codeBits (encodeNat Lay.config.state))
                (pushBits (codeBits (encodeNat Lay.stage))
                  (pushBits
                    (codeBits ((Lay.input.map some).map cellTok))
                    (pushBits
                      (codeBits (encodeNat (Lay.input.map some).length))
                      (pushBits (tokBits MachineCodeSymbol.header)
                        []))))))) ≠ [] := by
    simp [markedBits, pushBits]
  have hrlen := pushBits_ne_nil hmark
    (codeBits (encodeNat Lay.config.tape.right.length))
  have hfull := pushBits_ne_nil hrlen
    (codeBits (Lay.config.tape.right.map cellTok))
  obtain ⟨hitv2, hitv3, hhitbits⟩ :=
    exists_cellTok_bits (some Lay.hit)
  rw [hhitbits]
  refine Leads.trans
    (stepL_headTape (n := n) (mem_fixed (by decide))
      (fun _ => rfl) hfull _ Tape.blank) ?_
  simp only [pushBits_eq_reverse_append, codeBits_cells_reverse,
    codeBits_encodeNat_reverse]
  exact Leads.refl n _

private theorem leads_hd_spin_of_fold_none
    (n : Nat) (h : Option Bool) {v2 v3 : Bool}
    (hbits :
      tokBits (cellTok h) = [some false, some true, some v2, some v3])
    {e : Emission}
    (hfold : streamFold? e h.toList = none)
    (LL cellsR : List (Option Bool)) (acc : List Bool) :
    LeadsSpin n
      (coreCfg n (CoreState.hd0 v3 v2 e)
        (CommonGround.FiniteTransducers.tapeAtCells LL
          (some true :: cellsR))
        (emissionTape acc)) := by
  cases h with
  | none => simp at hfold
  | some bit =>
      cases bit with
      | false =>
          obtain ⟨e', hstream⟩ := stream_false_some e
          rw [show (some false).toList = [false] from rfl,
            streamFold?_cons_of_stream_some _ hstream] at hfold
          simp at hfold
      | true =>
          have hstream : e.stream true = none := by
            cases hs : e.stream true with
            | none => rfl
            | some e' =>
                rw [show (some true).toList = [true] from rfl,
                  streamFold?_cons_of_stream_some _ hs] at hfold
                simp at hfold
          have hbits' :
              ([some false, some true, some true, some false] :
                List (Option Bool)) =
                [some false, some true, some v2, some v3] := hbits
          simp at hbits'
          obtain ⟨hv2, hv3⟩ := hbits'
          subst hv2
          subst hv3
          exact leads_hd_spin n ⟨rfl, rfl⟩ hstream LL cellsR acc

private theorem leadsSpin_of_streamFold_none
    (n : Nat) (Lay : SimulatorLayout)
    (hstate : Lay.config.state = n)
    (hfold :
      streamFold? Emission.start (layoutStream Lay.config.tape) = none) :
    LeadsSpin n
      (coreCfg n CoreState.hdr0
        (CommonGround.FiniteTransducers.tapeAtCells []
          (codeBits (SimulatorLayout.encode Lay)))
        Tape.blank) := by
  refine leadsSpin_of_leads
    (leads_to_emission_start n Lay hstate) ?_
  rw [append_assoc_explicit doneRevBits
    (tickRevBits Lay.config.tape.right.length)
    (rewindContext Lay)]
  cases hR : streamFold? Emission.start
      (Lay.config.tape.right.reverse.filterMap id) with
  | none =>
      exact leads_re_spin n Lay.config.tape.right.reverse
        [] Emission.start _ _ rfl hR
  | some eR =>
      refine leadsSpin_of_leads
        (leads_re_ok n Lay.config.tape.right.reverse
          [] Emission.start eR _ _ rfl hR) ?_
      obtain ⟨headv2, headv3, hheadbits⟩ :=
        exists_cellTok_bits Lay.config.tape.head
      refine leadsSpin_of_leads
        (leads_rt n Lay.config.tape.right.length hheadbits
          _ _ eR _) ?_
      cases hH : streamFold? eR Lay.config.tape.head.toList with
      | none =>
          exact leads_hd_spin_of_fold_none n
            Lay.config.tape.head hheadbits hH _ _ _
      | some eH =>
          refine leadsSpin_of_leads
            (leads_hd_ok n Lay.config.tape.head hheadbits
              hR hH (append_cons_ne_nil _ _ _) _) ?_
          refine leadsSpin_of_leads
            (leads_ls n Lay.config.tape.left.reverse eH _ _ _) ?_
          rw [unwalkBits_reverse_eq]
          have hL :
              streamFold? eH
                (Lay.config.tape.left.filterMap id) = none := by
            rw [layoutStream, streamFold?_append, hR] at hfold
            change
              streamFold? eR
                (List.append Lay.config.tape.head.toList
                  (Lay.config.tape.left.filterMap id)) = none at hfold
            rw [streamFold?_append, hH] at hfold
            change
              streamFold? eH
                (Lay.config.tape.left.filterMap id) = none at hfold
            exact hfold
          have hfoldRH :
              streamFold? Emission.start
                (List.append
                  (Lay.config.tape.right.reverse.filterMap id)
                  Lay.config.tape.head.toList) = some eH := by
            rw [streamFold?_append, hR]
            exact hH
          exact leads_le_spin n Lay.config.tape.left
            _ eH _ _ hfoldRH hL

private theorem leadsSpin_of_streamFold_misaligned
    (n : Nat) (Lay : SimulatorLayout)
    (hstate : Lay.config.state = n)
    {efin : Emission}
    (hfold :
      streamFold? Emission.start (layoutStream Lay.config.tape) =
        some efin)
    (hpos : efin.pos ≠ GroupPos.p0) :
    LeadsSpin n
      (coreCfg n CoreState.hdr0
        (CommonGround.FiniteTransducers.tapeAtCells []
          (codeBits (SimulatorLayout.encode Lay)))
        Tape.blank) := by
  rw [layoutStream] at hfold
  rcases streamFold?_append_some hfold with
    ⟨eR, hfoldR, hfoldHL⟩
  rcases streamFold?_append_some hfoldHL with
    ⟨eH, hfoldH, hfoldL⟩
  refine leadsSpin_of_leads
    (leads_to_emission_start n Lay hstate) ?_
  rw [append_assoc_explicit doneRevBits
    (tickRevBits Lay.config.tape.right.length)
    (rewindContext Lay)]
  refine leadsSpin_of_leads
    (leads_re_ok n Lay.config.tape.right.reverse
      [] Emission.start eR _ _ rfl hfoldR) ?_
  obtain ⟨headv2, headv3, hheadbits⟩ :=
    exists_cellTok_bits Lay.config.tape.head
  refine leadsSpin_of_leads
    (leads_rt n Lay.config.tape.right.length hheadbits
      _ _ eR _) ?_
  refine leadsSpin_of_leads
    (leads_hd_ok n Lay.config.tape.head hheadbits
      hfoldR hfoldH (append_cons_ne_nil _ _ _) _) ?_
  refine leadsSpin_of_leads
    (leads_ls n Lay.config.tape.left.reverse eH _ _ _) ?_
  rw [unwalkBits_reverse_eq]
  have hfoldRH :
      streamFold? Emission.start
        (List.append
          (Lay.config.tape.right.reverse.filterMap id)
          Lay.config.tape.head.toList) = some eH := by
    rw [streamFold?_append, hfoldR]
    exact hfoldH
  refine leadsSpin_of_leads
    (leads_le_ok n Lay.config.tape.left _ eH efin _ _
      hfoldRH hfoldL) ?_
  exact leads_markCheck_spin n hpos _ _ _

private theorem tapeAtCells_map_some_eq_input (w : Word Bool) :
    CommonGround.FiniteTransducers.tapeAtCells [] (w.map some) =
      Tape.input w := by
  cases w <;> rfl

private theorem tapeAtCells_map_some_append_none_eq_padding
    (w : Word Bool) (hw : w ≠ []) :
    CommonGround.FiniteTransducers.tapeAtCells []
        (List.append (w.map some) [none]) =
      CommonGround.FiniteTransducers.inputWithTrailingBlankPadding w 1 := by
  cases w with
  | nil => exact absurd rfl hw
  | cons bit rest => rfl

/-- A valid layout runs to its padded logical input and exact output code. -/
theorem lowered_halts_of_valid_code
    (n : Nat) (Lay : SimulatorLayout) (out : Word MachineCodeSymbol)
    (hstate : Lay.config.state = n)
    (hout :
      Tape.normalizedOutput Lay.config.tape =
        encodeCodeWordAsInput out) :
    (lowerStructured3Description (coreD n)).HaltsFromTapeEquiv
      (encodedGuardedStructuredTapes
        [ Tape.input (encodeCodeWordAsInput (SimulatorLayout.encode Lay))
        , Tape.blank
        , Tape.blank ])
      (encodedGuardedStructuredTapes
        [ CommonGround.FiniteTransducers.inputWithTrailingBlankPadding
            (encodeCodeWordAsInput (SimulatorLayout.encode Lay)) 1
        , Tape.blank
        , Tape.input (encodeCodeWordAsInput out) ]) := by
  obtain ⟨efin, hfoldCode, hpos⟩ := streamFold?_encode_reverse out
  have hlayout :
      (layoutStream Lay.config.tape).reverse =
        encodeCodeWordAsInput out := by
    rw [layoutStream_reverse]
    exact hout
  have hfold :
      streamFold? Emission.start (layoutStream Lay.config.tape) =
        some efin := by
    rw [← List.reverse_reverse (layoutStream Lay.config.tape)]
    rw [hlayout]
    exact hfoldCode
  rcases (leads_halt_of_valid n Lay hstate hfold hpos).to_runConfig with
    ⟨j, hrun⟩
  let T0in :=
    CommonGround.FiniteTransducers.tapeAtCells []
      (codeBits (SimulatorLayout.encode Lay))
  let T0out :=
    CommonGround.FiniteTransducers.tapeAtCells []
      (List.append (codeBits (SimulatorLayout.encode Lay)) [none])
  let T2out := Tape.input (layoutStream Lay.config.tape).reverse
  have hhalts :
      (coreD n).HaltsWithTapes
        (coreCfg n CoreState.hdr0 T0in Tape.blank)
        [T0out, Tape.blank, T2out] := by
    refine ⟨j, ?_⟩
    change
      (coreD n).runConfig j
          (coreCfg n CoreState.hdr0 T0in Tape.blank) =
        coreCfg n CoreState.halt T0out T2out
    simpa [T0in, T0out, T2out] using hrun
  have hlowered :=
    lowerStructured3Description_haltsFromConfigWithTapes
      (table n).description_wellFormed
      (table n).description_haltTransitionFree
      (table n).description_supportsReadWriteRows3
      (c := coreCfg n CoreState.hdr0 T0in Tape.blank)
      (tapes := [T0out, Tape.blank, T2out])
      rfl rfl hhalts
  have hbitsne :
      encodeCodeWordAsInput (SimulatorLayout.encode Lay) ≠ [] := by
    rw [encode_decomp]
    simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput]
  have hT0in :
      T0in = Tape.input
        (encodeCodeWordAsInput (SimulatorLayout.encode Lay)) := by
    exact tapeAtCells_map_some_eq_input _
  have hT0out :
      T0out =
        CommonGround.FiniteTransducers.inputWithTrailingBlankPadding
          (encodeCodeWordAsInput (SimulatorLayout.encode Lay)) 1 := by
    exact tapeAtCells_map_some_append_none_eq_padding _ hbitsne
  have hT2out : T2out = Tape.input (encodeCodeWordAsInput out) := by
    unfold T2out
    rw [hlayout]
  rw [hT0in, hT0out, hT2out] at hlowered
  simpa [coreCfg, coreD] using hlowered

private theorem not_halts_of_layout_leadsSpin
    (n : Nat) (Lay : SimulatorLayout)
    (hspin :
      LeadsSpin n
        (coreCfg n CoreState.hdr0
          (CommonGround.FiniteTransducers.tapeAtCells []
            (codeBits (SimulatorLayout.encode Lay)))
          Tape.blank))
    (T : Tape Bool) :
    ¬ (lowerStructured3Description (coreD n)).HaltsFromTape
      (encodedGuardedStructuredTapes
        [ Tape.input (encodeCodeWordAsInput (SimulatorLayout.encode Lay))
        , Tape.blank
        , Tape.blank ]) T := by
  have hnot := not_halts_of_leadsSpin
    (n := n)
    (c :=
      coreCfg n CoreState.hdr0
        (CommonGround.FiniteTransducers.tapeAtCells []
          (codeBits (SimulatorLayout.encode Lay)))
        Tape.blank)
    rfl rfl hspin T
  simpa [coreCfg, codeBits,
    tapeAtCells_map_some_eq_input] using hnot

/-- Every physical halt recovers a valid layout and an encoded output witness. -/
theorem lowered_closed
    (n : Nat) (Lay : SimulatorLayout) (T : Tape Bool)
    (hhalt :
      (lowerStructured3Description (coreD n)).HaltsFromTape
        (encodedGuardedStructuredTapes
          [ Tape.input (encodeCodeWordAsInput (SimulatorLayout.encode Lay))
          , Tape.blank
          , Tape.blank ]) T) :
    exists out : Word MachineCodeSymbol,
      Lay.config.state = n ∧
        Tape.normalizedOutput Lay.config.tape =
          encodeCodeWordAsInput out ∧
        Tape.Equiv T
          (encodedGuardedStructuredTapes
            [ CommonGround.FiniteTransducers.inputWithTrailingBlankPadding
                (encodeCodeWordAsInput (SimulatorLayout.encode Lay)) 1
            , Tape.blank
            , Tape.input (encodeCodeWordAsInput out) ]) := by
  by_cases hstate : Lay.config.state = n
  · cases hfold :
      streamFold? Emission.start (layoutStream Lay.config.tape) with
    | none =>
        exfalso
        exact
          (not_halts_of_layout_leadsSpin n Lay
            (leadsSpin_of_streamFold_none n Lay hstate hfold) T)
            hhalt
    | some efin =>
        by_cases hpos : efin.pos = GroupPos.p0
        · have hrev :
              layoutStream Lay.config.tape =
                (Tape.normalizedOutput Lay.config.tape).reverse := by
            have h := congrArg List.reverse
              (layoutStream_reverse Lay.config.tape)
            simpa using h
          have hfoldOut :
              streamFold? Emission.start
                  (Tape.normalizedOutput Lay.config.tape).reverse =
                some efin := by
            rw [← hrev]
            exact hfold
          rcases exists_code_of_streamFold?_reverse hfoldOut hpos with
            ⟨out, hout⟩
          rcases lowered_halts_of_valid_code
              n Lay out hstate hout with
            ⟨Tactual, hactual, hTactual⟩
          have hLhtf :
              (lowerStructured3Description (coreD n)).HaltTransitionFree :=
            (lowerStructured3Description_subroutineReady
              (table n).description_wellFormed
              (table n).description_supportsReadWriteRows3).right
          have hEq :=
            MachineDescription.haltsFromTape_functional_of_haltTransitionFree
              hLhtf hhalt hactual
          refine ⟨out, hstate, hout, ?_⟩
          rw [hEq]
          exact hTactual
        · exfalso
          exact
            (not_halts_of_layout_leadsSpin n Lay
              (leadsSpin_of_streamFold_misaligned
                n Lay hstate hfold hpos) T) hhalt
  · exfalso
    exact
      (not_halts_of_layout_leadsSpin n Lay
        (leadsSpin_of_state_ne n Lay hstate) T) hhalt

end FoC.Computability.StructuredConstructionTargets.FuelOutputCore
