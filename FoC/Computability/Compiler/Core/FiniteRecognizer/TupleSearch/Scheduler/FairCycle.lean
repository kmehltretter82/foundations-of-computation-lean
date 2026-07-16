import FoC.Computability.TuringMachine

set_option doc.verso true

/-!
**Fair-cycle semantics for tuple search.** The physical driver exposes one
canonical configuration per scheduler frame.  A successful frame reaches the
public halt; a failed frame takes a positive finite run to the next canonical
frame.  These lemmas isolate the infinitary fairness argument from the finite
physical phase assembly.
-/

namespace FoC.Computability.TuringMachine.FairCycle

theorem computesIn_length_le_of_halted_run
    {M : TuringMachine symbol state}
    (hstop : HaltingTransitionsDisabled M)
    {runLength prefixLength : Nat}
    {source final prefixTarget : Configuration symbol state}
    (hrun : ComputesIn M runLength source final)
    (hfinal : Halted M final)
    (hprefix : ComputesIn M prefixLength source prefixTarget) :
    prefixLength ≤ runLength := by
  induction hrun generalizing prefixLength prefixTarget with
  | zero source =>
      cases hprefix with
      | zero _ => exact Nat.le_refl 0
      | succ hstep _ =>
          exact False.elim (no_step_from_halted hstop hfinal hstep)
  | @succ runLength source next final hstep htail ih =>
      cases hprefix with
      | zero _ => exact Nat.zero_le _
      | @succ prefixLength _ prefixNext prefixTarget hprefixStep hprefixTail =>
          have hnext : next = prefixNext :=
            step_deterministic hstep hprefixStep
          subst prefixNext
          exact Nat.succ_le_succ (ih hfinal hprefixTail)

theorem haltsFromIn_tail_of_computesIn
    {M : TuringMachine symbol state}
    {prefixLength tailLength : Nat}
    {source target : Configuration symbol state}
    (hprefix : ComputesIn M prefixLength source target)
    (hhalt : HaltsFromIn M (prefixLength + tailLength) source) :
    HaltsFromIn M tailLength target := by
  induction hprefix generalizing tailLength with
  | zero source =>
      simpa using hhalt
  | @succ prefixLength source next target hstep htail ih =>
      have hhalt' : HaltsFromIn M (prefixLength + tailLength) next := by
        apply haltsFromIn_tail_of_step hstep
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hhalt
      exact ih hhalt'

def advanceN (advance : cursor -> cursor) : Nat -> cursor -> cursor
  | 0, cursor => cursor
  | n + 1, cursor => advanceN advance n (advance cursor)

theorem advanceN_succ
    (advance : cursor -> cursor) (n : Nat) (cursor : cursor) :
    advanceN advance (n + 1) cursor =
      advanceN advance n (advance cursor) := by
  rfl

theorem advanceN_apply_comm
    (advance : cursor -> cursor) (n : Nat) (cursor : cursor) :
    advanceN advance n (advance cursor) =
      advance (advanceN advance n cursor) := by
  induction n generalizing cursor with
  | zero => rfl
  | succ n ih =>
      simp only [advanceN_succ]
      exact ih (advance cursor)

theorem advanceN_succ_right
    (advance : cursor -> cursor) (n : Nat) (cursor : cursor) :
    advanceN advance (n + 1) cursor =
      advance (advanceN advance n cursor) := by
  rw [advanceN_succ, advanceN_apply_comm]

theorem haltsFrom_of_eventual_success
    {M : TuringMachine symbol state}
    (source : cursor -> Configuration symbol state)
    (advance : cursor -> cursor)
    (success : cursor -> Prop)
    (hsuccess : forall cursor, success cursor -> HaltsFrom M (source cursor))
    (hfailure : forall cursor, ¬ success cursor ->
      exists steps : Nat,
        0 < steps ∧
          ComputesIn M steps (source cursor) (source (advance cursor)))
    {cursor : cursor}
    (heventual : exists n : Nat, success (advanceN advance n cursor)) :
    HaltsFrom M (source cursor) := by
  rcases heventual with ⟨n, hn⟩
  induction n generalizing cursor with
  | zero =>
      exact hsuccess cursor hn
  | succ n ih =>
      by_cases hcurrent : success cursor
      · exact hsuccess cursor hcurrent
      · rcases hfailure cursor hcurrent with ⟨steps, _hpositive, hrun⟩
        have htail : HaltsFrom M (source (advance cursor)) := by
          apply ih
          simpa [advanceN_succ] using hn
        exact halts_from_of_computes_prefix
          (computesIn_to_computes hrun) htail

theorem eventual_success_of_haltsFromIn
    {M : TuringMachine symbol state}
    (hstop : HaltingTransitionsDisabled M)
    (source : cursor -> Configuration symbol state)
    (advance : cursor -> cursor)
    (success : cursor -> Prop)
    (hfailure : forall cursor, ¬ success cursor ->
      exists steps : Nat,
        0 < steps ∧
          ComputesIn M steps (source cursor) (source (advance cursor))) :
    forall fuel cursor,
      HaltsFromIn M fuel (source cursor) ->
        exists n : Nat, success (advanceN advance n cursor) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      intro cursor hhalt
      by_cases hcurrent : success cursor
      · exact ⟨0, hcurrent⟩
      · rcases hfailure cursor hcurrent with
          ⟨steps, hpositive, hprefix⟩
        rcases hhalt with ⟨final, hrun, hfinal⟩
        have hle : steps ≤ fuel :=
          computesIn_length_le_of_halted_run hstop hrun hfinal hprefix
        let tailFuel := fuel - steps
        have hfuel : fuel = steps + tailFuel := by
          dsimp [tailFuel]
          exact (Nat.add_sub_of_le hle).symm
        have htailHalt : HaltsFromIn M tailFuel (source (advance cursor)) := by
          apply haltsFromIn_tail_of_computesIn hprefix
          rw [← hfuel]
          exact ⟨final, hrun, hfinal⟩
        have htailLt : tailFuel < fuel := by
          dsimp [tailFuel]
          lia
        rcases ih tailFuel htailLt (advance cursor) htailHalt with
          ⟨n, hn⟩
        exact ⟨n + 1, by simpa [advanceN_succ] using hn⟩

theorem haltsFrom_iff_eventual_success
    {M : TuringMachine symbol state}
    (hstop : HaltingTransitionsDisabled M)
    (source : cursor -> Configuration symbol state)
    (advance : cursor -> cursor)
    (success : cursor -> Prop)
    (hsuccess : forall cursor, success cursor -> HaltsFrom M (source cursor))
    (hfailure : forall cursor, ¬ success cursor ->
      exists steps : Nat,
        0 < steps ∧
          ComputesIn M steps (source cursor) (source (advance cursor)))
    (cursor : cursor) :
    HaltsFrom M (source cursor) <->
      exists n : Nat, success (advanceN advance n cursor) := by
  constructor
  · intro hhalt
    rcases halts_from_to_halts_from_in hhalt with ⟨fuel, hfuel⟩
    exact eventual_success_of_haltsFromIn hstop source advance success
      hfailure fuel cursor hfuel
  · exact haltsFrom_of_eventual_success source advance success
      hsuccess hfailure

/-!
The physical scheduler retains harmless tape padding between rounds.  Its
canonical-frame invariant is therefore relational: a round can finish at any
configuration representing the next cursor, rather than at one chosen tape
representative.  The following variant carries that representation relation
through the same fairness argument.
-/

theorem haltsFrom_of_eventual_success_rel
    {M : TuringMachine symbol state}
    (represents : cursor -> Configuration symbol state -> Prop)
    (advance : cursor -> cursor)
    (success : cursor -> Prop)
    (hsuccess : forall cursor config,
      represents cursor config -> success cursor -> HaltsFrom M config)
    (hfailure : forall cursor config,
      represents cursor config -> ¬ success cursor ->
        exists steps : Nat,
        exists nextConfig : Configuration symbol state,
          0 < steps ∧
            ComputesIn M steps config nextConfig ∧
            represents (advance cursor) nextConfig)
    {cursor : cursor} {config : Configuration symbol state}
    (hrep : represents cursor config)
    (heventual : exists n : Nat, success (advanceN advance n cursor)) :
    HaltsFrom M config := by
  rcases heventual with ⟨n, hn⟩
  induction n generalizing cursor config with
  | zero =>
      exact hsuccess cursor config hrep hn
  | succ n ih =>
      by_cases hcurrent : success cursor
      · exact hsuccess cursor config hrep hcurrent
      · rcases hfailure cursor config hrep hcurrent with
          ⟨steps, nextConfig, _hpositive, hrun, hnextRep⟩
        have htail : HaltsFrom M nextConfig := by
          apply ih hnextRep
          simpa [advanceN_succ] using hn
        exact halts_from_of_computes_prefix
          (computesIn_to_computes hrun) htail

theorem eventual_success_of_haltsFromIn_rel
    {M : TuringMachine symbol state}
    (hstop : HaltingTransitionsDisabled M)
    (represents : cursor -> Configuration symbol state -> Prop)
    (advance : cursor -> cursor)
    (success : cursor -> Prop)
    (hfailure : forall cursor config,
      represents cursor config -> ¬ success cursor ->
        exists steps : Nat,
        exists nextConfig : Configuration symbol state,
          0 < steps ∧
            ComputesIn M steps config nextConfig ∧
            represents (advance cursor) nextConfig) :
    forall fuel cursor config,
      represents cursor config ->
      HaltsFromIn M fuel config ->
        exists n : Nat, success (advanceN advance n cursor) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      intro cursor config hrep hhalt
      by_cases hcurrent : success cursor
      · exact ⟨0, hcurrent⟩
      · rcases hfailure cursor config hrep hcurrent with
          ⟨steps, nextConfig, hpositive, hprefix, hnextRep⟩
        rcases hhalt with ⟨final, hrun, hfinal⟩
        have hle : steps ≤ fuel :=
          computesIn_length_le_of_halted_run hstop hrun hfinal hprefix
        let tailFuel := fuel - steps
        have hfuel : fuel = steps + tailFuel := by
          dsimp [tailFuel]
          exact (Nat.add_sub_of_le hle).symm
        have htailHalt : HaltsFromIn M tailFuel nextConfig := by
          apply haltsFromIn_tail_of_computesIn hprefix
          rw [← hfuel]
          exact ⟨final, hrun, hfinal⟩
        have htailLt : tailFuel < fuel := by
          dsimp [tailFuel]
          lia
        rcases ih tailFuel htailLt (advance cursor) nextConfig
            hnextRep htailHalt with ⟨n, hn⟩
        exact ⟨n + 1, by simpa [advanceN_succ] using hn⟩

theorem haltsFrom_iff_eventual_success_rel
    {M : TuringMachine symbol state}
    (hstop : HaltingTransitionsDisabled M)
    (represents : cursor -> Configuration symbol state -> Prop)
    (advance : cursor -> cursor)
    (success : cursor -> Prop)
    (hsuccess : forall cursor config,
      represents cursor config -> success cursor -> HaltsFrom M config)
    (hfailure : forall cursor config,
      represents cursor config -> ¬ success cursor ->
        exists steps : Nat,
        exists nextConfig : Configuration symbol state,
          0 < steps ∧
            ComputesIn M steps config nextConfig ∧
            represents (advance cursor) nextConfig)
    (cursor : cursor) (config : Configuration symbol state)
    (hrep : represents cursor config) :
    HaltsFrom M config <->
      exists n : Nat, success (advanceN advance n cursor) := by
  constructor
  · intro hhalt
    rcases halts_from_to_halts_from_in hhalt with ⟨fuel, hfuel⟩
    exact eventual_success_of_haltsFromIn_rel hstop represents advance
      success hfailure fuel cursor config hrep hfuel
  · exact haltsFrom_of_eventual_success_rel represents advance success
      hsuccess hfailure hrep

theorem haltsFrom_iff_of_computesIn_prefix
    {M : TuringMachine symbol state}
    (hstop : HaltingTransitionsDisabled M)
    {steps : Nat} {source target : Configuration symbol state}
    (hprefix : ComputesIn M steps source target) :
    HaltsFrom M source <-> HaltsFrom M target := by
  constructor
  · intro hhalt
    rcases halts_from_to_halts_from_in hhalt with
      ⟨fuel, final, hrun, hfinal⟩
    have hle : steps ≤ fuel :=
      computesIn_length_le_of_halted_run hstop hrun hfinal hprefix
    let tailFuel := fuel - steps
    have hfuel : fuel = steps + tailFuel := by
      dsimp [tailFuel]
      exact (Nat.add_sub_of_le hle).symm
    apply halts_from_in_to_halts_from
    apply haltsFromIn_tail_of_computesIn hprefix
    rw [← hfuel]
    exact ⟨final, hrun, hfinal⟩
  · intro hhalt
    exact halts_from_of_computes_prefix
      (computesIn_to_computes hprefix) hhalt

end FoC.Computability.TuringMachine.FairCycle
