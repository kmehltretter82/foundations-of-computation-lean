import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Lookup

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.SemanticIteration

open FiniteRecognizer.Interpreter.UniformInterpreterOneStep

theorem find?_eq_some_first_decompose
    {α : Type}
    (predicate : α -> Bool)
    (items : List α)
    (found : α)
    (hfind : items.find? predicate = some found) :
    exists before after : List α,
      items = List.append before (found :: after) /\
        (forall candidate : α,
          List.Mem candidate before -> predicate candidate = false) /\
        predicate found = true := by
  induction items with
  | nil =>
      simp at hfind
  | cons head tail ih =>
      cases hhead : predicate head with
      | false =>
          have htail : tail.find? predicate = some found := by
            simpa [List.find?, hhead] using hfind
          rcases ih htail with
            ⟨before, after, hitems, hbefore, hfound⟩
          refine ⟨head :: before, after, ?_, ?_, hfound⟩
          · simp [hitems]
          · intro candidate hmem
            rcases List.mem_cons.mp hmem with hcandidate | hcandidate
            · subst candidate
              exact hhead
            · exact hbefore candidate hcandidate
      | true =>
          have hfound : head = found := by
            simpa [List.find?, hhead] using hfind
          subst found
          refine ⟨[], tail, rfl, ?_, hhead⟩
          intro candidate hmem
          cases hmem
  done

theorem lookupTransition_eq_some_first_decompose
    (D : MachineDescription)
    (config : MachineDescription.Configuration)
    (selected : TransitionDescription)
    (hlookup :
      D.lookupTransition config.state (Tape.read config.tape) =
        some selected) :
    exists before after : List TransitionDescription,
      D.transitions = List.append before (selected :: after) /\
        (forall candidate : TransitionDescription,
          List.Mem candidate before ->
            MachineDescription.Matches config.state
              (Tape.read config.tape) candidate = false) /\
        MachineDescription.Matches config.state
          (Tape.read config.tape) selected = true := by
  unfold MachineDescription.lookupTransition at hlookup
  exact find?_eq_some_first_decompose
    (MachineDescription.Matches config.state (Tape.read config.tape))
    D.transitions selected hlookup
  done

theorem lookupTransition_eq_none_every_misses
    (D : MachineDescription)
    (config : MachineDescription.Configuration)
    (hlookup :
      D.lookupTransition config.state (Tape.read config.tape) = none) :
    forall candidate : TransitionDescription,
      List.Mem candidate D.transitions ->
        MachineDescription.Matches config.state
          (Tape.read config.tape) candidate = false := by
  unfold MachineDescription.lookupTransition at hlookup
  intro candidate hmem
  have hnot := List.find?_eq_none.mp hlookup candidate hmem
  cases hmatch :
      MachineDescription.Matches config.state
        (Tape.read config.tape) candidate with
  | false => rfl
  | true =>
      exact False.elim (hnot hmatch)
  done

theorem runConfig_succ_of_lookup_some
    (D : MachineDescription)
    (remaining : Nat)
    (config : MachineDescription.Configuration)
    (selected : TransitionDescription)
    (hlookup :
      D.lookupTransition config.state (Tape.read config.tape) =
        some selected) :
    D.runConfig (remaining + 1) config =
      D.runConfig remaining
        { state := selected.target
          tape :=
            Tape.move selected.move
              (Tape.write selected.write config.tape) } := by
  simp [MachineDescription.runConfig, MachineDescription.stepConfig,
    hlookup]
  done

theorem runConfig_succ_of_lookup_none
    (D : MachineDescription)
    (remaining : Nat)
    (config : MachineDescription.Configuration)
    (hlookup :
      D.lookupTransition config.state (Tape.read config.tape) = none) :
    D.runConfig (remaining + 1) config = config := by
  simp [MachineDescription.runConfig, MachineDescription.stepConfig,
    hlookup]
  done

/-- Once lookup misses, the semantic machine stutters for every amount of
remaining fuel.  The configuration equality keeps both the state and the
entire tape context available to the physical terminal branch. -/
theorem runConfig_eq_self_of_lookup_none
    (D : MachineDescription)
    (config : MachineDescription.Configuration)
    (hlookup :
      D.lookupTransition config.state (Tape.read config.tape) = none) :
    forall later : Nat, D.runConfig later config = config := by
  intro later
  cases later with
  | zero =>
      rfl
  | succ remaining =>
      simpa [Nat.succ_eq_add_one] using
        runConfig_succ_of_lookup_none D remaining config hlookup
  done

/-- Component form of `runConfig_eq_self_of_lookup_none`, convenient when an
outer invariant stores the semantic state and tape context separately. -/
theorem runConfig_state_tape_stutter_of_lookup_none
    (D : MachineDescription)
    (config : MachineDescription.Configuration)
    (hlookup :
      D.lookupTransition config.state (Tape.read config.tape) = none) :
    forall later : Nat,
      (D.runConfig later config).state = config.state /\
      (D.runConfig later config).tape = config.tape := by
  intro later
  rw [runConfig_eq_self_of_lookup_none D config hlookup later]
  exact ⟨rfl, rfl⟩
  done


end FiniteRecognizer.Interpreter.SemanticIteration

end Computability
end FoC
