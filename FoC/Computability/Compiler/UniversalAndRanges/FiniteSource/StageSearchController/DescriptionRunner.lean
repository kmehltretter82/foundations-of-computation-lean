import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.StageSearchController.BoundedSimulatorLoop

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

universe uStage uDescription uSimulator

inductive BudgetCheckerDescriptionRunnerState
    (descriptionState : Type uDescription) where
  | scan : BudgetCheckerDescriptionRunnerState descriptionState
  | run : descriptionState ->
      BudgetCheckerDescriptionRunnerState descriptionState

namespace BudgetCheckerDescriptionRunnerState

def finite (hdescription : Foundation.FiniteType descriptionState) :
    Foundation.FiniteType
      (BudgetCheckerDescriptionRunnerState descriptionState) where
  elems := scan :: hdescription.elems.map run
  complete := by
    intro state
    cases state with
    | scan =>
        simp
    | run state =>
        simp
        exact hdescription.complete state

end BudgetCheckerDescriptionRunnerState

private abbrev BCRS := BudgetCheckerDescriptionRunnerState

def budgetCheckerDescriptionRunnerTape
    (blankPrefix : Nat) (rest : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := List.replicate blankPrefix none
        head := none
        right := [] }
  | symbol :: suffix =>
      { left := List.replicate blankPrefix none
        head := some symbol
        right := suffix.map some }

private abbrev BCRT := budgetCheckerDescriptionRunnerTape

theorem budgetCheckerDescriptionRunnerTape_nil_eq_input
    (tokens : Word MachineCodeSymbol) :
    BCRT 0 tokens = Tape.input tokens := by
  cases tokens <;> rfl

theorem budgetCheckerDescriptionRunnerTape_move_right
    (blankPrefix : Nat) (symbol : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    Tape.move Direction.right
        (Tape.write none
          (BCRT blankPrefix
            (symbol :: suffix))) =
      BCRT (blankPrefix + 1) suffix := by
  cases suffix <;>
    simp [budgetCheckerDescriptionRunnerTape, Tape.move,
      Tape.moveRight, Tape.write]
  all_goals
    rw [List.replicate_succ]

def budgetCheckerDescriptionRunnerMachine
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState) :
    TuringMachine MachineCodeSymbol
      (BCRS descriptionState) where
  start := BudgetCheckerDescriptionRunnerState.scan
  halt := BudgetCheckerDescriptionRunnerState.run descriptionDecoder.halt
  transition := fun state cell =>
    match state with
    | BudgetCheckerDescriptionRunnerState.scan =>
        match cell with
        | some MachineCodeSymbol.tick =>
            some (none, Direction.right,
              BudgetCheckerDescriptionRunnerState.scan)
        | some MachineCodeSymbol.done =>
            some (none, Direction.right,
              BudgetCheckerDescriptionRunnerState.run
                descriptionDecoder.start)
        | _ => none
    | BudgetCheckerDescriptionRunnerState.run state =>
        match descriptionDecoder.transition state cell with
        | none => none
        | some (write, dir, nextState) =>
            some (write, dir,
              BudgetCheckerDescriptionRunnerState.run nextState)
  statesFinite :=
    BudgetCheckerDescriptionRunnerState.finite
      descriptionDecoder.statesFinite

private abbrev BCRM
    {descriptionState : Type uDescription}
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState) :=
  budgetCheckerDescriptionRunnerMachine descriptionDecoder

theorem budgetCheckerDescriptionRunnerMachine_step_tick
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    (blankPrefix : Nat) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Step
      (BCRM descriptionDecoder)
      { state := BudgetCheckerDescriptionRunnerState.scan
        tape :=
          BCRT blankPrefix
            (MachineCodeSymbol.tick :: suffix) }
      { state := BudgetCheckerDescriptionRunnerState.scan
        tape :=
          BCRT (blankPrefix + 1) suffix } := by
  rw [← budgetCheckerDescriptionRunnerTape_move_right
    blankPrefix MachineCodeSymbol.tick suffix]
  exact TuringMachine.Step.mk (by
    simp [budgetCheckerDescriptionRunnerMachine,
                budgetCheckerDescriptionRunnerTape, Tape.read])

theorem budgetCheckerDescriptionRunnerMachine_step_done
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    (blankPrefix : Nat) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Step
      (BCRM descriptionDecoder)
      { state := BudgetCheckerDescriptionRunnerState.scan
        tape :=
          BCRT blankPrefix
            (MachineCodeSymbol.done :: suffix) }
      { state :=
          BudgetCheckerDescriptionRunnerState.run descriptionDecoder.start
        tape :=
          BCRT (blankPrefix + 1) suffix } := by
  rw [← budgetCheckerDescriptionRunnerTape_move_right
    blankPrefix MachineCodeSymbol.done suffix]
  exact TuringMachine.Step.mk (by
    simp [budgetCheckerDescriptionRunnerMachine,
                budgetCheckerDescriptionRunnerTape, Tape.read])

theorem budgetCheckerDescriptionRunnerMachine_step_run
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    {state nextState : descriptionState}
    {tape : Tape MachineCodeSymbol} {write : Option MachineCodeSymbol}
    {dir : Direction}
    (haction :
      descriptionDecoder.transition state (Tape.read tape) =
        some (write, dir, nextState)) :
    TuringMachine.Step
      (BCRM descriptionDecoder)
      { state := BudgetCheckerDescriptionRunnerState.run state
        tape := tape }
      { state := BudgetCheckerDescriptionRunnerState.run nextState
        tape := Tape.move dir (Tape.write write tape) } := by
  exact TuringMachine.Step.mk (by
    simp [budgetCheckerDescriptionRunnerMachine, haction])

theorem dropTrailingNone_replicate_none
    (n : Nat) :
    Tape.dropTrailingNone
        (List.replicate n (none : Option MachineCodeSymbol)) = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [List.replicate, Tape.dropTrailingNone, ih]

theorem budgetCheckerDescriptionRunnerTape_equiv_input
    (blankPrefix : Nat) (encoded : Word MachineCodeSymbol) :
    Tape.Equiv
      (BCRT blankPrefix encoded)
      (Tape.input encoded) := by
  cases encoded with
  | nil =>
      constructor
      · exact dropTrailingNone_replicate_none blankPrefix
      · constructor <;> rfl
  | cons symbol suffix =>
      constructor
      · exact dropTrailingNone_replicate_none blankPrefix
      · constructor <;> rfl

theorem turingMachine_step_of_tape_equiv
    {M : TuringMachine symbol state}
    {c d : TuringMachine.Configuration symbol state}
    {tape : Tape symbol}
    (hstep : TuringMachine.Step M c d)
    (htape : Tape.Equiv c.tape tape) :
    exists nextTape : Tape symbol,
      TuringMachine.Step M
        { state := c.state, tape := tape }
        { state := d.state, tape := nextTape } ∧
        Tape.Equiv d.tape nextTape := by
  cases hstep with
  | mk haction =>
      rename_i write dir nextState
      refine
        ⟨Tape.move dir (Tape.write write tape), ?_, ?_⟩
      · exact TuringMachine.Step.mk (by
          rw [← Tape.Equiv.read_eq htape]
          exact haction)
      · exact Tape.Equiv.move (Tape.Equiv.write htape write) dir

theorem turingMachine_computes_of_tape_equiv
    {M : TuringMachine symbol state}
    {c e : TuringMachine.Configuration symbol state}
    {tape : Tape symbol}
    (hcomp : TuringMachine.Computes M c e)
    (htape : Tape.Equiv c.tape tape) :
    exists e' : TuringMachine.Configuration symbol state,
      TuringMachine.Computes M { state := c.state, tape := tape } e' ∧
        e'.state = e.state ∧
        Tape.Equiv e.tape e'.tape := by
  induction hcomp generalizing tape with
  | refl c =>
      exact
        ⟨{ state := c.state, tape := tape },
          TuringMachine.Computes.refl _, rfl, htape⟩
  | step hstep hrest ih =>
      rcases turingMachine_step_of_tape_equiv hstep htape with
        ⟨nextTape, hstep', htape'⟩
      rcases ih htape' with ⟨e', hcomp', hstate'', htape''⟩
      exact
        ⟨e', TuringMachine.Computes.step hstep' hcomp',
          hstate'', htape''⟩

theorem turingMachine_haltsFrom_of_tape_equiv
    {M : TuringMachine symbol state}
    {state : state} {tape tape' : Tape symbol}
    (htape : Tape.Equiv tape tape')
    (hhalt : TuringMachine.HaltsFrom M { state := state, tape := tape }) :
    TuringMachine.HaltsFrom M { state := state, tape := tape' } := by
  rcases hhalt with ⟨final, hcomp, hfinal⟩
  rcases turingMachine_computes_of_tape_equiv hcomp htape with
    ⟨final', hcomp', hstate, _htape'⟩
  exact ⟨final', hcomp', by simpa [TuringMachine.Halted, hstate] using hfinal⟩

theorem turingMachine_haltsFrom_tape_equiv_iff
    (M : TuringMachine symbol state)
    (state : state) {tape tape' : Tape symbol}
    (htape : Tape.Equiv tape tape') :
    TuringMachine.HaltsFrom M { state := state, tape := tape } <->
      TuringMachine.HaltsFrom M { state := state, tape := tape' } := by
  constructor
  · exact turingMachine_haltsFrom_of_tape_equiv htape
  · exact turingMachine_haltsFrom_of_tape_equiv (Tape.Equiv.symm htape)

theorem budgetCheckerDescriptionRunnerMachine_computes_run
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    {c d : TuringMachine.Configuration MachineCodeSymbol descriptionState}
    (hcomp : TuringMachine.Computes descriptionDecoder c d) :
    TuringMachine.Computes
      (BCRM descriptionDecoder)
      { state := BudgetCheckerDescriptionRunnerState.run c.state
        tape := c.tape }
      { state := BudgetCheckerDescriptionRunnerState.run d.state
        tape := d.tape } := by
  induction hcomp with
  | refl c =>
      exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      cases hstep with
      | mk haction =>
          exact TuringMachine.Computes.step
            (budgetCheckerDescriptionRunnerMachine_step_run
              descriptionDecoder haction)
            ih

theorem budgetCheckerDescriptionRunnerMachine_computesIn_scan
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    (blankPrefix budget : Nat) (encoded : Word MachineCodeSymbol) :
    TuringMachine.ComputesIn
      (BCRM descriptionDecoder)
      (budget + 1)
      { state := BudgetCheckerDescriptionRunnerState.scan
        tape :=
          BCRT blankPrefix
            (CodePrefixRecognizerStageCode encoded budget) }
      { state :=
          BudgetCheckerDescriptionRunnerState.run descriptionDecoder.start
        tape :=
          BCRT
            (blankPrefix + budget + 1) encoded } := by
  induction budget generalizing blankPrefix with
  | zero =>
      simpa [CodePrefixRecognizerStageCode,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, Nat.add_assoc] using
        TuringMachine.ComputesIn.succ
          (budgetCheckerDescriptionRunnerMachine_step_done
            descriptionDecoder blankPrefix encoded)
          (TuringMachine.ComputesIn.zero _)
  | succ budget ih =>
      have htail := ih (blankPrefix + 1)
      have hstep :=
        budgetCheckerDescriptionRunnerMachine_step_tick
          descriptionDecoder blankPrefix
          (CodePrefixRecognizerStageCode encoded budget)
      simpa [CodePrefixRecognizerStageCode,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using
        TuringMachine.ComputesIn.succ hstep htail

theorem budgetCheckerDescriptionRunnerMachine_halts_run_only
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    {steps : Nat} {state : descriptionState}
    {tape : Tape MachineCodeSymbol}
    (hhalt :
      TuringMachine.HaltsFromIn
        (BCRM descriptionDecoder)
        steps
        { state := BudgetCheckerDescriptionRunnerState.run state
          tape := tape }) :
    TuringMachine.HaltsFrom descriptionDecoder
      { state := state, tape := tape } := by
  induction steps generalizing state tape with
  | zero =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp
      cases hfinal
      exact TuringMachine.halts_from_halted rfl
  | succ steps ih =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp with
      | succ hstep hrest =>
          cases hstep with
          | mk haction =>
              rename_i write dir nextState
              cases hdesc :
                  descriptionDecoder.transition state (Tape.read tape) with
              | none =>
                  simp [budgetCheckerDescriptionRunnerMachine, hdesc]
                    at haction
              | some action =>
                  rcases action with ⟨write', dir', nextState'⟩
                  simp [budgetCheckerDescriptionRunnerMachine, hdesc]
                    at haction
                  rcases haction with ⟨hwrite, hdir, hnext⟩
                  subst write
                  subst dir
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        (BCRM
                          descriptionDecoder)
                        steps
                        { state :=
                            BudgetCheckerDescriptionRunnerState.run
                              nextState'
                          tape :=
                            Tape.move dir' (Tape.write write' tape) } :=
                    ⟨final, hrest, hfinal⟩
                  rcases ih htail with
                    ⟨descFinal, hdescComp, hdescHalt⟩
                  exact
                    ⟨descFinal,
                      TuringMachine.Computes.step
                        (TuringMachine.Step.mk hdesc) hdescComp,
                      hdescHalt⟩

theorem budgetCheckerDescriptionRunnerMachine_halts_scan_only
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    {steps blankPrefix budget : Nat}
    {encoded : Word MachineCodeSymbol}
    (hhalt :
      TuringMachine.HaltsFromIn
        (BCRM descriptionDecoder)
        steps
        { state := BudgetCheckerDescriptionRunnerState.scan
          tape :=
            BCRT blankPrefix
              (CodePrefixRecognizerStageCode encoded budget) }) :
    TuringMachine.HaltsFrom descriptionDecoder
      { state := descriptionDecoder.start
        tape :=
          BCRT
            (blankPrefix + budget + 1) encoded } := by
  induction budget generalizing steps blankPrefix with
  | zero =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp with
      | zero =>
          cases hfinal
      | succ hstep hrest =>
          rename_i tailSteps mid
          cases hstep with
          | mk haction =>
              rename_i write dir nextState
              simp [budgetCheckerDescriptionRunnerMachine,
                budgetCheckerDescriptionRunnerTape,
                CodePrefixRecognizerStageCode,
                MachineDescription.encodeNatAppend,
                MachineDescription.encodeNat, Tape.read] at haction
              rcases haction with ⟨hwrite, hdir, hnext⟩
              subst write
              subst dir
              cases hnext
              have htail :
                  TuringMachine.HaltsFromIn
                    (BCRM
                      descriptionDecoder)
                    tailSteps
                    { state :=
                        BudgetCheckerDescriptionRunnerState.run
                          descriptionDecoder.start
                      tape :=
                        BCRT
                          (blankPrefix + 1) encoded } := by
                refine ⟨final, ?_, hfinal⟩
                simpa [CodePrefixRecognizerStageCode,
                  MachineDescription.encodeNatAppend,
                  MachineDescription.encodeNat,
                  budgetCheckerDescriptionRunnerTape_move_right]
                  using hrest
              simpa [Nat.add_assoc] using
                budgetCheckerDescriptionRunnerMachine_halts_run_only
                  descriptionDecoder htail
  | succ budget ih =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp with
      | zero =>
          cases hfinal
      | succ hstep hrest =>
          rename_i tailSteps mid
          cases hstep with
          | mk haction =>
              rename_i write dir nextState
              simp [budgetCheckerDescriptionRunnerMachine,
                budgetCheckerDescriptionRunnerTape,
                CodePrefixRecognizerStageCode,
                MachineDescription.encodeNatAppend,
                MachineDescription.encodeNat, Tape.read] at haction
              rcases haction with ⟨hwrite, hdir, hnext⟩
              subst write
              subst dir
              cases hnext
              have htail :
                  TuringMachine.HaltsFromIn
                    (BCRM
                      descriptionDecoder)
                    tailSteps
                    { state := BudgetCheckerDescriptionRunnerState.scan
                      tape :=
                        BCRT
                          (blankPrefix + 1)
                          (CodePrefixRecognizerStageCode encoded budget) } := by
                refine ⟨final, ?_, hfinal⟩
                simpa [CodePrefixRecognizerStageCode,
                  MachineDescription.encodeNatAppend,
                  MachineDescription.encodeNat,
                  budgetCheckerDescriptionRunnerTape_move_right]
                  using hrest
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                ih htail

noncomputable def finiteStateIndexOf
    {α : Type uDescription} (finite : Foundation.FiniteType α)
    (state : α) : Fin finite.elems.length :=
  let h : ∃ i, ∃ hlt : i < finite.elems.length,
      finite.elems[i] = state :=
    (List.mem_iff_getElem).mp (finite.complete state)
  ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩

def finiteStateValueOf
    {α : Type uDescription} (finite : Foundation.FiniteType α)
    (index : Fin finite.elems.length) : α :=
  finite.elems[index]

theorem finiteStateValueOf_indexOf
    {α : Type uDescription} (finite : Foundation.FiniteType α)
    (state : α) :
    finiteStateValueOf finite (finiteStateIndexOf finite state) = state := by
  unfold finiteStateValueOf finiteStateIndexOf
  let h : ∃ i, ∃ hlt : i < finite.elems.length,
      finite.elems[i] = state :=
    (List.mem_iff_getElem).mp (finite.complete state)
  exact Classical.choose_spec (Classical.choose_spec h)

def budgetCheckerDescriptionRunnerIndexedStateFinite (n : Nat) :
    Foundation.FiniteType (Option (Fin n)) where
  elems := none :: (List.finRange n).map some
  complete := by
    intro state
    cases state with
    | none =>
        simp
    | some index =>
        simp

noncomputable def budgetCheckerDescriptionRunnerIndexedMachine
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState) :
    TuringMachine MachineCodeSymbol
      (Option (Fin descriptionDecoder.statesFinite.elems.length)) where
  start := none
  halt :=
    some
      (finiteStateIndexOf descriptionDecoder.statesFinite
        descriptionDecoder.halt)
  transition := fun state cell =>
    match state with
    | none =>
        match cell with
        | some MachineCodeSymbol.tick =>
            some (none, Direction.right, none)
        | some MachineCodeSymbol.done =>
            some (none, Direction.right,
              some
                (finiteStateIndexOf descriptionDecoder.statesFinite
                  descriptionDecoder.start))
        | _ => none
    | some index =>
        match descriptionDecoder.transition
            (finiteStateValueOf descriptionDecoder.statesFinite index)
            cell with
        | none => none
        | some (write, dir, nextState) =>
            some (write, dir,
              some
                (finiteStateIndexOf descriptionDecoder.statesFinite
                  nextState))
  statesFinite :=
    budgetCheckerDescriptionRunnerIndexedStateFinite
      descriptionDecoder.statesFinite.elems.length

private noncomputable abbrev BCRIM
    {descriptionState : Type uDescription}
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState) :=
  budgetCheckerDescriptionRunnerIndexedMachine descriptionDecoder

theorem budgetCheckerDescriptionRunnerIndexedMachine_step_tick
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    (blankPrefix : Nat) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Step
      (BCRIM descriptionDecoder)
      { state := none
        tape :=
          BCRT blankPrefix
            (MachineCodeSymbol.tick :: suffix) }
      { state := none
        tape :=
          BCRT (blankPrefix + 1) suffix } := by
  rw [← budgetCheckerDescriptionRunnerTape_move_right
    blankPrefix MachineCodeSymbol.tick suffix]
  exact TuringMachine.Step.mk (by
    simp [budgetCheckerDescriptionRunnerIndexedMachine,
                budgetCheckerDescriptionRunnerTape, Tape.read])

theorem budgetCheckerDescriptionRunnerIndexedMachine_step_done
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    (blankPrefix : Nat) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Step
      (BCRIM descriptionDecoder)
      { state := none
        tape :=
          BCRT blankPrefix
            (MachineCodeSymbol.done :: suffix) }
      { state :=
          some
            (finiteStateIndexOf descriptionDecoder.statesFinite
              descriptionDecoder.start)
        tape :=
          BCRT (blankPrefix + 1) suffix } := by
  rw [← budgetCheckerDescriptionRunnerTape_move_right
    blankPrefix MachineCodeSymbol.done suffix]
  exact TuringMachine.Step.mk (by
    simp [budgetCheckerDescriptionRunnerIndexedMachine,
                budgetCheckerDescriptionRunnerTape, Tape.read])

theorem budgetCheckerDescriptionRunnerIndexedMachine_step_run
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    {state nextState : descriptionState}
    {tape : Tape MachineCodeSymbol} {write : Option MachineCodeSymbol}
    {dir : Direction}
    (haction :
      descriptionDecoder.transition state (Tape.read tape) =
        some (write, dir, nextState)) :
    TuringMachine.Step
      (BCRIM descriptionDecoder)
      { state :=
          some
            (finiteStateIndexOf descriptionDecoder.statesFinite state)
        tape := tape }
      { state :=
          some
            (finiteStateIndexOf descriptionDecoder.statesFinite nextState)
        tape := Tape.move dir (Tape.write write tape) } := by
  exact TuringMachine.Step.mk (by
    simp [budgetCheckerDescriptionRunnerIndexedMachine,
      finiteStateValueOf_indexOf, haction])

theorem budgetCheckerDescriptionRunnerIndexedMachine_computesIn_scan
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    (blankPrefix budget : Nat) (encoded : Word MachineCodeSymbol) :
    TuringMachine.ComputesIn
      (BCRIM descriptionDecoder)
      (budget + 1)
      { state := none
        tape :=
          BCRT blankPrefix
            (CodePrefixRecognizerStageCode encoded budget) }
      { state :=
          some
            (finiteStateIndexOf descriptionDecoder.statesFinite
              descriptionDecoder.start)
        tape :=
          BCRT
            (blankPrefix + budget + 1) encoded } := by
  induction budget generalizing blankPrefix with
  | zero =>
      simpa [CodePrefixRecognizerStageCode,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, Nat.add_assoc] using
        TuringMachine.ComputesIn.succ
          (budgetCheckerDescriptionRunnerIndexedMachine_step_done
            descriptionDecoder blankPrefix encoded)
          (TuringMachine.ComputesIn.zero _)
  | succ budget ih =>
      have htail := ih (blankPrefix + 1)
      have hstep :=
        budgetCheckerDescriptionRunnerIndexedMachine_step_tick
          descriptionDecoder blankPrefix
          (CodePrefixRecognizerStageCode encoded budget)
      simpa [CodePrefixRecognizerStageCode,
        MachineDescription.encodeNatAppend,
        MachineDescription.encodeNat, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using
        TuringMachine.ComputesIn.succ hstep htail

theorem budgetCheckerDescriptionRunnerIndexedMachine_computes_run
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    {c d : TuringMachine.Configuration MachineCodeSymbol descriptionState}
    (hcomp : TuringMachine.Computes descriptionDecoder c d) :
    TuringMachine.Computes
      (BCRIM descriptionDecoder)
      { state :=
          some
            (finiteStateIndexOf descriptionDecoder.statesFinite c.state)
        tape := c.tape }
      { state :=
          some
            (finiteStateIndexOf descriptionDecoder.statesFinite d.state)
        tape := d.tape } := by
  induction hcomp with
  | refl c =>
      exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      cases hstep with
      | mk haction =>
          exact TuringMachine.Computes.step
            (budgetCheckerDescriptionRunnerIndexedMachine_step_run
              descriptionDecoder haction)
            ih

theorem budgetCheckerDescriptionRunnerIndexedMachine_halts_run_only
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    {steps : Nat}
    {index : Fin descriptionDecoder.statesFinite.elems.length}
    {tape : Tape MachineCodeSymbol}
    (hhalt :
      TuringMachine.HaltsFromIn
        (BCRIM descriptionDecoder)
        steps
        { state := some index
          tape := tape }) :
    TuringMachine.HaltsFrom descriptionDecoder
      { state :=
          finiteStateValueOf descriptionDecoder.statesFinite index
        tape := tape } := by
  induction steps generalizing index tape with
  | zero =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp
      simp [TuringMachine.Halted,
        budgetCheckerDescriptionRunnerIndexedMachine] at hfinal
      subst index
      exact TuringMachine.halts_from_halted (by
        exact finiteStateValueOf_indexOf
          descriptionDecoder.statesFinite descriptionDecoder.halt)
  | succ steps ih =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp with
      | succ hstep hrest =>
          cases hstep with
          | mk haction =>
              rename_i write dir nextIndex
              let actual :=
                finiteStateValueOf descriptionDecoder.statesFinite index
              cases hdesc :
                  descriptionDecoder.transition actual (Tape.read tape) with
              | none =>
                  simp [budgetCheckerDescriptionRunnerIndexedMachine,
                    actual, hdesc] at haction
              | some action =>
                  rcases action with ⟨write', dir', nextState'⟩
                  simp [budgetCheckerDescriptionRunnerIndexedMachine,
                    actual, hdesc] at haction
                  rcases haction with ⟨hwrite, hdir, hnext⟩
                  subst write
                  subst dir
                  cases hnext
                  have htail :
                      TuringMachine.HaltsFromIn
                        (BCRIM
                          descriptionDecoder)
                        steps
                        { state :=
                            some
                              (finiteStateIndexOf
                                descriptionDecoder.statesFinite nextState')
                          tape :=
                            Tape.move dir' (Tape.write write' tape) } :=
                    ⟨final, hrest, hfinal⟩
                  rcases ih htail with
                    ⟨descFinal, hdescComp, hdescHalt⟩
                  have hdescComp' :
                      TuringMachine.Computes descriptionDecoder
                        { state := nextState'
                          tape :=
                            Tape.move dir' (Tape.write write' tape) }
                        descFinal := by
                    simpa [finiteStateValueOf_indexOf] using hdescComp
                  refine
                    ⟨descFinal,
                      TuringMachine.Computes.step
                        (TuringMachine.Step.mk hdesc) hdescComp',
                      hdescHalt⟩

theorem budgetCheckerDescriptionRunnerIndexedMachine_halts_scan_only
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState)
    {steps blankPrefix budget : Nat}
    {encoded : Word MachineCodeSymbol}
    (hhalt :
      TuringMachine.HaltsFromIn
        (BCRIM descriptionDecoder)
        steps
        { state := none
          tape :=
            BCRT blankPrefix
              (CodePrefixRecognizerStageCode encoded budget) }) :
    TuringMachine.HaltsFrom descriptionDecoder
      { state := descriptionDecoder.start
        tape :=
          BCRT
            (blankPrefix + budget + 1) encoded } := by
  induction budget generalizing steps blankPrefix with
  | zero =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp with
      | zero =>
          cases hfinal
      | succ hstep hrest =>
          rename_i tailSteps mid
          cases hstep with
          | mk haction =>
              rename_i write dir nextState
              simp [budgetCheckerDescriptionRunnerIndexedMachine,
                budgetCheckerDescriptionRunnerTape,
                CodePrefixRecognizerStageCode,
                MachineDescription.encodeNatAppend,
                MachineDescription.encodeNat, Tape.read] at haction
              rcases haction with ⟨hwrite, hdir, hnext⟩
              subst write
              subst dir
              cases hnext
              have htail :
                  TuringMachine.HaltsFromIn
                    (BCRIM
                      descriptionDecoder)
                    tailSteps
                    { state :=
                        some
                          (finiteStateIndexOf
                            descriptionDecoder.statesFinite
                            descriptionDecoder.start)
                      tape :=
                        BCRT
                          (blankPrefix + 1) encoded } := by
                refine ⟨final, ?_, hfinal⟩
                simpa [CodePrefixRecognizerStageCode,
                  MachineDescription.encodeNatAppend,
                  MachineDescription.encodeNat,
                  budgetCheckerDescriptionRunnerTape_move_right]
                  using hrest
              have hrun :=
                budgetCheckerDescriptionRunnerIndexedMachine_halts_run_only
                  descriptionDecoder htail
              simpa [Nat.add_assoc, finiteStateValueOf_indexOf] using hrun
  | succ budget ih =>
      rcases hhalt with ⟨final, hcomp, hfinal⟩
      cases hcomp with
      | zero =>
          cases hfinal
      | succ hstep hrest =>
          rename_i tailSteps mid
          cases hstep with
          | mk haction =>
              rename_i write dir nextState
              simp [budgetCheckerDescriptionRunnerIndexedMachine,
                budgetCheckerDescriptionRunnerTape,
                CodePrefixRecognizerStageCode,
                MachineDescription.encodeNatAppend,
                MachineDescription.encodeNat, Tape.read] at haction
              rcases haction with ⟨hwrite, hdir, hnext⟩
              subst write
              subst dir
              cases hnext
              have htail :
                  TuringMachine.HaltsFromIn
                    (BCRIM
                      descriptionDecoder)
                    tailSteps
                    { state := none
                      tape :=
                        BCRT
                          (blankPrefix + 1)
                          (CodePrefixRecognizerStageCode encoded budget) } := by
                refine ⟨final, ?_, hfinal⟩
                simpa [CodePrefixRecognizerStageCode,
                  MachineDescription.encodeNatAppend,
                  MachineDescription.encodeNat,
                  budgetCheckerDescriptionRunnerTape_move_right]
                  using hrest
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                ih htail

/--
Finite-machine leaf for stripping the stage budget before invoking the
description decoder.  This isolates the head-positioning and blank-context
simulation work from the bounded-pair search.
-/
theorem codePrefixStageSearchControllerBudgetCheckerDescriptionRunnerObligation_core
    (descriptionDecoder : TuringMachine MachineCodeSymbol descriptionState) :
    CodePrefixStageSearchControllerBudgetCheckerDescriptionRunnerObligation
      descriptionDecoder := by
  refine
    ⟨Option (Fin descriptionDecoder.statesFinite.elems.length),
      BCRIM descriptionDecoder, ?_⟩
  intro encoded budget
  constructor
  · intro hrunner
    rcases
        TuringMachine.halts_on_input_to_halts_on_input_in hrunner with
      ⟨steps, hsteps⟩
    have hfrom :
        TuringMachine.HaltsFromIn
          (BCRIM descriptionDecoder)
          steps
          { state := none
            tape :=
              BCRT 0
                (CodePrefixRecognizerStageCode encoded budget) } := by
      simpa [TuringMachine.HaltsOnInputIn, TuringMachine.initial,
        BCRIM,
        budgetCheckerDescriptionRunnerTape_nil_eq_input] using hsteps
    have hdescFrom :=
      budgetCheckerDescriptionRunnerIndexedMachine_halts_scan_only
        descriptionDecoder hfrom
    have hequiv :
        Tape.Equiv
          (BCRT (0 + budget + 1) encoded)
          (Tape.input encoded) :=
      budgetCheckerDescriptionRunnerTape_equiv_input
        (0 + budget + 1) encoded
    exact
      (turingMachine_haltsFrom_tape_equiv_iff
        descriptionDecoder descriptionDecoder.start hequiv).mp hdescFrom
  · intro hdescription
    rcases hdescription with ⟨final, hcomp, hhalt⟩
    have hscanIn :=
      budgetCheckerDescriptionRunnerIndexedMachine_computesIn_scan
        descriptionDecoder 0 budget encoded
    have hscan :
        TuringMachine.Computes
          (BCRIM descriptionDecoder)
          { state := none
            tape :=
              BCRT 0
                (CodePrefixRecognizerStageCode encoded budget) }
          { state :=
              some
                (finiteStateIndexOf descriptionDecoder.statesFinite
                  descriptionDecoder.start)
            tape :=
              BCRT (0 + budget + 1)
                encoded } :=
      TuringMachine.computesIn_to_computes hscanIn
    have hequiv :
        Tape.Equiv (Tape.input encoded)
          (BCRT (0 + budget + 1)
            encoded) :=
      Tape.Equiv.symm
        (budgetCheckerDescriptionRunnerTape_equiv_input
          (0 + budget + 1) encoded)
    rcases turingMachine_computes_of_tape_equiv hcomp hequiv with
      ⟨final', hcomp', hstate, _htape⟩
    have hrun :
        TuringMachine.Computes
          (BCRIM descriptionDecoder)
          { state :=
              some
                (finiteStateIndexOf descriptionDecoder.statesFinite
                  descriptionDecoder.start)
            tape :=
              BCRT (0 + budget + 1)
                encoded }
          { state :=
              some
                (finiteStateIndexOf descriptionDecoder.statesFinite
                  final'.state)
            tape := final'.tape } :=
      budgetCheckerDescriptionRunnerIndexedMachine_computes_run
        descriptionDecoder hcomp'
    have hhalt' :
        TuringMachine.Halted
          (BCRIM descriptionDecoder)
          { state :=
              some
                (finiteStateIndexOf descriptionDecoder.statesFinite
                  final'.state)
            tape := final'.tape } := by
      have hfinalState : final'.state = descriptionDecoder.halt := by
        simpa [TuringMachine.Halted, hstate] using hhalt
      simp [TuringMachine.Halted,
        budgetCheckerDescriptionRunnerIndexedMachine, hfinalState]
    have hrunnerFrom :
        TuringMachine.HaltsFrom
          (BCRIM descriptionDecoder)
          { state := none
            tape :=
              BCRT 0
                (CodePrefixRecognizerStageCode encoded budget) } :=
      TuringMachine.halts_from_of_computes
        (TuringMachine.computes_trans hscan hrun) hhalt'
    simpa [TuringMachine.HaltsOnInput, TuringMachine.initial,
      BCRIM,
      budgetCheckerDescriptionRunnerTape_nil_eq_input] using hrunnerFrom

/--
Finite-machine leaf for the bounded stage/fuel simulator search used by the
budget checker.
-/
theorem codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRunnerObligation_core
    (simulator : TuringMachine MachineCodeSymbol simulatorState) :
    CodePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRunnerObligation
      simulator := by
  rcases
      codePrefixStageSearchControllerBudgetCheckerBoundedSimulatorRawLoopObligation_core
        simulator with
    ⟨runnerState, runner, hrunner⟩
  refine ⟨runnerState, runner, ?_⟩
  intro encoded budget
  constructor
  · intro hhalt
    rcases
        (hrunner (CodePrefixRecognizerStageCode encoded budget)).mp
          hhalt with
      ⟨parsedBudget, parsedEncoded, checkedStage, fuel,
        htokens, hcheckedStage, hfuel, hsimulator⟩
    have hparsed :=
      codePrefixRecognizerStageCode_injective htokens.symm
    rcases hparsed with ⟨hbudget, hencoded⟩
    subst parsedBudget
    subst parsedEncoded
    exact ⟨checkedStage, fuel, hcheckedStage, hfuel, hsimulator⟩
  · intro htarget
    rcases htarget with
      ⟨checkedStage, fuel, hcheckedStage, hfuel, hsimulator⟩
    exact
      (hrunner (CodePrefixRecognizerStageCode encoded budget)).mpr
        ⟨budget, encoded, checkedStage, fuel, rfl,
          hcheckedStage, hfuel, hsimulator⟩


end Computability
end FoC
