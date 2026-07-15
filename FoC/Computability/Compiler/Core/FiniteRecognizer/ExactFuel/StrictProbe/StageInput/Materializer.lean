import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.HeaderInstaller

/-!
# Canonical exact-fuel stage-input materializer

Composition of the finite parser, empty writer, nonempty tail insertion, and
header installer into the canonical protected frame consumed by the strict
exact-fuel driver.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace InitialMaterializer

namespace FullMaterializerMachine

inductive Control {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount)) where
  | parse (control : StageFuelParser.Control stateCount)
  | emptyTurn
  | emptyWrite (control : Fin ((EmptyInputSuffix.suffix M).length + 1))
  | emptyHeaderTurn
  | emptyPrepend (control : PrependHeader.Control)
  | tailTurn
  | tail (control : NonemptyTailInitializer.Control)
  | baseTurn (headSymbol : MachineCodeSymbol)
  | baseRewind (headSymbol : MachineCodeSymbol) (control : SeparatorRewind.Control)
  | rawTurn (headSymbol : MachineCodeSymbol)
  | raw (headSymbol : MachineCodeSymbol) (control : RawTailLoopMachine.Control)
  | blockTurn (headSymbol : MachineCodeSymbol)
  | block (headSymbol : MachineCodeSymbol) (control : VariableBlockInsert.Control (NonemptyFixedPrefix.capacity M))
  | headerTurn
  | header (control : HeaderLeftInstaller.Control)
deriving DecidableEq

namespace Control
def baseRewindElems {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : List (Control M) :=
  MachineCodeSymbol.finite.elems.flatMap fun headSymbol =>
    SeparatorRewind.Control.finite.elems.map (Control.baseRewind headSymbol)
def rawElems {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : List (Control M) :=
  MachineCodeSymbol.finite.elems.flatMap fun headSymbol =>
    RawTailLoopMachine.Control.finite.elems.map (Control.raw headSymbol)
def blockElems {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : List (Control M) :=
  MachineCodeSymbol.finite.elems.flatMap fun headSymbol =>
    (VariableBlockInsert.Control.finite (NonemptyFixedPrefix.capacity M)).elems.map (Control.block headSymbol)
def elems {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount)) : List (Control M) :=
  List.append ((StageFuelParser.Control.finite stateCount).elems.map Control.parse)
    (List.append [.emptyTurn] (List.append ((Foundation.FiniteType.fin
          ((EmptyInputSuffix.suffix M).length + 1)).elems.map Control.emptyWrite)
        (List.append [.emptyHeaderTurn] (List.append (PrependHeader.Control.finite.elems.map
              Control.emptyPrepend) (List.append [.tailTurn] (List.append
                (NonemptyTailInitializer.Control.finite.elems.map Control.tail) (List.append
                  (MachineCodeSymbol.finite.elems.map Control.baseTurn) (List.append (baseRewindElems M) (List.append
                      (MachineCodeSymbol.finite.elems.map Control.rawTurn)
                      (List.append (rawElems M) (List.append (MachineCodeSymbol.finite.elems.map
                            Control.blockTurn) (List.append (blockElems M) (List.append [.headerTurn]
                              (HeaderLeftInstaller.Control.finite.elems.map Control.header))))))))))))))
def finite {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Foundation.FiniteType (Control M) where
  elems := elems M
  complete := by
    intro control
    cases control with
    | parse inner =>
        simp [elems, baseRewindElems, rawElems, blockElems]
        exact (StageFuelParser.Control.finite stateCount).complete inner
    | emptyTurn =>
        simp [elems, baseRewindElems, rawElems, blockElems]
    | emptyWrite inner =>
        simp [elems, baseRewindElems, rawElems, blockElems]
        exact (Foundation.FiniteType.fin ((EmptyInputSuffix.suffix M).length + 1)).complete inner
    | emptyHeaderTurn =>
        simp [elems, baseRewindElems, rawElems, blockElems]
    | emptyPrepend inner =>
        simp [elems, baseRewindElems, rawElems, blockElems]
        exact PrependHeader.Control.finite.complete inner
    | tailTurn =>
        simp [elems, baseRewindElems, rawElems, blockElems]
    | tail inner =>
        simp [elems, baseRewindElems, rawElems, blockElems]
        exact NonemptyTailInitializer.Control.finite.complete inner
    | baseTurn headSymbol =>
        simp [elems, baseRewindElems, rawElems, blockElems]
        exact MachineCodeSymbol.finite.complete headSymbol
    | baseRewind headSymbol inner =>
        simp [elems, baseRewindElems, rawElems, blockElems]
        exact ⟨MachineCodeSymbol.finite.complete headSymbol, SeparatorRewind.Control.finite.complete inner⟩
    | rawTurn headSymbol =>
        simp [elems, baseRewindElems, rawElems, blockElems]
        exact MachineCodeSymbol.finite.complete headSymbol
    | raw headSymbol inner =>
        simp [elems, baseRewindElems, rawElems, blockElems]
        exact ⟨MachineCodeSymbol.finite.complete headSymbol, RawTailLoopMachine.Control.finite.complete inner⟩
    | blockTurn headSymbol =>
        simp [elems, baseRewindElems, rawElems, blockElems]
        exact MachineCodeSymbol.finite.complete headSymbol
    | block headSymbol inner =>
        simp [elems, baseRewindElems, rawElems, blockElems]
        exact ⟨MachineCodeSymbol.finite.complete headSymbol, (VariableBlockInsert.Control.finite
              (NonemptyFixedPrefix.capacity M)).complete inner⟩
    | headerTurn =>
        simp [elems, baseRewindElems, rawElems, blockElems]
    | header inner =>
        simp [elems, baseRewindElems, rawElems, blockElems]
        exact HeaderLeftInstaller.Control.finite.complete inner
end Control
def transition {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    Control M -> Option MachineCodeSymbol -> Option (Option MachineCodeSymbol × Direction × Control M)
  | .parse (.gate _), some symbol =>
      some (some symbol, Direction.left, .tailTurn)
  | .parse (.gate _), none =>
      some (none, Direction.left, .emptyTurn)
  | .parse inner, cell =>
      match StageFuelParser.transition inner cell with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .parse target)
  | .emptyTurn, cell =>
      some (cell, Direction.right, .emptyWrite (FixedWordWriter.stateAt (EmptyInputSuffix.suffix M) 0 (by simp)))
  | .emptyWrite inner, cell =>
      if hhalt : inner = FixedWordWriter.stateAt (EmptyInputSuffix.suffix M)
            (EmptyInputSuffix.suffix M).length (by simp) then
        some (cell, Direction.left, .emptyHeaderTurn) else
        match FixedWordWriter.transition (EmptyInputSuffix.suffix M) inner cell with
        | none => none
        | some (write, direction, target) =>
            some (write, direction, .emptyWrite target)
  | .emptyHeaderTurn, cell =>
      some (cell, Direction.right, .emptyPrepend .start)
  | .emptyPrepend inner, cell =>
      match PrependHeader.transition inner cell with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .emptyPrepend target)
  | .tailTurn, cell =>
      some (cell, Direction.right, .tail .capture)
  | .tail (.halt headSymbol), cell =>
      some (cell, Direction.left, .baseTurn headSymbol)
  | .tail inner, cell =>
      match NonemptyTailInitializer.transition inner cell with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .tail target)
  | .baseTurn headSymbol, cell =>
      some (cell, Direction.right, .baseRewind headSymbol .start)
  | .baseRewind headSymbol .gate, cell =>
      some (cell, Direction.left, .rawTurn headSymbol)
  | .baseRewind headSymbol inner, cell =>
      match SeparatorRewind.transition inner cell with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .baseRewind headSymbol target)
  | .rawTurn headSymbol, cell =>
      some (cell, Direction.right, .raw headSymbol RawTailLoopMachine.machine.start)
  | .raw headSymbol .done, cell =>
      some (cell, Direction.left, .blockTurn headSymbol)
  | .raw headSymbol inner, cell =>
      match RawTailLoopMachine.transition inner cell with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .raw headSymbol target)
  | .blockTurn headSymbol, cell =>
      some (cell, Direction.right, .block headSymbol (.carry (NonemptyFixedPrefix.buffer M headSymbol)))
  | .block _ .halt, cell =>
      some (cell, Direction.left, .headerTurn)
  | .block headSymbol inner, cell =>
      match VariableBlockInsert.transition inner cell with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .block headSymbol target)
  | .headerTurn, cell =>
      some (cell, Direction.right, .header .start)
  | .header inner, cell =>
      match HeaderLeftInstaller.transition inner cell with
      | none => none
      | some (write, direction, target) =>
          some (write, direction, .header target)
def machine {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount)) :
    TuringMachine MachineCodeSymbol (Control M) where
  start := .parse (.fuel M.start)
  halt := .header .halt
  transition := transition M
  statesFinite := Control.finite M
def parseConfig {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (c : TuringMachine.Configuration MachineCodeSymbol (StageFuelParser.Control stateCount)) :
    TuringMachine.Configuration MachineCodeSymbol (Control M) where
  state := .parse c.state
  tape := c.tape
def emptyWriteConfig {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (c : TuringMachine.Configuration MachineCodeSymbol (Fin ((EmptyInputSuffix.suffix M).length + 1))) :
    TuringMachine.Configuration MachineCodeSymbol (Control M) where
  state := .emptyWrite c.state
  tape := c.tape
def emptyPrependConfig {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (c : TuringMachine.Configuration MachineCodeSymbol PrependHeader.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control M) where
  state := .emptyPrepend c.state
  tape := c.tape
def tailConfig {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (c : TuringMachine.Configuration MachineCodeSymbol NonemptyTailInitializer.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control M) where
  state := .tail c.state
  tape := c.tape
def baseRewindConfig {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol) (c : TuringMachine.Configuration MachineCodeSymbol
      SeparatorRewind.Control) : TuringMachine.Configuration MachineCodeSymbol (Control M) where
  state := .baseRewind headSymbol c.state
  tape := c.tape
def rawConfig {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol) (c : TuringMachine.Configuration MachineCodeSymbol RawTailLoopMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control M) where
  state := .raw headSymbol c.state
  tape := c.tape
def blockConfig {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol) (c : TuringMachine.Configuration MachineCodeSymbol
      (VariableBlockInsert.Control (NonemptyFixedPrefix.capacity M))) :
    TuringMachine.Configuration MachineCodeSymbol (Control M) where
  state := .block headSymbol c.state
  tape := c.tape
def headerConfig {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (c : TuringMachine.Configuration MachineCodeSymbol HeaderLeftInstaller.Control) :
    TuringMachine.Configuration MachineCodeSymbol (Control M) where
  state := .header c.state
  tape := c.tape
theorem parse_transition_of_eq_some {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (inner target : StageFuelParser.Control stateCount) (cell write : Option MachineCodeSymbol)
    (direction : Direction) (htransition : StageFuelParser.transition inner cell =
      some (write, direction, target)) : transition M (.parse inner) cell = some (write, direction, .parse target) := by
  cases inner with
  | fuel carriedState =>
      simp only [transition, htransition]
  | gate carriedState =>
      simp [StageFuelParser.transition] at htransition
theorem empty_write_transition_of_eq_some {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (inner target :
      Fin ((EmptyInputSuffix.suffix M).length + 1)) (cell write : Option MachineCodeSymbol)
    (direction : Direction) (htransition : FixedWordWriter.transition (EmptyInputSuffix.suffix M) inner cell =
        some (write, direction, target)) : transition M (.emptyWrite inner) cell =
      some (write, direction, .emptyWrite target) := by
  by_cases hhalt : inner = FixedWordWriter.stateAt (EmptyInputSuffix.suffix M)
        (EmptyInputSuffix.suffix M).length (by simp)
  · subst inner
    cases cell <;>
      simp [FixedWordWriter.transition, FixedWordWriter.stateAt] at htransition
  · simp only [transition, hhalt, ↓reduceDIte, htransition]
theorem empty_prepend_transition_of_eq_some {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (inner target : PrependHeader.Control) (cell write : Option MachineCodeSymbol)
    (direction : Direction) (htransition : PrependHeader.transition inner cell =
      some (write, direction, target)) : transition M (.emptyPrepend inner) cell =
      some (write, direction, .emptyPrepend target) := by
  simp only [transition, htransition]
theorem tail_transition_of_eq_some {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (inner target : NonemptyTailInitializer.Control) (cell write : Option MachineCodeSymbol)
    (direction : Direction) (htransition : NonemptyTailInitializer.transition inner cell =
      some (write, direction, target)) : transition M (.tail inner) cell = some (write, direction, .tail target) := by
  cases inner with
  | halt headSymbol =>
      simp [NonemptyTailInitializer.transition] at htransition
  | capture | seekEnd | writeDone | writeCaller =>
      simp only [transition, htransition]
theorem base_rewind_transition_of_eq_some {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (headSymbol : MachineCodeSymbol)
    (inner target : SeparatorRewind.Control) (cell write : Option MachineCodeSymbol)
    (direction : Direction) (htransition : SeparatorRewind.transition inner cell =
      some (write, direction, target)) : transition M (.baseRewind headSymbol inner) cell =
      some (write, direction, .baseRewind headSymbol target) := by
  cases inner with
  | gate =>
      simp [SeparatorRewind.transition] at htransition
  | start | scan =>
      simp only [transition, htransition]
theorem raw_transition_of_eq_some {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (headSymbol : MachineCodeSymbol)
    (inner target : RawTailLoopMachine.Control) (cell write : Option MachineCodeSymbol)
    (direction : Direction) (htransition : RawTailLoopMachine.transition inner cell =
      some (write, direction, target)) : transition M (.raw headSymbol inner) cell =
      some (write, direction, .raw headSymbol target) := by
  cases inner with
  | done =>
      simp [RawTailLoopMachine.transition] at htransition
  | loop | restart | finishReturn =>
      simp only [transition, htransition]
theorem block_transition_of_eq_some {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (headSymbol : MachineCodeSymbol)
    (inner target : VariableBlockInsert.Control (NonemptyFixedPrefix.capacity M))
    (cell write : Option MachineCodeSymbol) (direction : Direction)
    (htransition : VariableBlockInsert.transition inner cell =
      some (write, direction, target)) : transition M (.block headSymbol inner) cell =
      some (write, direction, .block headSymbol target) := by
  cases inner with
  | halt =>
      simp [VariableBlockInsert.transition] at htransition
  | carry buffer =>
      simp only [transition, htransition]
theorem header_transition_of_eq_some {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (inner target : HeaderLeftInstaller.Control) (cell write : Option MachineCodeSymbol)
    (direction : Direction) (htransition : HeaderLeftInstaller.transition inner cell =
      some (write, direction, target)) : transition M (.header inner) cell =
      some (write, direction, .header target) := by
  simp only [transition, htransition]
theorem step_of_transition_embedding {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    {innerState : Type} (N : TuringMachine MachineCodeSymbol innerState)
    (embedState : innerState -> Control M) (hsimulate : forall (inner target : innerState)
      (cell write : Option MachineCodeSymbol) (direction : Direction),
      N.transition inner cell = some (write, direction, target) ->
      transition M (embedState inner) cell = some (write, direction, embedState target))
    (c d : TuringMachine.Configuration MachineCodeSymbol innerState)
    (hstep : N.stepConfig c = some d) : (machine M).stepConfig
        { state := embedState c.state, tape := c.tape } = some { state := embedState d.state, tape := d.tape } := by
  cases c with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      unfold machine
      dsimp only at hstep ⊢
      cases htransition : N.transition inner (Tape.read tape) with
      | none =>
          rw [htransition] at hstep
          contradiction
      | some action =>
          rcases action with ⟨write, direction, target⟩
          rw [htransition] at hstep
          simp only at hstep
          rw [hsimulate inner target (Tape.read tape) write direction htransition]
          cases hstep
          rfl
theorem run_of_transition_embedding {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    {innerState : Type} (N : TuringMachine MachineCodeSymbol innerState)
    (embedState : innerState -> Control M) (hsimulate : forall (inner target : innerState)
      (cell write : Option MachineCodeSymbol) (direction : Direction),
      N.transition inner cell = some (write, direction, target) ->
      transition M (embedState inner) cell = some (write, direction, embedState target))
    (steps : Nat) (c d : TuringMachine.Configuration MachineCodeSymbol innerState)
    (hrun : N.runConfigExact? steps c = some d) : (machine M).runConfigExact? steps
        { state := embedState c.state, tape := c.tape } = some { state := embedState d.state, tape := d.tape } := by
  induction steps generalizing c d with
  | zero =>
      simp only [TuringMachine.runConfigExact?] at hrun ⊢
      cases hrun
      rfl
  | succ steps ih =>
      rw [TuringMachine.runConfigExact?] at hrun ⊢
      cases hstep : N.stepConfig c with
      | none =>
          rw [hstep] at hrun
          contradiction
      | some next =>
          rw [hstep] at hrun
          rw [step_of_transition_embedding M N embedState hsimulate c next hstep]
          simp only
          exact ih next d hrun
theorem parse_run_of_eq_some {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (steps : Nat)
    (c d : TuringMachine.Configuration MachineCodeSymbol (StageFuelParser.Control stateCount))
    (hrun : (StageFuelParser.machine M.start).runConfigExact? steps c = some d) :
    (machine M).runConfigExact? steps (parseConfig M c) = some (parseConfig M d) := by
  exact run_of_transition_embedding M (StageFuelParser.machine M.start) Control.parse (by
      intro inner target cell write direction htransition
      exact parse_transition_of_eq_some M inner target cell write direction htransition) steps c d hrun
theorem empty_write_run_of_eq_some {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (steps : Nat)
    (c d : TuringMachine.Configuration MachineCodeSymbol
      (Fin ((EmptyInputSuffix.suffix M).length + 1))) (hrun : (FixedWordWriter.machine
      (EmptyInputSuffix.suffix M)).runConfigExact? steps c = some d) :
    (machine M).runConfigExact? steps (emptyWriteConfig M c) = some (emptyWriteConfig M d) := by
  exact run_of_transition_embedding M (FixedWordWriter.machine (EmptyInputSuffix.suffix M)) Control.emptyWrite (by
      intro inner target cell write direction htransition
      exact empty_write_transition_of_eq_some M inner target cell write direction htransition) steps c d hrun
theorem empty_prepend_run_of_eq_some {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (steps : Nat)
    (c d : TuringMachine.Configuration MachineCodeSymbol PrependHeader.Control)
    (hrun : PrependHeader.machine.runConfigExact? steps c = some d) :
    (machine M).runConfigExact? steps (emptyPrependConfig M c) = some (emptyPrependConfig M d) := by
  exact run_of_transition_embedding M PrependHeader.machine Control.emptyPrepend (by
      intro inner target cell write direction htransition
      exact empty_prepend_transition_of_eq_some M inner target cell write direction htransition) steps c d hrun
theorem tail_run_of_eq_some {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (steps : Nat)
    (c d : TuringMachine.Configuration MachineCodeSymbol NonemptyTailInitializer.Control)
    (hrun : NonemptyTailInitializer.machine.runConfigExact? steps c = some d) :
    (machine M).runConfigExact? steps (tailConfig M c) = some (tailConfig M d) := by
  exact run_of_transition_embedding M NonemptyTailInitializer.machine Control.tail (by
      intro inner target cell write direction htransition
      exact tail_transition_of_eq_some M inner target cell write direction htransition) steps c d hrun
theorem base_rewind_run_of_eq_some {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (headSymbol : MachineCodeSymbol)
    (steps : Nat) (c d : TuringMachine.Configuration MachineCodeSymbol SeparatorRewind.Control)
    (hrun : SeparatorRewind.machine.runConfigExact? steps c = some d) :
    (machine M).runConfigExact? steps (baseRewindConfig M headSymbol c) = some (baseRewindConfig M headSymbol d) := by
  exact run_of_transition_embedding M SeparatorRewind.machine (Control.baseRewind headSymbol) (by
      intro inner target cell write direction htransition
      exact base_rewind_transition_of_eq_some M headSymbol inner target cell write direction htransition) steps c d hrun
theorem raw_run_of_eq_some {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (headSymbol : MachineCodeSymbol)
    (steps : Nat) (c d : TuringMachine.Configuration MachineCodeSymbol
      RawTailLoopMachine.Control) (hrun : RawTailLoopMachine.machine.runConfigExact?
      steps c = some d) : (machine M).runConfigExact? steps (rawConfig M headSymbol c) =
      some (rawConfig M headSymbol d) := by
  exact run_of_transition_embedding M RawTailLoopMachine.machine (Control.raw headSymbol) (by
      intro inner target cell write direction htransition
      exact raw_transition_of_eq_some M headSymbol inner target cell write direction htransition) steps c d hrun
theorem block_run_of_eq_some {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (headSymbol : MachineCodeSymbol)
    (steps : Nat) (c d : TuringMachine.Configuration MachineCodeSymbol
      (VariableBlockInsert.Control (NonemptyFixedPrefix.capacity M)))
    (hrun : (VariableBlockInsert.machine (NonemptyFixedPrefix.capacity M)
      (NonemptyFixedPrefix.buffer M headSymbol)).runConfigExact? steps c = some d) :
    (machine M).runConfigExact? steps (blockConfig M headSymbol c) = some (blockConfig M headSymbol d) := by
  exact run_of_transition_embedding M (VariableBlockInsert.machine
      (NonemptyFixedPrefix.capacity M) (NonemptyFixedPrefix.buffer M headSymbol)) (Control.block headSymbol) (by
      intro inner target cell write direction htransition
      exact block_transition_of_eq_some M headSymbol inner target cell write direction htransition) steps c d hrun
theorem header_run_of_eq_some {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (steps : Nat)
    (c d : TuringMachine.Configuration MachineCodeSymbol HeaderLeftInstaller.Control)
    (hrun : HeaderLeftInstaller.machine.runConfigExact? steps c = some d) :
    (machine M).runConfigExact? steps (headerConfig M c) = some (headerConfig M d) := by
  exact run_of_transition_embedding M HeaderLeftInstaller.machine Control.header (by
      intro inner target cell write direction htransition
      exact header_transition_of_eq_some M inner target cell write direction htransition) steps c d hrun
theorem parse_nonempty_bridge_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (fuel : Nat)
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    (machine M).runConfigExact? 2 (parseConfig M (StageFuelParser.gateConfig M.start fuel
            (headSymbol :: rest))) = some (tailConfig M (NonemptyTailInitializer.sourceConfig
            (MachineDescription.encodeNat fuel).reverse headSymbol rest)) := by
  have hnonempty : (MachineDescription.encodeNat fuel).reverse ≠ [] := by
    rw [OneCellMachine.encodeNat_eq_ticks_done]
    simp
  cases hleft : (MachineDescription.encodeNat fuel).reverse with
  | nil => contradiction
  | cons leftHead leftRest =>
      cases rest <;>
        simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig, machine, transition, parseConfig, tailConfig,
          StageFuelParser.gateConfig, StageFuelParser.config, NonemptyTailInitializer.sourceConfig,
          SerializedShift.cursorTape, Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, hleft]
theorem parse_empty_bridge_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (fuel : Nat) :
    (machine M).runConfigExact? 2 (parseConfig M (StageFuelParser.gateConfig M.start fuel [])) =
      some (emptyWriteConfig M (FixedWordWriter.config (EmptyInputSuffix.suffix M) 0 (by simp)
            (MachineDescription.encodeNat fuel).reverse)) := by
  have hnonempty : (MachineDescription.encodeNat fuel).reverse ≠ [] := by
    rw [OneCellMachine.encodeNat_eq_ticks_done]
    simp
  cases hleft : (MachineDescription.encodeNat fuel).reverse with
  | nil => contradiction
  | cons leftHead leftRest =>
      simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig, machine, transition, parseConfig, emptyWriteConfig,
        StageFuelParser.gateConfig, StageFuelParser.config, FixedWordWriter.config, FixedWordWriter.stateAt,
        SerializedShift.cursorTape, Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, hleft]
theorem empty_header_bridge_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (wordRev : Word MachineCodeSymbol)
    (hnonempty : wordRev ≠ []) : (machine M).runConfigExact? 2 (emptyWriteConfig M
          (FixedWordWriter.config (EmptyInputSuffix.suffix M)
            (EmptyInputSuffix.suffix M).length (by simp) wordRev)) = some (emptyPrependConfig M
          (PrependHeader.startConfig wordRev)) := by
  cases wordRev with
  | nil => contradiction
  | cons first rest =>
      cases rest <;>
        simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
          machine, transition, emptyWriteConfig, emptyPrependConfig, FixedWordWriter.config, FixedWordWriter.stateAt,
          PrependHeader.startConfig, PrependHeader.farRightTape, SerializedShift.cursorTape, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, Tape.moveRight]
theorem tail_base_bridge_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (headSymbol : MachineCodeSymbol)
    (leftRev restRev : Word MachineCodeSymbol) : (machine M).runConfigExact? 2 (tailConfig M
          (NonemptyTailInitializer.haltConfig headSymbol leftRev restRev)) = some
        (baseRewindConfig M headSymbol (SeparatorRewind.startConfigCells
            (NonemptyTailInitializer.rewindLeftContext leftRev restRev)
            [Frame.callerTag, MachineCodeSymbol.done])) := by
  cases leftRev <;> cases restRev <;> rfl
theorem base_raw_bridge_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (headSymbol : MachineCodeSymbol)
    (remainingRev fuelRev : Word MachineCodeSymbol) : (machine M).runConfigExact? 2
        (baseRewindConfig M headSymbol (SeparatorRewind.gateConfigCells
            (NonemptyTailInitializer.rewindLeftContext fuelRev remainingRev)
            [MachineCodeSymbol.done, Frame.callerTag])) = some (rawConfig M headSymbol
          (RawTailLoopMachine.gateConfig remainingRev [] fuelRev)) := by
  rfl
def blockPaddedSourceConfig {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (headSymbol : MachineCodeSymbol)
    (rest fuelRev : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol (Control M) where
  state := .block headSymbol (.carry (NonemptyFixedPrefix.buffer M headSymbol))
  tape := (RawTailLoopMachine.doneConfig rest fuelRev).tape
theorem raw_block_bridge_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (headSymbol : MachineCodeSymbol)
    (rest fuelRev : Word MachineCodeSymbol) : (machine M).runConfigExact? 2
        (rawConfig M headSymbol (RawTailLoopMachine.doneConfig rest fuelRev)) =
      some (blockPaddedSourceConfig M headSymbol rest fuelRev) := by
  have hnonempty := NonemptyRightRegion.region_ne_nil rest
  cases hregion : NonemptyRightRegion.region rest with
  | nil => contradiction
  | cons first regionRest =>
      cases regionRest <;>
        simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
          machine, transition, rawConfig, blockPaddedSourceConfig,
          RawTailLoopMachine.doneConfig, SeparatorRewind.gateTapeCells, Tape.read, Tape.write,
          Tape.move, Tape.moveLeft, Tape.moveRight, hregion]
theorem block_header_bridge_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (headSymbol : MachineCodeSymbol)
    (wordRev fuelRev : Word MachineCodeSymbol) (hnonempty : wordRev ≠ []) :
    (machine M).runConfigExact? 2 (blockConfig M headSymbol
          (VariableBlockInsert.haltConfig wordRev (none :: none :: fuelRev.map some))) = some
        (headerConfig M (HeaderLeftInstaller.sourceConfig wordRev fuelRev)) := by
  cases wordRev with
  | nil => contradiction
  | cons first rest =>
      cases rest <;> cases fuelRev <;>
        simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
          machine, transition, blockConfig, headerConfig, VariableBlockInsert.haltConfig,
          HeaderLeftInstaller.sourceConfig, Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]
theorem exactRun_trans {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (first second : Nat) (source middle target : TuringMachine.Configuration MachineCodeSymbol (Control M))
    (hfirst : (machine M).runConfigExact? first source = some middle)
    (hsecond : (machine M).runConfigExact? second middle = some target) :
    (machine M).runConfigExact? (first + second) source = some target := by
  rw [ExactRun.append]
  rw [hfirst]
  exact hsecond
def sourceConfig {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat) (input : Word MachineCodeSymbol) : TuringMachine.Configuration MachineCodeSymbol (Control M) :=
  parseConfig M (StageFuelParser.sourceConfig M.start fuel input)
theorem sourceConfig_eq_initial {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat) (input : Word MachineCodeSymbol) : sourceConfig M fuel input =
      TuringMachine.initial (machine M) (MachineDescription.encodeNatAppend fuel input) := by
  unfold sourceConfig
  rw [StageFuelParser.sourceConfig_eq_initial]
  rfl
def nonemptyHaltTape {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat) (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  HeaderLeftInstaller.haltTape (MachineDescription.encodeNat fuel)
    (List.append (NonemptyFixedPrefix.fixedPrefix M headSymbol) (NonemptyRightRegion.region rest))
theorem nonempty_run_to_padded_endpoint {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (fuel : Nat)
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) : exists (steps : Nat)
        (endpoint : TuringMachine.Configuration MachineCodeSymbol (Control M)),
      (machine M).runConfigExact? steps (sourceConfig M fuel (headSymbol :: rest)) =
        some endpoint ∧ endpoint.state = .header .halt ∧
      Tape.Equiv (nonemptyHaltTape M fuel headSymbol rest) endpoint.tape ∧
      Tape.normalizedOutput endpoint.tape = Frame.protectedWord (Layout.initial M (headSymbol :: rest) fuel) [] := by
  let fuelRev := (MachineDescription.encodeNat fuel).reverse
  have hparse : (machine M).runConfigExact? (fuel + 1) (sourceConfig M fuel (headSymbol :: rest)) = some (parseConfig M
            (StageFuelParser.gateConfig M.start fuel (headSymbol :: rest))) := by
    exact parse_run_of_eq_some M (fuel + 1) (StageFuelParser.sourceConfig M.start fuel
        (headSymbol :: rest)) (StageFuelParser.gateConfig M.start fuel (headSymbol :: rest))
      (StageFuelParser.run_exact M.start fuel (headSymbol :: rest))
  have hparseBridge :=
    parse_nonempty_bridge_exact M fuel headSymbol rest
  have htail : (machine M).runConfigExact? (rest.length + 4) (tailConfig M
            (NonemptyTailInitializer.sourceConfig fuelRev headSymbol rest)) = some (tailConfig M
            (NonemptyTailInitializer.haltConfig headSymbol fuelRev rest.reverse)) := by
    exact tail_run_of_eq_some M (rest.length + 4) (NonemptyTailInitializer.sourceConfig
        fuelRev headSymbol rest) (NonemptyTailInitializer.haltConfig
        headSymbol fuelRev rest.reverse) (NonemptyTailInitializer.run_exact fuelRev headSymbol rest)
  have htailBridge :=
    tail_base_bridge_exact M headSymbol fuelRev rest.reverse
  have hbase : (machine M).runConfigExact? 4 (baseRewindConfig M headSymbol
            (SeparatorRewind.startConfigCells (NonemptyTailInitializer.rewindLeftContext
                fuelRev rest.reverse) [Frame.callerTag, MachineCodeSymbol.done])) = some
          (baseRewindConfig M headSymbol (SeparatorRewind.gateConfigCells
              (NonemptyTailInitializer.rewindLeftContext fuelRev rest.reverse)
              [MachineCodeSymbol.done, Frame.callerTag])) := by
    exact base_rewind_run_of_eq_some M headSymbol 4 _ _
      (NonemptyTailInitializer.separator_return_exact fuelRev rest.reverse)
  have hbaseBridge :=
    base_raw_bridge_exact M headSymbol rest.reverse fuelRev
  rcases RawTailLoopMachine.run_to_done_equiv rest.reverse [] fuelRev with
    ⟨rawSteps, rawEndpoint, hrawInner, hrawState, hrawTape⟩
  have hraw : (machine M).runConfigExact? rawSteps (rawConfig M headSymbol
            (RawTailLoopMachine.gateConfig rest.reverse [] fuelRev)) = some (rawConfig M headSymbol rawEndpoint) := by
    exact raw_run_of_eq_some M headSymbol rawSteps _ _ hrawInner
  have hrestProcessed : List.append rest.reverse.reverse [] = rest := by
    simp
  rw [hrestProcessed] at hrawState hrawTape
  rcases TuringExactEquiv.runConfigExact?_some_of_equiv
      (clean := rawConfig M headSymbol (RawTailLoopMachine.doneConfig rest fuelRev))
      (padded := rawConfig M headSymbol rawEndpoint) (cleanFinal :=
        blockPaddedSourceConfig M headSymbol rest fuelRev) (machine M) 2 (by
        change Control.raw (M := M) headSymbol (RawTailLoopMachine.doneConfig rest fuelRev).state =
            Control.raw (M := M) headSymbol rawEndpoint.state
        exact congrArg (Control.raw (M := M) headSymbol) hrawState) hrawTape
      (raw_block_bridge_exact M headSymbol rest fuelRev) with
    ⟨actualBlockReady, hactualBlockBridge, hblockReadyState, hblockReadyTape⟩
  have hblockInputState : (blockConfig M headSymbol (NonemptyFixedPrefix.sourceConfig
          M headSymbol rest fuelRev)).state = actualBlockReady.state := by
    exact hblockReadyState
  have hblockInputTape : Tape.Equiv (blockConfig M headSymbol (NonemptyFixedPrefix.sourceConfig
            M headSymbol rest fuelRev)).tape actualBlockReady.tape := by
    exact Tape.Equiv.trans (Tape.Equiv.symm (NonemptyFixedPrefix.tail_done_equiv_source
          M headSymbol rest fuelRev)) hblockReadyTape
  have hblockClean : (machine M).runConfigExact?
          (NonemptyFixedPrefix.runSteps M headSymbol rest) (blockConfig M headSymbol
            (NonemptyFixedPrefix.sourceConfig M headSymbol rest fuelRev)) = some
          (blockConfig M headSymbol (NonemptyFixedPrefix.endpointConfig M headSymbol rest fuelRev)) := by
    exact block_run_of_eq_some M headSymbol (NonemptyFixedPrefix.runSteps M headSymbol rest) _ _
      (NonemptyFixedPrefix.run_exact M headSymbol rest fuelRev)
  rcases TuringExactEquiv.runConfigExact?_some_of_equiv
      (clean := blockConfig M headSymbol (NonemptyFixedPrefix.sourceConfig
          M headSymbol rest fuelRev)) (padded := actualBlockReady)
      (cleanFinal := blockConfig M headSymbol (NonemptyFixedPrefix.endpointConfig
          M headSymbol rest fuelRev)) (machine M) (NonemptyFixedPrefix.runSteps M headSymbol rest)
      hblockInputState hblockInputTape hblockClean with
    ⟨actualBlockEndpoint, hactualBlock, hblockEndpointState, hblockEndpointTape⟩
  let insertedRev :=
    VariableBlockInsert.finalLeftRev (NonemptyFixedPrefix.buffer M headSymbol) [] (NonemptyRightRegion.region rest)
  have hinsertedNonempty : insertedRev ≠ [] := by
    intro hnil
    have hword :=
      NonemptyFixedPrefix.endpoint_word_reverse M headSymbol rest
    change insertedRev.reverse = _ at hword
    rw [hnil] at hword
    have hright : List.append (NonemptyFixedPrefix.fixedPrefix M headSymbol)
          (NonemptyRightRegion.region rest) ≠ [] := by
      intro hempty
      exact NonemptyFixedPrefix.fixedPrefix_ne_nil M headSymbol (List.append_eq_nil_iff.mp hempty).1
    exact hright hword.symm
  have hblockBridgeClean : (machine M).runConfigExact? 2 (blockConfig M headSymbol
            (NonemptyFixedPrefix.endpointConfig M headSymbol rest fuelRev)) = some
          (headerConfig M (HeaderLeftInstaller.sourceConfig insertedRev fuelRev)) := by
    exact block_header_bridge_exact M headSymbol insertedRev fuelRev hinsertedNonempty
  rcases TuringExactEquiv.runConfigExact?_some_of_equiv
      (clean := blockConfig M headSymbol (NonemptyFixedPrefix.endpointConfig
          M headSymbol rest fuelRev)) (padded := actualBlockEndpoint)
      (cleanFinal := headerConfig M (HeaderLeftInstaller.sourceConfig insertedRev fuelRev))
      (machine M) 2 hblockEndpointState hblockEndpointTape hblockBridgeClean with
    ⟨actualHeaderReady, hactualHeaderBridge, hheaderReadyState, hheaderReadyTape⟩
  have hheaderClean : (machine M).runConfigExact? (HeaderLeftInstaller.runSteps fuel insertedRev) (headerConfig M
            (HeaderLeftInstaller.sourceConfig insertedRev fuelRev)) = some (headerConfig M
            (HeaderLeftInstaller.haltConfig (MachineDescription.encodeNat fuel) insertedRev.reverse)) := by
    exact header_run_of_eq_some M (HeaderLeftInstaller.runSteps fuel insertedRev) _ _
      (HeaderLeftInstaller.run_exact fuel insertedRev)
  rcases TuringExactEquiv.runConfigExact?_some_of_equiv (clean := headerConfig M
        (HeaderLeftInstaller.sourceConfig insertedRev fuelRev)) (padded := actualHeaderReady)
      (cleanFinal := headerConfig M (HeaderLeftInstaller.haltConfig
          (MachineDescription.encodeNat fuel) insertedRev.reverse)) (machine M)
      (HeaderLeftInstaller.runSteps fuel insertedRev) hheaderReadyState hheaderReadyTape hheaderClean with
    ⟨actualEndpoint, hactualHeader, hfinalState, hfinalTape⟩
  have hprefix0 := exactRun_trans M _ _ _ _ _ hparse hparseBridge
  have hprefix1 := exactRun_trans M _ _ _ _ _ hprefix0 htail
  have hprefix2 := exactRun_trans M _ _ _ _ _ hprefix1 htailBridge
  have hprefix3 := exactRun_trans M _ _ _ _ _ hprefix2 hbase
  have hprefix4 := exactRun_trans M _ _ _ _ _ hprefix3 hbaseBridge
  have hprefix5 := exactRun_trans M _ _ _ _ _ hprefix4 hraw
  have hprefix6 := exactRun_trans M _ _ _ _ _ hprefix5 hactualBlockBridge
  have hprefix7 := exactRun_trans M _ _ _ _ _ hprefix6 hactualBlock
  have hprefix8 := exactRun_trans M _ _ _ _ _ hprefix7 hactualHeaderBridge
  have hfull := exactRun_trans M _ _ _ _ _ hprefix8 hactualHeader
  refine ⟨_, actualEndpoint, hfull, ?_, ?_, ?_⟩
  · exact hfinalState.symm
  · have hinserted :=
      NonemptyFixedPrefix.endpoint_word_reverse M headSymbol rest
    change insertedRev.reverse = _ at hinserted
    rw [hinserted] at hfinalTape
    exact hfinalTape
  · have hcleanOutput : Tape.normalizedOutput (HeaderLeftInstaller.haltConfig
              (MachineDescription.encodeNat fuel) insertedRev.reverse).tape =
          Frame.protectedWord (Layout.initial M (headSymbol :: rest) fuel) [] := by
      have hnorm := HeaderLeftInstaller.halt_normalizedOutput
        (MachineDescription.encodeNat fuel) insertedRev.reverse (by
          intro hnil
          rw [OneCellMachine.encodeNat_eq_ticks_done] at hnil
          have htail := (List.append_eq_nil_iff.mp hnil).2
          cases htail)
      have hinserted :=
        NonemptyFixedPrefix.endpoint_word_reverse M headSymbol rest
      change insertedRev.reverse = _ at hinserted
      rw [hinserted] at hnorm
      rw [hinserted]
      simpa [HeaderLeftInstaller.haltConfig] using hnorm.trans
          (NonemptyFixedPrefix.body_eq_initial_protectedWord M fuel headSymbol rest)
    have hequivOutput := Tape.Equiv.normalizedOutput_eq hfinalTape
    exact hequivOutput.symm.trans hcleanOutput
def emptyHaltTape {stateCount : Nat} (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat) : Tape MachineCodeSymbol :=
  PrependHeader.gateTape (EmptyInputSuffix.body M fuel)
theorem empty_run_to_padded_endpoint {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount)) (fuel : Nat) : exists (steps : Nat)
        (endpoint : TuringMachine.Configuration MachineCodeSymbol (Control M)),
      (machine M).runConfigExact? steps (sourceConfig M fuel []) = some endpoint ∧
      endpoint.state = .emptyPrepend .gate ∧ endpoint.tape = emptyHaltTape M fuel ∧
      Tape.normalizedOutput endpoint.tape = Frame.protectedWord
          (Layout.initial M ([] : Word MachineCodeSymbol) fuel) [] := by
  let fuelRev := (MachineDescription.encodeNat fuel).reverse
  let writerRev :=
    List.append (EmptyInputSuffix.suffix M).reverse fuelRev
  have hparse : (machine M).runConfigExact? (fuel + 1) (sourceConfig M fuel []) = some
          (parseConfig M (StageFuelParser.gateConfig M.start fuel [])) := by
    exact parse_run_of_eq_some M (fuel + 1) (StageFuelParser.sourceConfig M.start fuel [])
      (StageFuelParser.gateConfig M.start fuel []) (StageFuelParser.run_exact M.start fuel [])
  have hparseBridge := parse_empty_bridge_exact M fuel
  have hwriter : (machine M).runConfigExact? (EmptyInputSuffix.suffix M).length
          (emptyWriteConfig M (FixedWordWriter.config
              (EmptyInputSuffix.suffix M) 0 (by simp) fuelRev)) = some (emptyWriteConfig M
            (FixedWordWriter.config (EmptyInputSuffix.suffix M)
              (EmptyInputSuffix.suffix M).length (by simp) writerRev)) := by
    exact empty_write_run_of_eq_some M (EmptyInputSuffix.suffix M).length _ _
      (FixedWordWriter.run_exact (EmptyInputSuffix.suffix M) fuelRev)
  have hwriterNonempty : writerRev ≠ [] := by
    intro hnil
    have hparts := List.append_eq_nil_iff.mp hnil
    have hfuel : fuelRev ≠ [] := by
      unfold fuelRev
      rw [OneCellMachine.encodeNat_eq_ticks_done]
      simp
    exact hfuel hparts.2
  have hwriterBridge :=
    empty_header_bridge_exact M writerRev hwriterNonempty
  have hprepend : (machine M).runConfigExact? (writerRev.length + 2) (emptyPrependConfig M
            (PrependHeader.startConfig writerRev)) = some (emptyPrependConfig M
            (PrependHeader.gateConfig writerRev.reverse)) := by
    exact empty_prepend_run_of_eq_some M (writerRev.length + 2) _ _ (PrependHeader.run_exact writerRev)
  have hprefix0 := exactRun_trans M _ _ _ _ _ hparse hparseBridge
  have hprefix1 := exactRun_trans M _ _ _ _ _ hprefix0 hwriter
  have hprefix2 := exactRun_trans M _ _ _ _ _ hprefix1 hwriterBridge
  have hfull := exactRun_trans M _ _ _ _ _ hprefix2 hprepend
  have hwriterShape : writerRev = (EmptyInputSuffix.body M fuel).reverse := by
    exact EmptyInputSuffix.writer_leftRev_eq_body_reverse M fuel
  refine ⟨_, emptyPrependConfig M (PrependHeader.gateConfig writerRev.reverse), hfull, rfl, ?_, ?_⟩
  · change PrependHeader.gateTape writerRev.reverse = _
    rw [hwriterShape]
    simp [emptyHaltTape]
  · have hgate :=
      PrependHeader.gateTape_normalizedOutput writerRev.reverse
    change Tape.normalizedOutput (PrependHeader.gateTape writerRev.reverse) = _
    rw [hgate]
    rw [hwriterShape]
    simp only [List.reverse_reverse]
    rw [EmptyInputSuffix.body_eq_initial_protected_tail]
    rfl
end FullMaterializerMachine

end InitialMaterializer
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
