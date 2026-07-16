import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.FinalGate.Integration

namespace FoC
namespace Computability

open Languages

namespace Section53NoMatchFinalGate

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open Section53UniformInterpreterOneStep
open Section53UniformInterpreterOneStep.RuntimeKeySingleKeyRepair
open Section53LoopRestagingAudit
open Section53StackIteration
open Section53FinalGateMaterializer

/-!
**All-miss final-gate builders.** The machine locates the halt field through
the structured stack/context scanners and replaces the two cells before that
field by a double-transition sentinel. Serialized transition rows and encoded
tape contexts cannot contain that pair, so front-to-back cleanup recognizes it
without storing the unbounded halt value in finite control.
-/

namespace DoubleTransitionMarker

inductive Control where
  | enter
  | markRight
  | markLeft
  | ready
  | halt
deriving DecidableEq

namespace Control

def elems : List Control := [.enter, .markRight, .markLeft, .ready, .halt]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control <;> simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .enter, read => some (read, Direction.left, .markRight)
  | .markRight, _ =>
      some (some MachineCodeSymbol.transition, Direction.left, .markLeft)
  | .markLeft, _ =>
      some (some MachineCodeSymbol.transition, Direction.right, .ready)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .enter
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def sourceConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (firstBefore secondBefore : MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .enter
  tape := SerializedShift.cursorTape
    (secondBefore :: firstBefore :: baseLeftRev)
    (MachineDescription.encodeNatAppend haltState suffix)

def targetConfig
    (baseLeftRev : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .ready
  tape := Tape.move Direction.right
    (SerializedShift.cursorTape baseLeftRev
      (MachineCodeSymbol.transition :: MachineCodeSymbol.transition ::
        MachineDescription.encodeNatAppend haltState suffix))

theorem run_exact
    (baseLeftRev : Word MachineCodeSymbol)
    (firstBefore secondBefore : MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? 3
        (sourceConfig baseLeftRev firstBefore secondBefore haltState suffix) =
      some (targetConfig baseLeftRev haltState suffix) := by
  cases baseLeftRev <;> cases haltState <;> cases suffix <;> rfl
  done

end DoubleTransitionMarker

namespace CurrentBuilder

inductive Control where
  | start
  | scanState
  | writeBlank
  | writeSeparator
  | writeDestination
  | eraseGap
  | checkTransition
  | markHalt
  | erasePendingTransition
  | crossChecked
  | returnChecked
  | rewindGap (token : Bool)
  | ready (token : Bool)
  | halt
deriving DecidableEq

namespace Control

def elems : List Control :=
  [.start, .scanState, .writeBlank, .writeSeparator, .writeDestination,
   .eraseGap, .checkTransition, .markHalt, .erasePendingTransition,
   .crossChecked, .returnChecked, .rewindGap false, .rewindGap true,
   .ready false, .ready true, .halt]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | rewindGap token => cases token <;> simp [elems]
    | ready token => cases token <;> simp [elems]
    | _ => simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .start, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.right, .scanState)
  | .scanState, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .scanState)
  | .scanState, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .writeBlank)
  | .writeBlank, _ =>
      some (some MachineCodeSymbol.blank, Direction.right, .writeSeparator)
  | .writeSeparator, _ =>
      some (some MachineCodeSymbol.transition, Direction.right,
        .writeDestination)
  | .writeDestination, _ =>
      some (some MachineCodeSymbol.header, Direction.right, .eraseGap)
  | .eraseGap, some MachineCodeSymbol.transition =>
      some (some MachineCodeSymbol.transition, Direction.right,
        .checkTransition)
  | .eraseGap, some _ =>
      some (some MachineCodeSymbol.blank, Direction.right, .eraseGap)
  | .checkTransition, some MachineCodeSymbol.transition =>
      some (some MachineCodeSymbol.blank, Direction.right, .markHalt)
  | .checkTransition, some symbol =>
      some (some symbol, Direction.left,
        .erasePendingTransition)
  | .markHalt, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.moveRight, Direction.left,
        .rewindGap false)
  | .markHalt, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.moveRight, Direction.left,
        .rewindGap true)
  | .erasePendingTransition, _ =>
      some (some MachineCodeSymbol.blank, Direction.right, .crossChecked)
  | .crossChecked, read => some (read, Direction.left, .returnChecked)
  | .returnChecked, read => some (read, Direction.right, .eraseGap)
  | .rewindGap token, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.right, .ready token)
  | .rewindGap token, some symbol =>
      some (some symbol, Direction.left, .rewindGap token)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .start
  halt := .halt
  transition := transition
  statesFinite := Control.finite

/-- No adjacent pair of `transition` tokens occurs in `symbols`. -/
def NoDoubleTransition (symbols : Word MachineCodeSymbol) : Prop :=
  forall (left tail : Word MachineCodeSymbol),
    symbols = List.append left
      (MachineCodeSymbol.transition :: MachineCodeSymbol.transition :: tail) ->
      False

def sourceWord
    (currentState : Nat)
    (queryRead firstJunk secondJunk : MachineCodeSymbol)
    (gap : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    MachineDescription.encodeNatAppend currentState
      (queryRead :: firstJunk :: secondJunk ::
        List.append gap
          (MachineCodeSymbol.transition :: MachineCodeSymbol.transition ::
            MachineDescription.encodeNatAppend haltState suffix))

def sourceConfig
    (currentState : Nat)
    (queryRead firstJunk secondJunk : MachineCodeSymbol)
    (gap : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .start
  tape := Tape.input
    (sourceWord currentState queryRead firstJunk secondJunk gap haltState
      suffix)

def cleanedGap : Word MachineCodeSymbol -> Word MachineCodeSymbol
  | [] => [MachineCodeSymbol.transition, MachineCodeSymbol.blank]
  | _ :: rest => MachineCodeSymbol.blank :: cleanedGap rest

def targetConfig
    (currentState : Nat)
    (gap : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .ready (Section53FinalGateMaterializer.firstToken haltState)
  tape := Section53FinalGateMaterializer.HaltCopier.sourceConfig
    (Section53FinalGateMaterializer.PrefixBuilder.comparatorPrefix
      currentState)
    (cleanedGap gap) haltState suffix |>.tape

theorem runConfigExact_trans
    {first second : Nat}
    {source middle target :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (hfirst : machine.runConfigExact? first source = some middle)
    (hsecond : machine.runConfigExact? second middle = some target) :
    machine.runConfigExact? (first + second) source = some target := by
  apply TuringMachine.runConfigExact?_eq_some_iff_computesIn.mpr
  exact TuringMachine.computesIn_trans
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hfirst)
    (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp hsecond)
  done

def builtLeftRev (currentState : Nat) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    (Section53FinalGateMaterializer.PrefixBuilder.comparatorPrefix
      currentState).reverse

def prefixTargetConfig
    (currentState : Nat)
    (gapAndTail : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .eraseGap
  tape := SerializedShift.cursorTape (builtLeftRev currentState) gapAndTail

theorem step_start
    (rest : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .start
          tape := SerializedShift.cursorTape []
            (MachineCodeSymbol.header :: rest) } =
      some
        { state := .scanState
          tape := SerializedShift.cursorTape
            [MachineCodeSymbol.header] rest } := by
  cases rest <;> rfl
  done

theorem step_scan_tick
    (leftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .scanState
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.tick :: rest) } =
      some
        { state := .scanState
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.tick :: leftRev) rest } := by
  cases rest <;> rfl
  done

theorem step_scan_done
    (leftRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .scanState
          tape := SerializedShift.cursorTape leftRev
            (MachineCodeSymbol.done :: rest) } =
      some
        { state := .writeBlank
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.done :: leftRev) rest } := by
  cases rest <;> rfl
  done

theorem scanNat_run_exact
    (value : Nat)
    (baseLeftRev rest : Word MachineCodeSymbol) :
    machine.runConfigExact? (value + 1)
        { state := .scanState
          tape := SerializedShift.cursorTape baseLeftRev
            (MachineDescription.encodeNatAppend value rest) } =
      some
        { state := .writeBlank
          tape := SerializedShift.cursorTape
            (List.append (MachineDescription.encodeNat value).reverse
              baseLeftRev) rest } := by
  induction value generalizing baseLeftRev with
  | zero =>
      change machine.runConfigExact? 1
        { state := .scanState
          tape := SerializedShift.cursorTape baseLeftRev
            (MachineCodeSymbol.done :: rest) } =
        some
          { state := .writeBlank
            tape := SerializedShift.cursorTape
              (MachineCodeSymbol.done :: baseLeftRev) rest }
      rw [TuringMachine.runConfigExact?]
      rw [step_scan_done]
      rfl
  | succ value ih =>
      change machine.runConfigExact? ((value + 1) + 1)
        { state := .scanState
          tape := SerializedShift.cursorTape baseLeftRev
            (MachineCodeSymbol.tick ::
              MachineDescription.encodeNatAppend value rest) } = _
      rw [TuringMachine.runConfigExact?]
      rw [step_scan_tick]
      simp only
      simpa [MachineDescription.encodeNat, List.reverse_cons,
        List.append_assoc] using ih (MachineCodeSymbol.tick :: baseLeftRev)
  done

theorem finishPrefix_run_exact
    (leftRev : Word MachineCodeSymbol)
    (queryRead firstJunk secondJunk : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.runConfigExact? 3
        { state := .writeBlank
          tape := SerializedShift.cursorTape leftRev
            (queryRead :: firstJunk :: secondJunk :: rest) } =
      some
        { state := .eraseGap
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.header :: MachineCodeSymbol.transition ::
              MachineCodeSymbol.blank :: leftRev) rest } := by
  cases queryRead <;> cases firstJunk <;> cases secondJunk <;>
    cases rest <;> rfl
  done

theorem prefix_run_exact
    (currentState : Nat)
    (queryRead firstJunk secondJunk : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.runConfigExact? (currentState + 5)
        { state := .start
          tape := Tape.input
            (MachineCodeSymbol.header ::
              MachineDescription.encodeNatAppend currentState
                (queryRead :: firstJunk :: secondJunk :: rest)) } =
      some (prefixTargetConfig currentState rest) := by
  have hstart : machine.runConfigExact? 1
      { state := .start
        tape := Tape.input
          (MachineCodeSymbol.header ::
            MachineDescription.encodeNatAppend currentState
              (queryRead :: firstJunk :: secondJunk :: rest)) } =
    some
      { state := .scanState
        tape := SerializedShift.cursorTape [MachineCodeSymbol.header]
          (MachineDescription.encodeNatAppend currentState
            (queryRead :: firstJunk :: secondJunk :: rest)) } := by
    change machine.runConfigExact? 1
      { state := .start
        tape := SerializedShift.cursorTape []
          (MachineCodeSymbol.header ::
            MachineDescription.encodeNatAppend currentState
              (queryRead :: firstJunk :: secondJunk :: rest)) } = _
    rw [TuringMachine.runConfigExact?]
    rw [step_start]
    rfl
  have hnat := scanNat_run_exact currentState
    [MachineCodeSymbol.header]
    (queryRead :: firstJunk :: secondJunk :: rest)
  have hfinish := finishPrefix_run_exact
    (List.append (MachineDescription.encodeNat currentState).reverse
      [MachineCodeSymbol.header])
    queryRead firstJunk secondJunk rest
  have hall := runConfigExact_trans (runConfigExact_trans hstart hnat) hfinish
  simpa [prefixTargetConfig, builtLeftRev,
    Section53FinalGateMaterializer.PrefixBuilder.comparatorPrefix,
    MachineDescription.encodeNatAppend, List.reverse_append,
    List.reverse_cons, List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall
  done

def eraseConfig
    (baseLeftRev remaining : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .eraseGap
  tape := SerializedShift.cursorTape baseLeftRev
    (List.append remaining
      (MachineCodeSymbol.transition :: MachineCodeSymbol.transition ::
        MachineDescription.encodeNatAppend haltState suffix))

def eraseTargetConfig
    (baseLeftRev cleanedRev : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .rewindGap
    (Section53FinalGateMaterializer.firstToken haltState)
  tape := SerializedShift.cursorTape
    (MachineCodeSymbol.transition ::
      List.append cleanedRev baseLeftRev)
    (MachineCodeSymbol.blank :: MachineCodeSymbol.moveRight ::
      List.append (Section53FinalGateMaterializer.tokenTail haltState)
        suffix)

theorem step_erase_symbol
    (baseLeftRev rest : Word MachineCodeSymbol)
    (symbol : MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol)
    (hsymbol : symbol ≠ MachineCodeSymbol.transition) :
    machine.stepConfig
        (eraseConfig baseLeftRev (symbol :: rest) haltState suffix) =
      some (eraseConfig
        (MachineCodeSymbol.blank :: baseLeftRev) rest haltState suffix) := by
  cases symbol <;> cases rest <;> cases haltState <;> cases suffix <;>
    simp_all [eraseConfig, machine, transition,
      TuringMachine.stepConfig, Tape.read, SerializedShift.cursorTape,
      Tape.write, Tape.move, Tape.moveRight, List.map_append]
  done

theorem run_erase_transition
    (baseLeftRev rest : Word MachineCodeSymbol)
    (next : MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol)
    (hnext : next ≠ MachineCodeSymbol.transition) :
    machine.runConfigExact? 5
        (eraseConfig baseLeftRev
          (MachineCodeSymbol.transition :: next :: rest)
          haltState suffix) =
      some (eraseConfig
        (MachineCodeSymbol.blank :: baseLeftRev)
        (next :: rest) haltState suffix) := by
  cases next <;> cases rest <;> cases haltState <;> cases suffix <;>
    simp_all [eraseConfig, machine, transition,
      TuringMachine.runConfigExact?, TuringMachine.stepConfig,
      Tape.read, SerializedShift.cursorTape, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight, List.map_append]
  done

theorem run_erase_sentinel
    (baseLeftRev : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.runConfigExact? 3
        (eraseConfig baseLeftRev [] haltState suffix) =
      some (eraseTargetConfig baseLeftRev [] haltState suffix) := by
  cases baseLeftRev <;> cases haltState <;> cases suffix <;> rfl
  done

theorem noDouble_tail
    (symbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (h : NoDoubleTransition
      (List.append (symbol :: rest) [MachineCodeSymbol.transition])) :
    NoDoubleTransition
      (List.append rest [MachineCodeSymbol.transition]) := by
  intro left tail heq
  apply h (symbol :: left) tail
  change symbol :: List.append rest [MachineCodeSymbol.transition] =
    symbol :: List.append left
      (MachineCodeSymbol.transition :: MachineCodeSymbol.transition :: tail)
  exact congrArg (List.cons symbol) heq
  done

theorem noDouble_transition_next
    (next : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (h : NoDoubleTransition
      (List.append (MachineCodeSymbol.transition :: next :: rest)
        [MachineCodeSymbol.transition])) :
    next ≠ MachineCodeSymbol.transition := by
  intro hnext
  subst next
  apply h [] (List.append rest [MachineCodeSymbol.transition])
  rfl
  done

theorem noDouble_transition_not_last
    (h : NoDoubleTransition
      (List.append [MachineCodeSymbol.transition]
        [MachineCodeSymbol.transition])) : False := by
  apply h [] []
  rfl
  done

theorem replicate_blank_slide
    (count : Nat)
    (suffix : Word MachineCodeSymbol) :
    List.append
        (List.replicate count MachineCodeSymbol.blank)
        (MachineCodeSymbol.blank :: suffix) =
      MachineCodeSymbol.blank ::
        List.append
          (List.replicate count MachineCodeSymbol.blank) suffix := by
  exact (cons_replicate_append_eq_replicate_append_cons count
    MachineCodeSymbol.blank suffix).symm
  done

theorem eraseTarget_cons_blank
    (baseLeftRev : Word MachineCodeSymbol)
    (count haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    eraseTargetConfig
        (MachineCodeSymbol.blank :: baseLeftRev)
        (List.replicate count MachineCodeSymbol.blank)
        haltState suffix =
      eraseTargetConfig baseLeftRev
        (List.replicate (count + 1) MachineCodeSymbol.blank)
        haltState suffix := by
  simp [eraseTargetConfig, replicate_succ_eq_append_singleton,
    List.append_assoc]
  done

theorem erase_run_exact
    (remaining : Word MachineCodeSymbol)
    (baseLeftRev : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol)
    (hnoDouble : NoDoubleTransition
      (List.append remaining [MachineCodeSymbol.transition])) :
    exists steps : Nat,
      machine.runConfigExact? steps
          (eraseConfig baseLeftRev remaining haltState suffix) =
        some (eraseTargetConfig baseLeftRev
          (List.replicate remaining.length MachineCodeSymbol.blank)
          haltState suffix) := by
  induction remaining generalizing baseLeftRev with
  | nil =>
      exact ⟨3, by simpa using
        run_erase_sentinel baseLeftRev haltState suffix⟩
  | cons symbol rest ih =>
      by_cases hsymbol : symbol = MachineCodeSymbol.transition
      · subst symbol
        cases rest with
        | nil =>
            exact False.elim (noDouble_transition_not_last hnoDouble)
        | cons next tail =>
            have hnext := noDouble_transition_next next tail hnoDouble
            have hpair := run_erase_transition baseLeftRev tail next
              haltState suffix hnext
            have htail0 := noDouble_tail MachineCodeSymbol.transition
              (next :: tail) hnoDouble
            rcases ih
                (MachineCodeSymbol.blank :: baseLeftRev)
                htail0 with ⟨steps, hrun⟩
            refine ⟨5 + steps, ?_⟩
            have hall := runConfigExact_trans hpair hrun
            rw [eraseTarget_cons_blank baseLeftRev
              (next :: tail).length haltState suffix] at hall
            simpa using hall
      ·
          have hstep := step_erase_symbol baseLeftRev rest symbol
            haltState suffix hsymbol
          have htail := noDouble_tail symbol rest hnoDouble
          rcases ih (MachineCodeSymbol.blank :: baseLeftRev) htail with
            ⟨steps, hrun⟩
          refine ⟨1 + steps, ?_⟩
          have hall := runConfigExact_trans
            (show machine.runConfigExact? 1
                (eraseConfig baseLeftRev (symbol :: rest) haltState suffix) =
              some (eraseConfig (MachineCodeSymbol.blank :: baseLeftRev)
                rest haltState suffix) by
              rw [TuringMachine.runConfigExact?, hstep]
              rfl)
            hrun
          rw [eraseTarget_cons_blank baseLeftRev rest.length
            haltState suffix] at hall
          simpa using hall
  done

def rewindTape
    (built remainingRev crossed tail : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      SerializedShift.cursorTape built.reverse
        (MachineCodeSymbol.header :: List.append crossed tail)
  | current :: more =>
      SerializedShift.cursorTape
        (List.append more
          (MachineCodeSymbol.header :: built.reverse))
        (current :: List.append crossed tail)

def rewindConfig
    (token : Bool)
    (built remainingRev crossed : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .rewindGap token
  tape := rewindTape built remainingRev crossed
    (MachineCodeSymbol.moveRight ::
      List.append (Section53FinalGateMaterializer.tokenTail haltState) suffix)

theorem step_rewind_symbol
    (token : Bool)
    (built : Word MachineCodeSymbol)
    (current : MachineCodeSymbol)
    (remainingRev crossed : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol)
    (hcurrent : current ≠ MachineCodeSymbol.header) :
    machine.stepConfig
        (rewindConfig token built (current :: remainingRev) crossed
          haltState suffix) =
      some (rewindConfig token built remainingRev (current :: crossed)
        haltState suffix) := by
  cases token <;> cases current <;> cases remainingRev <;> cases crossed <;>
    cases haltState <;> cases suffix <;>
      simp_all [rewindConfig, rewindTape, machine, transition,
        TuringMachine.stepConfig, Tape.read, SerializedShift.cursorTape,
        Tape.write, Tape.move, Tape.moveLeft, List.map_append]
  done

theorem step_rewind_header
    (token : Bool)
    (built crossed : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    machine.stepConfig
        (rewindConfig token built [] crossed haltState suffix) =
      some
        { state := .ready token
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.header :: built.reverse)
            (List.append crossed
              (MachineCodeSymbol.moveRight ::
                List.append
                  (Section53FinalGateMaterializer.tokenTail haltState)
                  suffix)) } := by
  cases token <;> cases built <;> cases crossed <;> cases haltState <;>
    cases suffix <;> rfl
  done

theorem rewind_run_exact
    (token : Bool)
    (built remainingRev crossed : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol)
    (hremaining : forall symbol : MachineCodeSymbol,
      List.Mem symbol remainingRev -> symbol ≠ MachineCodeSymbol.header) :
    machine.runConfigExact? (remainingRev.length + 1)
        (rewindConfig token built remainingRev crossed haltState suffix) =
      some
        { state := .ready token
          tape := SerializedShift.cursorTape
            (MachineCodeSymbol.header :: built.reverse)
            (List.append remainingRev.reverse
              (List.append crossed
                (MachineCodeSymbol.moveRight ::
                  List.append
                    (Section53FinalGateMaterializer.tokenTail haltState)
                    suffix))) } := by
  induction remainingRev generalizing crossed with
  | nil =>
      rw [TuringMachine.runConfigExact?]
      rw [step_rewind_header]
      rfl
  | cons current more ih =>
      have hcurrent := hremaining current (List.Mem.head more)
      have hmore : forall symbol : MachineCodeSymbol,
          List.Mem symbol more -> symbol ≠ MachineCodeSymbol.header := by
        intro symbol hmem
        exact hremaining symbol (List.Mem.tail current hmem)
      change machine.runConfigExact? ((more.length + 1) + 1)
        (rewindConfig token built (current :: more) crossed haltState suffix) = _
      rw [TuringMachine.runConfigExact?]
      rw [step_rewind_symbol token built current more crossed haltState suffix
        hcurrent]
      simp only
      simpa [List.reverse_cons, List.append_assoc] using
        ih (current :: crossed) hmore
  done

theorem cleanedGap_eq_replicate_append_transition
    (gap : Word MachineCodeSymbol) :
    cleanedGap gap =
      List.append (List.replicate gap.length MachineCodeSymbol.blank)
        [MachineCodeSymbol.transition, MachineCodeSymbol.blank] := by
  induction gap with
  | nil => rfl
  | cons symbol rest ih =>
      simp [cleanedGap, ih, List.replicate_succ, List.append_assoc]
  done

theorem cleanedGap_no_header
    (gap : Word MachineCodeSymbol)
    (symbol : MachineCodeSymbol)
    (hmem : List.Mem symbol (cleanedGap gap)) :
    symbol ≠ MachineCodeSymbol.header := by
  induction gap with
  | nil =>
      change List.Mem symbol
        [MachineCodeSymbol.transition, MachineCodeSymbol.blank] at hmem
      rcases List.mem_cons.mp hmem with htransition | hblank
      · subst symbol
        simp
      · have hblank' := List.mem_singleton.mp hblank
        subst symbol
        simp
  | cons current rest ih =>
      change List.Mem symbol
        (MachineCodeSymbol.blank :: cleanedGap rest) at hmem
      rcases List.mem_cons.mp hmem with hblank | htail
      · subst symbol
        simp
      · exact ih htail
  done

theorem cleanedGap_no_moveRight
    (gap : Word MachineCodeSymbol)
    (symbol : MachineCodeSymbol)
    (hmem : List.Mem symbol (cleanedGap gap)) :
    symbol ≠ MachineCodeSymbol.moveRight := by
  induction gap with
  | nil =>
      change List.Mem symbol
        [MachineCodeSymbol.transition, MachineCodeSymbol.blank] at hmem
      rcases List.mem_cons.mp hmem with htransition | hblank
      · subst symbol
        simp
      · have hblank' := List.mem_singleton.mp hblank
        subst symbol
        simp
  | cons current rest ih =>
      change List.Mem symbol
        (MachineCodeSymbol.blank :: cleanedGap rest) at hmem
      rcases List.mem_cons.mp hmem with hblank | htail
      · subst symbol
        simp
      · exact ih htail
  done

theorem run_exact
    (currentState : Nat)
    (queryRead firstJunk secondJunk : MachineCodeSymbol)
    (gap : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol)
    (hnoDouble : NoDoubleTransition
      (List.append gap [MachineCodeSymbol.transition])) :
    exists steps : Nat,
      machine.runConfigExact? steps
          (sourceConfig currentState queryRead firstJunk secondJunk gap
            haltState suffix) =
        some (targetConfig currentState gap haltState suffix) := by
  let tail : Word MachineCodeSymbol :=
    List.append gap
      (MachineCodeSymbol.transition :: MachineCodeSymbol.transition ::
        MachineDescription.encodeNatAppend haltState suffix)
  have hprefix := prefix_run_exact currentState queryRead firstJunk secondJunk
    tail
  rcases erase_run_exact gap (builtLeftRev currentState) haltState suffix
      hnoDouble with ⟨eraseSteps, herase⟩
  let blankRev : Word MachineCodeSymbol :=
    List.replicate gap.length MachineCodeSymbol.blank
  have hrewind := rewind_run_exact
    (Section53FinalGateMaterializer.firstToken haltState)
    (Section53FinalGateMaterializer.PrefixBuilder.comparatorPrefix currentState)
    (MachineCodeSymbol.blank :: MachineCodeSymbol.transition :: blankRev)
    [] haltState suffix
    (by
      intro symbol hmem
      rcases List.mem_cons.mp hmem with htransition | hblank
      · subst symbol
        simp
      · rcases List.mem_cons.mp hblank with htransition | hblank
        · subst symbol
          simp
        · have hblank' := (List.mem_replicate.mp hblank).right
          subst symbol
          simp)
  have herase' : machine.runConfigExact? eraseSteps
      (prefixTargetConfig currentState tail) =
    some (eraseTargetConfig (builtLeftRev currentState) blankRev
      haltState suffix) := by
    simpa [prefixTargetConfig, eraseConfig, tail, blankRev] using herase
  have hrewind' : machine.runConfigExact?
      ((MachineCodeSymbol.blank :: MachineCodeSymbol.transition ::
        blankRev).length + 1)
      (eraseTargetConfig (builtLeftRev currentState) blankRev
        haltState suffix) =
    some (targetConfig currentState gap haltState suffix) := by
    simpa [eraseTargetConfig, rewindConfig, targetConfig,
      rewindTape,
      Section53FinalGateMaterializer.HaltCopier.sourceConfig,
      builtLeftRev, blankRev, cleanedGap_eq_replicate_append_transition,
      List.reverse_cons, List.append_assoc] using hrewind
  refine ⟨(currentState + 5) + eraseSteps +
      ((MachineCodeSymbol.blank :: MachineCodeSymbol.transition ::
        blankRev).length + 1), ?_⟩
  have hfront : machine.runConfigExact? ((currentState + 5) + eraseSteps)
      (sourceConfig currentState queryRead firstJunk secondJunk gap
        haltState suffix) =
    some (eraseTargetConfig (builtLeftRev currentState) blankRev
      haltState suffix) := by
    apply runConfigExact_trans
      (by simpa [sourceConfig, sourceWord, tail] using hprefix)
      herase'
  exact runConfigExact_trans hfront hrewind'
  done


end CurrentBuilder

theorem currentBuilder_materializes_finalComparator
    (currentState : Nat)
    (queryRead firstJunk secondJunk : MachineCodeSymbol)
    (gap : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol)
    (hnoDouble : CurrentBuilder.NoDoubleTransition
      (List.append gap [MachineCodeSymbol.transition])) :
    exists builderTape finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes CurrentBuilder.machine
        { state := CurrentBuilder.Control.start
          tape := Tape.input
            (CurrentBuilder.sourceWord currentState queryRead firstJunk
              secondJunk gap haltState suffix) }
        { state := CurrentBuilder.Control.ready (firstToken haltState)
          tape := builderTape } ∧
      TuringMachine.Computes HaltCopier.machine
        { state := HaltCopier.Control.seekSource (firstToken haltState)
          tape := builderTape }
        { state := HaltCopier.Control.ready
          tape := finalTape } ∧
      Tape.Equiv finalTape
        (finalComparatorSourceConfig currentState haltState []).tape := by
  rcases CurrentBuilder.run_exact currentState queryRead firstJunk
      secondJunk gap haltState suffix hnoDouble with ⟨steps, hrun⟩
  let builderTape : Tape MachineCodeSymbol :=
    (CurrentBuilder.targetConfig currentState gap haltState suffix).tape
  have hbuilder : TuringMachine.Computes CurrentBuilder.machine
      { state := CurrentBuilder.Control.start
        tape := Tape.input
          (CurrentBuilder.sourceWord currentState queryRead firstJunk
            secondJunk gap haltState suffix) }
      { state := CurrentBuilder.Control.ready (firstToken haltState)
        tape := builderTape } := by
    exact TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
        (by simpa [CurrentBuilder.sourceConfig, builderTape,
          CurrentBuilder.targetConfig] using hrun))
  rcases HaltCopier.copy_computes
      (PrefixBuilder.comparatorPrefix currentState)
      (CurrentBuilder.cleanedGap gap) haltState suffix
      (CurrentBuilder.cleanedGap_no_header gap)
      (CurrentBuilder.cleanedGap_no_moveRight gap) with
    ⟨copyTarget, hcopy, hcopyState, hcopyTape⟩
  rcases copyTarget with ⟨copyState, finalTape⟩
  change copyState = HaltCopier.Control.ready at hcopyState
  subst copyState
  have hcopy' : TuringMachine.Computes HaltCopier.machine
      { state := HaltCopier.Control.seekSource (firstToken haltState)
        tape := builderTape }
      { state := HaltCopier.Control.ready, tape := finalTape } := by
    change TuringMachine.Computes HaltCopier.machine
      (HaltCopier.sourceConfig
        (PrefixBuilder.comparatorPrefix currentState)
        (CurrentBuilder.cleanedGap gap) haltState suffix)
      { state := HaltCopier.Control.ready, tape := finalTape }
    exact hcopy
  have hfinal : Tape.Equiv finalTape
      (finalComparatorSourceConfig currentState haltState []).tape := by
    rw [← haltCopier_output_tape_eq_finalComparator_source]
    exact hcopyTape
  exact ⟨builderTape, finalTape, hbuilder, hcopy', hfinal⟩
  done

theorem currentBuilder_materializes_finalComparator_of_tape_equiv
    (currentState : Nat)
    (queryRead firstJunk secondJunk : MachineCodeSymbol)
    (gap : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hnoDouble : CurrentBuilder.NoDoubleTransition
      (List.append gap [MachineCodeSymbol.transition]))
    (hsource : Tape.Equiv
      (Tape.input
        (CurrentBuilder.sourceWord currentState queryRead firstJunk
          secondJunk gap haltState suffix)) sourceTape) :
    exists builderTape finalTape : Tape MachineCodeSymbol,
      TuringMachine.Computes CurrentBuilder.machine
        { state := CurrentBuilder.Control.start, tape := sourceTape }
        { state := CurrentBuilder.Control.ready (firstToken haltState)
          tape := builderTape } ∧
      TuringMachine.Computes HaltCopier.machine
        { state := HaltCopier.Control.seekSource (firstToken haltState)
          tape := builderTape }
        { state := HaltCopier.Control.ready, tape := finalTape } ∧
      Tape.Equiv finalTape
        (finalComparatorSourceConfig currentState haltState []).tape := by
  rcases currentBuilder_materializes_finalComparator currentState queryRead
      firstJunk secondJunk gap haltState suffix hnoDouble with
    ⟨canonicalBuilder, canonicalFinal, hbuilder, hcopy, hfinal⟩
  rcases computes_transport_of_tape_equiv hbuilder hsource with
    ⟨builderConfig, hbuilderActual, hbuilderState, hbuilderTape⟩
  rcases builderConfig with ⟨builderState, builderTape⟩
  change builderState =
    CurrentBuilder.Control.ready (firstToken haltState) at hbuilderState
  subst builderState
  rcases computes_transport_of_tape_equiv hcopy hbuilderTape with
    ⟨finalConfig, hcopyActual, hcopyState, hcopyTape⟩
  rcases finalConfig with ⟨finalState, finalTape⟩
  change finalState = HaltCopier.Control.ready at hcopyState
  subst finalState
  exact ⟨builderTape, finalTape, hbuilderActual, hcopyActual,
    Tape.Equiv.trans (Tape.Equiv.symm hcopyTape) hfinal⟩
  done


end Section53NoMatchFinalGate

end Computability
end FoC
