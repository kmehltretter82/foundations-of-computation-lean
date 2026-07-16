import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.Context.Phase
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.RepeatedCopy
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.BoundedLoop

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.PositiveInitializerPhase

open FiniteRecognizer ExactFuel StrictProbe
open FiniteRecognizer.Interpreter.InitializerFrontier
open FiniteRecognizer.Interpreter.InitializerPersistentCopy
open FiniteRecognizer.Interpreter.InitializerPersistentCopy.PersistentMasterCopier
open FiniteRecognizer.Interpreter.InitializerRepeatedCopy
open FiniteRecognizer.Interpreter.LoopRestagingAudit
open FiniteRecognizer.Interpreter.BoundedLoopInduction
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep.RuntimeKeySingleKeyRepair

/-!
# Positive initializer phase

The Boolean-context materializer produces a retained raw transition table and
a zero-copy stack sentinel. The driver consumes parsed unary fuel from left
metadata and re-enters the persistent copier once per tick. On the final tick
it erases the retained table and every metadata field except the encoded start
state. A streaming gap compactor joins that field to the table stack, and
`NextCopyRestager` produces the single-key runtime-loop source.
-/

namespace CopyDriver

inductive Control where
  | fromReady
  | atActiveGap
  | scanMaster
  | scanBase
  | fuelDone
  | fuelFirstTick
  | fuelTicks
  | eraseLastTick
  | afterErase
  | returnBase
  | returnMaster
  | returnBounce
  | moreReady
  | finalHeader
  | finalState
  | keepStart
  | sealStart
  | eraseAfterStart
  | eraseMaster
  | compactReady
  | halt
deriving DecidableEq

namespace Control

def elems : List Control :=
  [.fromReady, .atActiveGap, .scanMaster, .scanBase, .fuelDone,
    .fuelFirstTick, .fuelTicks, .eraseLastTick, .afterErase,
    .returnBase, .returnMaster, .returnBounce, .moreReady, .finalHeader,
    .finalState, .keepStart, .sealStart, .eraseAfterStart, .eraseMaster,
    .compactReady, .halt]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control <;> simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .fromReady, some current =>
      some (some current, Direction.left, .atActiveGap)
  | .atActiveGap, none =>
      some (none, Direction.left, .scanMaster)
  | .scanMaster, some current =>
      some (some current, Direction.left, .scanMaster)
  | .scanMaster, none =>
      some (none, Direction.left, .scanBase)
  | .scanBase, some MachineCodeSymbol.header =>
      some (some MachineCodeSymbol.header, Direction.left, .fuelDone)
  | .scanBase, some current =>
      some (some current, Direction.left, .scanBase)
  | .fuelDone, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.left, .fuelFirstTick)
  | .fuelFirstTick, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.left, .fuelTicks)
  | .fuelTicks, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.left, .fuelTicks)
  | .fuelTicks, none =>
      some (none, Direction.right, .eraseLastTick)
  | .eraseLastTick, some MachineCodeSymbol.tick =>
      some (none, Direction.right, .afterErase)
  | .afterErase, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .returnBase)
  | .afterErase, some MachineCodeSymbol.done =>
      some (none, Direction.right, .finalHeader)
  | .returnBase, some current =>
      some (some current, Direction.right, .returnBase)
  | .returnBase, none =>
      some (none, Direction.right, .returnMaster)
  | .returnMaster, some current =>
      some (some current, Direction.right, .returnMaster)
  | .returnMaster, none =>
      some (none, Direction.right, .returnBounce)
  | .returnBounce, read =>
      some (read, Direction.left, .moreReady)
  | .finalHeader, some MachineCodeSymbol.header =>
      some (none, Direction.right, .finalState)
  | .finalState, some MachineCodeSymbol.tick =>
      some (none, Direction.right, .finalState)
  | .finalState, some MachineCodeSymbol.done =>
      some (none, Direction.right, .keepStart)
  | .keepStart, some MachineCodeSymbol.tick =>
      some (some MachineCodeSymbol.tick, Direction.right, .keepStart)
  | .keepStart, some MachineCodeSymbol.done =>
      some (some MachineCodeSymbol.done, Direction.right, .sealStart)
  | .sealStart, some _ =>
      some (some MachineCodeSymbol.header, Direction.right, .eraseAfterStart)
  | .eraseAfterStart, some _ =>
      some (none, Direction.right, .eraseAfterStart)
  | .eraseAfterStart, none =>
      some (none, Direction.right, .eraseMaster)
  | .eraseMaster, some _ =>
      some (none, Direction.right, .eraseMaster)
  | .eraseMaster, none =>
      some (none, Direction.right, .compactReady)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .fromReady
  halt := .halt
  transition := transition
  statesFinite := Control.finite

end CopyDriver

namespace CopyDriver

def nearStart
    (D : MachineDescription) : Word MachineCodeSymbol :=
  List.append
    (List.replicate D.transitions.length MachineCodeSymbol.blank)
    (MachineCodeSymbol.blank ::
      (MachineDescription.encodeNat D.halt).reverse)

def beforeFuel
    (D : MachineDescription) : Word MachineCodeSymbol :=
  List.append (nearStart D)
    (List.append (MachineDescription.encodeNat D.start).reverse
      (MachineDescription.encodeNat D.stateCount).reverse)

theorem encodeNat_eq_ticks_done
    (value : Nat) :
    MachineDescription.encodeNat value =
      List.replicate value MachineCodeSymbol.tick ++
        [MachineCodeSymbol.done] := by
  induction value with
  | zero => rfl
  | succ value ih =>
      simp [MachineDescription.encodeNat, List.replicate_succ, ih]

theorem encodeNat_reverse_eq_done_ticks
    (value : Nat) :
    (MachineDescription.encodeNat value).reverse =
      MachineCodeSymbol.done ::
        List.replicate value MachineCodeSymbol.tick := by
  rw [encodeNat_eq_ticks_done]
  simp [List.reverse_append, List.reverse_replicate]

theorem positiveBase_eq
    (D : MachineDescription)
    (fuel : Nat) :
    positiveMaterializerCopierBaseLeftRev D fuel =
      List.append (beforeFuel D)
        (MachineCodeSymbol.header ::
          MachineCodeSymbol.done ::
            List.replicate fuel MachineCodeSymbol.tick) := by
  simp [positiveMaterializerCopierBaseLeftRev, beforeFuel, nearStart,
    FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHaltLeftRev,
    FiniteRecognizer.Interpreter.ParserAssembly.headerAfterStartLeftRev,
    FiniteRecognizer.Interpreter.ParserAssembly.headerAfterStateLeftRev,
    FiniteRecognizer.Interpreter.ParserAssembly.headerAfterHeaderLeftRev,
    encodeNat_reverse_eq_done_ticks, List.append_assoc]

theorem encodeNat_no_header
    (value : Nat)
    (symbol : MachineCodeSymbol)
    (hmem : List.Mem symbol (MachineDescription.encodeNat value)) :
    symbol ≠ MachineCodeSymbol.header := by
  rw [encodeNat_eq_ticks_done] at hmem
  rcases List.mem_append.mp hmem with htick | hdone
  · have : symbol = MachineCodeSymbol.tick :=
      List.mem_replicate.mp htick |>.2
    simp [this]
  · have : symbol = MachineCodeSymbol.done :=
      List.mem_singleton.mp hdone
    simp [this]

theorem encodeNat_reverse_no_header
    (value : Nat)
    (symbol : MachineCodeSymbol)
    (hmem : List.Mem symbol (MachineDescription.encodeNat value).reverse) :
    symbol ≠ MachineCodeSymbol.header := by
  exact encodeNat_no_header value symbol (List.mem_reverse.mp hmem)

theorem beforeFuel_no_header
    (D : MachineDescription)
    (symbol : MachineCodeSymbol)
    (hmem : List.Mem symbol (beforeFuel D)) :
    symbol ≠ MachineCodeSymbol.header := by
  rcases List.mem_append.mp (show List.Mem symbol
      (List.append (nearStart D)
        (List.append (MachineDescription.encodeNat D.start).reverse
          (MachineDescription.encodeNat D.stateCount).reverse)) from hmem)
      with hnear | hfields
  · rcases List.mem_append.mp (show List.Mem symbol
        (List.append
          (List.replicate D.transitions.length MachineCodeSymbol.blank)
          (MachineCodeSymbol.blank ::
            (MachineDescription.encodeNat D.halt).reverse)) from hnear)
        with hrows | hhalt
    · have hsymbol : symbol = MachineCodeSymbol.blank :=
        (List.mem_replicate.mp hrows).2
      simp [hsymbol]
    · rcases List.mem_cons.mp hhalt with hblank | hhalt
      · subst symbol
        simp
      · exact encodeNat_reverse_no_header D.halt symbol hhalt
  · rcases List.mem_append.mp hfields with hstart | hstate
    · exact encodeNat_reverse_no_header D.start symbol hstart
    · exact encodeNat_reverse_no_header D.stateCount symbol hstate

def leftCursorTape
    (remaining : Word MachineCodeSymbol)
    (boundary : Option MachineCodeSymbol)
    (leftTail right : List (Option MachineCodeSymbol)) :
    Tape MachineCodeSymbol :=
  match remaining with
  | [] => { left := leftTail, head := boundary, right := right }
  | current :: more =>
      { left := more.map some ++ boundary :: leftTail
        head := some current
        right := right }

def scanMasterConfig
    (remaining : Word MachineCodeSymbol)
    (leftTail right : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .scanMaster
    tape := leftCursorTape remaining none leftTail right }

def scanBaseConfig
    (remaining : Word MachineCodeSymbol)
    (leftTail right : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .scanBase
    tape := leftCursorTape remaining (some MachineCodeSymbol.header)
      leftTail right }

theorem scanMaster_symbol_step
    (current : MachineCodeSymbol)
    (more : Word MachineCodeSymbol)
    (leftTail right : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (scanMasterConfig (current :: more) leftTail right) =
      some
        (scanMasterConfig more leftTail (some current :: right)) := by
  cases more <;> cases leftTail <;> cases right <;> rfl

theorem scanMaster_run
    (remaining : Word MachineCodeSymbol)
    (leftTail right : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes machine
      (scanMasterConfig remaining leftTail right)
      (scanMasterConfig [] leftTail
        (remaining.reverse.map some ++ right)) := by
  induction remaining generalizing right with
  | nil => exact TuringMachine.Computes.refl _
  | cons current more ih =>
      have hstep : TuringMachine.Step machine
          (scanMasterConfig (current :: more) leftTail right)
          (scanMasterConfig more leftTail (some current :: right)) :=
        TuringMachine.stepConfig_eq_some_iff_step.mp
          (scanMaster_symbol_step current more leftTail right)
      have htail := ih (some current :: right)
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        TuringMachine.Computes.step hstep htail

theorem atActiveGap_step
    (current : MachineCodeSymbol)
    (more : Word MachineCodeSymbol)
    (leftTail right : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        { state := .atActiveGap
          tape :=
            { left := (current :: more).map some ++ none :: leftTail
              head := none
              right := right } } =
      some
        (scanMasterConfig (current :: more) leftTail (none :: right)) := by
  cases more <;> cases leftTail <;> cases right <;> rfl

theorem scanMaster_gap_step
    (remaining : Word MachineCodeSymbol)
    (leftTail right : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (scanMasterConfig []
          (remaining.map some ++ some MachineCodeSymbol.header :: leftTail)
          right) =
      some
        (scanBaseConfig remaining leftTail (none :: right)) := by
  cases remaining <;> cases leftTail <;> cases right <;> rfl

theorem scanBase_symbol_step
    (current : MachineCodeSymbol)
    (more : Word MachineCodeSymbol)
    (leftTail right : List (Option MachineCodeSymbol))
    (hcurrent : current ≠ MachineCodeSymbol.header) :
    machine.stepConfig
        (scanBaseConfig (current :: more) leftTail right) =
      some
        (scanBaseConfig more leftTail (some current :: right)) := by
  cases current <;> cases more <;> cases leftTail <;> cases right <;>
    first | rfl | contradiction

theorem scanBase_run
    (remaining : Word MachineCodeSymbol)
    (leftTail right : List (Option MachineCodeSymbol))
    (hnoHeader : forall symbol, List.Mem symbol remaining ->
      symbol ≠ MachineCodeSymbol.header) :
    TuringMachine.Computes machine
      (scanBaseConfig remaining leftTail right)
      (scanBaseConfig [] leftTail
        (remaining.reverse.map some ++ right)) := by
  induction remaining generalizing right with
  | nil => exact TuringMachine.Computes.refl _
  | cons current more ih =>
      have hcurrent := hnoHeader current (List.mem_cons_self)
      have hstep : TuringMachine.Step machine
          (scanBaseConfig (current :: more) leftTail right)
          (scanBaseConfig more leftTail (some current :: right)) :=
        TuringMachine.stepConfig_eq_some_iff_step.mp
          (scanBase_symbol_step current more leftTail right hcurrent)
      have hmore : forall symbol, List.Mem symbol more ->
          symbol ≠ MachineCodeSymbol.header := by
        intro symbol hmem
        exact hnoHeader symbol (List.mem_cons_of_mem current hmem)
      have htail := ih (some current :: right) hmore
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        TuringMachine.Computes.step hstep htail

def fuelDoneTrail
    (D : MachineDescription)
    (master active : Word MachineCodeSymbol) :
    List (Option MachineCodeSymbol) :=
  some MachineCodeSymbol.header ::
    (beforeFuel D).reverse.map some ++
      none :: master.map some ++ none :: representedCells active

def fuelDoneConfig
    (D : MachineDescription)
    (fuel : Nat)
    (master active : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .fuelDone
    tape :=
      { left := List.replicate fuel (some MachineCodeSymbol.tick)
        head := some MachineCodeSymbol.done
        right := fuelDoneTrail D master active } }

theorem reachesFuelDone
    (D : MachineDescription)
    (fuel : Nat)
    (masterFirst : MachineCodeSymbol)
    (masterRest suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      { state := .fromReady
        tape := readyTape
          (positiveMaterializerCopierBaseLeftRev D fuel)
          (masterFirst :: masterRest) suffix }
      (fuelDoneConfig D fuel (masterFirst :: masterRest)
        (List.append (masterFirst :: masterRest) suffix)) := by
  let master := masterFirst :: masterRest
  let active := List.append master suffix
  have hready : TuringMachine.Step machine
      { state := .fromReady
        tape := readyTape
          (positiveMaterializerCopierBaseLeftRev D fuel) master suffix }
      { state := .atActiveGap
        tape :=
          { left := master.reverse.map some ++
              none :: (positiveMaterializerCopierBaseLeftRev D fuel).map some
            head := none
            right := representedCells active } } := by
    exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
      cases masterRest <;> cases suffix <;> rfl)
  have hgap : TuringMachine.Step machine
      { state := .atActiveGap
        tape :=
          { left := master.reverse.map some ++
              none :: (positiveMaterializerCopierBaseLeftRev D fuel).map some
            head := none
            right := representedCells active } }
      (scanMasterConfig master.reverse
        ((positiveMaterializerCopierBaseLeftRev D fuel).map some)
        (none :: representedCells active)) := by
    cases hrev : master.reverse with
    | nil =>
        have hlength := congrArg List.length hrev
        simp [master] at hlength
    | cons current more =>
        exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
          simpa [hrev] using atActiveGap_step current more
            ((positiveMaterializerCopierBaseLeftRev D fuel).map some)
            (representedCells active))
  have hmaster := scanMaster_run master.reverse
    ((positiveMaterializerCopierBaseLeftRev D fuel).map some)
    (none :: representedCells active)
  have hbaseStart : TuringMachine.Step machine
      (scanMasterConfig []
        ((positiveMaterializerCopierBaseLeftRev D fuel).map some)
        (master.reverse.reverse.map some ++
          none :: representedCells active))
      (scanBaseConfig (beforeFuel D)
        (some MachineCodeSymbol.done ::
          List.replicate fuel (some MachineCodeSymbol.tick))
        (none :: master.map some ++ none :: representedCells active)) := by
    exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
      simpa [positiveBase_eq, List.reverse_reverse, List.map_append,
        List.append_assoc] using
        scanMaster_gap_step (beforeFuel D)
          (some MachineCodeSymbol.done ::
            List.replicate fuel (some MachineCodeSymbol.tick))
          (master.map some ++ none :: representedCells active))
  have hbase := scanBase_run (beforeFuel D)
    (some MachineCodeSymbol.done ::
      List.replicate fuel (some MachineCodeSymbol.tick))
    (none :: master.map some ++ none :: representedCells active)
    (beforeFuel_no_header D)
  have hheader : TuringMachine.Step machine
      (scanBaseConfig []
        (some MachineCodeSymbol.done ::
          List.replicate fuel (some MachineCodeSymbol.tick))
        ((beforeFuel D).reverse.map some ++
          none :: master.map some ++ none :: representedCells active))
      (fuelDoneConfig D fuel master active) := by
    exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
      cases fuel <;> cases masterRest <;> cases suffix <;> rfl)
  have hheader' : TuringMachine.Step machine
      (scanBaseConfig []
        (some MachineCodeSymbol.done ::
          List.replicate fuel (some MachineCodeSymbol.tick))
        ((beforeFuel D).reverse.map some ++
          (none :: master.map some ++ none :: representedCells active)))
      (fuelDoneConfig D fuel master active) := by
    simpa [List.append_assoc] using hheader
  have hrun := TuringMachine.Computes.step hready
    (TuringMachine.Computes.step hgap
      (TuringMachine.computes_trans hmaster
        (TuringMachine.Computes.step hbaseStart
          (TuringMachine.computes_trans hbase
            (TuringMachine.Computes.step hheader'
              (TuringMachine.Computes.refl _))))))
  simpa [master, active, fuelDoneConfig, fuelDoneTrail,
    List.reverse_reverse, List.append_assoc] using hrun

def rightCursorTape
    (leftRev : List (Option MachineCodeSymbol))
    (remaining : Word MachineCodeSymbol)
    (boundary : Option MachineCodeSymbol)
    (rightTail : List (Option MachineCodeSymbol)) : Tape MachineCodeSymbol :=
  match remaining with
  | [] => { left := leftRev, head := boundary, right := rightTail }
  | current :: more =>
      { left := leftRev
        head := some current
        right := more.map some ++ boundary :: rightTail }

def returnBaseConfig
    (leftRev : List (Option MachineCodeSymbol))
    (remaining : Word MachineCodeSymbol)
    (rightTail : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .returnBase
    tape := rightCursorTape leftRev remaining none rightTail }

def returnMasterConfig
    (leftRev : List (Option MachineCodeSymbol))
    (remaining : Word MachineCodeSymbol)
    (rightTail : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .returnMaster
    tape := rightCursorTape leftRev remaining none rightTail }

theorem returnBase_symbol_step
    (leftRev : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol)
    (more : Word MachineCodeSymbol)
    (rightTail : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (returnBaseConfig leftRev (current :: more) rightTail) =
      some
        (returnBaseConfig (some current :: leftRev) more rightTail) := by
  cases leftRev <;> cases more <;> cases rightTail <;> rfl

theorem returnBase_run
    (leftRev : List (Option MachineCodeSymbol))
    (remaining : Word MachineCodeSymbol)
    (rightTail : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes machine
      (returnBaseConfig leftRev remaining rightTail)
      (returnBaseConfig
        (remaining.reverse.map some ++ leftRev) [] rightTail) := by
  induction remaining generalizing leftRev with
  | nil => exact TuringMachine.Computes.refl _
  | cons current more ih =>
      have hstep : TuringMachine.Step machine
          (returnBaseConfig leftRev (current :: more) rightTail)
          (returnBaseConfig (some current :: leftRev) more rightTail) :=
        TuringMachine.stepConfig_eq_some_iff_step.mp
          (returnBase_symbol_step leftRev current more rightTail)
      have htail := ih (some current :: leftRev)
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        TuringMachine.Computes.step hstep htail

theorem returnMaster_symbol_step
    (leftRev : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol)
    (more : Word MachineCodeSymbol)
    (rightTail : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (returnMasterConfig leftRev (current :: more) rightTail) =
      some
        (returnMasterConfig (some current :: leftRev) more rightTail) := by
  cases leftRev <;> cases more <;> cases rightTail <;> rfl

theorem returnMaster_run
    (leftRev : List (Option MachineCodeSymbol))
    (remaining : Word MachineCodeSymbol)
    (rightTail : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes machine
      (returnMasterConfig leftRev remaining rightTail)
      (returnMasterConfig
        (remaining.reverse.map some ++ leftRev) [] rightTail) := by
  induction remaining generalizing leftRev with
  | nil => exact TuringMachine.Computes.refl _
  | cons current more ih =>
      have hstep : TuringMachine.Step machine
          (returnMasterConfig leftRev (current :: more) rightTail)
          (returnMasterConfig (some current :: leftRev) more rightTail) :=
        TuringMachine.stepConfig_eq_some_iff_step.mp
          (returnMaster_symbol_step leftRev current more rightTail)
      have htail := ih (some current :: leftRev)
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        TuringMachine.Computes.step hstep htail

def fuelTicksConfig
    (remaining : Nat)
    (right : List (Option MachineCodeSymbol)) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .fuelTicks
    tape :=
      match remaining with
      | 0 => { left := [], head := none, right := right }
      | remaining + 1 =>
          { left := List.replicate remaining (some MachineCodeSymbol.tick)
            head := some MachineCodeSymbol.tick
            right := right } }

theorem fuelTicks_symbol_step
    (remaining : Nat)
    (right : List (Option MachineCodeSymbol)) :
    machine.stepConfig (fuelTicksConfig (remaining + 1) right) =
      some (fuelTicksConfig remaining
        (some MachineCodeSymbol.tick :: right)) := by
  cases remaining <;> cases right <;> rfl

theorem replicate_tick_append_tick
    (count : Nat)
    (suffix : List (Option MachineCodeSymbol)) :
    List.replicate count (some MachineCodeSymbol.tick) ++
        some MachineCodeSymbol.tick :: suffix =
      List.replicate (count + 1) (some MachineCodeSymbol.tick) ++ suffix := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa [List.replicate_succ] using
        congrArg (fun cells => some MachineCodeSymbol.tick :: cells) ih

theorem fuelTicks_run
    (remaining : Nat)
    (right : List (Option MachineCodeSymbol)) :
    TuringMachine.Computes machine
      (fuelTicksConfig remaining right)
      (fuelTicksConfig 0
        (List.replicate remaining (some MachineCodeSymbol.tick) ++ right)) := by
  induction remaining generalizing right with
  | zero => exact TuringMachine.Computes.refl _
  | succ remaining ih =>
      have hstep : TuringMachine.Step machine
          (fuelTicksConfig (remaining + 1) right)
          (fuelTicksConfig remaining
            (some MachineCodeSymbol.tick :: right)) :=
        TuringMachine.stepConfig_eq_some_iff_step.mp
          (fuelTicks_symbol_step remaining right)
      have htail := ih (some MachineCodeSymbol.tick :: right)
      have hrun := TuringMachine.Computes.step hstep htail
      rw [replicate_tick_append_tick] at hrun
      exact hrun

def moreReadyTape
    (D : MachineDescription)
    (fuel : Nat)
    (master active : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  { left := master.reverse.map some ++
      none :: (positiveMaterializerCopierBaseLeftRev D fuel).map some ++
        [none, none]
    head := none
    right := representedCells active }

def moreReadyConfig
    (D : MachineDescription)
    (fuel : Nat)
    (master active : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := .moreReady
    tape := moreReadyTape D fuel master active }

theorem moreReadyTape_equiv_source
    (D : MachineDescription)
    (fuel : Nat)
    (master active : Word MachineCodeSymbol) :
    Tape.Equiv (sourceTape
      (positiveMaterializerCopierBaseLeftRev D fuel) master active)
      (moreReadyTape D fuel master active) := by
  refine ⟨?_, rfl, rfl⟩
  change Tape.dropTrailingNone
      (master.reverse.map some ++
        none :: (positiveMaterializerCopierBaseLeftRev D fuel).map some) =
    Tape.dropTrailingNone
      ((master.reverse.map some ++
        none :: (positiveMaterializerCopierBaseLeftRev D fuel).map some) ++
          [none, none])
  simpa [List.replicate_succ] using
    (FoC.Computability.dropTrailingNone_append_replicate_none
      (master.reverse.map some ++
        none :: (positiveMaterializerCopierBaseLeftRev D fuel).map some)
      2).symm

theorem afterErase_tick_step
    (leftRev : List (Option MachineCodeSymbol))
    (next : MachineCodeSymbol)
    (right : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        { state := .afterErase
          tape :=
            { left := leftRev
              head := some MachineCodeSymbol.tick
              right := some next :: right } } =
      some
        { state := .returnBase
          tape :=
            { left := some MachineCodeSymbol.tick :: leftRev
              head := some next
              right := right } } := by
  cases leftRev <;> cases right <;> rfl

theorem fuelTicks_done_step
    (first : MachineCodeSymbol)
    (right : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        (fuelTicksConfig 0 (some first :: right)) =
      some
        { state := .eraseLastTick
          tape :=
            { left := [none]
              head := some first
              right := right } } := by
  cases right <;> rfl

theorem returnBounce_step
    (leftRev : List (Option MachineCodeSymbol))
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) :
    machine.stepConfig
        { state := .returnBounce
          tape := PersistentMasterCopier.tapeAtCells
            (none :: leftRev) (representedCells (first :: rest)) } =
      some
        { state := .moreReady
          tape :=
            { left := leftRev
              head := none
              right := representedCells (first :: rest) } } := by
  cases leftRev <;> cases rest <;> rfl

theorem more_round
    (D : MachineDescription)
    (remainingFuel : Nat)
    (masterFirst : MachineCodeSymbol)
    (masterRest suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (fuelDoneConfig D (remainingFuel + 2)
        (masterFirst :: masterRest)
        (List.append (masterFirst :: masterRest) suffix))
      (moreReadyConfig D (remainingFuel + 1)
        (masterFirst :: masterRest)
        (List.append (masterFirst :: masterRest) suffix)) := by
  let master := masterFirst :: masterRest
  let active := List.append master suffix
  let trail := fuelDoneTrail D master active
  have hdone : TuringMachine.Step machine
      (fuelDoneConfig D (remainingFuel + 2) master active)
      { state := .fuelFirstTick
        tape :=
          { left := List.replicate (remainingFuel + 1)
              (some MachineCodeSymbol.tick)
            head := some MachineCodeSymbol.tick
            right := some MachineCodeSymbol.done :: trail } } := by
    exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
      cases remainingFuel <;> cases masterRest <;> cases suffix <;> rfl)
  have hfirst : TuringMachine.Step machine
      { state := .fuelFirstTick
        tape :=
          { left := List.replicate (remainingFuel + 1)
              (some MachineCodeSymbol.tick)
            head := some MachineCodeSymbol.tick
            right := some MachineCodeSymbol.done :: trail } }
      (fuelTicksConfig (remainingFuel + 1)
        (some MachineCodeSymbol.tick ::
          some MachineCodeSymbol.done :: trail)) := by
    exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
      cases remainingFuel <;> cases masterRest <;> cases suffix <;> rfl)
  have hticks := fuelTicks_run (remainingFuel + 1)
    (some MachineCodeSymbol.tick :: some MachineCodeSymbol.done :: trail)
  have htoErase : TuringMachine.Step machine
      (fuelTicksConfig 0
        (List.replicate (remainingFuel + 1)
            (some MachineCodeSymbol.tick) ++
          some MachineCodeSymbol.tick ::
            some MachineCodeSymbol.done :: trail))
      { state := .eraseLastTick
        tape :=
          { left := [none]
            head := some MachineCodeSymbol.tick
            right := List.replicate (remainingFuel + 1)
                (some MachineCodeSymbol.tick) ++
              some MachineCodeSymbol.done :: trail } } := by
    exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
      have hright :
          List.replicate (remainingFuel + 1)
              (some MachineCodeSymbol.tick) ++
            some MachineCodeSymbol.tick ::
              some MachineCodeSymbol.done :: trail =
          some MachineCodeSymbol.tick ::
            (List.replicate (remainingFuel + 1)
                (some MachineCodeSymbol.tick) ++
              some MachineCodeSymbol.done :: trail) := by
        rw [replicate_tick_append_tick]
        simp [List.replicate_succ]
      rw [hright]
      exact fuelTicks_done_step MachineCodeSymbol.tick
        (List.replicate (remainingFuel + 1)
            (some MachineCodeSymbol.tick) ++
          some MachineCodeSymbol.done :: trail))
  have herase : TuringMachine.Step machine
      { state := .eraseLastTick
        tape :=
          { left := [none]
            head := some MachineCodeSymbol.tick
            right := List.replicate (remainingFuel + 1)
                (some MachineCodeSymbol.tick) ++
              some MachineCodeSymbol.done :: trail } }
      { state := .afterErase
        tape :=
          { left := [none, none]
            head := some MachineCodeSymbol.tick
            right := List.replicate remainingFuel
                (some MachineCodeSymbol.tick) ++
              some MachineCodeSymbol.done :: trail } } := by
    exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
      cases remainingFuel <;> cases masterRest <;> cases suffix <;> rfl)
  let baseReturn : Word MachineCodeSymbol :=
    List.replicate remainingFuel MachineCodeSymbol.tick ++
      MachineCodeSymbol.done :: MachineCodeSymbol.header ::
        (beforeFuel D).reverse
  let masterTail : List (Option MachineCodeSymbol) :=
    master.map some ++ none :: representedCells active
  have hreturnCells :
      List.replicate remainingFuel (some MachineCodeSymbol.tick) ++
          some MachineCodeSymbol.done :: trail =
        baseReturn.map some ++ none :: masterTail := by
    simp [baseReturn, masterTail, trail, fuelDoneTrail,
      List.map_append, List.append_assoc]
  have hafter : TuringMachine.Step machine
      { state := .afterErase
        tape :=
          { left := [none, none]
            head := some MachineCodeSymbol.tick
            right := List.replicate remainingFuel
                (some MachineCodeSymbol.tick) ++
              some MachineCodeSymbol.done :: trail } }
      (returnBaseConfig
        [some MachineCodeSymbol.tick, none, none]
        baseReturn masterTail) := by
    rw [hreturnCells]
    cases hreturn : baseReturn with
    | nil =>
        have hlength := congrArg List.length hreturn
        simp [baseReturn] at hlength
    | cons next more =>
        exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
          simpa [returnBaseConfig, rightCursorTape, hreturn,
            List.map_append, List.append_assoc] using
            afterErase_tick_step [none, none] next
              (more.map some ++ none :: masterTail))
  have hbase := returnBase_run
    [some MachineCodeSymbol.tick, none, none] baseReturn masterTail
  let baseLeft : List (Option MachineCodeSymbol) :=
    baseReturn.reverse.map some ++
      [some MachineCodeSymbol.tick, none, none]
  have hgap : TuringMachine.Step machine
      (returnBaseConfig baseLeft [] masterTail)
      (returnMasterConfig (none :: baseLeft) master
        (representedCells active)) := by
    exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
      cases masterRest <;> cases suffix <;> rfl)
  have hmaster := returnMaster_run (none :: baseLeft) master
    (representedCells active)
  have hactive : TuringMachine.Step machine
      (returnMasterConfig
        (master.reverse.map some ++ none :: baseLeft) []
        (representedCells active))
      { state := .returnBounce
        tape :=
          PersistentMasterCopier.tapeAtCells
            (none :: master.reverse.map some ++ none :: baseLeft)
            (representedCells active) } := by
    exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
      cases masterRest <;> cases suffix <;> rfl)
  have hbounce : TuringMachine.Step machine
      { state := .returnBounce
        tape :=
          PersistentMasterCopier.tapeAtCells
            (none :: master.reverse.map some ++ none :: baseLeft)
            (representedCells active) }
      (moreReadyConfig D (remainingFuel + 1) master active) := by
    have hbaseLeft : baseLeft =
        (positiveMaterializerCopierBaseLeftRev D
          (remainingFuel + 1)).map some ++ [none, none] := by
      have hticks := replicate_tick_append_tick remainingFuel [none, none]
      rw [positiveBase_eq]
      simp [baseLeft, baseReturn, List.reverse_append,
        List.reverse_replicate, List.map_append,
        List.replicate_succ, List.append_assoc, hticks]
    exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
      rw [hbaseLeft]
      have hactiveShape : active =
          masterFirst :: List.append masterRest suffix := by
        rfl
      rw [hactiveShape]
      let leftRev := master.reverse.map some ++
        (none ::
          ((positiveMaterializerCopierBaseLeftRev D
            (remainingFuel + 1)).map some ++ [none, none]))
      simpa only [moreReadyConfig, moreReadyTape, leftRev,
        List.cons_append, List.append_assoc] using
        returnBounce_step leftRev masterFirst
          (List.append masterRest suffix))
  have hrun := TuringMachine.Computes.step hdone
    (TuringMachine.Computes.refl _)
  have hrun := TuringMachine.computes_trans hrun
    (TuringMachine.Computes.step hfirst (TuringMachine.Computes.refl _))
  have hrun := TuringMachine.computes_trans hrun hticks
  have hrun := TuringMachine.computes_trans hrun
    (TuringMachine.Computes.step htoErase (TuringMachine.Computes.refl _))
  have hrun := TuringMachine.computes_trans hrun
    (TuringMachine.Computes.step herase (TuringMachine.Computes.refl _))
  have hrun := TuringMachine.computes_trans hrun
    (TuringMachine.Computes.step hafter (TuringMachine.Computes.refl _))
  have hrun := TuringMachine.computes_trans hrun hbase
  have hrun := TuringMachine.computes_trans hrun
    (TuringMachine.Computes.step hgap (TuringMachine.Computes.refl _))
  have hrun := TuringMachine.computes_trans hrun hmaster
  have hrun := TuringMachine.computes_trans hrun
    (TuringMachine.Computes.step hactive (TuringMachine.Computes.refl _))
  have hrun := TuringMachine.computes_trans hrun
    (TuringMachine.Computes.step hbounce (TuringMachine.Computes.refl _))
  simpa [master, active] using hrun

theorem beforeFuel_reverse_eq
    (D : MachineDescription) :
    (beforeFuel D).reverse =
      List.append (MachineDescription.encodeNat D.stateCount)
        (List.append (MachineDescription.encodeNat D.start)
          (nearStart D).reverse) := by
  simp [beforeFuel, List.reverse_append, List.append_assoc]

theorem afterErase_done_step
    (leftRev right : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        { state := .afterErase
          tape :=
            { left := leftRev
              head := some MachineCodeSymbol.done
              right := right } } =
      some
        { state := .finalHeader
          tape := PersistentMasterCopier.tapeAtCells
            (none :: leftRev) right } := by
  cases leftRev <;> cases right <;> rfl

theorem finalHeader_step
    (leftRev right : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        { state := .finalHeader
          tape :=
            { left := leftRev
              head := some MachineCodeSymbol.header
              right := right } } =
      some
        { state := .finalState
          tape := PersistentMasterCopier.tapeAtCells
            (none :: leftRev) right } := by
  cases leftRev <;> cases right <;> rfl

theorem finalState_tick_step
    (leftRev right : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        { state := .finalState
          tape := PersistentMasterCopier.tapeAtCells leftRev
            (some MachineCodeSymbol.tick :: right) } =
      some
        { state := .finalState
          tape := PersistentMasterCopier.tapeAtCells
            (none :: leftRev) right } := by
  cases leftRev <;> cases right <;> rfl

theorem finalState_done_step
    (leftRev right : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        { state := .finalState
          tape := PersistentMasterCopier.tapeAtCells leftRev
            (some MachineCodeSymbol.done :: right) } =
      some
        { state := .keepStart
          tape := PersistentMasterCopier.tapeAtCells
            (none :: leftRev) right } := by
  cases leftRev <;> cases right <;> rfl

theorem replicate_none_append_none
    (count : Nat)
    (tail : List (Option MachineCodeSymbol)) :
    List.replicate count none ++ none :: tail =
      List.replicate (count + 1) none ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa [List.replicate_succ] using
        congrArg (fun cells => none :: cells) ih

theorem replicate_none_add
    (left right : Nat) :
    List.replicate (left + right) (none : Option MachineCodeSymbol) =
      List.replicate left none ++ List.replicate right none := by
  exact (List.replicate_append_replicate
    (n := left) (m := right)
    (a := (none : Option MachineCodeSymbol))).symm

theorem finalState_run
    (leftRev right : List (Option MachineCodeSymbol))
    (value : Nat) :
    TuringMachine.Computes machine
      { state := .finalState
        tape := PersistentMasterCopier.tapeAtCells leftRev
          ((MachineDescription.encodeNat value).map some ++ right) }
      { state := .keepStart
        tape := PersistentMasterCopier.tapeAtCells
          (List.replicate (value + 1) none ++ leftRev) right } := by
  induction value generalizing leftRev with
  | zero =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp (by
          simpa [MachineDescription.encodeNat] using
            finalState_done_step leftRev right))
        (TuringMachine.Computes.refl _)
  | succ value ih =>
      have hstep : TuringMachine.Step machine
          { state := .finalState
            tape := PersistentMasterCopier.tapeAtCells leftRev
              ((MachineDescription.encodeNat (value + 1)).map some ++ right) }
          { state := .finalState
            tape := PersistentMasterCopier.tapeAtCells (none :: leftRev)
              ((MachineDescription.encodeNat value).map some ++ right) } :=
        TuringMachine.stepConfig_eq_some_iff_step.mp (by
          simpa [MachineDescription.encodeNat, List.map_append,
            List.append_assoc] using finalState_tick_step leftRev
              ((MachineDescription.encodeNat value).map some ++ right))
      have htail := ih (none :: leftRev)
      have hrun := TuringMachine.Computes.step hstep htail
      rw [replicate_none_append_none] at hrun
      exact hrun

theorem keepStart_tick_step
    (leftRev right : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        { state := .keepStart
          tape := PersistentMasterCopier.tapeAtCells leftRev
            (some MachineCodeSymbol.tick :: right) } =
      some
        { state := .keepStart
          tape := PersistentMasterCopier.tapeAtCells
            (some MachineCodeSymbol.tick :: leftRev) right } := by
  cases leftRev <;> cases right <;> rfl

theorem keepStart_done_step
    (leftRev right : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        { state := .keepStart
          tape := PersistentMasterCopier.tapeAtCells leftRev
            (some MachineCodeSymbol.done :: right) } =
      some
        { state := .sealStart
          tape := PersistentMasterCopier.tapeAtCells
            (some MachineCodeSymbol.done :: leftRev) right } := by
  cases leftRev <;> cases right <;> rfl

theorem keepStart_run
    (leftRev right : List (Option MachineCodeSymbol))
    (value : Nat) :
    TuringMachine.Computes machine
      { state := .keepStart
        tape := PersistentMasterCopier.tapeAtCells leftRev
          ((MachineDescription.encodeNat value).map some ++ right) }
      { state := .sealStart
        tape := PersistentMasterCopier.tapeAtCells
          ((MachineDescription.encodeNat value).reverse.map some ++ leftRev)
          right } := by
  induction value generalizing leftRev with
  | zero =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp (by
          simpa [MachineDescription.encodeNat] using
            keepStart_done_step leftRev right))
        (TuringMachine.Computes.refl _)
  | succ value ih =>
      have hstep : TuringMachine.Step machine
          { state := .keepStart
            tape := PersistentMasterCopier.tapeAtCells leftRev
              ((MachineDescription.encodeNat (value + 1)).map some ++ right) }
          { state := .keepStart
            tape := PersistentMasterCopier.tapeAtCells
              (some MachineCodeSymbol.tick :: leftRev)
              ((MachineDescription.encodeNat value).map some ++ right) } :=
        TuringMachine.stepConfig_eq_some_iff_step.mp (by
          simpa [MachineDescription.encodeNat, List.map_append,
            List.append_assoc] using keepStart_tick_step leftRev
              ((MachineDescription.encodeNat value).map some ++ right))
      have htail := ih (some MachineCodeSymbol.tick :: leftRev)
      simpa [MachineDescription.encodeNat, List.reverse_cons,
        List.map_append, List.append_assoc] using
        TuringMachine.Computes.step hstep htail

theorem sealStart_step
    (leftRev right : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol) :
    machine.stepConfig
        { state := .sealStart
          tape := PersistentMasterCopier.tapeAtCells leftRev
            (some current :: right) } =
      some
        { state := .eraseAfterStart
          tape := PersistentMasterCopier.tapeAtCells
            (some MachineCodeSymbol.header :: leftRev) right } := by
  cases current <;> cases leftRev <;> cases right <;> rfl

theorem eraseAfterStart_symbol_step
    (leftRev right : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol) :
    machine.stepConfig
        { state := .eraseAfterStart
          tape := PersistentMasterCopier.tapeAtCells leftRev
            (some current :: right) } =
      some
        { state := .eraseAfterStart
          tape := PersistentMasterCopier.tapeAtCells
            (none :: leftRev) right } := by
  cases current <;> cases leftRev <;> cases right <;> rfl

theorem eraseAfterStart_gap_step
    (leftRev right : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        { state := .eraseAfterStart
          tape := PersistentMasterCopier.tapeAtCells leftRev
            (none :: right) } =
      some
        { state := .eraseMaster
          tape := PersistentMasterCopier.tapeAtCells
            (none :: leftRev) right } := by
  cases leftRev <;> cases right <;> rfl

theorem eraseAfterStart_run
    (leftRev right : List (Option MachineCodeSymbol))
    (word : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      { state := .eraseAfterStart
        tape := PersistentMasterCopier.tapeAtCells leftRev
          (word.map some ++ none :: right) }
      { state := .eraseMaster
        tape := PersistentMasterCopier.tapeAtCells
          (List.replicate (word.length + 1) none ++ leftRev) right } := by
  induction word generalizing leftRev with
  | nil =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp (by
          simpa using eraseAfterStart_gap_step leftRev right))
        (TuringMachine.Computes.refl _)
  | cons current more ih =>
      have hstep : TuringMachine.Step machine
          { state := .eraseAfterStart
            tape := PersistentMasterCopier.tapeAtCells leftRev
              ((current :: more).map some ++ none :: right) }
          { state := .eraseAfterStart
            tape := PersistentMasterCopier.tapeAtCells (none :: leftRev)
              (more.map some ++ none :: right) } :=
        TuringMachine.stepConfig_eq_some_iff_step.mp (by
          simpa using eraseAfterStart_symbol_step leftRev
            (more.map some ++ none :: right) current)
      have htail := ih (none :: leftRev)
      have hrun := TuringMachine.Computes.step hstep htail
      rw [replicate_none_append_none] at hrun
      exact hrun

theorem sealAndEraseAfterStart_run
    (leftRev right : List (Option MachineCodeSymbol))
    (word : Word MachineCodeSymbol)
    (hword : word ≠ []) :
    TuringMachine.Computes machine
      { state := .sealStart
        tape := PersistentMasterCopier.tapeAtCells leftRev
          (word.map some ++ none :: right) }
      { state := .eraseMaster
        tape := PersistentMasterCopier.tapeAtCells
          (List.replicate word.length none ++
            some MachineCodeSymbol.header :: leftRev) right } := by
  cases word with
  | nil => contradiction
  | cons first rest =>
      have hseal : TuringMachine.Step machine
          { state := .sealStart
            tape := PersistentMasterCopier.tapeAtCells leftRev
              ((first :: rest).map some ++ none :: right) }
          { state := .eraseAfterStart
            tape := PersistentMasterCopier.tapeAtCells
              (some MachineCodeSymbol.header :: leftRev)
              (rest.map some ++ none :: right) } :=
        TuringMachine.stepConfig_eq_some_iff_step.mp (by
          simpa using sealStart_step leftRev
            (rest.map some ++ none :: right) first)
      have herase := eraseAfterStart_run
        (some MachineCodeSymbol.header :: leftRev) right rest
      exact TuringMachine.Computes.step hseal (by
        simpa using herase)

theorem nearStart_reverse_ne_nil
    (D : MachineDescription) : (nearStart D).reverse ≠ [] := by
  intro hnil
  have hlength := congrArg List.length hnil
  simp [nearStart] at hlength

theorem eraseMaster_symbol_step
    (leftRev right : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol) :
    machine.stepConfig
        { state := .eraseMaster
          tape := PersistentMasterCopier.tapeAtCells leftRev
            (some current :: right) } =
      some
        { state := .eraseMaster
          tape := PersistentMasterCopier.tapeAtCells
            (none :: leftRev) right } := by
  cases current <;> cases leftRev <;> cases right <;> rfl

theorem eraseMaster_gap_step
    (leftRev right : List (Option MachineCodeSymbol)) :
    machine.stepConfig
        { state := .eraseMaster
          tape := PersistentMasterCopier.tapeAtCells leftRev
            (none :: right) } =
      some
        { state := .compactReady
          tape := PersistentMasterCopier.tapeAtCells
            (none :: leftRev) right } := by
  cases leftRev <;> cases right <;> rfl

theorem eraseMaster_run
    (leftRev right : List (Option MachineCodeSymbol))
    (word : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      { state := .eraseMaster
        tape := PersistentMasterCopier.tapeAtCells leftRev
          (word.map some ++ none :: right) }
      { state := .compactReady
        tape := PersistentMasterCopier.tapeAtCells
          (List.replicate (word.length + 1) none ++ leftRev) right } := by
  induction word generalizing leftRev with
  | nil =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp (by
          simpa using eraseMaster_gap_step leftRev right))
        (TuringMachine.Computes.refl _)
  | cons current more ih =>
      have hstep : TuringMachine.Step machine
          { state := .eraseMaster
            tape := PersistentMasterCopier.tapeAtCells leftRev
              ((current :: more).map some ++ none :: right) }
          { state := .eraseMaster
            tape := PersistentMasterCopier.tapeAtCells (none :: leftRev)
              (more.map some ++ none :: right) } :=
        TuringMachine.stepConfig_eq_some_iff_step.mp (by
          simpa using eraseMaster_symbol_step leftRev
            (more.map some ++ none :: right) current)
      have htail := ih (none :: leftRev)
      have hrun := TuringMachine.Computes.step hstep htail
      rw [replicate_none_append_none] at hrun
      exact hrun

def finalCompactLeftRev
    (D : MachineDescription)
    (master : Word MachineCodeSymbol) :
    List (Option MachineCodeSymbol) :=
  List.replicate (master.length + 1) none ++
    List.replicate (nearStart D).length none ++
      some MachineCodeSymbol.header ::
        (MachineDescription.encodeNat D.start).reverse.map some ++
        List.replicate (D.stateCount + 1) none ++ [none, none, none, none]

def finalCompactTape
    (D : MachineDescription)
    (master active : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  PersistentMasterCopier.tapeAtCells
    (finalCompactLeftRev D master) (representedCells active)

theorem final_round
    (D : MachineDescription)
    (masterFirst : MachineCodeSymbol)
    (masterRest suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes machine
      (fuelDoneConfig D 1 (masterFirst :: masterRest)
        (List.append (masterFirst :: masterRest) suffix))
      { state := .compactReady
        tape := finalCompactTape D (masterFirst :: masterRest)
          (List.append (masterFirst :: masterRest) suffix) } := by
  let master := masterFirst :: masterRest
  let active := List.append master suffix
  let trail := fuelDoneTrail D master active
  have hdone : TuringMachine.Step machine
      (fuelDoneConfig D 1 master active)
      { state := .fuelFirstTick
        tape :=
          { left := []
            head := some MachineCodeSymbol.tick
            right := some MachineCodeSymbol.done :: trail } } :=
    TuringMachine.stepConfig_eq_some_iff_step.mp (by
      cases masterRest <;> cases suffix <;> rfl)
  have hfirst : TuringMachine.Step machine
      { state := .fuelFirstTick
        tape :=
          { left := []
            head := some MachineCodeSymbol.tick
            right := some MachineCodeSymbol.done :: trail } }
      (fuelTicksConfig 0
        (some MachineCodeSymbol.tick ::
          some MachineCodeSymbol.done :: trail)) :=
    TuringMachine.stepConfig_eq_some_iff_step.mp (by
      cases masterRest <;> cases suffix <;> rfl)
  have htoErase : TuringMachine.Step machine
      (fuelTicksConfig 0
        (some MachineCodeSymbol.tick ::
          some MachineCodeSymbol.done :: trail))
      { state := .eraseLastTick
        tape :=
          { left := [none]
            head := some MachineCodeSymbol.tick
            right := some MachineCodeSymbol.done :: trail } } :=
    TuringMachine.stepConfig_eq_some_iff_step.mp
      (fuelTicks_done_step MachineCodeSymbol.tick
        (some MachineCodeSymbol.done :: trail))
  have herase : TuringMachine.Step machine
      { state := .eraseLastTick
        tape :=
          { left := [none]
            head := some MachineCodeSymbol.tick
            right := some MachineCodeSymbol.done :: trail } }
      { state := .afterErase
        tape :=
          { left := [none, none]
            head := some MachineCodeSymbol.done
            right := trail } } :=
    TuringMachine.stepConfig_eq_some_iff_step.mp (by
      cases masterRest <;> cases suffix <;> rfl)
  have hdoneErase : TuringMachine.Step machine
      { state := .afterErase
        tape :=
          { left := [none, none]
            head := some MachineCodeSymbol.done
            right := trail } }
      { state := .finalHeader
        tape := PersistentMasterCopier.tapeAtCells
          [none, none, none] trail } :=
    TuringMachine.stepConfig_eq_some_iff_step.mp (by
      simpa using afterErase_done_step [none, none] trail)
  let afterStart : List (Option MachineCodeSymbol) :=
    (nearStart D).reverse.map some ++
      none :: master.map some ++ none :: representedCells active
  let afterState : List (Option MachineCodeSymbol) :=
    (MachineDescription.encodeNat D.start).map some ++ afterStart
  have htrail : trail =
      some MachineCodeSymbol.header ::
        (MachineDescription.encodeNat D.stateCount).map some ++ afterState := by
    simp [trail, fuelDoneTrail, afterState, afterStart,
      beforeFuel_reverse_eq, List.map_append, List.append_assoc]
  have hheader : TuringMachine.Step machine
      { state := .finalHeader
        tape := PersistentMasterCopier.tapeAtCells
          [none, none, none] trail }
      { state := .finalState
        tape := PersistentMasterCopier.tapeAtCells
          [none, none, none, none]
          ((MachineDescription.encodeNat D.stateCount).map some ++
            afterState) } := by
    rw [htrail]
    exact TuringMachine.stepConfig_eq_some_iff_step.mp (by
      simpa [PersistentMasterCopier.tapeAtCells] using
        finalHeader_step [none, none, none]
        ((MachineDescription.encodeNat D.stateCount).map some ++ afterState))
  have hstate := finalState_run [none, none, none, none]
    afterState D.stateCount
  have hstart := keepStart_run
    (List.replicate (D.stateCount + 1) none ++
      [none, none, none, none]) afterStart D.start
  let startLeft : List (Option MachineCodeSymbol) :=
    (MachineDescription.encodeNat D.start).reverse.map some ++
      List.replicate (D.stateCount + 1) none ++ [none, none, none, none]
  let masterCells : List (Option MachineCodeSymbol) :=
    master.map some ++ none :: representedCells active
  have hsealErase := sealAndEraseAfterStart_run startLeft masterCells
    (nearStart D).reverse (nearStart_reverse_ne_nil D)
  let afterMasterLeft : List (Option MachineCodeSymbol) :=
    List.replicate (nearStart D).reverse.length none ++
      some MachineCodeSymbol.header :: startLeft
  have heraseMaster := eraseMaster_run afterMasterLeft
    (representedCells active) master
  have hrun := TuringMachine.Computes.step hdone
    (TuringMachine.Computes.refl _)
  have hrun := TuringMachine.computes_trans hrun
    (TuringMachine.Computes.step hfirst (TuringMachine.Computes.refl _))
  have hrun := TuringMachine.computes_trans hrun
    (TuringMachine.Computes.step htoErase (TuringMachine.Computes.refl _))
  have hrun := TuringMachine.computes_trans hrun
    (TuringMachine.Computes.step herase (TuringMachine.Computes.refl _))
  have hrun := TuringMachine.computes_trans hrun
    (TuringMachine.Computes.step hdoneErase (TuringMachine.Computes.refl _))
  have hrun := TuringMachine.computes_trans hrun
    (TuringMachine.Computes.step hheader (TuringMachine.Computes.refl _))
  have hrun := TuringMachine.computes_trans hrun hstate
  have hrun := TuringMachine.computes_trans hrun (by
    simpa [afterState] using hstart)
  have hrun := TuringMachine.computes_trans hrun (by
    simpa [afterStart, startLeft, masterCells, List.append_assoc] using
      hsealErase)
  have hrun := TuringMachine.computes_trans hrun (by
    simpa [afterMasterLeft, startLeft, masterCells,
      List.length_reverse, List.append_assoc] using heraseMaster)
  simpa [master, active, finalCompactTape, finalCompactLeftRev,
    afterMasterLeft, startLeft, List.length_reverse,
    replicate_none_add, List.append_assoc] using hrun

end CopyDriver

end FiniteRecognizer.Interpreter.PositiveInitializerPhase

end Computability
end FoC
