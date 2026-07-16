import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.Positive.Compact
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.Common.PhaseRetarget

namespace FoC
namespace Computability

open Languages

namespace Section53PositiveInitializerMachine

open FiniteRecognizer ExactFuel StrictProbe
open Section53InitializerFrontier
open Section53InitializerPersistentCopy
open Section53InitializerPersistentCopy.PersistentMasterCopier
open Section53InitializerRepeatedCopy
open Section53LoopRestagingAudit
open Section53BoundedLoopInduction
open Section53UniformInterpreterOneStep
open Section53UniformInterpreterOneStep.RuntimeKeySingleKeyRepair
open Section53PositiveInitializerPhase

namespace Machine

inductive Control where
  | materializer
      (saved : Option MachineCodeSymbol)
      (inner : Section53BooleanContextPhase.Machine.Control)
  | copier
      (saved : Option MachineCodeSymbol)
      (inner : PersistentMasterCopier.Control)
  | driver
      (saved : Option MachineCodeSymbol)
      (inner : CopyDriver.Control)
  | compactor
      (saved : Option MachineCodeSymbol)
      (inner : GapCompactor.Control)
  | restager (inner : NextCopyRestager.Control)
  | ready
  | halt
deriving DecidableEq

namespace Control

def savedOptions : List (Option MachineCodeSymbol) :=
  none :: MachineCodeSymbol.finite.elems.map some

theorem savedOptions_complete
    (saved : Option MachineCodeSymbol) : saved ∈ savedOptions := by
  cases saved with
  | none => simp [savedOptions]
  | some symbol =>
      simp [savedOptions, MachineCodeSymbol.finite.complete symbol]

def savedInnerControls
    {inner : Type}
    (innerElems : List inner)
    (f : Option MachineCodeSymbol -> inner -> Control) : List Control :=
  savedOptions.flatMap fun saved => innerElems.map (f saved)

theorem savedInnerControls_complete
    {inner : Type}
    (innerElems : List inner)
    (hinner : forall value : inner, value ∈ innerElems)
    (f : Option MachineCodeSymbol -> inner -> Control)
    (saved : Option MachineCodeSymbol)
    (value : inner) :
    f saved value ∈ savedInnerControls innerElems f := by
  apply List.mem_flatMap.mpr
  refine ⟨saved, savedOptions_complete saved, ?_⟩
  exact List.mem_map.mpr ⟨value, hinner value, rfl⟩

def elems : List Control :=
  savedInnerControls
      Section53BooleanContextPhase.Machine.Control.finite.elems materializer ++
    savedInnerControls PersistentMasterCopier.Control.finite.elems copier ++
    savedInnerControls CopyDriver.Control.finite.elems driver ++
    savedInnerControls GapCompactor.Control.finite.elems compactor ++
    NextCopyRestager.Control.finite.elems.map restager ++
    [.ready, .halt]

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | materializer saved inner =>
        simp [elems, savedInnerControls_complete _
          Section53BooleanContextPhase.Machine.Control.finite.complete
          materializer saved inner]
    | copier saved inner =>
        simp [elems, savedInnerControls_complete _
          PersistentMasterCopier.Control.finite.complete copier saved inner]
    | driver saved inner =>
        simp [elems, savedInnerControls_complete _
          CopyDriver.Control.finite.complete driver saved inner]
    | compactor saved inner =>
        simp [elems, savedInnerControls_complete _
          GapCompactor.Control.finite.complete compactor saved inner]
    | restager inner =>
        simp [elems, NextCopyRestager.Control.finite.complete inner]
    | ready => simp [elems]
    | halt => simp [elems]

end Control

def liftMaterializerControl
    (saved : Option MachineCodeSymbol)
    (inner : Section53BooleanContextPhase.Machine.Control) : Control :=
  if inner = Section53BooleanContextPhase.Machine.halt then
    .copier saved PersistentMasterCopier.Control.enter
  else
    .materializer saved inner

def liftCopierControl
    (saved : Option MachineCodeSymbol) :
    PersistentMasterCopier.Control -> Control
  | .ready => .driver saved CopyDriver.Control.fromReady
  | inner => .copier saved inner

def liftDriverControl
    (saved : Option MachineCodeSymbol) : CopyDriver.Control -> Control
  | .moreReady => .copier saved PersistentMasterCopier.Control.enter
  | .compactReady => .compactor saved GapCompactor.Control.enter
  | inner => .driver saved inner

def savedRead
    (saved : Option MachineCodeSymbol) : Option Bool :=
  saved.map Section53InitializerFrontier.codeSymbolFirstBit

def liftCompactorControl
    (saved : Option MachineCodeSymbol) : GapCompactor.Control -> Control
  | .ready => .restager (NextCopyRestager.Control.target (savedRead saved))
  | inner => .compactor saved inner

def liftRestagerControl : NextCopyRestager.Control -> Control
  | .ready _ => .ready
  | inner => .restager inner

def mapAction
    {inner : Type}
    (lift : inner -> Control) :
    (Option MachineCodeSymbol × Direction × inner) ->
      (Option MachineCodeSymbol × Direction × Control)
  | (write, direction, target) => (write, direction, lift target)

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .materializer saved inner, read =>
      Option.map (mapAction (liftMaterializerControl saved))
        (Section53BooleanContextPhase.Machine.transition inner read)
  | .copier saved inner, read =>
      Option.map (mapAction (liftCopierControl saved))
        (PersistentMasterCopier.transition inner read)
  | .driver saved inner, read =>
      Option.map (mapAction (liftDriverControl saved))
        (CopyDriver.transition inner read)
  | .compactor saved inner, read =>
      Option.map (mapAction (liftCompactorControl saved))
        (GapCompactor.transition inner read)
  | .restager inner, read =>
      Option.map (mapAction liftRestagerControl)
        (NextCopyRestager.transition inner read)
  | _, _ => none

def entry (saved : Option MachineCodeSymbol) : Control :=
  liftMaterializerControl saved
    (Section53BooleanContextPhase.Machine.entry saved)

def ready : Control := .ready

def machine : TuringMachine MachineCodeSymbol Control where
  start := entry none
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def materializerConfig
    (saved : Option MachineCodeSymbol)
    (config : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextPhase.Machine.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := liftMaterializerControl saved config.state, tape := config.tape }

def copierConfig
    (saved : Option MachineCodeSymbol)
    (config : TuringMachine.Configuration MachineCodeSymbol
      PersistentMasterCopier.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := liftCopierControl saved config.state, tape := config.tape }

def driverConfig
    (saved : Option MachineCodeSymbol)
    (config : TuringMachine.Configuration MachineCodeSymbol
      CopyDriver.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := liftDriverControl saved config.state, tape := config.tape }

def compactorConfig
    (saved : Option MachineCodeSymbol)
    (config : TuringMachine.Configuration MachineCodeSymbol
      GapCompactor.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := liftCompactorControl saved config.state, tape := config.tape }

def restagerConfig
    (config : TuringMachine.Configuration MachineCodeSymbol
      NextCopyRestager.Control) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := liftRestagerControl config.state, tape := config.tape }

end Machine

theorem computes_of_tape_equiv
    {state : Type}
    {innerMachine : TuringMachine MachineCodeSymbol state}
    {source target : TuringMachine.Configuration MachineCodeSymbol state}
    (hrun : TuringMachine.Computes innerMachine source target)
    (tape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv source.tape tape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes innerMachine
        { state := source.state, tape := tape }
        { state := target.state, tape := targetTape } ∧
      Tape.Equiv target.tape targetTape := by
  rcases TuringMachine.computes_to_computesIn hrun with
    ⟨steps, hcanonical⟩
  rcases TuringMachine.TapeEquivTransport.computesIn_of_tape_equiv
      hcanonical hsource with
    ⟨actualTarget, hactual, hstate, htape⟩
  rcases actualTarget with ⟨actualState, targetTape⟩
  simp only at hstate
  subst actualState
  exact ⟨targetTape, TuringMachine.computesIn_to_computes hactual, htape⟩

theorem computes_lift_active
    {innerState : Type}
    {innerMachine : TuringMachine MachineCodeSymbol innerState}
    (embed : innerState -> Machine.Control)
    (hstep : forall
      (source target : TuringMachine.Configuration MachineCodeSymbol
        innerState),
      innerMachine.stepConfig source = some target ->
        Machine.machine.stepConfig
            (TuringMachine.PhaseEmbedding.liftConfig embed source) =
          some (TuringMachine.PhaseEmbedding.liftConfig embed target))
    {source target : TuringMachine.Configuration MachineCodeSymbol innerState}
    (hrun : TuringMachine.Computes innerMachine source target) :
    TuringMachine.Computes Machine.machine
      (TuringMachine.PhaseEmbedding.liftConfig embed source)
      (TuringMachine.PhaseEmbedding.liftConfig embed target) := by
  induction hrun with
  | refl config => exact TuringMachine.Computes.refl _
  | step hfirst hrest ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (hstep _ _ (TuringMachine.stepConfig_eq_some_iff_step.mpr hfirst)))
        ih

namespace Machine

theorem copier_step_active
    (saved : Option MachineCodeSymbol)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      PersistentMasterCopier.Control)
    (hstep : PersistentMasterCopier.machine.stepConfig source = some target) :
    machine.stepConfig
        (TuringMachine.PhaseEmbedding.liftConfig
          (liftCopierControl saved) source) =
      some
        (TuringMachine.PhaseEmbedding.liftConfig
          (liftCopierControl saved) target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [PersistentMasterCopier.machine] at hstep
      cases htransition : PersistentMasterCopier.transition inner
          (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          have hsourceLift : liftCopierControl saved inner =
              .copier saved inner := by
            cases inner <;> try rfl
            simp [PersistentMasterCopier.transition] at htransition
          cases hstep
          simp [machine, transition, TuringMachine.PhaseEmbedding.liftConfig,
            hsourceLift, htransition, mapAction]

theorem copier_computes_lift
    (saved : Option MachineCodeSymbol)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      PersistentMasterCopier.Control}
    (hrun : TuringMachine.Computes PersistentMasterCopier.machine
      source target) :
    TuringMachine.Computes machine
      (copierConfig saved source) (copierConfig saved target) := by
  simpa [copierConfig,
    TuringMachine.PhaseEmbedding.liftConfig] using
    computes_lift_active (liftCopierControl saved)
      (copier_step_active saved) hrun

theorem driver_step_active
    (saved : Option MachineCodeSymbol)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      CopyDriver.Control)
    (hstep : CopyDriver.machine.stepConfig source = some target) :
    machine.stepConfig
        (TuringMachine.PhaseEmbedding.liftConfig
          (liftDriverControl saved) source) =
      some
        (TuringMachine.PhaseEmbedding.liftConfig
          (liftDriverControl saved) target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [CopyDriver.machine] at hstep
      cases htransition : CopyDriver.transition inner (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          have hsourceLift : liftDriverControl saved inner =
              .driver saved inner := by
            cases inner <;> try rfl
            all_goals
              cases hread : Tape.read tape with
              | none =>
                  simp [CopyDriver.transition] at htransition
              | some symbol =>
                  cases symbol <;>
                    simp [CopyDriver.transition] at htransition
          cases hstep
          simp [machine, transition, TuringMachine.PhaseEmbedding.liftConfig,
            hsourceLift, htransition, mapAction]

theorem driver_computes_lift
    (saved : Option MachineCodeSymbol)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      CopyDriver.Control}
    (hrun : TuringMachine.Computes CopyDriver.machine source target) :
    TuringMachine.Computes machine
      (driverConfig saved source) (driverConfig saved target) := by
  simpa [driverConfig,
    TuringMachine.PhaseEmbedding.liftConfig] using
    computes_lift_active (liftDriverControl saved)
      (driver_step_active saved) hrun

end Machine

def compactorRest
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (context : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append
    (MachineDescription.encodeTransitions (first :: rest)).tail
    (MachineCodeSymbol.header ::
      Section53InitializerRepeatedCopy.stackSuffix
        (first :: rest) copies context)

theorem savedRead_savedHead_eq_initial_read
    (input : Word MachineCodeSymbol) :
    Machine.savedRead (transitionListParserSavedHead input) =
      Tape.read (initialTape input) := by
  cases input with
  | nil => rfl
  | cons symbol rest =>
      cases symbol <;> rfl

theorem restagerTarget_tape_eq_loopSource
    (D : MachineDescription)
    (input : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (remaining : Nat) :
    (NextCopyRestager.targetConfig
      (Machine.savedRead (transitionListParserSavedHead input)) D.start
      (MachineCodeSymbol.transition ::
        compactorRest first rest remaining
          (positiveInitialContextTail D input))).tape =
      (loopSourceConfig (initialConfiguration D input)
        (first :: rest) remaining D.halt []).tape := by
  have hinitial : initialConfiguration D input =
      { state := D.start, tape := initialTape input } := by
    rfl
  let table := MachineDescription.encodeTransitions (first :: rest)
  let tail := MachineCodeSymbol.header ::
    (List.append (tableStack (first :: rest) remaining)
      (protectedTapeContextsAppend (initialTape input)
        (MachineDescription.encodeNatAppend D.halt [])))
  have htableHead : table = MachineCodeSymbol.transition :: table.tail := by
    rfl
  have htableAppend : List.append table tail =
      MachineDescription.encodeTransitionsAppend (first :: rest) tail := by
    simpa [table, MachineDescription.encodeTransitions] using
      MachineDescription.encodeTransitionsAppend_append
        (first :: rest) [] tail
  have hword : MachineCodeSymbol.transition ::
      (List.append table.tail tail) =
      MachineDescription.encodeTransitionsAppend (first :: rest) tail := by
    calc
      MachineCodeSymbol.transition :: List.append table.tail tail =
          List.append (MachineCodeSymbol.transition :: table.tail) tail := by
        rfl
      _ = List.append table tail :=
        (congrArg (fun word : Word MachineCodeSymbol =>
          List.append word tail) htableHead).symm
      _ = MachineDescription.encodeTransitionsAppend (first :: rest) tail :=
        htableAppend
  have hcompactor :
      compactorRest first rest remaining
          (positiveInitialContextTail D input) =
        List.append table.tail tail := by
    rfl
  rw [savedRead_savedHead_eq_initial_read]
  rw [hinitial]
  rw [hcompactor]
  rw [hword]
  simp [NextCopyRestager.targetConfig, loopSourceConfig,
    canonicalScanRowsConfig, initialConfiguration,
    activeProtectedSuffix, Section53LoopRestagingAudit.contextTail,
    compactorRest, stackSuffix, positiveInitialContextTail,
    SerializedShift.cursorTape, runtimeKeyComparatorTape,
    MachineDescription.encodeTransitionsAppend, processedRows,
    tail, List.append_assoc]
  rfl

theorem copy_remaining
    (saved : Option MachineCodeSymbol)
    (D : MachineDescription)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (remaining copies : Nat)
    (context : Word MachineCodeSymbol)
    (tape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (copyPassSource
        (positiveMaterializerCopierBaseLeftRev D (remaining + 1))
        first rest copies context).tape tape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes Machine.machine
        { state := Machine.Control.copier saved
            PersistentMasterCopier.Control.enter
          tape := tape }
        { state := Machine.Control.compactor saved GapCompactor.Control.enter
          tape := targetTape } ∧
      Tape.Equiv
        (GapCompactor.sourceConfig
          (List.append (MachineDescription.encodeNat D.start)
            [MachineCodeSymbol.header])
          (GapCompactor.cleanupGap D
            (MachineDescription.encodeTransitions (first :: rest)))
          MachineCodeSymbol.transition
          (compactorRest first rest (copies + remaining) context)).tape
        targetTape := by
  let base := positiveMaterializerCopierBaseLeftRev D (remaining + 1)
  let master := MachineDescription.encodeTransitions (first :: rest)
  let suffix := MachineCodeSymbol.header ::
    stackSuffix (first :: rest) copies context
  have hcopyCanonical : TuringMachine.Computes
      PersistentMasterCopier.machine
      (copyPassSource base first rest copies context)
      (copyPassTarget base first rest copies context) :=
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
        (copyPass_run_exact base first rest copies context))
  rcases computes_of_tape_equiv hcopyCanonical tape (by
      simpa [base] using hsource) with
    ⟨copyTape, hcopy, hcopyShape⟩
  have hcopyOuter := Machine.copier_computes_lift saved hcopy
  have hreachCanonical := CopyDriver.reachesFuelDone D (remaining + 1)
    MachineCodeSymbol.transition master.tail suffix
  have hmaster : master = MachineCodeSymbol.transition :: master.tail := by
    rfl
  have hactive : List.append master suffix =
      stackSuffix (first :: rest) (copies + 1) context := by
    simpa [master, suffix] using
      copiedActiveWord_eq_stackSuffix_succ (first :: rest) copies context
  have hreachCanonical' : TuringMachine.Computes CopyDriver.machine
      { state := CopyDriver.Control.fromReady
        tape := (copyPassTarget base first rest copies context).tape }
      (CopyDriver.fuelDoneConfig D (remaining + 1) master
        (stackSuffix (first :: rest) (copies + 1) context)) := by
    rw [← hmaster] at hreachCanonical
    rw [hactive] at hreachCanonical
    simpa [base, copyPassTarget,
      PersistentMasterCopier.readyConfig] using hreachCanonical
  rcases computes_of_tape_equiv hreachCanonical' copyTape hcopyShape with
    ⟨fuelTape, hreach, hreachShape⟩
  have hreachOuter := Machine.driver_computes_lift saved hreach
  cases remaining with
  | zero =>
      have hfinalCanonical := CopyDriver.final_round D
        MachineCodeSymbol.transition master.tail suffix
      have hfinalCanonical' : TuringMachine.Computes CopyDriver.machine
          (CopyDriver.fuelDoneConfig D 1 master
            (stackSuffix (first :: rest) (copies + 1) context))
          { state := CopyDriver.Control.compactReady
            tape := CopyDriver.finalCompactTape D master
              (stackSuffix (first :: rest) (copies + 1) context) } := by
        rw [← hmaster] at hfinalCanonical
        rw [hactive] at hfinalCanonical
        exact hfinalCanonical
      rcases computes_of_tape_equiv hfinalCanonical' fuelTape
          (by simpa using hreachShape) with
        ⟨finalTape, hfinal, hfinalShape⟩
      have hfinalOuter := Machine.driver_computes_lift saved hfinal
      have hcompactCanonical :=
        GapCompactor.finalCompactTape_equiv_source D master.tail suffix
      have hcompact : Tape.Equiv
          (GapCompactor.sourceConfig
            (List.append (MachineDescription.encodeNat D.start)
              [MachineCodeSymbol.header])
            (GapCompactor.cleanupGap D master)
            MachineCodeSymbol.transition
            (compactorRest first rest copies context)).tape
          (CopyDriver.finalCompactTape D master
            (stackSuffix (first :: rest) (copies + 1) context)) := by
        rw [← hmaster] at hcompactCanonical
        rw [hactive] at hcompactCanonical
        simpa [compactorRest, master, suffix] using hcompactCanonical
      refine ⟨finalTape, ?_, Tape.Equiv.trans hcompact hfinalShape⟩
      have hrun := TuringMachine.computes_trans hcopyOuter hreachOuter
      have hrun := TuringMachine.computes_trans hrun hfinalOuter
      simpa [Machine.copierConfig, Machine.driverConfig,
        Machine.compactorConfig, Machine.liftCopierControl,
        Machine.liftDriverControl, copyPassSource,
        PersistentMasterCopier.sourceConfig, base] using hrun
  | succ nextRemaining =>
      have hmoreCanonical := CopyDriver.more_round D nextRemaining
        MachineCodeSymbol.transition master.tail suffix
      have hmoreCanonical' : TuringMachine.Computes CopyDriver.machine
          (CopyDriver.fuelDoneConfig D (nextRemaining + 2) master
            (stackSuffix (first :: rest) (copies + 1) context))
          (CopyDriver.moreReadyConfig D (nextRemaining + 1) master
            (stackSuffix (first :: rest) (copies + 1) context)) := by
        rw [← hmaster] at hmoreCanonical
        rw [hactive] at hmoreCanonical
        exact hmoreCanonical
      rcases computes_of_tape_equiv hmoreCanonical' fuelTape
          (by simpa using hreachShape) with
        ⟨moreTape, hmore, hmoreShape⟩
      have hmoreOuter := Machine.driver_computes_lift saved hmore
      have hnextSource : Tape.Equiv
          (copyPassSource
            (positiveMaterializerCopierBaseLeftRev D (nextRemaining + 1))
            first rest (copies + 1) context).tape
          (CopyDriver.moreReadyConfig D (nextRemaining + 1) master
            (stackSuffix (first :: rest) (copies + 1) context)).tape := by
        simpa only [copyPassSource, PersistentMasterCopier.sourceConfig,
          CopyDriver.moreReadyConfig, master] using
          CopyDriver.moreReadyTape_equiv_source D (nextRemaining + 1)
            master (stackSuffix (first :: rest) (copies + 1) context)
      have hnextActual := Tape.Equiv.trans hnextSource hmoreShape
      rcases copy_remaining saved D first rest nextRemaining (copies + 1)
          context moreTape hnextActual with
        ⟨targetTape, htail, htargetShape⟩
      refine ⟨targetTape, ?_, ?_⟩
      · have hrun := TuringMachine.computes_trans hcopyOuter hreachOuter
        have hrun := TuringMachine.computes_trans hrun hmoreOuter
        have hrun := TuringMachine.computes_trans hrun htail
        simpa [Machine.copierConfig, Machine.driverConfig,
          Machine.liftCopierControl, Machine.liftDriverControl,
          copyPassSource, PersistentMasterCopier.sourceConfig, base] using hrun
      · have hcount : copies + (nextRemaining + 1) =
            (copies + 1) + nextRemaining := by
          lia
        simpa [hcount] using htargetShape

namespace Machine

theorem materializer_step_of_some
    (saved : Option MachineCodeSymbol)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextPhase.Machine.Control)
    (hstep : Section53BooleanContextPhase.Machine.machine.stepConfig
      source = some target) :
    machine.stepConfig (materializerConfig saved source) =
      some (materializerConfig saved target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [Section53BooleanContextPhase.Machine.machine] at hstep
      cases htransition :
          Section53BooleanContextPhase.Machine.transition inner
            (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          have hsourceLift : liftMaterializerControl saved inner =
              .materializer saved inner := by
            rw [liftMaterializerControl, if_neg]
            intro heq
            subst inner
            simp [Section53BooleanContextPhase.Machine.halt,
              Section53BooleanContextPhase.Machine.transition,
              Section53BooleanContextSeparatorConverter.Machine.transition]
              at htransition
          cases hstep
          simp [machine, transition, materializerConfig, hsourceLift,
            htransition, mapAction]

theorem materializer_computes_lift
    (saved : Option MachineCodeSymbol)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      Section53BooleanContextPhase.Machine.Control}
    (hrun : TuringMachine.Computes
      Section53BooleanContextPhase.Machine.machine source target) :
    TuringMachine.Computes machine
      (materializerConfig saved source) (materializerConfig saved target) := by
  induction hrun with
  | refl config => exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (materializer_step_of_some saved _ _
            (TuringMachine.stepConfig_eq_some_iff_step.mpr hstep)))
        ih

theorem copier_step_of_some
    (saved : Option MachineCodeSymbol)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      PersistentMasterCopier.Control)
    (hstep : PersistentMasterCopier.machine.stepConfig source = some target) :
    machine.stepConfig (copierConfig saved source) =
      some (copierConfig saved target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [PersistentMasterCopier.machine] at hstep
      cases htransition : PersistentMasterCopier.transition inner
          (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          have hsourceLift : liftCopierControl saved inner =
              .copier saved inner := by
            cases inner <;> try rfl
            simp [PersistentMasterCopier.transition] at htransition
          cases hstep
          simp [machine, transition, copierConfig, hsourceLift,
            htransition, mapAction]

theorem copier_computes_lift_late
    (saved : Option MachineCodeSymbol)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      PersistentMasterCopier.Control}
    (hrun : TuringMachine.Computes PersistentMasterCopier.machine
      source target) :
    TuringMachine.Computes machine
      (copierConfig saved source) (copierConfig saved target) := by
  induction hrun with
  | refl config => exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (copier_step_of_some saved _ _
            (TuringMachine.stepConfig_eq_some_iff_step.mpr hstep)))
        ih

theorem driver_step_of_some
    (saved : Option MachineCodeSymbol)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      CopyDriver.Control)
    (hstep : CopyDriver.machine.stepConfig source = some target) :
    machine.stepConfig (driverConfig saved source) =
      some (driverConfig saved target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [CopyDriver.machine] at hstep
      cases htransition : CopyDriver.transition inner (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          have hsourceLift : liftDriverControl saved inner =
              .driver saved inner := by
            cases inner <;> try rfl
            all_goals
              cases hread : Tape.read tape with
              | none =>
                  simp [CopyDriver.transition, hread] at htransition
              | some symbol =>
                  cases symbol <;>
                    simp [CopyDriver.transition, hread] at htransition
          cases hstep
          simp [machine, transition, driverConfig, hsourceLift,
            htransition, mapAction]

theorem driver_computes_lift_late
    (saved : Option MachineCodeSymbol)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      CopyDriver.Control}
    (hrun : TuringMachine.Computes CopyDriver.machine source target) :
    TuringMachine.Computes machine
      (driverConfig saved source) (driverConfig saved target) := by
  induction hrun with
  | refl config => exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (driver_step_of_some saved _ _
            (TuringMachine.stepConfig_eq_some_iff_step.mpr hstep)))
        ih

theorem compactor_step_of_some
    (saved : Option MachineCodeSymbol)
    (source target : TuringMachine.Configuration MachineCodeSymbol
      GapCompactor.Control)
    (hstep : GapCompactor.machine.stepConfig source = some target) :
    machine.stepConfig (compactorConfig saved source) =
      some (compactorConfig saved target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [GapCompactor.machine] at hstep
      cases htransition : GapCompactor.transition inner (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          have hsourceLift : liftCompactorControl saved inner =
              .compactor saved inner := by
            cases inner <;> try rfl
            simp [GapCompactor.transition] at htransition
          cases hstep
          simp [machine, transition, compactorConfig, hsourceLift,
            htransition, mapAction]

theorem compactor_computes_lift
    (saved : Option MachineCodeSymbol)
    {source target : TuringMachine.Configuration MachineCodeSymbol
      GapCompactor.Control}
    (hrun : TuringMachine.Computes GapCompactor.machine source target) :
    TuringMachine.Computes machine
      (compactorConfig saved source) (compactorConfig saved target) := by
  induction hrun with
  | refl config => exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (compactor_step_of_some saved _ _
            (TuringMachine.stepConfig_eq_some_iff_step.mpr hstep)))
        ih

theorem restager_step_of_some
    (source target : TuringMachine.Configuration MachineCodeSymbol
      NextCopyRestager.Control)
    (hstep : NextCopyRestager.machine.stepConfig source = some target) :
    machine.stepConfig (restagerConfig source) =
      some (restagerConfig target) := by
  cases source with
  | mk inner tape =>
      unfold TuringMachine.stepConfig at hstep ⊢
      dsimp [NextCopyRestager.machine] at hstep
      cases htransition : NextCopyRestager.transition inner (Tape.read tape) with
      | none => simp [htransition] at hstep
      | some action =>
          rcases action with ⟨write, direction, next⟩
          simp only [htransition] at hstep
          have hsourceLift : liftRestagerControl inner = .restager inner := by
            cases inner <;> try rfl
            simp [NextCopyRestager.transition] at htransition
          cases hstep
          simp [machine, transition, restagerConfig, hsourceLift,
            htransition, mapAction]

theorem restager_computes_lift
    {source target : TuringMachine.Configuration MachineCodeSymbol
      NextCopyRestager.Control}
    (hrun : TuringMachine.Computes NextCopyRestager.machine source target) :
    TuringMachine.Computes machine
      (restagerConfig source) (restagerConfig target) := by
  induction hrun with
  | refl config => exact TuringMachine.Computes.refl _
  | step hstep hrest ih =>
      exact TuringMachine.Computes.step
        (TuringMachine.stepConfig_eq_some_iff_step.mp
          (restager_step_of_some _ _
            (TuringMachine.stepConfig_eq_some_iff_step.mpr hstep)))
        ih

end Machine

theorem positive_nonempty_computes_from_parser_tape
    (D : MachineDescription)
    (remaining : Nat)
    (input : Word MachineCodeSymbol)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (htransitions : D.transitions = first :: rest)
    (parserTape : Tape MachineCodeSymbol)
    (hparser : Tape.Equiv
      (markedParserMaterializerSourceTape
        (Section53ParserAssembly.headerAfterHaltLeftRev D (remaining + 1))
        first rest input)
      parserTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes Machine.machine
        { state := Machine.entry (transitionListParserSavedHead input)
          tape := parserTape }
        { state := Machine.ready, tape := targetTape } ∧
      Tape.Equiv
        (loopSourceConfig (initialConfiguration D input)
          (first :: rest) remaining D.halt []).tape
        targetTape := by
  let saved := transitionListParserSavedHead input
  let context := positiveInitialContextTail D input
  let base := positiveMaterializerCopierBaseLeftRev D (remaining + 1)
  let table := MachineDescription.encodeTransitions (first :: rest)
  rcases Section53BooleanContextPhase.Machine.saved_positive_materializer
      D remaining input first rest htransitions with
    ⟨materializerCanonicalTape, hmaterializerCanonical,
      hmaterializerCanonicalShape⟩
  rcases computes_of_tape_equiv hmaterializerCanonical parserTape hparser with
    ⟨materializerTape, hmaterializer, hmaterializerTransportShape⟩
  have hmaterializerShape : Tape.Equiv
      (positiveMaterializerTargetConfig D remaining input first rest).tape
      materializerTape :=
    Tape.Equiv.trans hmaterializerCanonicalShape
      hmaterializerTransportShape
  have hmaterializerOuter :=
    Machine.materializer_computes_lift saved hmaterializer
  have hcopySource : Tape.Equiv
      (copyPassSource base first rest 0 context).tape materializerTape := by
    simpa [base, context, copyPassSource, stackSuffix,
      positiveMaterializerTargetConfig, positiveInitialStackSuffix,
      tableStack] using hmaterializerShape
  rcases copy_remaining saved D first rest remaining 0 context
      materializerTape hcopySource with
    ⟨compactorTape, hcopies, hcompactorSource⟩
  let compactorTail := compactorRest first rest remaining context
  let baseWord := List.append (MachineDescription.encodeNat D.start)
    [MachineCodeSymbol.header]
  have hbaseWord : baseWord ≠ [] := by
    simp [baseWord]
  cases hbase : baseWord with
  | nil => exact (hbaseWord hbase).elim
  | cons baseFirst baseRest =>
      have hcompactorSource' : Tape.Equiv
          (GapCompactor.sourceConfig (baseFirst :: baseRest)
            (GapCompactor.cleanupGap D table)
            MachineCodeSymbol.transition compactorTail).tape
          compactorTape := by
        have hshape : Tape.Equiv
            (GapCompactor.sourceConfig baseWord
              (GapCompactor.cleanupGap D table)
              MachineCodeSymbol.transition compactorTail).tape
            compactorTape := by
          simpa [baseWord, table, compactorTail] using hcompactorSource
        rw [hbase] at hshape
        exact hshape
      rcases GapCompactor.computes_of_tape_equiv baseFirst baseRest
          compactorTail (GapCompactor.cleanupGap D table) compactorTape
          hcompactorSource' with
        ⟨compactedTape, hcompactor, hcompactorShape⟩
      have hcompactorOuter := Machine.compactor_computes_lift saved hcompactor
      let nextHead := Machine.savedRead saved
      let restagerRest := MachineCodeSymbol.transition :: compactorTail
      have hrestagerCanonical : TuringMachine.Computes
          NextCopyRestager.machine
          (NextCopyRestager.sourceConfig nextHead D.start restagerRest)
          (NextCopyRestager.targetConfig nextHead D.start restagerRest) :=
        TuringMachine.computesIn_to_computes
          (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp
            (NextCopyRestager.run_exact nextHead D.start restagerRest))
      have hrestagerSource : Tape.Equiv
          (NextCopyRestager.sourceConfig nextHead D.start restagerRest).tape
          compactedTape := by
        have hsourceEq :
            (NextCopyRestager.sourceConfig nextHead D.start restagerRest).tape =
              Tape.input
                (List.append (baseFirst :: baseRest) restagerRest) := by
          have hword :
              MachineDescription.encodeNatAppend D.start
                  (MachineCodeSymbol.header :: restagerRest) =
                List.append (baseFirst :: baseRest) restagerRest := by
            rw [← hbase]
            simp [baseWord, MachineDescription.encodeNatAppend,
              List.append_assoc]
          change SerializedShift.cursorTape []
              (MachineDescription.encodeNatAppend D.start
                (MachineCodeSymbol.header :: restagerRest)) = _
          rw [hword]
          rfl
        have hsourceEquiv : Tape.Equiv
            (NextCopyRestager.sourceConfig nextHead D.start
              restagerRest).tape
            (Tape.input
              (List.append (baseFirst :: baseRest) restagerRest)) := by
          rw [hsourceEq]
          exact Tape.Equiv.refl _
        exact Tape.Equiv.trans hsourceEquiv
          (by simpa [restagerRest] using hcompactorShape)
      rcases computes_of_tape_equiv hrestagerCanonical compactedTape
          hrestagerSource with
        ⟨targetTape, hrestager, hrestagerShape⟩
      have hrestagerOuter := Machine.restager_computes_lift hrestager
      have htarget : Tape.Equiv
          (loopSourceConfig (initialConfiguration D input)
            (first :: rest) remaining D.halt []).tape targetTape := by
        have hcanonicalTarget := restagerTarget_tape_eq_loopSource
          D input first rest remaining
        have hnextHead : nextHead =
            Machine.savedRead (transitionListParserSavedHead input) := by
          rfl
        have hrestagerRest : restagerRest =
            MachineCodeSymbol.transition ::
              compactorRest first rest remaining
                (positiveInitialContextTail D input) := by
          rfl
        rw [hnextHead, hrestagerRest] at hrestagerShape
        exact Tape.Equiv.trans
          (hcanonicalTarget ▸ Tape.Equiv.refl _) hrestagerShape
      refine ⟨targetTape, ?_, htarget⟩
      have hrun := TuringMachine.computes_trans hmaterializerOuter hcopies
      have hrun := TuringMachine.computes_trans hrun hcompactorOuter
      have hrun := TuringMachine.computes_trans hrun hrestagerOuter
      dsimp [Machine.materializerConfig, Machine.compactorConfig,
        Machine.restagerConfig, Machine.entry, Machine.ready,
        Machine.liftMaterializerControl, Machine.liftCompactorControl,
        Machine.liftRestagerControl, saved, context, base, table,
        compactorTail, nextHead, restagerRest,
        NextCopyRestager.targetConfig,
        Section53BooleanContextPhase.Machine.halt] at hrun
      exact hrun

end Section53PositiveInitializerMachine

end Computability
end FoC
