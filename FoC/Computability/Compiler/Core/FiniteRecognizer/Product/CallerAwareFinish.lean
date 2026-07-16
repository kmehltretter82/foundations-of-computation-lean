import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.FinishMachine
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.CallerAwareTail
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Contextual.EmptyCallerWriter
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.EquivWitness
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.TwoBlankCompactor

set_option doc.verso true

/-!
# Product caller-aware finish schedules

Branch-finishing schedules for the product pair-prefix materializer. Both
schedules keep the deterministic physical endpoint while relating it to the
canonical pair target by
{name (full := FoC.Computability.Tape.Equiv)}`Tape.Equiv`.
-/

namespace FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe

open Languages
open InitialMaterializer

namespace ProductCallerAwareFinish

abbrev Config (state : Type) :=
  TuringMachine.Configuration MachineCodeSymbol state

private theorem exactRun_trans
    {state : Type}
    (M : TuringMachine MachineCodeSymbol state)
    {first second : Nat}
    {source middle target : Config state}
    (hfirst : M.runConfigExact? first source = some middle)
    (hsecond : M.runConfigExact? second middle = some target) :
    M.runConfigExact? (first + second) source = some target := by
  rw [InitialMaterializer.ExactRun.append, hfirst]
  exact hsecond

/-! ## Empty-input branch -/

def emptyCallerData {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (rightFuel : Nat) : Word MachineCodeSymbol :=
  ProductInput.pairCallerData right [] rightFuel

def emptyWriterSource {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) : Config (ProductFinish.Control left right) :=
  ProductFinish.materializerConfig
    (FullMaterializerMachine.emptyWriteConfig left
      (ProductContextual.EmptyCallerWriter.sourceConfig
        (EmptyInputSuffix.suffix left)
        (MachineDescription.encodeNat leftFuel).reverse
        (emptyCallerData right rightFuel)))

def emptyWriterEndpoint {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) : Config (ProductFinish.Control left right) :=
  ProductFinish.materializerConfig
    (FullMaterializerMachine.emptyWriteConfig left
      (ProductContextual.EmptyCallerWriter.endpointConfig
        (EmptyInputSuffix.suffix left)
        (MachineDescription.encodeNat leftFuel).reverse
        (emptyCallerData right rightFuel)))

def emptyHeaderSource {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) : Config (ProductFinish.Control left right) :=
  ProductFinish.materializerConfig
    (FullMaterializerMachine.emptyPrependConfig left
      (ProductCallerTail.EmptyCallerHeader.sourceConfig
        (EmptyInputSuffix.body left leftFuel).reverse
        (emptyCallerData right rightFuel)))

def emptyHeaderEndpoint {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) : Config (ProductFinish.Control left right) :=
  ProductFinish.materializerConfig
    (FullMaterializerMachine.emptyPrependConfig left
      (ProductCallerTail.EmptyCallerHeader.gateConfig
        (EmptyInputSuffix.body left leftFuel)
        (emptyCallerData right rightFuel)))

def emptyTargetTape {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) : Tape MachineCodeSymbol :=
  Tape.move Direction.left
    (ProductCallerTail.EmptyCallerHeader.gateTape
      (EmptyInputSuffix.body left leftFuel)
      (emptyCallerData right rightFuel))

def emptyPhysicalTarget {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) : Config (ProductFinish.Control left right) :=
  { state := (ProductFinish.machine left right).halt
    tape := emptyTargetTape left right leftFuel rightFuel }

def emptyCanonicalTarget {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) : Config (ProductFinish.Control left right) :=
  { state := (ProductFinish.machine left right).halt
    tape := Tape.input
      (ProductInput.pairTargetWord left right [] leftFuel rightFuel) }

theorem empty_writer_run_exact {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    (ProductFinish.machine left right).runConfigExact?
        (EmptyInputSuffix.suffix left).length
        (emptyWriterSource left right leftFuel rightFuel) =
      some (emptyWriterEndpoint left right leftFuel rightFuel) := by
  have hwriter := ProductContextual.EmptyCallerWriter.run_exact
    (EmptyInputSuffix.suffix left)
    (MachineDescription.encodeNat leftFuel).reverse
    (emptyCallerData right rightFuel)
  have hinner := FullMaterializerMachine.empty_write_run_of_eq_some
    left (EmptyInputSuffix.suffix left).length _ _ hwriter
  exact ProductFinish.materializer_run_lift left right hinner

theorem contextual_writer_to_header_exact {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (leftFuel : Nat) (callerData : Word MachineCodeSymbol) :
    (FullMaterializerMachine.machine left).runConfigExact? 2
        (FullMaterializerMachine.emptyWriteConfig left
          (ProductContextual.EmptyCallerWriter.endpointConfig
            (EmptyInputSuffix.suffix left)
            (MachineDescription.encodeNat leftFuel).reverse callerData)) =
      some
        (FullMaterializerMachine.emptyPrependConfig left
          (ProductCallerTail.EmptyCallerHeader.sourceConfig
            (EmptyInputSuffix.body left leftFuel).reverse callerData)) := by
  have hwriter :
      List.append (EmptyInputSuffix.suffix left).reverse
          (MachineDescription.encodeNat leftFuel).reverse =
        (EmptyInputSuffix.body left leftFuel).reverse :=
    EmptyInputSuffix.writer_leftRev_eq_body_reverse left leftFuel
  have hne : (EmptyInputSuffix.body left leftFuel).reverse ≠ [] := by
    intro hnil
    have hlength := congrArg List.length hnil
    simp [EmptyInputSuffix.body, EmptyInputSuffix.suffix] at hlength
  cases hrev : (EmptyInputSuffix.body left leftFuel).reverse with
  | nil => contradiction
  | cons first rest =>
      unfold Word at hwriter
      have hwriterCells := congrArg
        (List.map (fun symbol : MachineCodeSymbol => some symbol)) hwriter
      rw [hrev] at hwriterCells
      have hwriterCells' :
          ((EmptyInputSuffix.suffix left).map some).reverse ++
              ((MachineDescription.encodeNat leftFuel).map some).reverse =
            some first :: rest.map some := by
        simpa [List.map_append, List.map_reverse] using hwriterCells
      cases callerData <;>
        simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
          FullMaterializerMachine.machine,
          FullMaterializerMachine.transition,
          FullMaterializerMachine.emptyWriteConfig,
          FullMaterializerMachine.emptyPrependConfig,
          ProductContextual.EmptyCallerWriter.endpointConfig,
          ProductCallerTail.EmptyCallerHeader.sourceConfig,
          ProductCallerTail.EmptyCallerHeader.sourceTape,
          FixedWordWriter.stateAt,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
          hwriterCells']

theorem empty_writer_to_header_outer_exact {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    (ProductFinish.machine left right).runConfigExact? 2
        (emptyWriterEndpoint left right leftFuel rightFuel) =
      some (emptyHeaderSource left right leftFuel rightFuel) := by
  exact ProductFinish.materializer_run_lift left right
    (contextual_writer_to_header_exact left leftFuel
      (emptyCallerData right rightFuel))

theorem empty_body_ne_nil {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (leftFuel : Nat) : EmptyInputSuffix.body left leftFuel ≠ [] := by
  intro hnil
  have hlength := congrArg List.length hnil
  simp [EmptyInputSuffix.body, EmptyInputSuffix.suffix] at hlength

theorem empty_header_inner_run_exact {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (leftFuel : Nat) (callerData : Word MachineCodeSymbol) :
    PrependHeader.machine.runConfigExact?
        ((EmptyInputSuffix.body left leftFuel).length + 2)
        (ProductCallerTail.EmptyCallerHeader.sourceConfig
          (EmptyInputSuffix.body left leftFuel).reverse callerData) =
      some
        (ProductCallerTail.EmptyCallerHeader.gateConfig
          (EmptyInputSuffix.body left leftFuel) callerData) := by
  cases hword : (EmptyInputSuffix.body left leftFuel).reverse with
  | nil =>
      exact False.elim
        (by
          apply empty_body_ne_nil left leftFuel
          unfold Word
          simpa using congrArg List.reverse hword)
  | cons first rest =>
      have hrun := ProductCallerTail.EmptyCallerHeader.run_exact
        first rest callerData
      have hlength :
          (first :: rest).length =
            (EmptyInputSuffix.body left leftFuel).length := by
        rw [← hword]
        simp
      have hreverse :
          (first :: rest).reverse =
            EmptyInputSuffix.body left leftFuel := by
        rw [← hword]
        simp
      rw [hlength, hreverse] at hrun
      exact hrun

theorem empty_header_outer_run_exact {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    (ProductFinish.machine left right).runConfigExact?
        ((EmptyInputSuffix.body left leftFuel).length + 2)
        (emptyHeaderSource left right leftFuel rightFuel) =
      some (emptyHeaderEndpoint left right leftFuel rightFuel) := by
  have hinner := FullMaterializerMachine.empty_prepend_run_of_eq_some
    left ((EmptyInputSuffix.body left leftFuel).length + 2) _ _
      (empty_header_inner_run_exact left leftFuel
        (emptyCallerData right rightFuel))
  exact ProductFinish.materializer_run_lift left right hinner

theorem empty_header_to_halt_exact {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    (ProductFinish.machine left right).runConfigExact? 1
        (emptyHeaderEndpoint left right leftFuel rightFuel) =
      some (emptyPhysicalTarget left right leftFuel rightFuel) := by
  simpa [emptyHeaderEndpoint, emptyPhysicalTarget, emptyTargetTape,
    ProductFinish.emptyMaterializerEndpoint,
    ProductFinish.materializerConfig,
    TuringMachine.PhaseEmbedding.liftConfig,
    FullMaterializerMachine.emptyPrependConfig,
    ProductCallerTail.EmptyCallerHeader.gateConfig] using
    (ProductFinish.empty_materializer_handoff_run_exact left right
      (ProductCallerTail.EmptyCallerHeader.gateTape
        (EmptyInputSuffix.body left leftFuel)
        (emptyCallerData right rightFuel)))

def emptyFinishSteps {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (leftFuel : Nat) : Nat :=
  (((EmptyInputSuffix.suffix left).length + 2) +
    ((EmptyInputSuffix.body left leftFuel).length + 2)) + 1

theorem empty_finish_run_exact {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    (ProductFinish.machine left right).runConfigExact?
        (emptyFinishSteps left leftFuel)
        (emptyWriterSource left right leftFuel rightFuel) =
      some (emptyPhysicalTarget left right leftFuel rightFuel) := by
  have hwriter := empty_writer_run_exact left right leftFuel rightFuel
  have hbridge := empty_writer_to_header_outer_exact
    left right leftFuel rightFuel
  have hheader := empty_header_outer_run_exact left right leftFuel rightFuel
  have hhalt := empty_header_to_halt_exact left right leftFuel rightFuel
  have hfirst := exactRun_trans (ProductFinish.machine left right)
    hwriter hbridge
  have hsecond := exactRun_trans (ProductFinish.machine left right)
    hfirst hheader
  have hfull := exactRun_trans (ProductFinish.machine left right)
    hsecond hhalt
  simpa [emptyFinishSteps, Nat.add_assoc] using hfull

theorem emptyTargetTape_equiv_pairTarget {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    Tape.Equiv (emptyTargetTape left right leftFuel rightFuel)
      (Tape.input
        (ProductInput.pairTargetWord left right [] leftFuel rightFuel)) := by
  let body := EmptyInputSuffix.body left leftFuel
  let callerData := emptyCallerData right rightFuel
  let fullWord := MachineCodeSymbol.header :: List.append body callerData
  have hfull :
      fullWord = ProductInput.pairTargetWord
        left right [] leftFuel rightFuel := by
    unfold fullWord body callerData emptyCallerData
    simpa [ProductInput.pairTargetWord] using
      ProductInput.emptyBody_append_callerData left leftFuel
        (ProductInput.pairCallerData right [] rightFuel)
  have hgate :=
    ProductCallerTail.EmptyCallerHeader.gateTape_equiv_paired_input
      body callerData
  have hmoved := Tape.Equiv.move hgate Direction.left
  have hbody : body ≠ [] := empty_body_ne_nil left leftFuel
  cases hbodyShape : body with
  | nil => contradiction
  | cons first rest =>
      have hright :
          (Tape.input fullWord).right =
            some first :: (List.append rest callerData).map some := by
        simp [fullWord, hbodyShape, Tape.input, List.map_append]
      have hcancel :=
        Tape.move_left_move_right_eq_self_of_right_cons
          (Tape.input fullWord) hright
      change Tape.Equiv
        (Tape.move Direction.left
          (ProductCallerTail.EmptyCallerHeader.gateTape body callerData))
        (Tape.move Direction.left
          (Tape.move Direction.right (Tape.input fullWord))) at hmoved
      rw [hcancel, hfull] at hmoved
      simpa [emptyTargetTape, body, callerData] using hmoved

def empty_finish_run {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftFuel rightFuel : Nat) :
    ProductEquivWitness.RunsToEquiv (ProductFinish.machine left right)
      (emptyWriterSource left right leftFuel rightFuel)
      (emptyCanonicalTarget left right leftFuel rightFuel) where
  endpoint := emptyPhysicalTarget left right leftFuel rightFuel
  steps := emptyFinishSteps left leftFuel
  run_exact := empty_finish_run_exact left right leftFuel rightFuel
  endpoint_state := rfl
  canonical_tape_equiv := Tape.Equiv.symm
    (emptyTargetTape_equiv_pairTarget left right leftFuel rightFuel)

/-! ## Nonempty-input branch -/

def nonemptyCallerData {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (rightFuel : Nat) : Word MachineCodeSymbol :=
  ProductInput.pairCallerData right (headSymbol :: rest) rightFuel

def nonemptySource {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) : Config (ProductFinish.Control left right) :=
  ProductFinish.materializerConfig
    (FullMaterializerMachine.tailConfig left
      (ProductCallerTail.NonemptyCallerTail.haltConfig
        headSymbol (MachineDescription.encodeNat leftFuel).reverse
        rest.reverse
        (nonemptyCallerData right headSymbol rest rightFuel)))

def nonemptyCanonicalTarget {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) : Config (ProductFinish.Control left right) :=
  { state := (ProductFinish.machine left right).halt
    tape := Tape.input
      (ProductInput.pairTargetWord left right (headSymbol :: rest)
        leftFuel rightFuel) }

def callerBody {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (headSymbol : MachineCodeSymbol)
    (rest callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append
    (NonemptyFixedPrefix.fixedPrefix left headSymbol)
    (ProductCallerAwareTail.regionWithCaller rest callerData)

def insertedRev {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (headSymbol : MachineCodeSymbol)
    (rest callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  VariableBlockInsert.finalLeftRev
    (NonemptyFixedPrefix.buffer left headSymbol) []
    (ProductCallerAwareTail.regionWithCaller rest callerData)

def cleanBlockSource {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (headSymbol : MachineCodeSymbol)
    (rest fuelRev callerData : Word MachineCodeSymbol) :
    Config (FullMaterializerMachine.Control left) :=
  FullMaterializerMachine.blockConfig left headSymbol
    (VariableBlockInsert.config
      (NonemptyFixedPrefix.buffer left headSymbol) []
      (none :: none :: fuelRev.map some)
      (ProductCallerAwareTail.regionWithCaller rest callerData))

def cleanBlockEndpoint {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (headSymbol : MachineCodeSymbol)
    (rest fuelRev callerData : Word MachineCodeSymbol) :
    Config (FullMaterializerMachine.Control left) :=
  FullMaterializerMachine.blockConfig left headSymbol
    (VariableBlockInsert.haltConfig
      (insertedRev left headSymbol rest callerData)
      (none :: none :: fuelRev.map some))

def cleanHeaderSource {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (wordRev fuelRev : Word MachineCodeSymbol) :
    Config (FullMaterializerMachine.Control left) :=
  FullMaterializerMachine.headerConfig left
    (HeaderLeftInstaller.sourceConfig wordRev fuelRev)

def cleanHeaderEndpoint {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (fuel : Nat) (body : Word MachineCodeSymbol) :
    Config (FullMaterializerMachine.Control left) :=
  FullMaterializerMachine.headerConfig left
    (HeaderLeftInstaller.haltConfig
      (MachineDescription.encodeNat fuel) body)

def blockSteps {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (headSymbol : MachineCodeSymbol)
    (rest callerData : Word MachineCodeSymbol) : Nat :=
  (ProductCallerAwareTail.regionWithCaller rest callerData).length +
    (NonemptyFixedPrefix.fixedPrefix left headSymbol).length

theorem insertedRev_reverse {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (headSymbol : MachineCodeSymbol)
    (rest callerData : Word MachineCodeSymbol) :
    (insertedRev left headSymbol rest callerData).reverse =
      callerBody left headSymbol rest callerData := by
  exact VariableBlockInsert.finalLeftRev_reverse
    (NonemptyFixedPrefix.buffer left headSymbol) []
    (ProductCallerAwareTail.regionWithCaller rest callerData)
    (NonemptyFixedPrefix.fixedPrefix_ne_nil left headSymbol)

theorem insertedRev_ne_nil {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (headSymbol : MachineCodeSymbol)
    (rest callerData : Word MachineCodeSymbol) :
    insertedRev left headSymbol rest callerData ≠ [] := by
  intro hnil
  have hreverse := insertedRev_reverse left headSymbol rest callerData
  rw [hnil] at hreverse
  have hbody : callerBody left headSymbol rest callerData ≠ [] := by
    intro hbodyNil
    exact NonemptyFixedPrefix.fixedPrefix_ne_nil left headSymbol
      (List.append_eq_nil_iff.mp hbodyNil).1
  exact hbody hreverse.symm

theorem clean_block_run_exact {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (headSymbol : MachineCodeSymbol)
    (rest fuelRev callerData : Word MachineCodeSymbol) :
    (FullMaterializerMachine.machine left).runConfigExact?
        (blockSteps left headSymbol rest callerData)
        (cleanBlockSource left headSymbol rest fuelRev callerData) =
      some (cleanBlockEndpoint left headSymbol rest fuelRev callerData) := by
  apply FullMaterializerMachine.block_run_of_eq_some
  exact VariableBlockInsert.run_exact
    (NonemptyFixedPrefix.buffer left headSymbol)
    (NonemptyFixedPrefix.buffer left headSymbol) []
    (ProductCallerAwareTail.regionWithCaller rest callerData)
    (none :: none :: fuelRev.map some)
    (NonemptyFixedPrefix.fixedPrefix_ne_nil left headSymbol)

theorem cleanBlockSource_equiv_blockPaddedSource {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (headSymbol : MachineCodeSymbol)
    (rest fuelRev callerData : Word MachineCodeSymbol) :
    Tape.Equiv
      (cleanBlockSource left headSymbol rest fuelRev callerData).tape
      (ProductCallerAwareTail.blockPaddedSourceConfig
        left headSymbol rest fuelRev callerData).tape := by
  have hnonempty :=
    ProductCallerAwareTail.ContextualRawTail.regionWithCaller_ne_nil
      rest callerData
  cases hregion :
      ProductCallerAwareTail.regionWithCaller rest callerData with
  | nil => contradiction
  | cons first regionRest =>
      simp [cleanBlockSource,
        ProductCallerAwareTail.blockPaddedSourceConfig,
        ProductCallerAwareTail.ContextualRawTail.doneConfig,
        SeparatorRewind.gateTapeCells,
        FullMaterializerMachine.blockConfig,
        VariableBlockInsert.config,
        InsertOneWithBoundary.cursorTape,
        Tape.Equiv, FoC.Computability.dropTrailingNone_append_none,
        hregion]

theorem clean_block_header_bridge_exact {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (headSymbol : MachineCodeSymbol)
    (rest fuelRev callerData : Word MachineCodeSymbol) :
    (FullMaterializerMachine.machine left).runConfigExact? 2
        (cleanBlockEndpoint left headSymbol rest fuelRev callerData) =
      some
        (cleanHeaderSource left
          (insertedRev left headSymbol rest callerData) fuelRev) := by
  exact FullMaterializerMachine.block_header_bridge_exact
    left headSymbol (insertedRev left headSymbol rest callerData) fuelRev
    (insertedRev_ne_nil left headSymbol rest callerData)

theorem clean_header_run_exact {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (fuel : Nat) (wordRev : Word MachineCodeSymbol) :
    (FullMaterializerMachine.machine left).runConfigExact?
        (HeaderLeftInstaller.runSteps fuel wordRev)
        (cleanHeaderSource left wordRev
          (MachineDescription.encodeNat fuel).reverse) =
      some (cleanHeaderEndpoint left fuel wordRev.reverse) := by
  exact FullMaterializerMachine.header_run_of_eq_some
    left _ _ _ (HeaderLeftInstaller.run_exact fuel wordRev)

def blockHeaderSteps {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (headSymbol : MachineCodeSymbol)
    (rest callerData : Word MachineCodeSymbol)
    (fuel : Nat) : Nat :=
  (blockSteps left headSymbol rest callerData + 2) +
    HeaderLeftInstaller.runSteps fuel
      (insertedRev left headSymbol rest callerData)

theorem clean_block_header_run_exact {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (headSymbol : MachineCodeSymbol)
    (rest callerData : Word MachineCodeSymbol)
    (fuel : Nat) :
    (FullMaterializerMachine.machine left).runConfigExact?
        (blockHeaderSteps left headSymbol rest callerData fuel)
        (cleanBlockSource left headSymbol rest
          (MachineDescription.encodeNat fuel).reverse callerData) =
      some
        (cleanHeaderEndpoint left fuel
          (callerBody left headSymbol rest callerData)) := by
  have hblock := clean_block_run_exact left headSymbol rest
    (MachineDescription.encodeNat fuel).reverse callerData
  have hbridge := clean_block_header_bridge_exact left headSymbol rest
    (MachineDescription.encodeNat fuel).reverse callerData
  have hheader := clean_header_run_exact left fuel
    (insertedRev left headSymbol rest callerData)
  have hfirst := FullMaterializerMachine.exactRun_trans
    left _ _ _ _ _ hblock hbridge
  have hfull := FullMaterializerMachine.exactRun_trans
    left _ _ _ _ _ hfirst hheader
  simpa [blockHeaderSteps,
    insertedRev_reverse left headSymbol rest callerData] using hfull

def compactorSteps (fuel : Nat) (body : Word MachineCodeSymbol) : Nat :=
  StageInput.TwoBlankCompactor.runSteps
    (MachineDescription.encodeNat fuel) body

theorem compactor_run_from_equiv_header_halt
    (fuel : Nat) (body : Word MachineCodeSymbol)
    (paddedTape : Tape MachineCodeSymbol)
    (hpadded : Tape.Equiv
      (HeaderLeftInstaller.haltTape
        (MachineDescription.encodeNat fuel) body)
      paddedTape) :
    exists endpoint : Config StageInput.TwoBlankCompactor.Control,
      StageInput.TwoBlankCompactor.machine.runConfigExact?
          (compactorSteps fuel body)
          (StageInput.TwoBlankCompactor.config .seek paddedTape) =
        some endpoint ∧
      endpoint.state = StageInput.TwoBlankCompactor.machine.halt ∧
      Tape.Equiv endpoint.tape
        (Tape.input
          (MachineCodeSymbol.header ::
            List.append (MachineDescription.encodeNat fuel) body)) := by
  let fuelWord := MachineDescription.encodeNat fuel
  let cleanTarget :=
    StageInput.TwoBlankCompactor.compactConfig
      (SerializedFieldComposer.DeleteRestagedMachine.rewindConfig
        (SerializedFieldComposer.DeleteEndpointRewind.gateConfig
          (MachineCodeSymbol.header :: List.append fuelWord body)
          StageInput.TwoBlankCompactor.gapCell))
  have hclean :
      StageInput.TwoBlankCompactor.machine.runConfigExact?
          (StageInput.TwoBlankCompactor.runSteps fuelWord body)
          (StageInput.TwoBlankCompactor.seekConfig fuelWord
            [MachineCodeSymbol.header] body) =
        some cleanTarget := by
    exact StageInput.TwoBlankCompactor.run_exact fuelWord body
  have hsource : Tape.Equiv
      (StageInput.TwoBlankCompactor.seekConfig fuelWord
        [MachineCodeSymbol.header] body).tape paddedTape := by
    exact Tape.Equiv.trans
      (StageInput.TwoBlankCompactor.seekTape_equiv_haltTape
        fuelWord body (by
          unfold fuelWord
          cases fuel <;> simp [MachineDescription.encodeNat]))
      (by simpa [fuelWord] using hpadded)
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hclean hsource with
    ⟨endpoint, hrun, hstate, htape⟩
  refine ⟨endpoint, ?_, hstate, ?_⟩
  · simpa [compactorSteps, fuelWord,
      StageInput.TwoBlankCompactor.seekConfig,
      StageInput.TwoBlankCompactor.config] using hrun
  · exact Tape.Equiv.trans (Tape.Equiv.symm htape) (by
      simpa [cleanTarget] using
        StageInput.TwoBlankCompactor.endpoint_tape_equiv_input
          fuelWord body)

theorem callerTargetWord_eq {leftCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (headSymbol : MachineCodeSymbol)
    (rest callerData : Word MachineCodeSymbol)
    (fuel : Nat) :
    MachineCodeSymbol.header ::
        List.append (MachineDescription.encodeNat fuel)
          (callerBody left headSymbol rest callerData) =
      Frame.protectedWord
        (Layout.initial left (headSymbol :: rest) fuel) callerData := by
  simpa [callerBody, ProductCallerAwareTail.regionWithCaller,
    NonemptyFixedPrefix.body, List.append_assoc] using
    (ProductInput.nonemptyBody_append_callerData
      left fuel headSymbol rest callerData)

structure BlockFinishResult {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol)
    (rest callerData : Word MachineCodeSymbol)
    (fuel : Nat)
    (blockSource : Config (FullMaterializerMachine.Control left)) where
  targetTape : Tape MachineCodeSymbol
  steps : Nat
  run_exact :
    (ProductFinish.machine left right).runConfigExact? steps
        (ProductFinish.materializerConfig blockSource) =
      some
        { state := (ProductFinish.machine left right).halt
          tape := targetTape }
  targetTape_equiv : Tape.Equiv targetTape
    (Tape.input
      (Frame.protectedWord
        (Layout.initial left (headSymbol :: rest) fuel) callerData))

def finish_from_related_block_source {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol)
    (rest callerData : Word MachineCodeSymbol)
    (fuel : Nat)
    (blockSource : Config (FullMaterializerMachine.Control left))
    (hstate :
      (ProductCallerAwareTail.blockPaddedSourceConfig left headSymbol rest
        (MachineDescription.encodeNat fuel).reverse callerData).state =
      blockSource.state)
    (htape : Tape.Equiv
      (ProductCallerAwareTail.blockPaddedSourceConfig left headSymbol rest
        (MachineDescription.encodeNat fuel).reverse callerData).tape
      blockSource.tape) :
    BlockFinishResult left right headSymbol rest callerData fuel
      blockSource := by
  let cleanSource := cleanBlockSource left headSymbol rest
    (MachineDescription.encodeNat fuel).reverse callerData
  let cleanFinal := cleanHeaderEndpoint left fuel
    (callerBody left headSymbol rest callerData)
  have hclean :
      (FullMaterializerMachine.machine left).runConfigExact?
          (blockHeaderSteps left headSymbol rest callerData fuel)
          cleanSource = some cleanFinal := by
    exact clean_block_header_run_exact left headSymbol rest callerData fuel
  have hsourceState : cleanSource.state = blockSource.state := hstate
  have hsourceTape : Tape.Equiv cleanSource.tape blockSource.tape :=
    Tape.Equiv.trans
      (cleanBlockSource_equiv_blockPaddedSource left headSymbol rest
        (MachineDescription.encodeNat fuel).reverse callerData)
      htape
  have hheaderExists := TuringExactEquiv.runConfigExact?_some_of_equiv
    (clean := cleanSource) (padded := blockSource)
    (cleanFinal := cleanFinal)
    (FullMaterializerMachine.machine left)
    (blockHeaderSteps left headSymbol rest callerData fuel)
    hsourceState hsourceTape hclean
  let headerResult :=
    (FullMaterializerMachine.machine left).runConfigExact?
      (blockHeaderSteps left headSymbol rest callerData fuel) blockSource
  have hheaderSome : headerResult.isSome := by
    rcases hheaderExists with ⟨endpoint, hrun, _hstate, _htape⟩
    simp [headerResult, hrun]
  let actualHeader := headerResult.get hheaderSome
  have hheader : headerResult = some actualHeader :=
    (Option.some_get hheaderSome).symm
  have hheaderRun :
      (FullMaterializerMachine.machine left).runConfigExact?
          (blockHeaderSteps left headSymbol rest callerData fuel)
          blockSource = some actualHeader := hheader
  have hheaderState : cleanFinal.state = actualHeader.state := by
    rcases hheaderExists with ⟨endpoint, hrun, hstate', _htape⟩
    have heq : endpoint = actualHeader :=
      Option.some.inj (hrun.symm.trans hheaderRun)
    simpa [heq] using hstate'
  have hheaderTape : Tape.Equiv cleanFinal.tape actualHeader.tape := by
    rcases hheaderExists with ⟨endpoint, hrun, _hstate, htape'⟩
    have heq : endpoint = actualHeader :=
      Option.some.inj (hrun.symm.trans hheaderRun)
    simpa [heq] using htape'
  let bounced := StageRunner.roundTripTape actualHeader.tape
  have hheaderEndpoint : actualHeader.state =
      ProductFinish.materializerEndpoint := hheaderState.symm
  have hheaderOuter := ProductFinish.materializer_run_lift
    left right hheaderRun
  have hfirstHandoff :
      (ProductFinish.machine left right).runConfigExact? 2
          (ProductFinish.materializerConfig actualHeader) =
        some
          (ProductFinish.compactorConfig
            (StageInput.TwoBlankCompactor.config .seek bounced)) := by
    simpa [ProductFinish.materializerConfig,
      TuringMachine.PhaseEmbedding.liftConfig,
      hheaderEndpoint, bounced] using
      (ProductFinish.materializer_handoff_run_exact
        left right actualHeader.tape)
  have hbounced : Tape.Equiv
      (HeaderLeftInstaller.haltTape
        (MachineDescription.encodeNat fuel)
        (callerBody left headSymbol rest callerData)) bounced :=
    Tape.Equiv.trans
      (by simpa [cleanFinal, cleanHeaderEndpoint,
          FullMaterializerMachine.headerConfig,
          HeaderLeftInstaller.haltConfig] using hheaderTape)
      (Tape.Equiv.symm
        (StageRunner.roundTripTape_equiv actualHeader.tape))
  have hcompactorExists := compactor_run_from_equiv_header_halt fuel
    (callerBody left headSymbol rest callerData) bounced hbounced
  let compactorResult :=
    StageInput.TwoBlankCompactor.machine.runConfigExact?
      (compactorSteps fuel (callerBody left headSymbol rest callerData))
      (StageInput.TwoBlankCompactor.config .seek bounced)
  have hcompactorSome : compactorResult.isSome := by
    rcases hcompactorExists with ⟨endpoint, hrun, _hstate, _htape⟩
    simp [compactorResult, hrun]
  let compactorEndpoint := compactorResult.get hcompactorSome
  have hcompactor : compactorResult = some compactorEndpoint :=
    (Option.some_get hcompactorSome).symm
  have hcompactorRun :
      StageInput.TwoBlankCompactor.machine.runConfigExact?
          (compactorSteps fuel
            (callerBody left headSymbol rest callerData))
          (StageInput.TwoBlankCompactor.config .seek bounced) =
        some compactorEndpoint := hcompactor
  have hcompactorState :
      compactorEndpoint.state =
        StageInput.TwoBlankCompactor.machine.halt := by
    rcases hcompactorExists with ⟨endpoint, hrun, hstate', _htape⟩
    have heq : endpoint = compactorEndpoint :=
      Option.some.inj (hrun.symm.trans hcompactorRun)
    simpa [heq] using hstate'
  have hcompactorTape : Tape.Equiv compactorEndpoint.tape
      (Tape.input
        (MachineCodeSymbol.header ::
          List.append (MachineDescription.encodeNat fuel)
            (callerBody left headSymbol rest callerData))) := by
    rcases hcompactorExists with ⟨endpoint, hrun, _hstate, htape'⟩
    have heq : endpoint = compactorEndpoint :=
      Option.some.inj (hrun.symm.trans hcompactorRun)
    simpa [heq] using htape'
  have hcompactorOuter := ProductFinish.compactor_run_lift
    left right hcompactorRun
  let targetTape := StageRunner.roundTripTape compactorEndpoint.tape
  have hsecondHandoff :
      (ProductFinish.machine left right).runConfigExact? 2
          (ProductFinish.compactorConfig compactorEndpoint) =
        some
          { state := (ProductFinish.machine left right).halt
            tape := targetTape } := by
    simpa [ProductFinish.compactorConfig,
      TuringMachine.PhaseEmbedding.liftConfig,
      hcompactorState, targetTape] using
      (ProductFinish.compactor_handoff_run_exact
        left right compactorEndpoint.tape)
  have hthroughHeader := exactRun_trans
    (ProductFinish.machine left right) hheaderOuter hfirstHandoff
  have hthroughCompactor := exactRun_trans
    (ProductFinish.machine left right) hthroughHeader hcompactorOuter
  have hfull := exactRun_trans
    (ProductFinish.machine left right) hthroughCompactor hsecondHandoff
  refine
    { targetTape := targetTape
      steps :=
        ((blockHeaderSteps left headSymbol rest callerData fuel + 2) +
          compactorSteps fuel
            (callerBody left headSymbol rest callerData)) + 2
      run_exact := hfull
      targetTape_equiv := ?_ }
  rw [← callerTargetWord_eq left headSymbol rest callerData fuel]
  exact Tape.Equiv.trans
    (StageRunner.roundTripTape_equiv compactorEndpoint.tape)
    hcompactorTape

def nonempty_finish_run {leftCount rightCount : Nat}
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    ProductEquivWitness.RunsToEquiv (ProductFinish.machine left right)
      (nonemptySource left right headSymbol rest leftFuel rightFuel)
      (nonemptyCanonicalTarget left right headSymbol rest
        leftFuel rightFuel) := by
  let callerData := nonemptyCallerData right headSymbol rest rightFuel
  let tailSteps := ProductCallerAwareTail.tailBaseRawSteps
    rest.reverse callerData
  let innerSource :=
    FullMaterializerMachine.tailConfig left
      (ProductCallerTail.NonemptyCallerTail.haltConfig
        headSymbol (MachineDescription.encodeNat leftFuel).reverse
        rest.reverse callerData)
  have hinnerExists := ProductCallerAwareTail.tail_base_raw_to_block_exact
    left headSymbol (MachineDescription.encodeNat leftFuel).reverse
    rest.reverse callerData
  let innerResult :=
    (FullMaterializerMachine.machine left).runConfigExact?
      tailSteps innerSource
  have hinnerSome : innerResult.isSome := by
    rcases hinnerExists with ⟨endpoint, hrun, _hstate, _htape⟩
    simp [innerResult, tailSteps, innerSource, hrun]
  let blockSource := innerResult.get hinnerSome
  have htail :
      (FullMaterializerMachine.machine left).runConfigExact?
          tailSteps innerSource = some blockSource := by
    exact (Option.some_get hinnerSome).symm
  have hblockState :
      (ProductCallerAwareTail.blockPaddedSourceConfig left headSymbol rest
        (MachineDescription.encodeNat leftFuel).reverse callerData).state =
      blockSource.state := by
    rcases hinnerExists with ⟨endpoint, hrun, hstate, _htape⟩
    have heq : endpoint = blockSource :=
      Option.some.inj (hrun.symm.trans htail)
    simpa [heq] using hstate
  have hblockTape : Tape.Equiv
      (ProductCallerAwareTail.blockPaddedSourceConfig left headSymbol rest
        (MachineDescription.encodeNat leftFuel).reverse callerData).tape
      blockSource.tape := by
    rcases hinnerExists with ⟨endpoint, hrun, _hstate, htape⟩
    have heq : endpoint = blockSource :=
      Option.some.inj (hrun.symm.trans htail)
    simpa [heq] using htape
  have htailOuter := ProductFinish.materializer_run_lift
    left right htail
  let finish := finish_from_related_block_source
    left right headSymbol rest callerData leftFuel blockSource
      hblockState hblockTape
  have hfull := exactRun_trans (ProductFinish.machine left right)
    htailOuter finish.run_exact
  refine
    { endpoint :=
        { state := (ProductFinish.machine left right).halt
          tape := finish.targetTape }
      steps :=
        tailSteps + finish.steps
      run_exact := ?_
      endpoint_state := rfl
      canonical_tape_equiv := ?_ }
  · simpa [nonemptySource, callerData, nonemptyCallerData,
      innerSource] using hfull
  · simpa [nonemptyCanonicalTarget, callerData, nonemptyCallerData,
      ProductInput.pairTargetWord] using Tape.Equiv.symm finish.targetTape_equiv

end ProductCallerAwareFinish
end FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe
