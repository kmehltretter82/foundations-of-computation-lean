import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Input

set_option doc.verso true

/-!
# Product inner-call duplication

A collision-free one-tape duplicator preserves the parsed outer fuel and copies
the entire inner generated call across a physical blank boundary.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductDuplicator

inductive Control where
  | scan
  | seekBoundary (carried : MachineCodeSymbol)
  | seekCopyEnd (carried : MachineCodeSymbol)
  | rewindCopy (carried : MachineCodeSymbol)
  | rewindSource (carried : MachineCodeSymbol)
  | halt
deriving DecidableEq

namespace Control

def elems : List Control :=
  List.append [.scan, .halt]
    (List.append
      (MachineCodeSymbol.finite.elems.map Control.seekBoundary)
      (List.append
        (MachineCodeSymbol.finite.elems.map Control.seekCopyEnd)
        (List.append
          (MachineCodeSymbol.finite.elems.map Control.rewindCopy)
          (MachineCodeSymbol.finite.elems.map Control.rewindSource))))

def finite : Foundation.FiniteType Control where
  elems := elems
  complete := by
    intro control
    cases control with
    | scan => simp [elems]
    | seekBoundary carried =>
        simp [elems]
        exact MachineCodeSymbol.finite.complete carried
    | seekCopyEnd carried =>
        simp [elems]
        exact MachineCodeSymbol.finite.complete carried
    | rewindCopy carried =>
        simp [elems]
        exact MachineCodeSymbol.finite.complete carried
    | rewindSource carried =>
        simp [elems]
        exact MachineCodeSymbol.finite.complete carried
    | halt => simp [elems]

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .scan, some current =>
      some (none, Direction.right, .seekBoundary current)
  | .scan, none =>
      some (none, Direction.right, .halt)
  | .seekBoundary carried, some current =>
      some (some current, Direction.right, .seekBoundary carried)
  | .seekBoundary carried, none =>
      some (none, Direction.right, .seekCopyEnd carried)
  | .seekCopyEnd carried, some current =>
      some (some current, Direction.right, .seekCopyEnd carried)
  | .seekCopyEnd carried, none =>
      some (some carried, Direction.left, .rewindCopy carried)
  | .rewindCopy carried, some current =>
      some (some current, Direction.left, .rewindCopy carried)
  | .rewindCopy carried, none =>
      some (none, Direction.left, .rewindSource carried)
  | .rewindSource carried, some current =>
      some (some current, Direction.left, .rewindSource carried)
  | .rewindSource carried, none =>
      some (some carried, Direction.right, .scan)
  | .halt, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .scan
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def tapeAtCells
    (leftRev cells : List (Option MachineCodeSymbol)) :
    Tape MachineCodeSymbol :=
  match cells with
  | [] => { left := leftRev, head := none, right := [] }
  | cell :: rest => { left := leftRev, head := cell, right := rest }

/-- At the scan gate, {lit}`processed ++ remaining` is the restored source and
{lit}`processed` is the copy already present beyond the physical blank boundary. -/
def scanTape
    (baseLeftRev processed remaining : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  tapeAtCells
    (List.append (processed.reverse.map some) (baseLeftRev.map some))
    (List.append (remaining.map some)
      (none :: processed.map some))

def scanConfig
    (baseLeftRev processed remaining : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .scan
  tape := scanTape baseLeftRev processed remaining

def sourceTape
    (baseLeftRev input : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  scanTape baseLeftRev [] input

def sourceConfig
    (baseLeftRev input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  scanConfig baseLeftRev [] input

/-- While seeking the source/copy boundary, {lit}`crossedRev` records the source
suffix already crossed, nearest cell first. -/
def seekBoundaryTape
    (baseLeftRev processed crossedRev remaining : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  tapeAtCells
    (List.append (crossedRev.map some)
      (none :: List.append (processed.reverse.map some)
        (baseLeftRev.map some)))
    (List.append (remaining.map some)
      (none :: processed.map some))

def seekBoundaryConfig
    (carried : MachineCodeSymbol)
    (baseLeftRev processed crossedRev remaining : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .seekBoundary carried
  tape := seekBoundaryTape baseLeftRev processed crossedRev remaining

/-- Beyond the boundary, {lit}`copyCrossedRev` records the part of the old copy
already crossed on the way to its right end. -/
def seekCopyTape
    (baseLeftRev processed sourceRev copyCrossedRev copyRemaining :
      Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  tapeAtCells
    (List.append (copyCrossedRev.map some)
      (none :: List.append (sourceRev.map some)
        (none :: List.append (processed.reverse.map some)
          (baseLeftRev.map some))))
    (copyRemaining.map some)

def seekCopyConfig
    (carried : MachineCodeSymbol)
    (baseLeftRev processed sourceRev copyCrossedRev copyRemaining :
      Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .seekCopyEnd carried
  tape := seekCopyTape baseLeftRev processed sourceRev
    copyCrossedRev copyRemaining

def rewindCopyTape
    (carried : MachineCodeSymbol)
    (baseLeftRev processed sourceRev remainingRev crossed :
      Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := List.append (sourceRev.map some)
          (none :: List.append (processed.reverse.map some)
            (baseLeftRev.map some))
        head := none
        right := List.append (crossed.map some)
          [some carried] }
  | current :: more =>
      { left := List.append (more.map some)
          (none :: List.append (sourceRev.map some)
            (none :: List.append (processed.reverse.map some)
              (baseLeftRev.map some)))
        head := some current
        right := List.append (crossed.map some)
          [some carried] }

def rewindCopyConfig
    (carried : MachineCodeSymbol)
    (baseLeftRev processed sourceRev remainingRev crossed :
      Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .rewindCopy carried
  tape := rewindCopyTape carried baseLeftRev processed sourceRev
    remainingRev crossed

def rewindSourceTape
    (carried : MachineCodeSymbol)
    (baseLeftRev processed remainingRev crossed : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := List.append (processed.reverse.map some)
          (baseLeftRev.map some)
        head := none
        right := List.append (crossed.map some)
          (none :: (List.append processed [carried]).map some) }
  | current :: more =>
      { left := List.append (more.map some)
          (none :: List.append (processed.reverse.map some)
            (baseLeftRev.map some))
        head := some current
        right := List.append (crossed.map some)
          (none :: (List.append processed [carried]).map some) }

def rewindSourceConfig
    (carried : MachineCodeSymbol)
    (baseLeftRev processed remainingRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .rewindSource carried
  tape := rewindSourceTape carried baseLeftRev processed remainingRev crossed

def haltTape
    (baseLeftRev input : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  Tape.move Direction.right (scanTape baseLeftRev input [])

def haltConfig
    (baseLeftRev input : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control where
  state := .halt
  tape := haltTape baseLeftRev input

theorem scan_symbol_step
    (current : MachineCodeSymbol)
    (baseLeftRev processed rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (scanConfig baseLeftRev processed (current :: rest)) =
      some
        (seekBoundaryConfig current baseLeftRev processed [] rest) := by
  cases rest <;> cases processed <;> cases baseLeftRev <;> rfl

theorem scan_blank_step
    (baseLeftRev processed : Word MachineCodeSymbol) :
    machine.stepConfig (scanConfig baseLeftRev processed []) =
      some (haltConfig baseLeftRev processed) := by
  cases processed <;> cases baseLeftRev <;> rfl

theorem seekBoundary_symbol_step
    (carried current : MachineCodeSymbol)
    (baseLeftRev processed crossedRev rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (seekBoundaryConfig carried baseLeftRev processed crossedRev
          (current :: rest)) =
      some
        (seekBoundaryConfig carried baseLeftRev processed
          (current :: crossedRev) rest) := by
  cases rest <;> cases crossedRev <;> cases processed <;>
    cases baseLeftRev <;> rfl

theorem seekBoundary_blank_step
    (carried : MachineCodeSymbol)
    (baseLeftRev processed sourceRev : Word MachineCodeSymbol) :
    machine.stepConfig
        (seekBoundaryConfig carried baseLeftRev processed sourceRev []) =
      some
        (seekCopyConfig carried baseLeftRev processed sourceRev []
          processed) := by
  cases processed <;> cases sourceRev <;> cases baseLeftRev <;> rfl

theorem seekCopy_symbol_step
    (carried current : MachineCodeSymbol)
    (baseLeftRev processed sourceRev copyCrossedRev rest :
      Word MachineCodeSymbol) :
    machine.stepConfig
        (seekCopyConfig carried baseLeftRev processed sourceRev
          copyCrossedRev (current :: rest)) =
      some
        (seekCopyConfig carried baseLeftRev processed sourceRev
          (current :: copyCrossedRev) rest) := by
  cases rest <;> cases copyCrossedRev <;> cases sourceRev <;>
    cases processed <;> cases baseLeftRev <;> rfl

theorem seekCopy_blank_step
    (carried : MachineCodeSymbol)
    (baseLeftRev processed sourceRev copyRev : Word MachineCodeSymbol) :
    machine.stepConfig
        (seekCopyConfig carried baseLeftRev processed sourceRev
          copyRev []) =
      some
        (rewindCopyConfig carried baseLeftRev processed sourceRev
          copyRev []) := by
  cases copyRev <;> cases sourceRev <;> cases processed <;>
    cases baseLeftRev <;> rfl

theorem rewindCopy_symbol_step
    (carried current : MachineCodeSymbol)
    (baseLeftRev processed sourceRev more crossed :
      Word MachineCodeSymbol) :
    machine.stepConfig
        (rewindCopyConfig carried baseLeftRev processed sourceRev
          (current :: more) crossed) =
      some
        (rewindCopyConfig carried baseLeftRev processed sourceRev
          more (current :: crossed)) := by
  cases more <;> cases crossed <;> cases sourceRev <;>
    cases processed <;> cases baseLeftRev <;> rfl

theorem rewindCopy_blank_step
    (carried : MachineCodeSymbol)
    (baseLeftRev processed sourceRev : Word MachineCodeSymbol) :
    machine.stepConfig
        (rewindCopyConfig carried baseLeftRev processed sourceRev []
          processed) =
      some
        (rewindSourceConfig carried baseLeftRev processed sourceRev []) := by
  cases sourceRev <;>
    simp [machine, transition, TuringMachine.stepConfig, Tape.read,
      rewindCopyConfig, rewindCopyTape, rewindSourceConfig,
      rewindSourceTape, Tape.write, Tape.move, Tape.moveLeft,
      List.map_append]

theorem rewindSource_symbol_step
    (carried current : MachineCodeSymbol)
    (baseLeftRev processed more crossed : Word MachineCodeSymbol) :
    machine.stepConfig
        (rewindSourceConfig carried baseLeftRev processed
          (current :: more) crossed) =
      some
        (rewindSourceConfig carried baseLeftRev processed
          more (current :: crossed)) := by
  cases more <;> cases crossed <;> cases processed <;>
    cases baseLeftRev <;> rfl

theorem rewindSource_blank_step
    (carried : MachineCodeSymbol)
    (baseLeftRev processed source : Word MachineCodeSymbol) :
    machine.stepConfig
        (rewindSourceConfig carried baseLeftRev processed [] source) =
      some
        (scanConfig baseLeftRev (List.append processed [carried])
          source) := by
  cases source <;>
    simp [machine, transition, TuringMachine.stepConfig,
      rewindSourceConfig, rewindSourceTape, scanConfig, scanTape,
      tapeAtCells, Tape.read, Tape.write, Tape.move, Tape.moveRight,
      List.reverse_append, List.map_append]

theorem seekBoundary_run_exact
    (carried : MachineCodeSymbol)
    (baseLeftRev processed crossedRev remaining : Word MachineCodeSymbol) :
    machine.runConfigExact? remaining.length
        (seekBoundaryConfig carried baseLeftRev processed crossedRev
          remaining) =
      some
        (seekBoundaryConfig carried baseLeftRev processed
          (List.append remaining.reverse crossedRev) []) := by
  induction remaining generalizing crossedRev with
  | nil => simp [TuringMachine.runConfigExact?]
  | cons current rest ih =>
      change
        machine.runConfigExact? (rest.length + 1)
            (seekBoundaryConfig carried baseLeftRev processed crossedRev
              (current :: rest)) = _
      rw [TuringMachine.runConfigExact?]
      rw [seekBoundary_symbol_step]
      simp only
      rw [ih (current :: crossedRev)]
      simp [List.reverse_cons, List.append_assoc]

theorem seekCopy_run_exact
    (carried : MachineCodeSymbol)
    (baseLeftRev processed sourceRev copyCrossedRev remaining :
      Word MachineCodeSymbol) :
    machine.runConfigExact? remaining.length
        (seekCopyConfig carried baseLeftRev processed sourceRev
          copyCrossedRev remaining) =
      some
        (seekCopyConfig carried baseLeftRev processed sourceRev
          (List.append remaining.reverse copyCrossedRev) []) := by
  induction remaining generalizing copyCrossedRev with
  | nil => simp [TuringMachine.runConfigExact?]
  | cons current rest ih =>
      change
        machine.runConfigExact? (rest.length + 1)
            (seekCopyConfig carried baseLeftRev processed sourceRev
              copyCrossedRev (current :: rest)) = _
      rw [TuringMachine.runConfigExact?]
      rw [seekCopy_symbol_step]
      simp only
      rw [ih (current :: copyCrossedRev)]
      simp [List.reverse_cons, List.append_assoc]

theorem rewindCopy_run_exact
    (carried : MachineCodeSymbol)
    (baseLeftRev processed sourceRev remainingRev crossed :
      Word MachineCodeSymbol) :
    machine.runConfigExact? remainingRev.length
        (rewindCopyConfig carried baseLeftRev processed sourceRev
          remainingRev crossed) =
      some
        (rewindCopyConfig carried baseLeftRev processed sourceRev []
          (List.append remainingRev.reverse crossed)) := by
  induction remainingRev generalizing crossed with
  | nil => simp [TuringMachine.runConfigExact?]
  | cons current more ih =>
      change
        machine.runConfigExact? (more.length + 1)
            (rewindCopyConfig carried baseLeftRev processed sourceRev
              (current :: more) crossed) = _
      rw [TuringMachine.runConfigExact?]
      rw [rewindCopy_symbol_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]

theorem rewindSource_run_exact
    (carried : MachineCodeSymbol)
    (baseLeftRev processed remainingRev crossed : Word MachineCodeSymbol) :
    machine.runConfigExact? remainingRev.length
        (rewindSourceConfig carried baseLeftRev processed
          remainingRev crossed) =
      some
        (rewindSourceConfig carried baseLeftRev processed []
          (List.append remainingRev.reverse crossed)) := by
  induction remainingRev generalizing crossed with
  | nil => simp [TuringMachine.runConfigExact?]
  | cons current more ih =>
      change
        machine.runConfigExact? (more.length + 1)
            (rewindSourceConfig carried baseLeftRev processed
              (current :: more) crossed) = _
      rw [TuringMachine.runConfigExact?]
      rw [rewindSource_symbol_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]

def iterationSteps
    (processed rest : Word MachineCodeSymbol) : Nat :=
  1 + (rest.length +
    (1 + (processed.length +
      (1 + (processed.length +
        (1 + (rest.length + 1)))))))

theorem run_one_of_step
    {source target : TuringMachine.Configuration MachineCodeSymbol Control}
    (hstep : machine.stepConfig source = some target) :
    machine.runConfigExact? 1 source = some target := by
  rw [TuringMachine.runConfigExact?]
  rw [hstep]
  simp only [TuringMachine.runConfigExact?]

theorem run_exact_trans
    {first second : Nat}
    {source middle target :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (hfirst : machine.runConfigExact? first source = some middle)
    (hsecond : machine.runConfigExact? second middle = some target) :
    machine.runConfigExact? (first + second) source = some target := by
  rw [InitialMaterializer.ExactRun.append]
  rw [hfirst]
  exact hsecond

theorem iteration_run_exact
    (current : MachineCodeSymbol)
    (baseLeftRev processed rest : Word MachineCodeSymbol) :
    machine.runConfigExact? (iterationSteps processed rest)
        (scanConfig baseLeftRev processed (current :: rest)) =
      some
        (scanConfig baseLeftRev (List.append processed [current]) rest) := by
  have h0 :
      machine.runConfigExact? 1
          (scanConfig baseLeftRev processed (current :: rest)) =
        some (seekBoundaryConfig current baseLeftRev processed [] rest) :=
    run_one_of_step (scan_symbol_step current baseLeftRev processed rest)
  have h1 :
      machine.runConfigExact? rest.length
          (seekBoundaryConfig current baseLeftRev processed [] rest) =
        some
          (seekBoundaryConfig current baseLeftRev processed rest.reverse []) := by
    simpa using
      seekBoundary_run_exact current baseLeftRev processed
        ([] : Word MachineCodeSymbol) rest
  have h2 :
      machine.runConfigExact? 1
          (seekBoundaryConfig current baseLeftRev processed rest.reverse []) =
        some
          (seekCopyConfig current baseLeftRev processed rest.reverse []
            processed) :=
    run_one_of_step
      (seekBoundary_blank_step current baseLeftRev processed rest.reverse)
  have h3 :
      machine.runConfigExact? processed.length
          (seekCopyConfig current baseLeftRev processed rest.reverse []
            processed) =
        some
          (seekCopyConfig current baseLeftRev processed rest.reverse
            processed.reverse []) := by
    simpa using
      seekCopy_run_exact current baseLeftRev processed rest.reverse
        ([] : Word MachineCodeSymbol) processed
  have h4 :
      machine.runConfigExact? 1
          (seekCopyConfig current baseLeftRev processed rest.reverse
            processed.reverse []) =
        some
          (rewindCopyConfig current baseLeftRev processed rest.reverse
            processed.reverse []) :=
    run_one_of_step
      (seekCopy_blank_step current baseLeftRev processed rest.reverse
        processed.reverse)
  have h5 :
      machine.runConfigExact? processed.length
          (rewindCopyConfig current baseLeftRev processed rest.reverse
            processed.reverse []) =
        some
          (rewindCopyConfig current baseLeftRev processed rest.reverse []
            processed) := by
    simpa using
      rewindCopy_run_exact current baseLeftRev processed rest.reverse
        processed.reverse ([] : Word MachineCodeSymbol)
  have h6 :
      machine.runConfigExact? 1
          (rewindCopyConfig current baseLeftRev processed rest.reverse []
            processed) =
        some
          (rewindSourceConfig current baseLeftRev processed
            rest.reverse []) :=
    run_one_of_step
      (rewindCopy_blank_step current baseLeftRev processed rest.reverse)
  have h7 :
      machine.runConfigExact? rest.length
          (rewindSourceConfig current baseLeftRev processed
            rest.reverse []) =
        some
          (rewindSourceConfig current baseLeftRev processed [] rest) := by
    simpa using
      rewindSource_run_exact current baseLeftRev processed rest.reverse
        ([] : Word MachineCodeSymbol)
  have h8 :
      machine.runConfigExact? 1
          (rewindSourceConfig current baseLeftRev processed [] rest) =
        some
          (scanConfig baseLeftRev (List.append processed [current]) rest) :=
    run_one_of_step
      (rewindSource_blank_step current baseLeftRev processed rest)
  have h78 := run_exact_trans h7 h8
  have h678 := run_exact_trans h6 h78
  have h5678 := run_exact_trans h5 h678
  have h45678 := run_exact_trans h4 h5678
  have h345678 := run_exact_trans h3 h45678
  have h2345678 := run_exact_trans h2 h345678
  have h12345678 := run_exact_trans h1 h2345678
  have h012345678 := run_exact_trans h0 h12345678
  simpa [iterationSteps] using h012345678

def runStepsFrom :
    Word MachineCodeSymbol -> Word MachineCodeSymbol -> Nat
  | _, [] => 1
  | processed, _current :: rest =>
      iterationSteps processed rest +
        runStepsFrom (List.append processed [_current]) rest

theorem run_from_exact
    (baseLeftRev processed remaining : Word MachineCodeSymbol) :
    machine.runConfigExact? (runStepsFrom processed remaining)
        (scanConfig baseLeftRev processed remaining) =
      some (haltConfig baseLeftRev (List.append processed remaining)) := by
  induction remaining generalizing processed with
  | nil =>
      rw [runStepsFrom]
      have happend :
          List.append processed ([] : List MachineCodeSymbol) = processed :=
        List.append_nil processed
      rw [happend]
      exact run_one_of_step (scan_blank_step baseLeftRev processed)
  | cons current rest ih =>
      rw [runStepsFrom]
      rw [InitialMaterializer.ExactRun.append]
      rw [iteration_run_exact]
      simp only
      rw [ih (List.append processed [current])]
      simp [List.append_assoc]

def runSteps (input : Word MachineCodeSymbol) : Nat :=
  runStepsFrom [] input

theorem iterationSteps_eq
    (processed rest : Word MachineCodeSymbol) :
    iterationSteps processed rest =
      2 * (processed.length + rest.length) + 5 := by
  unfold iterationSteps
  lia

theorem runStepsFrom_eq
    (processed remaining : Word MachineCodeSymbol) :
    runStepsFrom processed remaining =
      remaining.length *
          (2 * (processed.length + remaining.length) + 3) +
        1 := by
  induction remaining generalizing processed with
  | nil =>
      rw [runStepsFrom]
      simp
  | cons current rest ih =>
      change List MachineCodeSymbol at processed
      rw [runStepsFrom]
      rw [ih (List.append processed [current])]
      rw [iterationSteps_eq]
      have hlength :
          (List.append processed [current]).length = processed.length + 1 := by
        simp
      rw [hlength]
      simp only [List.length_cons]
      lia

theorem runSteps_eq (input : Word MachineCodeSymbol) :
    runSteps input =
      input.length * (2 * input.length + 3) + 1 := by
  rw [runSteps, runStepsFrom_eq]
  simp

theorem run_exact
    (baseLeftRev input : Word MachineCodeSymbol) :
    machine.runConfigExact? (runSteps input)
        (sourceConfig baseLeftRev input) =
      some (haltConfig baseLeftRev input) := by
  simpa [runSteps, sourceConfig] using
    run_from_exact baseLeftRev ([] : Word MachineCodeSymbol) input

theorem run_exact_closed
    (baseLeftRev input : Word MachineCodeSymbol) :
    machine.runConfigExact?
        (input.length * (2 * input.length + 3) + 1)
        (sourceConfig baseLeftRev input) =
      some (haltConfig baseLeftRev input) := by
  rw [← runSteps_eq input]
  exact run_exact baseLeftRev input

theorem sourceTape_equiv_cursor
    (baseLeftRev input : Word MachineCodeSymbol) :
    Tape.Equiv (sourceTape baseLeftRev input)
      (SerializedShift.cursorTape baseLeftRev input) := by
  cases input with
  | nil =>
      simp [sourceTape, scanTape, tapeAtCells,
        SerializedShift.cursorTape, Tape.Equiv]
  | cons first rest =>
      simp [sourceTape, scanTape, tapeAtCells,
        SerializedShift.cursorTape, Tape.Equiv,
        FoC.Computability.dropTrailingNone_append_none]

def productBaseLeftRev (leftFuel : Nat) : Word MachineCodeSymbol :=
  (MachineDescription.encodeNat leftFuel).reverse

def productInnerCode
    (input : Word MachineCodeSymbol) (rightFuel : Nat) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend rightFuel input

def productSourceConfig
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  sourceConfig (productBaseLeftRev leftFuel)
    (productInnerCode input rightFuel)

def productTargetConfig
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  haltConfig (productBaseLeftRev leftFuel)
    (productInnerCode input rightFuel)

theorem productSourceTape_equiv_outerParserEndpoint
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    Tape.Equiv
      (productSourceConfig input leftFuel rightFuel).tape
      (ProductInput.PairFuelParser.config .inner
        (productBaseLeftRev leftFuel)
        (productInnerCode input rightFuel)).tape := by
  simpa [productSourceConfig, sourceConfig, scanConfig, sourceTape,
      ProductInput.PairFuelParser.config] using
    sourceTape_equiv_cursor (productBaseLeftRev leftFuel)
      (productInnerCode input rightFuel)

theorem product_run_exact
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    machine.runConfigExact?
        (runSteps (productInnerCode input rightFuel))
        (productSourceConfig input leftFuel rightFuel) =
      some (productTargetConfig input leftFuel rightFuel) := by
  exact run_exact (productBaseLeftRev leftFuel)
    (productInnerCode input rightFuel)

theorem product_run_exact_closed
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    machine.runConfigExact?
        ((productInnerCode input rightFuel).length *
            (2 * (productInnerCode input rightFuel).length + 3) + 1)
        (productSourceConfig input leftFuel rightFuel) =
      some (productTargetConfig input leftFuel rightFuel) := by
  exact run_exact_closed (productBaseLeftRev leftFuel)
    (productInnerCode input rightFuel)

theorem haltTape_nonempty_shape
    (baseLeftRev : Word MachineCodeSymbol)
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    haltTape baseLeftRev (first :: rest) =
      { left := none :: List.append
          ((first :: rest).reverse.map some) (baseLeftRev.map some)
        head := some first
        right := rest.map some } := by
  rfl

theorem haltTape_empty_shape
    (baseLeftRev : Word MachineCodeSymbol) :
    haltTape baseLeftRev [] =
      { left := none :: baseLeftRev.map some
        head := none
        right := [] } := by
  rfl

end ProductDuplicator

end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
