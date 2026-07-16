import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Initializer.Frontier
import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.EncodedList.Prepend

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.BooleanContextMaterializer

open FiniteRecognizer ExactFuel StrictProbe
open FiniteRecognizer.Interpreter.InitializerFrontier
open FiniteRecognizer.Interpreter.RuntimeEncodedList

/-!
# Boolean-context materializer

The parser stores the first input cell in outer finite control. The machine
consumes the raw tail from right to left; each raw symbol contributes its four
Boolean cells in reverse prepend order, and the saved symbol contributes its
three tail bits. Its first bit is the runtime lookup key. The `Prepend`
contract carries the parser word to the left of the right-context count as
`baseLeftRev`. The counter terminator stays encoded during the prepend
schedule and is converted to the copier separator during closeout.
-/

theorem prepend_targetWord_eq_encoded_list
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (cell : Option Bool)
    (suffix : Word MachineCodeSymbol) :
    Prepend.targetWord baseLeftRev cells.length cell
        (MachineDescription.encodeCellsAppend cells suffix) =
      List.append baseLeftRev.reverse
        (MachineDescription.encodeCellListAppend (cell :: cells) suffix) := by
  simp [Prepend.targetWord, MachineDescription.encodeCellListAppend,
    MachineDescription.encodeCellsAppend,
    MachineDescription.encodeNatAppend]

/-- One concrete `Prepend` phase, transported across harmless tape-window
padding.  This is the machine-level reuse theorem needed by every bit phase of
the outer raw-tail driver. -/
theorem prepend_cell_computes_encoded_list_of_tape_equiv
    (baseLeftRev : Word MachineCodeSymbol)
    (cells : List (Option Bool))
    (cell : Option Bool)
    (suffix : Word MachineCodeSymbol)
    (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Prepend.sourceConfig baseLeftRev cells.length
        (MachineDescription.encodeCellsAppend cells suffix)).tape
      sourceTape) :
    exists targetTape : Tape MachineCodeSymbol,
      TuringMachine.Computes (Prepend.machine cell)
        { state := Prepend.Control.locate .count
          tape := sourceTape }
        { state := Prepend.Control.insert (.rewind .gate)
          tape := targetTape } ∧
      Tape.Equiv
        (Tape.input
          (List.append baseLeftRev.reverse
            (MachineDescription.encodeCellListAppend
              (cell :: cells) suffix)))
        targetTape := by
  rcases Prepend.run_exact baseLeftRev cells.length cell
      (MachineDescription.encodeCellsAppend cells suffix) with
    ⟨canonicalEndpoint, hrun, hstate, hcanonicalTape⟩
  rcases canonicalEndpoint with ⟨canonicalState, canonicalTape⟩
  simp only at hstate
  subst canonicalState
  rcases TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
      hrun hsource with
    ⟨targetConfig, htargetRun, htargetState, htargetTape⟩
  rcases targetConfig with ⟨targetState, targetTape⟩
  simp only at htargetState
  subst targetState
  refine ⟨targetTape,
    TuringMachine.computesIn_to_computes
      (TuringMachine.runConfigExact?_eq_some_iff_computesIn.mp htargetRun),
    ?_⟩
  rw [prepend_targetWord_eq_encoded_list] at hcanonicalTape
  exact Tape.Equiv.trans hcanonicalTape htargetTape

def applyPrependSchedule
    {cell : Type}
    (schedule current : List cell) : List cell :=
  schedule.foldl (fun cells next => next :: cells) current

theorem applyPrependSchedule_eq_reverse_append
    {cell : Type}
    (schedule current : List cell) :
    applyPrependSchedule schedule current =
      List.append schedule.reverse current := by
  induction schedule generalizing current with
  | nil => rfl
  | cons next rest ih =>
      rw [applyPrependSchedule]
      simp only [List.foldl_cons]
      rw [← applyPrependSchedule, ih]
      simp [List.reverse_cons, List.append_assoc]

def rawTailPrependSchedule
    (tail : Word MachineCodeSymbol) : List (Option Bool) :=
  (inputBits tail).reverse.map some

def savedTailPrependSchedule
    (saved : MachineCodeSymbol) : List (Option Bool) :=
  (codeSymbolTailBits saved).reverse.map some

def nonemptyInputPrependSchedule
    (saved : MachineCodeSymbol)
    (tail : Word MachineCodeSymbol) : List (Option Bool) :=
  List.append (rawTailPrependSchedule tail)
    (savedTailPrependSchedule saved)

/-- Right-to-left raw traversal followed by the saved three-bit tail builds
exactly the Boolean right context of the initial tape. -/
theorem nonemptyInputPrependSchedule_exact
    (saved : MachineCodeSymbol)
    (tail : Word MachineCodeSymbol) :
    applyPrependSchedule (nonemptyInputPrependSchedule saved tail) [] =
      (List.append (codeSymbolTailBits saved) (inputBits tail)).map some := by
  rw [applyPrependSchedule_eq_reverse_append]
  simp [nonemptyInputPrependSchedule, rawTailPrependSchedule,
    savedTailPrependSchedule, List.reverse_append]

theorem nonemptyInputPrependSchedule_eq_initial_right
    (saved : MachineCodeSymbol)
    (tail : Word MachineCodeSymbol) :
    applyPrependSchedule (nonemptyInputPrependSchedule saved tail) [] =
      (initialTape (saved :: tail)).right := by
  rw [nonemptyInputPrependSchedule_exact]
  rw [initialTape_cons]

/-- Executable materializer contract. The setup phase rewrites the parser
separator, installs two empty encoded context lists, and enters the raw-tail
loop. The loop realizes `nonemptyInputPrependSchedule`. Closeout converts the
encoded counter terminator to the copier separator and removes the input
marker, producing `positiveMaterializerTargetConfig`. The public caller suffix
is empty, and the active context suffix contains no fuel word. -/
def SavedRawTailPrependDriverContract
    {driverState : Type}
    (driver : TuringMachine MachineCodeSymbol driverState)
    (entry : Option MachineCodeSymbol -> driverState)
    (halt : driverState) : Prop :=
  SavedPositiveBooleanContextMaterializerContract driver entry halt


end FiniteRecognizer.Interpreter.BooleanContextMaterializer

end Computability
end FoC
