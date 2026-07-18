import FoC.Computability.Compiler.Core.SelfHaltingRecognizer.ValidatorDeterminismGate.Runs.SourceFinish

set_option doc.verso true

/-!
# Exact-code validator: selected-pair layouts

These suffix definitions name the fixed action and target segments of a row.
They keep the field-comparison proofs independent of list reassociation and
make the temporary source markers explicit.
-/

namespace FoC
namespace Computability
namespace SelfHaltingRecognizer
namespace ValidatorDeterminismGate

open Languages
open MachineDescription

/-- The logical table has reached its explicit nonhalting conflict state. -/
def ReachesConflict
    (source : ValidatorBlockDescription.Configuration) : Prop :=
  exists left right : Word ValidatorBlockSymbol,
    blockDescription.Reaches source (configuration 100 left right)

/-- Prefixing a conflict run preserves conflict reachability. -/
theorem ReachesConflict.of_reaches
    {source middle : ValidatorBlockDescription.Configuration}
    (hsource : blockDescription.Reaches source middle)
    (hmiddle : ReachesConflict middle) :
    ReachesConflict source := by
  rcases hmiddle with ⟨left, right, hconflict⟩
  exact ⟨left, right, hsource.trans hconflict⟩

/-- Row suffix beginning at the target field. -/
def rowTargetAndEndBlocks
    (row : TransitionDescription)
    (endSymbol : ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  List.append (List.replicate row.target .tick) [endSymbol]

/-- Row suffix immediately after the write symbol. -/
def rowAfterWriteBlocks
    (row : TransitionDescription)
    (endSymbol : ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  ValidatorCountedRows.directionBlock row.move ::
    rowTargetAndEndBlocks row endSymbol

/-- Row suffix immediately after the read symbol. -/
def rowAfterReadBlocks
    (row : TransitionDescription)
    (endSymbol : ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  ValidatorCountedRows.cellBlock row.write ::
    rowAfterWriteBlocks row endSymbol

/-- Row suffix immediately after the source terminator. -/
def rowAfterSourceBlocks
    (row : TransitionDescription)
    (endSymbol : ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  ValidatorCountedRows.cellBlock row.read ::
    rowAfterReadBlocks row endSymbol

/-- A selected row interior with a fully paired source field. -/
def markedSourceInterior
    (row : TransitionDescription) (paired : Nat)
    (endSymbol : ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  List.append (List.replicate paired .marker010)
    (.done :: rowAfterSourceBlocks row endSymbol)

/-- State-5 layout for a selected outer/inner pair.  The outer row necessarily
has a normal terminator because the inner row follows it. -/
def selectedPairSourceRight
    (outer inner : TransitionDescription) (paired : Nat)
    (between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  List.append (markedSourceInterior outer paired .done)
    (List.append between
      (.marker001 ::
        List.append (markedSourceInterior inner paired innerEnd) rest))

/-- State-15 layout at the outer read field. -/
def selectedPairReadRight
    (outer inner : TransitionDescription) (paired : Nat)
    (between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  List.append (rowAfterSourceBlocks outer .done)
    (List.append between
      (.marker001 ::
        List.append (markedSourceInterior inner paired innerEnd) rest))

/-- State-29 layout at the outer write field. -/
def selectedPairWriteRight
    (outer inner : TransitionDescription) (paired : Nat)
    (between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  List.append (rowAfterReadBlocks outer .done)
    (List.append between
      (.marker001 ::
        List.append (markedSourceInterior inner paired innerEnd) rest))

/-- State-47 layout at the outer move field. -/
def selectedPairMoveRight
    (outer inner : TransitionDescription) (paired : Nat)
    (between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  List.append (rowAfterWriteBlocks outer .done)
    (List.append between
      (.marker001 ::
        List.append (markedSourceInterior inner paired innerEnd) rest))

/-- State-64 layout at the outer target field. -/
def selectedPairTargetRight
    (outer inner : TransitionDescription) (paired : Nat)
    (between : Word ValidatorBlockSymbol)
    (innerEnd : ValidatorBlockSymbol)
    (rest : Word ValidatorBlockSymbol) :
    Word ValidatorBlockSymbol :=
  List.append (rowTargetAndEndBlocks outer .done)
    (List.append between
      (.marker001 ::
        List.append (markedSourceInterior inner paired innerEnd) rest))

end ValidatorDeterminismGate
end SelfHaltingRecognizer
end Computability
end FoC
