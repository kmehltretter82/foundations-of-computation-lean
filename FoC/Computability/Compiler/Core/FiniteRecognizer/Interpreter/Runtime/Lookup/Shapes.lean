import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.Lookup.Mismatch

namespace FoC
namespace Computability

open Languages

namespace Section53UniformInterpreterOneStep

/-- The untouched action fields and canonical remaining table after a row key. -/
def runtimeKeyCanonicalActionSuffix
    (transition : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeCellAppend transition.write
    (MachineDescription.encodeDirectionAppend transition.move
      (MachineDescription.encodeNatAppend transition.target
        (MachineDescription.encodeTransitionsAppend rest suffix)))
theorem runtimeKey_encodeNat_eq_replicate_tick_done
    (value : Nat) :
    MachineDescription.encodeNat value =
      List.append
        (List.replicate value MachineCodeSymbol.tick)
        [MachineCodeSymbol.done] := by
  induction value with
  | zero => rfl
  | succ value ih =>
      simp [MachineDescription.encodeNat, ih, List.replicate_succ]
  done

theorem runtimeKey_encodeCell_eq_singleton
    (cell : Option Bool) :
    MachineDescription.encodeCell cell = [runtimeKeyCellSymbol cell] := by
  cases cell with
  | none => rfl
  | some bit =>
      cases bit <;> rfl
  done

def runtimeKeyRepeatedTableFrame
    (queryState : Nat) (queryRead : Option Bool) :
    List TransitionDescription -> Word MachineCodeSymbol ->
      Word MachineCodeSymbol
  | [], suffix => MachineCodeSymbol.done :: suffix
  | transition :: rest, suffix =>
      MachineCodeSymbol.header ::
        MachineDescription.encodeNatAppend queryState
          (MachineDescription.encodeCellAppend queryRead
            (MachineDescription.encodeTransitionAppend transition
              (runtimeKeyRepeatedTableFrame queryState queryRead
                rest suffix)))

def runtimeKeyRepeatedActionSuffix
    (queryState : Nat) (queryRead : Option Bool)
    (transition : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeCellAppend transition.write
    (MachineDescription.encodeDirectionAppend transition.move
      (MachineDescription.encodeNatAppend transition.target
        (runtimeKeyRepeatedTableFrame queryState queryRead rest suffix)))

def runtimeKeyDirectionSymbol : Direction -> MachineCodeSymbol
  | Direction.left => MachineCodeSymbol.moveLeft
  | Direction.right => MachineCodeSymbol.moveRight

theorem runtimeKey_encodeDirection_eq_singleton
    (dir : Direction) :
    MachineDescription.encodeDirection dir =
      [runtimeKeyDirectionSymbol dir] := by
  cases dir <;> rfl
  done
def runtimeKeyRepeatedRowTargetTape
    (baseLeftRev : Word MachineCodeSymbol)
    (queryState : Nat) (queryRead : Option Bool)
    (transition : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  runtimeKeyComparatorTape
    (runtimeKeyComparatorRestoredLeft
      (List.replicate queryState MachineCodeSymbol.tick)
      queryRead
      (List.replicate transition.source MachineCodeSymbol.tick)
      transition.read (MachineCodeSymbol.header :: baseLeftRev))
    (runtimeKeyRepeatedActionSuffix queryState queryRead
      transition rest suffix)
/-- Self-delimiting lookup key that must be physically present at entry. -/
def runtimeKeyBuilderKeyCode
    (queryState : Nat) (queryRead : Option Bool) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend queryState
    (MachineDescription.encodeCell queryRead)
def runtimeKeyRawTransitionTail
    (transition : TransitionDescription)
    (rest : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend transition.source
    (MachineDescription.encodeCellAppend transition.read
      (MachineDescription.encodeCellAppend transition.write
        (MachineDescription.encodeDirectionAppend transition.move
          (MachineDescription.encodeNatAppend transition.target
            (MachineDescription.encodeTransitionsAppend rest suffix)))))


namespace RuntimeKeySelectedExtractor

def actionBase
    (baseLeftRev : Word MachineCodeSymbol)
    (queryState : Nat) (queryRead : Option Bool) :
    Word MachineCodeSymbol :=
  runtimeKeyCellSymbol queryRead ::
    MachineCodeSymbol.done ::
    List.append
      (List.replicate queryState MachineCodeSymbol.tick).reverse
      (MachineCodeSymbol.header :: baseLeftRev)

def selectedPrefixLeft
    (baseLeftRev : Word MachineCodeSymbol)
    (queryState : Nat) (queryRead : Option Bool)
    (selected : TransitionDescription) : Word MachineCodeSymbol :=
  runtimeKeyComparatorRestoredLeft
    (List.replicate queryState MachineCodeSymbol.tick)
    queryRead
    (List.replicate selected.source MachineCodeSymbol.tick)
    selected.read (MachineCodeSymbol.header :: baseLeftRev)
def rowTail (selected : TransitionDescription) :
    Word MachineCodeSymbol :=
  runtimeKeyRawTransitionTail selected [] []

def NoTransition (symbols : List MachineCodeSymbol) : Prop :=
  forall symbol : MachineCodeSymbol,
    symbol ∈ symbols -> symbol ≠ MachineCodeSymbol.transition

theorem noTransition_append
    {left right : List MachineCodeSymbol}
    (hleft : NoTransition left)
    (hright : NoTransition right) :
    NoTransition (List.append left right) := by
  intro symbol hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft symbol hmem
  · exact hright symbol hmem
  done

theorem noTransition_reverse
    {symbols : List MachineCodeSymbol}
    (hnoTransition : NoTransition symbols) :
    NoTransition symbols.reverse := by
  intro symbol hmem
  exact hnoTransition symbol (by simpa using hmem)
  done

theorem encodeNat_no_transition
    (value : Nat) :
    NoTransition (MachineDescription.encodeNat value) := by
  induction value with
  | zero =>
      intro symbol hmem
      simp [MachineDescription.encodeNat] at hmem
      subst symbol
      simp
  | succ value ih =>
      intro symbol hmem
      rcases List.mem_cons.mp hmem with hmem | hmem
      · subst symbol
        simp
      · exact ih symbol hmem
  done

theorem encodeCell_no_transition
    (cell : Option Bool) :
    NoTransition (MachineDescription.encodeCell cell) := by
  cases cell with
  | none =>
      intro symbol hmem
      simp [MachineDescription.encodeCell] at hmem
      subst symbol
      simp
  | some bit =>
      cases bit <;>
        intro symbol hmem <;>
        simp [MachineDescription.encodeCell] at hmem <;>
        subst symbol <;>
        simp
  done

theorem encodeDirection_no_transition
    (move : Direction) :
    NoTransition (MachineDescription.encodeDirection move) := by
  cases move <;>
    intro symbol hmem <;>
    simp [MachineDescription.encodeDirection] at hmem <;>
    subst symbol <;>
    simp
  done

theorem encodeNatAppend_no_transition
    (value : Nat) {suffix : List MachineCodeSymbol}
    (hsuffix : NoTransition suffix) :
    NoTransition (MachineDescription.encodeNatAppend value suffix) := by
  simpa [MachineDescription.encodeNatAppend] using
    noTransition_append (encodeNat_no_transition value) hsuffix
  done

theorem encodeCellAppend_no_transition
    (cell : Option Bool) {suffix : List MachineCodeSymbol}
    (hsuffix : NoTransition suffix) :
    NoTransition (MachineDescription.encodeCellAppend cell suffix) := by
  simpa [MachineDescription.encodeCellAppend] using
    noTransition_append (encodeCell_no_transition cell) hsuffix
  done

theorem encodeDirectionAppend_no_transition
    (move : Direction) {suffix : List MachineCodeSymbol}
    (hsuffix : NoTransition suffix) :
    NoTransition
      (MachineDescription.encodeDirectionAppend move suffix) := by
  simpa [MachineDescription.encodeDirectionAppend] using
    noTransition_append (encodeDirection_no_transition move) hsuffix
  done

theorem rowTail_no_transition
    (selected : TransitionDescription) :
    NoTransition (rowTail selected) := by
  unfold rowTail runtimeKeyRawTransitionTail
  exact encodeNatAppend_no_transition selected.source
    (encodeCellAppend_no_transition selected.read
      (encodeCellAppend_no_transition selected.write
        (encodeDirectionAppend_no_transition selected.move
          (encodeNatAppend_no_transition selected.target (by
            intro symbol hmem
            simp [MachineDescription.encodeTransitionsAppend] at hmem)))))
  done

theorem rowTail_ne_nil
    (selected : TransitionDescription) :
    rowTail selected ≠ [] := by
  rcases selected with ⟨source, read, write, move, target⟩
  cases source <;>
    simp [rowTail, runtimeKeyRawTransitionTail,
      MachineDescription.encodeNatAppend,
      MachineDescription.encodeNat]
  done

def rewindTape
    (baseLeftRev remaining crossed : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match remaining with
  | [] =>
      runtimeKeyComparatorTape baseLeftRev
        (MachineCodeSymbol.transition :: crossed)
  | current :: more =>
      runtimeKeyComparatorTape
        (List.append more
          (MachineCodeSymbol.transition :: baseLeftRev))
        (current :: crossed)


end RuntimeKeySelectedExtractor

end Section53UniformInterpreterOneStep
end Computability
end FoC
