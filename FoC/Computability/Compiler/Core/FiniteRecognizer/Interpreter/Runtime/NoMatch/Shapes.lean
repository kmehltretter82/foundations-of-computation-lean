import FoC.Computability.Compiler.Core.FiniteRecognizer.Interpreter.Runtime.NoMatch.Builders

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer.Interpreter.NoMatchFinalGate

open FiniteRecognizer ExactFuel StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep
open FiniteRecognizer.Interpreter.UniformInterpreterOneStep.RuntimeKeySingleKeyRepair
open FiniteRecognizer.Interpreter.LoopRestagingAudit
open FiniteRecognizer.Interpreter.StackIteration
open FiniteRecognizer.Interpreter.FinalGateMaterializer

namespace LastMiss

abbrev NoTransition := RuntimeKeySelectedExtractor.NoTransition

theorem noTransition_tail
    (first : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol)
    (h : NoTransition (first :: rest)) :
    NoTransition rest := by
  intro symbol hmem
  exact h symbol (List.Mem.tail first hmem)
  done

theorem noTransition_append
    (left right : Word MachineCodeSymbol)
    (hleft : NoTransition left)
    (hright : NoTransition right) :
    NoTransition (List.append left right) := by
  intro symbol hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft symbol hmem
  · exact hright symbol hmem
  done

theorem noTransition_header :
    NoTransition [MachineCodeSymbol.header] := by
  intro symbol hmem
  have hsymbol := List.mem_singleton.mp hmem
  subst symbol
  simp
  done

theorem encodeNat_noTransition
    (value : Nat) :
    NoTransition (MachineDescription.encodeNat value) := by
  induction value with
  | zero =>
      intro symbol hmem
      have hsymbol := List.mem_singleton.mp hmem
      subst symbol
      simp
  | succ value ih =>
      intro symbol hmem
      rcases List.mem_cons.mp hmem with htick | htail
      · subst symbol
        simp
      · exact ih symbol htail
  done

theorem encodeCells_noTransition
    (cells : List (Option Bool)) :
    NoTransition (MachineDescription.encodeCellsAppend cells []) := by
  induction cells with
  | nil =>
      intro symbol hmem
      cases hmem
  | cons cell rest ih =>
      intro symbol hmem
      cases cell with
      | none =>
          change List.Mem symbol
            (MachineCodeSymbol.blank ::
              MachineDescription.encodeCellsAppend rest []) at hmem
          rcases List.mem_cons.mp hmem with hblank | htail
          · subst symbol
            simp
          · exact ih symbol htail
      | some bit =>
          cases bit with
          | false =>
              change List.Mem symbol
                (MachineCodeSymbol.zero ::
                  MachineDescription.encodeCellsAppend rest []) at hmem
              rcases List.mem_cons.mp hmem with hzero | htail
              · subst symbol
                simp
              · exact ih symbol htail
          | true =>
              change List.Mem symbol
                (MachineCodeSymbol.one ::
                  MachineDescription.encodeCellsAppend rest []) at hmem
              rcases List.mem_cons.mp hmem with hone | htail
              · subst symbol
                simp
              · exact ih symbol htail
  done

theorem encodeCellList_noTransition
    (cells : List (Option Bool)) :
    NoTransition (MachineDescription.encodeCellListAppend cells []) := by
  rw [show MachineDescription.encodeCellListAppend cells [] =
      List.append (MachineDescription.encodeNat cells.length)
        (MachineDescription.encodeCellsAppend cells []) by rfl]
  exact noTransition_append _ _
    (encodeNat_noTransition cells.length)
    (encodeCells_noTransition cells)
  done

theorem contextPrefix_noTransition
    (left right : List (Option Bool)) :
    NoTransition (contextPrefix left right) := by
  have hshape : contextPrefix left right =
      List.append
        (MachineDescription.encodeCellListAppend left [])
        (MachineDescription.encodeCellListAppend right []) := by
    simpa [contextPrefix] using
      (encodeCellListAppend_append left []
        (MachineDescription.encodeCellListAppend right []))
  rw [hshape]
  exact noTransition_append _ _
    (encodeCellList_noTransition left)
    (encodeCellList_noTransition right)
  done

theorem noTransition_append_marker_noDouble
    (symbols : Word MachineCodeSymbol)
    (hnoTransition : NoTransition symbols) :
    CurrentBuilder.NoDoubleTransition
      (List.append symbols [MachineCodeSymbol.transition]) := by
  induction symbols with
  | nil =>
      intro left tail heq
      have hlength := congrArg List.length heq
      simp at hlength
      lia
  | cons current rest ih =>
      have hcurrent : current ≠ MachineCodeSymbol.transition :=
        hnoTransition current (List.Mem.head rest)
      have hrest := noTransition_tail current rest hnoTransition
      intro left tail heq
      cases left with
      | nil =>
          have hhead := congrArg List.head? heq
          simp at hhead
          exact hcurrent hhead
      | cons first more =>
          have htailEq :
              List.append rest [MachineCodeSymbol.transition] =
                List.append more
                  (MachineCodeSymbol.transition ::
                    MachineCodeSymbol.transition :: tail) := by
            have := congrArg List.tail heq
            simpa using this
          exact ih hrest more tail htailEq
  done

def AdjacentSafe : Word MachineCodeSymbol -> Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      (first ≠ MachineCodeSymbol.transition ∨
        second ≠ MachineCodeSymbol.transition) ∧
      AdjacentSafe (second :: rest)

theorem adjacentSafe_of_noTransition
    (symbols : Word MachineCodeSymbol)
    (hnoTransition : NoTransition symbols) :
    AdjacentSafe symbols := by
  induction symbols with
  | nil => trivial
  | cons first rest ih =>
      cases rest with
      | nil => trivial
      | cons second tail =>
          change
            (first ≠ MachineCodeSymbol.transition ∨
                second ≠ MachineCodeSymbol.transition) ∧
              AdjacentSafe (second :: tail)
          constructor
          · exact Or.inl
              (hnoTransition first (List.Mem.head (second :: tail)))
          · exact ih (noTransition_tail first (second :: tail)
              hnoTransition)
  done

theorem adjacentSafe_append_of_noTransition_left
    (left right : Word MachineCodeSymbol)
    (hleft : NoTransition left)
    (hright : AdjacentSafe right) :
    AdjacentSafe (List.append left right) := by
  induction left with
  | nil => exact hright
  | cons first rest ih =>
      have hfirst := hleft first (List.Mem.head rest)
      have hrest := noTransition_tail first rest hleft
      cases rest with
      | nil =>
          cases right with
          | nil => trivial
          | cons second tail =>
              cases tail with
              | nil => exact ⟨Or.inl hfirst, trivial⟩
              | cons third more =>
                  exact ⟨Or.inl hfirst, hright⟩
      | cons second tail =>
          change
            (first ≠ MachineCodeSymbol.transition ∨
                second ≠ MachineCodeSymbol.transition) ∧
              AdjacentSafe
                (List.append (second :: tail) right)
          exact ⟨Or.inl hfirst, ih hrest⟩
  done

theorem adjacentSafe_cons_of_head_ne
    (head : MachineCodeSymbol)
    (tail : Word MachineCodeSymbol)
    (hhead : head ≠ MachineCodeSymbol.transition)
    (htail : AdjacentSafe tail) :
    AdjacentSafe (head :: tail) := by
  cases tail with
  | nil => trivial
  | cons second rest =>
      cases rest with
      | nil => exact ⟨Or.inl hhead, trivial⟩
      | cons third more => exact ⟨Or.inl hhead, htail⟩
  done

theorem adjacentSafe_append_of_right_head_ne
    (left : Word MachineCodeSymbol)
    (head : MachineCodeSymbol)
    (right : Word MachineCodeSymbol)
    (hleft : AdjacentSafe left)
    (hhead : head ≠ MachineCodeSymbol.transition)
    (hright : AdjacentSafe (head :: right)) :
    AdjacentSafe (List.append left (head :: right)) := by
  induction left with
  | nil => exact hright
  | cons first rest ih =>
      cases rest with
      | nil =>
          cases right with
          | nil => exact ⟨Or.inr hhead, trivial⟩
          | cons second tail => exact ⟨Or.inr hhead, hright⟩
      | cons second tail =>
          have hpairs :
              (first ≠ MachineCodeSymbol.transition ∨
                second ≠ MachineCodeSymbol.transition) ∧
              AdjacentSafe (second :: tail) := hleft
          change
            (first ≠ MachineCodeSymbol.transition ∨
                second ≠ MachineCodeSymbol.transition) ∧
              AdjacentSafe
                (List.append (second :: tail) (head :: right))
          exact ⟨hpairs.left, ih hpairs.right⟩
  done

theorem adjacentSafe_to_noDouble
    (symbols : Word MachineCodeSymbol)
    (hsafe : AdjacentSafe symbols) :
    CurrentBuilder.NoDoubleTransition symbols := by
  induction symbols with
  | nil =>
      intro left tail heq
      have hlength := congrArg List.length heq
      simp at hlength
  | cons first rest ih =>
      cases rest with
      | nil =>
          intro left tail heq
          have hlength := congrArg List.length heq
          simp at hlength
          lia
      | cons second tail =>
          intro left suffix heq
          cases left with
          | nil =>
              have hfirst : first = MachineCodeSymbol.transition := by
                simpa using congrArg List.head? heq
              have htailEq := congrArg List.tail heq
              have hsecond : second = MachineCodeSymbol.transition := by
                simpa using congrArg List.head? htailEq
              exact hsafe.left.elim
                (fun h => h hfirst) (fun h => h hsecond)
          | cons prefixHead prefixTail =>
              have htailEq : second :: tail =
                  List.append prefixTail
                    (MachineCodeSymbol.transition ::
                      MachineCodeSymbol.transition :: suffix) := by
                have := congrArg List.tail heq
                simpa using this
              exact ih hsafe.right prefixTail suffix htailEq
  done

theorem encodeTransitions_cons_shape
    (row : TransitionDescription)
    (rows : List TransitionDescription) :
    MachineDescription.encodeTransitions (row :: rows) =
      MachineCodeSymbol.transition ::
        List.append (RuntimeKeySelectedExtractor.rowTail row)
          (MachineDescription.encodeTransitions rows) := by
  rcases row with ⟨source, read, write, move, target⟩
  simp [MachineDescription.encodeTransitions,
    MachineDescription.encodeTransitionsAppend,
    MachineDescription.encodeTransitionAppend,
    RuntimeKeySelectedExtractor.rowTail,
    runtimeKeyRawTransitionTail,
    MachineDescription.encodeNatAppend,
    MachineDescription.encodeCellAppend,
    MachineDescription.encodeDirectionAppend,
    List.append_assoc]
  done

theorem encodeTransitions_adjacentSafe
    (rows : List TransitionDescription) :
    AdjacentSafe (MachineDescription.encodeTransitions rows) := by
  induction rows with
  | nil => trivial
  | cons row rest ih =>
      rw [encodeTransitions_cons_shape]
      have htailNo := RuntimeKeySelectedExtractor.rowTail_no_transition row
      have htailNonempty := RuntimeKeySelectedExtractor.rowTail_ne_nil row
      cases htail : RuntimeKeySelectedExtractor.rowTail row with
      | nil => exact False.elim (htailNonempty htail)
      | cons first tail =>
          change
            (MachineCodeSymbol.transition ≠ MachineCodeSymbol.transition ∨
                first ≠ MachineCodeSymbol.transition) ∧
              AdjacentSafe
                (List.append (first :: tail)
                  (MachineDescription.encodeTransitions rest))
          constructor
          · exact Or.inr
              (htailNo first (by rw [htail]; exact List.Mem.head tail))
          · apply adjacentSafe_append_of_noTransition_left
            · simpa [htail] using htailNo
            · exact ih
  done

theorem rawTable_adjacentSafe
    (transitions : List TransitionDescription) :
    AdjacentSafe (rawTable transitions) := by
  exact encodeTransitions_adjacentSafe transitions
  done

theorem tableStack_append_adjacentSafe
    (transitions : List TransitionDescription)
    (copies : Nat)
    (suffix : Word MachineCodeSymbol)
    (hsuffix : AdjacentSafe suffix) :
    AdjacentSafe
      (List.append (tableStack transitions copies) suffix) := by
  induction copies with
  | zero =>
      rw [tableStack_zero]
      exact adjacentSafe_cons_of_head_ne MachineCodeSymbol.header suffix
        (by simp) hsuffix
  | succ copies ih =>
      rw [tableStack_succ]
      have htail : AdjacentSafe
          (MachineCodeSymbol.header ::
            List.append (tableStack transitions copies) suffix) :=
        adjacentSafe_cons_of_head_ne MachineCodeSymbol.header _
          (by simp) ih
      simpa [List.append_assoc] using
        adjacentSafe_append_of_right_head_ne
          (rawTable transitions) MachineCodeSymbol.header
          (List.append (tableStack transitions copies) suffix)
          (rawTable_adjacentSafe transitions) (by simp) htail
  done

def middleWordCopies
    (skipped transitions : List TransitionDescription)
    (copies : Nat)
    (contextFront : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (processedRows skipped)
    (MachineCodeSymbol.header ::
      List.append (tableStack transitions copies) contextFront)

theorem middleWordCopies_append_marker_noDouble
    (skipped transitions : List TransitionDescription)
    (copies : Nat)
    (contextFront : Word MachineCodeSymbol)
    (hcontext : NoTransition contextFront) :
    CurrentBuilder.NoDoubleTransition
      (List.append (middleWordCopies skipped transitions copies contextFront)
        [MachineCodeSymbol.transition]) := by
  have hcontextMarker : AdjacentSafe
      (List.append contextFront [MachineCodeSymbol.transition]) :=
    adjacentSafe_append_of_noTransition_left contextFront
      [MachineCodeSymbol.transition] hcontext (by trivial)
  have hstack := tableStack_append_adjacentSafe transitions copies
    (List.append contextFront [MachineCodeSymbol.transition]) hcontextMarker
  have hguard := adjacentSafe_cons_of_head_ne MachineCodeSymbol.header _
    (by simp) hstack
  have hall := adjacentSafe_append_of_noTransition_left
    (processedRows skipped)
    (MachineCodeSymbol.header ::
      List.append (tableStack transitions copies)
        (List.append contextFront [MachineCodeSymbol.transition]))
    (processedRows_no_transition skipped) hguard
  apply adjacentSafe_to_noDouble
  simpa [middleWordCopies, List.append_assoc] using hall
  done

theorem tableStack_decompose
    (transitions : List TransitionDescription)
    (copies : Nat) :
    exists first : MachineCodeSymbol, exists rest : Word MachineCodeSymbol,
      tableStack transitions copies = first :: rest := by
  cases copies with
  | zero =>
      exact ⟨MachineCodeSymbol.header, [], rfl⟩
  | succ copies =>
      rw [tableStack_succ]
      cases hraw : rawTable transitions with
      | nil =>
          exact ⟨MachineCodeSymbol.header,
            tableStack transitions copies, by simp [hraw]⟩
      | cons first rest =>
          exact ⟨first,
            List.append rest
              (MachineCodeSymbol.header :: tableStack transitions copies),
            by simp [hraw]⟩
  done

theorem middleWordCopies_decompose
    (skipped transitions : List TransitionDescription)
    (copies : Nat)
    (contextFront : Word MachineCodeSymbol)
    (hcontext : NoTransition contextFront) :
    exists firstJunk secondJunk : MachineCodeSymbol,
    exists gap : Word MachineCodeSymbol,
      middleWordCopies skipped transitions copies contextFront =
        firstJunk :: secondJunk :: gap ∧
      CurrentBuilder.NoDoubleTransition
        (List.append gap [MachineCodeSymbol.transition]) := by
  have hfull := middleWordCopies_append_marker_noDouble
    skipped transitions copies contextFront hcontext
  let processed : Word MachineCodeSymbol := processedRows skipped
  cases hprocessed : processed with
  | nil =>
      rcases tableStack_decompose transitions copies with
        ⟨stackHead, stackTail, hstack⟩
      let gap : Word MachineCodeSymbol :=
        List.append stackTail contextFront
      have hfull' : CurrentBuilder.NoDoubleTransition
          (List.append
            (MachineCodeSymbol.header :: stackHead :: gap)
            [MachineCodeSymbol.transition]) := by
        simpa [middleWordCopies, processed, hprocessed, hstack, gap,
          List.append_assoc] using hfull
      refine ⟨MachineCodeSymbol.header, stackHead, gap, ?_, ?_⟩
      · simp [middleWordCopies, processed, hprocessed, hstack, gap]
      · exact CurrentBuilder.noDouble_tail stackHead gap
          (CurrentBuilder.noDouble_tail MachineCodeSymbol.header
            (stackHead :: gap) hfull')
  | cons firstJunk rest =>
      cases hrest : rest with
      | nil =>
          let gap : Word MachineCodeSymbol :=
            List.append (tableStack transitions copies) contextFront
          have hfull' : CurrentBuilder.NoDoubleTransition
              (List.append
                (firstJunk :: MachineCodeSymbol.header :: gap)
                [MachineCodeSymbol.transition]) := by
            simpa [middleWordCopies, processed, hprocessed, hrest, gap,
              List.append_assoc] using hfull
          refine ⟨firstJunk, MachineCodeSymbol.header, gap, ?_, ?_⟩
          · simp [middleWordCopies, processed, hprocessed, hrest, gap]
          · exact CurrentBuilder.noDouble_tail MachineCodeSymbol.header gap
              (CurrentBuilder.noDouble_tail firstJunk
                (MachineCodeSymbol.header :: gap) hfull')
      | cons secondJunk processedTail =>
          let gap : Word MachineCodeSymbol :=
            List.append processedTail
              (MachineCodeSymbol.header ::
                List.append (tableStack transitions copies) contextFront)
          have hfull' : CurrentBuilder.NoDoubleTransition
              (List.append (firstJunk :: secondJunk :: gap)
                [MachineCodeSymbol.transition]) := by
            simpa [middleWordCopies, processed, hprocessed, hrest, gap,
              List.append_assoc] using hfull
          refine ⟨firstJunk, secondJunk, gap, ?_, ?_⟩
          · simp [middleWordCopies, processed, hprocessed, hrest, gap]
          · exact CurrentBuilder.noDouble_tail secondJunk gap
              (CurrentBuilder.noDouble_tail firstJunk
                (secondJunk :: gap) hfull')
  done

theorem noTransition_of_append
    (left right : Word MachineCodeSymbol)
    (h : NoTransition (List.append left right)) :
    NoTransition right := by
  intro symbol hmem
  exact h symbol (List.mem_append_right left hmem)
  done

theorem noTransition_prefix
    (left right : Word MachineCodeSymbol)
    (h : NoTransition (List.append left right)) :
    NoTransition left := by
  intro symbol hmem
  exact h symbol (List.mem_append_left right hmem)
  done

theorem encodeNat_length_local
    (value : Nat) :
    (MachineDescription.encodeNat value).length = value + 1 := by
  induction value with
  | zero => rfl
  | succ value ih =>
      simp [MachineDescription.encodeNat, ih]
  done

theorem contextPrefix_length_ge_two
    (left right : List (Option Bool)) :
    2 <= (contextPrefix left right).length := by
  simp [contextPrefix, MachineDescription.encodeCellListAppend,
    MachineDescription.encodeNatAppend,
    encodeNat_length_local,
    encodeCellsAppend_length]
  lia
  done

theorem contextPrefix_split_last_two
    (left right : List (Option Bool)) :
    exists firstBefore secondBefore : MachineCodeSymbol,
    exists contextFront : Word MachineCodeSymbol,
      contextPrefix left right =
        List.append contextFront [firstBefore, secondBefore] ∧
      NoTransition contextFront := by
  have hlen := contextPrefix_length_ge_two left right
  cases hreverse : (contextPrefix left right).reverse with
  | nil =>
      have hlength : (contextPrefix left right).length = 0 := by
        rw [← List.length_reverse]
        rw [hreverse]
        rfl
      lia
  | cons secondBefore tail =>
      cases tail with
      | nil =>
          have hlength : (contextPrefix left right).length = 1 := by
            rw [← List.length_reverse]
            rw [hreverse]
            rfl
          lia
      | cons firstBefore contextFrontRev =>
          let contextFront : Word MachineCodeSymbol :=
            contextFrontRev.reverse
          have hshape : contextPrefix left right =
              List.append contextFront [firstBefore, secondBefore] := by
            have hrev := congrArg List.reverse hreverse
            change (show List MachineCodeSymbol from contextPrefix left right) =
              List.append contextFront [firstBefore, secondBefore]
            simpa [contextFront, List.reverse_cons, List.append_assoc]
              using hrev
          have hnoTransition : NoTransition contextFront := by
            apply noTransition_prefix contextFront
              [firstBefore, secondBefore]
            rw [← hshape]
            exact contextPrefix_noTransition left right
          exact ⟨firstBefore, secondBefore, contextFront,
            hshape, hnoTransition⟩
  done

def middleWord
    (skipped : List TransitionDescription)
    (contextFront : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (processedRows skipped)
    (MachineCodeSymbol.header :: MachineCodeSymbol.header :: contextFront)

theorem middleWord_noTransition
    (skipped : List TransitionDescription)
    (contextFront : Word MachineCodeSymbol)
    (hcontext : NoTransition contextFront) :
    NoTransition (middleWord skipped contextFront) := by
  apply noTransition_append
  · exact processedRows_no_transition skipped
  · intro symbol hmem
    rcases List.mem_cons.mp hmem with hheader | hmem
    · subst symbol
      simp
    · rcases List.mem_cons.mp hmem with hheader | hcontextMem
      · subst symbol
        simp
      · exact hcontext symbol hcontextMem
  done

theorem middleWord_decompose
    (skipped : List TransitionDescription)
    (contextFront : Word MachineCodeSymbol)
    (hcontext : NoTransition contextFront) :
    exists firstJunk secondJunk : MachineCodeSymbol,
    exists gap : Word MachineCodeSymbol,
      middleWord skipped contextFront = firstJunk :: secondJunk :: gap ∧
      NoTransition gap := by
  let processed : Word MachineCodeSymbol := processedRows skipped
  have hmiddle := middleWord_noTransition skipped contextFront hcontext
  cases hprocessed : processed with
  | nil =>
      refine ⟨MachineCodeSymbol.header, MachineCodeSymbol.header,
        contextFront, ?_, hcontext⟩
      simp [middleWord, processed, hprocessed]
  | cons firstJunk rest =>
      cases hrest : rest with
      | nil =>
          refine ⟨firstJunk, MachineCodeSymbol.header,
            MachineCodeSymbol.header :: contextFront, ?_, ?_⟩
          · simp [middleWord, processed, hprocessed, hrest]
          · have hmiddle' : NoTransition
                (firstJunk :: MachineCodeSymbol.header ::
                  MachineCodeSymbol.header :: contextFront) := by
              simpa [middleWord, processed, hprocessed, hrest] using hmiddle
            exact noTransition_tail MachineCodeSymbol.header _
              (noTransition_tail firstJunk _ hmiddle')
      | cons secondJunk gapPrefix =>
          let gap : Word MachineCodeSymbol :=
            List.append gapPrefix
              (MachineCodeSymbol.header :: MachineCodeSymbol.header ::
                contextFront)
          refine ⟨firstJunk, secondJunk, gap, ?_, ?_⟩
          · simp [middleWord, processed, hprocessed, hrest, gap]
          · apply noTransition_tail secondJunk
            apply noTransition_tail firstJunk
            simpa [middleWord, processed, hprocessed, hrest, gap] using hmiddle
  done

def exhaustedBaseLeftRev
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    List.append (processedRows skipped).reverse
      (runtimeKeyCellSymbol (Tape.read current.tape) ::
        MachineCodeSymbol.done ::
        List.append
          (List.replicate current.state MachineCodeSymbol.tick).reverse
          [MachineCodeSymbol.header])

def zeroStackBaseLeftRev
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header :: exhaustedBaseLeftRev current skipped

def leftBoundaryBaseLeftRev
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (left : List (Option Bool)) : Word MachineCodeSymbol :=
  FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev
    (zeroStackBaseLeftRev current skipped) left

def haltBaseLeftRev
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (left right : List (Option Bool)) : Word MachineCodeSymbol :=
  FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev
    (leftBoundaryBaseLeftRev current skipped left) right

theorem exhaustedBaseLeftRev_reverse
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription) :
    (exhaustedBaseLeftRev current skipped).reverse =
      MachineCodeSymbol.header ::
        List.append
          (runtimeKeyBuilderKeyCode current.state
            (Tape.read current.tape))
          (List.append (processedRows skipped)
            [MachineCodeSymbol.header]) := by
  simp [exhaustedBaseLeftRev, runtimeKeyBuilderKeyCode,
    runtimeKey_encodeNat_eq_replicate_tick_done,
    MachineDescription.encodeNatAppend, List.reverse_append,
    List.reverse_replicate, List.append_assoc]
  rw [runtimeKey_encodeCell_eq_singleton]
  rfl
  done

theorem haltBaseLeftRev_reverse
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (left right : List (Option Bool)) :
    (haltBaseLeftRev current skipped left right).reverse =
      List.append
        (exhaustedBaseLeftRev current skipped).reverse
        (MachineCodeSymbol.header :: contextPrefix left right) := by
  rw [haltBaseLeftRev,
    FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev_reverse]
  rw [leftBoundaryBaseLeftRev,
    FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev_reverse]
  simp [zeroStackBaseLeftRev, contextPrefix,
    List.reverse_cons, List.append_assoc]
  change
    List.append
        (MachineDescription.encodeCellListAppend left [])
        (MachineDescription.encodeCellListAppend right []) =
      MachineDescription.encodeCellListAppend left
        (MachineDescription.encodeCellListAppend right [])
  exact
    (encodeCellListAppend_append left []
      (MachineDescription.encodeCellListAppend right [])).symm
  done

def markerBaseLeftRev
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (contextFront : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append contextFront.reverse
    (zeroStackBaseLeftRev current skipped)

theorem haltBaseLeftRev_eq_markerBase
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (left right : List (Option Bool))
    (firstBefore secondBefore : MachineCodeSymbol)
    (contextFront : Word MachineCodeSymbol)
    (hcontext : contextPrefix left right =
      List.append contextFront [firstBefore, secondBefore]) :
    haltBaseLeftRev current skipped left right =
      secondBefore :: firstBefore ::
        markerBaseLeftRev current skipped contextFront := by
  have hreverse :
      (haltBaseLeftRev current skipped left right).reverse =
        (secondBefore :: firstBefore ::
          markerBaseLeftRev current skipped contextFront).reverse := by
    rw [haltBaseLeftRev_reverse]
    rw [hcontext]
    simp [markerBaseLeftRev, zeroStackBaseLeftRev,
      List.reverse_cons, List.reverse_append, List.append_assoc]
  have hback := congrArg List.reverse hreverse
  change (show List MachineCodeSymbol from
      haltBaseLeftRev current skipped left right) =
    secondBefore :: firstBefore ::
      markerBaseLeftRev current skipped contextFront
  simpa only [List.reverse_reverse] using hback
  done

def markedFullWord
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (contextFront : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append
    (markerBaseLeftRev current skipped contextFront).reverse
    (MachineCodeSymbol.transition :: MachineCodeSymbol.transition ::
      MachineDescription.encodeNatAppend haltState suffix)

theorem markerBaseLeftRev_reverse
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (contextFront : Word MachineCodeSymbol) :
    (markerBaseLeftRev current skipped contextFront).reverse =
      List.append
        (exhaustedBaseLeftRev current skipped).reverse
        (MachineCodeSymbol.header :: contextFront) := by
  simp [markerBaseLeftRev, zeroStackBaseLeftRev,
    List.reverse_append, List.reverse_cons, List.append_assoc]
  done

theorem markedFullWord_eq_sourceWord
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (contextFront : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol)
    (firstJunk secondJunk : MachineCodeSymbol)
    (gap : Word MachineCodeSymbol)
    (hmiddle : middleWord skipped contextFront =
      firstJunk :: secondJunk :: gap) :
    markedFullWord current skipped contextFront haltState suffix =
      CurrentBuilder.sourceWord current.state
        (runtimeKeyCellSymbol (Tape.read current.tape))
        firstJunk secondJunk gap haltState suffix := by
  let intermediate : Word MachineCodeSymbol :=
    MachineCodeSymbol.header ::
      List.append
        (runtimeKeyBuilderKeyCode current.state
          (Tape.read current.tape))
        (List.append (middleWord skipped contextFront)
          (MachineCodeSymbol.transition ::
            MachineCodeSymbol.transition ::
            MachineDescription.encodeNatAppend haltState suffix))
  calc
    markedFullWord current skipped contextFront haltState suffix =
        intermediate := by
          rw [markedFullWord, markerBaseLeftRev_reverse,
            exhaustedBaseLeftRev_reverse]
          simp [intermediate, middleWord, List.append_assoc]
    _ = CurrentBuilder.sourceWord current.state
          (runtimeKeyCellSymbol (Tape.read current.tape))
          firstJunk secondJunk gap haltState suffix := by
      dsimp [intermediate]
      rw [hmiddle]
      simp [CurrentBuilder.sourceWord, runtimeKeyBuilderKeyCode,
        runtimeKey_encodeCell_eq_singleton,
        MachineDescription.encodeNatAppend, List.append_assoc]
  done

theorem canonicalExhausted_zero_tape_eq_stackSkip_source
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    (canonicalExhaustedRowsTarget current skipped
      (activeProtectedSuffix (first :: rest) 0 current.tape haltState
        suffix)).tape =
    (FiniteRecognizer.Interpreter.StackSkip.sourceConfig
      (exhaustedBaseLeftRev current skipped)
      first rest 0 (contextTail current.tape haltState suffix)).tape := by
  rfl
  done

theorem stackSkip_zero_target_tape_eq_leftBoundary_source
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    (FiniteRecognizer.Interpreter.StackSkip.targetConfig
      (exhaustedBaseLeftRev current skipped)
      first rest 0 (contextTail current.tape haltState suffix)).tape =
    (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.sourceConfig
      (zeroStackBaseLeftRev current skipped)
      current.tape.left current.tape.right.length
      (MachineDescription.encodeCellsAppend current.tape.right
        (persistent haltState suffix))).tape := by
  rfl
  done

theorem leftBoundary_target_tape_eq_rightBoundary_source
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetConfig
      (zeroStackBaseLeftRev current skipped)
      current.tape.left current.tape.right.length
      (MachineDescription.encodeCellsAppend current.tape.right
        (persistent haltState suffix))).tape =
    (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.sourceConfig
      (leftBoundaryBaseLeftRev current skipped current.tape.left)
      current.tape.right haltState suffix).tape := by
  rfl
  done

theorem rightBoundary_target_tape_eq_marker_source
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol)
    (firstBefore secondBefore : MachineCodeSymbol)
    (contextFront : Word MachineCodeSymbol)
    (hcontext : contextPrefix current.tape.left current.tape.right =
      List.append contextFront [firstBefore, secondBefore]) :
    (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetConfig
      (leftBoundaryBaseLeftRev current skipped current.tape.left)
      current.tape.right haltState suffix).tape =
    (DoubleTransitionMarker.sourceConfig
      (markerBaseLeftRev current skipped contextFront)
      firstBefore secondBefore haltState suffix).tape := by
  change SerializedShift.cursorTape
      (haltBaseLeftRev current skipped current.tape.left current.tape.right)
      (MachineDescription.encodeNatAppend haltState suffix) =
    SerializedShift.cursorTape
      (secondBefore :: firstBefore ::
        markerBaseLeftRev current skipped contextFront)
      (MachineDescription.encodeNatAppend haltState suffix)
  rw [haltBaseLeftRev_eq_markerBase current skipped
    current.tape.left current.tape.right firstBefore secondBefore
    contextFront hcontext]
  done

theorem marker_target_tape_eq_rewind_scan
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (contextFront : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    (DoubleTransitionMarker.targetConfig
      (markerBaseLeftRev current skipped contextFront)
      haltState suffix).tape =
    (Dispatch.NeighborProbe.PrefixRewind.scanConfig
      (MachineCodeSymbol.transition :: MachineCodeSymbol.transition ::
        markerBaseLeftRev current skipped contextFront)
      (MachineDescription.encodeNatAppend haltState suffix)).tape := by
  cases contextFront <;> cases haltState <;> cases suffix <;> rfl
  done

def remainingStackBaseLeftRev
    (current : MachineDescription.Configuration)
    (skipped transitions : List TransitionDescription)
    (copies : Nat) : Word MachineCodeSymbol :=
  List.append (tableStack transitions copies).reverse
    (exhaustedBaseLeftRev current skipped)

def remainingLeftBoundaryBaseLeftRev
    (current : MachineDescription.Configuration)
    (skipped transitions : List TransitionDescription)
    (copies : Nat)
    (left : List (Option Bool)) : Word MachineCodeSymbol :=
  FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev
    (remainingStackBaseLeftRev current skipped transitions copies) left

def remainingHaltBaseLeftRev
    (current : MachineDescription.Configuration)
    (skipped transitions : List TransitionDescription)
    (copies : Nat)
    (left right : List (Option Bool)) : Word MachineCodeSymbol :=
  FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev
    (remainingLeftBoundaryBaseLeftRev current skipped transitions copies left)
    right

def remainingMarkerBaseLeftRev
    (current : MachineDescription.Configuration)
    (skipped transitions : List TransitionDescription)
    (copies : Nat)
    (contextFront : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append contextFront.reverse
    (remainingStackBaseLeftRev current skipped transitions copies)

theorem remainingHaltBaseLeftRev_reverse
    (current : MachineDescription.Configuration)
    (skipped transitions : List TransitionDescription)
    (copies : Nat)
    (left right : List (Option Bool)) :
    (remainingHaltBaseLeftRev current skipped transitions copies
      left right).reverse =
      List.append
        (exhaustedBaseLeftRev current skipped).reverse
        (List.append (tableStack transitions copies)
          (contextPrefix left right)) := by
  rw [remainingHaltBaseLeftRev,
    FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev_reverse]
  rw [remainingLeftBoundaryBaseLeftRev,
    FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetBaseLeftRev_reverse]
  simp [remainingStackBaseLeftRev, contextPrefix,
    List.reverse_append, List.append_assoc]
  change
    List.append
        (MachineDescription.encodeCellListAppend left [])
        (MachineDescription.encodeCellListAppend right []) =
      MachineDescription.encodeCellListAppend left
        (MachineDescription.encodeCellListAppend right [])
  exact
    (encodeCellListAppend_append left []
      (MachineDescription.encodeCellListAppend right [])).symm
  done

theorem remainingHaltBaseLeftRev_eq_markerBase
    (current : MachineDescription.Configuration)
    (skipped transitions : List TransitionDescription)
    (copies : Nat)
    (left right : List (Option Bool))
    (firstBefore secondBefore : MachineCodeSymbol)
    (contextFront : Word MachineCodeSymbol)
    (hcontext : contextPrefix left right =
      List.append contextFront [firstBefore, secondBefore]) :
    remainingHaltBaseLeftRev current skipped transitions copies left right =
      secondBefore :: firstBefore ::
        remainingMarkerBaseLeftRev current skipped transitions copies
          contextFront := by
  have hreverse :
      (remainingHaltBaseLeftRev current skipped transitions copies
        left right).reverse =
        (secondBefore :: firstBefore ::
          remainingMarkerBaseLeftRev current skipped transitions copies
            contextFront).reverse := by
    rw [remainingHaltBaseLeftRev_reverse]
    rw [hcontext]
    simp [remainingMarkerBaseLeftRev, remainingStackBaseLeftRev,
      List.reverse_cons, List.reverse_append, List.append_assoc]
  have hback := congrArg List.reverse hreverse
  change (show List MachineCodeSymbol from
      remainingHaltBaseLeftRev current skipped transitions copies
        left right) =
    secondBefore :: firstBefore ::
      remainingMarkerBaseLeftRev current skipped transitions copies
        contextFront
  simpa only [List.reverse_reverse] using hback
  done

def remainingMarkedFullWord
    (current : MachineDescription.Configuration)
    (skipped transitions : List TransitionDescription)
    (copies : Nat)
    (contextFront : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append
    (remainingMarkerBaseLeftRev current skipped transitions copies
      contextFront).reverse
    (MachineCodeSymbol.transition :: MachineCodeSymbol.transition ::
      MachineDescription.encodeNatAppend haltState suffix)

theorem remainingMarkerBaseLeftRev_reverse
    (current : MachineDescription.Configuration)
    (skipped transitions : List TransitionDescription)
    (copies : Nat)
    (contextFront : Word MachineCodeSymbol) :
    (remainingMarkerBaseLeftRev current skipped transitions copies
      contextFront).reverse =
      List.append
        (exhaustedBaseLeftRev current skipped).reverse
        (List.append (tableStack transitions copies) contextFront) := by
  simp [remainingMarkerBaseLeftRev, remainingStackBaseLeftRev,
    List.reverse_append, List.append_assoc]
  done

theorem remainingMarkedFullWord_eq_sourceWord
    (current : MachineDescription.Configuration)
    (skipped transitions : List TransitionDescription)
    (copies : Nat)
    (contextFront : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol)
    (firstJunk secondJunk : MachineCodeSymbol)
    (gap : Word MachineCodeSymbol)
    (hmiddle : middleWordCopies skipped transitions copies contextFront =
      firstJunk :: secondJunk :: gap) :
    remainingMarkedFullWord current skipped transitions copies
        contextFront haltState suffix =
      CurrentBuilder.sourceWord current.state
        (runtimeKeyCellSymbol (Tape.read current.tape))
        firstJunk secondJunk gap haltState suffix := by
  let intermediate : Word MachineCodeSymbol :=
    MachineCodeSymbol.header ::
      List.append
        (runtimeKeyBuilderKeyCode current.state
          (Tape.read current.tape))
        (List.append
          (middleWordCopies skipped transitions copies contextFront)
          (MachineCodeSymbol.transition ::
            MachineCodeSymbol.transition ::
            MachineDescription.encodeNatAppend haltState suffix))
  calc
    remainingMarkedFullWord current skipped transitions copies
        contextFront haltState suffix = intermediate := by
      rw [remainingMarkedFullWord, remainingMarkerBaseLeftRev_reverse,
        exhaustedBaseLeftRev_reverse]
      simp [intermediate, middleWordCopies, List.append_assoc]
    _ = CurrentBuilder.sourceWord current.state
          (runtimeKeyCellSymbol (Tape.read current.tape))
          firstJunk secondJunk gap haltState suffix := by
      dsimp [intermediate]
      rw [hmiddle]
      simp [CurrentBuilder.sourceWord, runtimeKeyBuilderKeyCode,
        runtimeKey_encodeCell_eq_singleton,
        MachineDescription.encodeNatAppend, List.append_assoc]
  done

theorem canonicalExhausted_tape_eq_stackSkip_source
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    (canonicalExhaustedRowsTarget current skipped
      (activeProtectedSuffix (first :: rest) copies current.tape haltState
        suffix)).tape =
    (FiniteRecognizer.Interpreter.StackSkip.sourceConfig
      (exhaustedBaseLeftRev current skipped)
      first rest copies (contextTail current.tape haltState suffix)).tape := by
  rfl
  done

theorem remainingStack_target_tape_eq_leftBoundary_source
    (current : MachineDescription.Configuration)
    (skipped : List TransitionDescription)
    (first : TransitionDescription)
    (rest : List TransitionDescription)
    (copies : Nat)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    (FiniteRecognizer.Interpreter.StackSkip.targetConfig
      (exhaustedBaseLeftRev current skipped)
      first rest copies (contextTail current.tape haltState suffix)).tape =
    (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.sourceConfig
      (remainingStackBaseLeftRev current skipped (first :: rest) copies)
      current.tape.left current.tape.right.length
      (MachineDescription.encodeCellsAppend current.tape.right
        (persistent haltState suffix))).tape := by
  rfl
  done

theorem remainingLeftBoundary_target_tape_eq_rightBoundary_source
    (current : MachineDescription.Configuration)
    (skipped transitions : List TransitionDescription)
    (copies : Nat)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetConfig
      (remainingStackBaseLeftRev current skipped transitions copies)
      current.tape.left current.tape.right.length
      (MachineDescription.encodeCellsAppend current.tape.right
        (persistent haltState suffix))).tape =
    (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.sourceConfig
      (remainingLeftBoundaryBaseLeftRev current skipped transitions copies
        current.tape.left)
      current.tape.right haltState suffix).tape := by
  rfl
  done

theorem remainingRightBoundary_target_tape_eq_marker_source
    (current : MachineDescription.Configuration)
    (skipped transitions : List TransitionDescription)
    (copies : Nat)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol)
    (firstBefore secondBefore : MachineCodeSymbol)
    (contextFront : Word MachineCodeSymbol)
    (hcontext : contextPrefix current.tape.left current.tape.right =
      List.append contextFront [firstBefore, secondBefore]) :
    (FiniteRecognizer.Interpreter.DirectContextUpdate.Boundary.targetConfig
      (remainingLeftBoundaryBaseLeftRev current skipped transitions copies
        current.tape.left)
      current.tape.right haltState suffix).tape =
    (DoubleTransitionMarker.sourceConfig
      (remainingMarkerBaseLeftRev current skipped transitions copies
        contextFront)
      firstBefore secondBefore haltState suffix).tape := by
  change SerializedShift.cursorTape
      (remainingHaltBaseLeftRev current skipped transitions copies
        current.tape.left current.tape.right)
      (MachineDescription.encodeNatAppend haltState suffix) =
    SerializedShift.cursorTape
      (secondBefore :: firstBefore ::
        remainingMarkerBaseLeftRev current skipped transitions copies
          contextFront)
      (MachineDescription.encodeNatAppend haltState suffix)
  rw [remainingHaltBaseLeftRev_eq_markerBase current skipped transitions
    copies current.tape.left current.tape.right firstBefore secondBefore
    contextFront hcontext]
  done

theorem remainingMarker_target_tape_eq_rewind_scan
    (current : MachineDescription.Configuration)
    (skipped transitions : List TransitionDescription)
    (copies : Nat)
    (contextFront : Word MachineCodeSymbol)
    (haltState : Nat)
    (suffix : Word MachineCodeSymbol) :
    (DoubleTransitionMarker.targetConfig
      (remainingMarkerBaseLeftRev current skipped transitions copies
        contextFront)
      haltState suffix).tape =
    (Dispatch.NeighborProbe.PrefixRewind.scanConfig
      (MachineCodeSymbol.transition :: MachineCodeSymbol.transition ::
        remainingMarkerBaseLeftRev current skipped transitions copies
          contextFront)
      (MachineDescription.encodeNatAppend haltState suffix)).tape := by
  cases contextFront <;> cases haltState <;> cases suffix <;> rfl
  done

end LastMiss

end FiniteRecognizer.Interpreter.NoMatchFinalGate

end Computability
end FoC
