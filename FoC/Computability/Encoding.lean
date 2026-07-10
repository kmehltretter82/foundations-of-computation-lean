import FoC.Computability.MachineDescription

set_option doc.verso true

/-!
# Machine-description encoding

This module defines the finite token alphabet, serializers, and parsers for
Boolean-tape machine descriptions.  Executable transition-table semantics live
in {module}`FoC.Computability.MachineDescription`; languages obtained by
decoding and running description codes live in
{module -checked}`FoC.Computability.DescriptionLanguages`.

The descriptions here are intentionally first-order data: they are finite
lists of transition records, not arbitrary Lean functions.  This keeps later
compiler and universal-machine theorems tied to concrete syntax without
conflating parser correctness with construction of a finite universal runner.

## Book coordinates

Used by:
- Chapter 5, Sections 5.2 and 5.3: concrete machine encodings and universal
  interpretation infrastructure.
-/

namespace FoC
namespace Computability

open Foundation
open Languages

/-!
# Finite description alphabet

Natural numbers are encoded in unary by a sequence of {lit}`tick` tokens
terminated by {lit}`done`.  The remaining tokens identify headers,
transition records, cells, and movement directions.
-/

inductive MachineCodeSymbol where
  | header : MachineCodeSymbol
  | transition : MachineCodeSymbol
  | tick : MachineCodeSymbol
  | done : MachineCodeSymbol
  | blank : MachineCodeSymbol
  | zero : MachineCodeSymbol
  | one : MachineCodeSymbol
  | moveLeft : MachineCodeSymbol
  | moveRight : MachineCodeSymbol
deriving DecidableEq

namespace MachineCodeSymbol

def finite : FiniteType MachineCodeSymbol where
  elems :=
    [ header, transition, tick, done, blank, zero, one, moveLeft, moveRight ]
  complete := by
    intro symbol
    cases symbol <;> simp

end MachineCodeSymbol

namespace MachineDescription

/-!
# Encoding and decoding
-/

def encodeNat : Nat -> Word MachineCodeSymbol
  | 0 => [MachineCodeSymbol.done]
  | n + 1 => MachineCodeSymbol.tick :: encodeNat n

def decodeNat : Word MachineCodeSymbol ->
    Option (Nat × Word MachineCodeSymbol)
  | MachineCodeSymbol.done :: rest => some (0, rest)
  | MachineCodeSymbol.tick :: rest =>
      match decodeNat rest with
      | none => none
      | some (n, rest') => some (n + 1, rest')
  | _ => none

theorem decodeNat_encodeNat_append
    (n : Nat) (suffix : Word MachineCodeSymbol) :
    decodeNat (List.append (encodeNat n) suffix) = some (n, suffix) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        (match decodeNat (List.append (encodeNat n) suffix) with
        | none => none
        | some (n, rest') => some (n + 1, rest')) =
          some (n + 1, suffix)
      rw [ih]

def encodeCell : Option Bool -> Word MachineCodeSymbol
  | none => [MachineCodeSymbol.blank]
  | some false => [MachineCodeSymbol.zero]
  | some true => [MachineCodeSymbol.one]

def decodeCell : Word MachineCodeSymbol ->
    Option (Option Bool × Word MachineCodeSymbol)
  | MachineCodeSymbol.blank :: rest => some (none, rest)
  | MachineCodeSymbol.zero :: rest => some (some false, rest)
  | MachineCodeSymbol.one :: rest => some (some true, rest)
  | _ => none

theorem decodeCell_encodeCell_append
    (cell : Option Bool) (suffix : Word MachineCodeSymbol) :
    decodeCell (List.append (encodeCell cell) suffix) =
      some (cell, suffix) := by
  cases cell with
  | none => rfl
  | some b =>
      cases b <;> rfl

def encodeDirection : Direction -> Word MachineCodeSymbol
  | Direction.left => [MachineCodeSymbol.moveLeft]
  | Direction.right => [MachineCodeSymbol.moveRight]

def decodeDirection : Word MachineCodeSymbol ->
    Option (Direction × Word MachineCodeSymbol)
  | MachineCodeSymbol.moveLeft :: rest => some (Direction.left, rest)
  | MachineCodeSymbol.moveRight :: rest => some (Direction.right, rest)
  | _ => none

theorem decodeDirection_encodeDirection_append
    (dir : Direction) (suffix : Word MachineCodeSymbol) :
    decodeDirection (List.append (encodeDirection dir) suffix) =
      some (dir, suffix) := by
  cases dir <;> rfl

def encodeNatAppend (n : Nat) (suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  List.append (encodeNat n) suffix

def encodeCellAppend (cell : Option Bool)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (encodeCell cell) suffix

def encodeDirectionAppend (dir : Direction)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (encodeDirection dir) suffix

theorem decodeNat_encodeNatAppend
    (n : Nat) (suffix : Word MachineCodeSymbol) :
    decodeNat (encodeNatAppend n suffix) = some (n, suffix) :=
  decodeNat_encodeNat_append n suffix

theorem decodeNat_eq_some_encodeNatAppend
    {tokens : Word MachineCodeSymbol} {n : Nat}
    {suffix : Word MachineCodeSymbol}
    (h : decodeNat tokens = some (n, suffix)) :
    tokens = encodeNatAppend n suffix := by
  induction tokens generalizing n suffix with
  | nil =>
      cases h
  | cons symbol rest ih =>
      cases symbol with
      | header => cases h
      | transition => cases h
      | tick =>
          simp [decodeNat] at h
          cases hrest : decodeNat rest with
          | none =>
              simp [hrest] at h
          | some parsed =>
              cases parsed with
              | mk parsedN parsedSuffix =>
                  simp [hrest] at h
                  have hcanonical :
                      rest = encodeNatAppend parsedN parsedSuffix :=
                    ih hrest
                  cases h
                  subst n
                  subst suffix
                  simp [encodeNatAppend, encodeNat, hcanonical]
      | done =>
          simp [decodeNat] at h
          cases h
          subst n
          subst suffix
          rfl
      | blank => cases h
      | zero => cases h
      | one => cases h
      | moveLeft => cases h
      | moveRight => cases h

theorem decodeCell_encodeCellAppend
    (cell : Option Bool) (suffix : Word MachineCodeSymbol) :
    decodeCell (encodeCellAppend cell suffix) = some (cell, suffix) :=
  decodeCell_encodeCell_append cell suffix

theorem decodeCell_eq_some_encodeCellAppend
    {tokens : Word MachineCodeSymbol} {cell : Option Bool}
    {suffix : Word MachineCodeSymbol}
    (h : decodeCell tokens = some (cell, suffix)) :
    tokens = encodeCellAppend cell suffix := by
  cases tokens with
  | nil =>
      cases h
  | cons symbol rest =>
      cases symbol <;> simp [decodeCell] at h
      · cases h
        subst cell
        subst suffix
        rfl
      · cases h
        subst cell
        subst suffix
        rfl
      · cases h
        subst cell
        subst suffix
        rfl

theorem decodeDirection_encodeDirectionAppend
    (dir : Direction) (suffix : Word MachineCodeSymbol) :
    decodeDirection (encodeDirectionAppend dir suffix) =
      some (dir, suffix) :=
  decodeDirection_encodeDirection_append dir suffix

theorem decodeDirection_eq_some_encodeDirectionAppend
    {tokens : Word MachineCodeSymbol} {dir : Direction}
    {suffix : Word MachineCodeSymbol}
    (h : decodeDirection tokens = some (dir, suffix)) :
    tokens = encodeDirectionAppend dir suffix := by
  cases tokens with
  | nil =>
      cases h
  | cons symbol rest =>
      cases symbol <;> simp [decodeDirection] at h
      · cases h
        subst dir
        subst suffix
        rfl
      · cases h
        subst dir
        subst suffix
        rfl

def encodeTransitionAppend (t : TransitionDescription)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.transition ::
    encodeNatAppend t.source
      (encodeCellAppend t.read
        (encodeCellAppend t.write
          (encodeDirectionAppend t.move
            (encodeNatAppend t.target suffix))))

def encodeTransition (t : TransitionDescription) :
    Word MachineCodeSymbol :=
  encodeTransitionAppend t []

def decodeTransition (tokens : Word MachineCodeSymbol) :
    Option (TransitionDescription × Word MachineCodeSymbol) :=
  match tokens with
  | MachineCodeSymbol.transition :: rest =>
      match decodeNat rest with
      | none => none
      | some (source, rest) =>
          match decodeCell rest with
          | none => none
          | some (read, rest) =>
              match decodeCell rest with
              | none => none
              | some (write, rest) =>
                  match decodeDirection rest with
                  | none => none
                  | some (move, rest) =>
                      match decodeNat rest with
                      | none => none
                      | some (target, rest) =>
                          some
                            ({ source := source
                               read := read
                               write := write
                               move := move
                               target := target }, rest)
  | _ => none

theorem decodeTransition_encodeTransition_append
    (t : TransitionDescription) (suffix : Word MachineCodeSymbol) :
    decodeTransition (encodeTransitionAppend t suffix) =
      some (t, suffix) := by
  cases t
  simp [encodeTransitionAppend, decodeTransition,
    decodeNat_encodeNatAppend,
    decodeCell_encodeCellAppend,
    decodeDirection_encodeDirectionAppend]

theorem decodeTransition_encodeTransition :
    decodeTransition (encodeTransition t) = some (t, []) := by
  exact decodeTransition_encodeTransition_append t []

theorem decodeTransition_eq_some_encodeTransitionAppend
    {tokens : Word MachineCodeSymbol} {t : TransitionDescription}
    {suffix : Word MachineCodeSymbol}
    (h : decodeTransition tokens = some (t, suffix)) :
    tokens = encodeTransitionAppend t suffix := by
  cases tokens with
  | nil =>
      cases h
  | cons symbol rest =>
      cases symbol with
      | header => cases h
      | transition =>
          simp [decodeTransition] at h
          cases hsource : decodeNat rest with
          | none =>
              simp [hsource] at h
          | some parsedSource =>
              cases parsedSource with
              | mk source restAfterSource =>
                  simp [hsource] at h
                  cases hread : decodeCell restAfterSource with
                  | none =>
                      simp [hread] at h
                  | some parsedRead =>
                      cases parsedRead with
                      | mk read restAfterRead =>
                          simp [hread] at h
                          cases hwrite : decodeCell restAfterRead with
                          | none =>
                              simp [hwrite] at h
                          | some parsedWrite =>
                              cases parsedWrite with
                              | mk write restAfterWrite =>
                                  simp [hwrite] at h
                                  cases hmove :
                                      decodeDirection restAfterWrite with
                                  | none =>
                                      simp [hmove] at h
                                  | some parsedMove =>
                                      cases parsedMove with
                                      | mk move restAfterMove =>
                                          simp [hmove] at h
                                          cases htarget :
                                              decodeNat restAfterMove with
                                          | none =>
                                              simp [htarget] at h
                                          | some parsedTarget =>
                                              cases parsedTarget with
                                              | mk target parsedSuffix =>
                                                  simp [htarget] at h
                                                  cases h
                                                  subst t
                                                  subst suffix
                                                  have hsourceTokens :
                                                      rest =
                                                        encodeNatAppend source
                                                          restAfterSource :=
                                                    decodeNat_eq_some_encodeNatAppend
                                                      hsource
                                                  have hreadTokens :
                                                      restAfterSource =
                                                        encodeCellAppend read
                                                          restAfterRead :=
                                                    decodeCell_eq_some_encodeCellAppend
                                                      hread
                                                  have hwriteTokens :
                                                      restAfterRead =
                                                        encodeCellAppend write
                                                          restAfterWrite :=
                                                    decodeCell_eq_some_encodeCellAppend
                                                      hwrite
                                                  have hmoveTokens :
                                                      restAfterWrite =
                                                        encodeDirectionAppend
                                                          move restAfterMove :=
                                                    decodeDirection_eq_some_encodeDirectionAppend
                                                      hmove
                                                  have htargetTokens :
                                                      restAfterMove =
                                                        encodeNatAppend target
                                                          parsedSuffix :=
                                                    decodeNat_eq_some_encodeNatAppend
                                                      htarget
                                                  simp [encodeTransitionAppend,
                                                    hsourceTokens,
                                                    hreadTokens,
                                                    hwriteTokens,
                                                    hmoveTokens,
                                                    htargetTokens]
      | tick => cases h
      | done => cases h
      | blank => cases h
      | zero => cases h
      | one => cases h
      | moveLeft => cases h
      | moveRight => cases h

def encodeTransitionsAppend : List TransitionDescription ->
    Word MachineCodeSymbol -> Word MachineCodeSymbol
  | [], suffix => suffix
  | t :: rest, suffix =>
      encodeTransitionAppend t (encodeTransitionsAppend rest suffix)

def encodeTransitions (transitions : List TransitionDescription) :
    Word MachineCodeSymbol :=
  encodeTransitionsAppend transitions []

theorem encodeTransitionsAppend_append
    (transitions : List TransitionDescription)
    (suffix tail : Word MachineCodeSymbol) :
    List.append (encodeTransitionsAppend transitions suffix) tail =
      encodeTransitionsAppend transitions (List.append suffix tail) := by
  induction transitions with
  | nil =>
      rfl
  | cons t rest ih =>
      simpa [encodeTransitionsAppend, encodeTransitionAppend,
        encodeNatAppend, encodeCellAppend, encodeDirectionAppend,
        List.append_assoc] using ih

def decodeTransitions : Nat -> Word MachineCodeSymbol ->
    Option (List TransitionDescription × Word MachineCodeSymbol)
  | 0, tokens => some ([], tokens)
  | n + 1, tokens =>
      match decodeTransition tokens with
      | none => none
      | some (t, rest) =>
          match decodeTransitions n rest with
          | none => none
          | some (ts, rest') => some (t :: ts, rest')

theorem decodeTransitions_encodeTransitions_append
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    decodeTransitions transitions.length
      (encodeTransitionsAppend transitions suffix) =
        some (transitions, suffix) := by
  induction transitions with
  | nil =>
      rfl
  | cons t rest ih =>
      simp [encodeTransitionsAppend, decodeTransitions,
        decodeTransition_encodeTransition_append, ih]

theorem decodeTransitions_encodeTransitions
    (transitions : List TransitionDescription) :
    decodeTransitions transitions.length (encodeTransitions transitions) =
      some (transitions, []) :=
  decodeTransitions_encodeTransitions_append transitions []

theorem decodeTransitions_eq_some_encodeTransitionsAppend
    {count : Nat} {tokens : Word MachineCodeSymbol}
    {transitions : List TransitionDescription}
    {suffix : Word MachineCodeSymbol}
    (h : decodeTransitions count tokens = some (transitions, suffix)) :
    count = transitions.length ∧
      tokens = encodeTransitionsAppend transitions suffix := by
  induction count generalizing tokens transitions suffix with
  | zero =>
      simp [decodeTransitions] at h
      cases h
      subst transitions
      subst tokens
      constructor <;> rfl
  | succ count ih =>
      simp [decodeTransitions] at h
      cases htransition : decodeTransition tokens with
      | none =>
          simp [htransition] at h
      | some parsedTransition =>
          cases parsedTransition with
          | mk transition rest =>
              simp [htransition] at h
              cases htail : decodeTransitions count rest with
              | none =>
                  simp [htail] at h
              | some parsedTail =>
                  cases parsedTail with
                  | mk tail parsedSuffix =>
                      simp [htail] at h
                      cases h
                      subst transitions
                      subst suffix
                      have htokens :
                          tokens =
                            encodeTransitionAppend transition rest :=
                        decodeTransition_eq_some_encodeTransitionAppend
                          htransition
                      have hrest :
                          count = tail.length ∧
                            rest =
                              encodeTransitionsAppend tail parsedSuffix :=
                        ih htail
                      constructor
                      · simp [hrest.left]
                      · simp [encodeTransitionsAppend, htokens,
                          hrest.right]

def encodeDescriptionAppend (D : MachineDescription)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    encodeNatAppend D.stateCount
      (encodeNatAppend D.start
        (encodeNatAppend D.halt
          (encodeNatAppend D.transitions.length
            (encodeTransitionsAppend D.transitions suffix))))

def encodeDescription (D : MachineDescription) :
    Word MachineCodeSymbol :=
  encodeDescriptionAppend D []

theorem encodeDescriptionAppend_eq_encodeDescription_append
    (D : MachineDescription) (suffix : Word MachineCodeSymbol) :
    encodeDescriptionAppend D suffix =
      List.append (encodeDescription D) suffix := by
  cases D with
  | mk stateCount start halt transitions =>
      simp [encodeDescription, encodeDescriptionAppend, encodeNatAppend,
        List.append_assoc]
      have htrans :
          List.append (encodeTransitionsAppend transitions []) suffix =
            encodeTransitionsAppend transitions suffix := by
        simpa using encodeTransitionsAppend_append transitions [] suffix
      rw [← htrans]
      rfl

def decodeDescription (tokens : Word MachineCodeSymbol) :
    Option MachineDescription :=
  match tokens with
  | MachineCodeSymbol.header :: rest =>
      match decodeNat rest with
      | none => none
      | some (stateCount, rest) =>
          match decodeNat rest with
          | none => none
          | some (start, rest) =>
              match decodeNat rest with
              | none => none
              | some (halt, rest) =>
                  match decodeNat rest with
                  | none => none
                  | some (transitionCount, rest) =>
                      match decodeTransitions transitionCount rest with
                      | none => none
                      | some (transitions, []) =>
                          some
                            { stateCount := stateCount
                              start := start
                              halt := halt
                              transitions := transitions }
                      | some (_, _ :: _) => none
  | _ => none

def decodeDescriptionPrefix (tokens : Word MachineCodeSymbol) :
    Option (MachineDescription × Word MachineCodeSymbol) :=
  match tokens with
  | MachineCodeSymbol.header :: rest =>
      match decodeNat rest with
      | none => none
      | some (stateCount, rest) =>
          match decodeNat rest with
          | none => none
          | some (start, rest) =>
              match decodeNat rest with
              | none => none
              | some (halt, rest) =>
                  match decodeNat rest with
                  | none => none
                  | some (transitionCount, rest) =>
                      match decodeTransitions transitionCount rest with
                      | none => none
                      | some (transitions, suffix) =>
                          some
                            ({ stateCount := stateCount
                               start := start
                               halt := halt
                               transitions := transitions }, suffix)
  | _ => none

theorem decodeDescription_encodeDescription
    (D : MachineDescription) :
    decodeDescription (encodeDescription D) = some D := by
  cases D
  simp [encodeDescription, encodeDescriptionAppend, decodeDescription,
    decodeNat_encodeNatAppend,
    decodeTransitions_encodeTransitions_append]

theorem decodeDescriptionPrefix_encodeDescriptionAppend
    (D : MachineDescription) (suffix : Word MachineCodeSymbol) :
    decodeDescriptionPrefix (encodeDescriptionAppend D suffix) =
      some (D, suffix) := by
  cases D
  simp [encodeDescriptionAppend, decodeDescriptionPrefix,
    decodeNat_encodeNatAppend,
    decodeTransitions_encodeTransitions_append]

theorem decodeDescriptionPrefix_eq_some_encodeDescriptionAppend
    {tokens : Word MachineCodeSymbol} {D : MachineDescription}
    {suffix : Word MachineCodeSymbol}
    (h : decodeDescriptionPrefix tokens = some (D, suffix)) :
    tokens = encodeDescriptionAppend D suffix := by
  cases tokens with
  | nil =>
      cases h
  | cons symbol rest =>
      cases symbol with
      | header =>
          simp [decodeDescriptionPrefix] at h
          cases hstateCount : decodeNat rest with
          | none =>
              simp [hstateCount] at h
          | some parsedStateCount =>
              cases parsedStateCount with
              | mk stateCount restAfterStateCount =>
                  simp [hstateCount] at h
                  cases hstart : decodeNat restAfterStateCount with
                  | none =>
                      simp [hstart] at h
                  | some parsedStart =>
                      cases parsedStart with
                      | mk start restAfterStart =>
                          simp [hstart] at h
                          cases hhalt : decodeNat restAfterStart with
                          | none =>
                              simp [hhalt] at h
                          | some parsedHalt =>
                              cases parsedHalt with
                              | mk halt restAfterHalt =>
                                  simp [hhalt] at h
                                  cases hcount :
                                      decodeNat restAfterHalt with
                                  | none =>
                                      simp [hcount] at h
                                  | some parsedCount =>
                                      cases parsedCount with
                                      | mk transitionCount
                                          restAfterCount =>
                                          simp [hcount] at h
                                          cases htransitions :
                                              decodeTransitions
                                                transitionCount
                                                restAfterCount with
                                          | none =>
                                              simp [htransitions] at h
                                          | some parsedTransitions =>
                                              cases parsedTransitions with
                                              | mk transitions
                                                  parsedSuffix =>
                                                  simp [htransitions] at h
                                                  cases h
                                                  subst D
                                                  subst suffix
                                                  have hstateCountTokens :
                                                      rest =
                                                        encodeNatAppend
                                                          stateCount
                                                          restAfterStateCount :=
                                                    decodeNat_eq_some_encodeNatAppend
                                                      hstateCount
                                                  have hstartTokens :
                                                      restAfterStateCount =
                                                        encodeNatAppend start
                                                          restAfterStart :=
                                                    decodeNat_eq_some_encodeNatAppend
                                                      hstart
                                                  have hhaltTokens :
                                                      restAfterStart =
                                                        encodeNatAppend halt
                                                          restAfterHalt :=
                                                    decodeNat_eq_some_encodeNatAppend
                                                      hhalt
                                                  have hcountTokens :
                                                      restAfterHalt =
                                                        encodeNatAppend
                                                          transitionCount
                                                          restAfterCount :=
                                                    decodeNat_eq_some_encodeNatAppend
                                                      hcount
                                                  have htransitionTokens :
                                                      transitionCount =
                                                          transitions.length ∧
                                                        restAfterCount =
                                                          encodeTransitionsAppend
                                                            transitions
                                                            parsedSuffix :=
                                                    decodeTransitions_eq_some_encodeTransitionsAppend
                                                      htransitions
                                                  simp [encodeDescriptionAppend,
                                                    hstateCountTokens,
                                                    hstartTokens,
                                                    hhaltTokens,
                                                    hcountTokens,
                                                    htransitionTokens.left,
                                                    htransitionTokens.right]
      | transition => cases h
      | tick => cases h
      | done => cases h
      | blank => cases h
      | zero => cases h
      | one => cases h
      | moveLeft => cases h
      | moveRight => cases h

theorem decodeDescriptionPrefix_eq_some_encodeDescription_append
    {tokens : Word MachineCodeSymbol} {D : MachineDescription}
    {suffix : Word MachineCodeSymbol}
    (h : decodeDescriptionPrefix tokens = some (D, suffix)) :
    tokens = List.append (encodeDescription D) suffix := by
  rw [decodeDescriptionPrefix_eq_some_encodeDescriptionAppend h,
    encodeDescriptionAppend_eq_encodeDescription_append]

theorem decodeDescriptionPrefix_encodeDescription_append
    (D : MachineDescription) (suffix : Word MachineCodeSymbol) :
    decodeDescriptionPrefix (List.append (encodeDescription D) suffix) =
      some (D, suffix) := by
  have hword :
      List.append (encodeDescription D) suffix =
        encodeDescriptionAppend D suffix := by
    cases D
    rename_i stateCount start halt transitions
    simpa [encodeDescription, encodeDescriptionAppend, encodeNatAppend,
      List.append_assoc]
      using (encodeTransitionsAppend_append transitions [] suffix)
  rw [hword]
  exact decodeDescriptionPrefix_encodeDescriptionAppend D suffix

/-!
# Description-backed code-word decoder

The universal-machine layer treats both machine descriptions and machine inputs
as words over one code alphabet.  Concrete descriptions still run on Boolean
tapes, so the input code word is first expanded into a Boolean input word.
-/

def encodeCodeSymbolAsInput : MachineCodeSymbol -> Word Bool
  | MachineCodeSymbol.header => [false, false, false, false]
  | MachineCodeSymbol.transition => [false, false, false, true]
  | MachineCodeSymbol.tick => [false, false, true, false]
  | MachineCodeSymbol.done => [false, false, true, true]
  | MachineCodeSymbol.blank => [false, true, false, false]
  | MachineCodeSymbol.zero => [false, true, false, true]
  | MachineCodeSymbol.one => [false, true, true, false]
  | MachineCodeSymbol.moveLeft => [false, true, true, true]
  | MachineCodeSymbol.moveRight => [true, false, false, false]

def encodeCodeWordAsInput : Word MachineCodeSymbol -> Word Bool
  | [] => []
  | symbol :: rest =>
      List.append (encodeCodeSymbolAsInput symbol)
        (encodeCodeWordAsInput rest)

theorem encodeCodeWordAsInput_append
    (pre suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput (List.append pre suffix) =
      List.append (encodeCodeWordAsInput pre)
        (encodeCodeWordAsInput suffix) := by
  induction pre with
  | nil =>
      rfl
  | cons symbol rest ih =>
      simp [encodeCodeWordAsInput]
      exact congrArg
        (fun tail : Word Bool =>
          List.append (encodeCodeSymbolAsInput symbol) tail) ih

theorem encodeCodeWordAsInput_singleton
    (symbol : MachineCodeSymbol) :
    encodeCodeWordAsInput [symbol] =
      encodeCodeSymbolAsInput symbol := by
  cases symbol <;> rfl

def decodeCodeWordAsInput : Word Bool -> Option (Word MachineCodeSymbol)
  | [] => some []
  | false :: false :: false :: false :: rest =>
      Option.map (fun decoded => MachineCodeSymbol.header :: decoded)
        (decodeCodeWordAsInput rest)
  | false :: false :: false :: true :: rest =>
      Option.map (fun decoded => MachineCodeSymbol.transition :: decoded)
        (decodeCodeWordAsInput rest)
  | false :: false :: true :: false :: rest =>
      Option.map (fun decoded => MachineCodeSymbol.tick :: decoded)
        (decodeCodeWordAsInput rest)
  | false :: false :: true :: true :: rest =>
      Option.map (fun decoded => MachineCodeSymbol.done :: decoded)
        (decodeCodeWordAsInput rest)
  | false :: true :: false :: false :: rest =>
      Option.map (fun decoded => MachineCodeSymbol.blank :: decoded)
        (decodeCodeWordAsInput rest)
  | false :: true :: false :: true :: rest =>
      Option.map (fun decoded => MachineCodeSymbol.zero :: decoded)
        (decodeCodeWordAsInput rest)
  | false :: true :: true :: false :: rest =>
      Option.map (fun decoded => MachineCodeSymbol.one :: decoded)
        (decodeCodeWordAsInput rest)
  | false :: true :: true :: true :: rest =>
      Option.map (fun decoded => MachineCodeSymbol.moveLeft :: decoded)
        (decodeCodeWordAsInput rest)
  | true :: false :: false :: false :: rest =>
      Option.map (fun decoded => MachineCodeSymbol.moveRight :: decoded)
        (decodeCodeWordAsInput rest)
  | _ => none

theorem decodeCodeWordAsInput_encodeCodeWordAsInput
    (w : Word MachineCodeSymbol) :
    decodeCodeWordAsInput (encodeCodeWordAsInput w) = some w := by
  induction w with
  | nil =>
      rfl
  | cons symbol rest ih =>
      cases symbol <;>
        simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput,
          decodeCodeWordAsInput, Option.map, ih]

theorem decodeCodeWordAsInput_eq_some_encodeCodeWordAsInput :
    forall {bits : Word Bool} {code : Word MachineCodeSymbol},
      decodeCodeWordAsInput bits = some code ->
        bits = encodeCodeWordAsInput code
  | [], code, h => by
      simp [decodeCodeWordAsInput] at h
      cases h
      rfl
  | false :: false :: false :: false :: rest, code, h => by
      cases htail : decodeCodeWordAsInput rest with
      | none =>
          simp [decodeCodeWordAsInput, htail] at h
      | some tail =>
          cases code with
          | nil =>
              simp [decodeCodeWordAsInput, htail] at h
          | cons sym syms =>
              simp [decodeCodeWordAsInput, htail] at h
              rcases h with ⟨decoded, hopt, hcode⟩
              cases hopt
              cases hcode
              have hrest :=
                decodeCodeWordAsInput_eq_some_encodeCodeWordAsInput htail
              simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput, hrest]
  | false :: false :: false :: true :: rest, code, h => by
      cases htail : decodeCodeWordAsInput rest with
      | none =>
          simp [decodeCodeWordAsInput, htail] at h
      | some tail =>
          cases code with
          | nil =>
              simp [decodeCodeWordAsInput, htail] at h
          | cons sym syms =>
              simp [decodeCodeWordAsInput, htail] at h
              rcases h with ⟨decoded, hopt, hcode⟩
              cases hopt
              cases hcode
              have hrest :=
                decodeCodeWordAsInput_eq_some_encodeCodeWordAsInput htail
              simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput, hrest]
  | false :: false :: true :: false :: rest, code, h => by
      cases htail : decodeCodeWordAsInput rest with
      | none =>
          simp [decodeCodeWordAsInput, htail] at h
      | some tail =>
          cases code with
          | nil =>
              simp [decodeCodeWordAsInput, htail] at h
          | cons sym syms =>
              simp [decodeCodeWordAsInput, htail] at h
              rcases h with ⟨decoded, hopt, hcode⟩
              cases hopt
              cases hcode
              have hrest :=
                decodeCodeWordAsInput_eq_some_encodeCodeWordAsInput htail
              simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput, hrest]
  | false :: false :: true :: true :: rest, code, h => by
      cases htail : decodeCodeWordAsInput rest with
      | none =>
          simp [decodeCodeWordAsInput, htail] at h
      | some tail =>
          cases code with
          | nil =>
              simp [decodeCodeWordAsInput, htail] at h
          | cons sym syms =>
              simp [decodeCodeWordAsInput, htail] at h
              rcases h with ⟨decoded, hopt, hcode⟩
              cases hopt
              cases hcode
              have hrest :=
                decodeCodeWordAsInput_eq_some_encodeCodeWordAsInput htail
              simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput, hrest]
  | false :: true :: false :: false :: rest, code, h => by
      cases htail : decodeCodeWordAsInput rest with
      | none =>
          simp [decodeCodeWordAsInput, htail] at h
      | some tail =>
          cases code with
          | nil =>
              simp [decodeCodeWordAsInput, htail] at h
          | cons sym syms =>
              simp [decodeCodeWordAsInput, htail] at h
              rcases h with ⟨decoded, hopt, hcode⟩
              cases hopt
              cases hcode
              have hrest :=
                decodeCodeWordAsInput_eq_some_encodeCodeWordAsInput htail
              simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput, hrest]
  | false :: true :: false :: true :: rest, code, h => by
      cases htail : decodeCodeWordAsInput rest with
      | none =>
          simp [decodeCodeWordAsInput, htail] at h
      | some tail =>
          cases code with
          | nil =>
              simp [decodeCodeWordAsInput, htail] at h
          | cons sym syms =>
              simp [decodeCodeWordAsInput, htail] at h
              rcases h with ⟨decoded, hopt, hcode⟩
              cases hopt
              cases hcode
              have hrest :=
                decodeCodeWordAsInput_eq_some_encodeCodeWordAsInput htail
              simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput, hrest]
  | false :: true :: true :: false :: rest, code, h => by
      cases htail : decodeCodeWordAsInput rest with
      | none =>
          simp [decodeCodeWordAsInput, htail] at h
      | some tail =>
          cases code with
          | nil =>
              simp [decodeCodeWordAsInput, htail] at h
          | cons sym syms =>
              simp [decodeCodeWordAsInput, htail] at h
              rcases h with ⟨decoded, hopt, hcode⟩
              cases hopt
              cases hcode
              have hrest :=
                decodeCodeWordAsInput_eq_some_encodeCodeWordAsInput htail
              simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput, hrest]
  | false :: true :: true :: true :: rest, code, h => by
      cases htail : decodeCodeWordAsInput rest with
      | none =>
          simp [decodeCodeWordAsInput, htail] at h
      | some tail =>
          cases code with
          | nil =>
              simp [decodeCodeWordAsInput, htail] at h
          | cons sym syms =>
              simp [decodeCodeWordAsInput, htail] at h
              rcases h with ⟨decoded, hopt, hcode⟩
              cases hopt
              cases hcode
              have hrest :=
                decodeCodeWordAsInput_eq_some_encodeCodeWordAsInput htail
              simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput, hrest]
  | true :: false :: false :: false :: rest, code, h => by
      cases htail : decodeCodeWordAsInput rest with
      | none =>
          simp [decodeCodeWordAsInput, htail] at h
      | some tail =>
          cases code with
          | nil =>
              simp [decodeCodeWordAsInput, htail] at h
          | cons sym syms =>
              simp [decodeCodeWordAsInput, htail] at h
              rcases h with ⟨decoded, hopt, hcode⟩
              cases hopt
              cases hcode
              have hrest :=
                decodeCodeWordAsInput_eq_some_encodeCodeWordAsInput htail
              simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput, hrest]
  | true :: false :: false :: true :: rest, code, h => by
      simp [decodeCodeWordAsInput] at h
  | true :: false :: true :: false :: rest, code, h => by
      simp [decodeCodeWordAsInput] at h
  | true :: false :: true :: true :: rest, code, h => by
      simp [decodeCodeWordAsInput] at h
  | true :: true :: false :: false :: rest, code, h => by
      simp [decodeCodeWordAsInput] at h
  | true :: true :: false :: true :: rest, code, h => by
      simp [decodeCodeWordAsInput] at h
  | true :: true :: true :: false :: rest, code, h => by
      simp [decodeCodeWordAsInput] at h
  | true :: true :: true :: true :: rest, code, h => by
      simp [decodeCodeWordAsInput] at h
  | false :: [], code, h => by
      simp [decodeCodeWordAsInput] at h
  | true :: [], code, h => by
      simp [decodeCodeWordAsInput] at h
  | false :: false :: [], code, h => by
      simp [decodeCodeWordAsInput] at h
  | false :: true :: [], code, h => by
      simp [decodeCodeWordAsInput] at h
  | true :: false :: [], code, h => by
      simp [decodeCodeWordAsInput] at h
  | true :: true :: [], code, h => by
      simp [decodeCodeWordAsInput] at h
  | false :: false :: false :: [], code, h => by
      simp [decodeCodeWordAsInput] at h
  | false :: false :: true :: [], code, h => by
      simp [decodeCodeWordAsInput] at h
  | false :: true :: false :: [], code, h => by
      simp [decodeCodeWordAsInput] at h
  | false :: true :: true :: [], code, h => by
      simp [decodeCodeWordAsInput] at h
  | true :: false :: false :: [], code, h => by
      simp [decodeCodeWordAsInput] at h
  | true :: false :: true :: [], code, h => by
      simp [decodeCodeWordAsInput] at h
  | true :: true :: false :: [], code, h => by
      simp [decodeCodeWordAsInput] at h
  | true :: true :: true :: [], code, h => by
      simp [decodeCodeWordAsInput] at h

theorem decodeCodeWordAsInput_eq_some_iff
    (bits : Word Bool) (code : Word MachineCodeSymbol) :
    decodeCodeWordAsInput bits = some code <->
      bits = encodeCodeWordAsInput code := by
  constructor
  · exact decodeCodeWordAsInput_eq_some_encodeCodeWordAsInput
  · intro h
    rw [h]
    exact decodeCodeWordAsInput_encodeCodeWordAsInput code

theorem encodeCodeWordAsInput_injective :
    Function.Injective encodeCodeWordAsInput := by
  intro x y h
  have hdecode := congrArg decodeCodeWordAsInput h
  rw [decodeCodeWordAsInput_encodeCodeWordAsInput,
    decodeCodeWordAsInput_encodeCodeWordAsInput] at hdecode
  exact Option.some.inj hdecode

end MachineDescription

end Computability
end FoC
