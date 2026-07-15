import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.SemanticCore.Contract
import FoC.Computability.Compiler.Structured.Lowering.TypedStateRuns

namespace FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore

open Languages
open MachineDescription
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

inductive ResultPhase where
  | length0 | length1 | length2 | length3
  | seekCell | cell1 | cell2 | cell3False | cell3True
deriving DecidableEq

def resultPhases : List ResultPhase :=
  [ .length0, .length1, .length2, .length3, .seekCell,
    .cell1, .cell2, .cell3False, .cell3True ]

theorem mem_resultPhases (phase : ResultPhase) : phase ∈ resultPhases := by
  cases phase <;> simp [resultPhases]

inductive WritePhase where
  | length0 | length1 | length2 | lengthTick | lengthDone
  | cell0 | cell1 | cell2False | cell2True | cell3False | cell3True
deriving DecidableEq

def writePhases : List WritePhase :=
  [ .length0, .length1, .length2, .lengthTick, .lengthDone,
    .cell0, .cell1, .cell2False, .cell2True, .cell3False, .cell3True ]

theorem mem_writePhases (phase : WritePhase) : phase ∈ writePhases := by
  cases phase <;> simp [writePhases]

inductive CoreState where
  | header0 | header1 | header2 | header3
  | inputLen0 | inputLen1 | inputLen2 | inputLen3
  | field0 | field1 | cell2 | cell3 (third : Bool)
  | stage0 | stage1 | stage2 | stage3
  | eraseRight | eraseLeft | auxLeft | reconstruct | workLeft
  | run (state : Nat)
  | normalizeLeft
  | resultFirst | result (phase : ResultPhase) | writeResult (phase : WritePhase)
  | counterLeft | counterRight | checkCount
  | rewindA | rewindB | rewindC | rewindTokenFirst
  | markerSecond | rewindTrueBack
  | restoreThird | restoreFourth | restoreBackThird | restoreBackSecond
  | restoreFirst | spin | halt
deriving DecidableEq

def fixedStates : List CoreState :=
  [ .header0, .header1, .header2, .header3,
    .inputLen0, .inputLen1, .inputLen2, .inputLen3,
    .field0, .field1, .cell2, .cell3 false, .cell3 true,
    .stage0, .stage1, .stage2, .stage3,
    .eraseRight, .eraseLeft, .auxLeft, .reconstruct, .workLeft,
    .normalizeLeft, .resultFirst,
    .counterLeft, .counterRight, .checkCount,
    .rewindA, .rewindB, .rewindC, .rewindTokenFirst,
    .markerSecond, .rewindTrueBack,
    .restoreThird, .restoreFourth, .restoreBackThird, .restoreBackSecond,
    .restoreFirst, .spin, .halt ] ++
    resultPhases.map CoreState.result ++
    writePhases.map CoreState.writeResult

def states (attempt : MachineDescription) : List CoreState :=
  fixedStates ++
    (List.range attempt.stateCount).map CoreState.run

def StateBounded (attempt : MachineDescription) : CoreState -> Prop
  | .run q => q < attempt.stateCount
  | _ => True

theorem stateBounded_of_mem_states {attempt : MachineDescription} {s : CoreState}
    (hs : s ∈ states attempt) : StateBounded attempt s := by
  cases s with
  | run q =>
      simpa [StateBounded, states, fixedStates] using hs
  | cell3 b => cases b <;> trivial
  | result phase => trivial
  | writeResult phase => trivial
  | header0 | header1 | header2 | header3 |
      inputLen0 | inputLen1 | inputLen2 | inputLen3 |
      field0 | field1 | cell2 | stage0 | stage1 | stage2 | stage3 |
      eraseRight | eraseLeft | auxLeft | reconstruct | workLeft |
      normalizeLeft | resultFirst |
      counterLeft | counterRight | checkCount |
      rewindA | rewindB | rewindC | rewindTokenFirst |
      markerSecond | rewindTrueBack | restoreThird | restoreFourth |
      restoreBackThird | restoreBackSecond | restoreFirst | spin | halt => trivial

theorem mem_states_of_stateBounded {attempt : MachineDescription} {s : CoreState}
    (hs : StateBounded attempt s) : s ∈ states attempt := by
  cases s with
  | run q =>
      change q < attempt.stateCount at hs
      simpa [states, fixedStates] using hs
  | cell3 b => cases b <;> simp [states, fixedStates]
  | result phase => simp [states, fixedStates, mem_resultPhases phase]
  | writeResult phase => simp [states, fixedStates, mem_writePhases phase]
  | header0 | header1 | header2 | header3 |
      inputLen0 | inputLen1 | inputLen2 | inputLen3 |
      field0 | field1 | cell2 | stage0 | stage1 | stage2 | stage3 |
      eraseRight | eraseLeft | auxLeft | reconstruct | workLeft |
      normalizeLeft | resultFirst |
      counterLeft | counterRight | checkCount |
      rewindA | rewindB | rewindC | rewindTokenFirst |
      markerSecond | rewindTrueBack | restoreThird | restoreFourth |
      restoreBackThird | restoreBackSecond | restoreFirst | spin | halt =>
      simp [states, fixedStates]

def headMoveOfDirection : Direction -> HeadMove
  | .left => .left
  | .right => .right

def workAction (t : TransitionDescription) : TapeAction :=
  TapeAction.writeMove t.write (headMoveOfDirection t.move)

def markerAction (move : Direction) : TapeAction :=
  TapeAction.writeMove (some false) (headMoveOfDirection move)

def copyBoth (target : CoreState) (bit : Bool) : TypedStep CoreState :=
  { target := target, action0 := keepR,
    action1 := writeR (some bit), action2 := writeR (some bit) }

def copyOutput (target : CoreState) (bit : Bool) : TypedStep CoreState :=
  { target := target, action0 := keepR,
    action1 := keepS, action2 := writeR (some bit) }

def progressSpin : TypedStep CoreState :=
  { target := .spin, action0 := keepR, action1 := keepS, action2 := keepS }

def someStep (target : CoreState) (action0 action1 action2 : TapeAction) :
    Option (TypedStep CoreState) :=
  some ⟨target, action0, action1, action2⟩

def copyExpected (r0 : Option Bool) (expected : Bool)
    (target : CoreState) : Option (TypedStep CoreState) :=
  match r0 with
  | some bit =>
      if bit = expected then some (copyBoth target bit)
      else some progressSpin
  | none => some progressSpin

def writePhaseBit : WritePhase -> Bool
  | .length0 | .length1 | .lengthTick | .cell0 | .cell2False |
      .cell3True => false
  | .length2 | .lengthDone | .cell1 | .cell2True | .cell3False => true

def writePhaseTarget : WritePhase -> CoreState
  | .length0 => .result .length1
  | .length1 => .result .length2
  | .length2 => .result .length3
  | .lengthTick => .result .length0
  | .lengthDone => .result .seekCell
  | .cell0 => .result .cell1
  | .cell1 => .result .cell2
  | .cell2False => .result .cell3False
  | .cell2True => .result .cell3True
  | .cell3False | .cell3True => .result .seekCell

def writePhaseMarker : WritePhase -> Bool
  | .lengthTick => true
  | _ => false

def beginWrite (phase : WritePhase) : Option (TypedStep CoreState) :=
  someStep (writePhaseTarget phase) keepR
    (writeR (some (writePhaseMarker phase)))
    (writeR (some (writePhaseBit phase)))

def beginPendingWrite (phase : WritePhase) : Option (TypedStep CoreState) :=
  someStep (.writeResult phase) keepR
    (writeR (some (writePhaseMarker phase))) keepS

def next (attempt : MachineDescription) (s : CoreState) :
    Option Bool -> Option Bool -> Option Bool -> Option (TypedStep CoreState)
  | r0, r1, r2 =>
      match s with
      | .header0 =>
          if r0 = some false then some (copyOutput .header1 true) else some progressSpin
      | .header1 =>
          if r0 = some false then some (copyOutput .header2 true) else some progressSpin
      | .header2 =>
          if r0 = some false then some (copyOutput .header3 true) else some progressSpin
      | .header3 =>
          if r0 = some false then some (copyOutput .inputLen0 true) else some progressSpin
      | .inputLen0 => copyExpected r0 false .inputLen1
      | .inputLen1 => copyExpected r0 false .inputLen2
      | .inputLen2 => copyExpected r0 true .inputLen3
      | .inputLen3 =>
          match r0 with
          | some false => some (copyBoth .inputLen0 false)
          | some true => some (copyBoth .field0 true)
          | none => some progressSpin
      | .field0 => copyExpected r0 false .field1
      | .field1 =>
          match r0 with
          | some false => some (copyBoth .stage2 false)
          | some true => some (copyBoth .cell2 true)
          | none => some progressSpin
      | .cell2 =>
          match r0 with
          | some bit => some (copyBoth (.cell3 bit) bit)
          | none => some progressSpin
      | .cell3 third =>
          match r0 with
          | some bit =>
              if bit = !third then some (copyBoth .field0 bit)
              else some progressSpin
          | none => some progressSpin
      | .stage0 => copyExpected r0 false .stage1
      | .stage1 => copyExpected r0 false .stage2
      | .stage2 => copyExpected r0 true .stage3
      | .stage3 =>
          match r0 with
          | some false => some (copyBoth .stage0 false)
          | some true =>
              some ⟨.eraseRight, keepR,
                writeR (some true), writeR (some true)⟩
          | none => some progressSpin
      | .eraseRight =>
          match r0 with
          | some _ => someStep .eraseRight keepR keepS keepS
          | none => someStep .eraseLeft keepL keepS keepS
      | .eraseLeft =>
          match r0 with
          | some _ => someStep .eraseLeft eraseL keepS keepS
          | none => someStep .auxLeft keepR keepL keepS
      | .auxLeft =>
          match r1 with
          | some _ => someStep .auxLeft keepS keepL keepS
          | none => someStep .reconstruct keepS keepR keepS
      | .reconstruct =>
          match r1 with
          | some bit =>
              someStep .reconstruct (writeR (some bit))
                (writeR (some false)) keepS
          | none => someStep .workLeft keepL keepL keepS
      | .workLeft =>
          match r1 with
          | some _ => someStep .workLeft keepL keepL keepS
          | none => someStep (.run attempt.start) keepR keepR keepS
      | .run q =>
          if q = attempt.halt then
            someStep .normalizeLeft keepL (writeL (some false)) keepS
          else
            match attempt.lookupTransition q r0 with
            | none => some progressSpin
            | some t =>
                someStep (.run t.target) (workAction t)
                  (markerAction t.move) keepS
      | .normalizeLeft =>
          match r1 with
          | some _ => someStep .normalizeLeft keepL keepL keepS
          | none => someStep .resultFirst keepR keepR keepS
      | .resultFirst =>
          match r1, r0 with
          | some _, none =>
              someStep .resultFirst keepR (writeR (some false)) keepS
          | some _, some false =>
              someStep (.result .length1) keepR (writeR (some false))
                (writeR (some false))
          | _, _ => some progressSpin
      | .result phase =>
          match r1 with
          | none =>
              match phase with
              | .seekCell => someStep .checkCount keepS keepL keepS
              | _ => some progressSpin
          | some _ =>
              match r0 with
              | none =>
                  someStep (.result phase) keepR (writeR (some false)) keepS
              | some bit =>
                  match phase with
                  | .length0 => if bit = false then beginWrite .length0 else some progressSpin
                  | .length1 => if bit = false then beginWrite .length1 else some progressSpin
                  | .length2 => if bit = true then beginWrite .length2 else some progressSpin
                  | .length3 =>
                      if bit then beginPendingWrite .lengthDone
                      else beginWrite .lengthTick
                  | .seekCell =>
                      if bit = false then
                        someStep .counterLeft keepS eraseL keepS
                      else
                        some progressSpin
                  | .cell1 => if bit = true then beginWrite .cell1 else some progressSpin
                  | .cell2 => beginWrite (if bit then .cell2True else .cell2False)
                  | .cell3False =>
                      if bit = true then beginPendingWrite .cell3False
                      else some progressSpin
                  | .cell3True =>
                      if bit = false then beginPendingWrite .cell3True
                      else some progressSpin
      | .writeResult phase =>
          match phase with
          | .lengthDone | .cell3False | .cell3True =>
              match r1, r0 with
              | some _, none =>
                  someStep (.writeResult phase) keepR
                    (writeR (some false)) keepS
              | some _, some _ =>
                  someStep (writePhaseTarget phase) keepS keepS
                    (writeR (some (writePhaseBit phase)))
              | none, _ =>
                  someStep (writePhaseTarget phase) keepS keepS
                    (writeS (some (writePhaseBit phase)))
          | _ =>
              someStep (writePhaseTarget phase) keepR
                (writeR (some (writePhaseMarker phase)))
                (writeS (some (writePhaseBit phase)))
      | .counterLeft =>
          match r1 with
          | some false => someStep .counterLeft keepS keepL keepS
          | some true => someStep .counterRight keepS (writeR (some false)) keepS
          | none => some progressSpin
      | .counterRight =>
          match r1 with
          | some _ => someStep .counterRight keepS keepR keepS
          | none =>
              someStep (.result .cell1) keepR (writeR (some false))
                (writeR (some false))
      | .checkCount =>
          match r1 with
          | some false => someStep .checkCount keepS keepL keepS
          | some true => some progressSpin
          | none => someStep .rewindA keepS keepS keepS
      | .rewindA => someStep .rewindB keepS keepS keepL
      | .rewindB => someStep .rewindC keepS keepS keepL
      | .rewindC => someStep .rewindTokenFirst keepS keepS keepL
      | .rewindTokenFirst =>
          match r2 with
          | some false => someStep .rewindA keepS keepS keepL
          | some true => someStep .markerSecond keepS keepS keepR
          | none => some progressSpin
      | .markerSecond =>
          match r2 with
          | some false => someStep .rewindTrueBack keepS keepS keepL
          | some true => someStep .restoreThird keepS keepS (writeR (some false))
          | none => some progressSpin
      | .rewindTrueBack => someStep .rewindA keepS keepS keepL
      | .restoreThird =>
          if r2 = some true then
            someStep .restoreFourth keepS keepS (writeR (some false))
          else
            some progressSpin
      | .restoreFourth =>
          if r2 = some true then
            someStep .restoreBackThird keepS keepS (writeL (some false))
          else
            some progressSpin
      | .restoreBackThird => someStep .restoreBackSecond keepS keepS keepL
      | .restoreBackSecond => someStep .restoreFirst keepS keepS keepL
      | .restoreFirst =>
          if r2 = some true then
            someStep .halt keepR keepS (writeS (some false))
          else
            some progressSpin
      | .spin => some progressSpin
      | .halt => none

theorem next_target_bounded (attempt : MachineDescription)
    (hattempt : attempt.WellFormed) (s : CoreState)
    (hs : StateBounded attempt s) (r0 r1 r2 : Option Bool)
    (st : TypedStep CoreState) (hnext : next attempt s r0 r1 r2 = some st) :
    StateBounded attempt st.target := by
  cases s with
  | run q =>
      by_cases hq : q = attempt.halt
      · simp [next, hq, someStep] at hnext
        subst st
        trivial
      · simp [next, hq, someStep] at hnext
        cases ht : attempt.lookupTransition q r0 with
        | none =>
            simp [ht, progressSpin] at hnext
            subst st
            trivial
        | some t =>
            simp [ht] at hnext
            subst st
            exact (hattempt.right.right.right.left t
              (lookupTransition_mem ht)).right
  | cell3 third =>
      cases third <;> cases r0 <;> (try cases ‹Bool›) <;>
        simp [next, copyBoth, progressSpin] at hnext <;> subst st <;> trivial
  | result phase =>
      cases phase <;>
        cases r0 <;> (try cases ‹Bool›) <;>
          cases r1 <;> (try cases ‹Bool›) <;>
            cases r2 <;> (try cases ‹Bool›) <;>
              simp [next, beginWrite, beginPendingWrite,
                progressSpin, someStep] at hnext <;>
                subst st <;> trivial
  | writeResult phase =>
      cases phase <;>
        cases r0 <;> (try cases ‹Bool›) <;>
          cases r1 <;> (try cases ‹Bool›) <;>
            simp [next, writePhaseTarget, writePhaseMarker, writePhaseBit,
              someStep] at hnext <;> subst st <;> trivial
  | header0 | header1 | header2 | header3 |
      inputLen0 | inputLen1 | inputLen2 | inputLen3 |
      field0 | field1 | cell2 | stage0 | stage1 | stage2 | stage3 |
      eraseRight | eraseLeft | auxLeft | reconstruct | workLeft |
      normalizeLeft | resultFirst |
      counterLeft | counterRight | checkCount |
      rewindA | rewindB | rewindC | rewindTokenFirst |
      markerSecond | rewindTrueBack | restoreThird | restoreFourth |
      restoreBackThird | restoreBackSecond | restoreFirst | spin =>
      cases r0 <;> (try cases ‹Bool›) <;>
        cases r1 <;> (try cases ‹Bool›) <;>
          cases r2 <;> (try cases ‹Bool›) <;>
            simp [next, copyExpected, copyBoth, copyOutput,
              progressSpin, someStep] at hnext <;> subst st <;>
              simp [StateBounded, hattempt.right.left]
  | halt => simp [next] at hnext

def table (attempt : MachineDescription) (hattempt : attempt.SubroutineReady) :
    TypedStateTable CoreState :=
  TypedStateTable.ofList
    (states attempt) .header0 .halt (next attempt)
    (mem_states_of_stateBounded trivial)
    (mem_states_of_stateBounded trivial)
    (by intro r0 r1 r2; rfl)
    (fun s hs r0 r1 r2 st hnext =>
      mem_states_of_stateBounded
        (next_target_bounded attempt hattempt.left s
          (stateBounded_of_mem_states hs) r0 r1 r2 st hnext))

def coreD (attempt : MachineDescription) (hattempt : attempt.SubroutineReady) :
    Description :=
  (table attempt hattempt).description

end FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore
