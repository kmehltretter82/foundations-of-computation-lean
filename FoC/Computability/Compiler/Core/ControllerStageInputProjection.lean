import FoC.Computability.Compiler.Core.EncodedRewriters

set_option doc.verso true

/-!
# Controller stage-input projection machine
-/

namespace FoC
namespace Computability

open Languages

def dovetailControllerProjectionKeep
    (source : Nat) (cell : Bool) (target : Nat) :
    TransitionDescription :=
  MachineDescription.transition source (some cell) (some cell)
    Direction.right target

def dovetailControllerProjectionErase
    (source : Nat) (cell : Option Bool) (target : Nat) :
    TransitionDescription :=
  MachineDescription.transition source cell none Direction.right target

def dovetailControllerProjectionKeepMove
    (source : Nat) (cell : Option Bool) (move : Direction) (target : Nat) :
    TransitionDescription :=
  MachineDescription.transition source cell cell move target

def dovetailControllerProjectionWriteMove
    (source : Nat) (read write : Option Bool) (move : Direction)
    (target : Nat) : TransitionDescription :=
  MachineDescription.transition source read write move target

def dovetailControllerProjectionScanLeftToBoundary
    (scan one two three found : Nat) : List TransitionDescription :=
  [ dovetailControllerProjectionKeepMove scan none Direction.left one
  , dovetailControllerProjectionKeepMove scan (some false) Direction.left scan
  , dovetailControllerProjectionKeepMove scan (some true) Direction.left scan
  , dovetailControllerProjectionKeepMove one none Direction.left two
  , dovetailControllerProjectionKeepMove one (some false) Direction.left scan
  , dovetailControllerProjectionKeepMove one (some true) Direction.left scan
  , dovetailControllerProjectionKeepMove two none Direction.left three
  , dovetailControllerProjectionKeepMove two (some false) Direction.left scan
  , dovetailControllerProjectionKeepMove two (some true) Direction.left scan
  , dovetailControllerProjectionKeepMove three none Direction.right found
  , dovetailControllerProjectionKeepMove three (some false) Direction.left scan
  , dovetailControllerProjectionKeepMove three (some true) Direction.left scan ]

private def transitionWellFormedBool
    (stateCount : Nat) (t : TransitionDescription) : Bool :=
  decide (t.source < stateCount) && decide (t.target < stateCount)

private def transitionSameKeyBool
    (t u : TransitionDescription) : Bool :=
  decide (t.source = u.source) && decide (t.read = u.read)

private def transitionSameActionBool
    (t u : TransitionDescription) : Bool :=
  decide (t.write = u.write) && decide (t.move = u.move) &&
    decide (t.target = u.target)

private def transitionDeterministicPairBool
    (t u : TransitionDescription) : Bool :=
  !transitionSameKeyBool t u || transitionSameActionBool t u

private def transitionNotFromBool
    (state : Nat) (t : TransitionDescription) : Bool :=
  decide (t.source ≠ state)

private theorem transition_wellFormed_of_all
    {stateCount : Nat} {l : List TransitionDescription}
    (h : l.all (transitionWellFormedBool stateCount) = true) :
    forall t : TransitionDescription,
      t ∈ l -> TransitionDescription.WellFormed stateCount t := by
  intro t ht
  have htbool := (List.all_eq_true.mp h) t ht
  simpa [transitionWellFormedBool, TransitionDescription.WellFormed] using
    htbool

private theorem transition_deterministic_of_all
    {l : List TransitionDescription}
    (h :
      l.all (fun t =>
        l.all (fun u => transitionDeterministicPairBool t u)) = true) :
    forall t u : TransitionDescription,
      t ∈ l ->
      u ∈ l ->
      TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u := by
  intro t u ht hu hkey
  have htbool := (List.all_eq_true.mp h) t ht
  have hubool := (List.all_eq_true.mp htbool) u hu
  have hkeyBool :
      transitionSameKeyBool t u = true := by
    simpa [transitionSameKeyBool, TransitionDescription.SameKey] using hkey
  simp [transitionDeterministicPairBool, hkeyBool, transitionSameActionBool,
    TransitionDescription.SameAction] at hubool ⊢
  rcases hubool with ⟨⟨hwrite, hmove⟩, htarget⟩
  exact ⟨hwrite, hmove, htarget⟩

private theorem transition_notFrom_of_all
    {state : Nat} {l : List TransitionDescription}
    (h : l.all (transitionNotFromBool state) = true) :
    forall t : TransitionDescription, t ∈ l -> t.source ≠ state := by
  intro t ht
  have htbool := (List.all_eq_true.mp h) t ht
  exact of_decide_eq_true htbool

def DovetailControllerStageInputProjectionDescription :
    MachineDescription where
  stateCount := 1000
  start := 0
  halt := 999
  transitions :=
    [ dovetailControllerProjectionErase 0 (some false) 1
    , dovetailControllerProjectionErase 1 (some false) 2
    , dovetailControllerProjectionErase 2 (some false) 3
    , dovetailControllerProjectionErase 3 (some false) 100

    -- Validate the input bool-word length prefix, marking ticks and cells.
    , dovetailControllerProjectionKeep 100 false 101
    , dovetailControllerProjectionKeep 101 false 102
    , dovetailControllerProjectionKeep 102 true 103
    , dovetailControllerProjectionWriteMove 103 (some false) none Direction.right 120
    , dovetailControllerProjectionKeep 103 true 150
    , dovetailControllerProjectionKeepMove 103 none Direction.right 100

    -- Skip the remaining input length prefix to find the matching cell.
    , dovetailControllerProjectionKeep 120 false 121
    , dovetailControllerProjectionKeep 121 false 122
    , dovetailControllerProjectionKeep 122 true 123
    , dovetailControllerProjectionKeep 123 false 120
    , dovetailControllerProjectionKeep 123 true 130
    , dovetailControllerProjectionKeepMove 123 none Direction.right 120

    -- Mark one unprocessed input cell for the tick just marked.
    , dovetailControllerProjectionKeep 130 false 131
    , dovetailControllerProjectionWriteMove 131 (some true) none Direction.right 132
    , dovetailControllerProjectionKeepMove 131 none Direction.right 135
    , dovetailControllerProjectionKeep 132 false 133
    , dovetailControllerProjectionKeep 132 true 134
    , dovetailControllerProjectionKeepMove 133 (some true) Direction.left 140
    , dovetailControllerProjectionKeepMove 134 (some false) Direction.left 140
    , dovetailControllerProjectionKeep 135 false 136
    , dovetailControllerProjectionKeep 135 true 137
    , dovetailControllerProjectionKeep 136 true 130
    , dovetailControllerProjectionKeep 137 false 130

    -- No unmarked ticks remain: ensure all input cells were processed.
    , dovetailControllerProjectionKeep 150 false 151
    , dovetailControllerProjectionKeepMove 151 none Direction.right 152
    , dovetailControllerProjectionKeepMove 151 (some false) Direction.left 160
    , dovetailControllerProjectionKeep 152 false 153
    , dovetailControllerProjectionKeep 152 true 154
    , dovetailControllerProjectionKeep 153 true 150
    , dovetailControllerProjectionKeep 154 false 150

    -- Restore the marked input prefix, then continue at the stage nat.
    , dovetailControllerProjectionKeepMove 164 none Direction.right 165
    , dovetailControllerProjectionKeepMove 165 none Direction.right 166
    , dovetailControllerProjectionKeepMove 166 none Direction.right 170
    , dovetailControllerProjectionKeep 170 false 171
    , dovetailControllerProjectionKeep 171 false 172
    , dovetailControllerProjectionKeep 172 true 173
    , dovetailControllerProjectionKeep 173 false 170
    , dovetailControllerProjectionWriteMove 173 none (some false) Direction.right 170
    , dovetailControllerProjectionKeep 173 true 180
    , dovetailControllerProjectionKeep 180 false 181
    , dovetailControllerProjectionWriteMove 181 none (some true) Direction.right 182
    , dovetailControllerProjectionKeepMove 181 (some false) Direction.left 200
    , dovetailControllerProjectionKeep 182 false 183
    , dovetailControllerProjectionKeep 182 true 184
    , dovetailControllerProjectionKeep 183 true 180
    , dovetailControllerProjectionKeep 184 false 180

    -- Preserve and validate the stage nat prefix.
    , dovetailControllerProjectionKeep 200 false 201
    , dovetailControllerProjectionKeep 201 false 202
    , dovetailControllerProjectionKeep 202 true 203
    , dovetailControllerProjectionKeep 203 false 200
    , dovetailControllerProjectionKeep 203 true 210

    -- Mark the stage-nat terminator as a four-blank boundary.
    , dovetailControllerProjectionKeepMove 210 (some false) Direction.left 211
    , dovetailControllerProjectionWriteMove 211 (some true) none Direction.left 212
    , dovetailControllerProjectionWriteMove 212 (some true) none Direction.left 213
    , dovetailControllerProjectionWriteMove 213 (some false) none Direction.left 214
    , dovetailControllerProjectionWriteMove 214 (some false) none Direction.right 215
    , dovetailControllerProjectionKeepMove 215 none Direction.right 216
    , dovetailControllerProjectionKeepMove 216 none Direction.right 217
    , dovetailControllerProjectionKeepMove 217 none Direction.right 300

    -- Validate the result bool-word length prefix, marking ticks and cells.
    , dovetailControllerProjectionKeep 300 false 301
    , dovetailControllerProjectionKeep 301 false 302
    , dovetailControllerProjectionKeep 302 true 303
    , dovetailControllerProjectionWriteMove 303 (some false) none Direction.right 320
    , dovetailControllerProjectionKeep 303 true 350
    , dovetailControllerProjectionKeepMove 303 none Direction.right 300

    -- Skip the remaining result length prefix to find the matching cell.
    , dovetailControllerProjectionKeep 320 false 321
    , dovetailControllerProjectionKeep 321 false 322
    , dovetailControllerProjectionKeep 322 true 323
    , dovetailControllerProjectionKeep 323 false 320
    , dovetailControllerProjectionKeep 323 true 330
    , dovetailControllerProjectionKeepMove 323 none Direction.right 320

    -- Mark one unprocessed result cell for the tick just marked.
    , dovetailControllerProjectionKeep 330 false 331
    , dovetailControllerProjectionWriteMove 331 (some true) none Direction.right 332
    , dovetailControllerProjectionKeepMove 331 none Direction.right 335
    , dovetailControllerProjectionKeep 332 false 333
    , dovetailControllerProjectionKeep 332 true 334
    , dovetailControllerProjectionKeepMove 333 (some true) Direction.left 340
    , dovetailControllerProjectionKeepMove 334 (some false) Direction.left 340
    , dovetailControllerProjectionKeep 335 false 336
    , dovetailControllerProjectionKeep 335 true 337
    , dovetailControllerProjectionKeep 336 true 330
    , dovetailControllerProjectionKeep 337 false 330

    -- No unmarked ticks remain: ensure all result cells were processed.
    , dovetailControllerProjectionKeep 350 false 351
    , dovetailControllerProjectionKeepMove 350 none Direction.left 360
    , dovetailControllerProjectionKeepMove 351 none Direction.right 352
    , dovetailControllerProjectionKeep 352 false 353
    , dovetailControllerProjectionKeep 352 true 354
    , dovetailControllerProjectionKeep 353 true 350
    , dovetailControllerProjectionKeep 354 false 350

    -- Restore the stage-nat terminator boundary.
    , dovetailControllerProjectionWriteMove 363 none (some false) Direction.right 364
    , dovetailControllerProjectionWriteMove 364 none (some false) Direction.right 365
    , dovetailControllerProjectionWriteMove 365 none (some true) Direction.right 366
    , dovetailControllerProjectionWriteMove 366 none (some true) Direction.right 367

    -- Blank the validated result length prefix and cell payload.
    , dovetailControllerProjectionErase 367 (some false) 368
    , dovetailControllerProjectionErase 368 (some false) 369
    , dovetailControllerProjectionErase 369 (some true) 370
    , dovetailControllerProjectionErase 370 (some false) 367
    , dovetailControllerProjectionErase 370 none 367
    , dovetailControllerProjectionErase 370 (some true) 380
    , dovetailControllerProjectionErase 380 (some false) 381
    , dovetailControllerProjectionErase 380 none 999
    , dovetailControllerProjectionErase 381 none 382
    , dovetailControllerProjectionErase 382 (some false) 383
    , dovetailControllerProjectionErase 382 (some true) 384
    , dovetailControllerProjectionErase 383 (some true) 380
    , dovetailControllerProjectionErase 384 (some false) 380 ]
      ++ dovetailControllerProjectionScanLeftToBoundary 140 141 142 143 144
      ++
    [ dovetailControllerProjectionKeepMove 144 none Direction.right 145
    , dovetailControllerProjectionKeepMove 145 none Direction.right 146
    , dovetailControllerProjectionKeepMove 146 none Direction.right 100 ]
      ++ dovetailControllerProjectionScanLeftToBoundary 160 161 162 163 164
      ++ dovetailControllerProjectionScanLeftToBoundary 340 341 342 343 344
      ++
    [ dovetailControllerProjectionKeepMove 344 none Direction.right 345
    , dovetailControllerProjectionKeepMove 345 none Direction.right 346
    , dovetailControllerProjectionKeepMove 346 none Direction.right 300 ]
      ++
    [ dovetailControllerProjectionKeepMove 360 none Direction.left 361
    , dovetailControllerProjectionKeepMove 360 (some false) Direction.left 360
    , dovetailControllerProjectionKeepMove 360 (some true) Direction.left 360
    , dovetailControllerProjectionKeepMove 361 none Direction.left 362
    , dovetailControllerProjectionKeepMove 361 (some false) Direction.left 360
    , dovetailControllerProjectionKeepMove 361 (some true) Direction.left 360
    , dovetailControllerProjectionKeepMove 362 none Direction.left 363
    , dovetailControllerProjectionKeepMove 362 (some false) Direction.left 360
    , dovetailControllerProjectionKeepMove 362 (some true) Direction.left 360
    , dovetailControllerProjectionKeepMove 363 (some false) Direction.left 360
    , dovetailControllerProjectionKeepMove 363 (some true) Direction.left 360 ]

theorem dovetailControllerStageInputProjectionDescription_wellFormed :
    DovetailControllerStageInputProjectionDescription.WellFormed := by
  constructor
  · simp [DovetailControllerStageInputProjectionDescription]
  constructor
  · simp [DovetailControllerStageInputProjectionDescription]
  constructor
  · simp [DovetailControllerStageInputProjectionDescription]
  constructor
  · intro t ht
    exact transition_wellFormed_of_all
      (l := DovetailControllerStageInputProjectionDescription.transitions)
      (stateCount := DovetailControllerStageInputProjectionDescription.stateCount)
      (by
        native_decide) t ht
  · intro t u ht hu hkey
    exact transition_deterministic_of_all
      (l := DovetailControllerStageInputProjectionDescription.transitions)
      (by
        native_decide) t u ht hu hkey

theorem dovetailControllerStageInputProjectionDescription_haltTransitionFree :
    DovetailControllerStageInputProjectionDescription.HaltTransitionFree := by
  intro t ht
  exact transition_notFrom_of_all
    (l := DovetailControllerStageInputProjectionDescription.transitions)
    (state := DovetailControllerStageInputProjectionDescription.halt)
    (by
      native_decide) t ht

theorem dovetailControllerStageInputProjectionDescription_haltsWithOutput_of_transform_eq_some
    {code out : Word MachineCodeSymbol}
    (h :
      PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
          code = some out) :
    DovetailControllerStageInputProjectionDescription.HaltsWithOutput
      (MachineDescription.encodeCodeWordAsInput code)
      (MachineDescription.encodeCodeWordAsInput out) := by
  sorry

theorem dovetailControllerStageInputProjectionDescription_transform_eq_some_of_haltsWithOutput
    {code out : Word MachineCodeSymbol}
    (h :
      DovetailControllerStageInputProjectionDescription.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out)) :
    PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
        code = some out := by
  sorry

theorem dovetailControllerStageInputProjectionDescription_haltsWithOutput_iff
    (code out : Word MachineCodeSymbol) :
    DovetailControllerStageInputProjectionDescription.HaltsWithOutput
        (MachineDescription.encodeCodeWordAsInput code)
        (MachineDescription.encodeCodeWordAsInput out) <->
      PairedRecognizerDovetailControllerStageInputCodePrimitive.transform
        code = some out := by
  constructor
  · exact
      dovetailControllerStageInputProjectionDescription_transform_eq_some_of_haltsWithOutput
  · exact
      dovetailControllerStageInputProjectionDescription_haltsWithOutput_of_transform_eq_some

theorem dovetailControllerStageInputProjectionDescription_outputCompiledSubroutine :
    TapeCodePrimitiveOutputCompiledSubroutineByDescription
      PairedRecognizerDovetailControllerStageInputCodePrimitive
      DovetailControllerStageInputProjectionDescription :=
  ⟨⟨dovetailControllerStageInputProjectionDescription_wellFormed,
      dovetailControllerStageInputProjectionDescription_haltsWithOutput_iff⟩,
    dovetailControllerStageInputProjectionDescription_haltTransitionFree⟩

theorem encodedControllerStageInputProjectionCodeWordSubroutineConstruction_scaffold :
    EncodedControllerStageInputProjectionCodeWordSubroutineConstruction := by
  exact
    ⟨DovetailControllerStageInputProjectionDescription,
      dovetailControllerStageInputProjectionDescription_outputCompiledSubroutine⟩

end Computability
end FoC
