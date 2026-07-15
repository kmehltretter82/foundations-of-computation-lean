import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.IndexedMaterializer.CommonLocator
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.Tape2Rewinder
import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.WriteWordRight

set_option doc.verso true

/-!
Exact accepting-branch token phases and their lowered finite-machine contracts.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat
namespace Route
namespace AcceptBranch

open CanonicalLayouts.DovetailLayoutScanner CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver
open MarkerAwareCommon

def inputStageBits (L : DovetailLayout) : List Bool :=
  List.append (boolWordFieldBits L.input []).tail
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      L.stage)

def acceptBits (L : DovetailLayout) : List Bool :=
  configurationFieldBits L.acceptConfig []
def rejectBits (L : DovetailLayout) : List Bool :=
  configurationFieldBits L.rejectConfig []

def acceptHitBits (L : DovetailLayout) : List Bool :=
  boolFieldBits L.acceptHit []

def rejectHitBits (L : DovetailLayout) : List Bool :=
  boolFieldBits L.rejectHit []
def acceptCounterBits (L : DovetailLayout) : List Bool :=
  List.append (rejectBits L) (acceptHitBits L)

def liveBits (L : DovetailLayout) : List Bool :=
  List.append
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      L.stage)
    (List.append (acceptBits L)
      (List.append (rejectBits L)
        (List.append (acceptHitBits L) (rejectHitBits L))))

theorem dataBits_accept_decomp (L : DovetailLayout) :
    dataBits L =
      List.append (inputStageBits L)
        (List.append (acceptBits L)
          (List.append (rejectBits L)
            (List.append (acceptHitBits L) (rejectHitBits L)))) := by
  simp [dataBits, inputStageBits, acceptBits, rejectBits, acceptHitBits,
    rejectHitBits, configHitBits, List.append_assoc]
theorem afterStageTape2_accept_eq_counterTape (L : DovetailLayout) :
    afterStageTape2 (acceptOutputRest L) L =
      PairStream.counterTape
        (List.append
          ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
            L.stage).reverse.map some)
          (counterBaseLeft L))
        (acceptCounterBits L) := by
  simp [afterStageTape2, acceptOutputRest, acceptCounterBits,
    rejectBits, acceptHitBits,
    selectedProjectionPaddedTailCleanupSelectedHitBits,
    PairStream.counterTape, scanTape, tapeAtCells,
    List.map_append, List.append_assoc]

theorem acceptCounterBits_length_le_dataBits (L : DovetailLayout) :
    (acceptCounterBits L).length <= (dataBits L).length := by
  rw [dataBits_accept_decomp]
  simp [acceptCounterBits]
  lia

def pairDescription : MachineDescription :=
  lowerStructured3Description PairStream.description
theorem pair_ready : PairStream.description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool
    PairStream.description (by decide)

theorem pair_supports : SupportsReadWriteRows3 PairStream.description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

theorem pairDescription_ready : pairDescription.SubroutineReady := by
  simpa [pairDescription] using
    lowerStructured3Description_subroutineReady pair_ready.left pair_supports
theorem pairDescription_realizes
    (source counter : List Bool)
    (left0 left2 : List (Option Bool)) (rest0 : List Bool)
    (hlength : counter.length <= source.length) :
    pairDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (scanTape left0
          (List.append (AcceptConfigCopy.wrappedBits source) rest0))
        Tape.blank (PairStream.counterTape left2 counter))
      (encodedGuardedStructured3Tapes
        (scanTape
          (List.append
            ((AcceptConfigCopy.wrappedBits
              (source.take counter.length)).reverse.map some)
            left0)
          (List.append
            (AcceptConfigCopy.wrappedBits (source.drop counter.length))
            rest0))
        Tape.blank
        (PairStream.counterTape
          (List.append (counter.reverse.map some) left2) [])) := by
  simpa [pairDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      pair_ready.left pair_ready.right pair_supports
      (c := config PairStream.loop
        (scanTape left0
          (List.append (AcceptConfigCopy.wrappedBits source) rest0))
        Tape.blank (PairStream.counterTape left2 counter))
      (tapes :=
        [ scanTape
            (List.append
              ((AcceptConfigCopy.wrappedBits
                (source.take counter.length)).reverse.map some)
              left0)
            (List.append
              (AcceptConfigCopy.wrappedBits (source.drop counter.length))
              rest0)
        , Tape.blank
        , PairStream.counterTape
            (List.append (counter.reverse.map some) left2) [] ])
      rfl rfl ⟨PairStream.fuel counter,
        PairStream.run source counter left0 left2 rest0 hlength⟩

def afterPairTape0 (L : DovetailLayout) : Tape Bool :=
  scanTape
    (List.append
      ((AcceptConfigCopy.wrappedBits
        ((dataBits L).take (acceptCounterBits L).length)).reverse.map some)
      (commonEndpointLeft L))
    (List.append
      (AcceptConfigCopy.wrappedBits
        ((dataBits L).drop (acceptCounterBits L).length))
      (rawBoundaryRest true L))

def afterPairTape2 (L : DovetailLayout) : Tape Bool :=
  PairStream.counterTape
    (List.append ((acceptCounterBits L).reverse.map some)
      (List.append
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          L.stage).reverse.map some)
        (counterBaseLeft L)))
    []
theorem pairAtCommon_realizes (L : DovetailLayout) :
    pairDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (commonEndpointTape0 true L) Tape.blank
        (afterStageTape2 (acceptOutputRest L) L))
      (encodedGuardedStructured3Tapes
        (afterPairTape0 L) Tape.blank (afterPairTape2 L)) := by
  rw [afterStageTape2_accept_eq_counterTape]
  simpa [commonEndpointTape0, afterPairTape0, afterPairTape2] using
    pairDescription_realizes
      (dataBits L) (acceptCounterBits L) (commonEndpointLeft L)
      (List.append
        ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          L.stage).reverse.map some)
        (counterBaseLeft L))
      (rawBoundaryRest true L)
      (acceptCounterBits_length_le_dataBits L)

def counterBaseTail (L : DovetailLayout) : List (Option Bool) :=
  (counterBaseLeft L).tail

theorem counterBaseLeft_eq_none_cons (L : DovetailLayout) :
    counterBaseLeft L = none :: counterBaseTail L := by
  have hpos : 0 < (ParsedLayoutBits L).length := by
    rw [parsedLayoutBits_fieldDecomp]
    simp [transitionPrefixBits_length]
    lia
  cases hlen : (ParsedLayoutBits L).length with
  | zero => simp [hlen] at hpos
  | succ n =>
      simp [counterBaseLeft, counterBaseTail, hlen, List.replicate_succ]
def stageCounterBits (L : DovetailLayout) : List Bool :=
  List.append
    (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
      L.stage)
    (acceptCounterBits L)

theorem afterPairTape2_eq_rewindSource (L : DovetailLayout) :
    afterPairTape2 L =
      Tape2Rewinder.sourceTapeWithContext
        (counterBaseTail L) (stageCounterBits L) [] := by
  unfold afterPairTape2
  rw [counterBaseLeft_eq_none_cons]
  simp [Tape2Rewinder.sourceTapeWithContext, stageCounterBits,
    PairStream.counterTape, List.reverse_append, List.map_append,
    List.append_assoc]

def rewindDescription : MachineDescription :=
  Tape2Rewinder.loweredDescription
theorem rewindDescription_ready : rewindDescription.SubroutineReady := by
  simpa [rewindDescription] using
    Tape2Rewinder.loweredDescription_subroutineReady

theorem rewindDescription_realizes
    (baseLeft : List (Option Bool)) (bits : List Bool)
    (T0 : Tape Bool) :
    rewindDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (Tape2Rewinder.sourceTapeWithContext baseLeft bits []))
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (Tape2Rewinder.targetTapeWithContext baseLeft bits [])) := by
  simpa [rewindDescription] using
    Tape2Rewinder.loweredDescription_realizes_withContext
      baseLeft bits [] T0 Tape.blank

def afterRewindTape2 (L : DovetailLayout) : Tape Bool :=
  Tape2Rewinder.targetTapeWithContext
    (counterBaseTail L) (stageCounterBits L) []
theorem rewindAtPair_realizes (L : DovetailLayout) :
    rewindDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterPairTape0 L) Tape.blank (afterPairTape2 L))
      (encodedGuardedStructured3Tapes
        (afterPairTape0 L) Tape.blank (afterRewindTape2 L)) := by
  rw [afterPairTape2_eq_rewindSource]
  exact rewindDescription_realizes (counterBaseTail L)
    (stageCounterBits L) (afterPairTape0 L)

theorem rawBoundaryRest_eq_false_false_drop (L : DovetailLayout) :
    rawBoundaryRest true L =
      false :: false :: (rawBoundaryRest true L).drop 2 := by
  rcases
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_false_false_tail
        L.stage with
    ⟨tail, htail⟩
  rw [rawBoundaryRest, false_cons_structuredSuffixTail]
  simp [htail]

def remainingBits (L : DovetailLayout) : List Bool :=
  (dataBits L).drop (acceptCounterBits L).length
def atBoundaryTape0 (L : DovetailLayout) : Tape Bool :=
  scanTape
    (List.append
      ((AcceptConfigCopy.wrappedBits (remainingBits L)).reverse.map some)
      (List.append
        ((AcceptConfigCopy.wrappedBits
          ((dataBits L).take (acceptCounterBits L).length)).reverse.map some)
        (commonEndpointLeft L)))
    (rawBoundaryRest true L)

namespace EraseFour

def s0 : Nat := 0
def s1 : Nat := 1
def s2 : Nat := 2
def s3 : Nat := 3
def halt : Nat := 4

def rowsForRead (source target : Nat) :
    List CommonGround.FiniteTransducers.Structured.Transition :=
  allReads3 fun read0 read1 read2 =>
    row source read0 read1 read2 keepS keepS eraseR target
def rows : List CommonGround.FiniteTransducers.Structured.Transition :=
  [rowsForRead s0 s1, rowsForRead s1 s2, rowsForRead s2 s3,
    rowsForRead s3 halt].flatten

def description : CommonGround.FiniteTransducers.Structured.Description :=
  ThreeTape.description 5 s0 halt rows

syntax "erase_four_step_cases" ident ident ident : tactic

macro_rules
  | `(tactic| erase_four_step_cases $T0:ident $T1:ident $T2:ident) =>
      `(tactic|
        cases h0 : ($T0:ident).head with
        | none =>
            cases h1 : ($T1:ident).head with
            | none =>
                cases h2 : ($T2:ident).head with
                | none => three_tape_step [description, rows, rowsForRead,
                    s0, s1, s2, s3, halt, allReads3, allReads2,
                    allReadCells, List.find?, h0, h1, h2]
                | some b => cases b <;>
                    three_tape_step [description, rows, rowsForRead,
                      s0, s1, s2, s3, halt, allReads3, allReads2,
                      allReadCells, List.find?, h0, h1, h2]
            | some b1 => cases b1 <;>
                cases h2 : ($T2:ident).head with
                | none => three_tape_step [description, rows, rowsForRead,
                    s0, s1, s2, s3, halt, allReads3, allReads2,
                    allReadCells, List.find?, h0, h1, h2]
                | some b2 => cases b2 <;>
                    three_tape_step [description, rows, rowsForRead,
                      s0, s1, s2, s3, halt, allReads3, allReads2,
                      allReadCells, List.find?, h0, h1, h2]
        | some b0 => cases b0 <;>
            cases h1 : ($T1:ident).head with
            | none =>
                cases h2 : ($T2:ident).head with
                | none => three_tape_step [description, rows, rowsForRead,
                    s0, s1, s2, s3, halt, allReads3, allReads2,
                    allReadCells, List.find?, h0, h1, h2]
                | some b => cases b <;>
                    three_tape_step [description, rows, rowsForRead,
                      s0, s1, s2, s3, halt, allReads3, allReads2,
                      allReadCells, List.find?, h0, h1, h2]
            | some b1 => cases b1 <;>
                cases h2 : ($T2:ident).head with
                | none => three_tape_step [description, rows, rowsForRead,
                    s0, s1, s2, s3, halt, allReads3, allReads2,
                    allReadCells, List.find?, h0, h1, h2]
                | some b2 => cases b2 <;>
                    three_tape_step [description, rows, rowsForRead,
                      s0, s1, s2, s3, halt, allReads3, allReads2,
                      allReadCells, List.find?, h0, h1, h2])

theorem step0 (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config s0 T0 T1 T2) =
      config s1 T0 T1 (eraseR.apply T2) := by
  erase_four_step_cases T0 T1 T2
theorem step1 (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config s1 T0 T1 T2) =
      config s2 T0 T1 (eraseR.apply T2) := by
  erase_four_step_cases T0 T1 T2

theorem step2 (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config s2 T0 T1 T2) =
      config s3 T0 T1 (eraseR.apply T2) := by
  erase_four_step_cases T0 T1 T2

theorem step3 (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config s3 T0 T1 T2) =
      config halt T0 T1 (eraseR.apply T2) := by
  erase_four_step_cases T0 T1 T2
theorem run (T0 T1 T2 : Tape Bool) :
    description.runConfig 4 (config s0 T0 T1 T2) =
      config halt T0 T1 (Components.eraseRight 4 T2) := by
  rw [show 4 = 1 + (1 + (1 + 1)) by rfl]
  rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
  rw [step0]
  rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
  rw [step1]
  rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
  rw [step2, step3]
  rfl

end EraseFour

def eraseFourDescription : MachineDescription :=
  lowerStructured3Description EraseFour.description

theorem eraseFour_ready : EraseFour.description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool EraseFour.description
    (by decide)
theorem eraseFour_supports : SupportsReadWriteRows3 EraseFour.description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

theorem eraseFourDescription_ready : eraseFourDescription.SubroutineReady := by
  simpa [eraseFourDescription] using
    lowerStructured3Description_subroutineReady eraseFour_ready.left
      eraseFour_supports

theorem eraseFourDescription_realizes (T0 T2 : Tape Bool) :
    eraseFourDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 Tape.blank T2)
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (Components.eraseRight 4 T2)) := by
  simpa [eraseFourDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      eraseFour_ready.left eraseFour_ready.right eraseFour_supports
      (c := config EraseFour.s0 T0 Tape.blank T2)
      (tapes := [T0, Tape.blank, Components.eraseRight 4 T2])
      rfl rfl ⟨4, EraseFour.run T0 Tape.blank T2⟩
theorem wrappedBits_take_drop (bits : List Bool) (n : Nat) :
    List.append
        (AcceptConfigCopy.wrappedBits (bits.take n))
        (AcceptConfigCopy.wrappedBits (bits.drop n)) =
      AcceptConfigCopy.wrappedBits bits := by
  rw [← wrappedBits_append]
  exact congrArg AcceptConfigCopy.wrappedBits
    (List.take_append_drop n bits)

theorem atBoundaryTape0_eq_rewindSource (L : DovetailLayout) :
    atBoundaryTape0 L =
      scanTape
        (List.append
          ((AcceptConfigCopy.wrappedBits (ParsedLayoutBits L)).reverse.map
            some)
          (none :: primaryMarkerBaseLeft L))
        (rawBoundaryRest true L) := by
  rw [wrappedBits_parsed_eq_header_false_data]
  unfold atBoundaryTape0 commonEndpointLeft remainingBits
  rw [← wrappedBits_take_drop (dataBits L) (acceptCounterBits L).length]
  simp [List.reverse_append, List.map_append, List.append_assoc]

namespace CellStageGate

def invalid : Nat := 40
def halt : Nat := 41
def route : AcceptConfigCopy.Kind -> Nat
  | .zero => 0
  | .one => 0
  | .tick => halt
  | .done => halt
  | _ => invalid

def finalAction : AcceptConfigCopy.Kind ->
    CommonGround.FiniteTransducers.Structured.TapeAction
  | .tick => writeS (some false)
  | .done => writeS (some true)
  | _ => keepS

def description : CommonGround.FiniteTransducers.Structured.Description :=
  DirectTokenDriver.description 42 0 halt route
    keepS keepS keepS finalAction
theorem zero_run
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    description.runConfig 16
        (config 0
          (scanTape left (List.append (wrappedKind .zero) rest))
          Tape.blank T2) =
      config 0
        (scanTape
          (List.append ((wrappedKind .zero).reverse.map some) left) rest)
        Tape.blank T2 := by
  simpa [description, route, finalAction,
    DirectTokenDriver.applyOutputs,
    TapeAction.apply, TapeAction.stay, HeadMove.apply] using
    (DirectTokenDriver.zero_run 42 0 halt route
      keepS keepS keepS finalAction [] left rest T2)

theorem one_run
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    description.runConfig 16
        (config 0
          (scanTape left (List.append (wrappedKind .one) rest))
          Tape.blank T2) =
      config 0
        (scanTape
          (List.append ((wrappedKind .one).reverse.map some) left) rest)
        Tape.blank T2 := by
  simpa [description, route, finalAction,
    DirectTokenDriver.applyOutputs,
    TapeAction.apply, TapeAction.stay, HeadMove.apply] using
    (DirectTokenDriver.one_run 42 0 halt route
      keepS keepS keepS finalAction [] left rest T2)

theorem tick_run
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    description.runConfig 16
        (config 0
          (scanTape left (List.append (wrappedKind .tick) rest))
          Tape.blank T2) =
      config halt
        (scanTape
          (List.append ((wrappedKind .tick).reverse.map some) left) rest)
        Tape.blank (Components.markCurrent false T2) := by
  simpa [description, route, finalAction,
    DirectTokenDriver.applyOutputs,
    keepS, writeS, TapeAction.apply, TapeAction.stay, HeadMove.apply,
    Components.markCurrent] using
    (DirectTokenDriver.tick_run 42 0 halt route
      keepS keepS keepS finalAction [] left rest T2)
theorem done_run
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    description.runConfig 16
        (config 0
          (scanTape left (List.append (wrappedKind .done) rest))
          Tape.blank T2) =
      config halt
        (scanTape
          (List.append ((wrappedKind .done).reverse.map some) left) rest)
        Tape.blank (Components.markCurrent true T2) := by
  simpa [description, route, finalAction,
    DirectTokenDriver.applyOutputs,
    keepS, writeS, TapeAction.apply, TapeAction.stay, HeadMove.apply,
    Components.markCurrent] using
    (DirectTokenDriver.done_run 42 0 halt route
      keepS keepS keepS finalAction [] left rest T2)

theorem cells_run
    (bits : List Bool) (left : List (Option Bool))
    (rest : List Bool) (T2 : Tape Bool) :
    description.runConfig (Components.cellFuel bits)
        (config 0
          (scanTape left
            (List.append (Components.wrappedCellTokens bits) rest))
          Tape.blank T2) =
      config 0
        (scanTape
          (List.append
            ((Components.wrappedCellTokens bits).reverse.map some) left)
          rest)
        Tape.blank T2 := by
  induction bits generalizing left with
  | nil => rfl
  | cons bit bits ih =>
      cases bit with
      | false =>
          rw [show
            List.append (Components.wrappedCellTokens (false :: bits)) rest =
              List.append (wrappedKind .zero)
                (List.append (Components.wrappedCellTokens bits) rest) by
            simp [Components.wrappedCellTokens, List.append_assoc]]
          change description.runConfig (16 + Components.cellFuel bits) _ = _
          rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
          rw [zero_run]
          rw [ih]
          simp [Components.wrappedCellTokens, List.reverse_append,
            List.map_append, List.append_assoc]
      | true =>
          rw [show
            List.append (Components.wrappedCellTokens (true :: bits)) rest =
              List.append (wrappedKind .one)
                (List.append (Components.wrappedCellTokens bits) rest) by
            simp [Components.wrappedCellTokens, List.append_assoc]]
          change description.runConfig (16 + Components.cellFuel bits) _ = _
          rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
          rw [one_run]
          rw [ih]
          simp [Components.wrappedCellTokens, List.reverse_append,
            List.map_append, List.append_assoc]

theorem run_zero
    (bits : List Bool) (left : List (Option Bool))
    (rest : List Bool) (T2 : Tape Bool) :
    description.runConfig (Components.cellFuel bits + 16)
        (config 0
          (scanTape left
            (List.append (Components.wrappedCellTokens bits)
              (List.append (wrappedKind .done) rest)))
          Tape.blank T2) =
      config halt
        (scanTape
          (List.append
            ((List.append (Components.wrappedCellTokens bits)
              (wrappedKind .done)).reverse.map some)
            left)
          rest)
        Tape.blank (Components.markCurrent true T2) := by
  rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
  rw [cells_run, done_run]
  simp [List.reverse_append, List.map_append, List.append_assoc]
theorem run_succ
    (bits : List Bool) (stage : Nat)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    description.runConfig (Components.cellFuel bits + 16)
        (config 0
          (scanTape left
            (List.append (Components.wrappedCellTokens bits)
              (List.append (wrappedKind .tick)
                (List.append (Components.wrappedNatTokens stage) rest))))
          Tape.blank T2) =
      config halt
        (scanTape
          (List.append
            ((List.append (Components.wrappedCellTokens bits)
              (wrappedKind .tick)).reverse.map some)
            left)
          (List.append (Components.wrappedNatTokens stage) rest))
        Tape.blank (Components.markCurrent false T2) := by
  rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
  rw [cells_run, tick_run]
  simp [List.reverse_append, List.map_append, List.append_assoc]

end CellStageGate

def cellStageGateDescription : MachineDescription :=
  lowerStructured3Description CellStageGate.description

theorem cellStageGate_ready : CellStageGate.description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool
    CellStageGate.description (by decide)
theorem cellStageGate_supports :
    SupportsReadWriteRows3 CellStageGate.description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

theorem cellStageGateDescription_ready :
    cellStageGateDescription.SubroutineReady := by
  simpa [cellStageGateDescription] using
    lowerStructured3Description_subroutineReady cellStageGate_ready.left
      cellStageGate_supports

theorem cellStageGateDescription_realizes_zero
    (bits : List Bool) (left : List (Option Bool))
    (rest : List Bool) (T2 : Tape Bool) :
    cellStageGateDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (scanTape left
          (List.append (Components.wrappedCellTokens bits)
            (List.append (wrappedKind .done) rest)))
        Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (scanTape
          (List.append
            ((List.append (Components.wrappedCellTokens bits)
              (wrappedKind .done)).reverse.map some)
            left)
          rest)
        Tape.blank (Components.markCurrent true T2)) := by
  simpa [cellStageGateDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      cellStageGate_ready.left cellStageGate_ready.right
      cellStageGate_supports
      (c := config 0
        (scanTape left
          (List.append (Components.wrappedCellTokens bits)
            (List.append (wrappedKind .done) rest)))
        Tape.blank T2)
      (tapes :=
        [ scanTape
            (List.append
              ((List.append (Components.wrappedCellTokens bits)
                (wrappedKind .done)).reverse.map some)
              left)
            rest
        , Tape.blank
        , Components.markCurrent true T2 ])
      rfl rfl ⟨Components.cellFuel bits + 16,
        CellStageGate.run_zero bits left rest T2⟩
theorem cellStageGateDescription_realizes_succ
    (bits : List Bool) (stage : Nat)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    cellStageGateDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (scanTape left
          (List.append (Components.wrappedCellTokens bits)
            (List.append (wrappedKind .tick)
              (List.append (Components.wrappedNatTokens stage) rest))))
        Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (scanTape
          (List.append
            ((List.append (Components.wrappedCellTokens bits)
              (wrappedKind .tick)).reverse.map some)
            left)
          (List.append (Components.wrappedNatTokens stage) rest))
        Tape.blank (Components.markCurrent false T2)) := by
  simpa [cellStageGateDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      cellStageGate_ready.left cellStageGate_ready.right
      cellStageGate_supports
      (c := config 0
        (scanTape left
          (List.append (Components.wrappedCellTokens bits)
            (List.append (wrappedKind .tick)
              (List.append (Components.wrappedNatTokens stage) rest))))
        Tape.blank T2)
      (tapes :=
        [ scanTape
            (List.append
              ((List.append (Components.wrappedCellTokens bits)
                (wrappedKind .tick)).reverse.map some)
              left)
            (List.append (Components.wrappedNatTokens stage) rest)
        , Tape.blank
        , Components.markCurrent false T2 ])
      rfl rfl ⟨Components.cellFuel bits + 16,
        CellStageGate.run_succ bits stage left rest T2⟩

def configRest (L : DovetailLayout) : List Bool :=
  List.append (AcceptConfigCopy.wrappedBits (configHitBits L))
    (rawBoundaryRest true L)

def postPrefixLeft (L : DovetailLayout) : List (Option Bool) :=
  List.append
    ((List.append (wrappedKind .transition)
      (Components.wrappedNatTokens L.input.length)).reverse.map some)
    (none :: primaryMarkerBaseLeft L)
def afterFirstStageTape0 (L : DovetailLayout) : Tape Bool :=
  match L.stage with
  | 0 =>
      scanTape
        (List.append
          ((List.append (Components.wrappedCellTokens L.input)
            (wrappedKind .done)).reverse.map some)
          (postPrefixLeft L))
        (configRest L)
  | stage + 1 =>
      scanTape
        (List.append
          ((List.append (Components.wrappedCellTokens L.input)
            (wrappedKind .tick)).reverse.map some)
          (postPrefixLeft L))
        (List.append (Components.wrappedNatTokens stage) (configRest L))

def prefixGateCoreDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    MarkerAwareCommon.Lowered.prefixDescription
    cellStageGateDescription

theorem prefixGateCoreDescription_ready :
    prefixGateCoreDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    MarkerAwareCommon.Lowered.prefixDescription_ready
    cellStageGateDescription_ready
def prefixGateDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    MarkerAwareCommon.Lowered.armDescription
    prefixGateCoreDescription

theorem prefixGateDescription_ready :
    prefixGateDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    MarkerAwareCommon.Lowered.armDescription_ready
    prefixGateCoreDescription_ready

namespace StagePrefixFill

syntax "stage_prefix_step_cases" ident ident ident : tactic

macro_rules
  | `(tactic| stage_prefix_step_cases $T0:ident $T1:ident $T2:ident) =>
      `(tactic|
        cases h0 : ($T0:ident).head with
        | none =>
            cases h1 : ($T1:ident).head with
            | none =>
                cases h2 : ($T2:ident).head with
                | none => three_tape_step [description, rows, rowsForRead,
                    s0, s1, s2, s3, s4, s5, s6, halt,
                    allReads3, allReads2, allReadCells, List.find?,
                    h0, h1, h2]
                | some b => cases b <;>
                    three_tape_step [description, rows, rowsForRead,
                      s0, s1, s2, s3, s4, s5, s6, halt,
                      allReads3, allReads2, allReadCells, List.find?,
                      h0, h1, h2]
            | some b1 => cases b1 <;>
                cases h2 : ($T2:ident).head with
                | none => three_tape_step [description, rows, rowsForRead,
                    s0, s1, s2, s3, s4, s5, s6, halt,
                    allReads3, allReads2, allReadCells, List.find?,
                    h0, h1, h2]
                | some b2 => cases b2 <;>
                    three_tape_step [description, rows, rowsForRead,
                      s0, s1, s2, s3, s4, s5, s6, halt,
                      allReads3, allReads2, allReadCells, List.find?,
                      h0, h1, h2]
        | some b0 => cases b0 <;>
            cases h1 : ($T1:ident).head with
            | none =>
                cases h2 : ($T2:ident).head with
                | none => three_tape_step [description, rows, rowsForRead,
                    s0, s1, s2, s3, s4, s5, s6, halt,
                    allReads3, allReads2, allReadCells, List.find?,
                    h0, h1, h2]
                | some b => cases b <;>
                    three_tape_step [description, rows, rowsForRead,
                      s0, s1, s2, s3, s4, s5, s6, halt,
                      allReads3, allReads2, allReadCells, List.find?,
                      h0, h1, h2]
            | some b1 => cases b1 <;>
                cases h2 : ($T2:ident).head with
                | none => three_tape_step [description, rows, rowsForRead,
                    s0, s1, s2, s3, s4, s5, s6, halt,
                    allReads3, allReads2, allReadCells, List.find?,
                    h0, h1, h2]
                | some b2 => cases b2 <;>
                    three_tape_step [description, rows, rowsForRead,
                      s0, s1, s2, s3, s4, s5, s6, halt,
                      allReads3, allReads2, allReadCells, List.find?,
                      h0, h1, h2])

end StagePrefixFill

namespace StagePrefixForward

def start : Nat := 0
def tick1 : Nat := 1
def done1 : Nat := 2
def tick2 : Nat := 3
def done2 : Nat := 4
def tick3 : Nat := 5
def done3 : Nat := 6
def halt : Nat := 7
def rowsForTape2Read
    (source : Nat) (read2 : Option Bool)
    (action2 : CommonGround.FiniteTransducers.Structured.TapeAction)
    (target : Nat) :
    List CommonGround.FiniteTransducers.Structured.Transition :=
  allReads2 fun read0 read1 =>
    row source read0 read1 read2 keepS keepS action2 target

def rowsForAnyRead
    (source : Nat)
    (action2 : CommonGround.FiniteTransducers.Structured.TapeAction)
    (target : Nat) :
    List CommonGround.FiniteTransducers.Structured.Transition :=
  allReads3 fun read0 read1 read2 =>
    row source read0 read1 read2 keepS keepS action2 target

def rows : List CommonGround.FiniteTransducers.Structured.Transition :=
  [ rowsForTape2Read start (some false) (writeBitR false) tick1
  , rowsForTape2Read start (some true) (writeBitR false) done1
  , rowsForAnyRead tick1 (writeBitR false) tick2
  , rowsForAnyRead done1 (writeBitR false) done2
  , rowsForAnyRead tick2 (writeBitR true) tick3
  , rowsForAnyRead done2 (writeBitR true) done3
  , rowsForAnyRead tick3 (writeBitR false) halt
  , rowsForAnyRead done3 (writeBitR true) halt ].flatten
def description : CommonGround.FiniteTransducers.Structured.Description :=
  ThreeTape.description 8 start halt rows

def bits (last : Bool) : List Bool := [false, false, true, last]

syntax "stage_forward_step_cases" ident ident ident : tactic

macro_rules
  | `(tactic| stage_forward_step_cases $T0:ident $T1:ident $T2:ident) =>
      `(tactic|
        cases h0 : ($T0:ident).head with
        | none =>
            cases h1 : ($T1:ident).head with
            | none =>
                cases h2 : ($T2:ident).head with
                | none => three_tape_step [description, rows,
                    rowsForTape2Read, rowsForAnyRead,
                    start, tick1, done1, tick2, done2, tick3, done3, halt,
                    allReads3, allReads2, allReadCells, List.find?,
                    Components.markCurrent, writeWordRight, bits,
                    h0, h1, h2]
                | some b => cases b <;>
                    three_tape_step [description, rows,
                      rowsForTape2Read, rowsForAnyRead,
                      start, tick1, done1, tick2, done2, tick3, done3, halt,
                      allReads3, allReads2, allReadCells, List.find?,
                      Components.markCurrent, writeWordRight, bits,
                      h0, h1, h2]
            | some b1 => cases b1 <;>
                cases h2 : ($T2:ident).head with
                | none => three_tape_step [description, rows,
                    rowsForTape2Read, rowsForAnyRead,
                    start, tick1, done1, tick2, done2, tick3, done3, halt,
                    allReads3, allReads2, allReadCells, List.find?,
                    Components.markCurrent, writeWordRight, bits,
                    h0, h1, h2]
                | some b2 => cases b2 <;>
                    three_tape_step [description, rows,
                      rowsForTape2Read, rowsForAnyRead,
                      start, tick1, done1, tick2, done2, tick3, done3, halt,
                      allReads3, allReads2, allReadCells, List.find?,
                      Components.markCurrent, writeWordRight, bits,
                      h0, h1, h2]
        | some b0 => cases b0 <;>
            cases h1 : ($T1:ident).head with
            | none =>
                cases h2 : ($T2:ident).head with
                | none => three_tape_step [description, rows,
                    rowsForTape2Read, rowsForAnyRead,
                    start, tick1, done1, tick2, done2, tick3, done3, halt,
                    allReads3, allReads2, allReadCells, List.find?,
                    Components.markCurrent, writeWordRight, bits,
                    h0, h1, h2]
                | some b => cases b <;>
                    three_tape_step [description, rows,
                      rowsForTape2Read, rowsForAnyRead,
                      start, tick1, done1, tick2, done2, tick3, done3, halt,
                      allReads3, allReads2, allReadCells, List.find?,
                      Components.markCurrent, writeWordRight, bits,
                      h0, h1, h2]
            | some b1 => cases b1 <;>
                cases h2 : ($T2:ident).head with
                | none => three_tape_step [description, rows,
                    rowsForTape2Read, rowsForAnyRead,
                    start, tick1, done1, tick2, done2, tick3, done3, halt,
                    allReads3, allReads2, allReadCells, List.find?,
                    Components.markCurrent, writeWordRight, bits,
                    h0, h1, h2]
                | some b2 => cases b2 <;>
                    three_tape_step [description, rows,
                      rowsForTape2Read, rowsForAnyRead,
                      start, tick1, done1, tick2, done2, tick3, done3, halt,
                      allReads3, allReads2, allReadCells, List.find?,
                      Components.markCurrent, writeWordRight, bits,
                      h0, h1, h2])

theorem first_false (T0 T1 T2 : Tape Bool) :
    description.runConfig 1
        (config start T0 T1 (Components.markCurrent false T2)) =
      config tick1 T0 T1 ((writeBitR false).apply T2) := by
  stage_forward_step_cases T0 T1 T2
theorem first_true (T0 T1 T2 : Tape Bool) :
    description.runConfig 1
        (config start T0 T1 (Components.markCurrent true T2)) =
      config done1 T0 T1 ((writeBitR false).apply T2) := by
  stage_forward_step_cases T0 T1 T2

theorem tick_step1 (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config tick1 T0 T1 T2) =
      config tick2 T0 T1 ((writeBitR false).apply T2) := by
  stage_forward_step_cases T0 T1 T2

theorem done_step1 (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config done1 T0 T1 T2) =
      config done2 T0 T1 ((writeBitR false).apply T2) := by
  stage_forward_step_cases T0 T1 T2
theorem tick_step2 (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config tick2 T0 T1 T2) =
      config tick3 T0 T1 ((writeBitR true).apply T2) := by
  stage_forward_step_cases T0 T1 T2

theorem done_step2 (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config done2 T0 T1 T2) =
      config done3 T0 T1 ((writeBitR true).apply T2) := by
  stage_forward_step_cases T0 T1 T2

theorem tick_step3 (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config tick3 T0 T1 T2) =
      config halt T0 T1 ((writeBitR false).apply T2) := by
  stage_forward_step_cases T0 T1 T2
theorem done_step3 (T0 T1 T2 : Tape Bool) :
    description.runConfig 1 (config done3 T0 T1 T2) =
      config halt T0 T1 ((writeBitR true).apply T2) := by
  stage_forward_step_cases T0 T1 T2

theorem run (last : Bool) (T0 T1 T2 : Tape Bool) :
    description.runConfig 4
        (config start T0 T1 (Components.markCurrent last T2)) =
      config halt T0 T1 (writeWordRight (bits last) T2) := by
  cases last with
  | false =>
      rw [show 4 = 1 + (1 + (1 + 1)) by rfl]
      rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
      rw [first_false]
      rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
      rw [tick_step1]
      rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
      rw [tick_step2, tick_step3]
      rfl
  | true =>
      rw [show 4 = 1 + (1 + (1 + 1)) by rfl]
      rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
      rw [first_true]
      rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
      rw [done_step1]
      rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
      rw [done_step2, done_step3]
      rfl

end StagePrefixForward

def stagePrefixFillDescription : MachineDescription :=
  lowerStructured3Description StagePrefixForward.description
theorem stagePrefixFill_ready : StagePrefixForward.description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool
    StagePrefixForward.description (by decide)

theorem stagePrefixFill_supports :
    SupportsReadWriteRows3 StagePrefixForward.description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

theorem stagePrefixFillDescription_ready :
    stagePrefixFillDescription.SubroutineReady := by
  simpa [stagePrefixFillDescription] using
    lowerStructured3Description_subroutineReady stagePrefixFill_ready.left
      stagePrefixFill_supports
theorem stagePrefixFillDescription_realizes
    (last : Bool) (T0 T2 : Tape Bool) :
    stagePrefixFillDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (Components.markCurrent last T2))
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (writeWordRight (StagePrefixForward.bits last) T2)) := by
  simpa [stagePrefixFillDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      stagePrefixFill_ready.left stagePrefixFill_ready.right
      stagePrefixFill_supports
      (c := config StagePrefixForward.start T0 Tape.blank
        (Components.markCurrent last T2))
      (tapes :=
        [T0, Tape.blank, writeWordRight (StagePrefixForward.bits last) T2])
      rfl rfl ⟨4, StagePrefixForward.run last T0 Tape.blank T2⟩

def afterFirstStageLeft (L : DovetailLayout) : List (Option Bool) :=
  match L.stage with
  | 0 =>
      List.append
        ((List.append (Components.wrappedCellTokens L.input)
          (wrappedKind .done)).reverse.map some)
        (postPrefixLeft L)
  | _stage + 1 =>
      List.append
        ((List.append (Components.wrappedCellTokens L.input)
          (wrappedKind .tick)).reverse.map some)
        (postPrefixLeft L)

def remainingLiveBits (L : DovetailLayout) : List Bool :=
  match L.stage with
  | 0 => configHitBits L
  | stage + 1 =>
      List.append
        (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
          stage)
        (configHitBits L)
theorem afterFirstStageTape0_eq_copySource (L : DovetailLayout) :
    afterFirstStageTape0 L =
      scanTape (afterFirstStageLeft L)
        (List.append (AcceptConfigCopy.wrappedBits (remainingLiveBits L))
          (false :: false :: (rawBoundaryRest true L).drop 2)) := by
  have hraw := rawBoundaryRest_eq_false_false_drop L
  cases hstage : L.stage with
  | zero =>
      simp [afterFirstStageTape0, afterFirstStageLeft, remainingLiveBits,
        configRest, hstage, List.append_assoc]
      apply congrArg (scanTape _)
      exact congrArg
        (List.append (AcceptConfigCopy.wrappedBits (configHitBits L))) hraw
  | succ stage =>
      simp only [afterFirstStageTape0, afterFirstStageLeft,
        remainingLiveBits, hstage]
      rw [wrappedBits_append, wrappedBits_stageNatBits]
      simp [configRest, List.append_assoc]
      apply congrArg (scanTape _)
      exact congrArg (List.append (Components.wrappedNatTokens stage))
        (congrArg
          (List.append (AcceptConfigCopy.wrappedBits (configHitBits L))) hraw)

def stagePrefixDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription prefixGateDescription
    stagePrefixFillDescription

theorem stagePrefixDescription_ready :
    stagePrefixDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    prefixGateDescription_ready stagePrefixFillDescription_ready
theorem applyBits_write_eq_writeWordRight
    (bits : List Bool) (T : Tape Bool) :
    WrappedStream.applyBits (writeBitR false) (writeBitR true) bits T =
      writeWordRight bits T := by
  induction bits generalizing T with
  | nil => rfl
  | cons bit bits ih =>
      cases bit with
      | false =>
          change WrappedStream.applyBits (writeBitR false) (writeBitR true)
              bits ((writeBitR false).apply T) =
            writeWordRight bits
              (Tape.move Direction.right (Tape.write (some false) T))
          simpa [writeBitR, writeR, TapeAction.apply, HeadMove.apply] using
            ih ((writeBitR false).apply T)
      | true =>
          change WrappedStream.applyBits (writeBitR false) (writeBitR true)
              bits ((writeBitR true).apply T) =
            writeWordRight bits
              (Tape.move Direction.right (Tape.write (some true) T))
          simpa [writeBitR, writeR, TapeAction.apply, HeadMove.apply] using
            ih ((writeBitR true).apply T)

def liveCopyDescription : MachineDescription :=
  lowerStructured3Description
    (WrappedStream.description (writeBitR false) (writeBitR true))

theorem liveCopy_ready :
    (WrappedStream.description
      (writeBitR false) (writeBitR true)).SubroutineReady :=
  structuredDescription_subroutineReady_of_bool
    (WrappedStream.description (writeBitR false) (writeBitR true)) (by decide)
theorem liveCopy_supports :
    SupportsReadWriteRows3
      (WrappedStream.description (writeBitR false) (writeBitR true)) :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

theorem liveCopyDescription_ready : liveCopyDescription.SubroutineReady := by
  simpa [liveCopyDescription] using
    lowerStructured3Description_subroutineReady liveCopy_ready.left
      liveCopy_supports

theorem liveCopyDescription_realizes
    (bits : List Bool) (left : List (Option Bool))
    (boundaryRest : List Bool) (T2 : Tape Bool) :
    liveCopyDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (scanTape left
          (List.append (AcceptConfigCopy.wrappedBits bits)
            (false :: false :: boundaryRest)))
        Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (scanTape
          (List.append
            ((AcceptConfigCopy.wrappedBits bits).reverse.map some) left)
          (false :: false :: boundaryRest))
        Tape.blank (writeWordRight bits T2)) := by
  have hrun := WrappedStream.run
    (writeBitR false) (writeBitR true) bits left boundaryRest T2
  rw [applyBits_write_eq_writeWordRight] at hrun
  simpa [liveCopyDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      liveCopy_ready.left liveCopy_ready.right liveCopy_supports
      (c := config WrappedStream.loop
        (scanTape left
          (List.append (AcceptConfigCopy.wrappedBits bits)
            (false :: false :: boundaryRest)))
        Tape.blank T2)
      (tapes :=
        [ scanTape
            (List.append
              ((AcceptConfigCopy.wrappedBits bits).reverse.map some) left)
            (false :: false :: boundaryRest)
        , Tape.blank
        , writeWordRight bits T2 ])
      rfl rfl ⟨WrappedStream.fuel bits, hrun⟩
def afterLiveCopyTape0 (L : DovetailLayout) : Tape Bool :=
  scanTape
    (List.append
      ((AcceptConfigCopy.wrappedBits (remainingLiveBits L)).reverse.map some)
      (afterFirstStageLeft L))
    (false :: false :: (rawBoundaryRest true L).drop 2)

end AcceptBranch
end Route
end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
