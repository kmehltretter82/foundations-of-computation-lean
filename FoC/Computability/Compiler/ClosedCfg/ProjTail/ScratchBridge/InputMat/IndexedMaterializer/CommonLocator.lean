import FoC.Computability.Compiler.ClosedCfg.ProjTail.ScratchBridge.InputMat.IndexedMaterializer.Route

set_option doc.verso true

/-!
Marker-aware locator phases shared by the accepting and rejecting routes.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace FoC
namespace Computability

open Languages MachineDescription CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering

namespace EncRewriters
namespace BoundedLayoutRunner
namespace SelectedProjectionPaddedTailCleanup
namespace InputMat
namespace Route
namespace MarkerAwareCommon

open CanonicalLayouts.DovetailLayoutScanner CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape.CountWindowInputMat.DirectTokenDriver

namespace ArmPrimaryMarker

def start : Nat := 0
def mark : Nat := 1
def halt : Nat := 2

def rowsForRead
    (source : Nat) (read0 : Option Bool)
    (action0 : CommonGround.FiniteTransducers.Structured.TapeAction)
    (target : Nat) :
    List CommonGround.FiniteTransducers.Structured.Transition :=
  allReads2 fun read1 read2 =>
    row source read0 read1 read2 action0 keepS keepS target
def rows : List CommonGround.FiniteTransducers.Structured.Transition :=
  [ rowsForRead start (some false) keepL mark
  , rowsForRead mark (some true) (writeR none) halt ].flatten

def description : CommonGround.FiniteTransducers.Structured.Description :=
  ThreeTape.description 3 start halt rows

theorem run
    (left : List (Option Bool)) (rest : List Bool)
    (T1 T2 : Tape Bool) :
    description.runConfig 2
        (config start (scanTape (some true :: left) (false :: rest)) T1 T2) =
      config halt (scanTape (none :: left) (false :: rest)) T1 T2 := by
  cases h1 : T1.head with
  | none =>
      cases h2 : T2.head with
      | none =>
          three_tape_step [description, rows, rowsForRead, start, mark, halt,
            allReads2, allReadCells, List.find?, scanTape, tapeAtCells, h1, h2]
      | some b => cases b <;>
          three_tape_step [description, rows, rowsForRead, start, mark, halt,
            allReads2, allReadCells, List.find?, scanTape, tapeAtCells, h1, h2]
  | some b1 => cases b1 <;>
      cases h2 : T2.head with
      | none =>
          three_tape_step [description, rows, rowsForRead, start, mark, halt,
            allReads2, allReadCells, List.find?, scanTape, tapeAtCells, h1, h2]
      | some b2 => cases b2 <;>
          three_tape_step [description, rows, rowsForRead, start, mark, halt,
            allReads2, allReadCells, List.find?, scanTape, tapeAtCells, h1, h2]

end ArmPrimaryMarker

namespace RawStageScan
def bit0 : Nat := 0
def bit1 : Nat := 1
def bit2 : Nat := 2
def bit3 : Nat := 3
def halt : Nat := 4

def rowsForTape2Read
    (source : Nat) (read2 : Option Bool)
    (action2 : CommonGround.FiniteTransducers.Structured.TapeAction)
    (target : Nat) :
    List CommonGround.FiniteTransducers.Structured.Transition :=
  allReads2 fun read0 read1 =>
    row source read0 read1 read2 keepS keepS action2 target

def rows : List CommonGround.FiniteTransducers.Structured.Transition :=
  [ rowsForTape2Read bit0 (some false) keepR bit1
  , rowsForTape2Read bit1 (some false) keepR bit2
  , rowsForTape2Read bit2 (some true) keepR bit3
  , rowsForTape2Read bit3 (some false) keepR bit0
  , rowsForTape2Read bit3 (some true) keepR halt ].flatten
def description : CommonGround.FiniteTransducers.Structured.Description :=
  ThreeTape.description 5 bit0 halt rows

def stageBits : Nat -> List Bool
  | 0 => [false, false, true, true]
  | n + 1 => false :: false :: true :: false :: stageBits n

theorem stageBits_eq (stage : Nat) :
    stageBits stage =
      DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        stage := by
  induction stage with
  | zero => rfl
  | succ stage ih =>
      simp [stageBits,
        DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits_succ,
        ih]
def sourceTape
    (left : List (Option Bool)) (stage : Nat)
    (rest : List Bool) : Tape Bool :=
  scanTape left
    (List.append (stageBits stage) rest)

def targetTape
    (left : List (Option Bool)) (stage : Nat)
    (rest : List Bool) : Tape Bool :=
  scanTape
    (List.append
      ((stageBits stage).reverse.map some)
      left)
    rest

theorem tick_run
    (left : List (Option Bool)) (rest : List Bool)
    (T0 T1 : Tape Bool) :
    description.runConfig 4
        (config bit0 T0 T1
          (tapeAtCells left
            (some false :: some false :: some true :: some false ::
              List.append (rest.map some) [none]))) =
      config bit0 T0 T1
        (tapeAtCells
          ([some false, some true, some false, some false] ++ left)
          (List.append (rest.map some) [none])) := by
  cases rest <;>
    cases h0 : T0.head with
    | none =>
        cases h1 : T1.head with
        | none =>
            three_tape_step [description, rows, rowsForTape2Read,
              bit0, bit1, bit2, bit3, halt, allReads2, allReadCells,
              List.find?, tapeAtCells, h0, h1]
        | some b => cases b <;>
            three_tape_step [description, rows, rowsForTape2Read,
              bit0, bit1, bit2, bit3, halt, allReads2, allReadCells,
              List.find?, tapeAtCells, h0, h1]
    | some b0 => cases b0 <;>
        cases h1 : T1.head with
        | none =>
            three_tape_step [description, rows, rowsForTape2Read,
              bit0, bit1, bit2, bit3, halt, allReads2, allReadCells,
              List.find?, tapeAtCells, h0, h1]
        | some b1 => cases b1 <;>
            three_tape_step [description, rows, rowsForTape2Read,
              bit0, bit1, bit2, bit3, halt, allReads2, allReadCells,
              List.find?, tapeAtCells, h0, h1]
theorem done_run
    (left : List (Option Bool)) (rest : List Bool)
    (T0 T1 : Tape Bool) :
    description.runConfig 4
        (config bit0 T0 T1
          (tapeAtCells left
            (some false :: some false :: some true :: some true ::
              List.append (rest.map some) [none]))) =
      config halt T0 T1
        (tapeAtCells
          ([some true, some true, some false, some false] ++ left)
          (List.append (rest.map some) [none])) := by
  cases rest <;>
    cases h0 : T0.head with
    | none =>
        cases h1 : T1.head with
        | none =>
            three_tape_step [description, rows, rowsForTape2Read,
              bit0, bit1, bit2, bit3, halt, allReads2, allReadCells,
              List.find?, tapeAtCells, h0, h1]
        | some b => cases b <;>
            three_tape_step [description, rows, rowsForTape2Read,
              bit0, bit1, bit2, bit3, halt, allReads2, allReadCells,
              List.find?, tapeAtCells, h0, h1]
    | some b0 => cases b0 <;>
        cases h1 : T1.head with
        | none =>
            three_tape_step [description, rows, rowsForTape2Read,
              bit0, bit1, bit2, bit3, halt, allReads2, allReadCells,
              List.find?, tapeAtCells, h0, h1]
        | some b1 => cases b1 <;>
            three_tape_step [description, rows, rowsForTape2Read,
              bit0, bit1, bit2, bit3, halt, allReads2, allReadCells,
              List.find?, tapeAtCells, h0, h1]

def fuel (stage : Nat) : Nat := 4 * stage + 4

theorem run
    (stage : Nat) (left : List (Option Bool)) (rest : List Bool)
    (T0 T1 : Tape Bool) :
    description.runConfig (fuel stage)
        (config bit0 T0 T1 (sourceTape left stage rest)) =
      config halt T0 T1 (targetTape left stage rest) := by
  induction stage generalizing left with
  | zero =>
      simpa [fuel, sourceTape, targetTape, stageBits, scanTape,
        List.map_append]
        using done_run left rest T0 T1
  | succ stage ih =>
      rw [show fuel (stage + 1) = 4 + fuel stage by
        simp [fuel]
        lia]
      rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
      have htick :
          description.runConfig 4
              (config bit0 T0 T1 (sourceTape left (stage + 1) rest)) =
            config bit0 T0 T1
              (sourceTape
                ([some false, some true, some false, some false] ++ left)
                stage rest) := by
        simpa [sourceTape, stageBits, scanTape, List.map_append,
          List.append_assoc] using
          tick_run left (List.append (stageBits stage) rest) T0 T1
      rw [htick]
      rw [ih]
      simp [targetTape, scanTape, stageBits,
        List.reverse_cons, List.map_append, List.append_assoc]

end RawStageScan

namespace OneWrappedFalse
def start : Nat := 0
def second : Nat := 1
def payload : Nat := 2
def last : Nat := 3
def halt : Nat := 4

def rowsForRead
    (source : Nat) (read0 : Option Bool)
    (action0 : CommonGround.FiniteTransducers.Structured.TapeAction)
    (target : Nat) :
    List CommonGround.FiniteTransducers.Structured.Transition :=
  allReads2 fun read1 read2 =>
    row source read0 read1 read2 action0 keepS keepS target

def rows : List CommonGround.FiniteTransducers.Structured.Transition :=
  [ rowsForRead start (some false) keepR second
  , rowsForRead second (some true) keepR payload
  , rowsForRead payload (some false) keepR last
  , rowsForRead last (some true) keepR halt ].flatten
def description : CommonGround.FiniteTransducers.Structured.Description :=
  ThreeTape.description 5 start halt rows

theorem run
    (left : List (Option Bool)) (rest : List Bool)
    (T1 T2 : Tape Bool) :
    description.runConfig 4
        (config start
          (scanTape left (List.append (wrappedRawBit false) rest)) T1 T2) =
      config halt
        (scanTape
          (List.append ((wrappedRawBit false).reverse.map some) left) rest)
        T1 T2 := by
  cases rest <;>
    cases h1 : T1.head with
    | none =>
        cases h2 : T2.head with
        | none =>
            three_tape_step [description, rows, rowsForRead, start, second,
              payload, last, halt, allReads2, allReadCells, List.find?,
              scanTape, wrappedRawBit, cellsCodeBits, cellCodeBits,
              encodeCodeWordAsInput, encodeCodeSymbolAsInput, encodeCell,
              tapeAtCells, h1, h2]
        | some b => cases b <;>
            three_tape_step [description, rows, rowsForRead, start, second,
              payload, last, halt, allReads2, allReadCells, List.find?,
              scanTape, wrappedRawBit, cellsCodeBits, cellCodeBits,
              encodeCodeWordAsInput, encodeCodeSymbolAsInput, encodeCell,
              tapeAtCells, h1, h2]
    | some b1 => cases b1 <;>
        cases h2 : T2.head with
        | none =>
            three_tape_step [description, rows, rowsForRead, start, second,
              payload, last, halt, allReads2, allReadCells, List.find?,
              scanTape, wrappedRawBit, cellsCodeBits, cellCodeBits,
              encodeCodeWordAsInput, encodeCodeSymbolAsInput, encodeCell,
              tapeAtCells, h1, h2]
        | some b2 => cases b2 <;>
            three_tape_step [description, rows, rowsForRead, start, second,
              payload, last, halt, allReads2, allReadCells, List.find?,
              scanTape, wrappedRawBit, cellsCodeBits, cellCodeBits,
              encodeCodeWordAsInput, encodeCodeSymbolAsInput, encodeCell,
              tapeAtCells, h1, h2]

end OneWrappedFalse

namespace LocatorRuns

theorem token_run_bridge
    {D : CommonGround.FiniteTransducers.Structured.Description}
    {phase : AcceptConfigCopy.Phase} {kind : AcceptConfigCopy.Kind}
    (h : AcceptConfigCopy.TokenRun D phase kind)
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    D.runConfig 16
        (config (AcceptConfigCopy.tokenBase phase)
          (scanTape left (List.append (wrappedKind kind) rest))
          Tape.blank T2) =
      config (AcceptConfigCopy.route phase kind)
        (scanTape
          (List.append ((wrappedKind kind).reverse.map some) left) rest)
        Tape.blank T2 := by
  simpa [AcceptConfigCopy.TokenRun, AcceptConfigCopy.scanTape, scanTape,
    AcceptConfigCopy.wrappedKind, wrappedKind] using h left rest T2
theorem inputLength_run
    (n : Nat) (left : List (Option Bool)) (rest : List Bool)
    (T2 : Tape Bool) :
    AcceptConfigCopy.prefixDescription.runConfig (Components.natFuel n)
        (config (AcceptConfigCopy.tokenBase .inputLength)
          (scanTape left
            (List.append (Components.wrappedNatTokens n) rest))
          Tape.blank T2) =
      config (AcceptConfigCopy.tokenBase .inputCells)
        (scanTape
          (List.append
            ((Components.wrappedNatTokens n).reverse.map some) left)
          rest)
        Tape.blank T2 := by
  induction n generalizing left with
  | zero =>
      simpa [Components.natFuel, Components.wrappedNatTokens,
        AcceptConfigCopy.TokenRun, AcceptConfigCopy.route] using
        (token_run_bridge AcceptConfigCopy.inputLength_done_run
          left rest T2)
  | succ n ih =>
      rw [show
        List.append (Components.wrappedNatTokens (n + 1)) rest =
          List.append (wrappedKind .tick)
            (List.append (Components.wrappedNatTokens n) rest) by
        simp [Components.wrappedNatTokens, List.append_assoc]]
      change AcceptConfigCopy.prefixDescription.runConfig
        (16 + Components.natFuel n) _ = _
      rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
      rw [token_run_bridge AcceptConfigCopy.inputLength_tick_run left
        (List.append (Components.wrappedNatTokens n) rest) T2]
      simp only [AcceptConfigCopy.route]
      rw [ih]
      simp [Components.wrappedNatTokens, List.reverse_append,
        List.map_append, List.append_assoc]

theorem prefix_run
    (n : Nat) (left : List (Option Bool)) (rest : List Bool)
    (T2 : Tape Bool) :
    AcceptConfigCopy.prefixDescription.runConfig
        (16 + Components.natFuel n)
        (config (AcceptConfigCopy.tokenBase .layoutHeader)
          (scanTape left
            (List.append (wrappedKind .transition)
              (List.append (Components.wrappedNatTokens n) rest)))
          Tape.blank T2) =
      config (AcceptConfigCopy.tokenBase .inputCells)
        (scanTape
          (List.append
            ((List.append (wrappedKind .transition)
              (Components.wrappedNatTokens n)).reverse.map some)
            left)
          rest)
        Tape.blank T2 := by
  rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
  rw [token_run_bridge AcceptConfigCopy.header_token_run left
    (List.append (Components.wrappedNatTokens n) rest) T2]
  simp only [AcceptConfigCopy.route]
  rw [inputLength_run]
  simp [List.reverse_append, List.map_append, List.append_assoc]

theorem inputCells_run
    (bits : List Bool) (left : List (Option Bool))
    (rest : List Bool) (T2 : Tape Bool) :
    AcceptConfigCopy.cellsStageDescription.runConfig
        (Components.cellFuel bits)
        (config (AcceptConfigCopy.tokenBase .inputCells)
          (scanTape left
            (List.append (Components.wrappedCellTokens bits) rest))
          Tape.blank T2) =
      config (AcceptConfigCopy.tokenBase .inputCells)
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
          change AcceptConfigCopy.cellsStageDescription.runConfig
            (16 + Components.cellFuel bits) _ = _
          rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
          rw [token_run_bridge AcceptConfigCopy.inputCells_zero_run left
            (List.append (Components.wrappedCellTokens bits) rest) T2]
          simp only [AcceptConfigCopy.route]
          rw [ih]
          simp [Components.wrappedCellTokens, List.reverse_append,
            List.map_append, List.append_assoc]
      | true =>
          rw [show
            List.append (Components.wrappedCellTokens (true :: bits)) rest =
              List.append (wrappedKind .one)
                (List.append (Components.wrappedCellTokens bits) rest) by
            simp [Components.wrappedCellTokens, List.append_assoc]]
          change AcceptConfigCopy.cellsStageDescription.runConfig
            (16 + Components.cellFuel bits) _ = _
          rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
          rw [token_run_bridge AcceptConfigCopy.inputCells_one_run left
            (List.append (Components.wrappedCellTokens bits) rest) T2]
          simp only [AcceptConfigCopy.route]
          rw [ih]
          simp [Components.wrappedCellTokens, List.reverse_append,
            List.map_append, List.append_assoc]
theorem stage_run
    (n : Nat) (left : List (Option Bool)) (rest : List Bool)
    (T2 : Tape Bool) :
    AcceptConfigCopy.cellsStageDescription.runConfig (Components.natFuel n)
        (config (AcceptConfigCopy.tokenBase .stage)
          (scanTape left
            (List.append (Components.wrappedNatTokens n) rest))
          Tape.blank T2) =
      config (AcceptConfigCopy.tokenBase .initialize)
        (scanTape
          (List.append
            ((Components.wrappedNatTokens n).reverse.map some) left)
          rest)
        Tape.blank T2 := by
  induction n generalizing left with
  | zero =>
      simpa [Components.natFuel, Components.wrappedNatTokens,
        AcceptConfigCopy.TokenRun, AcceptConfigCopy.route] using
        (token_run_bridge AcceptConfigCopy.stage_done_run left rest T2)
  | succ n ih =>
      rw [show
        List.append (Components.wrappedNatTokens (n + 1)) rest =
          List.append (wrappedKind .tick)
            (List.append (Components.wrappedNatTokens n) rest) by
        simp [Components.wrappedNatTokens, List.append_assoc]]
      change AcceptConfigCopy.cellsStageDescription.runConfig
        (16 + Components.natFuel n) _ = _
      rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
      rw [token_run_bridge AcceptConfigCopy.stage_tick_run left
        (List.append (Components.wrappedNatTokens n) rest) T2]
      simp only [AcceptConfigCopy.route]
      rw [ih]
      simp [Components.wrappedNatTokens, List.reverse_append,
        List.map_append, List.append_assoc]

theorem stage_from_inputCells_run
    (n : Nat) (left : List (Option Bool)) (rest : List Bool)
    (T2 : Tape Bool) :
    AcceptConfigCopy.cellsStageDescription.runConfig (Components.natFuel n)
        (config (AcceptConfigCopy.tokenBase .inputCells)
          (scanTape left
            (List.append (Components.wrappedNatTokens n) rest))
          Tape.blank T2) =
      config (AcceptConfigCopy.tokenBase .initialize)
        (scanTape
          (List.append
            ((Components.wrappedNatTokens n).reverse.map some) left)
          rest)
        Tape.blank T2 := by
  cases n with
  | zero =>
      simpa [Components.natFuel, Components.wrappedNatTokens,
        AcceptConfigCopy.TokenRun, AcceptConfigCopy.route] using
        (token_run_bridge AcceptConfigCopy.inputCells_done_run
          left rest T2)
  | succ n =>
      rw [show
        List.append (Components.wrappedNatTokens (n + 1)) rest =
          List.append (wrappedKind .tick)
            (List.append (Components.wrappedNatTokens n) rest) by
        simp [Components.wrappedNatTokens, List.append_assoc]]
      change AcceptConfigCopy.cellsStageDescription.runConfig
        (16 + Components.natFuel n) _ = _
      rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
      rw [token_run_bridge AcceptConfigCopy.inputCells_tick_run left
        (List.append (Components.wrappedNatTokens n) rest) T2]
      simp only [AcceptConfigCopy.route]
      rw [stage_run]
      simp [Components.wrappedNatTokens, List.reverse_append,
        List.map_append, List.append_assoc]

theorem cells_stage_run
    (bits : List Bool) (stage : Nat)
    (left : List (Option Bool)) (rest : List Bool)
    (T2 : Tape Bool) :
    AcceptConfigCopy.cellsStageDescription.runConfig
        (Components.cellFuel bits + Components.natFuel stage)
        (config (AcceptConfigCopy.tokenBase .inputCells)
          (scanTape left
            (List.append (Components.wrappedCellTokens bits)
              (List.append (Components.wrappedNatTokens stage) rest)))
          Tape.blank T2) =
      config (AcceptConfigCopy.tokenBase .initialize)
        (scanTape
          (List.append
            ((List.append (Components.wrappedCellTokens bits)
              (Components.wrappedNatTokens stage)).reverse.map some)
            left)
          rest)
        Tape.blank T2 := by
  rw [CommonGround.FiniteTransducers.Structured.Description.runConfig_add]
  rw [inputCells_run]
  rw [stage_from_inputCells_run]
  simp [List.reverse_append, List.map_append, List.append_assoc]

end LocatorRuns

namespace Lowered
def armDescription : MachineDescription :=
  lowerStructured3Description ArmPrimaryMarker.description

def prefixDescription : MachineDescription :=
  lowerStructured3Description AcceptConfigCopy.prefixDescription

def cellsStageDescription : MachineDescription :=
  lowerStructured3Description AcceptConfigCopy.cellsStageDescription
def rawStageDescription : MachineDescription :=
  lowerStructured3Description RawStageScan.description

def rewindDescription : MachineDescription :=
  lowerStructured3Description PrimaryRewind.description

def oneFalseDescription : MachineDescription :=
  lowerStructured3Description OneWrappedFalse.description
theorem arm_ready : ArmPrimaryMarker.description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool
    ArmPrimaryMarker.description (by decide)

theorem arm_supports : SupportsReadWriteRows3 ArmPrimaryMarker.description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

theorem prefix_ready : AcceptConfigCopy.prefixDescription.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool
    AcceptConfigCopy.prefixDescription (by decide)
theorem prefix_supports :
    SupportsReadWriteRows3 AcceptConfigCopy.prefixDescription :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

theorem cellsStage_ready :
    AcceptConfigCopy.cellsStageDescription.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool
    AcceptConfigCopy.cellsStageDescription (by decide)

theorem cellsStage_supports :
    SupportsReadWriteRows3 AcceptConfigCopy.cellsStageDescription :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)
theorem rawStage_ready : RawStageScan.description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool
    RawStageScan.description (by decide)

theorem rawStage_supports : SupportsReadWriteRows3 RawStageScan.description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

theorem rewind_ready : PrimaryRewind.description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool
    PrimaryRewind.description (by decide)
theorem rewind_supports : SupportsReadWriteRows3 PrimaryRewind.description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)

theorem oneFalse_ready : OneWrappedFalse.description.SubroutineReady :=
  structuredDescription_subroutineReady_of_bool
    OneWrappedFalse.description (by decide)

theorem oneFalse_supports :
    SupportsReadWriteRows3 OneWrappedFalse.description :=
  supportedReadWriteRows3_of_supports_eq_true (by decide)
theorem armDescription_ready : armDescription.SubroutineReady := by
  simpa [armDescription] using
    lowerStructured3Description_subroutineReady arm_ready.left arm_supports

theorem prefixDescription_ready : prefixDescription.SubroutineReady := by
  simpa [prefixDescription] using
    lowerStructured3Description_subroutineReady prefix_ready.left
      prefix_supports

theorem cellsStageDescription_ready :
    cellsStageDescription.SubroutineReady := by
  simpa [cellsStageDescription] using
    lowerStructured3Description_subroutineReady cellsStage_ready.left
      cellsStage_supports
theorem rawStageDescription_ready : rawStageDescription.SubroutineReady := by
  simpa [rawStageDescription] using
    lowerStructured3Description_subroutineReady rawStage_ready.left
      rawStage_supports

theorem rewindDescription_ready : rewindDescription.SubroutineReady := by
  simpa [rewindDescription] using
    lowerStructured3Description_subroutineReady rewind_ready.left
      rewind_supports

theorem oneFalseDescription_ready : oneFalseDescription.SubroutineReady := by
  simpa [oneFalseDescription] using
    lowerStructured3Description_subroutineReady oneFalse_ready.left
      oneFalse_supports
theorem armDescription_realizes
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    armDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (scanTape (some true :: left) (false :: rest)) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (scanTape (none :: left) (false :: rest)) Tape.blank T2) := by
  simpa [armDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      arm_ready.left arm_ready.right arm_supports
      (c := config ArmPrimaryMarker.start
        (scanTape (some true :: left) (false :: rest)) Tape.blank T2)
      (tapes :=
        [scanTape (none :: left) (false :: rest), Tape.blank, T2])
      rfl rfl ⟨2, ArmPrimaryMarker.run left rest Tape.blank T2⟩

theorem prefixDescription_realizes
    (n : Nat) (left : List (Option Bool)) (rest : List Bool)
    (T2 : Tape Bool) :
    prefixDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (scanTape left
          (List.append (wrappedKind .transition)
            (List.append (Components.wrappedNatTokens n) rest)))
        Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (scanTape
          (List.append
            ((List.append (wrappedKind .transition)
              (Components.wrappedNatTokens n)).reverse.map some)
            left)
          rest)
        Tape.blank T2) := by
  simpa [prefixDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      prefix_ready.left prefix_ready.right prefix_supports
      (c := config (AcceptConfigCopy.tokenBase .layoutHeader)
        (scanTape left
          (List.append (wrappedKind .transition)
            (List.append (Components.wrappedNatTokens n) rest)))
        Tape.blank T2)
      (tapes :=
        [ scanTape
            (List.append
              ((List.append (wrappedKind .transition)
                (Components.wrappedNatTokens n)).reverse.map some)
              left)
            rest
        , Tape.blank
        , T2 ])
      rfl rfl ⟨16 + Components.natFuel n,
        LocatorRuns.prefix_run n left rest T2⟩

theorem cellsStageDescription_realizes
    (bits : List Bool) (stage : Nat)
    (left : List (Option Bool)) (rest : List Bool)
    (T2 : Tape Bool) :
    cellsStageDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (scanTape left
          (List.append (Components.wrappedCellTokens bits)
            (List.append (Components.wrappedNatTokens stage) rest)))
        Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (scanTape
          (List.append
            ((List.append (Components.wrappedCellTokens bits)
              (Components.wrappedNatTokens stage)).reverse.map some)
            left)
          rest)
        Tape.blank T2) := by
  simpa [cellsStageDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      cellsStage_ready.left cellsStage_ready.right cellsStage_supports
      (c := config (AcceptConfigCopy.tokenBase .inputCells)
        (scanTape left
          (List.append (Components.wrappedCellTokens bits)
            (List.append (Components.wrappedNatTokens stage) rest)))
        Tape.blank T2)
      (tapes :=
        [ scanTape
            (List.append
              ((List.append (Components.wrappedCellTokens bits)
                (Components.wrappedNatTokens stage)).reverse.map some)
              left)
            rest
        , Tape.blank
        , T2 ])
      rfl rfl ⟨Components.cellFuel bits + Components.natFuel stage,
        LocatorRuns.cells_stage_run bits stage left rest T2⟩
theorem rawStageDescription_realizes
    (stage : Nat) (left : List (Option Bool)) (rest : List Bool)
    (T0 : Tape Bool) :
    rawStageDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (RawStageScan.sourceTape left stage rest))
      (encodedGuardedStructured3Tapes T0 Tape.blank
        (RawStageScan.targetTape left stage rest)) := by
  simpa [rawStageDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      rawStage_ready.left rawStage_ready.right rawStage_supports
      (c := config RawStageScan.bit0 T0 Tape.blank
        (RawStageScan.sourceTape left stage rest))
      (tapes := [T0, Tape.blank, RawStageScan.targetTape left stage rest])
      rfl rfl ⟨RawStageScan.fuel stage,
        RawStageScan.run stage left rest T0 Tape.blank⟩

theorem rewindDescription_realizes
    (bits : List Bool) (left : List (Option Bool))
    (rest : List Bool) (T2 : Tape Bool) :
    rewindDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (scanTape
          (List.append
            ((AcceptConfigCopy.wrappedBits bits).reverse.map some)
            (none :: left))
          rest)
        Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (scanTape (some true :: left)
          (List.append (AcceptConfigCopy.wrappedBits bits) rest))
        Tape.blank T2) := by
  simpa [rewindDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      rewind_ready.left rewind_ready.right rewind_supports
      (c := config PrimaryRewind.loop
        (scanTape
          (List.append
            ((AcceptConfigCopy.wrappedBits bits).reverse.map some)
            (none :: left))
          rest)
        Tape.blank T2)
      (tapes :=
        [ scanTape (some true :: left)
            (List.append (AcceptConfigCopy.wrappedBits bits) rest)
        , Tape.blank
        , T2 ])
      rfl rfl ⟨PrimaryRewind.fuel bits,
        PrimaryRewind.run bits left rest Tape.blank T2⟩

theorem oneFalseDescription_realizes
    (left : List (Option Bool)) (rest : List Bool) (T2 : Tape Bool) :
    oneFalseDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (scanTape left (List.append (wrappedRawBit false) rest))
        Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (scanTape
          (List.append ((wrappedRawBit false).reverse.map some) left) rest)
        Tape.blank T2) := by
  simpa [oneFalseDescription, encodedGuardedStructured3Tapes] using
    lowerStructured3Description_haltsFromConfigWithTapes
      oneFalse_ready.left oneFalse_ready.right oneFalse_supports
      (c := config OneWrappedFalse.start
        (scanTape left (List.append (wrappedRawBit false) rest))
        Tape.blank T2)
      (tapes :=
        [ scanTape
            (List.append ((wrappedRawBit false).reverse.map some) left) rest
        , Tape.blank
        , T2 ])
      rfl rfl ⟨4, OneWrappedFalse.run left rest Tape.blank T2⟩

end Lowered
def primaryMarkerBaseLeft (L : DovetailLayout) : List (Option Bool) :=
  (positionTape0Left L).tail

theorem positionTape0Left_eq_marker_cons (L : DovetailLayout) :
    positionTape0Left L = some true :: primaryMarkerBaseLeft L := by
  rcases
      CanonicalLayouts.DovetailStagePrefix.stageNatBits_reverse_map_some_cons
        (ParsedLayoutBits L).length with
    ⟨tail, htail⟩
  simp [positionTape0Left, primaryMarkerBaseLeft, List.reverse_append,
    List.map_append, htail]

def rawBoundaryRest
    (useAccept : Bool) (L : DovetailLayout) : List Bool :=
  false ::
    countWindowPostFieldDecodedPrefixStructuredSuffixTail useAccept L
def markedPostPositionTape0
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  scanTape (none :: primaryMarkerBaseLeft L)
    (List.append (AcceptConfigCopy.wrappedBits (ParsedLayoutBits L))
      (rawBoundaryRest useAccept L))

def locatedConfigTape0
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  scanTape
    (List.append
      ((AcceptConfigCopy.wrappedBits (prefixThroughStageBits L)).reverse.map
        some)
      (none :: primaryMarkerBaseLeft L))
    (List.append (AcceptConfigCopy.wrappedBits (configHitBits L))
      (rawBoundaryRest useAccept L))

def counterBaseLeft (L : DovetailLayout) : List (Option Bool) :=
  List.append
    (List.replicate (ParsedLayoutBits L).length (none : Option Bool))
    [some true]
def afterStageTape2
    (outputRest : Word Bool) (L : DovetailLayout) : Tape Bool :=
  scanTape
    (List.append
      ((DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        L.stage).reverse.map some)
      (counterBaseLeft L))
    outputRest

def rewoundParsedTape0
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  scanTape (some true :: primaryMarkerBaseLeft L)
    (List.append (AcceptConfigCopy.wrappedBits (ParsedLayoutBits L))
      (rawBoundaryRest useAccept L))

def remarkedParsedTape0
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  scanTape (none :: primaryMarkerBaseLeft L)
    (List.append (AcceptConfigCopy.wrappedBits (ParsedLayoutBits L))
      (rawBoundaryRest useAccept L))
def dataBits (L : DovetailLayout) : List Bool :=
  List.append (boolWordFieldBits L.input []).tail
    (List.append
      (DovetailInitialLayoutInitializer.StageInputMarkedScanner.stageNatBits
        L.stage)
      (configHitBits L))

theorem parsedLayoutBits_eq_transition_false_data (L : DovetailLayout) :
    ParsedLayoutBits L =
      List.append transitionPrefixBits (false :: dataBits L) := by
  rcases cellListFieldBits_cons_false (L.input.map some) [] with
    ⟨tail, htail⟩
  have hword : boolWordFieldBits L.input [] = false :: tail := by
    exact htail
  have hwordTail : (boolWordFieldBits L.input []).tail = tail := by
    simp [hword]
  rw [parsedLayoutBits_eq_prefix_configHit]
  simp [prefixThroughStageBits, dataBits, hword, hwordTail,
    List.append_assoc]

theorem wrappedBits_parsed_eq_header_false_data (L : DovetailLayout) :
    AcceptConfigCopy.wrappedBits (ParsedLayoutBits L) =
      List.append (wrappedKind .transition)
        (List.append (wrappedRawBit false)
          (AcceptConfigCopy.wrappedBits (dataBits L))) := by
  rw [parsedLayoutBits_eq_transition_false_data, wrappedBits_append]
  rw [wrappedBits_transitionPrefixBits]
  simp [AcceptConfigCopy.wrappedBits, AcceptConfigCopy.wrappedBit,
    List.append_assoc]
def commonEndpointLeft (L : DovetailLayout) : List (Option Bool) :=
  List.append
    ((List.append (wrappedKind .transition)
      (wrappedRawBit false)).reverse.map some)
    (none :: primaryMarkerBaseLeft L)

def commonEndpointTape0
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  scanTape (commonEndpointLeft L)
    (List.append (AcceptConfigCopy.wrappedBits (dataBits L))
      (rawBoundaryRest useAccept L))

theorem postPositionTape0_eq_unmarked_shape
    (useAccept : Bool) (L : DovetailLayout) :
    postPositionTape0 useAccept L =
      scanTape (some true :: primaryMarkerBaseLeft L)
        (List.append (AcceptConfigCopy.wrappedBits (ParsedLayoutBits L))
          (rawBoundaryRest useAccept L)) := by
  rw [postPositionTape0_eq_scanTape, positionTape0Left_eq_marker_cons]
  rfl
theorem postPositionTape2_eq_stage_source
    (outputRest : Word Bool) (L : DovetailLayout) :
    postPositionTape2 outputRest L =
      RawStageScan.sourceTape (counterBaseLeft L) L.stage outputRest := by
  simp [postPositionTape2, counterBaseLeft, RawStageScan.sourceTape,
    RawStageScan.stageBits_eq, scanTape, AcceptConfigInserter.scanTape,
    List.map_append,
    List.append_assoc]

theorem afterStageTape2_eq_stage_target
    (outputRest : Word Bool) (L : DovetailLayout) :
    afterStageTape2 outputRest L =
      RawStageScan.targetTape (counterBaseLeft L) L.stage outputRest := by
  simp [afterStageTape2, counterBaseLeft, RawStageScan.targetTape,
    RawStageScan.stageBits_eq]

def locateDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    Lowered.prefixDescription Lowered.cellsStageDescription
theorem locateDescription_ready : locateDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    Lowered.prefixDescription_ready Lowered.cellsStageDescription_ready

theorem locateDescription_realizes
    (useAccept : Bool) (L : DovetailLayout) (T2 : Tape Bool) :
    locateDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (markedPostPositionTape0 useAccept L) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (locatedConfigTape0 useAccept L) Tape.blank T2) := by
  let configRest : List Bool :=
    List.append (AcceptConfigCopy.wrappedBits (configHitBits L))
      (rawBoundaryRest useAccept L)
  let cellsRest : List Bool :=
    List.append (Components.wrappedCellTokens L.input)
      (List.append (Components.wrappedNatTokens L.stage) configRest)
  let prefixLeft : List (Option Bool) :=
    List.append
      ((List.append (wrappedKind .transition)
        (Components.wrappedNatTokens L.input.length)).reverse.map some)
      (none :: primaryMarkerBaseLeft L)
  have hp := Lowered.prefixDescription_realizes L.input.length
    (none :: primaryMarkerBaseLeft L) cellsRest T2
  have hc := Lowered.cellsStageDescription_realizes L.input L.stage
    prefixLeft configRest T2
  have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    Lowered.prefixDescription_ready Lowered.cellsStageDescription_ready
    hp hc
  simpa [locateDescription, markedPostPositionTape0, locatedConfigTape0,
    configRest, cellsRest, prefixLeft, wrappedBits_parsedLayoutBits,
    wrappedBits_prefixThroughStage, List.reverse_append, List.map_append,
    List.append_assoc] using h

theorem wrappedParsedBoundary_eq_false_cons_tail
    (useAccept : Bool) (L : DovetailLayout) :
    List.append (AcceptConfigCopy.wrappedBits (ParsedLayoutBits L))
        (rawBoundaryRest useAccept L) =
      false ::
        (List.append (AcceptConfigCopy.wrappedBits (ParsedLayoutBits L))
          (rawBoundaryRest useAccept L)).tail := by
  rw [wrappedBits_parsed_eq_header_false_data]
  rfl
theorem armPostPosition_realizes
    (useAccept : Bool) (L : DovetailLayout) (T2 : Tape Bool) :
    Lowered.armDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (postPositionTape0 useAccept L) Tape.blank T2)
      (encodedGuardedStructured3Tapes
        (markedPostPositionTape0 useAccept L) Tape.blank T2) := by
  rw [postPositionTape0_eq_unmarked_shape]
  rw [wrappedParsedBoundary_eq_false_cons_tail]
  unfold markedPostPositionTape0
  rw [wrappedParsedBoundary_eq_false_cons_tail]
  exact Lowered.armDescription_realizes
    (primaryMarkerBaseLeft L)
    (List.append
      (AcceptConfigCopy.wrappedBits (ParsedLayoutBits L))
      (rawBoundaryRest useAccept L)).tail
    T2

theorem rawStageAtLocated_realizes
    (useAccept : Bool) (outputRest : Word Bool) (L : DovetailLayout) :
    Lowered.rawStageDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (locatedConfigTape0 useAccept L) Tape.blank
        (postPositionTape2 outputRest L))
      (encodedGuardedStructured3Tapes
        (locatedConfigTape0 useAccept L) Tape.blank
        (afterStageTape2 outputRest L)) := by
  rw [postPositionTape2_eq_stage_source,
    afterStageTape2_eq_stage_target]
  exact Lowered.rawStageDescription_realizes L.stage
    (counterBaseLeft L) outputRest (locatedConfigTape0 useAccept L)

def armLocateDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription Lowered.armDescription locateDescription
theorem armLocateDescription_ready :
    armLocateDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    Lowered.armDescription_ready locateDescription_ready

def armLocateStageDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    armLocateDescription Lowered.rawStageDescription

theorem armLocateStageDescription_ready :
    armLocateStageDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    armLocateDescription_ready Lowered.rawStageDescription_ready
theorem armLocateStageDescription_realizes
    (useAccept : Bool) (outputRest : Word Bool) (L : DovetailLayout) :
    armLocateStageDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (postPositionTape0 useAccept L) Tape.blank
        (postPositionTape2 outputRest L))
      (encodedGuardedStructured3Tapes
        (locatedConfigTape0 useAccept L) Tape.blank
        (afterStageTape2 outputRest L)) := by
  have ha := armPostPosition_realizes useAccept L
    (postPositionTape2 outputRest L)
  have hl := locateDescription_realizes useAccept L
    (postPositionTape2 outputRest L)
  have hal := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    Lowered.armDescription_ready locateDescription_ready ha hl
  have hs := rawStageAtLocated_realizes useAccept outputRest L
  have hall := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    armLocateDescription_ready Lowered.rawStageDescription_ready hal hs
  simpa [armLocateStageDescription, armLocateDescription] using hall

theorem rewindAtLocated_realizes
    (useAccept : Bool) (outputRest : Word Bool) (L : DovetailLayout) :
    Lowered.rewindDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (locatedConfigTape0 useAccept L) Tape.blank
        (afterStageTape2 outputRest L))
      (encodedGuardedStructured3Tapes
        (rewoundParsedTape0 useAccept L) Tape.blank
        (afterStageTape2 outputRest L)) := by
  unfold locatedConfigTape0 rewoundParsedTape0
  rw [parsedLayoutBits_eq_prefix_configHit, wrappedBits_append]
  simpa [List.append_assoc] using
    Lowered.rewindDescription_realizes
      (prefixThroughStageBits L) (primaryMarkerBaseLeft L)
      (List.append (AcceptConfigCopy.wrappedBits (configHitBits L))
        (rawBoundaryRest useAccept L))
      (afterStageTape2 outputRest L)

theorem remarkAtRewound_realizes
    (useAccept : Bool) (outputRest : Word Bool) (L : DovetailLayout) :
    Lowered.armDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (rewoundParsedTape0 useAccept L) Tape.blank
        (afterStageTape2 outputRest L))
      (encodedGuardedStructured3Tapes
        (remarkedParsedTape0 useAccept L) Tape.blank
        (afterStageTape2 outputRest L)) := by
  unfold rewoundParsedTape0 remarkedParsedTape0
  rw [wrappedParsedBoundary_eq_false_cons_tail]
  rw [wrappedParsedBoundary_eq_false_cons_tail]
  exact Lowered.armDescription_realizes
    (primaryMarkerBaseLeft L)
    (List.append
      (AcceptConfigCopy.wrappedBits (ParsedLayoutBits L))
      (rawBoundaryRest useAccept L)).tail
    (afterStageTape2 outputRest L)
def afterHeaderTape0
    (useAccept : Bool) (L : DovetailLayout) : Tape Bool :=
  scanTape
    (List.append ((wrappedKind .transition).reverse.map some)
      (none :: primaryMarkerBaseLeft L))
    (List.append (wrappedRawBit false)
      (List.append (AcceptConfigCopy.wrappedBits (dataBits L))
        (rawBoundaryRest useAccept L)))

theorem headerAtRemarked_realizes
    (useAccept : Bool) (outputRest : Word Bool) (L : DovetailLayout) :
    loweredHeaderDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (remarkedParsedTape0 useAccept L) Tape.blank
        (afterStageTape2 outputRest L))
      (encodedGuardedStructured3Tapes
        (afterHeaderTape0 useAccept L) Tape.blank
        (afterStageTape2 outputRest L)) := by
  simpa [remarkedParsedTape0, afterHeaderTape0,
    wrappedBits_parsed_eq_header_false_data, List.append_assoc] using
    loweredHeaderDescription_realizes
      (none :: primaryMarkerBaseLeft L)
      (List.append (wrappedRawBit false)
        (List.append (AcceptConfigCopy.wrappedBits (dataBits L))
          (rawBoundaryRest useAccept L)))
      (afterStageTape2 outputRest L)

theorem oneFalseAtHeader_realizes
    (useAccept : Bool) (outputRest : Word Bool) (L : DovetailLayout) :
    Lowered.oneFalseDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (afterHeaderTape0 useAccept L) Tape.blank
        (afterStageTape2 outputRest L))
      (encodedGuardedStructured3Tapes
        (commonEndpointTape0 useAccept L) Tape.blank
        (afterStageTape2 outputRest L)) := by
  simpa [afterHeaderTape0, commonEndpointTape0, commonEndpointLeft,
    List.reverse_append, List.map_append, List.append_assoc] using
    Lowered.oneFalseDescription_realizes
      (List.append ((wrappedKind .transition).reverse.map some)
        (none :: primaryMarkerBaseLeft L))
      (List.append (AcceptConfigCopy.wrappedBits (dataBits L))
        (rawBoundaryRest useAccept L))
      (afterStageTape2 outputRest L)
def rewindRemarkDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    Lowered.rewindDescription Lowered.armDescription

theorem rewindRemarkDescription_ready :
    rewindRemarkDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    Lowered.rewindDescription_ready Lowered.armDescription_ready

def headerOneDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    loweredHeaderDescription Lowered.oneFalseDescription
theorem headerOneDescription_ready : headerOneDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    loweredHeaderDescription_subroutineReady Lowered.oneFalseDescription_ready

def commonTailDescription : MachineDescription :=
  canonicalPrimitiveSeqDescription
    rewindRemarkDescription headerOneDescription

theorem commonTailDescription_ready : commonTailDescription.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    rewindRemarkDescription_ready headerOneDescription_ready
def description : MachineDescription :=
  canonicalPrimitiveSeqDescription armLocateStageDescription
    commonTailDescription

theorem description_ready : description.SubroutineReady := by
  exact canonicalPrimitiveSeqDescription_subroutineReady
    armLocateStageDescription_ready commonTailDescription_ready

theorem commonTailDescription_realizes
    (useAccept : Bool) (outputRest : Word Bool) (L : DovetailLayout) :
    commonTailDescription.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (locatedConfigTape0 useAccept L) Tape.blank
        (afterStageTape2 outputRest L))
      (encodedGuardedStructured3Tapes
        (commonEndpointTape0 useAccept L) Tape.blank
        (afterStageTape2 outputRest L)) := by
  have hr := rewindAtLocated_realizes useAccept outputRest L
  have hm := remarkAtRewound_realizes useAccept outputRest L
  have hrm := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    Lowered.rewindDescription_ready Lowered.armDescription_ready hr hm
  have hh := headerAtRemarked_realizes useAccept outputRest L
  have ho := oneFalseAtHeader_realizes useAccept outputRest L
  have hho := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    loweredHeaderDescription_subroutineReady Lowered.oneFalseDescription_ready
    hh ho
  have hall := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    rewindRemarkDescription_ready headerOneDescription_ready hrm hho
  simpa [commonTailDescription, rewindRemarkDescription,
    headerOneDescription] using hall
theorem realizes
    (useAccept : Bool) (outputRest : Word Bool) (L : DovetailLayout) :
    description.HaltsFromTapeEquiv
      (encodedGuardedStructured3Tapes
        (postPositionTape0 useAccept L) Tape.blank
        (postPositionTape2 outputRest L))
      (encodedGuardedStructured3Tapes
        (commonEndpointTape0 useAccept L) Tape.blank
        (afterStageTape2 outputRest L)) := by
  have hp := armLocateStageDescription_realizes useAccept outputRest L
  have ht := commonTailDescription_realizes useAccept outputRest L
  have h := canonicalPrimitiveSeqDescription_haltsFromTapeEquiv
    armLocateStageDescription_ready commonTailDescription_ready hp ht
  simpa [description] using h

end MarkerAwareCommon
end Route
end InputMat
end SelectedProjectionPaddedTailCleanup
end BoundedLayoutRunner
end EncRewriters

end Computability
end FoC
