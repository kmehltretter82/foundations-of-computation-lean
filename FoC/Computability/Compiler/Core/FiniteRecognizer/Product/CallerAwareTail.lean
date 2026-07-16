import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.CallerTail
import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.Materializer

set_option doc.verso true

/-!
# Caller-aware product tail continuation

Exact continuation of the nonempty product caller-tail endpoint through the
unchanged left stage-input materializer. The raw-tail loop carries arbitrary
caller data as a literal suffix while allowing only far-edge blank padding to
vary by tape equivalence.
-/

namespace FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe

open Languages

namespace ProductCallerAwareTail

open InitialMaterializer

def callerCells (callerData : Word MachineCodeSymbol) :
    List (Option MachineCodeSymbol) :=
  match callerData with
  | [] => [none]
  | _ :: _ => callerData.map some

def baseStartConfig {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (leftRev restRev callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (FullMaterializerMachine.Control M) where
  state := .baseRewind headSymbol .start
  tape :=
    { left := some Frame.callerTag :: some MachineCodeSymbol.done :: none ::
        List.append (restRev.map some) (none :: leftRev.map some)
      head := callerData.head?
      right := callerData.tail.map some }

def baseGateConfig {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (leftRev restRev callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (FullMaterializerMachine.Control M) where
  state := .baseRewind headSymbol .gate
  tape :=
    { left := none :: List.append (restRev.map some) (none :: leftRev.map some)
      head := some MachineCodeSymbol.done
      right := some Frame.callerTag :: callerCells callerData }

def rawGateConfig {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (remainingRev fuelRev callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol (FullMaterializerMachine.Control M) where
  state := .raw headSymbol (RawTailLoopMachine.Control.loop
    (.rewind .gate))
  tape :=
    { left := none :: List.append (remainingRev.map some) (none :: fuelRev.map some)
      head := some MachineCodeSymbol.done
      right := some Frame.callerTag :: callerCells callerData }

theorem tail_base_bridge_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (leftRev restRev callerData : Word MachineCodeSymbol) :
    (FullMaterializerMachine.machine M).runConfigExact? 2
        (FullMaterializerMachine.tailConfig M
          (ProductCallerTail.NonemptyCallerTail.haltConfig
            headSymbol leftRev restRev callerData)) =
      some (baseStartConfig M headSymbol leftRev restRev callerData) := by
  cases leftRev <;> cases restRev <;> cases callerData <;>
    simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
      FullMaterializerMachine.machine, FullMaterializerMachine.transition,
      FullMaterializerMachine.tailConfig, ProductCallerTail.NonemptyCallerTail.haltConfig,
      ProductCallerTail.NonemptyCallerTail.haltTape,
      ProductCallerTail.NonemptyCallerTail.writeCallerTape,
      baseStartConfig, Tape.read, Tape.write, Tape.move,
      Tape.moveLeft, Tape.moveRight]

theorem base_rewind_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (leftRev restRev callerData : Word MachineCodeSymbol) :
    (FullMaterializerMachine.machine M).runConfigExact? 4
        (baseStartConfig M headSymbol leftRev restRev callerData) =
      some (baseGateConfig M headSymbol leftRev restRev callerData) := by
  cases leftRev <;> cases restRev <;> cases callerData <;>
    simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
      FullMaterializerMachine.machine, FullMaterializerMachine.transition,
      SeparatorRewind.transition, baseStartConfig, baseGateConfig, callerCells,
      Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight]

theorem base_raw_bridge_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (remainingRev fuelRev callerData : Word MachineCodeSymbol) :
    (FullMaterializerMachine.machine M).runConfigExact? 2
        (baseGateConfig M headSymbol fuelRev remainingRev callerData) =
      some (rawGateConfig M headSymbol remainingRev fuelRev callerData) := by
  rfl

def regionWithCaller (processed callerData : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  List.append (NonemptyRightRegion.region processed) callerData

namespace ContextualRightCellPrep

def sourceConfig (deeperLeft : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol) (processed callerData : Word MachineCodeSymbol) :=
  RightCellPrep.sourceConfig deeperLeft current
    (regionWithCaller processed callerData)

def gateConfig (deeperLeft : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol) (processed callerData : Word MachineCodeSymbol) :=
  RightCellPrep.gateConfig current
    (List.append
      ((MachineDescription.encodeNat processed.length).reverse.map some)
      (some MachineCodeSymbol.tick :: none :: deeperLeft))
    (List.append (RightCellPrep.payload processed) callerData)

theorem run_exact (deeperLeft : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol) (processed callerData : Word MachineCodeSymbol) :
    RightCellPrep.machine.runConfigExact? (processed.length + 5)
        (sourceConfig deeperLeft current processed callerData) =
      some (gateConfig deeperLeft current processed callerData) := by
  have hnonempty : regionWithCaller processed callerData ≠ [] := by
    intro hnil
    have hparts := List.append_eq_nil_iff.mp hnil
    exact NonemptyRightRegion.region_ne_nil processed hparts.1
  cases hregion : regionWithCaller processed callerData with
  | nil => contradiction
  | cons first regionRest =>
      rw [show processed.length + 5 = 4 + (processed.length + 1) by lia]
      rw [InitialMaterializer.ExactRun.append]
      unfold sourceConfig
      rw [hregion]
      rw [RightCellPrep.prefix_run_exact_of_cons]
      simp only
      have hshape :
          regionWithCaller processed callerData =
            MachineDescription.encodeNatAppend processed.length
              (List.append (RightCellPrep.payload processed) callerData) := by
        rw [regionWithCaller, RightCellPrep.region_eq_count_payload]
        simp [MachineDescription.encodeNatAppend, List.append_assoc]
      rw [hregion] at hshape
      rw [hshape]
      exact RightCellPrep.locate_run_exact current processed.length
        (some MachineCodeSymbol.tick :: none :: deeperLeft)
        (List.append (RightCellPrep.payload processed) callerData)

end ContextualRightCellPrep

namespace ContextualOneCell

def baseCells (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol)) :=
  InitialMaterializer.RightCellInsert.baseCells processed deeperLeft

def payload (processed callerData : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  List.append (RightCellPrep.payload processed) callerData

def sourceConfig (current : MachineCodeSymbol)
    (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :=
  OneCellMachine.prepConfig
    (ContextualRightCellPrep.sourceConfig deeperLeft current processed callerData)

def prepEndpointConfig (current : MachineCodeSymbol)
    (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :=
  OneCellMachine.prepConfig
    (ContextualRightCellPrep.gateConfig deeperLeft current processed callerData)

def insertionSourceConfig (current : MachineCodeSymbol)
    (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :=
  OneCellMachine.insertConfig current
    (BoundedBlockInsert.config (BoundedBlockInsert.cellBuffer current) []
      (baseCells processed deeperLeft) (payload processed callerData))

def insertionEndpointConfig (current : MachineCodeSymbol)
    (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :=
  OneCellMachine.insertConfig current
    (BoundedBlockInsert.haltConfig
      (BoundedBlockInsert.finalLeftRev (BoundedBlockInsert.cellBuffer current) []
        (payload processed callerData))
      (baseCells processed deeperLeft))

def endpointConfig (current : MachineCodeSymbol)
    (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :=
  OneCellMachine.rewindConfig
    (SeparatorRewind.gateConfigCells deeperLeft
      (regionWithCaller (current :: processed) callerData))

theorem prep_run_exact (current : MachineCodeSymbol)
    (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    OneCellMachine.machine.runConfigExact? (processed.length + 5)
        (sourceConfig current processed deeperLeft callerData) =
      some (prepEndpointConfig current processed deeperLeft callerData) := by
  exact OneCellMachine.prep_run_of_eq_some _ _ _
    (ContextualRightCellPrep.run_exact deeperLeft current processed callerData)

theorem payload_ne_nil (processed callerData : Word MachineCodeSymbol) :
    payload processed callerData ≠ [] := by
  intro hnil
  have hparts := List.append_eq_nil_iff.mp hnil
  exact OneCellMachine.payload_ne_nil processed hparts.1

theorem bridge_run_exact (current : MachineCodeSymbol)
    (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    OneCellMachine.machine.runConfigExact? 2
        (prepEndpointConfig current processed deeperLeft callerData) =
      some (insertionSourceConfig current processed deeperLeft callerData) := by
  have hnonempty := payload_ne_nil processed callerData
  cases hpayload : List.append (RightCellPrep.payload processed) callerData with
  | nil => contradiction
  | cons first payloadRest =>
      unfold prepEndpointConfig insertionSourceConfig
      unfold ContextualRightCellPrep.gateConfig
      unfold baseCells payload
      have hbase :
          List.append
              ((MachineDescription.encodeNat processed.length).reverse.map some)
              (some MachineCodeSymbol.tick :: none :: deeperLeft) =
            some MachineCodeSymbol.done ::
              OneCellMachine.bridgeLeftCells processed deeperLeft := by
        simpa [InitialMaterializer.RightCellInsert.baseCells] using
          OneCellMachine.baseCells_eq_done_cons processed deeperLeft
      rw [hbase]
      rw [OneCellMachine.baseCells_eq_done_cons]
      rw [hpayload]
      change OneCellMachine.machine.runConfigExact? (1 + 1)
        (OneCellMachine.prepConfig
          (RightCellPrep.gateConfig current
            (some MachineCodeSymbol.done ::
              OneCellMachine.bridgeLeftCells processed deeperLeft)
            (first :: payloadRest))) = _
      rw [TuringMachine.runConfigExact?]
      rw [OneCellMachine.prep_gate_bridge_step_of_cons]
      simp only
      rw [TuringMachine.runConfigExact?]
      rw [OneCellMachine.bridge_insert_step_of_cons]
      rfl

def insertionSteps (current : MachineCodeSymbol)
    (processed callerData : Word MachineCodeSymbol) : Nat :=
  (payload processed callerData).length +
    (BoundedBlockInsert.cellBuffer current).word.length

theorem insertion_run_exact (current : MachineCodeSymbol)
    (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    OneCellMachine.machine.runConfigExact?
        (insertionSteps current processed callerData)
        (insertionSourceConfig current processed deeperLeft callerData) =
      some (insertionEndpointConfig current processed deeperLeft callerData) := by
  apply OneCellMachine.insert_run_of_eq_some current
  exact BoundedBlockInsert.insertCell_run_exact current []
    (payload processed callerData) (baseCells processed deeperLeft)

theorem finalPayloadRev_eq (current : MachineCodeSymbol)
    (processed callerData : Word MachineCodeSymbol) :
    BoundedBlockInsert.finalLeftRev (BoundedBlockInsert.cellBuffer current) []
        (payload processed callerData) =
      (List.append (NonemptyRightRegion.cellWord current)
        (payload processed callerData)).reverse := by
  have hreverse := BoundedBlockInsert.insertedCell_word current
    ([] : Word MachineCodeSymbol) (payload processed callerData)
  have hboth := congrArg (fun word : Word MachineCodeSymbol => word.reverse) hreverse
  unfold Languages.Word at hboth ⊢
  simpa using hboth

def encodedRevAfter (current : MachineCodeSymbol)
    (processed callerData : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append
    (BoundedBlockInsert.finalLeftRev (BoundedBlockInsert.cellBuffer current) []
      (payload processed callerData))
    (List.append
      (MachineDescription.encodeNat processed.length).reverse
      [MachineCodeSymbol.tick])

theorem encodedRevAfter_eq (current : MachineCodeSymbol)
    (processed callerData : Word MachineCodeSymbol) :
    encodedRevAfter current processed callerData =
      (regionWithCaller (current :: processed) callerData).reverse := by
  rw [show encodedRevAfter current processed callerData =
      List.append
        (List.append (NonemptyRightRegion.cellWord current)
          (payload processed callerData)).reverse
        (List.append
          (MachineDescription.encodeNat processed.length).reverse
          [MachineCodeSymbol.tick]) by
    simp [encodedRevAfter, finalPayloadRev_eq]]
  unfold regionWithCaller
  rw [NonemptyRightRegion.region_cons]
  simp [payload, RightCellPrep.payload,
    List.reverse_append, List.append_assoc]

theorem insertionEndpoint_tape_eq_separatorStart
    (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    (insertionEndpointConfig current processed deeperLeft callerData).tape =
      SeparatorRewind.startTapeCells deeperLeft
        (regionWithCaller (current :: processed) callerData).reverse := by
  rw [← encodedRevAfter_eq current processed callerData]
  simp [insertionEndpointConfig, OneCellMachine.insertConfig,
    BoundedBlockInsert.haltConfig,
    VariableBlockInsert.haltConfig, baseCells,
    InitialMaterializer.RightCellInsert.baseCells, encodedRevAfter,
    SeparatorRewind.startTapeCells, List.map_append, List.append_assoc]

theorem insertionEndpoint_eq_rewind_source
    (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    insertionEndpointConfig current processed deeperLeft callerData =
      { state := .insert current .halt
        tape := SeparatorRewind.startTapeCells deeperLeft
          (regionWithCaller (current :: processed) callerData).reverse } := by
  change
    (⟨OneCellMachine.Control.insert current BoundedBlockInsert.Control.halt,
      (insertionEndpointConfig current processed deeperLeft callerData).tape⟩ :
      TuringMachine.Configuration MachineCodeSymbol OneCellMachine.Control) = _
  rw [insertionEndpoint_tape_eq_separatorStart]

theorem insertion_halt_retarget_step
    (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    OneCellMachine.machine.stepConfig
        (insertionEndpointConfig current processed deeperLeft callerData) =
      some (OneCellMachine.rewindConfig
        (SeparatorRewind.scanConfigCells deeperLeft
          (regionWithCaller (current :: processed) callerData).reverse [])) := by
  rw [insertionEndpoint_eq_rewind_source]
  cases hencoded :
      (regionWithCaller (current :: processed) callerData).reverse <;> rfl

theorem rewind_run_from_insertion_endpoint
    (current : MachineCodeSymbol) (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    OneCellMachine.machine.runConfigExact?
        ((regionWithCaller (current :: processed) callerData).length + 2)
        (insertionEndpointConfig current processed deeperLeft callerData) =
      some (endpointConfig current processed deeperLeft callerData) := by
  rw [show (regionWithCaller (current :: processed) callerData).length + 2 =
      (((regionWithCaller (current :: processed) callerData).reverse).length + 1) + 1 by
    simp]
  rw [TuringMachine.runConfigExact?]
  rw [insertion_halt_retarget_step]
  simp only
  simpa [endpointConfig] using
    OneCellMachine.rewind_scan_run_exact deeperLeft
      (regionWithCaller (current :: processed) callerData).reverse
      ([] : Word MachineCodeSymbol)

def runSteps (current : MachineCodeSymbol)
    (processed callerData : Word MachineCodeSymbol) : Nat :=
  (processed.length + 5) +
    (2 + (insertionSteps current processed callerData +
      ((regionWithCaller (current :: processed) callerData).length + 2)))

theorem run_exact (current : MachineCodeSymbol)
    (processed : Word MachineCodeSymbol)
    (deeperLeft : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    OneCellMachine.machine.runConfigExact?
        (runSteps current processed callerData)
        (sourceConfig current processed deeperLeft callerData) =
      some (endpointConfig current processed deeperLeft callerData) := by
  unfold runSteps
  rw [InitialMaterializer.ExactRun.append]
  rw [prep_run_exact]
  simp only
  rw [InitialMaterializer.ExactRun.append]
  rw [bridge_run_exact]
  simp only
  rw [InitialMaterializer.ExactRun.append]
  rw [insertion_run_exact]
  simp only
  exact rewind_run_from_insertion_endpoint current processed deeperLeft callerData

end ContextualOneCell

namespace ContextualRawTail

def leftContext (remainingRev fuelRev : Word MachineCodeSymbol) :
    List (Option MachineCodeSymbol) :=
  List.append (remainingRev.map some) (none :: fuelRev.map some)

def gateConfig (remainingRev processed fuelRev callerData :
    Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RawTailLoopMachine.Control :=
  RawTailLoopMachine.loopConfig
    (OneCellMachine.rewindConfig
      (SeparatorRewind.gateConfigCells (leftContext remainingRev fuelRev)
        (regionWithCaller processed callerData)))

def restartConfig (remainingRev processed fuelRev callerData :
    Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RawTailLoopMachine.Control where
  state := .restart
  tape :=
    { left := leftContext remainingRev fuelRev
      head := none
      right := List.append
        ((regionWithCaller processed callerData).map some) [none] }

def paddedIterationSourceConfig (current : MachineCodeSymbol)
    (remainingRev processed fuelRev callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RawTailLoopMachine.Control :=
  RawTailLoopMachine.loopConfig
    { state := .prep .start
      tape := SeparatorRewind.gateTapeCells
        (some current :: leftContext remainingRev fuelRev)
        (regionWithCaller processed callerData) }

def emptyStartConfig (processed fuelRev callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RawTailLoopMachine.Control where
  state := .loop (.prep .start)
  tape := SeparatorRewind.gateTapeCells (none :: fuelRev.map some)
    (regionWithCaller processed callerData)

def doneConfig (processed fuelRev callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol RawTailLoopMachine.Control where
  state := .done
  tape := SeparatorRewind.gateTapeCells (none :: fuelRev.map some)
    (regionWithCaller processed callerData)

theorem regionWithCaller_ne_nil (processed callerData : Word MachineCodeSymbol) :
    regionWithCaller processed callerData ≠ [] := by
  intro hnil
  have hparts := List.append_eq_nil_iff.mp hnil
  exact NonemptyRightRegion.region_ne_nil processed hparts.1

theorem gate_restart_step (remainingRev processed fuelRev callerData :
    Word MachineCodeSymbol) :
    RawTailLoopMachine.machine.stepConfig
        (gateConfig remainingRev processed fuelRev callerData) =
      some (restartConfig remainingRev processed fuelRev callerData) := by
  cases hregion : regionWithCaller processed callerData <;>
    simp [TuringMachine.stepConfig, RawTailLoopMachine.machine,
      RawTailLoopMachine.transition, gateConfig, restartConfig,
      RawTailLoopMachine.loopConfig, OneCellMachine.rewindConfig,
      SeparatorRewind.gateConfigCells, SeparatorRewind.gateTapeCells,
      leftContext, Tape.read, Tape.write, Tape.move, Tape.moveLeft, hregion]

theorem restart_iteration_step_of_cons (current : MachineCodeSymbol)
    (remainingRev processed fuelRev callerData : Word MachineCodeSymbol) :
    RawTailLoopMachine.machine.stepConfig
        (restartConfig (current :: remainingRev) processed fuelRev callerData) =
      some (paddedIterationSourceConfig current remainingRev processed
        fuelRev callerData) := by
  cases hregion : regionWithCaller processed callerData <;>
    simp [TuringMachine.stepConfig, RawTailLoopMachine.machine,
      RawTailLoopMachine.transition, restartConfig,
      paddedIterationSourceConfig, RawTailLoopMachine.loopConfig,
      SeparatorRewind.gateTapeCells, leftContext, Tape.read, Tape.write,
      Tape.move, Tape.moveRight, hregion]

theorem paddedIterationSource_equiv_clean (current : MachineCodeSymbol)
    (remainingRev processed fuelRev callerData : Word MachineCodeSymbol) :
    Tape.Equiv
      (paddedIterationSourceConfig current remainingRev processed
        fuelRev callerData).tape
      (RawTailLoopMachine.loopConfig
        (ContextualOneCell.sourceConfig current processed
          (leftContext remainingRev fuelRev) callerData)).tape := by
  have hnonempty := regionWithCaller_ne_nil processed callerData
  cases hregion : regionWithCaller processed callerData with
  | nil => contradiction
  | cons first regionRest =>
      unfold paddedIterationSourceConfig RawTailLoopMachine.loopConfig
      unfold ContextualOneCell.sourceConfig
      unfold ContextualRightCellPrep.sourceConfig
      unfold OneCellMachine.prepConfig RightCellPrep.sourceConfig
      rw [hregion]
      simp [SeparatorRewind.gateTapeCells,
        InsertOneWithBoundary.cursorTape, Tape.Equiv,
        dropTrailingNone_append_none]

theorem clean_iteration_run_exact (current : MachineCodeSymbol)
    (remainingRev processed fuelRev callerData : Word MachineCodeSymbol) :
    RawTailLoopMachine.machine.runConfigExact?
        (ContextualOneCell.runSteps current processed callerData)
        (RawTailLoopMachine.loopConfig
          (ContextualOneCell.sourceConfig current processed
            (leftContext remainingRev fuelRev) callerData)) =
      some (gateConfig remainingRev (current :: processed)
        fuelRev callerData) := by
  simpa [gateConfig, ContextualOneCell.endpointConfig] using
    RawTailLoopMachine.loop_run_of_eq_some
      (ContextualOneCell.runSteps current processed callerData)
      (ContextualOneCell.sourceConfig current processed
        (leftContext remainingRev fuelRev) callerData)
      (ContextualOneCell.endpointConfig current processed
        (leftContext remainingRev fuelRev) callerData)
      (ContextualOneCell.run_exact current processed
        (leftContext remainingRev fuelRev) callerData)

theorem padded_iteration_run_exact (current : MachineCodeSymbol)
    (remainingRev processed fuelRev callerData : Word MachineCodeSymbol) :
    exists paddedEndpoint :
        TuringMachine.Configuration MachineCodeSymbol RawTailLoopMachine.Control,
      RawTailLoopMachine.machine.runConfigExact?
          (ContextualOneCell.runSteps current processed callerData)
          (paddedIterationSourceConfig current remainingRev processed
            fuelRev callerData) = some paddedEndpoint ∧
      (gateConfig remainingRev (current :: processed) fuelRev callerData).state =
        paddedEndpoint.state ∧
      Tape.Equiv
        (gateConfig remainingRev (current :: processed)
          fuelRev callerData).tape paddedEndpoint.tape := by
  exact InitialMaterializer.TuringExactEquiv.runConfigExact?_some_of_equiv
    (clean := RawTailLoopMachine.loopConfig
      (ContextualOneCell.sourceConfig current processed
        (leftContext remainingRev fuelRev) callerData))
    (padded := paddedIterationSourceConfig current remainingRev processed
      fuelRev callerData)
    (cleanFinal := gateConfig remainingRev (current :: processed)
      fuelRev callerData)
    RawTailLoopMachine.machine
    (ContextualOneCell.runSteps current processed callerData)
    rfl
    (Tape.Equiv.symm (paddedIterationSource_equiv_clean current
      remainingRev processed fuelRev callerData))
    (clean_iteration_run_exact current remainingRev processed
      fuelRev callerData)

theorem restart_empty_step (processed fuelRev callerData :
    Word MachineCodeSymbol) :
    RawTailLoopMachine.machine.stepConfig
        (restartConfig [] processed fuelRev callerData) =
      some (emptyStartConfig processed fuelRev callerData) := by
  cases hregion : regionWithCaller processed callerData <;>
    simp [TuringMachine.stepConfig, RawTailLoopMachine.machine,
      RawTailLoopMachine.transition, restartConfig, emptyStartConfig,
      SeparatorRewind.gateTapeCells, leftContext, Tape.read, Tape.write,
      Tape.move, Tape.moveRight, hregion]

theorem empty_finish_run_exact (processed fuelRev callerData :
    Word MachineCodeSymbol) :
    RawTailLoopMachine.machine.runConfigExact? 4
        (emptyStartConfig processed fuelRev callerData) =
      some (doneConfig processed fuelRev callerData) := by
  have hnonempty := regionWithCaller_ne_nil processed callerData
  cases hregion : regionWithCaller processed callerData with
  | nil => contradiction
  | cons first rest =>
      cases rest <;>
        simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
          RawTailLoopMachine.machine, RawTailLoopMachine.transition,
          emptyStartConfig, doneConfig, OneCellMachine.transition,
          RightCellPrep.transition, SeparatorRewind.gateTapeCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
          hregion]

def runSteps : Word MachineCodeSymbol -> Word MachineCodeSymbol ->
    Word MachineCodeSymbol -> Nat
  | [], _, _ => 6
  | current :: remainingRev, processed, callerData =>
      (ContextualOneCell.runSteps current processed callerData +
        runSteps remainingRev (current :: processed) callerData) + 2

theorem run_to_done_equiv
    (remainingRev processed fuelRev callerData : Word MachineCodeSymbol) :
    exists endpoint : TuringMachine.Configuration MachineCodeSymbol
        RawTailLoopMachine.Control,
      RawTailLoopMachine.machine.runConfigExact?
          (runSteps remainingRev processed callerData)
          (gateConfig remainingRev processed fuelRev callerData) =
        some endpoint ∧
      (doneConfig (List.append remainingRev.reverse processed)
        fuelRev callerData).state = endpoint.state ∧
      Tape.Equiv
        (doneConfig (List.append remainingRev.reverse processed)
          fuelRev callerData).tape endpoint.tape := by
  induction remainingRev generalizing processed with
  | nil =>
      refine ⟨doneConfig processed fuelRev callerData, ?_, rfl,
        Tape.Equiv.refl _⟩
      change RawTailLoopMachine.machine.runConfigExact? (1 + (1 + 4))
        (gateConfig [] processed fuelRev callerData) = _
      rw [TuringMachine.runConfigExact?]
      rw [gate_restart_step]
      simp only
      rw [TuringMachine.runConfigExact?]
      rw [restart_empty_step]
      simp only
      exact empty_finish_run_exact processed fuelRev callerData
  | cons current remainingRev ih =>
      rcases padded_iteration_run_exact current remainingRev processed
          fuelRev callerData with
        ⟨cellEndpoint, hcellRun, hcellState, hcellTape⟩
      rcases ih (current :: processed) with
        ⟨restEndpoint, hrestRun, hrestState, hrestTape⟩
      rcases InitialMaterializer.TuringExactEquiv.runConfigExact?_some_of_equiv
          (clean := gateConfig remainingRev (current :: processed)
            fuelRev callerData)
          (padded := cellEndpoint)
          (cleanFinal := restEndpoint)
          RawTailLoopMachine.machine
          (runSteps remainingRev (current :: processed) callerData)
          hcellState hcellTape hrestRun with
        ⟨actualEndpoint, hactualRun, hactualState, hactualTape⟩
      refine ⟨actualEndpoint, ?_, ?_, ?_⟩
      · change RawTailLoopMachine.machine.runConfigExact?
          ((ContextualOneCell.runSteps current processed callerData +
            runSteps remainingRev (current :: processed) callerData) + 2)
          (gateConfig (current :: remainingRev) processed fuelRev callerData) = _
        rw [TuringMachine.runConfigExact?]
        rw [gate_restart_step]
        simp only
        rw [TuringMachine.runConfigExact?]
        rw [restart_iteration_step_of_cons]
        simp only
        rw [InitialMaterializer.ExactRun.append]
        rw [hcellRun]
        simp only
        exact hactualRun
      · have htarget :
            doneConfig (List.append (current :: remainingRev).reverse
                processed) fuelRev callerData =
              doneConfig (List.append remainingRev.reverse
                (current :: processed)) fuelRev callerData := by
          simp [List.reverse_cons, List.append_assoc]
        rw [htarget]
        exact hrestState.trans hactualState
      · have htarget :
            doneConfig (List.append (current :: remainingRev).reverse
                processed) fuelRev callerData =
              doneConfig (List.append remainingRev.reverse
                (current :: processed)) fuelRev callerData := by
          simp [List.reverse_cons, List.append_assoc]
        rw [htarget]
        exact Tape.Equiv.trans hrestTape hactualTape

end ContextualRawTail

def cleanRawGateConfig {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (remainingRev fuelRev callerData : Word MachineCodeSymbol) :=
  FullMaterializerMachine.rawConfig M headSymbol
    (ContextualRawTail.gateConfig remainingRev [] fuelRev callerData)

theorem cleanRawGate_state_eq_actual {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (remainingRev fuelRev callerData : Word MachineCodeSymbol) :
    (cleanRawGateConfig M headSymbol remainingRev fuelRev callerData).state =
      (rawGateConfig M headSymbol remainingRev fuelRev callerData).state := by
  rfl

theorem cleanRawGate_tape_equiv_actual {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (remainingRev fuelRev callerData : Word MachineCodeSymbol) :
    Tape.Equiv
      (cleanRawGateConfig M headSymbol remainingRev fuelRev callerData).tape
      (rawGateConfig M headSymbol remainingRev fuelRev callerData).tape := by
  cases callerData with
  | nil =>
      simp [cleanRawGateConfig, rawGateConfig,
        FullMaterializerMachine.rawConfig, ContextualRawTail.gateConfig,
        ContextualRawTail.leftContext, RawTailLoopMachine.loopConfig,
        OneCellMachine.rewindConfig, SeparatorRewind.gateConfigCells,
        SeparatorRewind.gateTapeCells, regionWithCaller,
        NonemptyRightRegion.region_nil, callerCells, Tape.Equiv]
  | cons first rest =>
      simp [cleanRawGateConfig, rawGateConfig,
        FullMaterializerMachine.rawConfig, ContextualRawTail.gateConfig,
        ContextualRawTail.leftContext, RawTailLoopMachine.loopConfig,
        OneCellMachine.rewindConfig, SeparatorRewind.gateConfigCells,
        SeparatorRewind.gateTapeCells, regionWithCaller,
        NonemptyRightRegion.region_nil, callerCells, Tape.Equiv]
      simpa [List.cons_append] using
        dropTrailingNone_append_none
          (some Frame.callerTag :: some first :: rest.map some)

def blockPaddedSourceConfig {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (processed fuelRev callerData : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      (FullMaterializerMachine.Control M) where
  state := .block headSymbol
    (.carry (NonemptyFixedPrefix.buffer M headSymbol))
  tape := (ContextualRawTail.doneConfig processed fuelRev callerData).tape

theorem raw_block_bridge_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (processed fuelRev callerData : Word MachineCodeSymbol) :
    (FullMaterializerMachine.machine M).runConfigExact? 2
        (FullMaterializerMachine.rawConfig M headSymbol
          (ContextualRawTail.doneConfig processed fuelRev callerData)) =
      some (blockPaddedSourceConfig M headSymbol processed
        fuelRev callerData) := by
  have hnonempty := ContextualRawTail.regionWithCaller_ne_nil
    processed callerData
  cases hregion : regionWithCaller processed callerData with
  | nil => contradiction
  | cons first regionRest =>
      cases regionRest <;>
        simp [TuringMachine.runConfigExact?, TuringMachine.stepConfig,
          FullMaterializerMachine.machine, FullMaterializerMachine.transition,
          FullMaterializerMachine.rawConfig, blockPaddedSourceConfig,
          ContextualRawTail.doneConfig, SeparatorRewind.gateTapeCells,
          Tape.read, Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight,
          hregion]

theorem raw_to_block_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (remainingRev fuelRev callerData : Word MachineCodeSymbol) :
    exists blockSource : TuringMachine.Configuration MachineCodeSymbol
        (FullMaterializerMachine.Control M),
      (FullMaterializerMachine.machine M).runConfigExact?
          (ContextualRawTail.runSteps remainingRev [] callerData + 2)
          (rawGateConfig M headSymbol remainingRev fuelRev callerData) =
        some blockSource ∧
      (blockPaddedSourceConfig M headSymbol remainingRev.reverse
        fuelRev callerData).state = blockSource.state ∧
      Tape.Equiv
        (blockPaddedSourceConfig M headSymbol remainingRev.reverse
          fuelRev callerData).tape blockSource.tape := by
  rcases ContextualRawTail.run_to_done_equiv remainingRev []
      fuelRev callerData with
    ⟨rawEndpoint, hrawInner, hrawState, hrawTape⟩
  let rawSteps := ContextualRawTail.runSteps remainingRev [] callerData
  have hcleanRaw :
      (FullMaterializerMachine.machine M).runConfigExact? rawSteps
          (cleanRawGateConfig M headSymbol remainingRev fuelRev callerData) =
        some (FullMaterializerMachine.rawConfig M headSymbol rawEndpoint) := by
    exact FullMaterializerMachine.raw_run_of_eq_some M headSymbol
      rawSteps _ _ hrawInner
  rcases InitialMaterializer.TuringExactEquiv.runConfigExact?_some_of_equiv
      (clean := cleanRawGateConfig M headSymbol remainingRev fuelRev callerData)
      (padded := rawGateConfig M headSymbol remainingRev fuelRev callerData)
      (cleanFinal := FullMaterializerMachine.rawConfig M headSymbol rawEndpoint)
      (FullMaterializerMachine.machine M) rawSteps
      (cleanRawGate_state_eq_actual M headSymbol remainingRev fuelRev callerData)
      (cleanRawGate_tape_equiv_actual M headSymbol remainingRev fuelRev callerData)
      hcleanRaw with
    ⟨actualRawEndpoint, hactualRaw, hactualRawState, hactualRawTape⟩
  have hprocessed : List.append remainingRev.reverse [] =
      remainingRev.reverse := by simp
  rw [hprocessed] at hrawState hrawTape
  have hdoneState :
      (FullMaterializerMachine.rawConfig M headSymbol
        (ContextualRawTail.doneConfig remainingRev.reverse
          fuelRev callerData)).state = actualRawEndpoint.state := by
    exact (congrArg (FullMaterializerMachine.Control.raw
      (M := M) headSymbol) hrawState).trans hactualRawState
  have hdoneTape : Tape.Equiv
      (FullMaterializerMachine.rawConfig M headSymbol
        (ContextualRawTail.doneConfig remainingRev.reverse
          fuelRev callerData)).tape actualRawEndpoint.tape := by
    exact Tape.Equiv.trans hrawTape hactualRawTape
  rcases InitialMaterializer.TuringExactEquiv.runConfigExact?_some_of_equiv
      (clean := FullMaterializerMachine.rawConfig M headSymbol
        (ContextualRawTail.doneConfig remainingRev.reverse
          fuelRev callerData))
      (padded := actualRawEndpoint)
      (cleanFinal := blockPaddedSourceConfig M headSymbol remainingRev.reverse
        fuelRev callerData)
      (FullMaterializerMachine.machine M) 2 hdoneState hdoneTape
      (raw_block_bridge_exact M headSymbol remainingRev.reverse
        fuelRev callerData) with
    ⟨actualBlockSource, hactualBlock, hactualBlockState,
      hactualBlockTape⟩
  refine ⟨actualBlockSource, ?_,
    hactualBlockState, hactualBlockTape⟩
  change (FullMaterializerMachine.machine M).runConfigExact?
    (rawSteps + 2)
    (rawGateConfig M headSymbol remainingRev fuelRev callerData) = _
  rw [InitialMaterializer.ExactRun.append]
  rw [hactualRaw]
  exact hactualBlock

def tailBaseRawSteps (restRev callerData : Word MachineCodeSymbol) : Nat :=
  2 + (4 + (2 +
    (ContextualRawTail.runSteps restRev [] callerData + 2)))

theorem tail_base_raw_to_block_exact {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (headSymbol : MachineCodeSymbol)
    (leftRev restRev callerData : Word MachineCodeSymbol) :
    exists blockSource : TuringMachine.Configuration MachineCodeSymbol
        (FullMaterializerMachine.Control M),
      (FullMaterializerMachine.machine M).runConfigExact?
          (tailBaseRawSteps restRev callerData)
          (FullMaterializerMachine.tailConfig M
            (ProductCallerTail.NonemptyCallerTail.haltConfig
              headSymbol leftRev restRev callerData)) =
        some blockSource ∧
      (blockPaddedSourceConfig M headSymbol restRev.reverse
        leftRev callerData).state = blockSource.state ∧
      Tape.Equiv
        (blockPaddedSourceConfig M headSymbol restRev.reverse
          leftRev callerData).tape blockSource.tape := by
  rcases raw_to_block_exact M headSymbol restRev leftRev callerData with
    ⟨blockSource, hraw, hblockState, hblockTape⟩
  have htail := tail_base_bridge_exact M headSymbol leftRev restRev callerData
  have hbase := base_rewind_exact M headSymbol leftRev restRev callerData
  have hbaseRaw := base_raw_bridge_exact M headSymbol restRev leftRev callerData
  refine ⟨blockSource, ?_,
    hblockState, hblockTape⟩
  unfold tailBaseRawSteps
  rw [InitialMaterializer.ExactRun.append]
  rw [htail]
  simp only
  rw [InitialMaterializer.ExactRun.append]
  rw [hbase]
  simp only
  rw [InitialMaterializer.ExactRun.append]
  rw [hbaseRaw]
  simp only
  exact hraw

/--
Constructive lifted continuation result for an arbitrary caller-data suffix.
The endpoint is selected from the deterministic exact run, so consumers do
not need classical choice to package the continuation as data.
-/
structure LiftedTailBaseRawResult
    {materializerState : Type} {leftCount : Nat}
    (materializer : TuringMachine MachineCodeSymbol materializerState)
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (leftConfig :
      TuringMachine.Configuration MachineCodeSymbol
          (FullMaterializerMachine.Control left) ->
        TuringMachine.Configuration MachineCodeSymbol materializerState)
    (headSymbol : MachineCodeSymbol)
    (leftRev restRev callerData : Word MachineCodeSymbol) where
  blockSource :
    TuringMachine.Configuration MachineCodeSymbol materializerState
  steps : Nat
  run_exact :
    materializer.runConfigExact? steps
        (leftConfig
          (FullMaterializerMachine.tailConfig left
            (ProductCallerTail.NonemptyCallerTail.haltConfig
              headSymbol leftRev restRev callerData))) =
      some blockSource

/--
Lift the caller-aware continuation through an enclosing materializer phase.
-/
def liftedTailBaseRawResult
    {materializerState : Type} {leftCount : Nat}
    (materializer : TuringMachine MachineCodeSymbol materializerState)
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (leftConfig :
      TuringMachine.Configuration MachineCodeSymbol
          (FullMaterializerMachine.Control left) ->
        TuringMachine.Configuration MachineCodeSymbol materializerState)
    (leftRun_exact : forall steps source target,
      (FullMaterializerMachine.machine left).runConfigExact? steps source =
          some target ->
        materializer.runConfigExact? steps (leftConfig source) =
          some (leftConfig target))
    (headSymbol : MachineCodeSymbol)
    (leftRev restRev callerData : Word MachineCodeSymbol) :
    LiftedTailBaseRawResult materializer left leftConfig
      headSymbol leftRev restRev callerData := by
  let steps := tailBaseRawSteps restRev callerData
  let source :=
    leftConfig
      (FullMaterializerMachine.tailConfig left
        (ProductCallerTail.NonemptyCallerTail.haltConfig
          headSymbol leftRev restRev callerData))
  let result := materializer.runConfigExact? steps source
  have hexists : exists blockSource, result = some blockSource := by
    rcases tail_base_raw_to_block_exact left headSymbol
        leftRev restRev callerData with
      ⟨innerBlockSource, hrun, _hstate, _htape⟩
    refine ⟨leftConfig innerBlockSource, ?_⟩
    simpa [result, steps, source] using
      leftRun_exact _ _ _ hrun
  have hsome : result.isSome := by
    rcases hexists with ⟨blockSource, hrun⟩
    simp [hrun]
  let blockSource := result.get hsome
  have hrun : result = some blockSource := by
    exact (Option.some_get hsome).symm
  exact
    { blockSource := blockSource
      steps := steps
      run_exact := by simpa [result, source] using hrun }

theorem lifted_pair_tail_base_raw_exact
    {materializerState : Type} [DecidableEq materializerState]
    {leftCount rightCount : Nat}
    (materializer : TuringMachine MachineCodeSymbol materializerState)
    (left : TuringMachine MachineCodeSymbol (Fin leftCount))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (leftConfig :
      TuringMachine.Configuration MachineCodeSymbol
          (FullMaterializerMachine.Control left) ->
        TuringMachine.Configuration MachineCodeSymbol materializerState)
    (leftRun_exact : forall steps source target,
      (FullMaterializerMachine.machine left).runConfigExact? steps source =
          some target ->
        materializer.runConfigExact? steps (leftConfig source) =
          some (leftConfig target))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (leftFuel rightFuel : Nat) :
    exists blockSource : TuringMachine.Configuration MachineCodeSymbol
        materializerState,
      materializer.runConfigExact?
          (tailBaseRawSteps rest.reverse
            (ProductInput.pairCallerData right (headSymbol :: rest) rightFuel))
          (leftConfig
            (FullMaterializerMachine.tailConfig left
              (ProductCallerTail.NonemptyCallerTail.haltConfig
                headSymbol (MachineDescription.encodeNat leftFuel).reverse
                rest.reverse
                (ProductInput.pairCallerData right (headSymbol :: rest)
                  rightFuel)))) =
        some blockSource := by
  rcases tail_base_raw_to_block_exact left headSymbol
      (MachineDescription.encodeNat leftFuel).reverse rest.reverse
      (ProductInput.pairCallerData right (headSymbol :: rest) rightFuel) with
    ⟨innerBlockSource, hrun, _hstate, _htape⟩
  exact ⟨leftConfig innerBlockSource,
    leftRun_exact _ _ _ hrun⟩

end ProductCallerAwareTail
end FoC.Computability.FiniteRecognizer.ExactFuel.StrictProbe
