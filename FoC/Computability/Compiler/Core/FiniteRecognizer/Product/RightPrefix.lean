import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Contextual.Full
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Duplicator

set_option doc.verso true

/-!
# Contextual right-call product prefix

Connect the collision-free product-call duplicator to the contextual stage-input
materializer. The resulting endpoint retains the left call and the copied raw
right call to the left of the protected right probe frame.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductRightPrefix

def innerCode (input : Word MachineCodeSymbol) (rightFuel : Nat) :
    Word MachineCodeSymbol :=
  ProductDuplicator.productInnerCode input rightFuel

def retainedOuterRev
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    Word MachineCodeSymbol :=
  List.append (innerCode input rightFuel).reverse
    (ProductDuplicator.productBaseLeftRev leftFuel)

theorem retainedOuterRev_reverse
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    (retainedOuterRev input leftFuel rightFuel).reverse =
      List.append (MachineDescription.encodeNat leftFuel)
        (MachineDescription.encodeNatAppend rightFuel input) := by
  simp [retainedOuterRev, innerCode,
    ProductDuplicator.productInnerCode,
    ProductDuplicator.productBaseLeftRev, List.reverse_append]

def rightSourceConfig {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :=
  ProductContextual.Full.sourceConfig right
    (retainedOuterRev input leftFuel rightFuel) rightFuel input

theorem rightSourceTape_eq_duplicatorTarget {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    (rightSourceConfig right input leftFuel rightFuel).tape =
      (ProductDuplicator.productTargetConfig
        input leftFuel rightFuel).tape := by
  cases rightFuel with
  | zero =>
      cases input <;>
        simp [rightSourceConfig,
          ProductContextual.Full.sourceConfig,
          ProductContextual.Full.parserConfig,
          InitialMaterializer.FullMaterializerMachine.parseConfig,
          ProductContextual.Parser.config,
          ProductContextual.Parser.tape,
          retainedOuterRev, innerCode,
          ProductDuplicator.productTargetConfig,
          ProductDuplicator.haltConfig,
          ProductDuplicator.haltTape,
          ProductDuplicator.scanTape,
          ProductDuplicator.tapeAtCells,
          ProductDuplicator.productInnerCode,
          ProductDuplicator.productBaseLeftRev,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat, List.map_append,
          List.append_assoc, Tape.move, Tape.moveRight]
  | succ rightFuel =>
      cases input <;>
        simp [rightSourceConfig,
          ProductContextual.Full.sourceConfig,
          ProductContextual.Full.parserConfig,
          InitialMaterializer.FullMaterializerMachine.parseConfig,
          ProductContextual.Parser.config,
          ProductContextual.Parser.tape,
          retainedOuterRev, innerCode,
          ProductDuplicator.productTargetConfig,
          ProductDuplicator.haltConfig,
          ProductDuplicator.haltTape,
          ProductDuplicator.scanTape,
          ProductDuplicator.tapeAtCells,
          ProductDuplicator.productInnerCode,
          ProductDuplicator.productBaseLeftRev,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeNat, List.map_append,
          List.append_assoc, Tape.move, Tape.moveRight]

def canonicalRightEndpointTape {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    Tape MachineCodeSymbol :=
  match input with
  | [] =>
      ProductContextual.Full.emptyHaltTape right
        (retainedOuterRev input leftFuel rightFuel) rightFuel
  | headSymbol :: rest =>
      ProductContextual.Full.nonemptyHaltTape right
        (retainedOuterRev input leftFuel rightFuel) rightFuel
        headSymbol rest

def rightTerminalState {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) :
    ProductContextual.Full.Control right :=
  match input with
  | [] => .emptyPrepend .gate
  | _ :: _ => .header .halt

theorem right_run_to_endpoint {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    exists (steps : Nat)
        (endpoint : TuringMachine.Configuration MachineCodeSymbol
          (ProductContextual.Full.Control right)),
      (InitialMaterializer.FullMaterializerMachine.machine right).runConfigExact?
          steps (rightSourceConfig right input leftFuel rightFuel) =
        some endpoint ∧
      endpoint.state = rightTerminalState right input ∧
      Tape.Equiv
        (canonicalRightEndpointTape right input leftFuel rightFuel)
        endpoint.tape := by
  cases input with
  | nil =>
      rcases ProductContextual.Full.empty_run_to_contextual_endpoint
          right (retainedOuterRev [] leftFuel rightFuel) rightFuel with
        ⟨steps, endpoint, hrun, hstate, htape⟩
      refine ⟨steps, endpoint, ?_, ?_, ?_⟩
      · exact hrun
      · simpa [rightTerminalState] using hstate
      · change Tape.Equiv
          (ProductContextual.Full.emptyHaltTape right
            (retainedOuterRev ([] : Word MachineCodeSymbol)
              leftFuel rightFuel) rightFuel)
          endpoint.tape
        rw [htape]
        exact Tape.Equiv.refl _
  | cons headSymbol rest =>
      rcases ProductContextual.Full.nonempty_run_to_contextual_endpoint
          right (retainedOuterRev (headSymbol :: rest) leftFuel rightFuel)
          rightFuel headSymbol rest with
        ⟨steps, endpoint, hrun, hstate, htape⟩
      refine ⟨steps, endpoint, ?_, ?_, ?_⟩
      · exact hrun
      · simpa [rightTerminalState] using hstate
      · exact htape

theorem filterMap_some_word (word : Word MachineCodeSymbol) :
    List.filterMap
        ((fun cell : Option MachineCodeSymbol => cell) ∘ some) word =
      word := by
  induction word with
  | nil => rfl
  | cons head tail ih => simp [Function.comp_def]

theorem canonicalRightEndpoint_normalizedOutput {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (input : Word MachineCodeSymbol) (leftFuel rightFuel : Nat) :
    Tape.normalizedOutput
        (canonicalRightEndpointTape right input leftFuel rightFuel) =
      List.append (MachineDescription.encodeNat leftFuel)
        (List.append (innerCode input rightFuel)
          (ProductInput.pairCallerData right input rightFuel)) := by
  cases input with
  | nil =>
      have hbody := ProductInput.emptyBody_append_callerData
        right rightFuel ([] : Word MachineCodeSymbol)
      have hraw :
          Tape.normalizedOutput
              (canonicalRightEndpointTape right [] leftFuel rightFuel) =
            List.append
              (retainedOuterRev [] leftFuel rightFuel).reverse
              (MachineCodeSymbol.header ::
                InitialMaterializer.EmptyInputSuffix.body right rightFuel) := by
        cases rightFuel <;>
          simp [canonicalRightEndpointTape,
            ProductContextual.Full.emptyHaltTape,
            ProductContextual.Prepend.gateTape,
            InitialMaterializer.EmptyInputSuffix.body,
            MachineDescription.encodeNat,
            Tape.normalizedOutput, Tape.cells, filterMap_some_word,
            List.append_assoc]
      rw [hraw, retainedOuterRev_reverse]
      have hbody' :
          MachineCodeSymbol.header ::
              InitialMaterializer.EmptyInputSuffix.body right rightFuel =
            ProductInput.pairCallerData right [] rightFuel := by
        simpa [ProductInput.pairCallerData] using hbody
      rw [hbody']
      simp [innerCode, ProductDuplicator.productInnerCode,
        List.append_assoc]
  | cons headSymbol rest =>
      have hbody := ProductInput.nonemptyBody_append_callerData
        right rightFuel headSymbol rest ([] : Word MachineCodeSymbol)
      have hraw :
          Tape.normalizedOutput
              (canonicalRightEndpointTape right (headSymbol :: rest)
                leftFuel rightFuel) =
            List.append
              (retainedOuterRev (headSymbol :: rest)
                leftFuel rightFuel).reverse
              (MachineCodeSymbol.header ::
                InitialMaterializer.NonemptyFixedPrefix.body right
                  rightFuel headSymbol rest) := by
        cases rightFuel <;>
          simp [canonicalRightEndpointTape,
            ProductContextual.Full.nonemptyHaltTape,
            ProductContextual.Header.haltTape,
            InitialMaterializer.NonemptyFixedPrefix.body,
            MachineDescription.encodeNat,
            Tape.normalizedOutput, Tape.cells, filterMap_some_word,
            List.append_assoc]
      rw [hraw, retainedOuterRev_reverse]
      have hbody' :
          MachineCodeSymbol.header ::
              InitialMaterializer.NonemptyFixedPrefix.body right
                rightFuel headSymbol rest =
            ProductInput.pairCallerData right (headSymbol :: rest)
              rightFuel := by
        simpa [ProductInput.pairCallerData] using hbody
      rw [hbody']
      simp [innerCode, ProductDuplicator.productInnerCode,
        List.append_assoc]

end ProductRightPrefix
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
