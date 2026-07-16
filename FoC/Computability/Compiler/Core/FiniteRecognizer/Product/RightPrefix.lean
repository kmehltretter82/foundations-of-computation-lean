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

end ProductRightPrefix
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC
