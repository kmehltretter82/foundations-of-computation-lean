import FoC.Computability.Compiler.Core.EncodedRewriters.BoundedLayoutRunner.ConfigRunner.Closed

set_option doc.verso true

/-!
# Bounded recognizer-configuration runner phase

The runner phase starts from a validated layout tape, simulates both stored
recognizer configurations for the layout stage, and preserves the exact updated
layout needed by the emitter phase.
-/
