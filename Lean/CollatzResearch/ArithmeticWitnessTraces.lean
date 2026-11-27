import CollatzResearch.ArithmeticWitness

/-!
# Concrete arithmetic trace fixtures (story R04)

This module is **generated** by `scripts/generate_arithmetic_traces.py`.
Regenerate it with that script; do not edit it by hand.

The numbers below come from the untrusted Python reference arithmetic. Lean
re-checks every equation in `CollatzResearch.ArithmeticWitness`, and the
acceptance theorems in `ArithmeticWitnessTests` prove that the accepted
traces are the canonical accelerated trajectories.

The generator is deterministic: the same inputs produce a byte-identical file.
-/

namespace CollatzResearch


/-- The odd trajectory 3 -> 5 -> 1, two accelerated steps. -/
def traceThreeFiveOne : TraceWitness :=
  { start := 3
    steps := [⟨1, 5⟩, ⟨4, 1⟩]
    endpoint := 1 }

/-- The trajectory from 27: 41 accelerated steps to 1. -/
def traceTwentySeven : TraceWitness :=
  { start := 27
    steps := [⟨1, 41⟩, ⟨2, 31⟩, ⟨1, 47⟩, ⟨1, 71⟩, ⟨1, 107⟩, ⟨1, 161⟩, ⟨2, 121⟩, ⟨2, 91⟩, ⟨1, 137⟩, ⟨2, 103⟩, ⟨1, 155⟩, ⟨1, 233⟩, ⟨2, 175⟩, ⟨1, 263⟩, ⟨1, 395⟩, ⟨1, 593⟩, ⟨2, 445⟩, ⟨3, 167⟩, ⟨1, 251⟩, ⟨1, 377⟩, ⟨2, 283⟩, ⟨1, 425⟩, ⟨2, 319⟩, ⟨1, 479⟩, ⟨1, 719⟩, ⟨1, 1079⟩, ⟨1, 1619⟩, ⟨1, 2429⟩, ⟨3, 911⟩, ⟨1, 1367⟩, ⟨1, 2051⟩, ⟨1, 3077⟩, ⟨4, 577⟩, ⟨2, 433⟩, ⟨2, 325⟩, ⟨4, 61⟩, ⟨3, 23⟩, ⟨1, 35⟩, ⟨1, 53⟩, ⟨5, 5⟩, ⟨4, 1⟩]
    endpoint := 1 }

end CollatzResearch
