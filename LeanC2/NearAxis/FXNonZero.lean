import Mathlib
import LeanC2.Cutoff.DecayRate
import LeanC2.Glue.Decomposition
import LeanC2.NearAxis.GlobalBound

namespace LeanC2

def nearRegionEventuallyNonvanishing
    (FX : Nat -> Complex -> Complex) (deltaStar : ℝ -> ℝ) (T0 : ℝ) : Prop :=
  ∃ X0 : Nat, ∀ X : Nat, X0 ≤ X -> ∀ s : Complex, nearRegion deltaStar T0 s -> FX X s ≠ 0

/-!
Scaffold for the near-axis zero-free region of `F_X`.

Primary sources:
- docs/c2_bulk_offaxis_glue.md

Legacy seeds:
- Lean/Antigo_Lean_C2/CutoffDecay.lean
- Lean/Antigo_Lean_C2/Continuation.lean

This layer is kept as an explicit interface that produces eventual nonvanishing on the near-axis
region for sufficiently large cutoff parameter `X`.
-/

end LeanC2
