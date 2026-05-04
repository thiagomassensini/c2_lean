import Mathlib
import LeanC2.Bulk.BulkLowerBound
import LeanC2.Cutoff.DecayRate
import LeanC2.Glue.Decomposition

namespace LeanC2

def bulkRegionEventuallyNonvanishing
    (FX : Nat -> Complex -> Complex) (deltaStar : ℝ -> ℝ) (eps T0 : ℝ) : Prop :=
  ∃ X0 : Nat,
    ∀ X : Nat, X0 ≤ X -> ∀ s : Complex, bulkRegion deltaStar eps T0 s -> FX X s ≠ 0

/-!
Scaffold for the bulk zero-free region of `F_X`.

Primary sources:
- docs/c2_bulk_offaxis_glue.md

This layer is kept as an explicit interface that produces eventual nonvanishing on the bulk region
for sufficiently large cutoff parameter `X`.
-/

end LeanC2
