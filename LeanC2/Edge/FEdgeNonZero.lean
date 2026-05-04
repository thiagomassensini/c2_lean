import Mathlib
import LeanC2.Cutoff.DecayRate
import LeanC2.Edge.EdgeLeft
import LeanC2.Edge.EdgeRight
import LeanC2.Glue.Decomposition
import LeanC2.Identity.C0NonZero

namespace LeanC2

def edgeRegionEventuallyNonvanishing
    (FX : Nat -> Complex -> Complex) (eps T0 : ℝ) : Prop :=
  ∃ X0 : Nat, ∀ X : Nat, X0 ≤ X -> ∀ s : Complex, edgeRegion eps T0 s -> FX X s ≠ 0

/-!
Scaffold for the edge zero-free region of `F_X`.

Primary sources:
- docs/c2_bulk_offaxis_edge_lemma.md

This layer is kept as an explicit interface that produces eventual nonvanishing on the edge region
for sufficiently large cutoff parameter `X`.
-/

end LeanC2
