import Mathlib
import LeanC2.Bulk.FXNonZeroBulk
import LeanC2.Edge.FEdgeNonZero
import LeanC2.Glue.Compatibility
import LeanC2.NearAxis.FXNonZero

namespace LeanC2

theorem highOffCriticalStripEventuallyNonvanishing_of_glue
    {FX : Nat -> Complex -> Complex} {deltaStar : ℝ -> ℝ} {eps T0 : ℝ}
    (hCover : glueCovering deltaStar eps T0)
    (hNear : nearRegionEventuallyNonvanishing FX deltaStar T0)
    (hBulk : bulkRegionEventuallyNonvanishing FX deltaStar eps T0)
    (hEdge : edgeRegionEventuallyNonvanishing FX eps T0) :
    cutoffFamilyEventuallyNonvanishingOnHighOffCriticalStrip FX T0 := by
  rcases hNear with ⟨XNear, hNearX⟩
  rcases hBulk with ⟨XBulk, hBulkX⟩
  rcases hEdge with ⟨XEdge, hEdgeX⟩
  let X0 := uniformCutoffThreshold XNear XBulk XEdge
  refine ⟨X0, ?_⟩
  intro X hX s hs
  rcases hCover s hs with hsNear | hsBulk | hsEdge
  · exact hNearX X (le_trans (le_uniformCutoffThreshold_left _ _ _) hX) s hsNear
  · exact hBulkX X (le_trans (le_uniformCutoffThreshold_bulk _ _ _) hX) s hsBulk
  · exact hEdgeX X (le_trans (le_uniformCutoffThreshold_edge _ _ _) hX) s hsEdge

/-!
Scaffold for the uniform cutoff scale `X(T)`.

Primary sources:
- docs/c2_bulk_offaxis_glue.md

At the current abstraction level, this file packages the statement that one common cutoff threshold
controls all three regional nonvanishing mechanisms simultaneously.
-/

end LeanC2
