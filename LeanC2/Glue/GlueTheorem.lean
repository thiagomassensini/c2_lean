import Mathlib
import LeanC2.Bulk.FXNonZeroBulk
import LeanC2.Edge.FEdgeNonZero
import LeanC2.Glue.UniformCutoff
import LeanC2.NearAxis.FXNonZero
import LeanC2.Numerical.Constants

namespace LeanC2

theorem glueTheorem_highOffCriticalStrip
    {FX : Nat -> Complex -> Complex} {deltaStar : ℝ -> ℝ} {eps T0 : ℝ}
    (hCover : glueCovering deltaStar eps T0)
    (hNear : nearRegionEventuallyNonvanishing FX deltaStar T0)
    (hBulk : bulkRegionEventuallyNonvanishing FX deltaStar eps T0)
    (hEdge : edgeRegionEventuallyNonvanishing FX eps T0) :
    cutoffFamilyEventuallyNonvanishingOnHighOffCriticalStrip FX T0 :=
  highOffCriticalStripEventuallyNonvanishing_of_glue hCover hNear hBulk hEdge

theorem glueTheorem_highOffCriticalStrip_default
    {FX : Nat -> Complex -> Complex} {deltaStar : ℝ -> ℝ}
    (hDelta : ∀ t : ℝ, 0 ≤ deltaStar t)
    (hNear : nearRegionEventuallyNonvanishing FX deltaStar defaultT0)
    (hBulk : bulkRegionEventuallyNonvanishing FX deltaStar defaultEps defaultT0)
    (hEdge : edgeRegionEventuallyNonvanishing FX defaultEps defaultT0) :
    cutoffFamilyEventuallyNonvanishingOnHighOffCriticalStrip FX defaultT0 := by
  apply glueTheorem_highOffCriticalStrip
  · exact defaultGlueCovering hDelta
  · exact hNear
  · exact hBulk
  · exact hEdge

/-!
Scaffold for the global gluing theorem.

Primary sources:
- docs/c2_bulk_offaxis_glue.md

This theorem is the high-height gluing layer: near-axis, bulk, and edge are combined into eventual
nonvanishing of the cutoff family on the whole off-critical strip above the global height cutoff.
-/

end LeanC2
