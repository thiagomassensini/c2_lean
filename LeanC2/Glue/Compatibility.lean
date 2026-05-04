import Mathlib
import LeanC2.Glue.Decomposition

namespace LeanC2

def uniformCutoffThreshold (XNear XBulk XEdge : Nat) : Nat :=
  max XNear (max XBulk XEdge)

theorem le_uniformCutoffThreshold_left (XNear XBulk XEdge : Nat) :
    XNear ≤ uniformCutoffThreshold XNear XBulk XEdge := by
  exact le_max_left _ _

theorem le_uniformCutoffThreshold_bulk (XNear XBulk XEdge : Nat) :
    XBulk ≤ uniformCutoffThreshold XNear XBulk XEdge := by
  exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem le_uniformCutoffThreshold_edge (XNear XBulk XEdge : Nat) :
    XEdge ≤ uniformCutoffThreshold XNear XBulk XEdge := by
  exact le_trans (le_max_right _ _) (le_max_right _ _)

/-!
Scaffold for overlap compatibility lemmas.

Primary sources:
- docs/c2_bulk_offaxis_glue.md

At the current level of abstraction, overlap compatibility is encoded by a single threshold that
dominates the near, bulk, and edge cutoff thresholds.
-/

end LeanC2
