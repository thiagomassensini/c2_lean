import Mathlib

namespace LeanC2

def discreteLaplacian (f : Int -> Real) (c : Int) : Real :=
  f (c - 1) + f (c + 1) - 2 * f c

/-!
Centered second difference used by the tilt and carry layers.

Primary sources:
- docs/derivacao_tilt_c2_global.md
- docs/c2_rota_K_rigorosamente_fechada.md

Legacy seeds:
- Lean/Antigo_Lean_C2/Tilt.lean
- Lean/Antigo_Lean_C2/TiltConvexity.lean
-/

end LeanC2
