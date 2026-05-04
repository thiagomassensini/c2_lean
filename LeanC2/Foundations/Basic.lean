import Mathlib

namespace LeanC2

abbrev sigmaPart (s : Complex) : Real := s.re
abbrev tPart (s : Complex) : Real := s.im
noncomputable def deltaPart (s : Complex) : Real := s.re - (1 : Real) / 2

/-!
Base layer for the C2 formalization.

Primary sources:
- docs/c2_rota_K_rigorosamente_fechada.md
- docs/derivacao_tilt_c2_global.md

Legacy seeds:
- Lean/Antigo_Lean_C2/Tree.lean
- Lean/Antigo_Lean_C2/GlobalDecomposition.lean
-/

end LeanC2
