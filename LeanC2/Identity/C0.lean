import Mathlib
import LeanC2.Foundations.Basic

namespace LeanC2

noncomputable def c0 (s : Complex) : Complex :=
  ((2 : Complex) ^ (-2 * s)) * (((2 : Complex) ^ s) - 1) / (2 * ((2 : Complex) ^ s) - 1)

/-!
Normalization factor for the exact identity `F_infty = c0 * zeta`.

Primary sources:
- docs/algebra_Z_igual_zeta.md

Legacy seeds:
- Lean/Antigo_Lean_C2/Normalization.lean
-/

end LeanC2
