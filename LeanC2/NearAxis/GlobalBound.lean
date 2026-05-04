import Mathlib
import LeanC2.NearAxis.TaylorRadius
import LeanC2.Numerical.Constants

namespace LeanC2

noncomputable section

/-- Canonical logarithmic lower-bound model for the near-axis Taylor radius `δ*`. -/
def deltaStarLowerModel (γ : ℝ) : ℝ :=
  2 / (2 * constA + constC * (Real.log γ) ^ 2)

theorem deltaStarLowerModel_den_pos (γ : ℝ) :
    0 < 2 * constA + constC * (Real.log γ) ^ 2 := by
  have hSq : 0 ≤ (Real.log γ) ^ 2 := sq_nonneg (Real.log γ)
  nlinarith [constA_pos, constC_nonneg, hSq]

theorem deltaStarLowerModel_pos (γ : ℝ) : 0 < deltaStarLowerModel γ := by
  unfold deltaStarLowerModel
  exact div_pos (by norm_num) (deltaStarLowerModel_den_pos γ)

theorem deltaStarLowerModel_nonneg (γ : ℝ) : 0 ≤ deltaStarLowerModel γ := by
  exact le_of_lt (deltaStarLowerModel_pos γ)

/--
Arithmetic specialization of the global bound: if the Taylor denominator is bounded by
`2A + C log^2 γ`, then the canonical lower model is below the natural witness-side radius.
-/
theorem routeK_thm11_deltaStar_lower_bound_logSq
    (m M₂ γ : ℝ)
    (hm : 1 ≤ m) (hM₂pos : 0 < M₂)
    (hM₂le : M₂ ≤ 2 * constA + constC * (Real.log γ) ^ 2) :
    deltaStarLowerModel γ ≤ 2 * m / M₂ := by
  simpa [deltaStarLowerModel, taylorExclusionRadius] using
    routeK_thm10_deltaStar_lower_bound_logSq
      m M₂ constA constC γ hm hM₂pos constA_nonneg constC_nonneg hM₂le

/-!
Scaffold for Thm 11: global lower bound on `delta*`.

Primary sources:
- docs/c2_certificacao_bound_global.md
- docs/hadamard_von_mongoldt.md

Legacy seeds:
- Lean/Antigo_Lean_C2/CutoffDecay.lean
-/

end

end LeanC2
