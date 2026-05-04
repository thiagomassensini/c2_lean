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
  unfold deltaStarLowerModel
  have hDenPos : 0 < 2 * constA + constC * (Real.log γ) ^ 2 :=
    deltaStarLowerModel_den_pos γ
  have hFirst : 2 / (2 * constA + constC * (Real.log γ) ^ 2) ≤ 2 / M₂ := by
    have hInv : 1 / (2 * constA + constC * (Real.log γ) ^ 2) ≤ 1 / M₂ := by
      exact one_div_le_one_div_of_le hM₂pos hM₂le
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left hInv (by norm_num : 0 ≤ (2 : ℝ))
  have hSecond : 2 / M₂ ≤ 2 * m / M₂ := by
    have hMul : (2 : ℝ) ≤ 2 * m := by
      nlinarith
    exact div_le_div_of_nonneg_right hMul hM₂pos.le
  exact le_trans hFirst hSecond

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
