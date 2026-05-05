import Mathlib
import LeanC2.Identity.C0LogDerivative
import LeanC2.NearAxis.TaylorRadius
import LeanC2.Numerical.Constants

namespace LeanC2

noncomputable section

/-- Parametric logarithmic lower-bound model for the near-axis Taylor radius `δ*`. -/
def deltaStarLowerModelOf (A C γ : ℝ) : ℝ :=
  2 / (2 * A + C * (Real.log γ) ^ 2)

/-- Canonical logarithmic lower-bound model for the near-axis Taylor radius `δ*`. -/
def deltaStarLowerModel (γ : ℝ) : ℝ :=
  deltaStarLowerModelOf constA constC γ

/--
Theoretical logarithmic lower-bound model driven by the proved critical-line bound on `c0'/c0`.
-/
def theoreticalDeltaStarLowerModel (γ : ℝ) : ℝ :=
  deltaStarLowerModelOf c0LogDerivativeCriticalBound constC γ

theorem deltaStarLowerModelOf_den_pos (A C γ : ℝ)
    (hA : 0 < A) (hC : 0 ≤ C) :
    0 < 2 * A + C * (Real.log γ) ^ 2 := by
  have hSq : 0 ≤ (Real.log γ) ^ 2 := sq_nonneg (Real.log γ)
  nlinarith

theorem deltaStarLowerModel_den_pos (γ : ℝ) :
    0 < 2 * constA + constC * (Real.log γ) ^ 2 := by
  exact deltaStarLowerModelOf_den_pos constA constC γ constA_pos constC_nonneg

theorem theoreticalDeltaStarLowerModel_den_pos (γ : ℝ) :
    0 < 2 * c0LogDerivativeCriticalBound + constC * (Real.log γ) ^ 2 := by
  exact
    deltaStarLowerModelOf_den_pos
      c0LogDerivativeCriticalBound constC γ
      c0LogDerivativeCriticalBound_pos constC_nonneg

theorem deltaStarLowerModelOf_pos (A C γ : ℝ)
    (hA : 0 < A) (hC : 0 ≤ C) :
    0 < deltaStarLowerModelOf A C γ := by
  unfold deltaStarLowerModelOf
  exact div_pos (by norm_num) (deltaStarLowerModelOf_den_pos A C γ hA hC)

theorem deltaStarLowerModelOf_nonneg (A C γ : ℝ)
    (hA : 0 < A) (hC : 0 ≤ C) :
    0 ≤ deltaStarLowerModelOf A C γ := by
  exact le_of_lt (deltaStarLowerModelOf_pos A C γ hA hC)

theorem deltaStarLowerModel_pos (γ : ℝ) : 0 < deltaStarLowerModel γ := by
  unfold deltaStarLowerModel
  exact deltaStarLowerModelOf_pos constA constC γ constA_pos constC_nonneg

theorem deltaStarLowerModel_nonneg (γ : ℝ) : 0 ≤ deltaStarLowerModel γ := by
  exact le_of_lt (deltaStarLowerModel_pos γ)

theorem theoreticalDeltaStarLowerModel_pos (γ : ℝ) :
    0 < theoreticalDeltaStarLowerModel γ := by
  unfold theoreticalDeltaStarLowerModel
  exact
    deltaStarLowerModelOf_pos
      c0LogDerivativeCriticalBound constC γ
      c0LogDerivativeCriticalBound_pos constC_nonneg

theorem theoreticalDeltaStarLowerModel_nonneg (γ : ℝ) :
    0 ≤ theoreticalDeltaStarLowerModel γ := by
  exact le_of_lt (theoreticalDeltaStarLowerModel_pos γ)

/--
Arithmetic specialization of the global bound with explicit constants `A` and `C`: if the Taylor
denominator is bounded by `2A + C log^2 γ`, then the corresponding lower model is below the
natural witness-side radius.
-/
theorem deltaStarLowerModelOf_le_taylorExclusionRadius_logSq
    (m M₂ A C γ : ℝ)
    (hm : 1 ≤ m) (hM₂pos : 0 < M₂)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hM₂le : M₂ ≤ 2 * A + C * (Real.log γ) ^ 2) :
    deltaStarLowerModelOf A C γ ≤ 2 * m / M₂ := by
  simpa [deltaStarLowerModelOf, taylorExclusionRadius] using
    routeK_thm10_deltaStar_lower_bound_logSq
      m M₂ A C γ hm hM₂pos hA hC hM₂le

/--
Arithmetic specialization of the global bound: if the Taylor denominator is bounded by
`2A + C log^2 γ`, then the canonical lower model is below the natural witness-side radius.
-/
theorem deltaStarLowerModel_le_taylorExclusionRadius_logSq
    (m M₂ γ : ℝ)
    (hm : 1 ≤ m) (hM₂pos : 0 < M₂)
    (hM₂le : M₂ ≤ 2 * constA + constC * (Real.log γ) ^ 2) :
    deltaStarLowerModel γ ≤ 2 * m / M₂ := by
  exact deltaStarLowerModelOf_le_taylorExclusionRadius_logSq
    m M₂ constA constC γ hm hM₂pos constA_nonneg constC_nonneg hM₂le

/--
Theoretical specialization of the global bound driven by the proved critical-line bound on
`α = c0'/c0` and the default Hadamard-von-Mangoldt constant `constC`.
-/
theorem theoreticalDeltaStarLowerModel_le_taylorExclusionRadius_logSq
    (m M₂ γ : ℝ)
    (hm : 1 ≤ m) (hM₂pos : 0 < M₂)
    (hM₂le : M₂ ≤ 2 * c0LogDerivativeCriticalBound + constC * (Real.log γ) ^ 2) :
    theoreticalDeltaStarLowerModel γ ≤ 2 * m / M₂ := by
  exact deltaStarLowerModelOf_le_taylorExclusionRadius_logSq
    m M₂ c0LogDerivativeCriticalBound constC γ hm hM₂pos
    c0LogDerivativeCriticalBound_nonneg constC_nonneg hM₂le

/-!
Scaffold for Thm 11: global lower bound on `delta*`.

Primary sources:
- docs/c2_certificacao_bound_global.md
- docs/hadamard_von_mongoldt.md

Besides the default numerical model driven by `constA = 1.5862`, this file also exposes the
theoretical specialization `theoreticalDeltaStarLowerModel` built from the proved critical-line
bound on `α = c0'/c0` in `Identity/C0LogDerivative.lean`.
-/

end

end LeanC2
