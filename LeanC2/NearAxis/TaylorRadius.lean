import Mathlib

namespace LeanC2

/-- Abstract Taylor exclusion radius attached to first- and second-order witnesses. -/
noncomputable def taylorExclusionRadius (m M₂ : ℝ) : ℝ :=
  2 * m / M₂

/--
For `0 < δ < 2m/M₂`, the first-order Taylor term strictly dominates the quadratic correction.
-/
theorem routeK_elo5_firstorder_dominates (m M₂ δ : ℝ)
    (hm : 0 < m) (hM₂ : 0 < M₂) (hδ : 0 < δ)
    (hδ_small : δ < taylorExclusionRadius m M₂) :
    0 < δ * m - δ ^ 2 / 2 * M₂ := by
  have h1 : δ * M₂ < 2 * m := by
    calc
      δ * M₂ < taylorExclusionRadius m M₂ * M₂ :=
        mul_lt_mul_of_pos_right hδ_small hM₂
      _ = 2 * m := by
        unfold taylorExclusionRadius
        field_simp [hM₂.ne']
  have key : 0 < δ * (2 * m - δ * M₂) := mul_pos hδ (by linarith)
  have hRewrite : δ * m - δ ^ 2 / 2 * M₂ = δ * (2 * m - δ * M₂) / 2 := by
    ring
  linarith

/-- The Taylor exclusion radius is strictly positive as soon as the witnesses are positive. -/
theorem routeK_elo5_exclusion_radius_pos (m M₂ : ℝ) (hm : 0 < m) (hM₂ : 0 < M₂) :
    0 < taylorExclusionRadius m M₂ := by
  unfold taylorExclusionRadius
  exact div_pos (by linarith) hM₂

/--
If the Taylor lower bound strictly dominates the residual, then the target value is nonzero.
-/
theorem routeK_elo5_nonzero_from_taylor (m M₂ R : ℝ) (hm : 0 < m) (hM₂ : 0 < M₂)
    (δ : ℝ) (hδ : 0 < δ) (hδ_small : δ < taylorExclusionRadius m M₂)
    (_hR : 0 ≤ R) (hR_small : R < δ * m - δ ^ 2 / 2 * M₂)
    (F : Complex) (hF_lb : δ * m - δ ^ 2 / 2 * M₂ - R ≤ ‖F‖) :
    F ≠ 0 :=
  norm_pos_iff.mp (by
    have hMain := routeK_elo5_firstorder_dominates m M₂ δ hm hM₂ hδ hδ_small
    linarith)

/--
A pointwise witness that the Taylor lower bound already forces nonvanishing at offset `δ`.
-/
def taylorNonvanishingWitness (F : Complex) (δ : ℝ) : Prop :=
  ∃ m M₂ R : ℝ,
    0 < m ∧
    0 < M₂ ∧
    0 < δ ∧
    δ < taylorExclusionRadius m M₂ ∧
    0 ≤ R ∧
    R < δ * m - δ ^ 2 / 2 * M₂ ∧
    δ * m - δ ^ 2 / 2 * M₂ - R ≤ ‖F‖

/-- Any Taylor nonvanishing witness yields actual nonvanishing of the target value. -/
theorem nonzero_of_taylorNonvanishingWitness {F : Complex} {δ : ℝ}
    (hWitness : taylorNonvanishingWitness F δ) :
    F ≠ 0 := by
  rcases hWitness with ⟨m, M₂, R, hm, hM₂, hδ, hδ_small, hR, hR_small, hF_lb⟩
  exact routeK_elo5_nonzero_from_taylor
    m M₂ R hm hM₂ δ hδ hδ_small hR hR_small F hF_lb

/--
If `M₂ ≤ M₂bound`, then the Taylor exclusion radius is bounded below by the corresponding
bound-side radius.
-/
theorem routeK_thm10_deltaStar_lower_bound_scaled_from_M2bound
    (m M₂ M₂bound : ℝ)
    (hm : 0 < m) (hM₂pos : 0 < M₂) (hBoundPos : 0 < M₂bound)
    (hM₂le : M₂ ≤ M₂bound) :
    2 * m / M₂bound ≤ taylorExclusionRadius m M₂ := by
  unfold taylorExclusionRadius
  have hBoundNe : M₂bound ≠ 0 := ne_of_gt hBoundPos
  have hM₂ne : M₂ ≠ 0 := ne_of_gt hM₂pos
  field_simp [hBoundNe, hM₂ne]
  nlinarith [hM₂le, hm]

/-- Version of the previous bound normalized only by `m ≥ 1`. -/
theorem routeK_thm10_deltaStar_lower_bound_from_M2bound
    (m M₂ M₂bound : ℝ)
    (hm : 1 ≤ m) (hM₂pos : 0 < M₂) (hBoundPos : 0 < M₂bound)
    (hM₂le : M₂ ≤ M₂bound) :
    2 / M₂bound ≤ taylorExclusionRadius m M₂ := by
  have hScaled : 2 * m / M₂bound ≤ taylorExclusionRadius m M₂ :=
    routeK_thm10_deltaStar_lower_bound_scaled_from_M2bound
      m M₂ M₂bound (lt_of_lt_of_le (by norm_num) hm) hM₂pos hBoundPos hM₂le
  have hBase : 2 / M₂bound ≤ 2 * m / M₂bound := by
    have hBoundNe : M₂bound ≠ 0 := ne_of_gt hBoundPos
    field_simp [hBoundNe]
    nlinarith [hm]
  exact le_trans hBase hScaled

/-- Parametric C2-form lower bound for the Taylor radius. -/
theorem routeK_thm10_deltaStar_lower_bound_parametric
    (m M₂ A C L : ℝ)
    (hm : 1 ≤ m) (hM₂pos : 0 < M₂)
    (_hA : 0 ≤ A) (_hC : 0 ≤ C) (_hL : 0 ≤ L)
    (hM₂le : M₂ ≤ 2 * A + C * L) :
    2 / (2 * A + C * L) ≤ taylorExclusionRadius m M₂ := by
  have hBoundPos : 0 < 2 * A + C * L := by
    linarith
  exact routeK_thm10_deltaStar_lower_bound_from_M2bound
    m M₂ (2 * A + C * L) hm hM₂pos hBoundPos hM₂le

/-- Scaled parametric C2-form lower bound for the Taylor radius. -/
theorem routeK_thm10_deltaStar_lower_bound_scaled_parametric
    (m M₂ A C L : ℝ)
    (hm : 0 < m) (hM₂pos : 0 < M₂)
    (_hA : 0 ≤ A) (_hC : 0 ≤ C) (_hL : 0 ≤ L)
    (hM₂le : M₂ ≤ 2 * A + C * L) :
    2 * m / (2 * A + C * L) ≤ taylorExclusionRadius m M₂ := by
  have hBoundPos : 0 < 2 * A + C * L := by
    linarith
  exact routeK_thm10_deltaStar_lower_bound_scaled_from_M2bound
    m M₂ (2 * A + C * L) hm hM₂pos hBoundPos hM₂le

/-- Logarithmic specialization of the generic Taylor-radius lower bound. -/
theorem routeK_thm10_deltaStar_lower_bound_logSq
    (m M₂ A C γ : ℝ)
    (hm : 1 ≤ m) (hM₂pos : 0 < M₂)
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hM₂le : M₂ ≤ 2 * A + C * (Real.log γ) ^ 2) :
    2 / (2 * A + C * (Real.log γ) ^ 2) ≤ taylorExclusionRadius m M₂ := by
  exact routeK_thm10_deltaStar_lower_bound_parametric
    m M₂ A C ((Real.log γ) ^ 2) hm hM₂pos _hA _hC (sq_nonneg (Real.log γ)) hM₂le

/-- Scaled logarithmic specialization of the generic Taylor-radius lower bound. -/
theorem routeK_thm10_deltaStar_lower_bound_scaled_logSq
    (m M₂ A C γ : ℝ)
    (hm : 0 < m) (hM₂pos : 0 < M₂)
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hM₂le : M₂ ≤ 2 * A + C * (Real.log γ) ^ 2) :
    2 * m / (2 * A + C * (Real.log γ) ^ 2) ≤ taylorExclusionRadius m M₂ := by
  exact routeK_thm10_deltaStar_lower_bound_scaled_parametric
    m M₂ A C ((Real.log γ) ^ 2) hm hM₂pos _hA _hC (sq_nonneg (Real.log γ)) hM₂le

/-!
Scaffold for the Taylor radius `delta*` near zeros.

Primary sources:
- docs/c2_lower_bound_transversal_taylor.md

This module keeps only the algebraic Taylor-radius layer: positivity of the exclusion radius,
dominance of the linear term over the quadratic error, and the generic `M₂`-bound transfer used
later by the concrete global model.
-/

end LeanC2
