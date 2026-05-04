import Mathlib
import LeanC2.Bulk.Resolvent

namespace LeanC2

/-- Degree-3 truncation of the exact resolvent. -/
noncomputable def quartetPolynomial (r θ : Real) : Complex :=
  let z := radialPhase r θ
  1 + z + z ^ 2 + z ^ 3

theorem quartetPolynomial_eq_closedForm {r θ : Real}
    (hneq : radialPhase r θ ≠ 1) :
    quartetPolynomial r θ =
      (1 - radialPhase r θ ^ 4) / (1 - radialPhase r θ) := by
  have hz : (1 : Complex) - radialPhase r θ ≠ 0 := by
    apply sub_ne_zero.mpr
    simpa [eq_comm] using hneq
  have hcf :
      (1 - radialPhase r θ ^ 4) / (1 - radialPhase r θ) = quartetPolynomial r θ := by
    apply (div_eq_iff hz).2
    unfold quartetPolynomial
    ring
  exact hcf.symm

theorem norm_quartetPolynomial_ge_sharp {r θ : Real}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (1 - r) * (1 + r ^ 2) ≤ ‖quartetPolynomial r θ‖ := by
  let z : Complex := radialPhase r θ
  have hneq : z ≠ 1 := radialPhase_ne_one_of_lt_one hr0 hr1 θ
  have hz : ‖z‖ = r := by
    simpa [z] using norm_radialPhase hr0 θ
  have hdenUpper : ‖1 - z‖ ≤ 1 + r := by
    calc
      ‖1 - z‖ = ‖(1 : Complex) + (-z)‖ := by simp [sub_eq_add_neg]
      _ ≤ ‖(1 : Complex)‖ + ‖-z‖ := norm_add_le _ _
      _ = 1 + r := by rw [norm_one, norm_neg, hz]
  have hz4 : ‖z ^ 4‖ = r ^ 4 := by rw [norm_pow, hz]
  have hnumLower : 1 - r ^ 4 ≤ ‖1 - z ^ 4‖ := by
    have hraw : ‖(1 : Complex)‖ - ‖z ^ 4‖ ≤ ‖(1 : Complex) - z ^ 4‖ :=
      norm_sub_norm_le _ _
    rw [norm_one, hz4] at hraw
    simpa using hraw
  have hdenPos : 0 < ‖1 - z‖ := by
    apply norm_pos_iff.mpr
    apply sub_ne_zero.mpr
    simpa [z, eq_comm] using hneq
  have hinv : (1 + r)⁻¹ ≤ ‖1 - z‖⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hdenPos hdenUpper
  have hpowlt : r ^ 4 < 1 := by
    exact pow_lt_one₀ hr0 hr1 (by decide : (4 : Nat) ≠ 0)
  have hbound : (1 - r ^ 4) / (1 + r) ≤ ‖1 - z ^ 4‖ / ‖1 - z‖ := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hbound1 : (1 - r ^ 4) * (1 + r)⁻¹ ≤ ‖1 - z ^ 4‖ * (1 + r)⁻¹ := by
      apply mul_le_mul_of_nonneg_right hnumLower
      positivity
    have hbound2 : ‖1 - z ^ 4‖ * (1 + r)⁻¹ ≤ ‖1 - z ^ 4‖ * ‖1 - z‖⁻¹ := by
      exact mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
    exact le_trans hbound1 hbound2
  have hsharp : (1 - r ^ 4) / (1 + r) = (1 - r) * (1 + r ^ 2) := by
    have hneq' : (1 : Real) + r ≠ 0 := by linarith
    field_simp [hneq']
    ring
  have hnorm : ‖quartetPolynomial r θ‖ = ‖1 - z ^ 4‖ / ‖1 - z‖ := by
    rw [quartetPolynomial_eq_closedForm hneq, norm_div]
  calc
    (1 - r) * (1 + r ^ 2) = (1 - r ^ 4) / (1 + r) := hsharp.symm
    _ ≤ ‖1 - z ^ 4‖ / ‖1 - z‖ := hbound
    _ = ‖quartetPolynomial r θ‖ := hnorm.symm

@[simp] theorem quartetPolynomial_pi (r : Real) :
    quartetPolynomial r Real.pi = (((1 - r) * (1 + r ^ 2) : Real) : Complex) := by
  unfold quartetPolynomial
  rw [radialPhase_pi]
  have hExpand :
      (1 : Complex) + ((-r : Real) : Complex) + ((-r : Real) : Complex) ^ 2 +
          ((-r : Real) : Complex) ^ 3 = ((1 - r + r ^ 2 - r ^ 3 : Real) : Complex) := by
    have hExpandReal :
        (1 : Real) + (-r) + (-r) ^ 2 + (-r) ^ 3 = 1 - r + r ^ 2 - r ^ 3 := by
      ring
    exact_mod_cast hExpandReal
  have hFactor :
      ((1 - r + r ^ 2 - r ^ 3 : Real) : Complex) =
        (((1 - r) * (1 + r ^ 2) : Real) : Complex) := by
    congr 1
    ring
  exact hExpand.trans hFactor

theorem norm_quartetPolynomial_pi {r : Real} (hr1 : r < 1) :
    ‖quartetPolynomial r Real.pi‖ = (1 - r) * (1 + r ^ 2) := by
  rw [quartetPolynomial_pi]
  have hpos : 0 ≤ (1 - r) * (1 + r ^ 2) := by
    have hleft : 0 ≤ 1 - r := by linarith
    have hright : 0 ≤ 1 + r ^ 2 := by positivity
    exact mul_nonneg hleft hright
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]

/-- Coordinate form of the sharp quartet lower bound from the bulk note. -/
theorem routeK_quartet_lower_bound {r θ : Real} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (1 - r) * (1 + r ^ 2) ≤ ‖quartetPolynomial r θ‖ := by
  exact norm_quartetPolynomial_ge_sharp hr0 hr1

/-- The quartet lower bound is attained at `θ = π`. -/
theorem routeK_quartet_sharpness_at_pi {r : Real} (hr1 : r < 1) :
  ‖quartetPolynomial r Real.pi‖ = (1 - r) * (1 + r ^ 2) := by
  exact norm_quartetPolynomial_pi hr1

/-!
Scaffold for the sharpened quartet lower bound.

Primary sources:
- docs/c2_quarteto_resolvente_sharpening.md
-/

end LeanC2
