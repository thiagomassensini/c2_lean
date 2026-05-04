import Mathlib

namespace LeanC2

/-- Unit-modulus phase used in the bulk resolvent model. -/
noncomputable def phaseFactor (θ : Real) : Complex :=
  Complex.exp (θ * Complex.I)

@[simp] theorem norm_phaseFactor (θ : Real) : ‖phaseFactor θ‖ = 1 := by
  simp [phaseFactor, Complex.norm_exp_ofReal_mul_I]

@[simp] theorem phaseFactor_pi : phaseFactor Real.pi = -1 := by
  unfold phaseFactor
  exact Complex.exp_pi_mul_I

/-- Radial point `r e^{i θ}` on the complex plane. -/
noncomputable def radialPhase (r θ : Real) : Complex :=
  (r : Complex) * phaseFactor θ

@[simp] theorem norm_radialPhase {r : Real} (hr : 0 ≤ r) (θ : Real) :
    ‖radialPhase r θ‖ = r := by
  simp [radialPhase, abs_of_nonneg hr]

@[simp] theorem radialPhase_pi (r : Real) : radialPhase r Real.pi = (-r : Real) := by
  simp [radialPhase, phaseFactor_pi]

theorem radialPhase_ne_one_of_lt_one {r : Real} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : Real) :
    radialPhase r θ ≠ 1 := by
  intro h
  have hnorm : ‖radialPhase r θ‖ = 1 := by
    simpa using congrArg norm h
  rw [norm_radialPhase hr0 θ] at hnorm
  linarith

/-- Denominator of the exact central resolvent `T_r(θ) = 1 / (1 - r e^{i θ})`. -/
noncomputable def resolventDenominator (r θ : Real) : Complex :=
  1 - radialPhase r θ

/-- Exact central resolvent used in the bulk-sharpness note. -/
noncomputable def resolventKernel (r θ : Real) : Complex :=
  (resolventDenominator r θ)⁻¹

theorem resolventDenominator_ne_zero_of_lt_one {r : Real}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : Real) :
    resolventDenominator r θ ≠ 0 := by
  intro h
  have hEq : radialPhase r θ = 1 := by
    have := sub_eq_zero.mp h
    simpa [resolventDenominator, eq_comm] using this
  exact radialPhase_ne_one_of_lt_one hr0 hr1 θ hEq

theorem norm_resolventDenominator_le_one_add_r {r : Real} (hr0 : 0 ≤ r) (θ : Real) :
    ‖resolventDenominator r θ‖ ≤ 1 + r := by
  unfold resolventDenominator radialPhase
  calc
    ‖1 - (r : Complex) * phaseFactor θ‖ = ‖(1 : Complex) + -((r : Complex) * phaseFactor θ)‖ := by
      simp [sub_eq_add_neg]
    _ ≤ ‖(1 : Complex)‖ + ‖-((r : Complex) * phaseFactor θ)‖ := norm_add_le _ _
    _ = 1 + r := by simp [abs_of_nonneg hr0]

theorem norm_resolventKernel_ge_inv_one_add_r {r : Real}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : Real) :
    (1 + r)⁻¹ ≤ ‖resolventKernel r θ‖ := by
  have hden0 : resolventDenominator r θ ≠ 0 :=
    resolventDenominator_ne_zero_of_lt_one hr0 hr1 θ
  have hdenPos : 0 < ‖resolventDenominator r θ‖ := norm_pos_iff.mpr hden0
  have hupper : ‖resolventDenominator r θ‖ ≤ 1 + r :=
    norm_resolventDenominator_le_one_add_r hr0 θ
  rw [resolventKernel, norm_inv]
  simpa [one_div] using one_div_le_one_div_of_le hdenPos hupper

@[simp] theorem resolventDenominator_pi (r : Real) :
    resolventDenominator r Real.pi = ((1 + r : Real) : Complex) := by
  simp [resolventDenominator, radialPhase]

theorem norm_resolventKernel_pi {r : Real} (hr0 : 0 ≤ r) :
    ‖resolventKernel r Real.pi‖ = (1 + r)⁻¹ := by
  rw [resolventKernel, resolventDenominator_pi, norm_inv]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 + r)]

/-- Coordinate form of the sharp resolvent lower bound from the bulk note. -/
theorem routeK_resolvent_lower_bound {r θ : Real} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (1 + r)⁻¹ ≤ ‖resolventKernel r θ‖ := by
  exact norm_resolventKernel_ge_inv_one_add_r hr0 hr1 θ

/-- The lower bound is attained at `θ = π`. -/
theorem routeK_resolvent_sharpness_at_pi {r : Real} (hr0 : 0 ≤ r) :
  ‖resolventKernel r Real.pi‖ = (1 + r)⁻¹ := by
  exact norm_resolventKernel_pi hr0

/-!
Scaffold for the quartet resolvent lower bounds.

Primary sources:
- docs/c2_quarteto_resolvente_sharpening.md
-/

end LeanC2
