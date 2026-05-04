import Mathlib
import LeanC2.TransversalAnalytic

namespace LeanC2

open Set

/-- Real scalar multiplication on `ℂ` as multiplication by the real scalar. -/
theorem routeK_real_smul_complex (r : ℝ) (z : ℂ) :
    r • z = (r : ℂ) * z := by
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im]

/-!
# Literal Taylor Bounds

This module internalizes the one-variable Taylor estimate used by the Route-K
transversal layer.  It is intentionally independent of any zeta-specific
input: the caller supplies a real slice `f : ℝ → ℂ`, a base point `a`, and a
bound for the second derivative on `[a, a + δ]`.
-/

/--
First-order Taylor polynomial at the left endpoint of a closed interval.

For `x = a + δ`, this is the literal term
`f(a) + δ • f'(a)` used in the transversal Taylor argument.
-/
theorem routeK_taylorWithinEval_one_left
    (f : ℝ → ℂ) (a b x : ℝ) :
    taylorWithinEval f 1 (Icc a b) a x =
      f a + ((x - a : ℝ) : ℂ) * derivWithin f (Icc a b) a := by
  rw [show (1 : ℕ) = 0 + 1 by rfl]
  simp only [zero_add, taylorWithinEval_succ, taylor_within_zero_eval,
    CharP.cast_eq_zero, Nat.factorial_zero, Nat.cast_one, mul_one, inv_one,
    pow_one, one_mul, iteratedDerivWithin_one, Complex.ofReal_sub, add_right_inj]
  calc
    (x - a) • derivWithin f (Icc a b) a =
        ((x - a : ℝ) : ℂ) * derivWithin f (Icc a b) a :=
      routeK_real_smul_complex (x - a) _
    _ = (↑x - ↑a) * derivWithin f (Icc a b) a := by simp

/--
Literal right-hand Taylor lower bound.

If `f(a) = 0`, `f'(a) = F₁`, and the second derivative is bounded by `C₂`
on `[a, a + δ]`, then

`δ * ‖F₁‖ - δ^2 / 2 * (2*C₂) ≤ ‖f(a+δ)‖`.

The factor `2*C₂` matches the `δ²/2 * M₂` normalization used by the C₂
Taylor-dominance API.
-/
theorem routeK_taylor_right_lower_bound_of_second_deriv_bound
    {f : ℝ → ℂ} {a δ C₂ : ℝ} {F₁ : ℂ}
    (hδ : 0 < δ)
    (hf : ContDiffOn ℝ 2 f (Icc a (a + δ)))
    (hSecond :
      ∀ y ∈ Icc a (a + δ),
        ‖iteratedDerivWithin 2 f (Icc a (a + δ)) y‖ ≤ C₂)
    (hzero : f a = 0)
    (hDeriv : derivWithin f (Icc a (a + δ)) a = F₁) :
    δ * ‖F₁‖ - δ ^ 2 / 2 * (2 * C₂) ≤ ‖f (a + δ)‖ := by
  have hle : a ≤ a + δ := by linarith
  have hx : a + δ ∈ Icc a (a + δ) := by
    exact right_mem_Icc.mpr hle
  have hTaylor :=
    taylor_mean_remainder_bound
      (f := f) (a := a) (b := a + δ) (C := C₂) (x := a + δ)
      (n := 1) hle hf hx hSecond
  have hPoly :
      taylorWithinEval f 1 (Icc a (a + δ)) a (a + δ) = (δ : ℂ) * F₁ := by
    rw [routeK_taylorWithinEval_one_left, hzero, hDeriv]
    simp
  have hR :
      ‖f (a + δ) - (δ : ℂ) * F₁‖ ≤ C₂ * δ ^ 2 := by
    have hPow : (a + δ - a) ^ (1 + 1) = δ ^ 2 := by ring
    have hFact : (Nat.factorial 1 : ℝ) = 1 := by norm_num
    have hTaylor' :
        ‖f (a + δ) - taylorWithinEval f 1 (Icc a (a + δ)) a (a + δ)‖ ≤
          C₂ * δ ^ 2 := by
      simpa [hPow, hFact] using hTaylor
    simpa [hzero, hDeriv, routeK_real_smul_complex] using hTaylor'
  have hTriangle :
      ‖(δ : ℂ) * F₁‖ ≤ ‖f (a + δ)‖ + ‖f (a + δ) - (δ : ℂ) * F₁‖ := by
    have h := norm_add_le (f (a + δ)) ((δ : ℂ) * F₁ - f (a + δ))
    have hEq : f (a + δ) + ((δ : ℂ) * F₁ - f (a + δ)) = (δ : ℂ) * F₁ := by
      abel
    simpa [hEq, norm_sub_rev] using h
  have hMain :
      ‖(δ : ℂ) * F₁‖ - C₂ * δ ^ 2 ≤ ‖f (a + δ)‖ := by
    linarith
  have hNorm : ‖(δ : ℂ) * F₁‖ = δ * ‖F₁‖ := by
    rw [Complex.norm_mul]
    simp [abs_of_pos hδ]
  have hQuadratic : δ ^ 2 / 2 * (2 * C₂) = C₂ * δ ^ 2 := by
    ring
  rw [hQuadratic, ← hNorm]
  exact hMain

/--
The literal Taylor lower bound packaged directly as a plain C₂
Taylor-dominance witness with zero residual.
-/
theorem routeK_OffAxisTaylorDominanceAt_of_realSlice_second_deriv_bound
    {Dinf Binf : ℂ → ℂ} {s : ℂ}
    {f : ℝ → ℂ} {a δ C₂ : ℝ} {F₁ : ℂ}
    (hPoint : Dinf s - Binf s = f (a + δ))
    (hδ : 0 < δ)
    (hF₁ : 0 < ‖F₁‖)
    (hC₂ : 0 < C₂)
    (hf : ContDiffOn ℝ 2 f (Icc a (a + δ)))
    (hSecond :
      ∀ y ∈ Icc a (a + δ),
        ‖iteratedDerivWithin 2 f (Icc a (a + δ)) y‖ ≤ C₂)
    (hzero : f a = 0)
    (hDeriv : derivWithin f (Icc a (a + δ)) a = F₁)
    (hδsmall : δ < 2 * ‖F₁‖ / (2 * C₂)) :
    routeK_OffAxisTaylorDominanceAt Dinf Binf s := by
  refine ⟨‖F₁‖, 2 * C₂, 0, δ, hF₁, by linarith, hδ, hδsmall,
    by norm_num, ?_, ?_⟩
  · simpa using routeK_elo5_firstorder_dominates
      ‖F₁‖ (2 * C₂) δ hF₁ (by linarith) hδ hδsmall
  · have hLower :=
      routeK_taylor_right_lower_bound_of_second_deriv_bound
        (f := f) (a := a) (δ := δ) (C₂ := C₂) (F₁ := F₁)
        hδ hf hSecond hzero hDeriv
    simpa [hPoint] using hLower

end LeanC2
