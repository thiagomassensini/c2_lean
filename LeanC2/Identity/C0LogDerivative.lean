import Mathlib
import LeanC2.Identity.C0NonZero

namespace LeanC2

/-- Closed-form logarithmic derivative of the normalization factor `c0`. -/
noncomputable def c0LogDerivativeFormula (s : Complex) : Complex :=
  (Real.log 2 : Complex) *
    (-((2 : ℂ)) +
      ((2 : ℂ) ^ s) / (((2 : ℂ) ^ s) - 1) -
      ((2 : ℂ) * ((2 : ℂ) ^ s)) / ((2 : ℂ) * ((2 : ℂ) ^ s) - 1))

/-- The explicit theoretical bound from the analytic certification of `|c0'/c0|` on `Re(s)=1/2`. -/
noncomputable def c0LogDerivativeCriticalBound : ℝ :=
  9 * (4 + Real.sqrt 2) * Real.log 2 / 7

theorem c0LogDerivativeCriticalBound_pos : 0 < c0LogDerivativeCriticalBound := by
  unfold c0LogDerivativeCriticalBound
  have hsqrt : 0 < 4 + Real.sqrt 2 := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem c0LogDerivativeCriticalBound_nonneg : 0 ≤ c0LogDerivativeCriticalBound := by
  exact le_of_lt c0LogDerivativeCriticalBound_pos

theorem logDeriv_twoPow_negTwoMul (s : Complex) :
    logDeriv (fun z : Complex => (2 : Complex) ^ (-2 * z)) s =
      (Real.log 2 : Complex) * (-2 : Complex) := by
  rw [logDeriv_apply, Complex.deriv_const_cpow (by fun_prop) (2 : Complex)]
  have hpow_ne : (2 : Complex) ^ (-2 * s) ≠ 0 := by
    exact (Complex.cpow_ne_zero_iff).2 (Or.inl (by norm_num : (2 : Complex) ≠ 0))
  field_simp [hpow_ne]
  rw [deriv_const_mul_field]
  have hderiv : deriv (fun y : Complex => y) s = 1 := by
    simp
  rw [hderiv]
  have hlog : Complex.log (2 : Complex) = (Real.log 2 : Complex) := by
    simp
  rw [hlog]
  ring

theorem logDeriv_twoPow_sub_one {s : Complex} (hs : 0 < s.re) :
    logDeriv (fun z : Complex => (2 : Complex) ^ z - 1) s =
      (Real.log 2 : Complex) * ((2 : Complex) ^ s) / (((2 : Complex) ^ s) - 1) := by
  rw [logDeriv_apply, deriv_sub_const, Complex.deriv_const_cpow (by fun_prop) (2 : Complex)]
  have hden_ne : ((2 : Complex) ^ s) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (twoCpow_ne_one_of_re_pos hs)
  field_simp [hden_ne]
  simp

theorem logDeriv_twoMulTwoPow_sub_one {s : Complex} (hs : 0 < s.re) :
    logDeriv (fun z : Complex => (2 : Complex) * ((2 : Complex) ^ z) - 1) s =
      (Real.log 2 : Complex) * ((2 : Complex) * ((2 : Complex) ^ s)) /
        (((2 : Complex) * ((2 : Complex) ^ s)) - 1) := by
  rw [logDeriv_apply, deriv_sub_const, deriv_const_mul_field,
    Complex.deriv_const_cpow (by fun_prop) (2 : Complex)]
  have hden_ne : (2 : Complex) * ((2 : Complex) ^ s) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (twoMulTwoCpow_ne_one_of_re_pos hs)
  field_simp [hden_ne]
  simp

/-- Closed-form formula for the logarithmic derivative `c0'/c0` on the open right half-plane. -/
theorem logDeriv_c0_eq_formula {s : Complex} (hs : 0 < s.re) :
    logDeriv c0 s = c0LogDerivativeFormula s := by
  have hpow_ne : (2 : Complex) ^ (-2 * s) ≠ 0 := by
    exact (Complex.cpow_ne_zero_iff).2 (Or.inl (by norm_num : (2 : Complex) ≠ 0))
  have hnum_ne : ((2 : Complex) ^ s) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (twoCpow_ne_one_of_re_pos hs)
  have hden_ne : (2 : Complex) * ((2 : Complex) ^ s) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (twoMulTwoCpow_ne_one_of_re_pos hs)
  unfold c0 c0LogDerivativeFormula
  have hdiv :=
    logDeriv_div (f := fun z : Complex => (2 : Complex) ^ (-2 * z) * ((2 : Complex) ^ z - 1))
      (g := fun z : Complex => (2 : Complex) * ((2 : Complex) ^ z) - 1)
      (x := s) (mul_ne_zero hpow_ne hnum_ne) hden_ne (by fun_prop) (by fun_prop)
  rw [hdiv]
  have hmul :=
    logDeriv_mul (f := fun z : Complex => (2 : Complex) ^ (-2 * z))
      (g := fun z : Complex => (2 : Complex) ^ z - 1)
      (x := s) hpow_ne hnum_ne (by fun_prop) (by fun_prop)
  rw [hmul]
  rw [logDeriv_twoPow_negTwoMul, logDeriv_twoPow_sub_one hs, logDeriv_twoMulTwoPow_sub_one hs]
  ring

theorem norm_twoPow_eq_criticalLine (s : Complex) (hcrit : s.re = (1 : ℝ) / 2) :
    ‖(2 : Complex) ^ s‖ = Real.sqrt 2 := by
  calc
    ‖(2 : Complex) ^ s‖ = (2 : ℝ) ^ s.re := by
      simpa using Complex.norm_cpow_eq_rpow_re_of_pos (x := (2 : Real)) (by norm_num) s
    _ = Real.sqrt 2 := by
      rw [hcrit, ← Real.sqrt_eq_rpow]

theorem norm_twoPow_div_sub_one_le_criticalLine (s : Complex)
    (hcrit : s.re = (1 : ℝ) / 2) :
    ‖((2 : Complex) ^ s) / (((2 : Complex) ^ s) - 1)‖ ≤ 2 + Real.sqrt 2 := by
  let z : Complex := (2 : Complex) ^ s
  have hz_norm : ‖z‖ = Real.sqrt 2 := by
    simpa [z] using norm_twoPow_eq_criticalLine s hcrit
  have hsqrt_pos : 0 < Real.sqrt 2 := by
    exact Real.sqrt_pos.2 (by positivity)
  have hsqrt_gt_one : 1 < Real.sqrt 2 := by
    have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [Real.sqrt_nonneg 2, hsqrt_sq]
  have hbase_pos : 0 < ‖z‖ - 1 := by
    rw [hz_norm]
    linarith
  have hrev : ‖z‖ - ‖(1 : Complex)‖ ≤ ‖z - 1‖ := norm_sub_norm_le z 1
  have hden_lower : ‖z‖ - 1 ≤ ‖z - 1‖ := by
    simpa using hrev
  have hden_pos : 0 < ‖z - 1‖ := lt_of_lt_of_le hbase_pos hden_lower
  have hfrac : ‖z‖ / ‖z - 1‖ ≤ ‖z‖ / (‖z‖ - 1) := by
    have hinv : (‖z - 1‖)⁻¹ ≤ (‖z‖ - 1)⁻¹ := by
      exact (inv_le_inv₀ hden_pos hbase_pos).2 hden_lower
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hinv (norm_nonneg z)
  rw [norm_div]
  have hrat : Real.sqrt 2 / (Real.sqrt 2 - 1) = 2 + Real.sqrt 2 := by
    have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := by
      rw [Real.sq_sqrt]
      positivity
    field_simp [sub_ne_zero.mpr hsqrt_gt_one.ne', hsqrt_pos.ne']
    nlinarith
  calc
    ‖z‖ / ‖z - 1‖ ≤ ‖z‖ / (‖z‖ - 1) := hfrac
    _ = Real.sqrt 2 / (Real.sqrt 2 - 1) := by rw [hz_norm]
    _ = 2 + Real.sqrt 2 := hrat

theorem norm_twoMulTwoPow_div_sub_one_le_criticalLine (s : Complex)
    (hcrit : s.re = (1 : ℝ) / 2) :
    ‖((2 : Complex) * ((2 : Complex) ^ s)) /
      (((2 : Complex) * ((2 : Complex) ^ s)) - 1)‖ ≤ (8 + 2 * Real.sqrt 2) / 7 := by
  let z : Complex := (2 : Complex) ^ s
  let w : Complex := (2 : Complex) * z
  have hz_norm : ‖z‖ = Real.sqrt 2 := by
    simpa [z] using norm_twoPow_eq_criticalLine s hcrit
  have hw_norm : ‖w‖ = 2 * Real.sqrt 2 := by
    dsimp [w]
    rw [norm_mul, hz_norm]
    norm_num
  have hsqrt_pos : 0 < Real.sqrt 2 := by
    exact Real.sqrt_pos.2 (by positivity)
  have hsqrt_gt_one : 1 < Real.sqrt 2 := by
    have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [Real.sqrt_nonneg 2, hsqrt_sq]
  have hbase_pos : 0 < ‖w‖ - 1 := by
    rw [hw_norm]
    nlinarith
  have hrev : ‖w‖ - ‖(1 : Complex)‖ ≤ ‖w - 1‖ := norm_sub_norm_le w 1
  have hden_lower : ‖w‖ - 1 ≤ ‖w - 1‖ := by
    simpa using hrev
  have hden_pos : 0 < ‖w - 1‖ := lt_of_lt_of_le hbase_pos hden_lower
  have hfrac : ‖w‖ / ‖w - 1‖ ≤ ‖w‖ / (‖w‖ - 1) := by
    have hinv : (‖w - 1‖)⁻¹ ≤ (‖w‖ - 1)⁻¹ := by
      exact (inv_le_inv₀ hden_pos hbase_pos).2 hden_lower
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hinv (norm_nonneg w)
  rw [norm_div]
  have hrat : (2 * Real.sqrt 2) / (2 * Real.sqrt 2 - 1) = (8 + 2 * Real.sqrt 2) / 7 := by
    have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := by
      rw [Real.sq_sqrt]
      positivity
    have hden_ne : 2 * Real.sqrt 2 - 1 ≠ 0 := by
      nlinarith [hsqrt_pos]
    field_simp [hden_ne]
    nlinarith
  calc
    ‖w‖ / ‖w - 1‖ ≤ ‖w‖ / (‖w‖ - 1) := hfrac
    _ = (2 * Real.sqrt 2) / (2 * Real.sqrt 2 - 1) := by rw [hw_norm]
    _ = (8 + 2 * Real.sqrt 2) / 7 := hrat

/-- The theoretical critical-line bound for the `c0` logarithmic derivative. -/
theorem norm_c0LogDerivativeFormula_le_criticalBound (s : Complex)
    (hcrit : s.re = (1 : ℝ) / 2) :
    ‖c0LogDerivativeFormula s‖ ≤ c0LogDerivativeCriticalBound := by
  let a : Complex := ((2 : Complex) ^ s) / (((2 : Complex) ^ s) - 1)
  let b : Complex := ((2 : Complex) * ((2 : Complex) ^ s)) /
    (((2 : Complex) * ((2 : Complex) ^ s)) - 1)
  have hlog_nonneg : 0 ≤ Real.log 2 := by
    exact Real.log_nonneg (by norm_num)
  have ha : ‖a‖ ≤ 2 + Real.sqrt 2 := by
    simpa [a] using norm_twoPow_div_sub_one_le_criticalLine s hcrit
  have hb : ‖b‖ ≤ (8 + 2 * Real.sqrt 2) / 7 := by
    simpa [b] using norm_twoMulTwoPow_div_sub_one_le_criticalLine s hcrit
  have hinner : ‖(-((2 : ℂ)) + a) - b‖ ≤ 2 + ‖a‖ + ‖b‖ := by
    calc
      ‖(-((2 : ℂ)) + a) - b‖ ≤ ‖-((2 : ℂ)) + a‖ + ‖b‖ := norm_sub_le _ _
      _ ≤ (‖(-((2 : ℂ)) : Complex)‖ + ‖a‖) + ‖b‖ := by
        gcongr
        exact norm_add_le _ _
      _ = 2 + ‖a‖ + ‖b‖ := by simp
  have hsum : 2 + ‖a‖ + ‖b‖ ≤ 9 * (4 + Real.sqrt 2) / 7 := by
    nlinarith [ha, hb]
  unfold c0LogDerivativeFormula c0LogDerivativeCriticalBound
  calc
    ‖(Real.log 2 : Complex) * (-((2 : ℂ)) + a - b)‖ = Real.log 2 * ‖-((2 : ℂ)) + a - b‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog_nonneg]
    _ ≤ Real.log 2 * (2 + ‖a‖ + ‖b‖) := by
      exact mul_le_mul_of_nonneg_left hinner hlog_nonneg
    _ ≤ Real.log 2 * (9 * (4 + Real.sqrt 2) / 7) := by
      exact mul_le_mul_of_nonneg_left hsum hlog_nonneg
    _ = 9 * (4 + Real.sqrt 2) * Real.log 2 / 7 := by ring

/-- Critical-line specialization of the analytic certification bound for `α(s) = c0'(s) / c0(s)`. -/
theorem norm_logDeriv_c0_le_criticalBound (s : Complex) (hcrit : s.re = (1 : ℝ) / 2) :
    ‖logDeriv c0 s‖ ≤ c0LogDerivativeCriticalBound := by
  have hs : 0 < s.re := by linarith [hcrit]
  rw [logDeriv_c0_eq_formula hs]
  exact norm_c0LogDerivativeFormula_le_criticalBound s hcrit

/-!
Explicit logarithmic-derivative control for the normalization factor `c0`.

Primary sources:
- docs/c2_certificacao_bound_global.md

This module formalizes the `α = c0'/c0` part of the certified global Taylor-radius bound: the
closed form of the logarithmic derivative on the open right half-plane and the explicit theoretical
critical-line estimate used in the near-axis global model.
-/

end LeanC2
