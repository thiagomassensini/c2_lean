import Mathlib
import LeanC2.Identity.C0

set_option linter.style.whitespace false

namespace LeanC2

/-- Real-axis normalization factor used in the C2 identity. -/
noncomputable def c0Real (sigma : Real) : Real :=
  Real.rpow 2 (-2 * sigma) * (Real.rpow 2 sigma - 1) / (2 * Real.rpow 2 sigma - 1)

theorem c0Real_pos_of_sigma_pos {sigma : Real} (hsigma : 0 < sigma) : 0 < c0Real sigma := by
  unfold c0Real
  have hpowGtOne : 1 < Real.rpow 2 sigma := Real.one_lt_rpow (by norm_num) hsigma
  have hnumPos : 0 < Real.rpow 2 sigma - 1 := sub_pos.mpr hpowGtOne
  have hdenPos : 0 < 2 * Real.rpow 2 sigma - 1 := by linarith
  exact div_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hnumPos) hdenPos

theorem c0Real_ne_zero_of_sigma_pos {sigma : Real} (hsigma : 0 < sigma) :
    c0Real sigma ≠ 0 := by
  exact (c0Real_pos_of_sigma_pos hsigma).ne'

lemma twoCpow_ne_one_of_re_pos {s : Complex} (hs : 0 < s.re) : ((2 : Complex) ^ s) ≠ 1 := by
  intro h
  have hnorm : ‖((2 : Complex) ^ s)‖ = Real.rpow 2 s.re := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (x := (2 : Real)) (by norm_num) s
  have hnormOne : ‖((2 : Complex) ^ s)‖ = 1 := by
    simp [h]
  have hgt : 1 < ‖((2 : Complex) ^ s)‖ := by
    rw [hnorm]
    exact Real.one_lt_rpow (by norm_num) hs
  linarith

lemma twoMulTwoCpow_ne_one_of_re_pos {s : Complex} (hs : 0 < s.re) :
    (2 : Complex) * ((2 : Complex) ^ s) ≠ 1 := by
  intro h
  have hnorm : ‖((2 : Complex) ^ s)‖ = Real.rpow 2 s.re := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (x := (2 : Real)) (by norm_num) s
  have hpowGtOne : 1 < ‖((2 : Complex) ^ s)‖ := by
    rw [hnorm]
    exact Real.one_lt_rpow (by norm_num) hs
  have hmulGtTwo : 2 < ‖(2 : Complex) * ((2 : Complex) ^ s)‖ := by
    rw [Complex.norm_mul]
    norm_num
    nlinarith
  have hmulEqOne : ‖(2 : Complex) * ((2 : Complex) ^ s)‖ = 1 := by
    simp [h]
  linarith

/-- Thm 14 style nonvanishing on the half-plane `Re(s) > 0`. -/
theorem c0_ne_zero_of_re_pos {s : Complex} (hs : 0 < s.re) : c0 s ≠ 0 := by
  unfold c0
  refine div_ne_zero ?_ ?_
  · refine mul_ne_zero ?_ ?_
    · exact (Complex.cpow_ne_zero_iff).2 (Or.inl (by norm_num : (2 : Complex) ≠ 0))
    · exact sub_ne_zero.mpr (twoCpow_ne_one_of_re_pos hs)
  · exact sub_ne_zero.mpr (twoMulTwoCpow_ne_one_of_re_pos hs)

/-- Critical-line corollary of the half-plane nonvanishing. -/
theorem c0_ne_zero_on_critical (t : Real) :
    c0 (((1 : Complex) / 2) + t * Complex.I) ≠ 0 := by
  have hs : 0 < ((((1 : Complex) / 2) + t * Complex.I)).re := by
    simp
  exact c0_ne_zero_of_re_pos hs

/-- On real inputs, the complex `c0` matches the real-axis model. -/
theorem c0_ofReal_eq_c0Real (sigma : Real) :
    c0 (sigma : Complex) = (c0Real sigma : Complex) := by
  have h2nonneg : (0 : Real) <= 2 := by
    norm_num
  have hpowSigma :
      (2 : Complex) ^ (sigma : Complex) = ((Real.rpow 2 sigma : Real) : Complex) := by
    simpa using (Complex.ofReal_cpow h2nonneg sigma).symm
  have hpowM :
      (2 : Complex) ^ ((-2 * sigma : Real) : Complex) =
        ((Real.rpow 2 (-2 * sigma) : Real) : Complex) := by
    simpa using (Complex.ofReal_cpow h2nonneg (-2 * sigma)).symm
  unfold c0 c0Real
  rw [show (-2 : Complex) * (sigma : Complex) = ((-2 * sigma : Real) : Complex) by norm_num]
  rw [hpowM, hpowSigma]
  simp

/-- Real-axis corollary re-exported from the complex nonvanishing. -/
theorem c0_ofReal_ne_zero_of_pos {sigma : Real} (hsigma : 0 < sigma) :
    c0 (sigma : Complex) ≠ 0 := by
  exact c0_ne_zero_of_re_pos (by simpa using hsigma)

/-- Compatibility corollary: complex nonvanishing implies the real-axis model is nonzero. -/
theorem c0Real_ne_zero_of_sigma_pos_via_complex {sigma : Real} (hsigma : 0 < sigma) :
    c0Real sigma ≠ 0 := by
  intro h0
  have h0c : (c0Real sigma : Complex) = 0 := by
    exact_mod_cast h0
  have hcz : c0 (sigma : Complex) = 0 := by
    simpa [c0_ofReal_eq_c0Real sigma] using h0c
  exact (c0_ofReal_ne_zero_of_pos hsigma) hcz

/-- Rota K name for Thm 14 on the open right half-plane. -/
theorem routeK_thm14_c0_nonvanishing_halfplane {s : Complex} (hs : 0 < s.re) :
    c0 s ≠ 0 := by
  exact c0_ne_zero_of_re_pos hs

/-- Rota K critical-line corollary of Thm 14. -/
theorem routeK_thm14_c0_nonvanishing_critical (t : Real) :
    c0 (((1 : Complex) / 2) + t * Complex.I) ≠ 0 := by
  exact c0_ne_zero_on_critical t

/-!
Thm 14: nonvanishing of `c0` on the open right half-plane.

Primary sources:
- docs/algebra_Z_igual_zeta.md

Legacy seeds:
- Lean/Antigo_Lean_C2/Normalization.lean
-/

end LeanC2