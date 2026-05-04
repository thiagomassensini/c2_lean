import Mathlib

namespace LeanC2

/-- Real-axis normalization factor used in the C2 identity. -/
noncomputable def c0Real (σ : ℝ) : ℝ :=
  Real.rpow 2 (-2 * σ) * (Real.rpow 2 σ - 1) / (2 * Real.rpow 2 σ - 1)

theorem c0Real_pos_of_sigma_pos {σ : ℝ} (hσ : 0 < σ) : 0 < c0Real σ := by
  unfold c0Real
  have hpowPos : 0 < Real.rpow 2 σ := Real.rpow_pos_of_pos (by norm_num) _
  have hpowGtOne : 1 < Real.rpow 2 σ := Real.one_lt_rpow (by norm_num) hσ
  have hnumPos : 0 < Real.rpow 2 σ - 1 := sub_pos.mpr hpowGtOne
  have hdenPos : 0 < 2 * Real.rpow 2 σ - 1 := by linarith
  exact div_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hnumPos) hdenPos

theorem c0Real_ne_zero_of_sigma_pos {σ : ℝ} (hσ : 0 < σ) : c0Real σ ≠ 0 := by
  exact (c0Real_pos_of_sigma_pos hσ).ne'

/-- Thm-14 real-axis form: `c0` does not vanish on the open right half-line. -/
theorem c0Real_nonvanishing_on_pos : ∀ σ > 0, c0Real σ ≠ 0 := by
  intro σ hσ
  exact c0Real_ne_zero_of_sigma_pos hσ

/-- Explicit positivity at the critical abscissa `σ = 1/2` (real-axis model). -/
theorem c0Real_half_pos : 0 < c0Real ((1 : ℝ) / 2) := by
  exact c0Real_pos_of_sigma_pos (by norm_num)

/-- Non-vanishing at `σ = 1/2` in the real-axis model. -/
theorem c0Real_half_ne_zero : c0Real ((1 : ℝ) / 2) ≠ 0 := by
  exact c0Real_half_pos.ne'

/-- Complex normalization factor used in the full C2 identity. -/
noncomputable def c0Complex (s : ℂ) : ℂ :=
  ((2 : ℂ) ^ (-2 * s)) * (((2 : ℂ) ^ s) - 1) / (2 * ((2 : ℂ) ^ s) - 1)

lemma twoCpow_ne_one_of_re_pos {s : ℂ} (hs : 0 < s.re) : ((2 : ℂ) ^ s) ≠ 1 := by
  intro h
  have hnorm : ‖((2 : ℂ) ^ s)‖ = Real.rpow 2 s.re := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (x := (2 : ℝ)) (by norm_num) s
  have hnormOne : ‖((2 : ℂ) ^ s)‖ = 1 := by
    simp [h]
  have hgt : 1 < ‖((2 : ℂ) ^ s)‖ := by
    rw [hnorm]
    exact Real.one_lt_rpow (by norm_num) hs
  linarith

lemma twoMulTwoCpow_ne_one_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    (2 : ℂ) * ((2 : ℂ) ^ s) ≠ 1 := by
  intro h
  have hnorm : ‖((2 : ℂ) ^ s)‖ = Real.rpow 2 s.re := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (x := (2 : ℝ)) (by norm_num) s
  have hpowGtOne : 1 < ‖((2 : ℂ) ^ s)‖ := by
    rw [hnorm]
    exact Real.one_lt_rpow (by norm_num) hs
  have hmulGtTwo : 2 < ‖(2 : ℂ) * ((2 : ℂ) ^ s)‖ := by
    rw [Complex.norm_mul]
    norm_num
    nlinarith
  have hmulEqOne : ‖(2 : ℂ) * ((2 : ℂ) ^ s)‖ = 1 := by
    simp [h]
  linarith

lemma twoCpow_analyticAt (s : ℂ) : AnalyticAt ℂ (fun z : ℂ => (2 : ℂ) ^ z) s := by
  have htwo : (2 : ℂ) ∈ Complex.slitPlane := by
    simp
  simpa using
    (AnalyticAt.cpow (f := fun _ : ℂ => (2 : ℂ)) (g := fun z : ℂ => z)
      analyticAt_const analyticAt_id htwo)

theorem c0Complex_analyticAt_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ c0Complex s := by
  unfold c0Complex
  have hpow : AnalyticAt ℂ (fun z : ℂ => (2 : ℂ) ^ z) s := twoCpow_analyticAt s
  have hpowNeg : AnalyticAt ℂ (fun z : ℂ => (2 : ℂ) ^ (-2 * z)) s := by
    have hlin : AnalyticAt ℂ (fun z : ℂ => (-2 : ℂ) * z) s :=
      analyticAt_const.mul analyticAt_id
    convert (twoCpow_analyticAt ((-2 : ℂ) * s)).comp hlin using 1
  have hnum : AnalyticAt ℂ (fun z : ℂ => ((2 : ℂ) ^ z) - 1) s :=
    hpow.sub analyticAt_const
  have hden : AnalyticAt ℂ (fun z : ℂ => (2 : ℂ) * ((2 : ℂ) ^ z) - 1) s :=
    (analyticAt_const.mul hpow).sub analyticAt_const
  have hden0 : (2 : ℂ) * ((2 : ℂ) ^ s) - 1 ≠ 0 :=
    sub_ne_zero.mpr (twoMulTwoCpow_ne_one_of_re_pos hs)
  exact (hpowNeg.mul hnum).div hden hden0

/-- Thm-14-style complex non-vanishing in the half-plane `Re(s) > 0`. -/
theorem c0Complex_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : c0Complex s ≠ 0 := by
  unfold c0Complex
  refine div_ne_zero ?_ ?_
  · refine mul_ne_zero ?_ ?_
    · exact (Complex.cpow_ne_zero_iff).2 (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
    · exact sub_ne_zero.mpr (twoCpow_ne_one_of_re_pos hs)
  · exact sub_ne_zero.mpr (twoMulTwoCpow_ne_one_of_re_pos hs)

/-- Critical-line corollary of complex non-vanishing. -/
theorem c0Complex_ne_zero_on_critical (t : ℝ) :
    c0Complex (((1 : ℂ) / 2) + t * Complex.I) ≠ 0 := by
  have hs : 0 < ((((1 : ℂ) / 2) + t * Complex.I)).re := by
    simp
  exact c0Complex_ne_zero_of_re_pos hs

/-- Bridge: on real inputs, complex `c0` matches the real-axis model. -/
theorem c0Complex_ofReal_eq_c0Real (σ : ℝ) :
    c0Complex (σ : ℂ) = (c0Real σ : ℂ) := by
  have h2nonneg : (0 : ℝ) ≤ 2 := by norm_num
  have hpowσ : (2 : ℂ) ^ (σ : ℂ) = ((Real.rpow 2 σ : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow h2nonneg σ).symm
  have hpowm : (2 : ℂ) ^ ((-2 * σ : ℝ) : ℂ) = ((Real.rpow 2 (-2 * σ) : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow h2nonneg (-2 * σ)).symm
  unfold c0Complex c0Real
  rw [show (-2 : ℂ) * (σ : ℂ) = ((-2 * σ : ℝ) : ℂ) by norm_num]
  rw [hpowm, hpowσ]
  simp

/-- Real-axis non-vanishing re-exported from the complex formulation. -/
theorem c0Complex_ofReal_ne_zero_of_pos {σ : ℝ} (hσ : 0 < σ) :
    c0Complex (σ : ℂ) ≠ 0 := by
  exact c0Complex_ne_zero_of_re_pos (by simpa using hσ)

/-- Compatibility corollary: complex non-vanishing implies real non-vanishing. -/
theorem c0Real_ne_zero_of_sigma_pos_via_complex {σ : ℝ} (hσ : 0 < σ) :
    c0Real σ ≠ 0 := by
  intro h0
  have h0c : (c0Real σ : ℂ) = 0 := by exact_mod_cast h0
  have hcz : c0Complex (σ : ℂ) = 0 := by
    simpa [c0Complex_ofReal_eq_c0Real σ] using h0c
  exact (c0Complex_ofReal_ne_zero_of_pos hσ) hcz

/-- Rota K (Thm 14 form): `c0` is nonzero on the half-plane `Re(s) > 0`. -/
theorem routeK_thm14_c0_nonvanishing_halfplane {s : ℂ} (hs : 0 < s.re) :
    c0Complex s ≠ 0 := by
  exact c0Complex_ne_zero_of_re_pos hs

/-- Rota K (Thm 14 critical-line corollary). -/
theorem routeK_thm14_c0_nonvanishing_critical (t : ℝ) :
    c0Complex (((1 : ℂ) / 2) + t * Complex.I) ≠ 0 := by
  exact c0Complex_ne_zero_on_critical t

/-- Rota K (Thm 14 real-axis form): non-vanishing for every `σ > 0`. -/
theorem routeK_thm14_c0Real_nonvanishing_pos {σ : ℝ} (hσ : 0 < σ) :
    c0Real σ ≠ 0 := by
  exact c0Real_ne_zero_of_sigma_pos_via_complex hσ

/-- Explicit lower-bound constant used on the critical line for `‖c0(1/2+it)‖`. -/
noncomputable def c0CriticalLower : ℝ :=
  ((1 : ℝ) / 2) * (Real.rpow 2 ((1 : ℝ) / 2) - 1) / (2 * Real.rpow 2 ((1 : ℝ) / 2) + 1)

theorem c0CriticalLower_pos : 0 < c0CriticalLower := by
  unfold c0CriticalLower
  have hq : 1 < Real.rpow 2 ((1 : ℝ) / 2) := by
    exact Real.one_lt_rpow (by norm_num) (by norm_num)
  have hnum : 0 < ((1 : ℝ) / 2) * (Real.rpow 2 ((1 : ℝ) / 2) - 1) := by
    refine mul_pos (by norm_num) ?_
    linarith
  have hden : 0 < 2 * Real.rpow 2 ((1 : ℝ) / 2) + 1 := by
    nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ((1 : ℝ) / 2)]
  exact div_pos hnum hden

theorem c0Complex_norm_ge_c0CriticalLower (t : ℝ) :
    c0CriticalLower ≤ ‖c0Complex (((1 : ℂ) / 2) + t * Complex.I)‖ := by
  let s : ℂ := ((1 : ℂ) / 2) + t * Complex.I
  let u : ℂ := (2 : ℂ) ^ s
  have hs : 0 < s.re := by
    simp [s]
  have hq : 1 < Real.rpow 2 ((1 : ℝ) / 2) := by
    exact Real.one_lt_rpow (by norm_num) (by norm_num)
  have huNorm : ‖u‖ = Real.rpow 2 ((1 : ℝ) / 2) := by
    have hnorm := Complex.norm_cpow_eq_rpow_re_of_pos (x := (2 : ℝ)) (by norm_num) s
    simpa [u, s] using hnorm
  have haNorm : ‖(2 : ℂ) ^ (-2 * s)‖ = (1 : ℝ) / 2 := by
    have hnorm := Complex.norm_cpow_eq_rpow_re_of_pos (x := (2 : ℝ)) (by norm_num) (-2 * s)
    have hre : (-2 * s).re = (-1 : ℝ) := by
      simp [s]
    calc
      ‖(2 : ℂ) ^ (-2 * s)‖ = Real.rpow 2 ((-2 * s).re) := by
        simpa using hnorm
      _ = Real.rpow 2 (-1 : ℝ) := by rw [hre]
      _ = (1 : ℝ) / 2 := by
        norm_num [Real.rpow_neg_one]
  have hnumLower :
      ((1 : ℝ) / 2) * (Real.rpow 2 ((1 : ℝ) / 2) - 1)
        ≤ ‖(2 : ℂ) ^ (-2 * s) * (u - 1)‖ := by
    have hsub : Real.rpow 2 ((1 : ℝ) / 2) - 1 ≤ ‖u - 1‖ := by
      have haux : ‖u‖ - ‖(1 : ℂ)‖ ≤ ‖u - 1‖ := norm_sub_norm_le u 1
      simpa [huNorm] using haux
    have hmul : ‖(2 : ℂ) ^ (-2 * s) * (u - 1)‖ = ((1 : ℝ) / 2) * ‖u - 1‖ := by
      rw [Complex.norm_mul, haNorm]
    rw [hmul]
    have hcoef : 0 ≤ (1 : ℝ) / 2 := by norm_num
    exact mul_le_mul_of_nonneg_left hsub hcoef
  have hdenUpper : ‖2 * u - 1‖ ≤ 2 * Real.rpow 2 ((1 : ℝ) / 2) + 1 := by
    calc
      ‖2 * u - 1‖ ≤ ‖2 * u‖ + ‖(1 : ℂ)‖ := norm_sub_le (2 * u) 1
      _ = 2 * ‖u‖ + 1 := by
        rw [Complex.norm_mul]
        norm_num
      _ = 2 * Real.rpow 2 ((1 : ℝ) / 2) + 1 := by rw [huNorm]
  have hdenPos : 0 < ‖2 * u - 1‖ := by
    have hne : (2 : ℂ) * u ≠ 1 := twoMulTwoCpow_ne_one_of_re_pos hs
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hnormDiv :
      ‖c0Complex s‖ = ‖(2 : ℂ) ^ (-2 * s) * (u - 1)‖ / ‖2 * u - 1‖ := by
    unfold c0Complex
    simp [u]
  have hscale :
      c0CriticalLower * ‖2 * u - 1‖ ≤ ((1 : ℝ) / 2) * (Real.rpow 2 ((1 : ℝ) / 2) - 1) := by
    unfold c0CriticalLower
    have hcoefNonneg :
        0 ≤
          ((1 : ℝ) / 2) * (Real.rpow 2 ((1 : ℝ) / 2) - 1) /
            (2 * Real.rpow 2 ((1 : ℝ) / 2) + 1) := by
      exact le_of_lt c0CriticalLower_pos
    have hdenConstPos : 0 < 2 * Real.rpow 2 ((1 : ℝ) / 2) + 1 := by
      nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ((1 : ℝ) / 2)]
    have :
        ((1 : ℝ) / 2) * (Real.rpow 2 ((1 : ℝ) / 2) - 1) / (2 * Real.rpow 2 ((1 : ℝ) / 2) + 1)
          * ‖2 * u - 1‖
        ≤ ((1 : ℝ) / 2) * (Real.rpow 2 ((1 : ℝ) / 2) - 1) / (2 * Real.rpow 2 ((1 : ℝ) / 2) + 1)
          * (2 * Real.rpow 2 ((1 : ℝ) / 2) + 1) :=
      mul_le_mul_of_nonneg_left hdenUpper hcoefNonneg
    have hcancel :
        ((1 : ℝ) / 2) * (Real.rpow 2 ((1 : ℝ) / 2) - 1) / (2 * Real.rpow 2 ((1 : ℝ) / 2) + 1)
          * (2 * Real.rpow 2 ((1 : ℝ) / 2) + 1)
        = ((1 : ℝ) / 2) * (Real.rpow 2 ((1 : ℝ) / 2) - 1) := by
      field_simp [hdenConstPos.ne']
    exact this.trans (le_of_eq hcancel)
  have hmain : c0CriticalLower ≤ ‖(2 : ℂ) ^ (-2 * s) * (u - 1)‖ / ‖2 * u - 1‖ := by
    have hmulLe : c0CriticalLower * ‖2 * u - 1‖ ≤ ‖(2 : ℂ) ^ (-2 * s) * (u - 1)‖ :=
      le_trans hscale hnumLower
    exact (le_div_iff₀ hdenPos).2 hmulLe
  have hmain' : c0CriticalLower ≤ ‖c0Complex s‖ := by
    rw [hnormDiv]
    exact hmain
  simpa [s] using hmain'

/-- Rota K Thm 14: explicit uniform lower bound along the critical line. -/
theorem routeK_thm14_uniform_bound (t : ℝ) :
    c0CriticalLower ≤ ‖c0Complex (((1 : ℂ) / 2) + t * Complex.I)‖ := by
  exact c0Complex_norm_ge_c0CriticalLower t

/-- Rota K Thm 14: explicit non-vanishing from the uniform lower bound. -/
theorem routeK_thm14_uniform_nonvanishing (t : ℝ) :
    0 < ‖c0Complex (((1 : ℂ) / 2) + t * Complex.I)‖ := by
  exact lt_of_lt_of_le c0CriticalLower_pos (routeK_thm14_uniform_bound t)


end LeanC2
