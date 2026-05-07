import LeanC2.Bulk.QuartetSharp
import LeanC2.Identity.FundamentalIdentity
import LeanC2.Identity.MeromorphicExt

namespace LeanC2

/-- The first retained central shell coefficient before summing the geometric tail. -/
noncomputable def firstShellCoeff (s : Complex) : Complex :=
  (2 : Complex) * shellRatio s ^ 2

/-- Critical-line bulk radius from the resolvent note, written as `2^(-3/2)`. -/
noncomputable def bulkCriticalRadius : Real :=
  Real.exp (-((3 : Real) / 2) * Real.log 2)

theorem bulkCriticalRadius_eq_two_rpow_neg_three_halves :
    bulkCriticalRadius = (2 : Real) ^ (-((3 : Real) / 2)) := by
  unfold bulkCriticalRadius
  rw [Real.rpow_def_of_pos (by norm_num : 0 < (2 : Real))]
  congr 1
  ring_nf

theorem bulkCriticalRadius_pos : 0 < bulkCriticalRadius := by
  unfold bulkCriticalRadius
  positivity

theorem bulkCriticalRadius_nonneg : 0 ≤ bulkCriticalRadius :=
  bulkCriticalRadius_pos.le

theorem bulkCriticalRadius_lt_one : bulkCriticalRadius < 1 := by
  rw [bulkCriticalRadius_eq_two_rpow_neg_three_halves]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : Real) < 2) (by norm_num)

/-- The shell ratio in polar coordinates. -/
theorem shellRatio_eq_radialPhase_exp (s : Complex) :
    shellRatio s =
      radialPhase (Real.exp (-(1 + s.re) * Real.log 2)) (-s.im * Real.log 2) := by
  have h2 : (2 : Complex) ≠ 0 := by norm_num
  have hlog : Complex.log (2 : Complex) = (Real.log 2 : Complex) := by
    exact (Complex.ofReal_log (x := 2) (by norm_num : (0 : Real) ≤ 2)).symm
  have hhalf : ((1 : Complex) / 2) = Complex.exp (-(Real.log 2 : Complex)) := by
    calc
      ((1 : Complex) / 2) = ((Real.exp (-Real.log 2) : Real) : Complex) := by
        norm_cast
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : Real) < 2)]
        norm_num
      _ = Complex.exp (((-Real.log 2 : Real) : Complex)) := by
        rw [Complex.ofReal_exp]
      _ = Complex.exp (-(Real.log 2 : Complex)) := by
        congr 1
        norm_num
  unfold shellRatio radialPhase phaseFactor
  calc
    ((1 : Complex) / 2) * (2 : Complex) ^ (-s)
        = Complex.exp (-(Real.log 2 : Complex)) *
          Complex.exp ((Real.log 2 : Complex) * (-s)) := by
          rw [hhalf, Complex.cpow_def_of_ne_zero h2, hlog]
    _ = Complex.exp (-(Real.log 2 : Complex) + (Real.log 2 : Complex) * (-s)) := by
      rw [Complex.exp_add]
    _ = Complex.exp
        (((-(1 + s.re) * Real.log 2 : Real) : Complex) +
          ((-s.im * Real.log 2 : Real) : Complex) * Complex.I) := by
      congr 1
      apply Complex.ext <;> simp [mul_comm] <;> ring
    _ = (Real.exp (-(1 + s.re) * Real.log 2) : Complex) *
        Complex.exp (((-s.im * Real.log 2 : Real) : Complex) * Complex.I) := by
      rw [Complex.exp_add, ← Complex.ofReal_exp]

/-- Critical-line specialization of the shell ratio, matching `r = 2^(-3/2)`. -/
theorem shellRatio_eq_radialPhase_bulkCritical_of_criticalLine
    {s : Complex} (hcrit : s.re = (1 : Real) / 2) :
    shellRatio s = radialPhase bulkCriticalRadius (-s.im * Real.log 2) := by
  rw [shellRatio_eq_radialPhase_exp]
  unfold bulkCriticalRadius
  congr 1
  rw [hcrit]
  ring_nf

/--
Algebraic bridge from the genuine central coefficient to the abstract bulk
resolvent.  The only input is the coordinate identification of the shell ratio
with the radial phase used by `resolventKernel`.
-/
theorem centerCoeff_eq_firstShellCoeff_mul_resolvent_of_shellRatio
    {s : Complex} {r θ : Real}
    (hShell : shellRatio s = radialPhase r θ) :
    centerCoeff s = firstShellCoeff s * resolventKernel r θ := by
  unfold centerCoeff firstShellCoeff resolventKernel resolventDenominator
  rw [hShell]
  simp [div_eq_mul_inv]

/-- Central coefficient written directly in the natural shell polar coordinates. -/
theorem centerCoeff_eq_firstShellCoeff_mul_resolvent_shellCoordinates (s : Complex) :
    centerCoeff s =
      firstShellCoeff s *
        resolventKernel (Real.exp (-(1 + s.re) * Real.log 2)) (-s.im * Real.log 2) := by
  exact centerCoeff_eq_firstShellCoeff_mul_resolvent_of_shellRatio
    (shellRatio_eq_radialPhase_exp s)

/-- Central coefficient on the critical line using the note's fixed radius `r = 2^(-3/2)`. -/
theorem centerCoeff_eq_firstShellCoeff_mul_resolvent_bulkCritical
    {s : Complex} (hcrit : s.re = (1 : Real) / 2) :
    centerCoeff s =
      firstShellCoeff s * resolventKernel bulkCriticalRadius (-s.im * Real.log 2) := by
  exact centerCoeff_eq_firstShellCoeff_mul_resolvent_of_shellRatio
    (shellRatio_eq_radialPhase_bulkCritical_of_criticalLine hcrit)

/--
Analytic-license bridge on the critical line: the continued spectral quotient is the Riemann zeta
channel, while the central coefficient is expressed by the fixed critical resolvent.
-/
theorem criticalLine_resolvent_continuation_bridge
    {numFun : Complex -> Complex}
    (hData : PoleClearedRiemannZetaData numFun)
    {s : Complex} (hcrit : s.re = (1 : Real) / 2) :
    spectralZeta numFun s = riemannZeta s ∧
      centerCoeff s =
        firstShellCoeff s * resolventKernel bulkCriticalRadius (-s.im * Real.log 2) := by
  constructor
  · have hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta :=
      fundamentalIdentity_riemannZeta_on_puncturedRightHalfPlane_of_data hData
    refine fundamentalIdentity_ratio_of_punctured_model hId ?_ ?_
    · rw [hcrit]
      norm_num
    · exact re_lt_one_ne_one (by rw [hcrit]; norm_num)
  · exact centerCoeff_eq_firstShellCoeff_mul_resolvent_bulkCritical hcrit

/-- Critical-line nonvanishing transfer for the continued numerator. -/
theorem criticalLine_continuedNumerator_nonzero_iff_riemannZeta
    {numFun : Complex -> Complex}
    (hData : PoleClearedRiemannZetaData numFun)
    {s : Complex} (hcrit : s.re = (1 : Real) / 2) :
    numFun s ≠ 0 ↔ riemannZeta s ≠ 0 := by
  have hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta :=
    fundamentalIdentity_riemannZeta_on_puncturedRightHalfPlane_of_data hData
  refine fundamentalIdentity_nonzero_iff_of_punctured_model hId ?_ ?_
  · rw [hcrit]
    norm_num
  · exact re_lt_one_ne_one (by rw [hcrit]; norm_num)

/-- Resolvent lower bound at the fixed critical-line bulk radius. -/
theorem routeK_resolvent_lower_bound_bulkCritical (θ : Real) :
    (1 + bulkCriticalRadius)⁻¹ ≤ ‖resolventKernel bulkCriticalRadius θ‖ := by
  exact routeK_resolvent_lower_bound bulkCriticalRadius_nonneg bulkCriticalRadius_lt_one

/-- The critical-line bulk resolvent bound is attained at `θ = π`. -/
theorem routeK_resolvent_sharpness_at_pi_bulkCritical :
    ‖resolventKernel bulkCriticalRadius Real.pi‖ = (1 + bulkCriticalRadius)⁻¹ := by
  exact routeK_resolvent_sharpness_at_pi bulkCriticalRadius_nonneg

/-- Tail left after subtracting the degree-3 quartet from the exact resolvent. -/
noncomputable def resolventTail (r θ : Real) : Complex :=
  resolventKernel r θ - quartetPolynomial r θ

/-- The exact resolvent is the quartet plus its tail. -/
theorem resolventKernel_eq_quartetPolynomial_add_tail (r θ : Real) :
    resolventKernel r θ = quartetPolynomial r θ + resolventTail r θ := by
  unfold resolventTail
  abel

/-- The sharp quartet phase is a global minimum, in the non-unique sense needed for the bound. -/
theorem norm_quartetPolynomial_pi_le {r θ : Real} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ‖quartetPolynomial r Real.pi‖ ≤ ‖quartetPolynomial r θ‖ := by
  rw [norm_quartetPolynomial_pi hr1]
  exact routeK_quartet_lower_bound hr0 hr1

/-- The sharp resolvent phase is a global minimum, in the non-unique sense needed for the bound. -/
theorem norm_resolventKernel_pi_le {r θ : Real} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ‖resolventKernel r Real.pi‖ ≤ ‖resolventKernel r θ‖ := by
  rw [norm_resolventKernel_pi hr0]
  exact routeK_resolvent_lower_bound hr0 hr1

/-- Closed form of the quartet tail from the resolvent note. -/
theorem resolventTail_eq_closedForm {r θ : Real} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    resolventTail r θ = radialPhase r θ ^ 4 / (1 - radialPhase r θ) := by
  let z : Complex := radialPhase r θ
  have hz1 : z ≠ 1 := radialPhase_ne_one_of_lt_one hr0 hr1 θ
  have hden : (1 : Complex) - z ≠ 0 := by
    exact sub_ne_zero.mpr (by simpa [eq_comm, z] using hz1)
  unfold resolventTail resolventKernel resolventDenominator
  rw [quartetPolynomial_eq_closedForm (by simpa [z] using hz1)]
  change (1 - z)⁻¹ - (1 - z ^ 4) / (1 - z) = z ^ 4 / (1 - z)
  field_simp [hden]
  ring

theorem norm_resolventDenominator_ge_one_sub_r {r θ : Real} (hr0 : 0 ≤ r) :
    1 - r ≤ ‖resolventDenominator r θ‖ := by
  have hraw :
      ‖(1 : Complex)‖ - ‖radialPhase r θ‖ ≤
        ‖(1 : Complex) - radialPhase r θ‖ :=
    norm_sub_norm_le _ _
  rw [norm_one, norm_radialPhase hr0 θ] at hraw
  simpa [resolventDenominator] using hraw

/-- Uniform upper bound for the quartet tail. -/
theorem norm_resolventTail_le {r θ : Real} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ‖resolventTail r θ‖ ≤ r ^ 4 / (1 - r) := by
  let z : Complex := radialPhase r θ
  have hz1 : z ≠ 1 := radialPhase_ne_one_of_lt_one hr0 hr1 θ
  have hden : (1 : Complex) - z ≠ 0 := by
    exact sub_ne_zero.mpr (by simpa [eq_comm, z] using hz1)
  have hdenPos : 0 < ‖(1 : Complex) - z‖ := norm_pos_iff.mpr hden
  have honeSubPos : 0 < 1 - r := by linarith
  have hdenLower : 1 - r ≤ ‖(1 : Complex) - z‖ := by
    simpa [resolventDenominator, z] using norm_resolventDenominator_ge_one_sub_r
      (r := r) (θ := θ) hr0
  rw [resolventTail_eq_closedForm hr0 hr1, norm_div]
  have hz4 : ‖radialPhase r θ ^ 4‖ = r ^ 4 := by
    rw [norm_pow, norm_radialPhase hr0 θ]
  rw [hz4]
  exact div_le_div_of_nonneg_left (by positivity) honeSubPos hdenLower

@[simp] theorem radialPhase_zero (r : Real) : radialPhase r 0 = (r : Complex) := by
  simp [radialPhase, phaseFactor]

/-- The quartet tail upper bound is attained at `θ = 0`. -/
theorem norm_resolventTail_zero {r : Real} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ‖resolventTail r 0‖ = r ^ 4 / (1 - r) := by
  rw [resolventTail_eq_closedForm hr0 hr1, radialPhase_zero]
  have hden : (1 : Real) - r ≠ 0 := by linarith
  have hdenC : (1 : Complex) - (r : Complex) ≠ 0 := by
    exact_mod_cast hden
  have honeSubPos : 0 < 1 - r := by linarith
  have hnonneg : 0 ≤ r ^ 4 / (1 - r) := by
    exact div_nonneg (pow_nonneg hr0 4) honeSubPos.le
  have hcomplex :
      ((r : Complex) ^ 4 / (1 - (r : Complex))) =
        ((r ^ 4 / (1 - r) : Real) : Complex) := by
    norm_num [Complex.ofReal_div]
  rw [hcomplex, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]

/-- The tail upper bound is attained at `θ = 0`, so this phase gives a global tail maximum. -/
theorem norm_resolventTail_le_zero {r θ : Real} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ‖resolventTail r θ‖ ≤ ‖resolventTail r 0‖ := by
  calc
    ‖resolventTail r θ‖ ≤ r ^ 4 / (1 - r) := norm_resolventTail_le hr0 hr1
    _ = ‖resolventTail r 0‖ := (norm_resolventTail_zero hr0 hr1).symm

/--
At the sharp resolvent phase `θ = π`, the quartet tail is smaller by the alternating denominator.
-/
theorem norm_resolventTail_pi {r : Real} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ‖resolventTail r Real.pi‖ = r ^ 4 / (1 + r) := by
  rw [resolventTail_eq_closedForm hr0 hr1, radialPhase_pi]
  have hden : (1 : Real) + r ≠ 0 := by linarith
  have hdenC : (1 : Complex) - ((-r : Real) : Complex) ≠ 0 := by
    norm_num
    exact_mod_cast hden
  have hdenPos : 0 < 1 + r := by linarith
  have hnonneg : 0 ≤ r ^ 4 / (1 + r) := by
    exact div_nonneg (pow_nonneg hr0 4) hdenPos.le
  have hcomplex :
      ((((-r : Real) : Complex) ^ 4) / (1 - ((-r : Real) : Complex))) =
        ((r ^ 4 / (1 + r) : Real) : Complex) := by
    norm_num [Complex.ofReal_div]
  rw [hcomplex, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]

/-- At positive radius, the tail at `π` is strictly smaller than the worst tail at `0`. -/
theorem norm_resolventTail_pi_lt_zero {r : Real} (hr0 : 0 < r) (hr1 : r < 1) :
    ‖resolventTail r Real.pi‖ < ‖resolventTail r 0‖ := by
  rw [norm_resolventTail_pi hr0.le hr1, norm_resolventTail_zero hr0.le hr1]
  have hnum : 0 < r ^ 4 := pow_pos hr0 4
  have hdenPlus : 0 < 1 + r := by linarith
  have hdenMinus : 0 < 1 - r := by linarith
  rw [div_lt_div_iff₀ hdenPlus hdenMinus]
  nlinarith

/-- At `π`, the full resolvent is strictly larger than the quartet truncation. -/
theorem norm_quartetPolynomial_pi_lt_norm_resolventKernel_pi
    {r : Real} (hr0 : 0 < r) (hr1 : r < 1) :
    ‖quartetPolynomial r Real.pi‖ < ‖resolventKernel r Real.pi‖ := by
  rw [norm_quartetPolynomial_pi hr1, norm_resolventKernel_pi hr0.le]
  have hden : 0 < 1 + r := by linarith
  have hpow : 0 < r ^ 4 := pow_pos hr0 4
  rw [inv_eq_one_div, lt_div_iff₀ hden]
  have hprod : (1 - r) * (1 + r ^ 2) * (1 + r) = 1 - r ^ 4 := by
    ring
  rw [hprod]
  nlinarith

theorem norm_resolventTail_pi_lt_zero_bulkCritical :
    ‖resolventTail bulkCriticalRadius Real.pi‖ < ‖resolventTail bulkCriticalRadius 0‖ := by
  exact norm_resolventTail_pi_lt_zero bulkCriticalRadius_pos bulkCriticalRadius_lt_one

theorem norm_quartetPolynomial_pi_lt_norm_resolventKernel_pi_bulkCritical :
    ‖quartetPolynomial bulkCriticalRadius Real.pi‖ <
      ‖resolventKernel bulkCriticalRadius Real.pi‖ := by
  exact norm_quartetPolynomial_pi_lt_norm_resolventKernel_pi
    bulkCriticalRadius_pos bulkCriticalRadius_lt_one

/-- The `k = 2` central shell is exactly the first retained shell coefficient times one odd core. -/
theorem centerTerm_two_eq_firstShellCoeff_mul_oddCore (s : Complex) (m : Nat) :
    centerTerm s 2 m =
      firstShellCoeff s * ((((oddCore m : Nat) : Complex) ^ (-s))) := by
  rw [centerTerm_eq_shellRatio_pow_mul_oddCore]
  simp [firstShellCoeff]

/-- One odd-core central tower as first shell times the abstract bulk resolvent. -/
theorem centerTowerCore_eq_firstShellCoeff_mul_resolvent_mul_oddCore
    {s : Complex} (hs : 1 < s.re) (m : Nat) {r θ : Real}
    (hShell : shellRatio s = radialPhase r θ) :
    (∑' j : Nat, centerTerm s (j + 2) m) =
      (firstShellCoeff s * resolventKernel r θ) *
        ((((oddCore m : Nat) : Complex) ^ (-s))) := by
  let q : Complex := shellRatio s
  let b : Complex := (((oddCore m : Nat) : Complex) ^ (-s))
  have hq : ‖q‖ < 1 := by
    simpa [q] using norm_shellRatio_lt_one hs
  have hterm :
      ∀ j : Nat, centerTerm s (j + 2) m = (firstShellCoeff s * q ^ j) * b := by
    intro j
    calc
      centerTerm s (j + 2) m =
          ((2 : Complex) * shellRatio s ^ (j + 2)) *
            ((((oddCore m : Nat) : Complex) ^ (-s))) := by
            rw [centerTerm_eq_shellRatio_pow_mul_oddCore]
      _ = (firstShellCoeff s * q ^ j) * b := by
        simp [firstShellCoeff, q, b, pow_add, mul_left_comm, mul_comm]
  calc
    (∑' j : Nat, centerTerm s (j + 2) m) =
        ∑' j : Nat, (firstShellCoeff s * q ^ j) * b := by
          exact tsum_congr hterm
    _ = (∑' j : Nat, firstShellCoeff s * q ^ j) * b := by
      rw [tsum_mul_right]
    _ = (firstShellCoeff s * (∑' j : Nat, q ^ j)) * b := by
      rw [tsum_mul_left]
    _ = (firstShellCoeff s * (1 - q)⁻¹) * b := by
      rw [tsum_geometric_of_norm_lt_one hq]
    _ = (firstShellCoeff s * resolventKernel r θ) * b := by
      unfold resolventKernel resolventDenominator q
      rw [hShell]
    _ = (firstShellCoeff s * resolventKernel r θ) *
        ((((oddCore m : Nat) : Complex) ^ (-s))) := by
      rfl

/-- One odd-core central tower in the literal "first shell times resolvent" form. -/
theorem centerTowerCore_eq_centerTerm_two_mul_resolvent_of_shellRatio
    {s : Complex} (hs : 1 < s.re) (m : Nat) {r θ : Real}
    (hShell : shellRatio s = radialPhase r θ) :
    (∑' j : Nat, centerTerm s (j + 2) m) =
      centerTerm s 2 m * resolventKernel r θ := by
  rw [centerTowerCore_eq_firstShellCoeff_mul_resolvent_mul_oddCore hs m hShell]
  rw [centerTerm_two_eq_firstShellCoeff_mul_oddCore]
  ring

/-- One odd-core central tower in the natural shell polar coordinates. -/
theorem centerTowerCore_eq_centerTerm_two_mul_resolvent_shellCoordinates
    {s : Complex} (hs : 1 < s.re) (m : Nat) :
    (∑' j : Nat, centerTerm s (j + 2) m) =
      centerTerm s 2 m *
        resolventKernel (Real.exp (-(1 + s.re) * Real.log 2)) (-s.im * Real.log 2) := by
  exact centerTowerCore_eq_centerTerm_two_mul_resolvent_of_shellRatio hs m
    (shellRatio_eq_radialPhase_exp s)

/--
Central infinite tower as a first shell times the exact bulk resolvent and the
odd-core Dirichlet factor, on the convergent right half-plane already
formalized in `FundamentalIdentity`.
-/
theorem centerSeries_eq_firstShellCoeff_mul_resolvent_mul_oddZeta
    {s : Complex} (hs : 1 < s.re) {r θ : Real}
    (hShell : shellRatio s = radialPhase r θ) :
    centerSeries s = (firstShellCoeff s * resolventKernel r θ) * oddZeta s := by
  calc
    centerSeries s = centerCoeff s * oddZeta s :=
      centerSeries_eq_centerCoeff_mul_oddZeta hs
    _ = (firstShellCoeff s * resolventKernel r θ) * oddZeta s := by
      rw [centerCoeff_eq_firstShellCoeff_mul_resolvent_of_shellRatio hShell]

/-- Central infinite tower written directly in the shell polar coordinates. -/
theorem centerSeries_eq_firstShellCoeff_mul_resolvent_shellCoordinates_mul_oddZeta
    {s : Complex} (hs : 1 < s.re) :
    centerSeries s =
      (firstShellCoeff s *
        resolventKernel (Real.exp (-(1 + s.re) * Real.log 2)) (-s.im * Real.log 2)) *
          oddZeta s := by
  exact centerSeries_eq_firstShellCoeff_mul_resolvent_mul_oddZeta hs
    (shellRatio_eq_radialPhase_exp s)

/--
The genuine numerator inherits the same central resolvent form on the
right-half-plane where the cancellation and double-series rearrangements are
already proved.
-/
theorem FInfinity_eq_firstShellCoeff_mul_resolvent_mul_oddZeta
    {s : Complex} (hs : 1 < s.re) {r θ : Real}
    (hShell : shellRatio s = radialPhase r θ) :
    FInfinity s = (firstShellCoeff s * resolventKernel r θ) * oddZeta s := by
  rw [FInfinity_eq_centerSeries_on_right_half_plane hs]
  exact centerSeries_eq_firstShellCoeff_mul_resolvent_mul_oddZeta hs hShell

/-- Genuine numerator written directly in the shell polar coordinates. -/
theorem FInfinity_eq_firstShellCoeff_mul_resolvent_shellCoordinates_mul_oddZeta
    {s : Complex} (hs : 1 < s.re) :
    FInfinity s =
      (firstShellCoeff s *
        resolventKernel (Real.exp (-(1 + s.re) * Real.log 2)) (-s.im * Real.log 2)) *
          oddZeta s := by
  exact FInfinity_eq_firstShellCoeff_mul_resolvent_mul_oddZeta hs
    (shellRatio_eq_radialPhase_exp s)

end LeanC2
