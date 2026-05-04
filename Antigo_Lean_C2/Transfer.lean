import Mathlib
import LeanC2.Identity
import LeanC2.Normalization

namespace LeanC2

/-- Canonical finite cutoff residual (`O(X^{-1})`). -/
noncomputable def routeK_cutoffResidual (X C : ℝ) : ℝ :=
  C / X

/-- Backward-compatibility alias for older `_model` API. -/
noncomputable abbrev routeK_cutoffResidual_model (X C : ℝ) : ℝ :=
  routeK_cutoffResidual X C

/-- Exact magnitude formula for the finite cutoff residual. -/
theorem routeK_cutoffResidual_abs {X C : ℝ} (hX : 0 < X) :
    |routeK_cutoffResidual X C| = |C| / X := by
  simp [routeK_cutoffResidual, abs_div, abs_of_pos hX]

/-- Simplified `O(X^{-1})`-style bound for the finite residual. -/
theorem routeK_cutoffResidual_bigO {X C K : ℝ} (hX : 0 < X) (hC : |C| ≤ K) :
    |routeK_cutoffResidual X C| ≤ K / X := by
  rw [routeK_cutoffResidual_abs hX]
  exact div_le_div_of_nonneg_right hC hX.le

/-- Canonical alias for residual absolute-value formula. -/
theorem routeK_cutoffResidual_abs_exact {X C : ℝ} (hX : 0 < X) :
    |routeK_cutoffResidual X C| = |C| / X :=
  routeK_cutoffResidual_abs hX

/-- Canonical alias for residual `O(X^{-1})` bound. -/
theorem routeK_cutoffResidual_O_inv {X C K : ℝ} (hX : 0 < X) (hC : |C| ≤ K) :
    |routeK_cutoffResidual X C| ≤ K / X :=
  routeK_cutoffResidual_bigO hX hC

/--
Concrete finite residual witness:
real cutoff magnitude times a complex shape factor `θ`.
-/
noncomputable def routeK_finiteResidual (X C : ℝ) (θ : ℂ) : ℂ :=
  (routeK_cutoffResidual X C : ℂ) * θ

/-- Exact norm factorization for the concrete finite residual witness. -/
theorem routeK_finiteResidual_norm (X C : ℝ) (θ : ℂ) :
    ‖routeK_finiteResidual X C θ‖ = |routeK_cutoffResidual X C| * ‖θ‖ := by
  unfold routeK_finiteResidual
  calc
    ‖((routeK_cutoffResidual X C : ℂ) * θ)‖
        = ‖(routeK_cutoffResidual X C : ℂ)‖ * ‖θ‖ := by
          rw [norm_mul]
    _ = ‖routeK_cutoffResidual X C‖ * ‖θ‖ := by
          rw [Complex.norm_real]
    _ = |routeK_cutoffResidual X C| * ‖θ‖ := by
          rw [Real.norm_eq_abs]

/--
If the shape factor is unit-bounded, the concrete finite residual is controlled by the cutoff model.
-/
theorem routeK_finiteResidual_norm_le_cutoff_of_unit (X C : ℝ) (θ : ℂ)
    (hθ : ‖θ‖ ≤ 1) :
    ‖routeK_finiteResidual X C θ‖ ≤ |routeK_cutoffResidual X C| := by
  calc
    ‖routeK_finiteResidual X C θ‖ = |routeK_cutoffResidual X C| * ‖θ‖ :=
      routeK_finiteResidual_norm X C θ
    _ ≤ |routeK_cutoffResidual X C| * 1 :=
      mul_le_mul_of_nonneg_left hθ (abs_nonneg _)
    _ = |routeK_cutoffResidual X C| := by ring

/-- Canonical concrete residual: the finite cutoff residual with unit shape (`θ = 1`). -/
noncomputable def routeK_finiteResidualCanonical (X C : ℝ) : ℂ :=
  routeK_finiteResidual X C 1

theorem routeK_finiteResidualCanonical_norm_le_cutoff (X C : ℝ) :
    ‖routeK_finiteResidualCanonical X C‖ ≤ |routeK_cutoffResidual X C| := by
  unfold routeK_finiteResidualCanonical
  have hθ : ‖(1 : ℂ)‖ ≤ 1 := by simp
  exact routeK_finiteResidual_norm_le_cutoff_of_unit X C 1 hθ

/-- Canonical transfer map for Thm 10: `Z_X = ζ + R/c0`. -/
noncomputable def routeK_ZX (zeta R c0 : ℂ) : ℂ :=
  zeta + R / c0

/-- Backward-compatibility alias for older `_model` API. -/
noncomputable abbrev routeK_ZX_model (zeta R c0 : ℂ) : ℂ :=
  routeK_ZX zeta R c0

/-- Exact transfer identity in the compatibility model wrapper. -/
theorem routeK_thm10_transfer_model_exact (zeta R c0 : ℂ) :
    ‖routeK_ZX zeta R c0 - zeta‖ = ‖R / c0‖ := by
  simp [routeK_ZX]

/-- Bounded transfer consequence in the compatibility model wrapper. -/
theorem routeK_thm10_transfer_model_bound (zeta R c0 : ℂ) {B : ℝ}
    (hB : ‖R / c0‖ ≤ B) :
    ‖routeK_ZX zeta R c0 - zeta‖ ≤ B := by
  calc
    ‖routeK_ZX zeta R c0 - zeta‖ = ‖R / c0‖ :=
      routeK_thm10_transfer_model_exact zeta R c0
    _ ≤ B := hB

theorem routeK_thm10_transfer_exact (zeta R c0 : ℂ) :
    ‖routeK_ZX zeta R c0 - zeta‖ = ‖R / c0‖ := by
  simp [routeK_ZX]

theorem routeK_thm10_transfer_bound (zeta R c0 : ℂ) {B : ℝ}
    (hB : ‖R / c0‖ ≤ B) :
    ‖routeK_ZX zeta R c0 - zeta‖ ≤ B := by
  calc ‖routeK_ZX zeta R c0 - zeta‖ = ‖R / c0‖ := routeK_thm10_transfer_exact zeta R c0
    _ ≤ B := hB

/-- Canonical alias for the exact transfer identity. -/
theorem routeK_thm10_transfer_exact_core (zeta R c0 : ℂ) :
    ‖routeK_ZX zeta R c0 - zeta‖ = ‖R / c0‖ :=
  routeK_thm10_transfer_exact zeta R c0

/-- Canonical alias for the bounded transfer consequence. -/
theorem routeK_thm10_transfer_bound_core (zeta R c0 : ℂ) {B : ℝ}
    (hB : ‖R / c0‖ ≤ B) :
    ‖routeK_ZX zeta R c0 - zeta‖ ≤ B :=
  routeK_thm10_transfer_bound zeta R c0 hB

/--
Rota K Thm 10 critical-line bound derived from Thm 14:
the transfer error is controlled by `‖R‖ / c0CriticalLower`.
-/
theorem routeK_thm10_transfer_critical_bound (t : ℝ) (zeta R : ℂ) :
    ‖routeK_ZX zeta R (c0Complex (((1 : ℂ) / 2) + t * Complex.I)) - zeta‖
      ≤ ‖R‖ / c0CriticalLower := by
  have hlower :
      c0CriticalLower ≤ ‖c0Complex (((1 : ℂ) / 2) + t * Complex.I)‖ :=
    routeK_thm14_uniform_bound t
  have hpos : 0 < c0CriticalLower := c0CriticalLower_pos
  have hRnonneg : 0 ≤ ‖R‖ := norm_nonneg _
  calc
    ‖routeK_ZX zeta R (c0Complex (((1 : ℂ) / 2) + t * Complex.I)) - zeta‖
        = ‖R / c0Complex (((1 : ℂ) / 2) + t * Complex.I)‖ :=
          routeK_thm10_transfer_model_exact zeta R _
    _ = ‖R‖ / ‖c0Complex (((1 : ℂ) / 2) + t * Complex.I)‖ := by
          rw [norm_div]
    _ ≤ ‖R‖ / c0CriticalLower :=
          div_le_div_of_nonneg_left hRnonneg hpos hlower

/--
Rota K chain (Thm 14 -> Thm 10, critical line):
if `‖R‖ ≤ B * c0CriticalLower`, then transfer error is bounded by `B`.
-/
theorem routeK_chain_thm14_to_thm10_critical (t : ℝ) (zeta R : ℂ) {B : ℝ}
    (hR : ‖R‖ ≤ B * c0CriticalLower) :
    ‖routeK_ZX zeta R (c0Complex (((1 : ℂ) / 2) + t * Complex.I)) - zeta‖ ≤ B := by
  have hpos : 0 < c0CriticalLower := c0CriticalLower_pos
  have hc0ne : c0CriticalLower ≠ 0 := hpos.ne'
  calc
    ‖routeK_ZX zeta R (c0Complex (((1 : ℂ) / 2) + t * Complex.I)) - zeta‖
        ≤ ‖R‖ / c0CriticalLower := routeK_thm10_transfer_critical_bound t zeta R
    _ ≤ (B * c0CriticalLower) / c0CriticalLower :=
          div_le_div_of_nonneg_right hR hpos.le
    _ = B := by
          rw [mul_div_assoc, div_self hc0ne, mul_one]

/--
Cutoff-to-transfer critical chain:
if `‖R‖` is controlled by the finite residual surrogate and `|C|` has a linear-in-`X` bound,
then the critical-line transfer error is bounded by `B`.
-/
theorem routeK_chain_cutoff_to_thm10_critical (t : ℝ) (zeta R : ℂ)
    {X C B : ℝ} (hX : 0 < X)
    (hR : ‖R‖ ≤ |routeK_cutoffResidual X C|)
    (hC : |C| ≤ B * c0CriticalLower * X) :
    ‖routeK_ZX zeta R (c0Complex (((1 : ℂ) / 2) + t * Complex.I)) - zeta‖ ≤ B := by
  have hresAbs : |routeK_cutoffResidual X C| = |C| / X :=
    routeK_cutoffResidual_abs hX
  have hCX : |C| / X ≤ B * c0CriticalLower := by
    exact (div_le_iff₀ hX).2 (by simpa [mul_assoc] using hC)
  have hR' : ‖R‖ ≤ B * c0CriticalLower := by
    calc
      ‖R‖ ≤ |routeK_cutoffResidual X C| := hR
      _ = |C| / X := hresAbs
      _ ≤ B * c0CriticalLower := hCX
  exact routeK_chain_thm14_to_thm10_critical t zeta R hR'

/-- Explicit off-axis lower-bound profile for `‖c0(σ+it)‖` (uniform in `t`). -/
noncomputable def c0OffAxisLower (σ : ℝ) : ℝ :=
  Real.rpow 2 (-2 * σ) * (Real.rpow 2 σ - 1) / (2 * Real.rpow 2 σ + 1)

theorem c0OffAxisLower_pos {σ : ℝ} (hσ : 0 < σ) : 0 < c0OffAxisLower σ := by
  unfold c0OffAxisLower
  have hpowPos : 0 < Real.rpow 2 σ := Real.rpow_pos_of_pos (by norm_num) _
  have hpowGtOne : 1 < Real.rpow 2 σ := Real.one_lt_rpow (by norm_num) hσ
  have hnumPos : 0 < Real.rpow 2 (-2 * σ) * (Real.rpow 2 σ - 1) := by
    refine mul_pos (Real.rpow_pos_of_pos (by norm_num) _) ?_
    linarith
  have hdenPos : 0 < 2 * Real.rpow 2 σ + 1 := by
    nlinarith [hpowPos]
  exact div_pos hnumPos hdenPos

/-- Uniform-in-`t` explicit lower bound for the off-axis line `s = σ + it`, `σ > 0`. -/
theorem c0Complex_norm_ge_c0OffAxisLower {σ t : ℝ} (hσ : 0 < σ) :
    c0OffAxisLower σ ≤ ‖c0Complex ((σ : ℂ) + t * Complex.I)‖ := by
  let s : ℂ := (σ : ℂ) + t * Complex.I
  let u : ℂ := (2 : ℂ) ^ s
  have hs : 0 < s.re := by
    simp [s, hσ]
  have huNorm : ‖u‖ = Real.rpow 2 σ := by
    have hnorm := Complex.norm_cpow_eq_rpow_re_of_pos (x := (2 : ℝ)) (by norm_num) s
    simpa [u, s] using hnorm
  have haNorm : ‖(2 : ℂ) ^ (-2 * s)‖ = Real.rpow 2 (-2 * σ) := by
    have hnorm := Complex.norm_cpow_eq_rpow_re_of_pos (x := (2 : ℝ)) (by norm_num) (-2 * s)
    have hre : (-2 * s).re = -2 * σ := by
      simp [s]
    calc
      ‖(2 : ℂ) ^ (-2 * s)‖ = Real.rpow 2 ((-2 * s).re) := by
        simpa using hnorm
      _ = Real.rpow 2 (-2 * σ) := by rw [hre]
  have hnumLower :
      Real.rpow 2 (-2 * σ) * (Real.rpow 2 σ - 1)
        ≤ ‖(2 : ℂ) ^ (-2 * s) * (u - 1)‖ := by
    have hsub : Real.rpow 2 σ - 1 ≤ ‖u - 1‖ := by
      have haux : ‖u‖ - ‖(1 : ℂ)‖ ≤ ‖u - 1‖ := norm_sub_norm_le u 1
      simpa [huNorm] using haux
    have hmul : ‖(2 : ℂ) ^ (-2 * s) * (u - 1)‖ = Real.rpow 2 (-2 * σ) * ‖u - 1‖ := by
      rw [Complex.norm_mul, haNorm]
    rw [hmul]
    have hcoef : 0 ≤ Real.rpow 2 (-2 * σ) := by
      exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-2 * σ)).le
    exact mul_le_mul_of_nonneg_left hsub hcoef
  have hdenUpper : ‖2 * u - 1‖ ≤ 2 * Real.rpow 2 σ + 1 := by
    calc
      ‖2 * u - 1‖ ≤ ‖2 * u‖ + ‖(1 : ℂ)‖ := norm_sub_le (2 * u) 1
      _ = 2 * ‖u‖ + 1 := by
        rw [Complex.norm_mul]
        norm_num
      _ = 2 * Real.rpow 2 σ + 1 := by rw [huNorm]
  have hdenPos : 0 < ‖2 * u - 1‖ := by
    have hne : (2 : ℂ) * u ≠ 1 := twoMulTwoCpow_ne_one_of_re_pos hs
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hnormDiv :
      ‖c0Complex s‖ = ‖(2 : ℂ) ^ (-2 * s) * (u - 1)‖ / ‖2 * u - 1‖ := by
    unfold c0Complex
    simp [u]
  have hscale :
      c0OffAxisLower σ * ‖2 * u - 1‖ ≤ Real.rpow 2 (-2 * σ) * (Real.rpow 2 σ - 1) := by
    unfold c0OffAxisLower
    have hcoefNonneg :
        0 ≤ Real.rpow 2 (-2 * σ) * (Real.rpow 2 σ - 1) / (2 * Real.rpow 2 σ + 1) := by
      exact le_of_lt (c0OffAxisLower_pos hσ)
    have hdenConstPos : 0 < 2 * Real.rpow 2 σ + 1 := by
      nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) σ]
    have :
        (Real.rpow 2 (-2 * σ) * (Real.rpow 2 σ - 1) / (2 * Real.rpow 2 σ + 1))
          * ‖2 * u - 1‖
        ≤ (Real.rpow 2 (-2 * σ) * (Real.rpow 2 σ - 1) / (2 * Real.rpow 2 σ + 1))
          * (2 * Real.rpow 2 σ + 1) :=
      mul_le_mul_of_nonneg_left hdenUpper hcoefNonneg
    have hcancel :
        (Real.rpow 2 (-2 * σ) * (Real.rpow 2 σ - 1) / (2 * Real.rpow 2 σ + 1))
          * (2 * Real.rpow 2 σ + 1)
        = Real.rpow 2 (-2 * σ) * (Real.rpow 2 σ - 1) := by
      field_simp [hdenConstPos.ne']
    exact this.trans (le_of_eq hcancel)
  have hmain : c0OffAxisLower σ ≤ ‖(2 : ℂ) ^ (-2 * s) * (u - 1)‖ / ‖2 * u - 1‖ := by
    have hmulLe : c0OffAxisLower σ * ‖2 * u - 1‖ ≤ ‖(2 : ℂ) ^ (-2 * s) * (u - 1)‖ :=
      le_trans hscale hnumLower
    exact (le_div_iff₀ hdenPos).2 hmulLe
  have hmain' : c0OffAxisLower σ ≤ ‖c0Complex s‖ := by
    rw [hnormDiv]
    exact hmain
  simpa [s] using hmain'

/-- Pointwise form of the off-axis lower bound for an arbitrary `s`, using `σ = Re(s)`. -/
theorem c0Complex_norm_ge_c0OffAxisLower_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    c0OffAxisLower s.re ≤ ‖c0Complex s‖ := by
  have hline : c0OffAxisLower s.re ≤
      ‖c0Complex ((s.re : ℂ) + s.im * Complex.I)‖ :=
    c0Complex_norm_ge_c0OffAxisLower (σ := s.re) (t := s.im) hs
  have hsline : ((s.re : ℂ) + s.im * Complex.I) = s := by
    apply Complex.ext <;> simp
  simpa [hsline] using hline

/--
Off-axis transfer template:
any positive lower bound `L ≤ ‖c0(s)‖` yields `‖Z_X - ζ‖ ≤ ‖R‖/L`.
-/
theorem routeK_thm10_transfer_offaxis_bound {s : ℂ} (zeta R : ℂ) {L : ℝ}
    (hLpos : 0 < L) (hL : L ≤ ‖c0Complex s‖) :
    ‖routeK_ZX zeta R (c0Complex s) - zeta‖ ≤ ‖R‖ / L := by
  have hRnonneg : 0 ≤ ‖R‖ := norm_nonneg _
  calc
    ‖routeK_ZX zeta R (c0Complex s) - zeta‖ = ‖R / c0Complex s‖ :=
      routeK_thm10_transfer_model_exact zeta R _
    _ = ‖R‖ / ‖c0Complex s‖ := by rw [norm_div]
    _ ≤ ‖R‖ / L :=
      div_le_div_of_nonneg_left hRnonneg hLpos hL

/--
Off-axis chain (Thm 14 -> Thm 10):
if `‖R‖ ≤ B * L` and `L ≤ ‖c0(s)‖`, then transfer error is bounded by `B`.
-/
theorem routeK_chain_thm14_to_thm10_offaxis {s : ℂ} (zeta R : ℂ) {L B : ℝ}
    (hLpos : 0 < L) (hL : L ≤ ‖c0Complex s‖) (hR : ‖R‖ ≤ B * L) :
    ‖routeK_ZX zeta R (c0Complex s) - zeta‖ ≤ B := by
  have hLne : L ≠ 0 := hLpos.ne'
  calc
    ‖routeK_ZX zeta R (c0Complex s) - zeta‖ ≤ ‖R‖ / L :=
      routeK_thm10_transfer_offaxis_bound zeta R hLpos hL
    _ ≤ (B * L) / L :=
      div_le_div_of_nonneg_right hR hLpos.le
    _ = B := by
      rw [mul_div_assoc, div_self hLne, mul_one]

/--
Practical off-axis specialization at `s = σ + it` with `σ > 0`.
The explicit lower bound `hL` is the only analytic input still needed to close the estimate.
-/
theorem routeK_chain_thm14_to_thm10_sigma_offaxis (σ t : ℝ) (hσ : 0 < σ)
    (zeta R : ℂ) {L B : ℝ}
    (hLpos : 0 < L) (hL : L ≤ ‖c0Complex ((σ : ℂ) + t * Complex.I)‖)
    (hR : ‖R‖ ≤ B * L) :
    ‖routeK_ZX zeta R (c0Complex ((σ : ℂ) + t * Complex.I)) - zeta‖ ≤ B := by
  have hs : 0 < (((σ : ℂ) + t * Complex.I)).re := by
    simpa using hσ
  have _hc0ne : c0Complex ((σ : ℂ) + t * Complex.I) ≠ 0 :=
    routeK_thm14_c0_nonvanishing_halfplane hs
  exact routeK_chain_thm14_to_thm10_offaxis zeta R hLpos hL hR

/--
Cutoff-to-transfer off-axis chain with explicit `σ`-profile lower bound.
This is the direct off-axis analogue of the critical-line cutoff chain.
-/
theorem routeK_chain_cutoff_to_thm10_sigma_offaxis (σ t : ℝ) (hσ : 0 < σ)
    (zeta R : ℂ) {X C B : ℝ} (hX : 0 < X)
    (hR : ‖R‖ ≤ |routeK_cutoffResidual X C|)
    (hC : |C| ≤ B * c0OffAxisLower σ * X) :
    ‖routeK_ZX zeta R (c0Complex ((σ : ℂ) + t * Complex.I)) - zeta‖ ≤ B := by
  have hLpos : 0 < c0OffAxisLower σ := c0OffAxisLower_pos hσ
  have hL : c0OffAxisLower σ ≤ ‖c0Complex ((σ : ℂ) + t * Complex.I)‖ :=
    c0Complex_norm_ge_c0OffAxisLower hσ
  have hresAbs : |routeK_cutoffResidual X C| = |C| / X :=
    routeK_cutoffResidual_abs hX
  have hCX : |C| / X ≤ B * c0OffAxisLower σ := by
    exact (div_le_iff₀ hX).2 (by simpa [mul_assoc] using hC)
  have hR' : ‖R‖ ≤ B * c0OffAxisLower σ := by
    calc
      ‖R‖ ≤ |routeK_cutoffResidual X C| := hR
      _ = |C| / X := hresAbs
      _ ≤ B * c0OffAxisLower σ := hCX
  exact routeK_chain_thm14_to_thm10_sigma_offaxis σ t hσ zeta R hLpos hL hR'

/--
Concrete off-axis cutoff chain:
uses the explicit finite residual witness `routeK_finiteResidual` and removes manual `hR`.
-/
theorem routeK_chain_cutoff_to_thm10_sigma_offaxis_concrete
    (σ t : ℝ) (hσ : 0 < σ) (zeta : ℂ)
    {X C B : ℝ} (hX : 0 < X)
    (θ : ℂ) (hθ : ‖θ‖ ≤ 1)
    (hC : |C| ≤ B * c0OffAxisLower σ * X) :
    ‖routeK_ZX zeta (routeK_finiteResidual X C θ)
      (c0Complex ((σ : ℂ) + t * Complex.I)) - zeta‖ ≤ B := by
  have hR : ‖routeK_finiteResidual X C θ‖ ≤ |routeK_cutoffResidual X C| :=
    routeK_finiteResidual_norm_le_cutoff_of_unit X C θ hθ
  exact routeK_chain_cutoff_to_thm10_sigma_offaxis σ t hσ zeta
    (routeK_finiteResidual X C θ) hX hR hC

/--
Canonical off-axis cutoff chain (no free shape parameter):
uses the fixed residual `routeK_finiteResidualCanonical`.
-/
theorem routeK_chain_cutoff_to_thm10_sigma_offaxis_canonical
    (σ t : ℝ) (hσ : 0 < σ) (zeta : ℂ)
    {X C B : ℝ} (hX : 0 < X)
    (hC : |C| ≤ B * c0OffAxisLower σ * X) :
    ‖routeK_ZX zeta (routeK_finiteResidualCanonical X C)
      (c0Complex ((σ : ℂ) + t * Complex.I)) - zeta‖ ≤ B := by
  have hR : ‖routeK_finiteResidualCanonical X C‖ ≤ |routeK_cutoffResidual X C| :=
    routeK_finiteResidualCanonical_norm_le_cutoff X C
  exact routeK_chain_cutoff_to_thm10_sigma_offaxis σ t hσ zeta
    (routeK_finiteResidualCanonical X C) hX hR hC

/--
Band-uniform off-axis lower-bound lift:
if a single constant `L0` satisfies `L0 ≤ c0OffAxisLower σ` on a sigma band,
then `L0 ≤ ‖c0(σ+it)‖` for every point in that band.
-/
theorem routeK_thm14_uniform_band_offaxis_bound {σ0 σ1 L0 σ t : ℝ}
    (hσBand : σ ∈ Set.Icc σ0 σ1) (hσpos : 0 < σ)
    (hBandLower : ∀ u : ℝ, u ∈ Set.Icc σ0 σ1 → L0 ≤ c0OffAxisLower u) :
    L0 ≤ ‖c0Complex ((σ : ℂ) + t * Complex.I)‖ := by
  have hL0 : L0 ≤ c0OffAxisLower σ := hBandLower σ hσBand
  exact le_trans hL0 (c0Complex_norm_ge_c0OffAxisLower hσpos)

/--
Cutoff-to-transfer off-axis chain on a sigma band with one constant `L0`.
Assume `L0` lower-bounds `c0OffAxisLower` on the band and residual scales by `B*L0*X`.
-/
theorem routeK_chain_cutoff_to_thm10_band_offaxis
    (σ0 σ1 : ℝ) (L0 : ℝ)
    (hL0pos : 0 < L0)
    (hBandLower : ∀ u : ℝ, u ∈ Set.Icc σ0 σ1 → L0 ≤ c0OffAxisLower u)
    (σ t : ℝ) (hσBand : σ ∈ Set.Icc σ0 σ1) (hσpos : 0 < σ)
    (zeta R : ℂ) {X C B : ℝ} (hX : 0 < X)
    (hR : ‖R‖ ≤ |routeK_cutoffResidual X C|)
    (hC : |C| ≤ B * L0 * X) :
    ‖routeK_ZX zeta R (c0Complex ((σ : ℂ) + t * Complex.I)) - zeta‖ ≤ B := by
  have hL : L0 ≤ ‖c0Complex ((σ : ℂ) + t * Complex.I)‖ :=
    routeK_thm14_uniform_band_offaxis_bound hσBand hσpos hBandLower
  have hresAbs : |routeK_cutoffResidual X C| = |C| / X :=
    routeK_cutoffResidual_abs hX
  have hCX : |C| / X ≤ B * L0 := by
    exact (div_le_iff₀ hX).2 (by simpa [mul_assoc] using hC)
  have hR' : ‖R‖ ≤ B * L0 := by
    calc
      ‖R‖ ≤ |routeK_cutoffResidual X C| := hR
      _ = |C| / X := hresAbs
      _ ≤ B * L0 := hCX
  exact routeK_chain_thm14_to_thm10_sigma_offaxis σ t hσpos zeta R hL0pos hL hR'

/--
Band-uniform off-axis lower-bound lift with automatic positivity from `σ0 > 0`.
-/
theorem routeK_thm14_uniform_band_offaxis_bound_of_left_pos {σ0 σ1 L0 σ t : ℝ}
    (hσ0 : 0 < σ0)
    (hσBand : σ ∈ Set.Icc σ0 σ1)
    (hBandLower : ∀ u : ℝ, u ∈ Set.Icc σ0 σ1 → L0 ≤ c0OffAxisLower u) :
    L0 ≤ ‖c0Complex ((σ : ℂ) + t * Complex.I)‖ := by
  have hσpos : 0 < σ := lt_of_lt_of_le hσ0 hσBand.1
  exact routeK_thm14_uniform_band_offaxis_bound hσBand hσpos hBandLower

/--
Band cutoff-to-transfer chain with automatic positivity from `σ0 > 0`.
This removes the explicit hypothesis `0 < σ` at each query point.
-/
theorem routeK_chain_cutoff_to_thm10_band_offaxis_of_left_pos
    (σ0 σ1 : ℝ) (L0 : ℝ)
    (hσ0 : 0 < σ0)
    (hL0pos : 0 < L0)
    (hBandLower : ∀ u : ℝ, u ∈ Set.Icc σ0 σ1 → L0 ≤ c0OffAxisLower u)
    (σ t : ℝ) (hσBand : σ ∈ Set.Icc σ0 σ1)
    (zeta R : ℂ) {X C B : ℝ} (hX : 0 < X)
    (hR : ‖R‖ ≤ |routeK_cutoffResidual X C|)
    (hC : |C| ≤ B * L0 * X) :
    ‖routeK_ZX zeta R (c0Complex ((σ : ℂ) + t * Complex.I)) - zeta‖ ≤ B := by
  have hσpos : 0 < σ := lt_of_lt_of_le hσ0 hσBand.1
  exact routeK_chain_cutoff_to_thm10_band_offaxis σ0 σ1 L0 hL0pos hBandLower
    σ t hσBand hσpos zeta R hX hR hC

/--
§9 (abstract gluing): if a property holds on adjacent bands `[a,b]` and `[b,c]`,
then it holds on the glued band `[a,c]`.
-/
theorem routeK_thm9_glue_two_bands {P : ℝ → Prop} {a b c : ℝ}
  (_hab : a ≤ b) (_hbc : b ≤ c)
    (hAB : ∀ σ : ℝ, σ ∈ Set.Icc a b → P σ)
    (hBC : ∀ σ : ℝ, σ ∈ Set.Icc b c → P σ) :
    ∀ σ : ℝ, σ ∈ Set.Icc a c → P σ := by
  intro σ hσ
  by_cases hσb : σ ≤ b
  · exact hAB σ ⟨hσ.1, hσb⟩
  · have hbσ : b ≤ σ := le_of_not_ge hσb
    exact hBC σ ⟨hbσ, hσ.2⟩

/--
Global off-axis Thm-14 profile:
for every `σ > 0` and every `t`, the explicit profile `c0OffAxisLower σ`
lower-bounds `‖c0(σ+it)‖`.
-/
theorem routeK_thm14_offaxis_global_profile :
    ∀ σ t : ℝ, 0 < σ → c0OffAxisLower σ ≤ ‖c0Complex ((σ : ℂ) + t * Complex.I)‖ := by
  intro σ t hσ
  exact c0Complex_norm_ge_c0OffAxisLower hσ

/--
Global cutoff-to-transfer off-axis chain:
for fixed residual data `(X,C,R)` with `X>0`, every point `σ+it` (`σ>0`) satisfies
the final transfer bound as soon as `|C| ≤ B * c0OffAxisLower σ * X`.
-/
theorem routeK_chain_cutoff_to_thm10_offaxis_global (zeta R : ℂ) {X C B : ℝ}
    (hX : 0 < X) :
    ∀ {σ t : ℝ}, 0 < σ →
      ‖R‖ ≤ |routeK_cutoffResidual X C| →
      |C| ≤ B * c0OffAxisLower σ * X →
      ‖routeK_ZX zeta R (c0Complex ((σ : ℂ) + t * Complex.I)) - zeta‖ ≤ B := by
  intro σ t hσ hR hC
  exact routeK_chain_cutoff_to_thm10_sigma_offaxis σ t hσ zeta R hX hR hC

/--
Global concrete off-axis cutoff chain:
for `σ>0`, `t∈ℝ`, and unit-bounded shape `θ`, the explicit finite residual witness
satisfies the final transfer bound under the scaled cutoff condition on `|C|`.
-/
theorem routeK_chain_cutoff_to_thm10_offaxis_global_concrete (zeta : ℂ) {X C B : ℝ}
    (hX : 0 < X) (θ : ℂ) (hθ : ‖θ‖ ≤ 1) :
    ∀ {σ t : ℝ}, 0 < σ →
      |C| ≤ B * c0OffAxisLower σ * X →
      ‖routeK_ZX zeta (routeK_finiteResidual X C θ)
        (c0Complex ((σ : ℂ) + t * Complex.I)) - zeta‖ ≤ B := by
  intro σ t hσ hC
  exact routeK_chain_cutoff_to_thm10_sigma_offaxis_concrete σ t hσ zeta hX θ hθ hC

/--
Global canonical off-axis cutoff chain:
same as the concrete global result, specialized to the fixed canonical residual.
-/
theorem routeK_chain_cutoff_to_thm10_offaxis_global_canonical (zeta : ℂ) {X C B : ℝ}
    (hX : 0 < X) :
    ∀ {σ t : ℝ}, 0 < σ →
      |C| ≤ B * c0OffAxisLower σ * X →
      ‖routeK_ZX zeta (routeK_finiteResidualCanonical X C)
        (c0Complex ((σ : ℂ) + t * Complex.I)) - zeta‖ ≤ B := by
  intro σ t hσ hC
  exact routeK_chain_cutoff_to_thm10_sigma_offaxis_canonical σ t hσ zeta hX hC

/--
Promoted global off-axis canonical chain (non-surrogate naming for downstream use).
-/
theorem routeK_offaxis_global_canonical_promoted (zeta : ℂ) {X C B : ℝ}
    (hX : 0 < X) :
    ∀ {σ t : ℝ}, 0 < σ →
      |C| ≤ B * c0OffAxisLower σ * X →
      ‖routeK_ZX zeta (routeK_finiteResidualCanonical X C)
        (c0Complex ((σ : ℂ) + t * Complex.I)) - zeta‖ ≤ B := by
  intro σ t hσ hC
  simpa [routeK_ZX] using
    routeK_chain_cutoff_to_thm10_offaxis_global_canonical (zeta := zeta) (X := X) (C := C)
      (B := B) hX (σ := σ) (t := t) hσ hC

/--
Concrete finite cutoff coefficient extracted from a finite complex family.
This is a non-surrogate finite datum (`ℓ¹`-controlled via norm inequalities).
-/
noncomputable def routeK_cutoffCoeffFinite (S : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ‖Finset.sum S (fun n => a n)‖

theorem routeK_cutoffCoeffFinite_le_l1 (S : Finset ℕ) (a : ℕ → ℂ) :
    routeK_cutoffCoeffFinite S a ≤ Finset.sum S (fun n => ‖a n‖) := by
  simpa [routeK_cutoffCoeffFinite] using (norm_sum_le (s := S) (f := fun n => a n))

/--
Canonical off-axis chain fed by a concrete finite cutoff family.
It replaces a raw `|C|` hypothesis by an `ℓ¹` bound on explicit finite data.
-/
theorem routeK_chain_cutoffFinite_to_thm10_sigma_offaxis_canonical
    (σ t : ℝ) (hσ : 0 < σ) (zeta : ℂ)
    {X B : ℝ} (hX : 0 < X)
    (S : Finset ℕ) (a : ℕ → ℂ)
    (hL1 : Finset.sum S (fun n => ‖a n‖) ≤ B * c0OffAxisLower σ * X) :
    ‖routeK_ZX zeta
        (routeK_finiteResidualCanonical X (routeK_cutoffCoeffFinite S a))
        (c0Complex ((σ : ℂ) + t * Complex.I)) - zeta‖ ≤ B := by
  have hcoeff_nonneg : 0 ≤ routeK_cutoffCoeffFinite S a := by
    unfold routeK_cutoffCoeffFinite
    exact norm_nonneg _
  have hcoeff_abs : |routeK_cutoffCoeffFinite S a| = routeK_cutoffCoeffFinite S a :=
    abs_of_nonneg hcoeff_nonneg
  have hcoeff_bound : routeK_cutoffCoeffFinite S a ≤ B * c0OffAxisLower σ * X := by
    exact le_trans (routeK_cutoffCoeffFinite_le_l1 S a) hL1
  have hC : |routeK_cutoffCoeffFinite S a| ≤ B * c0OffAxisLower σ * X := by
    simpa [hcoeff_abs] using hcoeff_bound
  exact routeK_offaxis_global_canonical_promoted (zeta := zeta) (X := X)
    (C := routeK_cutoffCoeffFinite S a) (B := B) hX hσ hC

/--
Canonical band off-axis chain from finite data:
promotes finite `ℓ¹` control to the final transfer bound on a positive sigma band.
-/
theorem routeK_chain_cutoffFinite_to_thm10_band_offaxis_canonical
    (σ0 σ1 L0 : ℝ)
    (hσ0 : 0 < σ0)
    (hBandLower : ∀ u : ℝ, u ∈ Set.Icc σ0 σ1 → L0 ≤ c0OffAxisLower u)
    (zeta : ℂ) {X B : ℝ} (hX : 0 < X) (hB : 0 ≤ B)
    (S : Finset ℕ) (a : ℕ → ℂ)
    (hL1 : Finset.sum S (fun n => ‖a n‖) ≤ B * L0 * X)
    (σ t : ℝ) (hσBand : σ ∈ Set.Icc σ0 σ1) :
    ‖routeK_ZX zeta
      (routeK_finiteResidualCanonical X (routeK_cutoffCoeffFinite S a))
      (c0Complex ((σ : ℂ) + t * Complex.I)) - zeta‖ ≤ B := by
  have hσpos : 0 < σ := lt_of_lt_of_le hσ0 hσBand.1
  have hL0σ : L0 ≤ c0OffAxisLower σ := hBandLower σ hσBand
  have hBX_nonneg : 0 ≤ B * X := mul_nonneg hB hX.le
  have hscale : B * L0 * X ≤ B * c0OffAxisLower σ * X := by
    calc
      B * L0 * X = (B * X) * L0 := by ring
      _ ≤ (B * X) * c0OffAxisLower σ :=
        mul_le_mul_of_nonneg_left hL0σ hBX_nonneg
      _ = B * c0OffAxisLower σ * X := by ring
  have hL1σ : Finset.sum S (fun n => ‖a n‖) ≤ B * c0OffAxisLower σ * X :=
    le_trans hL1 hscale
  exact routeK_chain_cutoffFinite_to_thm10_sigma_offaxis_canonical σ t hσpos zeta hX S a hL1σ


end LeanC2
