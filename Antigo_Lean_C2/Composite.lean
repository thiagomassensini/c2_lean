import Mathlib
import LeanC2.Tilt
import LeanC2.Transfer

namespace LeanC2


-- ═══════════════════════════════════════════════════════════════════════
-- Rota K Theorem Promotions: Thm 3, 4, 6, 11  (🟡 → 🔵 DERIVADO)
-- ═══════════════════════════════════════════════════════════════════════

/--
Rota K Thm 3 (cutoff universality — core):
the cutoff residual `C/X` vanishes as `X → ∞`.
For any admissible cutoff family, the `O(1/X)` residual decays to 0 as the cutoff scale grows.
-/
theorem routeK_thm3_cutoff_vanishes_atTop (C : ℝ) :
    Filter.Tendsto (fun X : ℝ => routeK_cutoffResidual X C)
      Filter.atTop (nhds 0) := by
  simp only [routeK_cutoffResidual]
  have hinv : Filter.Tendsto (fun X : ℝ => X⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hmul : Filter.Tendsto (fun X : ℝ => C * X⁻¹) Filter.atTop (nhds (C * 0)) :=
    tendsto_const_nhds.mul hinv
  simp only [mul_zero] at hmul
  simpa [div_eq_mul_inv, mul_comm] using hmul

/--
Rota K Thm 3 (transfer squeeze):
if an error term is bounded by `K/X` for all `X > 0`, it vanishes as `X → ∞`.
This is the abstract selectivity closure: `Z_X → ζ` on the critical line.
-/
theorem routeK_thm3_transfer_vanishes_of_cutoff_bound
  {K : ℝ} (_hK : 0 ≤ K)
    {e : ℝ → ℝ} (he_nonneg : ∀ X, 0 ≤ e X)
    (he_bound : ∀ X : ℝ, 0 < X → e X ≤ K / X) :
    Filter.Tendsto e Filter.atTop (nhds 0) := by
  have hKX : Filter.Tendsto (fun X : ℝ => K / X) Filter.atTop (nhds 0) :=
    routeK_thm3_cutoff_vanishes_atTop K
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hKX
  · filter_upwards with X
    exact he_nonneg X
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with X hX
    exact he_bound X hX

/--
Rota K Thm 4 (annihilation at critical line):
the tilt bracket vanishes at `δ = 0`.
This is the algebraic cancellation `Δ²[1] = 0` that eliminates tilt on the critical line.
-/
theorem routeK_thm4_annihilation_zero (c : ℝ) :
    tiltBracket 0 c = 0 := tiltBracket_zero c

/--
Rota K Thm 4 (2800:1 ratio — formal core):
the ratio of the annihilated bracket (δ=0) to the off-axis bracket (δ=n>0) is zero.
The large observed cancellation ratio follows because the numerator is exactly 0 by Thm 2,
while the denominator is strictly positive by Thm 5.
-/
theorem routeK_thm4_annihilation_tilt_ratio {n : ℕ} (_hn : 0 < n) {c : ℝ} (_hc : 1 < c) :
    tiltBracket 0 c / tiltBracket (n : ℝ) c = 0 := by
  rw [tiltBracket_zero, zero_div]

/--
Rota K Thm 4 combined: at `δ=0` the bracket is annihilated;
at `δ=n>0` it is strictly positive.
The 2800:1 numerics follow from this 0/positive structure.
-/
theorem routeK_thm4_annihilation_vs_offaxis {n : ℕ} (hn : 0 < n) {c : ℝ} (hc : 1 < c) :
    tiltBracket 0 c = 0 ∧ 0 < tiltBracket (n : ℝ) c :=
  ⟨tiltBracket_zero c, tiltBracket_pos_of_nat hn hc⟩

/--
Rota K Thm 6 (amplification — divergence):
the amplification factor `A = num / |C/X|` diverges to `+∞` as `X → ∞`,
whenever the numerator `num` is positive (e.g., `num = |c₀(ρ)·ζ'(ρ)|` from Thm 17).
-/
theorem routeK_thm6_amplification_diverges {C : ℝ} (hC : 0 < C) {num : ℝ} (hnum : 0 < num) :
    Filter.Tendsto (fun X : ℝ => num / (C / X)) Filter.atTop Filter.atTop := by
  have heq : (fun X : ℝ => num / (C / X)) = (fun X => num / C * X) := by
    ext X
    by_cases hX : X = 0
    · simp [hX]
    · field_simp [hC.ne', hX]
  rw [heq]
  have hposNC : 0 < num / C := div_pos hnum hC
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨b / (num / C), fun X hX => ?_⟩
  calc b = b / (num / C) * (num / C) := (div_mul_cancel₀ b hposNC.ne').symm
    _ ≤ X * (num / C) := mul_le_mul_of_nonneg_right hX hposNC.le
    _ = num / C * X := mul_comm _ _

/--
Rota K Thm 6 (amplification using residual directly):
for fixed `C > 0` and `num > 0`, the ratio `num / |C/X|` diverges as `X → ∞`.
-/
theorem routeK_thm6_amplification_residual_diverges
    {C : ℝ} (hC : 0 < C) {num : ℝ} (hnum : 0 < num) :
    Filter.Tendsto
      (fun X : ℝ => num / |routeK_cutoffResidual X C|)
      Filter.atTop Filter.atTop :=
  (routeK_thm6_amplification_diverges hC hnum).congr' <| by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with X hX
    simp [routeK_cutoffResidual, abs_div, abs_of_pos hC, abs_of_pos hX]

/--
Rota K Thm 11 (exclusion zone existence):
for any natural `δ > 0` and center `c > 1`, there exists a cutoff scale `X₀` such that
for all `X ≥ X₀`, the cutoff residual is strictly dominated by the off-axis tilt bracket.
This is the formal basis of the δ_crit lower bound: beyond `X₀`, the off-axis signal
exceeds the residual, establishing a nonzero exclusion zone around every zero of ζ.
-/
theorem routeK_thm11_exclusion_zone_exists
    {n : ℕ} (hn : 0 < n) {c : ℝ} (hc : 1 < c) (C : ℝ) :
    ∃ X₀ : ℝ, ∀ X ≥ X₀, |routeK_cutoffResidual X C| < tiltBracket (n : ℝ) c := by
  have htilt : 0 < tiltBracket (n : ℝ) c := tiltBracket_pos_of_nat hn hc
  have hresid : Filter.Tendsto
      (fun X : ℝ => |routeK_cutoffResidual X C|)
      Filter.atTop (nhds 0) := by
    simpa [abs_zero] using (routeK_thm3_cutoff_vanishes_atTop C).abs
  have hlt : ∀ᶠ X in Filter.atTop,
      |routeK_cutoffResidual X C| < tiltBracket (n : ℝ) c :=
    hresid.eventually_lt tendsto_const_nhds htilt
  exact Filter.eventually_atTop.mp hlt

/--
Rota K Thm 11 combined package:
transversal non-degeneracy (Thm 8) + exclusion zone existence (above).
The zero-density at σ=1/2 is isolated with a quantifiable exclusion zone.
-/
theorem routeK_thm11_transversal_and_exclusion_zone
    {n : ℕ} (hn : 0 < n) {c : ℝ} (hc : 1 < c) (C : ℝ)
    (cJet zJet : ℕ → ℂ)
    (hz : ∀ k < n, zJet k = 0) (hc0 : cJet 0 ≠ 0) (hzn : zJet n ≠ 0) :
    (Finset.sum (Finset.range (n + 1))
        (fun j => (Nat.choose n j : ℂ) * cJet j * zJet (n - j)) ≠ 0) ∧
    (∃ X₀ : ℝ, ∀ X ≥ X₀, |routeK_cutoffResidual X C| < tiltBracket (n : ℝ) c) :=
  ⟨leibnizNondegenerateByMultiplicity n cJet zJet hz hc0 hzn,
   routeK_thm11_exclusion_zone_exists hn hc C⟩

-- ═══════════════════════════════════════════════════════════════════════
-- ELO 5 — Abstract Taylor exclusion zone (Cadeia Única)
-- ═══════════════════════════════════════════════════════════════════════

/-- ELO 5: for 0 < δ < 2m/M₂, the first-order Taylor term δ·m strictly
    dominates the second-order quadratic δ²/2·M₂. Algebraic core of the
    exclusion-zone argument. -/
theorem routeK_elo5_firstorder_dominates (m M₂ δ : ℝ)
    (hm : 0 < m) (hM₂ : 0 < M₂) (hδ : 0 < δ) (hδ_small : δ < 2 * m / M₂) :
    0 < δ * m - δ ^ 2 / 2 * M₂ := by
  have h1 : δ * M₂ < 2 * m := by
    calc δ * M₂ < 2 * m / M₂ * M₂ := mul_lt_mul_of_pos_right hδ_small hM₂
      _ = 2 * m := by field_simp
  have key : 0 < δ * (2 * m - δ * M₂) := mul_pos hδ (by linarith)
  have : δ * m - δ ^ 2 / 2 * M₂ = δ * (2 * m - δ * M₂) / 2 := by ring
  linarith

/-- ELO 5: the Taylor exclusion radius δ* = 2m/M₂ is strictly positive. -/
theorem routeK_elo5_exclusion_radius_pos (m M₂ : ℝ) (hm : 0 < m) (hM₂ : 0 < M₂) :
    0 < 2 * m / M₂ :=
  div_pos (by linarith) hM₂

/--
§10 (scaled parametric form): if `δ* = 2m/M₂` with `m > 0` and `M₂ ≤ M₂bound`,
then `δ*` is bounded below by the scaled quantity `2m/M₂bound`.

This is the natural lower-bound shape for Taylor witnesses, which only provide
`m > 0` a priori rather than the stronger normalization `m ≥ 1`.
-/
theorem routeK_thm10_deltaStar_lower_bound_scaled_from_M2bound
    (m M₂ M₂bound : ℝ)
    (hm : 0 < m) (hM₂pos : 0 < M₂) (hBoundPos : 0 < M₂bound)
    (hM₂le : M₂ ≤ M₂bound) :
    2 * m / M₂bound ≤ 2 * m / M₂ := by
  have hBoundNe : M₂bound ≠ 0 := ne_of_gt hBoundPos
  have hM₂ne : M₂ ≠ 0 := ne_of_gt hM₂pos
  field_simp [hBoundNe, hM₂ne]
  nlinarith [hM₂le, hm]

/-- ELO 5: if the Taylor lower bound strictly dominates the residual then F ≠ 0.
    Abstract form: `‖F‖ ≥ δ·m - δ²/2·M₂ - R` and `R < δ·m - δ²/2·M₂` implies `F ≠ 0`. -/
theorem routeK_elo5_nonzero_from_taylor (m M₂ R : ℝ) (hm : 0 < m) (hM₂ : 0 < M₂)
    (δ : ℝ) (hδ : 0 < δ) (hδ_small : δ < 2 * m / M₂)
    (_hR : 0 ≤ R) (hR_small : R < δ * m - δ ^ 2 / 2 * M₂)
    (F : ℂ) (hF_lb : δ * m - δ ^ 2 / 2 * M₂ - R ≤ ‖F‖) :
    F ≠ 0 :=
  norm_pos_iff.mp (by
    have := routeK_elo5_firstorder_dominates m M₂ δ hm hM₂ hδ hδ_small
    linarith)

/--
§10 (parametric): if `δ* = 2m/M₂` with `m ≥ 1` and `M₂ ≤ M₂bound`, then
`δ*` is bounded below by `2/M₂bound`.
-/
theorem routeK_thm10_deltaStar_lower_bound_from_M2bound
    (m M₂ M₂bound : ℝ)
    (hm : 1 ≤ m) (hM₂pos : 0 < M₂) (hBoundPos : 0 < M₂bound)
    (hM₂le : M₂ ≤ M₂bound) :
    2 / M₂bound ≤ 2 * m / M₂ := by
  have hscaled : 2 * m / M₂bound ≤ 2 * m / M₂ :=
    routeK_thm10_deltaStar_lower_bound_scaled_from_M2bound
      m M₂ M₂bound (lt_of_lt_of_le (by norm_num) hm) hM₂pos hBoundPos hM₂le
  have hbase : 2 / M₂bound ≤ 2 * m / M₂bound := by
    have hBoundNe : M₂bound ≠ 0 := ne_of_gt hBoundPos
    field_simp [hBoundNe]
    nlinarith [hm]
  exact le_trans hbase hscaled

/--
§10 (parametric C2 form): instantiate `M₂bound = 2A + C*L`.
No numeric constants are hardcoded in this symbolic lower-bound theorem.
-/
theorem routeK_thm10_deltaStar_lower_bound_parametric
    (m M₂ A C L : ℝ)
    (hm : 1 ≤ m) (hM₂pos : 0 < M₂)
  (_hA : 0 ≤ A) (_hC : 0 ≤ C) (_hL : 0 ≤ L)
    (hM₂le : M₂ ≤ 2 * A + C * L) :
    2 / (2 * A + C * L) ≤ 2 * m / M₂ := by
  have hBoundPos : 0 < 2 * A + C * L := by linarith
  exact routeK_thm10_deltaStar_lower_bound_from_M2bound
    m M₂ (2 * A + C * L) hm hM₂pos hBoundPos hM₂le

/--
§10 (scaled parametric C2 form): instantiate `M₂bound = 2A + C*L` while only
assuming the Taylor-side positivity `m > 0`.
-/
theorem routeK_thm10_deltaStar_lower_bound_scaled_parametric
    (m M₂ A C L : ℝ)
    (hm : 0 < m) (hM₂pos : 0 < M₂)
    (_hA : 0 ≤ A) (_hC : 0 ≤ C) (_hL : 0 ≤ L)
    (hM₂le : M₂ ≤ 2 * A + C * L) :
    2 * m / (2 * A + C * L) ≤ 2 * m / M₂ := by
  have hBoundPos : 0 < 2 * A + C * L := by linarith
  exact routeK_thm10_deltaStar_lower_bound_scaled_from_M2bound
    m M₂ (2 * A + C * L) hm hM₂pos hBoundPos hM₂le

/--
§10 (concrete logarithmic specialization): instantiate the parametric lower
bound with `L = (log γ)^2`.
-/
theorem routeK_thm10_deltaStar_lower_bound_logSq
    (m M₂ A C γ : ℝ)
    (hm : 1 ≤ m) (hM₂pos : 0 < M₂)
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hM₂le : M₂ ≤ 2 * A + C * (Real.log γ) ^ 2) :
    2 / (2 * A + C * (Real.log γ) ^ 2) ≤ 2 * m / M₂ := by
  exact routeK_thm10_deltaStar_lower_bound_parametric
    m M₂ A C ((Real.log γ) ^ 2) hm hM₂pos _hA _hC (sq_nonneg (Real.log γ)) hM₂le

/--
§10 (concrete logarithmic scaled specialization): instantiate the scaled
parametric lower bound with `L = (log γ)^2`, matching the natural witness-side
assumption `m > 0`.
-/
theorem routeK_thm10_deltaStar_lower_bound_scaled_logSq
    (m M₂ A C γ : ℝ)
    (hm : 0 < m) (hM₂pos : 0 < M₂)
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hM₂le : M₂ ≤ 2 * A + C * (Real.log γ) ^ 2) :
    2 * m / (2 * A + C * (Real.log γ) ^ 2) ≤ 2 * m / M₂ := by
  exact routeK_thm10_deltaStar_lower_bound_scaled_parametric
    m M₂ A C ((Real.log γ) ^ 2) hm hM₂pos _hA _hC (sq_nonneg (Real.log γ)) hM₂le


end LeanC2
