import Mathlib
import LeanC2.Composite
import LeanC2.Continuation

namespace LeanC2

/--
Pointwise Taylor-dominance datum for the off-axis numerator `Dinf - Binf`.

This packages exactly the lower-bound shape used by
`routeK_elo5_nonzero_from_taylor`.
-/
def routeK_OffAxisTaylorDominanceAt (Dinf Binf : ℂ → ℂ) (s : ℂ) : Prop :=
  ∃ m M₂ R δ : ℝ,
    0 < m ∧
    0 < M₂ ∧
    0 < δ ∧
    δ < 2 * m / M₂ ∧
    0 ≤ R ∧
    R < δ * m - δ ^ 2 / 2 * M₂ ∧
    δ * m - δ ^ 2 / 2 * M₂ - R ≤ ‖Dinf s - Binf s‖

/--
Global off-axis Taylor-dominance datum on the admissible strip.
-/
def routeK_OffAxisTaylorDominanceGlobal (Dinf Binf : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
    routeK_OffAxisTaylorDominanceAt Dinf Binf s

/--
Pointwise Taylor-dominance datum together with a parametric upper bound on the
quadratic coefficient `M₂`.

This is the endpoint-facing form needed to combine a Taylor witness with the
symbolic lower-bound API from `Composite.lean`.
-/
def routeK_OffAxisTaylorDominanceBoundedAt
    (Dinf Binf : ℂ → ℂ) (s : ℂ) (M₂Bound : ℝ → Prop) : Prop :=
  ∃ m M₂ R δ : ℝ,
    0 < m ∧
    0 < M₂ ∧
    0 < δ ∧
    δ < 2 * m / M₂ ∧
    0 ≤ R ∧
    R < δ * m - δ ^ 2 / 2 * M₂ ∧
    δ * m - δ ^ 2 / 2 * M₂ - R ≤ ‖Dinf s - Binf s‖ ∧
    M₂Bound M₂

/--
Pointwise curvature envelope: a point-dependent upper bound for the quadratic
Taylor coefficient `M₂`.
-/
def routeK_OffAxisCurvatureEnvelopeAt
    (M₂Envelope : ℂ → ℝ) (s : ℂ) (M₂ : ℝ) : Prop :=
  M₂ ≤ M₂Envelope s

/--
Pointwise Taylor-dominance datum packaged against a pointwise curvature
envelope `M₂Envelope : ℂ → ℝ`.
-/
def routeK_OffAxisTaylorDominanceEnvelopeAt
    (Dinf Binf : ℂ → ℂ) (s : ℂ) (M₂Envelope : ℂ → ℝ) : Prop :=
  routeK_OffAxisTaylorDominanceBoundedAt Dinf Binf s
    (routeK_OffAxisCurvatureEnvelopeAt M₂Envelope s)

/--
Global off-axis Taylor-dominance datum packaged against a pointwise curvature
envelope `M₂Envelope : ℂ → ℝ`.
-/
def routeK_OffAxisTaylorDominanceEnvelopeGlobal
    (Dinf Binf : ℂ → ℂ) (M₂Envelope : ℂ → ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
    routeK_OffAxisTaylorDominanceEnvelopeAt Dinf Binf s M₂Envelope

/--
Constant parametric curvature envelope `s ↦ 2A + C*L`.
-/
def routeK_parametricCurvatureEnvelope (A C L : ℝ) : ℂ → ℝ :=
  fun _ => 2 * A + C * L

/--
Pointwise Taylor-dominance datum together with a parametric upper bound on the
quadratic coefficient `M₂`.

This is the endpoint-facing form needed to combine a Taylor witness with the
symbolic lower-bound API from `Composite.lean`.
-/
def routeK_OffAxisTaylorDominanceParametricAt
    (Dinf Binf : ℂ → ℂ) (s : ℂ) (A C L : ℝ) : Prop :=
  routeK_OffAxisTaylorDominanceEnvelopeAt Dinf Binf s
    (routeK_parametricCurvatureEnvelope A C L)

/--
Global off-axis Taylor-dominance datum together with a parametric upper bound
on `M₂` across the admissible strip.
-/
def routeK_OffAxisTaylorDominanceParametricGlobal
    (Dinf Binf : ℂ → ℂ) (A C L : ℝ) : Prop :=
  routeK_OffAxisTaylorDominanceEnvelopeGlobal Dinf Binf
    (routeK_parametricCurvatureEnvelope A C L)

/--
Canonical internal height parameter attached to an off-axis point.

This is the library-side replacement for the external scalar `γ` appearing in
the concrete `log² γ` bounds.
-/
def routeK_offAxisHeight (s : ℂ) : ℝ :=
  |s.im|

/--
The internal height parameter is nonzero exactly when the imaginary part of the
point is nonzero.
-/
theorem routeK_offAxisHeight_ne_zero_iff {s : ℂ} :
    routeK_offAxisHeight s ≠ 0 ↔ s.im ≠ 0 := by
  simp [routeK_offAxisHeight, abs_eq_zero]

/--
Structural logarithmic envelope for the quadratic Taylor coefficient at the
point `s`, expressed in terms of the internal height `|Im(s)|`.
-/
noncomputable def routeK_logSqM2Envelope (A C : ℝ) (s : ℂ) : ℝ :=
  2 * A + C * (Real.log (routeK_offAxisHeight s)) ^ 2

/--
The concrete height-based logarithmic curvature envelope.
-/
noncomputable def routeK_heightLogSqCurvatureEnvelope (A C : ℝ) : ℂ → ℝ :=
  routeK_logSqM2Envelope A C

/--
Pointwise structural curvature bound on the quadratic Taylor coefficient.

This separates the logarithmic `M₂` envelope from the Taylor witness itself.
-/
def routeK_OffAxisHeightLogSqCurvatureBoundAt
    (s : ℂ) (A C : ℝ) (M₂ : ℝ) : Prop :=
  routeK_OffAxisCurvatureEnvelopeAt
    (routeK_heightLogSqCurvatureEnvelope A C) s M₂

/--
Pointwise Taylor-dominance datum together with the structural logarithmic
envelope `M₂ ≤ 2A + C (log |Im(s)|)^2`.

This is closer to an internal theorem shape than the old endpoint-facing form,
because the logarithmic scale is now tied to the point `s` inside the library.
-/
def routeK_OffAxisTaylorDominanceHeightLogSqAt
    (Dinf Binf : ℂ → ℂ) (s : ℂ) (A C : ℝ) : Prop :=
  routeK_OffAxisTaylorDominanceEnvelopeAt Dinf Binf s
    (routeK_heightLogSqCurvatureEnvelope A C)

/--
Global off-axis Taylor-dominance datum with the structural logarithmic envelope
attached to the point height `|Im(s)|`.
-/
def routeK_OffAxisTaylorDominanceHeightLogSqGlobal
    (Dinf Binf : ℂ → ℂ) (A C : ℝ) : Prop :=
  routeK_OffAxisTaylorDominanceEnvelopeGlobal Dinf Binf
    (routeK_heightLogSqCurvatureEnvelope A C)

/--
Pointwise Taylor-dominance datum together with a bound on the normalized
quadratic coefficient `M₂ / m`.

This is the paper-level theorem-11 shape: the exclusion radius `δStar = 2m/M₂`
is controlled directly by a bound on `M₂ / m`, rather than on `M₂` itself.
-/
def routeK_OffAxisTaylorDominanceRatioEnvelopeAt
    (Dinf Binf : ℂ → ℂ) (s : ℂ) (ratioEnvelope : ℂ → ℝ) : Prop :=
  ∃ m M₂ R δ : ℝ,
    0 < m ∧
    0 < M₂ ∧
    0 < δ ∧
    δ < 2 * m / M₂ ∧
    0 ≤ R ∧
    R < δ * m - δ ^ 2 / 2 * M₂ ∧
    δ * m - δ ^ 2 / 2 * M₂ - R ≤ ‖Dinf s - Binf s‖ ∧
    M₂ / m ≤ ratioEnvelope s

/--
Global off-axis Taylor-dominance datum together with a bound on the normalized
quadratic coefficient `M₂ / m`.
-/
def routeK_OffAxisTaylorDominanceRatioEnvelopeGlobal
    (Dinf Binf : ℂ → ℂ) (ratioEnvelope : ℂ → ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
    routeK_OffAxisTaylorDominanceRatioEnvelopeAt Dinf Binf s ratioEnvelope

/--
Pointwise theorem-11 witness in the structural `log² |Im(s)|` regime, now in
the normalized form `M₂ / m ≤ 2A + C (log |Im(s)|)^2`.
-/
def routeK_OffAxisTaylorDominanceHeightLogSqRatioAt
    (Dinf Binf : ℂ → ℂ) (s : ℂ) (A C : ℝ) : Prop :=
  routeK_OffAxisTaylorDominanceRatioEnvelopeAt Dinf Binf s
    (routeK_heightLogSqCurvatureEnvelope A C)

/--
Global theorem-11 witness in the structural `log² |Im(s)|` regime, in the
normalized form `M₂ / m ≤ 2A + C (log |Im(s)|)^2`.
-/
def routeK_OffAxisTaylorDominanceHeightLogSqRatioGlobal
    (Dinf Binf : ℂ → ℂ) (A C : ℝ) : Prop :=
  routeK_OffAxisTaylorDominanceRatioEnvelopeGlobal Dinf Binf
    (routeK_heightLogSqCurvatureEnvelope A C)

/--
Forgetting the normalized coefficient bound recovers the plain Taylor witness.
-/
theorem routeK_OffAxisTaylorDominanceAt_of_ratioEnvelopeAt
    {Dinf Binf : ℂ → ℂ} {s : ℂ} {ratioEnvelope : ℂ → ℝ}
    (hTaylor : routeK_OffAxisTaylorDominanceRatioEnvelopeAt Dinf Binf s ratioEnvelope) :
    routeK_OffAxisTaylorDominanceAt Dinf Binf s := by
  rcases hTaylor with ⟨m, M₂, R, δ, hm, hM₂, hδ, hδsmall, hR, hRsmall, hF_lb, hRatio⟩
  exact ⟨m, M₂, R, δ, hm, hM₂, hδ, hδsmall, hR, hRsmall, hF_lb⟩

/--
Global bridge from the normalized theorem-11 witness to the plain Taylor API.
-/
theorem routeK_OffAxisTaylorDominanceGlobal_of_ratioEnvelopeGlobal
    {Dinf Binf : ℂ → ℂ} {ratioEnvelope : ℂ → ℝ}
    (hTaylor : routeK_OffAxisTaylorDominanceRatioEnvelopeGlobal Dinf Binf ratioEnvelope) :
    routeK_OffAxisTaylorDominanceGlobal Dinf Binf := by
  intro s hs hstrip hhalf
  exact routeK_OffAxisTaylorDominanceAt_of_ratioEnvelopeAt
    (hTaylor s hs hstrip hhalf)

/-- Explicit theorem-11 constant `A = 1.5862 = 7931 / 5000`. -/
noncomputable def routeK_explicitTaylorA : ℝ := (7931 : ℝ) / 5000

/-- Explicit theorem-11 constant `C = 0.153 = 153 / 1000`. -/
noncomputable def routeK_explicitTaylorC : ℝ := (153 : ℝ) / 1000

theorem routeK_explicitTaylorA_nonneg : 0 ≤ routeK_explicitTaylorA := by
  norm_num [routeK_explicitTaylorA]

theorem routeK_explicitTaylorC_nonneg : 0 ≤ routeK_explicitTaylorC := by
  norm_num [routeK_explicitTaylorC]

/--
Pointwise theorem-11 witness specialized to the explicit research constants
`A = 1.5862`, `C = 0.153`.
-/
def routeK_OffAxisTaylorDominanceExplicitAt
    (Dinf Binf : ℂ → ℂ) (s : ℂ) : Prop :=
  routeK_OffAxisTaylorDominanceHeightLogSqRatioAt
    Dinf Binf s routeK_explicitTaylorA routeK_explicitTaylorC

/--
Global theorem-11 witness specialized to the explicit research constants
`A = 1.5862`, `C = 0.153`.
-/
def routeK_OffAxisTaylorDominanceExplicitGlobal
    (Dinf Binf : ℂ → ℂ) : Prop :=
  routeK_OffAxisTaylorDominanceHeightLogSqRatioGlobal
    Dinf Binf routeK_explicitTaylorA routeK_explicitTaylorC

/--
Literal theorem-11 first-order transversal size
`M₁ = ‖c₀(ρ) * ζ'(ρ)‖`.
-/
noncomputable def routeK_transversalM1
    (c0Val zetaDeriv : ℂ) : ℝ :=
  ‖c0Val * zetaDeriv‖

/--
Literal theorem-11 second-order transversal size
`M₂ = ‖2 c₀'(ρ) ζ'(ρ) + c₀(ρ) ζ''(ρ)‖`.
-/
noncomputable def routeK_transversalM2
    (c0Val c0Deriv zetaDeriv zetaSecondDeriv : ℂ) : ℝ :=
  ‖2 * c0Deriv * zetaDeriv + c0Val * zetaSecondDeriv‖

/-- Literal logarithmic derivative `α = c₀'/c₀`. -/
noncomputable def routeK_transversalAlpha
    (c0Val c0Deriv : ℂ) : ℂ :=
  c0Deriv / c0Val

/-- Literal simple-zero curvature ratio `β = ζ''/ζ'`. -/
noncomputable def routeK_transversalBeta
    (zetaDeriv zetaSecondDeriv : ℂ) : ℂ :=
  zetaSecondDeriv / zetaDeriv

/--
Literal norm identity for the transversal `α = c₀'/c₀`.
-/
theorem routeK_transversalAlpha_norm_eq_div_norm
    (c0Val c0Deriv : ℂ) :
    ‖routeK_transversalAlpha c0Val c0Deriv‖ =
      ‖c0Deriv‖ / ‖c0Val‖ := by
  simp [routeK_transversalAlpha]

/--
Concrete `α` bound from a lower bound on `‖c₀‖` and a derivative bound
`‖c₀'‖ ≤ A * L` relative to that lower bound.

This is the literal analytic shape needed to replace a bare hypothesis
`‖α‖ ≤ A` by certifiable estimates on `c₀` itself.
-/
theorem routeK_transversalAlpha_norm_le_of_deriv_bound_and_c0_lower
    {c0Val c0Deriv : ℂ} {A L : ℝ}
    (hLpos : 0 < L)
    (hLower : L ≤ ‖c0Val‖)
    (hDeriv : ‖c0Deriv‖ ≤ A * L) :
    ‖routeK_transversalAlpha c0Val c0Deriv‖ ≤ A := by
  rw [routeK_transversalAlpha_norm_eq_div_norm]
  have hDivDen :
      ‖c0Deriv‖ / ‖c0Val‖ ≤ ‖c0Deriv‖ / L := by
    exact div_le_div_of_nonneg_left (norm_nonneg _) hLpos hLower
  have hDivNum : ‖c0Deriv‖ / L ≤ (A * L) / L := by
    exact div_le_div_of_nonneg_right hDeriv (le_of_lt hLpos)
  calc
    ‖c0Deriv‖ / ‖c0Val‖ ≤ ‖c0Deriv‖ / L := hDivDen
    _ ≤ (A * L) / L := hDivNum
    _ = A := by
      field_simp [ne_of_gt hLpos]

/--
Concrete derivative bound for the normalization factor `c₀`, scaled by the
explicit off-axis lower-bound profile for `‖c₀(s)‖`.
-/
def routeK_C0AlphaDerivativeBoundAt (s : ℂ) (A : ℝ) : Prop :=
  ‖deriv c0Complex s‖ ≤ A * c0OffAxisLower s.re

/--
Global `c₀` derivative bound on the admissible off-critical strip.
-/
def routeK_C0AlphaDerivativeBoundGlobal (A : ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
    routeK_C0AlphaDerivativeBoundAt s A

/--
The concrete `c₀` derivative bound gives the transversal `α` bound for the
actual normalization factor `c0Complex`.
-/
theorem routeK_c0Alpha_norm_le_of_derivBoundAt
    {s : ℂ} {A : ℝ}
    (hs : 0 < s.re)
    (hDeriv : routeK_C0AlphaDerivativeBoundAt s A) :
    ‖routeK_transversalAlpha (c0Complex s) (deriv c0Complex s)‖ ≤ A := by
  exact routeK_transversalAlpha_norm_le_of_deriv_bound_and_c0_lower
    (c0OffAxisLower_pos hs)
    (c0Complex_norm_ge_c0OffAxisLower_of_re_pos hs)
    hDeriv

/--
Global concrete `c₀` derivative bounds imply the global transversal `α` bound
for `c0Complex`.
-/
theorem routeK_c0Alpha_bound_global_of_derivBoundGlobal
    {A : ℝ}
    (hDeriv : routeK_C0AlphaDerivativeBoundGlobal A) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ‖routeK_transversalAlpha (c0Complex s) (deriv c0Complex s)‖ ≤ A := by
  intro s hs hstrip hhalf
  exact routeK_c0Alpha_norm_le_of_derivBoundAt hs
    (hDeriv s hs hstrip hhalf)

theorem routeK_transversalM1_pos
    {c0Val zetaDeriv : ℂ}
    (hc0 : c0Val ≠ 0) (hzeta : zetaDeriv ≠ 0) :
    0 < routeK_transversalM1 c0Val zetaDeriv := by
  unfold routeK_transversalM1
  exact norm_pos_iff.2 (mul_ne_zero hc0 hzeta)

/--
Literal factorization of the theorem-11 quadratic coefficient:
`M₂ = ‖2α + β‖ * M₁`.
-/
theorem routeK_transversalM2_eq_norm_twoAlpha_add_beta_mul_M1
    {c0Val c0Deriv zetaDeriv zetaSecondDeriv : ℂ}
    (hc0 : c0Val ≠ 0) (hzeta : zetaDeriv ≠ 0) :
    routeK_transversalM2 c0Val c0Deriv zetaDeriv zetaSecondDeriv =
      ‖2 * routeK_transversalAlpha c0Val c0Deriv +
          routeK_transversalBeta zetaDeriv zetaSecondDeriv‖ *
        routeK_transversalM1 c0Val zetaDeriv := by
  have hFactor :
      2 * c0Deriv * zetaDeriv + c0Val * zetaSecondDeriv =
        (2 * routeK_transversalAlpha c0Val c0Deriv +
            routeK_transversalBeta zetaDeriv zetaSecondDeriv) *
          (c0Val * zetaDeriv) := by
    unfold routeK_transversalAlpha routeK_transversalBeta
    field_simp [hc0, hzeta]
  rw [routeK_transversalM2, routeK_transversalM1, hFactor, norm_mul]

/--
Literal theorem-11 ratio identity
`M₂ / M₁ = ‖2α + β‖`.
-/
theorem routeK_transversalM2_div_M1_eq_norm_twoAlpha_add_beta
    {c0Val c0Deriv zetaDeriv zetaSecondDeriv : ℂ}
    (hc0 : c0Val ≠ 0) (hzeta : zetaDeriv ≠ 0) :
    routeK_transversalM2 c0Val c0Deriv zetaDeriv zetaSecondDeriv /
        routeK_transversalM1 c0Val zetaDeriv =
      ‖2 * routeK_transversalAlpha c0Val c0Deriv +
          routeK_transversalBeta zetaDeriv zetaSecondDeriv‖ := by
  have hM1ne : routeK_transversalM1 c0Val zetaDeriv ≠ 0 :=
    ne_of_gt (routeK_transversalM1_pos hc0 hzeta)
  rw [routeK_transversalM2_eq_norm_twoAlpha_add_beta_mul_M1 hc0 hzeta]
  calc
    ‖2 * routeK_transversalAlpha c0Val c0Deriv +
        routeK_transversalBeta zetaDeriv zetaSecondDeriv‖ *
          routeK_transversalM1 c0Val zetaDeriv /
          routeK_transversalM1 c0Val zetaDeriv =
        ‖2 * routeK_transversalAlpha c0Val c0Deriv +
            routeK_transversalBeta zetaDeriv zetaSecondDeriv‖ *
          (routeK_transversalM1 c0Val zetaDeriv /
            routeK_transversalM1 c0Val zetaDeriv) := by
      rw [mul_div_assoc]
    _ = ‖2 * routeK_transversalAlpha c0Val c0Deriv +
          routeK_transversalBeta zetaDeriv zetaSecondDeriv‖ * 1 := by
      rw [div_self hM1ne]
    _ = ‖2 * routeK_transversalAlpha c0Val c0Deriv +
          routeK_transversalBeta zetaDeriv zetaSecondDeriv‖ := by
      ring

/--
Triangle-inequality control of the literal theorem-11 ratio from bounds on
`α = c₀'/c₀` and `β = ζ''/ζ'`.
-/
theorem routeK_transversalM2_div_M1_le_of_alpha_beta_bounds
    {c0Val c0Deriv zetaDeriv zetaSecondDeriv : ℂ}
    {A B : ℝ}
    (hc0 : c0Val ≠ 0) (hzeta : zetaDeriv ≠ 0)
    (hAlpha : ‖routeK_transversalAlpha c0Val c0Deriv‖ ≤ A)
    (hBeta : ‖routeK_transversalBeta zetaDeriv zetaSecondDeriv‖ ≤ B) :
    routeK_transversalM2 c0Val c0Deriv zetaDeriv zetaSecondDeriv /
        routeK_transversalM1 c0Val zetaDeriv ≤
      2 * A + B := by
  rw [routeK_transversalM2_div_M1_eq_norm_twoAlpha_add_beta hc0 hzeta]
  calc
    ‖2 * routeK_transversalAlpha c0Val c0Deriv +
        routeK_transversalBeta zetaDeriv zetaSecondDeriv‖ ≤
        ‖2 * routeK_transversalAlpha c0Val c0Deriv‖ +
          ‖routeK_transversalBeta zetaDeriv zetaSecondDeriv‖ :=
      norm_add_le _ _
    _ = 2 * ‖routeK_transversalAlpha c0Val c0Deriv‖ +
          ‖routeK_transversalBeta zetaDeriv zetaSecondDeriv‖ := by
      simp
    _ ≤ 2 * A + B := by
      nlinarith

/--
Height-based theorem-11 ratio bound in the structural `log² |Im(s)|` regime.
-/
theorem routeK_transversalM2_div_M1_le_heightLogSq_of_alpha_beta_bounds
    {s : ℂ} {c0Val c0Deriv zetaDeriv zetaSecondDeriv : ℂ}
    {A C : ℝ}
    (hc0 : c0Val ≠ 0) (hzeta : zetaDeriv ≠ 0)
    (hAlpha : ‖routeK_transversalAlpha c0Val c0Deriv‖ ≤ A)
    (hBeta : ‖routeK_transversalBeta zetaDeriv zetaSecondDeriv‖ ≤
      C * (Real.log (routeK_offAxisHeight s)) ^ 2) :
    routeK_transversalM2 c0Val c0Deriv zetaDeriv zetaSecondDeriv /
        routeK_transversalM1 c0Val zetaDeriv ≤
      routeK_logSqM2Envelope A C s := by
  simpa [routeK_logSqM2Envelope] using
    routeK_transversalM2_div_M1_le_of_alpha_beta_bounds
      (c0Val := c0Val) (c0Deriv := c0Deriv)
      (zetaDeriv := zetaDeriv) (zetaSecondDeriv := zetaSecondDeriv)
      (A := A) (B := C * (Real.log (routeK_offAxisHeight s)) ^ 2)
      hc0 hzeta hAlpha hBeta

/--
Explicit theorem-11 ratio bound specialized to the research constants
`A = 1.5862`, `C = 0.153`.
-/
theorem routeK_transversalM2_div_M1_le_explicit_heightLogSq_of_alpha_beta_bounds
    {s : ℂ} {c0Val c0Deriv zetaDeriv zetaSecondDeriv : ℂ}
    (hc0 : c0Val ≠ 0) (hzeta : zetaDeriv ≠ 0)
    (hAlpha : ‖routeK_transversalAlpha c0Val c0Deriv‖ ≤ routeK_explicitTaylorA)
    (hBeta : ‖routeK_transversalBeta zetaDeriv zetaSecondDeriv‖ ≤
      routeK_explicitTaylorC * (Real.log (routeK_offAxisHeight s)) ^ 2) :
    routeK_transversalM2 c0Val c0Deriv zetaDeriv zetaSecondDeriv /
        routeK_transversalM1 c0Val zetaDeriv ≤
      routeK_logSqM2Envelope routeK_explicitTaylorA routeK_explicitTaylorC s := by
  exact routeK_transversalM2_div_M1_le_heightLogSq_of_alpha_beta_bounds
    (s := s) hc0 hzeta hAlpha hBeta

/--
Standard-analytic Hadamard-von-Mangoldt input for the curvature ratio
`β = ζ''/ζ'` at the point `s`.

This isolates exactly the external theorem-level ingredient used in the global
`log² |Im(s)|` theorem-11 bound.
-/
def routeK_HadamardVonMangoldtBetaBoundAt
    (s : ℂ) (zetaDeriv zetaSecondDeriv : ℂ) (C : ℝ) : Prop :=
  ‖routeK_transversalBeta zetaDeriv zetaSecondDeriv‖ ≤
    C * (Real.log (routeK_offAxisHeight s)) ^ 2

/--
Global Hadamard-von-Mangoldt input for the curvature ratio `β = ζ''/ζ'`.
-/
def routeK_HadamardVonMangoldtBetaBoundGlobal
    (zetaDeriv zetaSecondDeriv : ℂ → ℂ) (C : ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 ->
    routeK_HadamardVonMangoldtBetaBoundAt s (zetaDeriv s) (zetaSecondDeriv s) C

/--
Explicit specialization of the standard Hadamard-von-Mangoldt input to the
research constant `C = 0.153`.
-/
def routeK_HadamardVonMangoldtBetaBoundExplicitAt
    (s : ℂ) (zetaDeriv zetaSecondDeriv : ℂ) : Prop :=
  routeK_HadamardVonMangoldtBetaBoundAt s zetaDeriv zetaSecondDeriv
    routeK_explicitTaylorC

/--
Global explicit specialization of the standard Hadamard-von-Mangoldt input.
-/
def routeK_HadamardVonMangoldtBetaBoundExplicitGlobal
    (zetaDeriv zetaSecondDeriv : ℂ → ℂ) : Prop :=
  routeK_HadamardVonMangoldtBetaBoundGlobal zetaDeriv zetaSecondDeriv
    routeK_explicitTaylorC

/--
Pointwise log-square normalizing constant for the literal curvature ratio
`β = ζ''/ζ'`.

This is an unconditional finite/certified substitute for a single point: it does
not assert the classical uniform Hadamard-von-Mangoldt asymptotic constant, but
it gives the exact constant needed to satisfy the same Lean predicate whenever
`log |Im(s)|` is nonzero.
-/
noncomputable def routeK_betaPointwiseLogSqConstant
    (s : ℂ) (zetaDeriv zetaSecondDeriv : ℂ) : ℝ :=
  ‖routeK_transversalBeta zetaDeriv zetaSecondDeriv‖ /
    (Real.log (routeK_offAxisHeight s)) ^ 2

theorem routeK_betaPointwiseLogSqConstant_nonneg
    {s : ℂ} {zetaDeriv zetaSecondDeriv : ℂ} :
    0 ≤ routeK_betaPointwiseLogSqConstant s zetaDeriv zetaSecondDeriv := by
  unfold routeK_betaPointwiseLogSqConstant
  exact div_nonneg (norm_nonneg _) (sq_nonneg _)

/--
At any point with nonzero logarithmic height, the pointwise normalizing constant
unconditionally discharges the `β`-bound predicate.
-/
theorem routeK_HadamardVonMangoldtBetaBoundAt_of_pointwiseLogSqConstant
    {s : ℂ} {zetaDeriv zetaSecondDeriv : ℂ}
    (hlog : Real.log (routeK_offAxisHeight s) ≠ 0) :
    routeK_HadamardVonMangoldtBetaBoundAt s zetaDeriv zetaSecondDeriv
      (routeK_betaPointwiseLogSqConstant s zetaDeriv zetaSecondDeriv) := by
  unfold routeK_HadamardVonMangoldtBetaBoundAt
    routeK_betaPointwiseLogSqConstant
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 hlog)]

/--
Finite-window version of the `β`-bound predicate.

This is useful for certified stripwise work: the constant may depend on the
finite window, but no Hadamard product or zero-counting theorem is assumed.
-/
def routeK_HadamardVonMangoldtBetaBoundOn
    (S : Finset ℂ) (zetaDeriv zetaSecondDeriv : ℂ → ℂ) (C : ℝ) : Prop :=
  ∀ s ∈ S,
    routeK_HadamardVonMangoldtBetaBoundAt s (zetaDeriv s) (zetaSecondDeriv s) C

/--
Uniform finite-window log-square constant obtained by summing the exact
pointwise constants over the window.
-/
noncomputable def routeK_betaFiniteLogSqConstant
    (S : Finset ℂ) (zetaDeriv zetaSecondDeriv : ℂ → ℂ) : ℝ :=
  ∑ s ∈ S,
    routeK_betaPointwiseLogSqConstant s (zetaDeriv s) (zetaSecondDeriv s)

theorem routeK_betaFiniteLogSqConstant_nonneg
    (S : Finset ℂ) (zetaDeriv zetaSecondDeriv : ℂ → ℂ) :
    0 ≤ routeK_betaFiniteLogSqConstant S zetaDeriv zetaSecondDeriv := by
  unfold routeK_betaFiniteLogSqConstant
  exact Finset.sum_nonneg fun s _ =>
    routeK_betaPointwiseLogSqConstant_nonneg

/--
Every finite window whose points have nonzero logarithmic height carries an
unconditional uniform `β`-bound, with the explicit finite constant above.
-/
theorem routeK_HadamardVonMangoldtBetaBoundOn_of_finiteLogSqConstant
    {S : Finset ℂ} {zetaDeriv zetaSecondDeriv : ℂ → ℂ}
    (hlog : ∀ s ∈ S, Real.log (routeK_offAxisHeight s) ≠ 0) :
    routeK_HadamardVonMangoldtBetaBoundOn S zetaDeriv zetaSecondDeriv
      (routeK_betaFiniteLogSqConstant S zetaDeriv zetaSecondDeriv) := by
  intro s hs
  unfold routeK_HadamardVonMangoldtBetaBoundAt
  set L : ℝ := Real.log (routeK_offAxisHeight s)
  have hLne : L ≠ 0 := by
    simpa [L] using hlog s hs
  have hLsq_pos : 0 < L ^ 2 := sq_pos_of_ne_zero hLne
  have hpoint_nonneg :
      ∀ u ∈ S,
        0 ≤ routeK_betaPointwiseLogSqConstant u (zetaDeriv u) (zetaSecondDeriv u) := by
    intro u hu
    exact routeK_betaPointwiseLogSqConstant_nonneg
  have hsingle :
      routeK_betaPointwiseLogSqConstant s (zetaDeriv s) (zetaSecondDeriv s) ≤
        routeK_betaFiniteLogSqConstant S zetaDeriv zetaSecondDeriv := by
    unfold routeK_betaFiniteLogSqConstant
    exact Finset.single_le_sum hpoint_nonneg hs
  have hmul := mul_le_mul_of_nonneg_right hsingle (le_of_lt hLsq_pos)
  have hleft :
      routeK_betaPointwiseLogSqConstant s (zetaDeriv s) (zetaSecondDeriv s) * L ^ 2 =
        ‖routeK_transversalBeta (zetaDeriv s) (zetaSecondDeriv s)‖ := by
    unfold routeK_betaPointwiseLogSqConstant
    rw [show Real.log (routeK_offAxisHeight s) = L from rfl]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hLne)
  simpa [L, hleft] using hmul

/--
Dyadic-shell certificate for the Hadamard-von-Mangoldt bound on
`β = ζ''/ζ'`.

This is the Lean version of the argument in the Route-K notes: a Hadamard
regular part bounded by a base `O(log γ)` term, a family of dyadic shell
contributions each bounded by `O(log γ)`, and `O(log γ)` relevant shells imply
the structural `O(log² γ)` bound.

The certificate is intentionally theorem-facing: the analytic construction of
the shells from the classical Hadamard product and the zero-counting theorem can
be supplied later without changing downstream C2 code.
-/
def routeK_HadamardVonMangoldtDyadicShellBetaCertificateAt
    (s : ℂ) (zetaDeriv zetaSecondDeriv : ℂ)
    (shells : Finset ℕ) (shellContribution : ℕ → ℝ)
    (base shellC shellCountC C : ℝ) : Prop :=
  ∃ L : ℝ,
    L = Real.log (routeK_offAxisHeight s) ∧
    0 ≤ base ∧
    0 ≤ shellC ∧
    0 ≤ shellCountC ∧
    1 ≤ L ∧
    ‖routeK_transversalBeta zetaDeriv zetaSecondDeriv‖ ≤
      base * L + ∑ j ∈ shells, shellContribution j ∧
    (∀ j ∈ shells,
      0 ≤ shellContribution j ∧ shellContribution j ≤ shellC * L) ∧
    (shells.card : ℝ) ≤ shellCountC * L ∧
    base + shellC * shellCountC ≤ C

/--
The Route-K dyadic-shell certificate discharges the standard
Hadamard-von-Mangoldt `β` predicate.
-/
theorem routeK_HadamardVonMangoldtBetaBoundAt_of_dyadicShellCertificate
    {s : ℂ} {zetaDeriv zetaSecondDeriv : ℂ}
    {shells : Finset ℕ} {shellContribution : ℕ → ℝ}
    {base shellC shellCountC C : ℝ}
    (hcert : routeK_HadamardVonMangoldtDyadicShellBetaCertificateAt
      s zetaDeriv zetaSecondDeriv shells shellContribution
      base shellC shellCountC C) :
    routeK_HadamardVonMangoldtBetaBoundAt s zetaDeriv zetaSecondDeriv C := by
  rcases hcert with
    ⟨L, hLdef, hbase0, hshellC0, _hshellCountC0, hL1, hBeta, hShell, hCard, hC⟩
  have hL0 : 0 ≤ L := by linarith
  have hShellCL0 : 0 ≤ shellC * L := mul_nonneg hshellC0 hL0
  have hsum_le_const :
      (∑ j ∈ shells, shellContribution j) ≤
        ∑ j ∈ shells, shellC * L := by
    exact Finset.sum_le_sum fun j hj => (hShell j hj).2
  have hsum_const :
      (∑ j ∈ shells, shellC * L) =
        (shells.card : ℝ) * (shellC * L) := by
    simp
  have hsum_le_card :
      (∑ j ∈ shells, shellContribution j) ≤
        (shells.card : ℝ) * (shellC * L) := by
    calc
      (∑ j ∈ shells, shellContribution j) ≤
          ∑ j ∈ shells, shellC * L := hsum_le_const
      _ = (shells.card : ℝ) * (shellC * L) := hsum_const
  have hsum_le_logSq :
      (∑ j ∈ shells, shellContribution j) ≤
        shellC * shellCountC * L ^ 2 := by
    calc
      (∑ j ∈ shells, shellContribution j) ≤
          (shells.card : ℝ) * (shellC * L) := hsum_le_card
      _ ≤ (shellCountC * L) * (shellC * L) :=
          mul_le_mul_of_nonneg_right hCard hShellCL0
      _ = shellC * shellCountC * L ^ 2 := by ring
  have hL_le_sq : L ≤ L ^ 2 := by nlinarith
  have hbase_le_logSq : base * L ≤ base * L ^ 2 :=
    mul_le_mul_of_nonneg_left hL_le_sq hbase0
  have hmain :
      ‖routeK_transversalBeta zetaDeriv zetaSecondDeriv‖ ≤
        (base + shellC * shellCountC) * L ^ 2 := by
    calc
      ‖routeK_transversalBeta zetaDeriv zetaSecondDeriv‖ ≤
          base * L + ∑ j ∈ shells, shellContribution j := hBeta
      _ ≤ base * L ^ 2 + shellC * shellCountC * L ^ 2 :=
          add_le_add hbase_le_logSq hsum_le_logSq
      _ = (base + shellC * shellCountC) * L ^ 2 := by ring
  have hfinal :
      (base + shellC * shellCountC) * L ^ 2 ≤ C * L ^ 2 :=
    mul_le_mul_of_nonneg_right hC (sq_nonneg L)
  unfold routeK_HadamardVonMangoldtBetaBoundAt
  simpa [hLdef] using hmain.trans hfinal

/--
Explicit-constant variant of the dyadic-shell certificate, specialized to the
research constant `C = 0.153`.
-/
theorem routeK_HadamardVonMangoldtBetaBoundExplicitAt_of_dyadicShellCertificate
    {s : ℂ} {zetaDeriv zetaSecondDeriv : ℂ}
    {shells : Finset ℕ} {shellContribution : ℕ → ℝ}
    {base shellC shellCountC : ℝ}
    (hcert : routeK_HadamardVonMangoldtDyadicShellBetaCertificateAt
      s zetaDeriv zetaSecondDeriv shells shellContribution
      base shellC shellCountC routeK_explicitTaylorC) :
    routeK_HadamardVonMangoldtBetaBoundExplicitAt s zetaDeriv zetaSecondDeriv := by
  simpa [routeK_HadamardVonMangoldtBetaBoundExplicitAt] using
    routeK_HadamardVonMangoldtBetaBoundAt_of_dyadicShellCertificate hcert

/--
Global dyadic-shell certificate for `β = ζ''/ζ'` on the admissible off-axis
strip.
-/
def routeK_HadamardVonMangoldtDyadicShellBetaCertificateGlobal
    (zetaDeriv zetaSecondDeriv : ℂ → ℂ)
    (shells : ℂ → Finset ℕ) (shellContribution : ℂ → ℕ → ℝ)
    (base shellC shellCountC C : ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
    routeK_HadamardVonMangoldtDyadicShellBetaCertificateAt
      s (zetaDeriv s) (zetaSecondDeriv s)
      (shells s) (shellContribution s) base shellC shellCountC C

/--
The global dyadic-shell certificate promotes to the global
Hadamard-von-Mangoldt `β` predicate used by the theorem-11 API.
-/
theorem routeK_HadamardVonMangoldtBetaBoundGlobal_of_dyadicShellCertificateGlobal
    {zetaDeriv zetaSecondDeriv : ℂ → ℂ}
    {shells : ℂ → Finset ℕ} {shellContribution : ℂ → ℕ → ℝ}
    {base shellC shellCountC C : ℝ}
    (hcert : routeK_HadamardVonMangoldtDyadicShellBetaCertificateGlobal
      zetaDeriv zetaSecondDeriv shells shellContribution base shellC shellCountC C) :
    routeK_HadamardVonMangoldtBetaBoundGlobal zetaDeriv zetaSecondDeriv C := by
  intro s hs hstrip hhalf
  exact routeK_HadamardVonMangoldtBetaBoundAt_of_dyadicShellCertificate
    (hcert s hs hstrip hhalf)

/--
Literal Taylor-dominance datum obtained by plugging the explicit analytic
quantities

`M₁ = ‖c₀ζ'‖`, `M₂ = ‖2c₀'ζ' + c₀ζ''‖`

directly into the pointwise theorem-11 witness.
-/
def routeK_OffAxisTaylorDominanceLiteralAt
    (Dinf Binf : ℂ → ℂ) (s : ℂ)
    (c0Val c0Deriv zetaDeriv zetaSecondDeriv : ℂ) : Prop :=
  ∃ R δ : ℝ,
    0 < routeK_transversalM1 c0Val zetaDeriv ∧
    0 < routeK_transversalM2 c0Val c0Deriv zetaDeriv zetaSecondDeriv ∧
    0 < δ ∧
    δ < 2 * routeK_transversalM1 c0Val zetaDeriv /
      routeK_transversalM2 c0Val c0Deriv zetaDeriv zetaSecondDeriv ∧
    0 ≤ R ∧
    R < δ * routeK_transversalM1 c0Val zetaDeriv -
      δ ^ 2 / 2 * routeK_transversalM2 c0Val c0Deriv zetaDeriv zetaSecondDeriv ∧
    δ * routeK_transversalM1 c0Val zetaDeriv -
        δ ^ 2 / 2 * routeK_transversalM2 c0Val c0Deriv zetaDeriv zetaSecondDeriv - R ≤
      ‖Dinf s - Binf s‖

/--
Global literal Taylor-dominance datum obtained from the explicit analytic
quantities `M₁ = ‖c₀ζ'‖`, `M₂ = ‖2c₀'ζ' + c₀ζ''‖`.
-/
def routeK_OffAxisTaylorDominanceLiteralGlobal
    (Dinf Binf c0Val c0Deriv zetaDeriv zetaSecondDeriv : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 ->
    routeK_OffAxisTaylorDominanceLiteralAt Dinf Binf s
      (c0Val s) (c0Deriv s) (zetaDeriv s) (zetaSecondDeriv s)

/--
Positivity of the literal first-order transversal size forces both factors in
`M₁ = ‖c₀ζ'‖` to be nonzero.
-/
theorem routeK_transversalFactors_ne_zero_of_M1_pos
    {c0Val zetaDeriv : ℂ}
    (hM1 : 0 < routeK_transversalM1 c0Val zetaDeriv) :
    c0Val ≠ 0 ∧ zetaDeriv ≠ 0 := by
  have hnorm : ‖c0Val * zetaDeriv‖ ≠ 0 :=
    ne_of_gt (by simpa [routeK_transversalM1] using hM1)
  constructor
  · intro hc0
    apply norm_ne_zero_iff.mp hnorm
    simp [hc0]
  · intro hzeta
    apply norm_ne_zero_iff.mp hnorm
    simp [hzeta]

/--
Forget the literal analytic packaging and recover the plain Taylor-dominance
witness.
-/
theorem routeK_OffAxisTaylorDominanceAt_of_literalAt
    {Dinf Binf : ℂ → ℂ} {s : ℂ}
    {c0Val c0Deriv zetaDeriv zetaSecondDeriv : ℂ}
    (hTaylor : routeK_OffAxisTaylorDominanceLiteralAt
      Dinf Binf s c0Val c0Deriv zetaDeriv zetaSecondDeriv) :
    routeK_OffAxisTaylorDominanceAt Dinf Binf s := by
  rcases hTaylor with ⟨R, δ, hM1, hM2, hδ, hδsmall, hR, hRsmall, hF_lb⟩
  exact ⟨routeK_transversalM1 c0Val zetaDeriv,
    routeK_transversalM2 c0Val c0Deriv zetaDeriv zetaSecondDeriv,
    R, δ, hM1, hM2, hδ, hδsmall, hR, hRsmall, hF_lb⟩

/--
From a literal local Taylor package and any bound on `M₂ / M₁`, one recovers
the normalized theorem-11 witness.
-/
theorem routeK_OffAxisTaylorDominanceRatioEnvelopeAt_of_literalAt_of_ratioBound
    {Dinf Binf : ℂ → ℂ} {s : ℂ} {ratioEnvelope : ℂ → ℝ}
    {c0Val c0Deriv zetaDeriv zetaSecondDeriv : ℂ}
    (hTaylor : routeK_OffAxisTaylorDominanceLiteralAt
      Dinf Binf s c0Val c0Deriv zetaDeriv zetaSecondDeriv)
    (hRatio : routeK_transversalM2 c0Val c0Deriv zetaDeriv zetaSecondDeriv /
      routeK_transversalM1 c0Val zetaDeriv ≤ ratioEnvelope s) :
    routeK_OffAxisTaylorDominanceRatioEnvelopeAt Dinf Binf s ratioEnvelope := by
  rcases hTaylor with ⟨R, δ, hM1, hM2, hδ, hδsmall, hR, hRsmall, hF_lb⟩
  exact ⟨routeK_transversalM1 c0Val zetaDeriv,
    routeK_transversalM2 c0Val c0Deriv zetaDeriv zetaSecondDeriv,
    R, δ, hM1, hM2, hδ, hδsmall, hR, hRsmall, hF_lb, hRatio⟩

/--
Literal local Taylor package plus an internal `α`-bound and the isolated
standard Hadamard-von-Mangoldt `β`-bound yield the structural theorem-11
ratio witness.
-/
theorem
  routeK_OffAxisTaylorDominanceHeightLogSqRatioAt_of_literalAt_of_alpha_bound_of_hadamardBetaBound
    {Dinf Binf : ℂ → ℂ} {s : ℂ} {A C : ℝ}
    {c0Val c0Deriv zetaDeriv zetaSecondDeriv : ℂ}
    (hTaylor : routeK_OffAxisTaylorDominanceLiteralAt
      Dinf Binf s c0Val c0Deriv zetaDeriv zetaSecondDeriv)
    (hAlpha : ‖routeK_transversalAlpha c0Val c0Deriv‖ ≤ A)
    (hBeta : routeK_HadamardVonMangoldtBetaBoundAt s zetaDeriv zetaSecondDeriv C) :
    routeK_OffAxisTaylorDominanceHeightLogSqRatioAt Dinf Binf s A C := by
  rcases hTaylor with ⟨R, δ, hM1, hM2, hδ, hδsmall, hR, hRsmall, hF_lb⟩
  rcases routeK_transversalFactors_ne_zero_of_M1_pos hM1 with ⟨hc0, hzeta⟩
  have hRatio :
      routeK_transversalM2 c0Val c0Deriv zetaDeriv zetaSecondDeriv /
          routeK_transversalM1 c0Val zetaDeriv ≤
        routeK_heightLogSqCurvatureEnvelope A C s := by
    simpa [routeK_heightLogSqCurvatureEnvelope,
      routeK_HadamardVonMangoldtBetaBoundAt] using
      routeK_transversalM2_div_M1_le_heightLogSq_of_alpha_beta_bounds
        (s := s) hc0 hzeta hAlpha hBeta
  simpa [routeK_OffAxisTaylorDominanceHeightLogSqRatioAt] using
    (routeK_OffAxisTaylorDominanceRatioEnvelopeAt_of_literalAt_of_ratioBound
      (ratioEnvelope := routeK_heightLogSqCurvatureEnvelope A C)
      ⟨R, δ, hM1, hM2, hδ, hδsmall, hR, hRsmall, hF_lb⟩ hRatio)

/--
Explicit theorem-11 specialization of the previous bridge, using the research
constants `A = 1.5862`, `C = 0.153`.
-/
theorem routeK_OffAxisTaylorDominanceExplicitAt_of_literalAt_of_alpha_bound_of_hadamardBetaBound
    {Dinf Binf : ℂ → ℂ} {s : ℂ}
    {c0Val c0Deriv zetaDeriv zetaSecondDeriv : ℂ}
    (hTaylor : routeK_OffAxisTaylorDominanceLiteralAt
      Dinf Binf s c0Val c0Deriv zetaDeriv zetaSecondDeriv)
    (hAlpha : ‖routeK_transversalAlpha c0Val c0Deriv‖ ≤ routeK_explicitTaylorA)
    (hBeta : routeK_HadamardVonMangoldtBetaBoundExplicitAt s zetaDeriv zetaSecondDeriv) :
    routeK_OffAxisTaylorDominanceExplicitAt Dinf Binf s := by
  simpa [routeK_OffAxisTaylorDominanceExplicitAt,
    routeK_HadamardVonMangoldtBetaBoundExplicitAt] using
    routeK_OffAxisTaylorDominanceHeightLogSqRatioAt_of_literalAt_of_alpha_bound_of_hadamardBetaBound
      (A := routeK_explicitTaylorA) (C := routeK_explicitTaylorC)
      hTaylor hAlpha hBeta

/--
Global bridge from literal local Taylor packages and pointwise `α` /
Hadamard-von-Mangoldt `β` bounds to the structural theorem-11 witness.
-/
theorem routeK_taylor_heightLogSqRatioGlobal_of_literalGlobal_of_alpha_bound_of_hadamardBetaBound
    {Dinf Binf c0Val c0Deriv zetaDeriv zetaSecondDeriv : ℂ → ℂ} {A C : ℝ}
    (hTaylor : routeK_OffAxisTaylorDominanceLiteralGlobal
      Dinf Binf c0Val c0Deriv zetaDeriv zetaSecondDeriv)
    (hAlpha : ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 ->
      ‖routeK_transversalAlpha (c0Val s) (c0Deriv s)‖ ≤ A)
    (hBeta : routeK_HadamardVonMangoldtBetaBoundGlobal zetaDeriv zetaSecondDeriv C) :
    routeK_OffAxisTaylorDominanceHeightLogSqRatioGlobal Dinf Binf A C := by
  intro s hs hstrip hhalf
  exact
    routeK_OffAxisTaylorDominanceHeightLogSqRatioAt_of_literalAt_of_alpha_bound_of_hadamardBetaBound
    (hTaylor s hs hstrip hhalf) (hAlpha s hs hstrip hhalf)
    (hBeta s hs hstrip hhalf)

/--
Global bridge from literal local Taylor packages plus concrete `c₀` lower and
derivative bounds to the structural theorem-11 witness.

The `α` estimate is derived internally from data of the form
`∃ L, 0 < L ∧ L ≤ ‖c₀(s)‖ ∧ ‖c₀'(s)‖ ≤ A*L`.
-/
theorem
  routeK_taylor_heightLogSqRatioGlobal_of_literalGlobal_of_c0_lower_deriv_bound_of_hadamardBetaBound
    {Dinf Binf c0Val c0Deriv zetaDeriv zetaSecondDeriv : ℂ → ℂ} {A C : ℝ}
    (hTaylor : routeK_OffAxisTaylorDominanceLiteralGlobal
      Dinf Binf c0Val c0Deriv zetaDeriv zetaSecondDeriv)
    (hC0 : ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ∃ L : ℝ, 0 < L ∧ L ≤ ‖c0Val s‖ ∧ ‖c0Deriv s‖ ≤ A * L)
    (hBeta : routeK_HadamardVonMangoldtBetaBoundGlobal zetaDeriv zetaSecondDeriv C) :
    routeK_OffAxisTaylorDominanceHeightLogSqRatioGlobal Dinf Binf A C := by
  refine routeK_taylor_heightLogSqRatioGlobal_of_literalGlobal_of_alpha_bound_of_hadamardBetaBound
    hTaylor ?_ hBeta
  intro s hs hstrip hhalf
  rcases hC0 s hs hstrip hhalf with ⟨L, hLpos, hLower, hDeriv⟩
  exact routeK_transversalAlpha_norm_le_of_deriv_bound_and_c0_lower
    hLpos hLower hDeriv

/--
Global explicit theorem-11 bridge from literal local Taylor packages and the
isolated standard Hadamard-von-Mangoldt `β` input.
-/
theorem routeK_taylor_explicitGlobal_of_literalGlobal_of_alpha_bound_of_hadamardBetaBound
    {Dinf Binf c0Val c0Deriv zetaDeriv zetaSecondDeriv : ℂ → ℂ}
    (hTaylor : routeK_OffAxisTaylorDominanceLiteralGlobal
      Dinf Binf c0Val c0Deriv zetaDeriv zetaSecondDeriv)
    (hAlpha : ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 ->
      ‖routeK_transversalAlpha (c0Val s) (c0Deriv s)‖ ≤ routeK_explicitTaylorA)
    (hBeta : routeK_HadamardVonMangoldtBetaBoundExplicitGlobal zetaDeriv zetaSecondDeriv) :
    routeK_OffAxisTaylorDominanceExplicitGlobal Dinf Binf := by
  simpa [routeK_OffAxisTaylorDominanceExplicitGlobal,
    routeK_HadamardVonMangoldtBetaBoundExplicitGlobal] using
    routeK_taylor_heightLogSqRatioGlobal_of_literalGlobal_of_alpha_bound_of_hadamardBetaBound
      (A := routeK_explicitTaylorA) (C := routeK_explicitTaylorC)
      hTaylor hAlpha hBeta

/--
Explicit-constant variant of the concrete `c₀` lower/derivative bridge.
-/
theorem
  routeK_taylor_explicitGlobal_of_literalGlobal_of_c0_lower_deriv_bound_of_hadamardBetaBound
    {Dinf Binf c0Val c0Deriv zetaDeriv zetaSecondDeriv : ℂ → ℂ}
    (hTaylor : routeK_OffAxisTaylorDominanceLiteralGlobal
      Dinf Binf c0Val c0Deriv zetaDeriv zetaSecondDeriv)
    (hC0 : ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ∃ L : ℝ, 0 < L ∧ L ≤ ‖c0Val s‖ ∧
        ‖c0Deriv s‖ ≤ routeK_explicitTaylorA * L)
    (hBeta : routeK_HadamardVonMangoldtBetaBoundExplicitGlobal zetaDeriv zetaSecondDeriv) :
    routeK_OffAxisTaylorDominanceExplicitGlobal Dinf Binf := by
  apply routeK_taylor_explicitGlobal_of_literalGlobal_of_alpha_bound_of_hadamardBetaBound
    hTaylor
  · intro s hs hstrip hhalf
    rcases hC0 s hs hstrip hhalf with ⟨L, hLpos, hLower, hDeriv⟩
    exact routeK_transversalAlpha_norm_le_of_deriv_bound_and_c0_lower
      hLpos hLower hDeriv
  · exact hBeta

/--
Specialized global theorem-11 bridge for the actual normalization factor
`c0Complex`.  The `α` input is reduced to the concrete derivative bound
`‖deriv c0Complex s‖ ≤ A * c0OffAxisLower(s.re)`.
-/
theorem routeK_taylor_ratioGlobal_of_literalGlobal_of_c0DerivBound_of_betaBound
    {Dinf Binf zetaDeriv zetaSecondDeriv : ℂ → ℂ} {A C : ℝ}
    (hTaylor : routeK_OffAxisTaylorDominanceLiteralGlobal
      Dinf Binf c0Complex (deriv c0Complex) zetaDeriv zetaSecondDeriv)
    (hC0 : routeK_C0AlphaDerivativeBoundGlobal A)
    (hBeta : routeK_HadamardVonMangoldtBetaBoundGlobal zetaDeriv zetaSecondDeriv C) :
    routeK_OffAxisTaylorDominanceHeightLogSqRatioGlobal Dinf Binf A C := by
  exact routeK_taylor_heightLogSqRatioGlobal_of_literalGlobal_of_alpha_bound_of_hadamardBetaBound
    hTaylor (routeK_c0Alpha_bound_global_of_derivBoundGlobal hC0) hBeta

/--
Explicit-constant specialization of the `c0Complex` derivative-bound bridge.
-/
theorem routeK_taylor_explicitGlobal_of_literalGlobal_of_c0DerivBound_of_betaBound
    {Dinf Binf zetaDeriv zetaSecondDeriv : ℂ → ℂ}
    (hTaylor : routeK_OffAxisTaylorDominanceLiteralGlobal
      Dinf Binf c0Complex (deriv c0Complex) zetaDeriv zetaSecondDeriv)
    (hC0 : routeK_C0AlphaDerivativeBoundGlobal routeK_explicitTaylorA)
    (hBeta : routeK_HadamardVonMangoldtBetaBoundExplicitGlobal
      zetaDeriv zetaSecondDeriv) :
    routeK_OffAxisTaylorDominanceExplicitGlobal Dinf Binf := by
  exact routeK_taylor_explicitGlobal_of_literalGlobal_of_alpha_bound_of_hadamardBetaBound
    hTaylor (routeK_c0Alpha_bound_global_of_derivBoundGlobal hC0) hBeta

/--
Height-based Taylor-dominance together with the native geometric source
`|Im(s)| ≠ 0`.

This keeps the main Taylor chain independent of Van der Corput.  The optional
VdC module can derive its logarithmic phase-curvature source from the same
nonzero-height condition.
-/
def routeK_OffAxisTaylorDominanceHeightLogSqSourcedAt
    (Dinf Binf : ℂ → ℂ) (s : ℂ) (A C : ℝ) : Prop :=
  routeK_OffAxisTaylorDominanceHeightLogSqAt Dinf Binf s A C ∧
    routeK_offAxisHeight s ≠ 0

/--
Global height-based Taylor-dominance together with the native nonzero-height
source.
-/
def routeK_OffAxisTaylorDominanceHeightLogSqSourcedGlobal
    (Dinf Binf : ℂ → ℂ) (A C : ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
    routeK_OffAxisTaylorDominanceHeightLogSqSourcedAt Dinf Binf s A C

/--
Upgrade a height-based Taylor witness to the sourced form when the internal
height `|Im(s)|` is known to be nonzero.
-/
theorem routeK_OffAxisTaylorDominanceHeightLogSqSourcedAt_of_nonzero_height
    {Dinf Binf : ℂ → ℂ} {s : ℂ} {A C : ℝ}
    (hs : routeK_offAxisHeight s ≠ 0)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqAt Dinf Binf s A C) :
    routeK_OffAxisTaylorDominanceHeightLogSqSourcedAt Dinf Binf s A C := by
  exact ⟨hTaylor, hs⟩

/--
Upgrade a height-based Taylor witness to the sourced form from the more native
geometric hypothesis `Im(s) ≠ 0`.
-/
theorem routeK_OffAxisTaylorDominanceHeightLogSqSourcedAt_of_im_ne_zero
    {Dinf Binf : ℂ → ℂ} {s : ℂ} {A C : ℝ}
    (hs : s.im ≠ 0)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqAt Dinf Binf s A C) :
    routeK_OffAxisTaylorDominanceHeightLogSqSourcedAt Dinf Binf s A C := by
  exact routeK_OffAxisTaylorDominanceHeightLogSqSourcedAt_of_nonzero_height
    ((routeK_offAxisHeight_ne_zero_iff).2 hs) hTaylor

/--
Global upgrade from the height-based witness to the sourced form under a
nonvanishing internal-height hypothesis on the admissible strip.
-/
theorem routeK_OffAxisTaylorDominanceHeightLogSqSourcedGlobal_of_nonzero_height
    {Dinf Binf : ℂ → ℂ} {A C : ℝ}
    (hHeight : ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      routeK_offAxisHeight s ≠ 0)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqGlobal Dinf Binf A C) :
    routeK_OffAxisTaylorDominanceHeightLogSqSourcedGlobal Dinf Binf A C := by
  intro s hs hstrip hhalf
  exact routeK_OffAxisTaylorDominanceHeightLogSqSourcedAt_of_nonzero_height
    (hHeight s hs hstrip hhalf) (hTaylor s hs hstrip hhalf)

/--
Global upgrade from the height-based witness to the sourced form under the
native geometric hypothesis `Im(s) ≠ 0` on the admissible strip.
-/
theorem routeK_OffAxisTaylorDominanceHeightLogSqSourcedGlobal_of_im_ne_zero
    {Dinf Binf : ℂ → ℂ} {A C : ℝ}
    (hIm : ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      s.im ≠ 0)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqGlobal Dinf Binf A C) :
    routeK_OffAxisTaylorDominanceHeightLogSqSourcedGlobal Dinf Binf A C := by
  intro s hs hstrip hhalf
  exact routeK_OffAxisTaylorDominanceHeightLogSqSourcedAt_of_im_ne_zero
    (hIm s hs hstrip hhalf) (hTaylor s hs hstrip hhalf)

/--
Forget the native phase-curvature source and recover the plain height-based
Taylor witness.
-/
theorem routeK_OffAxisTaylorDominanceHeightLogSqAt_of_sourcedAt
    {Dinf Binf : ℂ → ℂ} {s : ℂ} {A C : ℝ}
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqSourcedAt Dinf Binf s A C) :
    routeK_OffAxisTaylorDominanceHeightLogSqAt Dinf Binf s A C :=
  hTaylor.1

/--
Forget the native phase-curvature source and recover the plain global
height-based Taylor witness.
-/
theorem routeK_OffAxisTaylorDominanceHeightLogSqGlobal_of_sourcedGlobal
    {Dinf Binf : ℂ → ℂ} {A C : ℝ}
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqSourcedGlobal Dinf Binf A C) :
    routeK_OffAxisTaylorDominanceHeightLogSqGlobal Dinf Binf A C := by
  intro s hs hstrip hhalf
  exact (hTaylor s hs hstrip hhalf).1

/--
Forget the sourced height-based witness all the way down to the generic
curvature-envelope API.
-/
theorem routeK_OffAxisTaylorDominanceEnvelopeAt_of_heightLogSqSourcedAt
    {Dinf Binf : ℂ → ℂ} {s : ℂ} {A C : ℝ}
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqSourcedAt Dinf Binf s A C) :
    routeK_OffAxisTaylorDominanceEnvelopeAt Dinf Binf s
      (routeK_heightLogSqCurvatureEnvelope A C) :=
  hTaylor.1

/--
Global bridge from the sourced height-based witness to the generic
curvature-envelope API.
-/
theorem routeK_OffAxisTaylorDominanceEnvelopeGlobal_of_heightLogSqSourcedGlobal
    {Dinf Binf : ℂ → ℂ} {A C : ℝ}
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqSourcedGlobal Dinf Binf A C) :
    routeK_OffAxisTaylorDominanceEnvelopeGlobal Dinf Binf
      (routeK_heightLogSqCurvatureEnvelope A C) := by
  intro s hs hstrip hhalf
  exact routeK_OffAxisTaylorDominanceEnvelopeAt_of_heightLogSqSourcedAt
    (hTaylor s hs hstrip hhalf)

/--
Pointwise extraction of the explicit Taylor exclusion-radius data carried by a
Taylor-dominance witness.

In particular, the witness already determines a concrete radius
`δStar = 2m / M₂` with `0 < δ < δStar`.
-/
theorem routeK_taylor_exclusion_radius_data_at
    {Dinf Binf : ℂ → ℂ} {s : ℂ}
    (hTaylor : routeK_OffAxisTaylorDominanceAt Dinf Binf s) :
    ∃ m M₂ δ δStar : ℝ,
      0 < m ∧
      0 < M₂ ∧
      0 < δ ∧
      δStar = 2 * m / M₂ ∧
      δ < δStar ∧
      0 < δStar := by
  rcases hTaylor with ⟨m, M₂, R, δ, hm, hM₂, hδ, hδsmall, hR, hRsmall, hF_lb⟩
  refine ⟨m, M₂, δ, 2 * m / M₂, hm, hM₂, hδ, rfl, ?_, ?_⟩
  · simpa using hδsmall
  · exact routeK_elo5_exclusion_radius_pos m M₂ hm hM₂

/--
Pointwise extraction of explicit Taylor exclusion-radius data from a generic
pointwise curvature envelope `M₂Envelope : ℂ → ℝ`.
-/
theorem routeK_taylor_envelope_exclusion_radius_data_at
    {Dinf Binf : ℂ → ℂ} {s : ℂ} {M₂Envelope : ℂ → ℝ}
    (hTaylor : routeK_OffAxisTaylorDominanceEnvelopeAt Dinf Binf s M₂Envelope) :
    ∃ m M₂ δ δStar : ℝ,
      0 < m ∧
      0 < M₂ ∧
      0 < δ ∧
      δStar = 2 * m / M₂ ∧
      δ < δStar ∧
      0 < δStar ∧
      2 * m / M₂Envelope s ≤ δStar := by
  rcases hTaylor with ⟨m, M₂, R, δ, hm, hM₂, hδ, hδsmall, hR, hRsmall, hF_lb, hM₂le⟩
  refine ⟨m, M₂, δ, 2 * m / M₂, hm, hM₂, hδ, rfl, ?_, ?_, ?_⟩
  · simpa using hδsmall
  · exact routeK_elo5_exclusion_radius_pos m M₂ hm hM₂
  · have hEnvelopePos : 0 < M₂Envelope s := lt_of_lt_of_le hM₂ hM₂le
    exact routeK_thm10_deltaStar_lower_bound_scaled_from_M2bound
      m M₂ (M₂Envelope s) hm hM₂ hEnvelopePos hM₂le

/--
Pointwise extraction of explicit Taylor exclusion-radius data from a normalized
pointwise bound on the ratio `M₂ / m`.

This is the direct theorem-11 shape: the lower bound on `δStar` no longer
retains the factor `m`.
-/
theorem routeK_taylor_ratio_envelope_exclusion_radius_data_at
    {Dinf Binf : ℂ → ℂ} {s : ℂ} {ratioEnvelope : ℂ → ℝ}
    (hTaylor : routeK_OffAxisTaylorDominanceRatioEnvelopeAt Dinf Binf s ratioEnvelope) :
    ∃ m M₂ δ δStar : ℝ,
      0 < m ∧
      0 < M₂ ∧
      0 < δ ∧
      δStar = 2 * m / M₂ ∧
      δ < δStar ∧
      0 < δStar ∧
      2 / ratioEnvelope s ≤ δStar := by
  rcases hTaylor with ⟨m, M₂, R, δ, hm, hM₂, hδ, hδsmall, hR, hRsmall, hF_lb, hRatio⟩
  refine ⟨m, M₂, δ, 2 * m / M₂, hm, hM₂, hδ, rfl, ?_, ?_, ?_⟩
  · simpa using hδsmall
  · exact routeK_elo5_exclusion_radius_pos m M₂ hm hM₂
  · have hRatioPos : 0 < M₂ / m := div_pos hM₂ hm
    have hEnvelopePos : 0 < ratioEnvelope s := lt_of_lt_of_le hRatioPos hRatio
    have hm_ne : m ≠ 0 := ne_of_gt hm
    have hM₂le : M₂ ≤ ratioEnvelope s * m := by
      have hRatioMul : M₂ / m * m ≤ ratioEnvelope s * m :=
        mul_le_mul_of_nonneg_right hRatio (le_of_lt hm)
      simpa [div_eq_mul_inv, hm_ne, mul_assoc] using hRatioMul
    have hScaled :
        2 * m / (ratioEnvelope s * m) ≤ 2 * m / M₂ :=
      routeK_thm10_deltaStar_lower_bound_scaled_from_M2bound
        m M₂ (ratioEnvelope s * m) hm hM₂ (mul_pos hEnvelopePos hm) hM₂le
    have hEnvelopeNe : ratioEnvelope s ≠ 0 := ne_of_gt hEnvelopePos
    have hcancel : 2 * m / (ratioEnvelope s * m) = 2 / ratioEnvelope s := by
      rw [mul_comm (ratioEnvelope s) m]
      field_simp [hm_ne, hEnvelopeNe]
    simpa [hcancel] using hScaled

/--
Pointwise extraction of explicit Taylor exclusion-radius data together with the
parametric lower bound coming from `M₂ ≤ 2A + C*L`.
-/
theorem routeK_taylor_parametric_exclusion_radius_data_at
    {Dinf Binf : ℂ → ℂ} {s : ℂ} {A C L : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C) (_hL : 0 ≤ L)
    (hTaylor : routeK_OffAxisTaylorDominanceParametricAt Dinf Binf s A C L) :
    ∃ m M₂ δ δStar : ℝ,
      0 < m ∧
      0 < M₂ ∧
      0 < δ ∧
      δStar = 2 * m / M₂ ∧
      δ < δStar ∧
      0 < δStar ∧
      2 * m / (2 * A + C * L) ≤ δStar := by
  simpa [routeK_OffAxisTaylorDominanceParametricAt,
    routeK_OffAxisTaylorDominanceEnvelopeAt,
    routeK_OffAxisTaylorDominanceBoundedAt,
    routeK_OffAxisCurvatureEnvelopeAt,
    routeK_parametricCurvatureEnvelope]
    using routeK_taylor_envelope_exclusion_radius_data_at
      (Dinf := Dinf) (Binf := Binf) (s := s)
      (M₂Envelope := routeK_parametricCurvatureEnvelope A C L) hTaylor

/--
Global off-axis extraction of the explicit Taylor exclusion-radius data.
-/
theorem routeK_offaxis_taylor_exclusion_radius_data_global
    {Dinf Binf : ℂ → ℂ}
    (hTaylor : routeK_OffAxisTaylorDominanceGlobal Dinf Binf) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar := by
  intro s hs hstrip hhalf
  exact routeK_taylor_exclusion_radius_data_at
    (hTaylor s hs hstrip hhalf)

/--
Global off-axis extraction of explicit Taylor exclusion-radius data from a
generic pointwise curvature envelope `M₂Envelope : ℂ → ℝ`.
-/
theorem routeK_offaxis_taylor_envelope_exclusion_radius_data_global
    {Dinf Binf : ℂ → ℂ} {M₂Envelope : ℂ → ℝ}
    (hTaylor : routeK_OffAxisTaylorDominanceEnvelopeGlobal Dinf Binf M₂Envelope) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / M₂Envelope s ≤ δStar := by
  intro s hs hstrip hhalf
  exact routeK_taylor_envelope_exclusion_radius_data_at
    (hTaylor s hs hstrip hhalf)

/--
Global off-axis extraction of explicit Taylor exclusion-radius data from a
normalized pointwise bound on `M₂ / m`.
-/
theorem routeK_offaxis_taylor_ratio_envelope_exclusion_radius_data_global
    {Dinf Binf : ℂ → ℂ} {ratioEnvelope : ℂ → ℝ}
    (hTaylor : routeK_OffAxisTaylorDominanceRatioEnvelopeGlobal Dinf Binf ratioEnvelope) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 / ratioEnvelope s ≤ δStar := by
  intro s hs hstrip hhalf
  exact routeK_taylor_ratio_envelope_exclusion_radius_data_at
    (hTaylor s hs hstrip hhalf)

/--
Global off-axis extraction of explicit Taylor exclusion-radius data together
with the parametric lower bound induced by `M₂ ≤ 2A + C*L`.
-/
theorem routeK_offaxis_taylor_parametric_exclusion_radius_data_global
    {Dinf Binf : ℂ → ℂ} {A C L : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C) (_hL : 0 ≤ L)
    (hTaylor : routeK_OffAxisTaylorDominanceParametricGlobal Dinf Binf A C L) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / (2 * A + C * L) ≤ δStar := by
  simpa [routeK_OffAxisTaylorDominanceParametricGlobal,
    routeK_OffAxisTaylorDominanceEnvelopeGlobal,
    routeK_parametricCurvatureEnvelope]
    using routeK_offaxis_taylor_envelope_exclusion_radius_data_global
      (Dinf := Dinf) (Binf := Binf)
      (M₂Envelope := routeK_parametricCurvatureEnvelope A C L) hTaylor

/--
Pointwise extraction of explicit Taylor exclusion-radius data from the
structural height-based logarithmic envelope.
-/
theorem routeK_taylor_heightLogSq_exclusion_radius_data_at
    {Dinf Binf : ℂ → ℂ} {s : ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqAt Dinf Binf s A C) :
    ∃ m M₂ δ δStar : ℝ,
      0 < m ∧
      0 < M₂ ∧
      0 < δ ∧
      δStar = 2 * m / M₂ ∧
      δ < δStar ∧
      0 < δStar ∧
      2 * m / routeK_logSqM2Envelope A C s ≤ δStar := by
  simpa [routeK_OffAxisTaylorDominanceHeightLogSqAt,
    routeK_OffAxisTaylorDominanceEnvelopeAt,
    routeK_OffAxisTaylorDominanceBoundedAt,
    routeK_OffAxisCurvatureEnvelopeAt,
    routeK_heightLogSqCurvatureEnvelope,
    routeK_OffAxisHeightLogSqCurvatureBoundAt]
    using routeK_taylor_envelope_exclusion_radius_data_at
      (Dinf := Dinf) (Binf := Binf) (s := s)
      (M₂Envelope := routeK_heightLogSqCurvatureEnvelope A C) hTaylor

/--
Pointwise extraction of the theorem-11 exclusion radius from the normalized
`log² |Im(s)|` witness `M₂ / m ≤ 2A + C (log |Im(s)|)^2`.
-/
theorem routeK_taylor_heightLogSq_ratio_exclusion_radius_data_at
    {Dinf Binf : ℂ → ℂ} {s : ℂ} {A C : ℝ}
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqRatioAt Dinf Binf s A C) :
    ∃ m M₂ δ δStar : ℝ,
      0 < m ∧
      0 < M₂ ∧
      0 < δ ∧
      δStar = 2 * m / M₂ ∧
      δ < δStar ∧
      0 < δStar ∧
      2 / routeK_logSqM2Envelope A C s ≤ δStar := by
  simpa [routeK_OffAxisTaylorDominanceHeightLogSqRatioAt,
    routeK_heightLogSqCurvatureEnvelope]
    using routeK_taylor_ratio_envelope_exclusion_radius_data_at
      (Dinf := Dinf) (Binf := Binf) (s := s)
      (ratioEnvelope := routeK_heightLogSqCurvatureEnvelope A C) hTaylor

/--
Pointwise extraction of the theorem-11 exclusion radius in the explicit
constant regime `A = 1.5862`, `C = 0.153`.
-/
theorem routeK_taylor_explicit_exclusion_radius_data_at
    {Dinf Binf : ℂ → ℂ} {s : ℂ}
    (hTaylor : routeK_OffAxisTaylorDominanceExplicitAt Dinf Binf s) :
    ∃ m M₂ δ δStar : ℝ,
      0 < m ∧
      0 < M₂ ∧
      0 < δ ∧
      δStar = 2 * m / M₂ ∧
      δ < δStar ∧
      0 < δStar ∧
      2 / routeK_logSqM2Envelope routeK_explicitTaylorA routeK_explicitTaylorC s ≤ δStar := by
  simpa [routeK_OffAxisTaylorDominanceExplicitAt]
    using routeK_taylor_heightLogSq_ratio_exclusion_radius_data_at
      (Dinf := Dinf) (Binf := Binf) (s := s)
      (A := routeK_explicitTaylorA) (C := routeK_explicitTaylorC) hTaylor

/--
Global off-axis extraction of explicit Taylor exclusion-radius data from the
structural height-based logarithmic envelope.
-/
theorem routeK_offaxis_taylor_heightLogSq_exclusion_radius_data_global
    {Dinf Binf : ℂ → ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / routeK_logSqM2Envelope A C s ≤ δStar := by
  simpa [routeK_OffAxisTaylorDominanceHeightLogSqGlobal,
    routeK_OffAxisTaylorDominanceEnvelopeGlobal,
    routeK_heightLogSqCurvatureEnvelope]
    using routeK_offaxis_taylor_envelope_exclusion_radius_data_global
      (Dinf := Dinf) (Binf := Binf)
      (M₂Envelope := routeK_heightLogSqCurvatureEnvelope A C) hTaylor

/--
Global off-axis extraction of the theorem-11 exclusion radius from the
normalized `log² |Im(s)|` witness `M₂ / m ≤ 2A + C (log |Im(s)|)^2`.
-/
theorem routeK_offaxis_taylor_heightLogSq_ratio_exclusion_radius_data_global
    {Dinf Binf : ℂ → ℂ} {A C : ℝ}
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqRatioGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 / routeK_logSqM2Envelope A C s ≤ δStar := by
  intro s hs hstrip hhalf
  exact routeK_taylor_heightLogSq_ratio_exclusion_radius_data_at
    (hTaylor s hs hstrip hhalf)

/--
Global off-axis extraction of the theorem-11 exclusion radius in the explicit
constant regime `A = 1.5862`, `C = 0.153`.
-/
theorem routeK_offaxis_taylor_explicit_exclusion_radius_data_global
    {Dinf Binf : ℂ → ℂ}
    (hTaylor : routeK_OffAxisTaylorDominanceExplicitGlobal Dinf Binf) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 / routeK_logSqM2Envelope routeK_explicitTaylorA routeK_explicitTaylorC s ≤ δStar := by
  intro s hs hstrip hhalf
  exact routeK_taylor_explicit_exclusion_radius_data_at
    (hTaylor s hs hstrip hhalf)

/--
Pointwise extraction of explicit Taylor exclusion-radius data from the
height-based witness together with the native nonzero-height source.
-/
theorem routeK_taylor_heightLogSq_sourced_exclusion_radius_data_at
    {Dinf Binf : ℂ → ℂ} {s : ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqSourcedAt Dinf Binf s A C) :
    ∃ m M₂ δ δStar : ℝ,
      0 < m ∧
      0 < M₂ ∧
      0 < δ ∧
      δStar = 2 * m / M₂ ∧
      δ < δStar ∧
      0 < δStar ∧
      2 * m / routeK_logSqM2Envelope A C s ≤ δStar := by
  exact routeK_taylor_heightLogSq_exclusion_radius_data_at _hA _hC
    (routeK_OffAxisTaylorDominanceHeightLogSqAt_of_sourcedAt hTaylor)

/--
Global extraction of explicit Taylor exclusion-radius data from the
height-based witness together with the native nonzero-height source.
-/
theorem routeK_offaxis_taylor_heightLogSq_sourced_exclusion_radius_data_global
    {Dinf Binf : ℂ → ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqSourcedGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / routeK_logSqM2Envelope A C s ≤ δStar := by
  intro s hs hstrip hhalf
  exact routeK_taylor_heightLogSq_sourced_exclusion_radius_data_at _hA _hC
    (hTaylor s hs hstrip hhalf)

/--
Pointwise strict norm positivity of the numerator from a Taylor-dominance
witness.
-/
theorem routeK_numerator_norm_pos_of_taylor_dominance_at
    {Dinf Binf : ℂ → ℂ} {s : ℂ}
    (hTaylor : routeK_OffAxisTaylorDominanceAt Dinf Binf s) :
    0 < ‖Dinf s - Binf s‖ := by
  rcases hTaylor with ⟨m, M₂, R, δ, hm, hM₂, hδ, hδsmall, hR, hRsmall, hF_lb⟩
  have hmain : 0 < δ * m - δ ^ 2 / 2 * M₂ :=
    routeK_elo5_firstorder_dominates m M₂ δ hm hM₂ hδ hδsmall
  have hgap : 0 < δ * m - δ ^ 2 / 2 * M₂ - R := by
    linarith
  exact lt_of_lt_of_le hgap hF_lb

/--
Global off-axis strict norm positivity of the numerator from Taylor-dominance
data.
-/
theorem routeK_offaxis_numerator_norm_pos_of_taylor_dominance_global
    {Dinf Binf : ℂ → ℂ}
    (hTaylor : routeK_OffAxisTaylorDominanceGlobal Dinf Binf) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖Dinf s - Binf s‖ := by
  intro s hs hstrip hhalf
  exact routeK_numerator_norm_pos_of_taylor_dominance_at
    (hTaylor s hs hstrip hhalf)

/--
Pointwise numerator nonvanishing from a Taylor-dominance witness.
-/
theorem routeK_numerator_nonzero_of_taylor_dominance_at
    {Dinf Binf : ℂ → ℂ} {s : ℂ}
    (hTaylor : routeK_OffAxisTaylorDominanceAt Dinf Binf s) :
    Dinf s - Binf s ≠ 0 := by
  exact norm_pos_iff.mp
    (routeK_numerator_norm_pos_of_taylor_dominance_at hTaylor)

/--
Global off-axis numerator nonvanishing from Taylor-dominance data.
-/
theorem routeK_offaxis_numerator_nonzero_of_taylor_dominance_global
    {Dinf Binf : ℂ → ℂ}
    (hTaylor : routeK_OffAxisTaylorDominanceGlobal Dinf Binf) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      Dinf s - Binf s ≠ 0 := by
  intro s hs hstrip hhalf
  exact routeK_numerator_nonzero_of_taylor_dominance_at
    (hTaylor s hs hstrip hhalf)

/--
Pointwise zeta-side nonvanishing from Taylor domination of the numerator.
-/
theorem routeK_zeta_nonzero_of_taylor_dominance_at
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {s : ℂ}
    (hCont : ∀ z : ℂ, 0 < z.re → Dinf z - Binf z = c0Complex z * ζfun z)
    (hs : 0 < s.re)
    (hTaylor : routeK_OffAxisTaylorDominanceAt Dinf Binf s) :
    ζfun s ≠ 0 := by
  have hnum : Dinf s - Binf s ≠ 0 :=
    routeK_numerator_nonzero_of_taylor_dominance_at hTaylor
  exact (routeK_continuation_nonzero_iff_zeta_nonzero
    (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) hCont s hs).1 hnum

/--
Global off-axis zeta-side nonvanishing from Taylor-dominance data.
-/
theorem routeK_offaxis_zeta_nonzero_of_taylor_dominance_global
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ z : ℂ, 0 < z.re → Dinf z - Binf z = c0Complex z * ζfun z)
    (hTaylor : routeK_OffAxisTaylorDominanceGlobal Dinf Binf) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ζfun s ≠ 0 := by
  intro s hs hstrip hhalf
  have hAt : routeK_OffAxisTaylorDominanceAt Dinf Binf s :=
    hTaylor s hs hstrip hhalf
  exact routeK_zeta_nonzero_of_taylor_dominance_at hCont hs hAt
end LeanC2
