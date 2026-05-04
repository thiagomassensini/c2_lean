import Mathlib
import LeanC2.Chain
import LeanC2.TransversalAnalytic

namespace LeanC2

/-!
# Full Chain Endpoint Module

This module packages the currently available endpoint closure of the C2 chain:
the internal ELO 1-7 chain from `Chain.lean`, plus the off-axis numerator/zeta
nonvanishing consequences obtainable from Taylor-dominance data.
-/

theorem routeK_full_chain_norm_pos_with_data_of_nonzero_with_data
    {F : ℂ → ℂ} {P : ℂ → Prop}
    (hEndpoint :
      ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
        F s ≠ 0 ∧ P s) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖F s‖ ∧ P s := by
  intro s hs hstrip hhalf
  rcases hEndpoint s hs hstrip hhalf with ⟨hF, hP⟩
  exact ⟨norm_pos_iff.mpr hF, hP⟩

theorem routeK_full_chain_Zspec_norm_pos_with_data_of_zeta_nonzero_with_data
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {P : ℂ → Prop}
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hEndpoint :
      ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
        ζfun s ≠ 0 ∧ P s) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖routeK_Zspec Dinf Binf s‖ ∧ P s := by
  intro s hs hstrip hhalf
  rcases hEndpoint s hs hstrip hhalf with ⟨hζ, hP⟩
  exact ⟨routeK_continuation_Zspec_norm_pos_of_zeta_nonzero
    (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) hCont hs hζ, hP⟩

/--
Full-chain C2-only six-barrier bundle from pointwise Taylor dominance.

This remains C2-facing: Taylor dominance supplies nonvanishing of the C2
numerator `D∞ - B∞`, while the off-axis barrier and leader/tail noncancellation
come from the C2-internal chain.
-/
theorem routeK_full_chain_c2_only_six_barrier_bundle_of_taylor_dominance_at
    {Dinf Binf : ℂ → ℂ} {s leader tail : ℂ}
    (hs : 0 < s.re) (hstrip : s.re < 1)
    (hhalf : s.re ≠ (1 : ℝ) / 2)
    (hdom : routeK_C2HierarchicalDominance leader tail)
    (hTaylor : routeK_OffAxisTaylorDominanceAt Dinf Binf s) :
    routeK_C2OnlySixBarrierBundleAt s leader tail (Dinf s - Binf s) := by
  exact routeK_c2_only_six_barrier_bundle_at hs hstrip hhalf hdom
    (routeK_numerator_norm_pos_of_taylor_dominance_at hTaylor)

/--
Finite-tail full-chain form of the C2-only six-barrier bundle, with the
numerator endpoint discharged by Taylor dominance.
-/
theorem routeK_full_chain_c2_only_six_barrier_bundle_from_tail_sum_of_taylor_dominance_at
    {ι : Type*} (S : Finset ι)
    {Dinf Binf : ℂ → ℂ} {s leader : ℂ} (tail : ι → ℂ)
    (hs : 0 < s.re) (hstrip : s.re < 1)
    (hhalf : s.re ≠ (1 : ℝ) / 2)
    (hdom : (∑ i ∈ S, ‖tail i‖) < ‖leader‖)
    (hTaylor : routeK_OffAxisTaylorDominanceAt Dinf Binf s) :
    routeK_C2OnlySixBarrierBundleAt s leader (∑ i ∈ S, tail i) (Dinf s - Binf s) := by
  exact routeK_c2_only_six_barrier_bundle_from_tail_sum (S := S) (tail := tail)
    hs hstrip hhalf hdom
    (routeK_numerator_norm_pos_of_taylor_dominance_at hTaylor)

/--
Ratio-tail full-chain form of the C2-only six-barrier bundle, with
`tail ≤ r * leader`, `r < 1`, and numerator nonvanishing supplied by Taylor
dominance.
-/
theorem routeK_full_chain_c2_only_six_barrier_bundle_from_ratio_of_taylor_dominance_at
    {ι : Type*} (S : Finset ι)
    {Dinf Binf : ℂ → ℂ} {s leader : ℂ} (tail : ι → ℂ) {r : ℝ}
    (hs : 0 < s.re) (hstrip : s.re < 1)
    (hhalf : s.re ≠ (1 : ℝ) / 2)
    (hleader : 0 < ‖leader‖)
    (htail : (∑ i ∈ S, ‖tail i‖) ≤ r * ‖leader‖)
    (hr : r < 1)
    (hTaylor : routeK_OffAxisTaylorDominanceAt Dinf Binf s) :
    routeK_C2OnlySixBarrierBundleAt s leader (∑ i ∈ S, tail i) (Dinf s - Binf s) := by
  exact routeK_c2_only_six_barrier_bundle_from_ratio (S := S) (tail := tail)
    hs hstrip hhalf hleader htail hr
    (routeK_numerator_norm_pos_of_taylor_dominance_at hTaylor)

/--
Full-chain endpoint on the numerator side from global Taylor-dominance data.
-/
theorem routeK_full_chain_numerator_endpoint_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ}
    (hTaylor : routeK_OffAxisTaylorDominanceGlobal Dinf Binf) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      Dinf s - Binf s ≠ 0 := by
  exact routeK_offaxis_numerator_nonzero_of_taylor_dominance_global hTaylor

/--
Full-chain numerator endpoint together with an explicit exclusion radius coming
from a generic pointwise curvature envelope `M₂Envelope : ℂ → ℝ`.
-/
theorem routeK_full_chain_numerator_envelope_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {M₂Envelope : ℂ → ℝ}
    (hTaylor : routeK_OffAxisTaylorDominanceEnvelopeGlobal Dinf Binf M₂Envelope) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      Dinf s - Binf s ≠ 0 ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / M₂Envelope s ≤ δStar := by
  intro s hs hstrip hhalf
  have hAt : routeK_OffAxisTaylorDominanceEnvelopeAt Dinf Binf s M₂Envelope :=
    hTaylor s hs hstrip hhalf
  rcases hAt with ⟨m, M₂, R, δ, hm, hM₂, hδ, hδsmall, hR, hRsmall, hF_lb, hM₂le⟩
  have hBase : routeK_OffAxisTaylorDominanceAt Dinf Binf s :=
    ⟨m, M₂, R, δ, hm, hM₂, hδ, hδsmall, hR, hRsmall, hF_lb⟩
  refine ⟨routeK_numerator_nonzero_of_taylor_dominance_at hBase, ?_⟩
  exact routeK_taylor_envelope_exclusion_radius_data_at
    ⟨m, M₂, R, δ, hm, hM₂, hδ, hδsmall, hR, hRsmall, hF_lb, hM₂le⟩

/--
Full-chain quantitative numerator endpoint together with an explicit exclusion
radius coming from a generic pointwise curvature envelope.
-/
theorem routeK_full_chain_numerator_norm_pos_envelope_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {M₂Envelope : ℂ → ℝ}
    (hTaylor : routeK_OffAxisTaylorDominanceEnvelopeGlobal Dinf Binf M₂Envelope) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖Dinf s - Binf s‖ ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / M₂Envelope s ≤ δStar := by
  exact routeK_full_chain_norm_pos_with_data_of_nonzero_with_data
    (routeK_full_chain_numerator_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) (M₂Envelope := M₂Envelope) hTaylor)

/--
Full-chain numerator endpoint together with an explicit parametric lower bound
for the Taylor exclusion radius.
-/
theorem routeK_full_chain_numerator_parametric_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {A C L : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C) (_hL : 0 ≤ L)
    (hTaylor : routeK_OffAxisTaylorDominanceParametricGlobal Dinf Binf A C L) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      Dinf s - Binf s ≠ 0 ∧
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
    using routeK_full_chain_numerator_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf)
      (M₂Envelope := routeK_parametricCurvatureEnvelope A C L) hTaylor

/--
Full-chain numerator endpoint with the concrete logarithmic bound
`M₂ ≤ 2A + C (log γ)^2`.
-/
theorem routeK_full_chain_numerator_logSq_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {A C γ : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hTaylor : routeK_OffAxisTaylorDominanceParametricGlobal
      Dinf Binf A C ((Real.log γ) ^ 2)) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      Dinf s - Binf s ≠ 0 ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / (2 * A + C * (Real.log γ) ^ 2) ≤ δStar := by
  exact routeK_full_chain_numerator_parametric_exclusion_radius_of_taylor_dominance
    _hA _hC (sq_nonneg (Real.log γ)) hTaylor

/--
Full-chain numerator endpoint with the structural logarithmic bound tied to the
internal point height `|Im(s)|`.
-/
theorem routeK_full_chain_numerator_heightLogSq_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      Dinf s - Binf s ≠ 0 ∧
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
    using routeK_full_chain_numerator_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf)
      (M₂Envelope := routeK_heightLogSqCurvatureEnvelope A C) hTaylor

/--
Full-chain numerator endpoint with the structural logarithmic bound tied to the
internal point height `|Im(s)|`, together with the native nonzero-height
source.
-/
theorem routeK_full_chain_numerator_heightLogSq_sourced_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqSourcedGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      Dinf s - Binf s ≠ 0 ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / routeK_logSqM2Envelope A C s ≤ δStar := by
  simpa [routeK_heightLogSqCurvatureEnvelope]
    using routeK_full_chain_numerator_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf)
      (M₂Envelope := routeK_heightLogSqCurvatureEnvelope A C)
      (routeK_OffAxisTaylorDominanceEnvelopeGlobal_of_heightLogSqSourcedGlobal hTaylor)

/--
Derived sourced numerator endpoint from the native geometric hypothesis
`Im(s) ≠ 0` and the structural height-log-squared witness.
-/
theorem
  routeK_full_chain_numerator_heightLogSq_sourced_exclusion_radius_of_im_ne_zero
    {Dinf Binf : ℂ → ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hIm : ∀ s : ℂ,
      0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 → s.im ≠ 0)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      Dinf s - Binf s ≠ 0 ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / routeK_logSqM2Envelope A C s ≤ δStar := by
  exact routeK_full_chain_numerator_heightLogSq_sourced_exclusion_radius_of_taylor_dominance
    _hA _hC
    (routeK_OffAxisTaylorDominanceHeightLogSqSourcedGlobal_of_im_ne_zero hIm hTaylor)

/--
Full-chain quantitative endpoint on the numerator side together with an
explicit parametric lower bound for the Taylor exclusion radius.
-/
theorem routeK_full_chain_numerator_norm_pos_parametric_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {A C L : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C) (_hL : 0 ≤ L)
    (hTaylor : routeK_OffAxisTaylorDominanceParametricGlobal Dinf Binf A C L) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖Dinf s - Binf s‖ ∧
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
    using routeK_full_chain_numerator_norm_pos_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf)
      (M₂Envelope := routeK_parametricCurvatureEnvelope A C L) hTaylor

/--
Full-chain quantitative endpoint on the numerator side with the concrete
logarithmic bound `M₂ ≤ 2A + C (log γ)^2`.
-/
theorem routeK_full_chain_numerator_norm_pos_logSq_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {A C γ : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hTaylor : routeK_OffAxisTaylorDominanceParametricGlobal
      Dinf Binf A C ((Real.log γ) ^ 2)) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖Dinf s - Binf s‖ ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / (2 * A + C * (Real.log γ) ^ 2) ≤ δStar := by
  exact routeK_full_chain_norm_pos_with_data_of_nonzero_with_data
    (routeK_full_chain_numerator_logSq_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) _hA _hC hTaylor)

/--
Full-chain quantitative endpoint on the numerator side with the structural
logarithmic bound tied to the internal point height `|Im(s)|`.
-/
theorem routeK_full_chain_numerator_norm_pos_heightLogSq_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖Dinf s - Binf s‖ ∧
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
    using routeK_full_chain_numerator_norm_pos_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf)
      (M₂Envelope := routeK_heightLogSqCurvatureEnvelope A C) hTaylor

/--
Full-chain quantitative numerator endpoint for the sourced structural
height-based theorem-11 witness.
-/
theorem
  routeK_full_chain_numerator_norm_pos_heightLogSq_sourced_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqSourcedGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖Dinf s - Binf s‖ ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / routeK_logSqM2Envelope A C s ≤ δStar := by
  simpa [routeK_heightLogSqCurvatureEnvelope]
    using routeK_full_chain_numerator_norm_pos_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf)
      (M₂Envelope := routeK_heightLogSqCurvatureEnvelope A C)
      (routeK_OffAxisTaylorDominanceEnvelopeGlobal_of_heightLogSqSourcedGlobal hTaylor)

/--
Derived quantitative sourced numerator endpoint from `Im(s) ≠ 0` and the
structural height-log-squared witness.
-/
theorem
  routeK_full_chain_numerator_norm_pos_heightLogSq_sourced_exclusion_radius_of_im_ne_zero
    {Dinf Binf : ℂ → ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hIm : ∀ s : ℂ,
      0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 → s.im ≠ 0)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖Dinf s - Binf s‖ ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / routeK_logSqM2Envelope A C s ≤ δStar := by
  exact
    routeK_full_chain_numerator_norm_pos_heightLogSq_sourced_exclusion_radius_of_taylor_dominance
    _hA _hC
    (routeK_OffAxisTaylorDominanceHeightLogSqSourcedGlobal_of_im_ne_zero hIm hTaylor)

/--
Full-chain endpoint on the zeta side together with an explicit exclusion
radius coming from a generic pointwise curvature envelope.
-/
theorem routeK_full_chain_zeta_envelope_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {M₂Envelope : ℂ → ℝ}
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceEnvelopeGlobal Dinf Binf M₂Envelope) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ζfun s ≠ 0 ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / M₂Envelope s ≤ δStar := by
  intro s hs hstrip hhalf
  rcases routeK_full_chain_numerator_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) (M₂Envelope := M₂Envelope)
      hTaylor s hs hstrip hhalf with ⟨hNum, hRadius⟩
  have hζ : ζfun s ≠ 0 :=
    (routeK_continuation_nonzero_iff_zeta_nonzero
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) hCont s hs).1 hNum
  exact ⟨hζ, hRadius⟩

/--
Full-chain endpoint on the `Z_spec` side together with an explicit exclusion
radius coming from a generic pointwise curvature envelope.
-/
theorem routeK_full_chain_Zspec_envelope_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {M₂Envelope : ℂ → ℝ}
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceEnvelopeGlobal Dinf Binf M₂Envelope) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      routeK_Zspec Dinf Binf s ≠ 0 ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / M₂Envelope s ≤ δStar := by
  intro s hs hstrip hhalf
  rcases routeK_full_chain_zeta_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) (M₂Envelope := M₂Envelope)
      hCont hTaylor s hs hstrip hhalf with ⟨hζ, hRadius⟩
  have hZspec : routeK_Zspec Dinf Binf s ≠ 0 := by
    intro hZ0
    exact hζ ((routeK_continuation_zero_iff
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) hCont hs).1 hZ0)
  exact ⟨hZspec, hRadius⟩

/--
Full-chain endpoint on the zeta side together with an explicit parametric lower
bound for the Taylor exclusion radius.
-/
theorem routeK_full_chain_zeta_parametric_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {A C L : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C) (_hL : 0 ≤ L)
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceParametricGlobal Dinf Binf A C L) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ζfun s ≠ 0 ∧
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
    using routeK_full_chain_zeta_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun)
      (M₂Envelope := routeK_parametricCurvatureEnvelope A C L) hCont hTaylor

/--
Full-chain endpoint on the `Z_spec` side together with an explicit parametric
lower bound for the Taylor exclusion radius.
-/
theorem routeK_full_chain_Zspec_parametric_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {A C L : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C) (_hL : 0 ≤ L)
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceParametricGlobal Dinf Binf A C L) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      routeK_Zspec Dinf Binf s ≠ 0 ∧
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
    using routeK_full_chain_Zspec_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun)
      (M₂Envelope := routeK_parametricCurvatureEnvelope A C L) hCont hTaylor

/--
Full-chain endpoint on the zeta side with the concrete logarithmic bound
`M₂ ≤ 2A + C (log γ)^2`.
-/
theorem routeK_full_chain_zeta_logSq_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {A C γ : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceParametricGlobal
      Dinf Binf A C ((Real.log γ) ^ 2)) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ζfun s ≠ 0 ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / (2 * A + C * (Real.log γ) ^ 2) ≤ δStar := by
  exact routeK_full_chain_zeta_parametric_exclusion_radius_of_taylor_dominance
    _hA _hC (sq_nonneg (Real.log γ)) hCont hTaylor

/--
Full-chain endpoint on the `Z_spec` side with the concrete logarithmic bound
`M₂ ≤ 2A + C (log γ)^2`.
-/
theorem routeK_full_chain_Zspec_logSq_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {A C γ : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceParametricGlobal
      Dinf Binf A C ((Real.log γ) ^ 2)) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      routeK_Zspec Dinf Binf s ≠ 0 ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / (2 * A + C * (Real.log γ) ^ 2) ≤ δStar := by
  exact routeK_full_chain_Zspec_parametric_exclusion_radius_of_taylor_dominance
    _hA _hC (sq_nonneg (Real.log γ)) hCont hTaylor

/--
Full-chain quantitative endpoint on the `Z_spec` side together with an
explicit parametric lower bound for the Taylor exclusion radius.
-/
theorem routeK_full_chain_Zspec_norm_pos_parametric_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {A C L : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C) (_hL : 0 ≤ L)
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceParametricGlobal Dinf Binf A C L) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖routeK_Zspec Dinf Binf s‖ ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / (2 * A + C * L) ≤ δStar := by
  exact routeK_full_chain_Zspec_norm_pos_with_data_of_zeta_nonzero_with_data
    (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) hCont
    (routeK_full_chain_zeta_parametric_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) _hA _hC _hL hCont hTaylor)

/--
Full-chain quantitative endpoint on the `Z_spec` side with the concrete
logarithmic bound `M₂ ≤ 2A + C (log γ)^2`.
-/
theorem routeK_full_chain_Zspec_norm_pos_logSq_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {A C γ : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceParametricGlobal
      Dinf Binf A C ((Real.log γ) ^ 2)) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖routeK_Zspec Dinf Binf s‖ ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / (2 * A + C * (Real.log γ) ^ 2) ≤ δStar := by
  exact routeK_full_chain_Zspec_norm_pos_with_data_of_zeta_nonzero_with_data
    (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) hCont
    (routeK_full_chain_zeta_logSq_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) _hA _hC hCont hTaylor)

/--
Full-chain endpoint on the zeta side with the structural logarithmic bound
tied to the internal point height `|Im(s)|`.
-/
theorem routeK_full_chain_zeta_heightLogSq_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ζfun s ≠ 0 ∧
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
    using routeK_full_chain_zeta_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun)
      (M₂Envelope := routeK_heightLogSqCurvatureEnvelope A C) hCont hTaylor

/--
Full-chain endpoint on the zeta side for the sourced structural height-based
theorem-11 witness.
-/
theorem routeK_full_chain_zeta_heightLogSq_sourced_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqSourcedGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ζfun s ≠ 0 ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / routeK_logSqM2Envelope A C s ≤ δStar := by
  simpa [routeK_heightLogSqCurvatureEnvelope]
    using routeK_full_chain_zeta_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun)
      (M₂Envelope := routeK_heightLogSqCurvatureEnvelope A C) hCont
      (routeK_OffAxisTaylorDominanceEnvelopeGlobal_of_heightLogSqSourcedGlobal hTaylor)

/--
Derived sourced zeta endpoint from `Im(s) ≠ 0` and the structural
height-log-squared witness.
-/
theorem
  routeK_full_chain_zeta_heightLogSq_sourced_exclusion_radius_of_im_ne_zero
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hIm : ∀ s : ℂ,
      0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 → s.im ≠ 0)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ζfun s ≠ 0 ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / routeK_logSqM2Envelope A C s ≤ δStar := by
  exact routeK_full_chain_zeta_heightLogSq_sourced_exclusion_radius_of_taylor_dominance
    _hA _hC hCont
    (routeK_OffAxisTaylorDominanceHeightLogSqSourcedGlobal_of_im_ne_zero hIm hTaylor)

/--
Full-chain quantitative endpoint on the zeta side together with an explicit
exclusion radius coming from a generic pointwise curvature envelope.
-/
theorem routeK_full_chain_zeta_norm_pos_envelope_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {M₂Envelope : ℂ → ℝ}
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceEnvelopeGlobal Dinf Binf M₂Envelope) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖ζfun s‖ ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / M₂Envelope s ≤ δStar := by
  exact routeK_full_chain_norm_pos_with_data_of_nonzero_with_data
    (routeK_full_chain_zeta_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun)
      (M₂Envelope := M₂Envelope) hCont hTaylor)

/--
Full-chain quantitative endpoint on the zeta side together with an explicit
parametric lower bound for the Taylor exclusion radius.
-/
theorem routeK_full_chain_zeta_norm_pos_parametric_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {A C L : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C) (_hL : 0 ≤ L)
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceParametricGlobal Dinf Binf A C L) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖ζfun s‖ ∧
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
    using routeK_full_chain_zeta_norm_pos_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun)
      (M₂Envelope := routeK_parametricCurvatureEnvelope A C L) hCont hTaylor

/--
Full-chain quantitative endpoint on the zeta side with the concrete
logarithmic bound `M₂ ≤ 2A + C (log γ)^2`.
-/
theorem routeK_full_chain_zeta_norm_pos_logSq_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {A C γ : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceParametricGlobal
      Dinf Binf A C ((Real.log γ) ^ 2)) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖ζfun s‖ ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / (2 * A + C * (Real.log γ) ^ 2) ≤ δStar := by
  exact routeK_full_chain_norm_pos_with_data_of_nonzero_with_data
    (routeK_full_chain_zeta_logSq_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) _hA _hC hCont hTaylor)

/--
Full-chain quantitative endpoint on the zeta side with the structural
logarithmic bound tied to the internal point height `|Im(s)|`.
-/
theorem routeK_full_chain_zeta_norm_pos_heightLogSq_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖ζfun s‖ ∧
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
    using routeK_full_chain_zeta_norm_pos_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun)
      (M₂Envelope := routeK_heightLogSqCurvatureEnvelope A C) hCont hTaylor

/--
Full-chain quantitative endpoint on the zeta side for the sourced structural
height-based theorem-11 witness.
-/
theorem routeK_full_chain_zeta_norm_pos_heightLogSq_sourced_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqSourcedGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖ζfun s‖ ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / routeK_logSqM2Envelope A C s ≤ δStar := by
  simpa [routeK_heightLogSqCurvatureEnvelope]
    using routeK_full_chain_zeta_norm_pos_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun)
      (M₂Envelope := routeK_heightLogSqCurvatureEnvelope A C) hCont
      (routeK_OffAxisTaylorDominanceEnvelopeGlobal_of_heightLogSqSourcedGlobal hTaylor)

/--
Derived quantitative sourced zeta endpoint from `Im(s) ≠ 0` and the
structural height-log-squared witness.
-/
theorem
  routeK_full_chain_zeta_norm_pos_heightLogSq_sourced_exclusion_radius_of_im_ne_zero
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hIm : ∀ s : ℂ,
      0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 → s.im ≠ 0)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖ζfun s‖ ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / routeK_logSqM2Envelope A C s ≤ δStar := by
  exact routeK_full_chain_zeta_norm_pos_heightLogSq_sourced_exclusion_radius_of_taylor_dominance
    _hA _hC hCont
    (routeK_OffAxisTaylorDominanceHeightLogSqSourcedGlobal_of_im_ne_zero hIm hTaylor)

/--
Full-chain quantitative endpoint on the `Z_spec` side together with an
explicit exclusion radius coming from a generic pointwise curvature envelope.
-/
theorem routeK_full_chain_Zspec_norm_pos_envelope_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {M₂Envelope : ℂ → ℝ}
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceEnvelopeGlobal Dinf Binf M₂Envelope) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖routeK_Zspec Dinf Binf s‖ ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / M₂Envelope s ≤ δStar := by
  exact routeK_full_chain_Zspec_norm_pos_with_data_of_zeta_nonzero_with_data
    (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) hCont
    (routeK_full_chain_zeta_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun)
      (M₂Envelope := M₂Envelope) hCont hTaylor)

/--
Full-chain endpoint on the `Z_spec` side with the structural logarithmic bound
tied to the internal point height `|Im(s)|`.
-/
theorem routeK_full_chain_Zspec_heightLogSq_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      routeK_Zspec Dinf Binf s ≠ 0 ∧
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
    using routeK_full_chain_Zspec_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun)
      (M₂Envelope := routeK_heightLogSqCurvatureEnvelope A C) hCont hTaylor

/--
Full-chain endpoint on the `Z_spec` side for the sourced structural
height-based theorem-11 witness.
-/
theorem routeK_full_chain_Zspec_heightLogSq_sourced_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqSourcedGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      routeK_Zspec Dinf Binf s ≠ 0 ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / routeK_logSqM2Envelope A C s ≤ δStar := by
  simpa [routeK_heightLogSqCurvatureEnvelope]
    using routeK_full_chain_Zspec_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun)
      (M₂Envelope := routeK_heightLogSqCurvatureEnvelope A C) hCont
      (routeK_OffAxisTaylorDominanceEnvelopeGlobal_of_heightLogSqSourcedGlobal hTaylor)

/--
Derived sourced `Z_spec` endpoint from `Im(s) ≠ 0` and the structural
height-log-squared witness.
-/
theorem
  routeK_full_chain_Zspec_heightLogSq_sourced_exclusion_radius_of_im_ne_zero
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hIm : ∀ s : ℂ,
      0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 → s.im ≠ 0)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      routeK_Zspec Dinf Binf s ≠ 0 ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / routeK_logSqM2Envelope A C s ≤ δStar := by
  exact routeK_full_chain_Zspec_heightLogSq_sourced_exclusion_radius_of_taylor_dominance
    _hA _hC hCont
    (routeK_OffAxisTaylorDominanceHeightLogSqSourcedGlobal_of_im_ne_zero hIm hTaylor)

/--
Full-chain quantitative endpoint on the `Z_spec` side with the structural
logarithmic bound tied to the internal point height `|Im(s)|`.
-/
theorem routeK_full_chain_Zspec_norm_pos_heightLogSq_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖routeK_Zspec Dinf Binf s‖ ∧
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
    using routeK_full_chain_Zspec_norm_pos_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun)
      (M₂Envelope := routeK_heightLogSqCurvatureEnvelope A C) hCont hTaylor

/--
Full-chain quantitative endpoint on the `Z_spec` side for the sourced
structural height-based theorem-11 witness.
-/
theorem routeK_full_chain_Zspec_norm_pos_heightLogSq_sourced_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqSourcedGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖routeK_Zspec Dinf Binf s‖ ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / routeK_logSqM2Envelope A C s ≤ δStar := by
  simpa [routeK_heightLogSqCurvatureEnvelope]
    using routeK_full_chain_Zspec_norm_pos_envelope_exclusion_radius_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun)
      (M₂Envelope := routeK_heightLogSqCurvatureEnvelope A C) hCont
      (routeK_OffAxisTaylorDominanceEnvelopeGlobal_of_heightLogSqSourcedGlobal hTaylor)

/--
Derived quantitative sourced `Z_spec` endpoint from `Im(s) ≠ 0` and the
structural height-log-squared witness.
-/
theorem
  routeK_full_chain_Zspec_norm_pos_heightLogSq_sourced_exclusion_radius_of_im_ne_zero
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ} {A C : ℝ}
    (_hA : 0 ≤ A) (_hC : 0 ≤ C)
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hIm : ∀ s : ℂ,
      0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 → s.im ≠ 0)
    (hTaylor : routeK_OffAxisTaylorDominanceHeightLogSqGlobal Dinf Binf A C) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖routeK_Zspec Dinf Binf s‖ ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / routeK_logSqM2Envelope A C s ≤ δStar := by
  exact routeK_full_chain_Zspec_norm_pos_heightLogSq_sourced_exclusion_radius_of_taylor_dominance
    _hA _hC hCont
    (routeK_OffAxisTaylorDominanceHeightLogSqSourcedGlobal_of_im_ne_zero hIm hTaylor)

/--
Full-chain quantitative endpoint on the numerator side specialized to the
explicit theorem-11 constants `A = 1.5862`, `C = 0.153`.
-/
theorem routeK_full_chain_numerator_norm_pos_explicit_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ}
    (hTaylor : routeK_OffAxisTaylorDominanceExplicitGlobal Dinf Binf) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖Dinf s - Binf s‖ ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 / routeK_logSqM2Envelope routeK_explicitTaylorA routeK_explicitTaylorC s ≤ δStar := by
  intro s hs hstrip hhalf
  have hAt : routeK_OffAxisTaylorDominanceExplicitAt Dinf Binf s :=
    hTaylor s hs hstrip hhalf
  have hBase : routeK_OffAxisTaylorDominanceAt Dinf Binf s :=
    routeK_OffAxisTaylorDominanceAt_of_ratioEnvelopeAt hAt
  refine ⟨routeK_numerator_norm_pos_of_taylor_dominance_at hBase, ?_⟩
  exact routeK_taylor_explicit_exclusion_radius_data_at hAt

/--
Full-chain quantitative endpoint on the zeta side specialized to the explicit
theorem-11 constants `A = 1.5862`, `C = 0.153`.
-/
theorem routeK_full_chain_zeta_norm_pos_explicit_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceExplicitGlobal Dinf Binf) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖ζfun s‖ ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 / routeK_logSqM2Envelope routeK_explicitTaylorA routeK_explicitTaylorC s ≤ δStar := by
  exact routeK_full_chain_norm_pos_with_data_of_nonzero_with_data
    (fun s hs hstrip hhalf => by
      have hAt : routeK_OffAxisTaylorDominanceExplicitAt Dinf Binf s :=
        hTaylor s hs hstrip hhalf
      have hBase : routeK_OffAxisTaylorDominanceAt Dinf Binf s :=
        routeK_OffAxisTaylorDominanceAt_of_ratioEnvelopeAt hAt
      exact ⟨routeK_zeta_nonzero_of_taylor_dominance_at hCont hs hBase,
        routeK_taylor_explicit_exclusion_radius_data_at hAt⟩)

/--
Full-chain quantitative endpoint on the `Z_spec` side specialized to the
explicit theorem-11 constants `A = 1.5862`, `C = 0.153`.
-/
theorem routeK_full_chain_Zspec_norm_pos_explicit_exclusion_radius_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceExplicitGlobal Dinf Binf) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖routeK_Zspec Dinf Binf s‖ ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 / routeK_logSqM2Envelope routeK_explicitTaylorA routeK_explicitTaylorC s ≤ δStar := by
  exact routeK_full_chain_Zspec_norm_pos_with_data_of_zeta_nonzero_with_data
    (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) hCont
    (fun s hs hstrip hhalf => by
      rcases routeK_full_chain_zeta_norm_pos_explicit_exclusion_radius_of_taylor_dominance
          (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) hCont hTaylor
          s hs hstrip hhalf with
        ⟨hζnorm, hRadius⟩
      exact ⟨norm_pos_iff.mp hζnorm, hRadius⟩)

/--
Full-chain endpoint on the `Z_spec` side from numerator Taylor domination and
the continuation equivalence.
-/
theorem routeK_full_chain_Zspec_endpoint_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceGlobal Dinf Binf) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      routeK_Zspec Dinf Binf s ≠ 0 := by
  intro s hs hstrip hhalf hZ0
  have hζ : ζfun s ≠ 0 :=
    routeK_offaxis_zeta_nonzero_of_taylor_dominance_global hCont hTaylor s hs hstrip hhalf
  exact hζ ((routeK_continuation_zero_iff
    (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) hCont hs).1 hZ0)

/--
Full-chain endpoint on the zeta side from numerator Taylor domination and the
continuation identity.
-/
theorem routeK_full_chain_zeta_endpoint_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceGlobal Dinf Binf) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ζfun s ≠ 0 := by
  exact routeK_offaxis_zeta_nonzero_global_of_numerator_nonzero hCont
    (routeK_full_chain_numerator_endpoint_of_taylor_dominance hTaylor)

/--
Full-chain quantitative endpoint on the `Z_spec` side from Taylor-dominance
data and the continuation identity.
-/
theorem routeK_full_chain_Zspec_norm_pos_of_taylor_dominance
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceGlobal Dinf Binf) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      0 < ‖routeK_Zspec Dinf Binf s‖ := by
  intro s hs hstrip hhalf
  exact
    (routeK_full_chain_Zspec_norm_pos_with_data_of_zeta_nonzero_with_data
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) hCont
      (fun z hz hstripz hhalfz =>
        ⟨routeK_offaxis_zeta_nonzero_of_taylor_dominance_global
          hCont hTaylor z hz hstripz hhalfz, True.intro⟩)
      s hs hstrip hhalf).1

/--
Full-chain endpoint on the zeta side from plain numerator nonvanishing and the
continuation identity.
-/
theorem routeK_full_chain_zeta_endpoint_of_numerator_nonzero
    {Dinf Binf : ℂ → ℂ} {ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re -> Dinf s - Binf s = c0Complex s * ζfun s)
    (hNum : ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      Dinf s - Binf s ≠ 0) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
      ζfun s ≠ 0 := by
  exact routeK_offaxis_zeta_nonzero_global_of_numerator_nonzero hCont hNum
end LeanC2
