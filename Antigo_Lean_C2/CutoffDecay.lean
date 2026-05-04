import Mathlib
import LeanC2.Transfer
import LeanC2.Composite

namespace LeanC2

/-!
# Cutoff Decay Interface

This module isolates the quantitative cutoff-residual layer: exact `O(X^{-1})`
control, vanishing at infinity, amplification, and the exclusion-zone package.
-/

/--
Exact absolute-value formula for the canonical cutoff residual.
-/
theorem routeK_cutoff_decay_abs {X C : ℝ} (hX : 0 < X) :
    |routeK_cutoffResidual X C| = |C| / X :=
  routeK_cutoffResidual_abs hX

/--
`O(X^{-1})` bound for the cutoff residual.
-/
theorem routeK_cutoff_decay_O_inv {X C K : ℝ}
    (hX : 0 < X) (hC : |C| ≤ K) :
    |routeK_cutoffResidual X C| ≤ K / X :=
  routeK_cutoffResidual_O_inv hX hC

/--
Decay of the cutoff residual as `X → ∞`.
-/
theorem routeK_cutoff_decay_vanishes_atTop (C : ℝ) :
    Filter.Tendsto (fun X : ℝ => routeK_cutoffResidual X C)
      Filter.atTop (nhds 0) :=
  routeK_thm3_cutoff_vanishes_atTop C

/--
Abstract transfer squeeze from an `O(X^{-1})` bound.
-/
theorem routeK_cutoff_decay_transfer_vanishes_of_cutoff_bound
    {K : ℝ} (hK : 0 ≤ K)
    {e : ℝ → ℝ} (he_nonneg : ∀ X, 0 ≤ e X)
    (he_bound : ∀ X : ℝ, 0 < X → e X ≤ K / X) :
    Filter.Tendsto e Filter.atTop (nhds 0) :=
  routeK_thm3_transfer_vanishes_of_cutoff_bound hK he_nonneg he_bound

/--
Norm factorization for the concrete finite residual witness.
-/
theorem routeK_cutoff_finiteResidual_norm (X C : ℝ) (θ : ℂ) :
    ‖routeK_finiteResidual X C θ‖ = |routeK_cutoffResidual X C| * ‖θ‖ :=
  routeK_finiteResidual_norm X C θ

/--
Unit-shape domination by the scalar cutoff residual.
-/
theorem routeK_cutoff_finiteResidual_norm_le_cutoff_of_unit
    (X C : ℝ) (θ : ℂ) (hθ : ‖θ‖ ≤ 1) :
    ‖routeK_finiteResidual X C θ‖ ≤ |routeK_cutoffResidual X C| :=
  routeK_finiteResidual_norm_le_cutoff_of_unit X C θ hθ

/--
Canonical residual domination by the scalar cutoff residual.
-/
theorem routeK_cutoff_finiteResidualCanonical_norm_le_cutoff
    (X C : ℝ) :
    ‖routeK_finiteResidualCanonical X C‖ ≤ |routeK_cutoffResidual X C| :=
  routeK_finiteResidualCanonical_norm_le_cutoff X C

/--
Amplification diverges when the numerator is positive.
-/
theorem routeK_cutoff_amplification_diverges
    {C : ℝ} (hC : 0 < C) {num : ℝ} (hnum : 0 < num) :
    Filter.Tendsto (fun X : ℝ => num / (C / X)) Filter.atTop Filter.atTop :=
  routeK_thm6_amplification_diverges hC hnum

/--
Amplification diverges in residual form.
-/
theorem routeK_cutoff_amplification_residual_diverges
    {C : ℝ} (hC : 0 < C) {num : ℝ} (hnum : 0 < num) :
    Filter.Tendsto
      (fun X : ℝ => num / |routeK_cutoffResidual X C|)
      Filter.atTop Filter.atTop :=
  routeK_thm6_amplification_residual_diverges hC hnum

/--
Existence of an off-axis exclusion scale where the residual is dominated by the
tilt signal.
-/
theorem routeK_cutoff_exclusion_zone_exists
    {n : ℕ} (hn : 0 < n) {c : ℝ} (hc : 1 < c) (C : ℝ) :
    ∃ X₀ : ℝ, ∀ X ≥ X₀, |routeK_cutoffResidual X C| < tiltBracket (n : ℝ) c :=
  routeK_thm11_exclusion_zone_exists hn hc C

/--
Combined transversal-plus-decay exclusion-zone package.
-/
theorem routeK_cutoff_transversal_and_exclusion_zone
    {n : ℕ} (hn : 0 < n) {c : ℝ} (hc : 1 < c) (C : ℝ)
    (cJet zJet : ℕ → ℂ)
    (hz : ∀ k < n, zJet k = 0) (hc0 : cJet 0 ≠ 0) (hzn : zJet n ≠ 0) :
    (Finset.sum (Finset.range (n + 1))
        (fun j => (Nat.choose n j : ℂ) * cJet j * zJet (n - j)) ≠ 0) ∧
    (∃ X₀ : ℝ, ∀ X ≥ X₀, |routeK_cutoffResidual X C| < tiltBracket (n : ℝ) c) :=
  routeK_thm11_transversal_and_exclusion_zone hn hc C cJet zJet hz hc0 hzn

end LeanC2
