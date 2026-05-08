import Mathlib
import LeanC2.Glue.Decomposition
import LeanC2.Cutoff.Residue

namespace LeanC2

/-- Analyticity of each cutoff approximant on the off-critical strip. -/
def cutoffAnalyticOnOffCriticalStrip (FX : Nat -> Complex -> Complex) : Prop :=
  ∀ X : Nat, AnalyticOnNhd ℂ (FX X) offCriticalStripSet

/--
Cutoff-layer package for off-strip analyticity of a cutoff family.

This keeps the analytic cutoff input anchored in the cutoff layer rather than in the Hurwitz
transfer layer.
-/
structure CutoffAnalyticData (FX : Nat -> Complex -> Complex) : Prop where
  hAnalytic : cutoffAnalyticOnOffCriticalStrip FX

theorem cutoffAnalyticOnOffCriticalStrip_of_pointwise
    {FX : Nat -> Complex -> Complex}
    (hAnalytic : ∀ X : Nat, AnalyticOnNhd ℂ (FX X) offCriticalStripSet) :
    cutoffAnalyticOnOffCriticalStrip FX := hAnalytic

theorem cutoffAnalyticOnOffCriticalStrip_of_data
    {FX : Nat -> Complex -> Complex}
    (hData : CutoffAnalyticData FX) :
    cutoffAnalyticOnOffCriticalStrip FX := hData.hAnalytic

theorem canonicalCutoffFamily_analyticData :
    CutoffAnalyticData canonicalCutoffFamily := by
  refine ⟨?_⟩
  exact canonicalCutoffFamily_analyticOnOffCriticalStrip

theorem canonicalSmoothCutoffFamily_analyticData :
    CutoffAnalyticData canonicalSmoothCutoffFamily := by
  refine ⟨?_⟩
  exact canonicalSmoothCutoffFamily_analyticOnOffCriticalStrip

/-! ### Thm 16: `‖R_X‖ = O(1 / X)` -/

/--
The cutoff scale satisfies `X ≤ cutoffScale X = X + 1`.

This bridges the Lean notion `cutoffScale X = X + 1` to the informal statement that the
decay rate is `O(1/X)`.
-/
lemma cutoffScale_ge_cast (X : Nat) : (X : Real) ≤ cutoffScale X := by
  unfold cutoffScale
  exact_mod_cast Nat.le_add_right X 1

/--
The canonical cutoff residual satisfies `‖R_X(s)‖ ≤ C(s, X) / X` for `X ≥ 1`.

This is the formal statement of Thm 16: `|R_X| = O(1/X)`.

`norm_canonicalCutoffResidual_le` gives `‖R_X‖ ≤ C / (X+1)`, and since `X+1 ≥ X`
we have `C / (X+1) ≤ C / X`.

`canonicalCutoffResidualCoeff s X` is the explicit finite sum (the Lean analogue of
`|D̃(s-1; M, K)|` from docs/c2_prova_taxa_decaimento_cutoff.md §2 Proposition 1).
-/
theorem norm_canonicalCutoffResidual_le_div_cast
    (X : Nat) (hX : 0 < X) (s : Complex) :
    ‖canonicalCutoffResidual X s‖ ≤ canonicalCutoffResidualCoeff s X / (X : Real) := by
  have hScale := norm_canonicalCutoffResidual_le X s
  have hCutoff : (X : Real) ≤ cutoffScale X := cutoffScale_ge_cast X
  have hCpos : 0 ≤ canonicalCutoffResidualCoeff s X := by
    unfold canonicalCutoffResidualCoeff cutoffResidualFiniteCoeff
    apply Finset.sum_nonneg; intro m _
    apply Finset.sum_nonneg; intro k _
    positivity
  have hXpos : (0 : Real) < (X : Real) := Nat.cast_pos.mpr hX
  calc ‖canonicalCutoffResidual X s‖
      ≤ canonicalCutoffResidualCoeff s X / cutoffScale X := hScale
    _ ≤ canonicalCutoffResidualCoeff s X / (X : Real) :=
        div_le_div_of_nonneg_left hCpos hXpos hCutoff

/--
Eventual form of Thm 16: for `Re(s) > 2`, `‖R_X(s)‖ → 0` as `X → ∞`.

Consequence of `O(1/X)` decay with `canonicalCutoffResidualCoeff` uniformly bounded
(by `canonicalCutoffResidualCoeff_bounded_of_two_lt_re`).
-/
theorem norm_canonicalCutoffResidual_tendsto_zero
    (s : Complex) (hs : 2 < s.re) :
    Filter.Tendsto (fun X : Nat => ‖canonicalCutoffResidual X s‖) Filter.atTop (nhds 0) := by
  obtain ⟨C, _hCnn, hCbd⟩ := canonicalCutoffResidualCoeff_bounded_of_two_lt_re hs
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  refine ⟨N + 1, fun X hX => ?_⟩
  simp only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hXN : (N : ℝ) + 1 ≤ (X : ℝ) := by exact_mod_cast hX
  have hCX : C < (X : ℝ) * ε := by
    nlinarith [mul_lt_mul_of_pos_right hN hε, div_mul_cancel₀ C hε.ne',
               mul_le_mul_of_nonneg_right hXN hε.le]
  calc ‖canonicalCutoffResidual X s‖
      ≤ C / (X : ℝ) :=
        (norm_canonicalCutoffResidual_le_div_cast X (by omega) s).trans
          (div_le_div_of_nonneg_right (hCbd X) hXpos.le)
    _ < ε := (div_lt_iff₀ hXpos).mpr (by linarith)

/-!
Thm 16: `|R_X| = O(1 / X)` for the canonical cutoff residual.

Primary sources:
- docs/c2_prova_taxa_decaimento_cutoff.md §1–§2 (Proposition 1, Taylor regime)
- docs/nota_cutoff_c2.md

The Taylor expansion in the note:
  R_X = −D̃(s−1)/X + O(1/X²)
is reflected here as `‖R_X‖ ≤ canonicalCutoffResidualCoeff s X / X`
where `canonicalCutoffResidualCoeff s X` plays the role of `|D̃(s−1)|`.

The Mellin-Barnes analysis (§3) and crossover scale X_cross (§4) are interpretive
material confirming the O(1/X) regime dominates for all practical X; they do not enter
the formal proof chain.
-/

end LeanC2
