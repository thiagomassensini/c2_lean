import Mathlib

namespace LeanC2

/-- Infinite dominant row mass: two branches per depth, starting at depth `2`. -/
noncomputable def dominantBranchMass (q : ℝ) : ℝ :=
  ∑' k : ℕ, (2 : ℝ) * q ^ (k + 2)

theorem dominantBranchMass_eq {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    dominantBranchMass q = 2 * q ^ 2 * (1 - q)⁻¹ := by
  unfold dominantBranchMass
  calc
    ∑' k : ℕ, (2 : ℝ) * q ^ (k + 2)
        = ∑' k : ℕ, (2 * q ^ 2) * q ^ k := by
            congr with k
            rw [pow_add]
            ring
    _ = (2 * q ^ 2) * ∑' k : ℕ, q ^ k := by
          rw [tsum_mul_left]
    _ = (2 * q ^ 2) * (1 - q)⁻¹ := by
          rw [tsum_geometric_of_lt_one hq0 hq1]
    _ = 2 * q ^ 2 * (1 - q)⁻¹ := by ring

theorem dominantBranchMass_half : dominantBranchMass ((1 : ℝ) / 2) = 1 := by
  rw [dominantBranchMass_eq]
  · norm_num
  · positivity
  · norm_num

theorem dominantBranchMass_lt_one_iff {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    dominantBranchMass q < 1 ↔ q < (1 : ℝ) / 2 := by
  rw [dominantBranchMass_eq hq0 hq1]
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hrewrite : 2 * q ^ 2 * (1 - q)⁻¹ = (2 * q ^ 2) / (1 - q) := by
    field_simp [hden.ne']
  rw [hrewrite, div_lt_iff₀ hden, one_mul]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem dominantBranchMass_eq_one_iff {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    dominantBranchMass q = 1 ↔ q = (1 : ℝ) / 2 := by
  rw [dominantBranchMass_eq hq0 hq1]
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hrewrite : 2 * q ^ 2 * (1 - q)⁻¹ = (2 * q ^ 2) / (1 - q) := by
    field_simp [hden.ne']
  rw [hrewrite]
  constructor
  · intro h
    have h' : 2 * q ^ 2 = 1 - q := by
      simpa using (div_eq_iff hden.ne').mp h
    nlinarith
  · intro hq
    apply (div_eq_iff hden.ne').2
    simpa using (show 2 * q ^ 2 = 1 - q by nlinarith [hq])

/-- The branch parameter induced by the real abscissa `σ`. -/
noncomputable def qOfSigma (σ : ℝ) : ℝ :=
  Real.exp (-(2 * σ) * Real.log 2)

lemma qOfSigma_nonneg (σ : ℝ) : 0 ≤ qOfSigma σ := by
  exact (Real.exp_pos _).le

lemma qOfSigma_lt_one_iff {σ : ℝ} : qOfSigma σ < 1 ↔ 0 < σ := by
  unfold qOfSigma
  rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero], Real.exp_lt_exp]
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith [hlog2]

lemma qOfSigma_lt_half_iff {σ : ℝ} : qOfSigma σ < (1 : ℝ) / 2 ↔ (1 : ℝ) / 2 < σ := by
  unfold qOfSigma
  have hhalf : (1 : ℝ) / 2 = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : 0 < (2 : ℝ))]
    norm_num
  rw [hhalf, Real.exp_lt_exp]
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith [hlog2]

lemma qOfSigma_gt_half_iff {σ : ℝ} : (1 : ℝ) / 2 < qOfSigma σ ↔ σ < (1 : ℝ) / 2 := by
  unfold qOfSigma
  have hhalf : (1 : ℝ) / 2 = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : 0 < (2 : ℝ))]
    norm_num
  rw [hhalf, Real.exp_lt_exp]
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith [hlog2]

theorem qOfSigma_half : qOfSigma ((1 : ℝ) / 2) = (1 : ℝ) / 2 := by
  unfold qOfSigma
  have h : -(2 * ((1 : ℝ) / 2)) * Real.log 2 = -Real.log 2 := by ring
  rw [h, Real.exp_neg, Real.exp_log (by norm_num : 0 < (2 : ℝ))]
  norm_num

theorem qOfSigma_eq_half_iff {σ : ℝ} : qOfSigma σ = (1 : ℝ) / 2 ↔ σ = (1 : ℝ) / 2 := by
  constructor
  · intro hq
    have hnotlt : ¬ qOfSigma σ < (1 : ℝ) / 2 := by
      simp [hq]
    have hnotgt : ¬ (1 : ℝ) / 2 < qOfSigma σ := by
      simp [hq]
    have hge : ¬ (1 : ℝ) / 2 < σ := by
      intro hlt
      exact hnotlt ((qOfSigma_lt_half_iff).2 hlt)
    have hle : ¬ σ < (1 : ℝ) / 2 := by
      intro hlt
      exact hnotgt ((qOfSigma_gt_half_iff).2 hlt)
    linarith
  · intro hσ
    rw [hσ, qOfSigma_half]


end LeanC2
