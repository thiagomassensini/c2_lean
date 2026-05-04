import Mathlib
import LeanC2.Barrier
import LeanC2.Tree

namespace LeanC2

theorem dominantBranchMass_sigma_half : dominantBranchMass (qOfSigma ((1 : ℝ) / 2)) = 1 := by
  rw [qOfSigma_half, dominantBranchMass_half]

theorem dominantBranchMass_sigma_lt_one_iff {σ : ℝ} (hσ : 0 < σ) :
    dominantBranchMass (qOfSigma σ) < 1 ↔ (1 : ℝ) / 2 < σ := by
  have hq0 : 0 ≤ qOfSigma σ := qOfSigma_nonneg σ
  have hq1 : qOfSigma σ < 1 := qOfSigma_lt_one_iff.2 hσ
  rw [dominantBranchMass_lt_one_iff hq0 hq1, qOfSigma_lt_half_iff]

/-- Depth weight induced by the abscissa `σ`. -/
noncomputable def branchWeight (σ : ℝ) (k : ℕ) : ℝ :=
  (qOfSigma σ) ^ k

/-- Sigma-t wrapper: by construction, branch weights only see `σ`. -/
noncomputable def branchWeightSigmaT (σ _t : ℝ) (k : ℕ) : ℝ :=
  branchWeight σ k

theorem branchWeightSigmaT_indep_t (σ t t' : ℝ) (k : ℕ) :
    branchWeightSigmaT σ t k = branchWeightSigmaT σ t' k := by
  rfl

/-- Rota K ELO2: branch weight depends only on `σ`, not on `t`. -/
theorem routeK_elo2_weight_sigma_only (σ t t' : ℝ) (k : ℕ) :
    branchWeightSigmaT σ t k = branchWeightSigmaT σ t' k := by
  exact branchWeightSigmaT_indep_t σ t t' k

/-- Finite-cutoff approximation of the squared branch-operator norm. -/
noncomputable def branchNormSqFinite (M : ℕ) (σ : ℝ) (m : ℕ) : ℝ :=
  rowMass M (branchWeight σ) m

theorem branchNormSqFinite_le_at_one {M m : ℕ} {σ : ℝ} (hm : Odd m) :
    branchNormSqFinite M σ m ≤ branchNormSqFinite M σ 1 := by
  unfold branchNormSqFinite branchWeight
  exact rowMass_le_rowMass_one hm (fun k ↦ pow_nonneg (qOfSigma_nonneg σ) k)

theorem branchNormSqFinite_nonneg {M m : ℕ} {σ : ℝ} :
    0 ≤ branchNormSqFinite M σ m := by
  classical
  unfold branchNormSqFinite rowMass branchWeight
  exact Finset.sum_nonneg fun p _ ↦ pow_nonneg (qOfSigma_nonneg σ) p.1

/-- The dominant finite row, i.e. the cutoff version of the operator norm square. -/
noncomputable def branchNormSqFiniteTop (M : ℕ) (σ : ℝ) : ℝ :=
  branchNormSqFinite M σ 1

theorem branchNormSqFinite_le_top {M m : ℕ} {σ : ℝ} (hm : Odd m) :
    branchNormSqFinite M σ m ≤ branchNormSqFiniteTop M σ := by
  unfold branchNormSqFiniteTop
  exact branchNormSqFinite_le_at_one hm

/-- Squared magnitude of a single branch coefficient, indexed by depth/sign. -/
noncomputable def branchEntryAbsSq (M : ℕ) (σ : ℝ) (m : ℕ) (p : ℕ × BranchSign) : ℝ :=
  if p ∈ rowSupport M m then branchWeight σ p.1 else 0

/-- Row norm square written as a sum over the ambient address space `(k, ε)`. -/
noncomputable def branchRowNormSqByEntry (M : ℕ) (σ : ℝ) (m : ℕ) : ℝ :=
  Finset.sum ((Finset.range (M + 1)).product Finset.univ) (fun p => branchEntryAbsSq M σ m p)

theorem branchRowNormSqByEntry_eq {M m : ℕ} {σ : ℝ} :
    branchRowNormSqByEntry M σ m = branchNormSqFinite M σ m := by
  classical
  unfold branchRowNormSqByEntry branchEntryAbsSq branchNormSqFinite rowMass rowSupport
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hpRange : p.1 < M + 1 := by
    exact Finset.mem_range.mp ((Finset.mem_product.mp hp).1)
  have hpLe : p.1 ≤ M := Nat.lt_succ_iff.mp hpRange
  by_cases hmem : 2 ≤ p.1 ∧ natDescendant p.1 p.2 m ≤ M
  · simp [hmem, hpLe]
  · simp [hmem]

theorem branchRowNormSqByEntry_le_top {M m : ℕ} {σ : ℝ} (hm : Odd m) :
    branchRowNormSqByEntry M σ m ≤ branchNormSqFiniteTop M σ := by
  rw [branchRowNormSqByEntry_eq]
  exact branchNormSqFinite_le_top hm

/-- The finite dominant row rewritten in entrywise form. -/
noncomputable def branchOperatorNormSqFinite (M : ℕ) (σ : ℝ) : ℝ :=
  branchRowNormSqByEntry M σ 1

theorem branchOperatorNormSqFinite_eq {M : ℕ} {σ : ℝ} :
    branchOperatorNormSqFinite M σ = branchNormSqFiniteTop M σ := by
  unfold branchOperatorNormSqFinite branchNormSqFiniteTop
  exact branchRowNormSqByEntry_eq

/-- Canonical infinite squared branch-operator norm at abscissa `σ`. -/
noncomputable def branchNormSq (σ : ℝ) : ℝ :=
  dominantBranchMass (qOfSigma σ)

/-- Sigma-t wrapper: ELO2 statement in two-variable form. -/
noncomputable def branchNormSqSigmaT (σ _t : ℝ) : ℝ :=
  branchNormSq σ

theorem branchNormSqSigmaT_indep_t (σ t t' : ℝ) :
    branchNormSqSigmaT σ t = branchNormSqSigmaT σ t' := by
  rfl

/-- Rota K ELO2: branch norm square depends only on `σ`, not on `t`. -/
theorem routeK_elo2_norm_sigma_only (σ t t' : ℝ) :
    branchNormSqSigmaT σ t = branchNormSqSigmaT σ t' := by
  exact branchNormSqSigmaT_indep_t σ t t'

theorem branchNormSq_eq {σ : ℝ} (hσ : 0 < σ) :
    branchNormSq σ = 2 * (qOfSigma σ) ^ 2 * (1 - qOfSigma σ)⁻¹ := by
  unfold branchNormSq
  exact dominantBranchMass_eq (qOfSigma_nonneg σ) (qOfSigma_lt_one_iff.2 hσ)

theorem branchNormSq_half : branchNormSq ((1 : ℝ) / 2) = 1 := by
  unfold branchNormSq
  exact dominantBranchMass_sigma_half

theorem branchNormSq_lt_one_iff {σ : ℝ} (hσ : 0 < σ) :
    branchNormSq σ < 1 ↔ (1 : ℝ) / 2 < σ := by
  unfold branchNormSq
  exact dominantBranchMass_sigma_lt_one_iff hσ

theorem branchNormSq_eq_one_iff {σ : ℝ} (hσ : 0 < σ) :
    branchNormSq σ = 1 ↔ σ = (1 : ℝ) / 2 := by
  unfold branchNormSq
  have hq0 : 0 ≤ qOfSigma σ := qOfSigma_nonneg σ
  have hq1 : qOfSigma σ < 1 := qOfSigma_lt_one_iff.2 hσ
  rw [dominantBranchMass_eq_one_iff hq0 hq1, qOfSigma_eq_half_iff]

theorem branchNormSq_gt_one_iff {σ : ℝ} (hσ : 0 < σ) :
    1 < branchNormSq σ ↔ σ < (1 : ℝ) / 2 := by
  constructor
  · intro hgt
    by_contra hnot
    have hhalf_le : (1 : ℝ) / 2 ≤ σ := le_of_not_gt hnot
    by_cases hEq : σ = (1 : ℝ) / 2
    · have hone : branchNormSq σ = 1 := (branchNormSq_eq_one_iff hσ).2 hEq
      linarith
    · have hhalf : (1 : ℝ) / 2 < σ := lt_of_le_of_ne hhalf_le (by simpa [eq_comm] using hEq)
      have hlt : branchNormSq σ < 1 := (branchNormSq_lt_one_iff hσ).2 hhalf
      linarith
  · intro hlt
    have hneq : branchNormSq σ ≠ 1 := by
      intro hEq
      have : σ = (1 : ℝ) / 2 := (branchNormSq_eq_one_iff hσ).1 hEq
      linarith
    have hnotlt : ¬ branchNormSq σ < 1 := by
      intro hltNorm
      have : (1 : ℝ) / 2 < σ := (branchNormSq_lt_one_iff hσ).1 hltNorm
      linarith
    exact lt_of_le_of_ne (le_of_not_gt hnotlt) (Ne.symm hneq)

theorem branchNormSq_barrier {σ : ℝ} (hσ : 0 < σ) :
    branchNormSq σ < 1 ↔ (1 : ℝ) / 2 < σ := branchNormSq_lt_one_iff hσ


end LeanC2
