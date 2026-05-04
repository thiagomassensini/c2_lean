import Mathlib
import LeanC2.Foundations.Basic
import LeanC2.Foundations.DyadicArith

set_option linter.style.whitespace false

namespace LeanC2

/-- Infinite dominant row mass: two branches per depth, starting at depth `2`. -/
noncomputable def dominantBranchMass (q : Real) : Real :=
  ∑' k : Nat, (2 : Real) * q ^ (k + 2)

theorem dominantBranchMass_eq {q : Real} (hq0 : 0 <= q) (hq1 : q < 1) :
    dominantBranchMass q = 2 * q ^ 2 * (1 - q)⁻¹ := by
  unfold dominantBranchMass
  calc
    ∑' k : Nat, (2 : Real) * q ^ (k + 2)
        = ∑' k : Nat, (2 * q ^ 2) * q ^ k := by
            congr with k
            rw [pow_add]
            ring
    _ = (2 * q ^ 2) * ∑' k : Nat, q ^ k := by
          rw [tsum_mul_left]
    _ = (2 * q ^ 2) * (1 - q)⁻¹ := by
          rw [tsum_geometric_of_lt_one hq0 hq1]
    _ = 2 * q ^ 2 * (1 - q)⁻¹ := by ring

theorem dominantBranchMass_half : dominantBranchMass ((1 : Real) / 2) = 1 := by
  rw [dominantBranchMass_eq]
  · norm_num
  · positivity
  · norm_num

/-- The branch parameter induced by the real abscissa `σ`. -/
noncomputable def qOfSigma (sigma : Real) : Real :=
  Real.exp (-(2 * sigma) * Real.log 2)

lemma qOfSigma_nonneg (sigma : Real) : 0 <= qOfSigma sigma := by
  exact (Real.exp_pos _).le

lemma qOfSigma_lt_one_iff {sigma : Real} : qOfSigma sigma < 1 ↔ 0 < sigma := by
  unfold qOfSigma
  rw [show (1 : Real) = Real.exp 0 by rw [Real.exp_zero], Real.exp_lt_exp]
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith [hlog2]

lemma qOfSigma_lt_half_iff {sigma : Real} :
    qOfSigma sigma < (1 : Real) / 2 ↔ (1 : Real) / 2 < sigma := by
  unfold qOfSigma
  have hhalf : (1 : Real) / 2 = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : 0 < (2 : Real))]
    norm_num
  rw [hhalf, Real.exp_lt_exp]
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith [hlog2]

lemma qOfSigma_gt_half_iff {sigma : Real} :
    (1 : Real) / 2 < qOfSigma sigma ↔ sigma < (1 : Real) / 2 := by
  unfold qOfSigma
  have hhalf : (1 : Real) / 2 = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : 0 < (2 : Real))]
    norm_num
  rw [hhalf, Real.exp_lt_exp]
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith [hlog2]

theorem qOfSigma_half : qOfSigma ((1 : Real) / 2) = (1 : Real) / 2 := by
  unfold qOfSigma
  have h : -(2 * ((1 : Real) / 2)) * Real.log 2 = -Real.log 2 := by ring
  rw [h, Real.exp_neg, Real.exp_log (by norm_num : 0 < (2 : Real))]
  norm_num

theorem qOfSigma_eq_half_iff {sigma : Real} :
    qOfSigma sigma = (1 : Real) / 2 ↔ sigma = (1 : Real) / 2 := by
  constructor
  · intro hq
    have hnotlt : ¬ qOfSigma sigma < (1 : Real) / 2 := by
      simp [hq]
    have hnotgt : ¬ (1 : Real) / 2 < qOfSigma sigma := by
      simp [hq]
    have hge : ¬ (1 : Real) / 2 < sigma := by
      intro hlt
      exact hnotlt ((qOfSigma_lt_half_iff).2 hlt)
    have hle : ¬ sigma < (1 : Real) / 2 := by
      intro hlt
      exact hnotgt ((qOfSigma_gt_half_iff).2 hlt)
    linarith
  · intro hsigma
    rw [hsigma, qOfSigma_half]

/-- Depth weight induced by the abscissa `σ`. -/
noncomputable def branchWeight (sigma : Real) (k : Nat) : Real :=
  (qOfSigma sigma) ^ k

/-- Sigma-t wrapper: by construction, branch weights only see `σ`. -/
noncomputable def branchWeightSigmaT (sigma _t : Real) (k : Nat) : Real :=
  branchWeight sigma k

theorem branchWeightSigmaT_indep_t (sigma t t' : Real) (k : Nat) :
    branchWeightSigmaT sigma t k = branchWeightSigmaT sigma t' k := by
  rfl

/-- Rota K ELO2: branch weight depends only on `σ`, not on `t`. -/
theorem routeK_elo2_weight_sigma_only (sigma t t' : Real) (k : Nat) :
    branchWeightSigmaT sigma t k = branchWeightSigmaT sigma t' k := by
  exact branchWeightSigmaT_indep_t sigma t t' k

/-- Finite-cutoff approximation of the squared branch-operator norm. -/
noncomputable def branchNormSqFinite (M : Nat) (sigma : Real) (m : Nat) : Real :=
  rowMass M (branchWeight sigma) m

theorem branchNormSqFinite_le_at_one {M m : Nat} {sigma : Real} (hm : Odd m) :
    branchNormSqFinite M sigma m <= branchNormSqFinite M sigma 1 := by
  unfold branchNormSqFinite branchWeight
  exact rowMass_le_rowMass_one hm (fun k ↦ pow_nonneg (qOfSigma_nonneg sigma) k)

theorem branchNormSqFinite_nonneg {M m : Nat} {sigma : Real} :
    0 <= branchNormSqFinite M sigma m := by
  classical
  unfold branchNormSqFinite rowMass branchWeight
  exact Finset.sum_nonneg fun p _ ↦ pow_nonneg (qOfSigma_nonneg sigma) p.1

/-- The dominant finite row, i.e. the cutoff version of the operator norm square. -/
noncomputable def branchNormSqFiniteTop (M : Nat) (sigma : Real) : Real :=
  branchNormSqFinite M sigma 1

theorem branchNormSqFinite_le_top {M m : Nat} {sigma : Real} (hm : Odd m) :
    branchNormSqFinite M sigma m <= branchNormSqFiniteTop M sigma := by
  unfold branchNormSqFiniteTop
  exact branchNormSqFinite_le_at_one hm

/-- Squared magnitude of a single branch coefficient, indexed by depth/sign. -/
noncomputable def branchEntryAbsSq
    (M : Nat) (sigma : Real) (m : Nat) (p : Nat × BranchSign) : Real :=
  if p ∈ rowSupport M m then branchWeight sigma p.1 else 0

/-- Row norm square written as a sum over the ambient address space `(k, ε)`. -/
noncomputable def branchRowNormSqByEntry (M : Nat) (sigma : Real) (m : Nat) : Real :=
  Finset.sum ((Finset.range (M + 1)).product Finset.univ) fun p =>
    branchEntryAbsSq M sigma m p

theorem branchRowNormSqByEntry_eq {M m : Nat} {sigma : Real} :
    branchRowNormSqByEntry M sigma m = branchNormSqFinite M sigma m := by
  classical
  unfold branchRowNormSqByEntry branchEntryAbsSq branchNormSqFinite rowMass rowSupport
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hpRange : p.1 < M + 1 := by
    exact Finset.mem_range.mp ((Finset.mem_product.mp hp).1)
  have hpLe : p.1 <= M := Nat.lt_succ_iff.mp hpRange
  by_cases hmem : 2 <= p.1 ∧ natDescendant p.1 p.2 m <= M
  · simp [hmem, hpLe]
  · simp [hmem]

theorem branchRowNormSqByEntry_le_top {M m : Nat} {sigma : Real} (hm : Odd m) :
    branchRowNormSqByEntry M sigma m <= branchNormSqFiniteTop M sigma := by
  rw [branchRowNormSqByEntry_eq]
  exact branchNormSqFinite_le_top hm

/-- The finite dominant row rewritten in entrywise form. -/
noncomputable def branchOperatorNormSqFinite (M : Nat) (sigma : Real) : Real :=
  branchRowNormSqByEntry M sigma 1

theorem branchOperatorNormSqFinite_eq {M : Nat} {sigma : Real} :
    branchOperatorNormSqFinite M sigma = branchNormSqFiniteTop M sigma := by
  unfold branchOperatorNormSqFinite branchNormSqFiniteTop
  exact branchRowNormSqByEntry_eq

/-- Canonical infinite squared branch-operator norm at abscissa `σ`. -/
noncomputable def branchNormSq (sigma : Real) : Real :=
  dominantBranchMass (qOfSigma sigma)

/-- Sigma-t wrapper: ELO2 statement in two-variable form. -/
noncomputable def branchNormSqSigmaT (sigma _t : Real) : Real :=
  branchNormSq sigma

theorem branchNormSqSigmaT_indep_t (sigma t t' : Real) :
    branchNormSqSigmaT sigma t = branchNormSqSigmaT sigma t' := by
  rfl

/-- Rota K ELO2: branch norm square depends only on `σ`, not on `t`. -/
theorem routeK_elo2_norm_sigma_only (sigma t t' : Real) :
    branchNormSqSigmaT sigma t = branchNormSqSigmaT sigma t' := by
  exact branchNormSqSigmaT_indep_t sigma t t'

theorem branchNormSq_eq {sigma : Real} (hsigma : 0 < sigma) :
    branchNormSq sigma = 2 * (qOfSigma sigma) ^ 2 * (1 - qOfSigma sigma)⁻¹ := by
  unfold branchNormSq
  exact dominantBranchMass_eq (qOfSigma_nonneg sigma) (qOfSigma_lt_one_iff.2 hsigma)

theorem branchNormSq_half : branchNormSq ((1 : Real) / 2) = 1 := by
  unfold branchNormSq
  rw [qOfSigma_half, dominantBranchMass_half]

/-!
Core branch-operator layer.

Primary sources:
- docs/nota_offaxis_c2.md
- docs/c2_operador_ramo_invariancia_t_ponte_genuine.md

Legacy seeds:
- Lean/Antigo_Lean_C2/Barrier.lean
- Lean/Antigo_Lean_C2/OperatorNorm.lean
- Lean/Antigo_Lean_C2/Tree.lean
-/

end LeanC2