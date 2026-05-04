import Mathlib
import LeanC2.Operators.Branch

set_option linter.style.whitespace false

namespace LeanC2

theorem dominantBranchMass_lt_one_iff {q : Real} (hq0 : 0 <= q) (hq1 : q < 1) :
    dominantBranchMass q < 1 ↔ q < (1 : Real) / 2 := by
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

theorem dominantBranchMass_eq_one_iff {q : Real} (hq0 : 0 <= q) (hq1 : q < 1) :
    dominantBranchMass q = 1 ↔ q = (1 : Real) / 2 := by
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

theorem dominantBranchMass_sigma_half :
    dominantBranchMass (qOfSigma ((1 : Real) / 2)) = 1 := by
  rw [qOfSigma_half, dominantBranchMass_half]

theorem dominantBranchMass_sigma_lt_one_iff {sigma : Real} (hsigma : 0 < sigma) :
    dominantBranchMass (qOfSigma sigma) < 1 ↔ (1 : Real) / 2 < sigma := by
  have hq0 : 0 <= qOfSigma sigma := qOfSigma_nonneg sigma
  have hq1 : qOfSigma sigma < 1 := qOfSigma_lt_one_iff.2 hsigma
  rw [dominantBranchMass_lt_one_iff hq0 hq1, qOfSigma_lt_half_iff]

theorem branchNormSq_lt_one_iff {sigma : Real} (hsigma : 0 < sigma) :
    branchNormSq sigma < 1 ↔ (1 : Real) / 2 < sigma := by
  unfold branchNormSq
  exact dominantBranchMass_sigma_lt_one_iff hsigma

theorem branchNormSq_eq_one_iff {sigma : Real} (hsigma : 0 < sigma) :
    branchNormSq sigma = 1 ↔ sigma = (1 : Real) / 2 := by
  unfold branchNormSq
  have hq0 : 0 <= qOfSigma sigma := qOfSigma_nonneg sigma
  have hq1 : qOfSigma sigma < 1 := qOfSigma_lt_one_iff.2 hsigma
  rw [dominantBranchMass_eq_one_iff hq0 hq1, qOfSigma_eq_half_iff]

theorem branchNormSq_gt_one_iff {sigma : Real} (hsigma : 0 < sigma) :
    1 < branchNormSq sigma ↔ sigma < (1 : Real) / 2 := by
  constructor
  · intro hgt
    by_contra hnot
    have hhalf_le : (1 : Real) / 2 <= sigma := le_of_not_gt hnot
    by_cases hEq : sigma = (1 : Real) / 2
    · have hone : branchNormSq sigma = 1 := (branchNormSq_eq_one_iff hsigma).2 hEq
      linarith
    · have hhalf : (1 : Real) / 2 < sigma :=
        lt_of_le_of_ne hhalf_le (by simpa [eq_comm] using hEq)
      have hlt : branchNormSq sigma < 1 := (branchNormSq_lt_one_iff hsigma).2 hhalf
      linarith
  · intro hlt
    have hneq : branchNormSq sigma ≠ 1 := by
      intro hEq
      have : sigma = (1 : Real) / 2 := (branchNormSq_eq_one_iff hsigma).1 hEq
      linarith
    have hnotlt : ¬ branchNormSq sigma < 1 := by
      intro hltNorm
      have : (1 : Real) / 2 < sigma := (branchNormSq_lt_one_iff hsigma).1 hltNorm
      linarith
    exact lt_of_le_of_ne (le_of_not_gt hnotlt) (Ne.symm hneq)

/-- Barrier statement for the infinite branch operator. -/
theorem branchNormSq_barrier {sigma : Real} (hsigma : 0 < sigma) :
    branchNormSq sigma < 1 ↔ (1 : Real) / 2 < sigma :=
  branchNormSq_lt_one_iff hsigma

/-!
Norm-barrier consequences for the infinite branch operator.

Primary sources:
- docs/nota_offaxis_c2.md

Legacy seeds:
- Lean/Antigo_Lean_C2/Barrier.lean
- Lean/Antigo_Lean_C2/OperatorNorm.lean
-/

end LeanC2