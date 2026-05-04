import Mathlib
import LeanC2.Identity.FundamentalIdentity
import LeanC2.Operators.Cutoff

namespace LeanC2

open scoped BigOperators

/-- Residual correction carried by a single leg after subtracting the uncut term. -/
noncomputable def cutoffResidualLegTerm
    (X : Nat) (s : Complex) (k m : Nat) (epsilon : BranchSign) : Complex :=
  (((cutoffDefectWeight X (natDescendant k epsilon (oddCore m)) : Real) : Complex)) *
    legTerm s k m epsilon

/-- Residual two-leg packet at one depth and one odd core. -/
noncomputable def cutoffResidualPairTerm (X : Nat) (s : Complex) (k m : Nat) : Complex :=
  cutoffResidualLegTerm X s k m BranchSign.minus +
    cutoffResidualLegTerm X s k m BranchSign.plus

/-- Finite residual correction on one odd core. -/
noncomputable def cutoffResidualCore (X : Nat) (s : Complex) (K m : Nat) : Complex :=
  ∑ k ∈ depthWindow K, cutoffResidualPairTerm X s k m

/-- Finite smooth residual on the first `M` odd cores. -/
noncomputable def cutoffResidualFinite (X : Nat) (s : Complex) (K M : Nat) : Complex :=
  ∑ m ∈ Finset.range M, cutoffResidualCore X s K m

/-- Explicit finite coefficient controlling the smooth residual. -/
noncomputable def cutoffResidualFiniteCoeff (s : Complex) (K M : Nat) : Real :=
  ∑ m ∈ Finset.range M,
    ∑ k ∈ depthWindow K,
      ((natDescendant k BranchSign.minus (oddCore m) : Real) *
          ‖legTerm s k m BranchSign.minus‖ +
        (natDescendant k BranchSign.plus (oddCore m) : Real) *
          ‖legTerm s k m BranchSign.plus‖)

/-- Canonical smooth direct channel, now identified with `canonicalCutoffD`. -/
noncomputable abbrev canonicalSmoothCutoffD (X : Nat) (s : Complex) : Complex :=
  canonicalCutoffD X s

/-- Canonical smooth numerator, now identified with `canonicalCutoffFamily`. -/
noncomputable abbrev canonicalSmoothCutoffFamily (X : Nat) (s : Complex) : Complex :=
  canonicalCutoffFamily X s

/-- Canonical smooth residual, specialized to the windows used by `canonicalCutoffFamily`. -/
noncomputable def canonicalCutoffResidual (X : Nat) (s : Complex) : Complex :=
  cutoffResidualFinite X s (cutoffDepth X) (X + 1)

/-- Explicit coefficient controlling the canonical smooth residual. -/
noncomputable def canonicalCutoffResidualCoeff (s : Complex) (X : Nat) : Real :=
  cutoffResidualFiniteCoeff s (cutoffDepth X) (X + 1)

lemma cutoffWeight_nonneg (X n : Nat) : 0 <= cutoffWeight X n := by
  unfold cutoffWeight
  positivity

lemma cutoffWeight_le_one (X n : Nat) : cutoffWeight X n <= 1 := by
  unfold cutoffWeight cutoffScale
  have hExpLe :
      Real.exp (-((n : Real) / (X + 1 : Real))) <= Real.exp 0 := by
    refine Real.exp_le_exp.mpr ?_
    have hnonneg : 0 <= ((n : Real) / (X + 1 : Real)) := by positivity
    linarith
  simpa using hExpLe

lemma cutoffDefectWeight_nonpos (X n : Nat) : cutoffDefectWeight X n <= 0 := by
  unfold cutoffDefectWeight
  linarith [cutoffWeight_le_one X n]

lemma cutoffDefectWeight_abs_eq (X n : Nat) :
    |cutoffDefectWeight X n| = 1 - cutoffWeight X n := by
  rw [abs_of_nonpos (cutoffDefectWeight_nonpos X n)]
  unfold cutoffDefectWeight
  ring

lemma cutoffDefectWeight_abs_le (X n : Nat) :
    |cutoffDefectWeight X n| <= (n : Real) / cutoffScale X := by
  rw [cutoffDefectWeight_abs_eq, cutoffWeight]
  have hExp :
      1 - (n : Real) / cutoffScale X <=
        Real.exp (-((n : Real) / cutoffScale X)) := by
    simpa [sub_eq_add_neg] using
      (Real.one_sub_le_exp_neg ((n : Real) / cutoffScale X))
  linarith

lemma smoothCutoffLegTerm_eq_legTerm_add_residual
    (X : Nat) (s : Complex) (k m : Nat) (epsilon : BranchSign) :
    smoothCutoffLegTerm X s k m epsilon =
      legTerm s k m epsilon + cutoffResidualLegTerm X s k m epsilon := by
  have hCoeff :
      (((cutoffWeight X (natDescendant k epsilon (oddCore m)) : Real) : Complex)) =
        (1 : Complex) +
          (((cutoffDefectWeight X (natDescendant k epsilon (oddCore m)) : Real) : Complex)) := by
    simp [cutoffDefectWeight]
  calc
    smoothCutoffLegTerm X s k m epsilon =
        ((((1 : Complex) +
            (((cutoffDefectWeight X (natDescendant k epsilon (oddCore m)) : Real) : Complex))) *
          legTerm s k m epsilon)) := by
            unfold smoothCutoffLegTerm
            rw [hCoeff]
    _ = legTerm s k m epsilon + cutoffResidualLegTerm X s k m epsilon := by
          unfold cutoffResidualLegTerm
          rw [add_mul, one_mul]

lemma smoothCutoffPairTerm_eq_legPairTerm_add_residual
    (X : Nat) (s : Complex) (k m : Nat) :
    smoothCutoffLegTerm X s k m BranchSign.minus +
        smoothCutoffLegTerm X s k m BranchSign.plus =
      legPairTerm s k m + cutoffResidualPairTerm X s k m := by
  rw [smoothCutoffLegTerm_eq_legTerm_add_residual,
    smoothCutoffLegTerm_eq_legTerm_add_residual]
  simp [legPairTerm, cutoffResidualPairTerm, add_assoc, add_left_comm, add_comm]

lemma cutoffResidualLegTerm_analyticOnNhd
    (X : Nat) {k m : Nat} {epsilon : BranchSign} (hk : 2 <= k) :
    AnalyticOnNhd ℂ (fun s : Complex => cutoffResidualLegTerm X s k m epsilon)
      offCriticalStripSet := by
  simpa [cutoffResidualLegTerm] using
    (analyticOnNhd_const.mul (legTerm_analyticOnNhd (k := k) (m := m) (epsilon := epsilon) hk))

lemma cutoffResidualPairTerm_analyticOnNhd (X : Nat) {k m : Nat} (hk : 2 <= k) :
    AnalyticOnNhd ℂ (fun s : Complex => cutoffResidualPairTerm X s k m) offCriticalStripSet := by
  simpa [cutoffResidualPairTerm] using
    (cutoffResidualLegTerm_analyticOnNhd (X := X) (k := k) (m := m)
      (epsilon := BranchSign.minus) hk).add
      (cutoffResidualLegTerm_analyticOnNhd (X := X) (k := k) (m := m)
        (epsilon := BranchSign.plus) hk)

lemma cutoffResidualCore_analyticOnNhd (X K m : Nat) :
    AnalyticOnNhd ℂ (fun s : Complex => cutoffResidualCore X s K m) offCriticalStripSet := by
  unfold cutoffResidualCore
  exact (depthWindow K).analyticOnNhd_fun_sum fun k hk =>
    cutoffResidualPairTerm_analyticOnNhd (X := X) (k := k) (m := m) (Finset.mem_Icc.mp hk).1

lemma cutoffResidualFinite_analyticOnNhd (X K M : Nat) :
    AnalyticOnNhd ℂ (fun s : Complex => cutoffResidualFinite X s K M) offCriticalStripSet := by
  unfold cutoffResidualFinite
  exact (Finset.range M).analyticOnNhd_fun_sum fun m hm =>
    cutoffResidualCore_analyticOnNhd X K m

theorem smoothCutoffDCore_eq_partialDCore_add_cutoffResidualCore
    (X : Nat) (s : Complex) (K m : Nat) :
    smoothCutoffDCore X s K m = partialDCore s K m + cutoffResidualCore X s K m := by
  unfold smoothCutoffDCore partialDCore cutoffResidualCore
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simpa using smoothCutoffPairTerm_eq_legPairTerm_add_residual X s k m

theorem smoothCutoffDFinite_eq_sharpCutoffD_add_cutoffResidualFinite
    (X : Nat) (s : Complex) (K M : Nat) :
    smoothCutoffDFinite X s K M =
      (∑ m ∈ Finset.range M, partialDCore s K m) + cutoffResidualFinite X s K M := by
  unfold smoothCutoffDFinite cutoffResidualFinite
  calc
    ∑ m ∈ Finset.range M, smoothCutoffDCore X s K m
        = ∑ m ∈ Finset.range M, (partialDCore s K m + cutoffResidualCore X s K m) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            exact smoothCutoffDCore_eq_partialDCore_add_cutoffResidualCore X s K m
    _ = (∑ m ∈ Finset.range M, partialDCore s K m) +
          ∑ m ∈ Finset.range M, cutoffResidualCore X s K m := by
            rw [Finset.sum_add_distrib]
    _ = (∑ m ∈ Finset.range M, partialDCore s K m) + cutoffResidualFinite X s K M := by
          rfl

theorem canonicalCutoffD_eq_sharpCutoffD_add_residual
    (X : Nat) (s : Complex) :
    canonicalCutoffD X s = sharpCutoffD X s + canonicalCutoffResidual X s := by
  simpa [canonicalCutoffD, sharpCutoffD, canonicalCutoffResidual, cutoffCoreWindow] using
    smoothCutoffDFinite_eq_sharpCutoffD_add_cutoffResidualFinite X s (cutoffDepth X) (X + 1)

theorem canonicalCutoffFamily_eq_sharpCutoffFamily_add_residual
    (X : Nat) (s : Complex) :
    canonicalCutoffFamily X s = sharpCutoffFamily X s + canonicalCutoffResidual X s := by
  unfold canonicalCutoffFamily sharpCutoffFamily
  rw [canonicalCutoffD_eq_sharpCutoffD_add_residual]
  ring

theorem canonicalSmoothCutoffD_eq_canonicalCutoffD (X : Nat) (s : Complex) :
    canonicalSmoothCutoffD X s = canonicalCutoffD X s := rfl

theorem canonicalSmoothCutoffFamily_eq_canonicalCutoffFamily (X : Nat) (s : Complex) :
    canonicalSmoothCutoffFamily X s = canonicalCutoffFamily X s := rfl

theorem canonicalSmoothCutoffFamily_eq_sharpCutoffFamily_add_residual
    (X : Nat) (s : Complex) :
    canonicalSmoothCutoffFamily X s = sharpCutoffFamily X s + canonicalCutoffResidual X s := by
  simpa [canonicalSmoothCutoffFamily_eq_canonicalCutoffFamily X s] using
    canonicalCutoffFamily_eq_sharpCutoffFamily_add_residual X s

lemma canonicalCutoffResidual_analyticOnNhd (X : Nat) :
    AnalyticOnNhd ℂ (canonicalCutoffResidual X) offCriticalStripSet := by
  simpa [canonicalCutoffResidual] using
    cutoffResidualFinite_analyticOnNhd X (cutoffDepth X) (X + 1)

theorem canonicalSmoothCutoffFamily_analyticOnOffCriticalStrip :
    ∀ X : Nat, AnalyticOnNhd ℂ (canonicalSmoothCutoffFamily X) offCriticalStripSet := by
  intro X
  simpa [canonicalSmoothCutoffFamily] using canonicalCutoffFamily_analyticOnOffCriticalStrip X

lemma norm_cutoffResidualLegTerm_le
    (X : Nat) (s : Complex) (k m : Nat) (epsilon : BranchSign) :
    ‖cutoffResidualLegTerm X s k m epsilon‖ <=
      ((natDescendant k epsilon (oddCore m) : Real) / cutoffScale X) *
        ‖legTerm s k m epsilon‖ := by
  unfold cutoffResidualLegTerm
  rw [norm_mul]
  have hWeight :
      ‖(((cutoffDefectWeight X (natDescendant k epsilon (oddCore m)) : Real) : Complex))‖ =
        |cutoffDefectWeight X (natDescendant k epsilon (oddCore m))| := by
    simp
  rw [hWeight]
  exact mul_le_mul_of_nonneg_right
    (cutoffDefectWeight_abs_le X (natDescendant k epsilon (oddCore m)))
    (norm_nonneg _)

theorem norm_cutoffResidualFinite_le
    (X : Nat) (s : Complex) (K M : Nat) :
    ‖cutoffResidualFinite X s K M‖ <= cutoffResidualFiniteCoeff s K M / cutoffScale X := by
  unfold cutoffResidualFinite cutoffResidualFiniteCoeff
  calc
    ‖∑ m ∈ Finset.range M, cutoffResidualCore X s K m‖
        <= ∑ m ∈ Finset.range M, ‖cutoffResidualCore X s K m‖ := by
            exact norm_sum_le _ _
    _ <= ∑ m ∈ Finset.range M,
          ∑ k ∈ depthWindow K,
            (((natDescendant k BranchSign.minus (oddCore m) : Real) / cutoffScale X) *
                ‖legTerm s k m BranchSign.minus‖ +
              ((natDescendant k BranchSign.plus (oddCore m) : Real) / cutoffScale X) *
                ‖legTerm s k m BranchSign.plus‖) := by
          refine Finset.sum_le_sum ?_
          intro m hm
          unfold cutoffResidualCore cutoffResidualPairTerm
          calc
            ‖∑ k ∈ depthWindow K,
                  (cutoffResidualLegTerm X s k m BranchSign.minus +
                    cutoffResidualLegTerm X s k m BranchSign.plus)‖
                <= ∑ k ∈ depthWindow K,
                    ‖cutoffResidualLegTerm X s k m BranchSign.minus +
                      cutoffResidualLegTerm X s k m BranchSign.plus‖ := by
                      exact norm_sum_le _ _
            _ <= ∑ k ∈ depthWindow K,
                  (‖cutoffResidualLegTerm X s k m BranchSign.minus‖ +
                    ‖cutoffResidualLegTerm X s k m BranchSign.plus‖) := by
                      refine Finset.sum_le_sum ?_
                      intro k hk
                      exact norm_add_le _ _
            _ <= ∑ k ∈ depthWindow K,
                  (((natDescendant k BranchSign.minus (oddCore m) : Real) / cutoffScale X) *
                      ‖legTerm s k m BranchSign.minus‖ +
                    ((natDescendant k BranchSign.plus (oddCore m) : Real) / cutoffScale X) *
                      ‖legTerm s k m BranchSign.plus‖) := by
                      refine Finset.sum_le_sum ?_
                      intro k hk
                      exact add_le_add
                        (norm_cutoffResidualLegTerm_le X s k m BranchSign.minus)
                        (norm_cutoffResidualLegTerm_le X s k m BranchSign.plus)
    _ = cutoffResidualFiniteCoeff s K M / cutoffScale X := by
          unfold cutoffScale
          rw [div_eq_mul_inv]
          simp_rw [div_eq_mul_inv]
          calc
            ∑ m ∈ Finset.range M,
                ∑ k ∈ depthWindow K,
                  (↑(natDescendant k BranchSign.minus (oddCore m)) * (↑X + 1)⁻¹ *
                      ‖legTerm s k m BranchSign.minus‖ +
                    ↑(natDescendant k BranchSign.plus (oddCore m)) * (↑X + 1)⁻¹ *
                      ‖legTerm s k m BranchSign.plus‖)
                = ∑ m ∈ Finset.range M,
                    (∑ k ∈ depthWindow K,
                      ((↑(natDescendant k BranchSign.minus (oddCore m)) *
                            ‖legTerm s k m BranchSign.minus‖ +
                          ↑(natDescendant k BranchSign.plus (oddCore m)) *
                            ‖legTerm s k m BranchSign.plus‖) *
                        (↑X + 1)⁻¹)) := by
                          refine Finset.sum_congr rfl ?_
                          intro m hm
                          refine Finset.sum_congr rfl ?_
                          intro k hk
                          ring
            _ = ∑ m ∈ Finset.range M,
                  ((∑ k ∈ depthWindow K,
                      (↑(natDescendant k BranchSign.minus (oddCore m)) *
                          ‖legTerm s k m BranchSign.minus‖ +
                        ↑(natDescendant k BranchSign.plus (oddCore m)) *
                          ‖legTerm s k m BranchSign.plus‖)) *
                    (↑X + 1)⁻¹) := by
                      refine Finset.sum_congr rfl ?_
                      intro m hm
                      rw [Finset.sum_mul]
            _ = cutoffResidualFiniteCoeff s K M * (↑X + 1)⁻¹ := by
                  unfold cutoffResidualFiniteCoeff
                  rw [Finset.sum_mul]

theorem norm_canonicalCutoffResidual_le
    (X : Nat) (s : Complex) :
    ‖canonicalCutoffResidual X s‖ <= canonicalCutoffResidualCoeff s X / cutoffScale X := by
  simpa [canonicalCutoffResidual, canonicalCutoffResidualCoeff] using
    norm_cutoffResidualFinite_le X s (cutoffDepth X) (X + 1)

lemma cutoffResidualCoeffLeg_shift_le {s : Complex} (hs : 2 < s.re)
    (j m : Nat) (epsilon : BranchSign) :
    (natDescendant (j + 2) epsilon (oddCore m) : Real) *
        ‖legTerm s (j + 2) m epsilon‖ <=
      ‖dyadicComplexWeight (j + 2)‖ *
        ‖(((oddCore m : Nat) : Complex) ^ (-(s - 1)))‖ := by
  let n := natDescendant (j + 2) epsilon (oddCore m)
  have hs1 : 1 < s.re := lt_trans one_lt_two hs
  have hsShift : 1 < (s - 1).re := by
    have hShift : 1 < s.re - 1 := by linarith
    simpa [Complex.sub_re] using hShift
  have hk : 2 <= j + 2 := by omega
  have hn : 0 < n := by
    dsimp [n]
    exact natDescendant_oddCore_pos (j + 2) m epsilon hk
  have hNormNeg : ‖(((n : Nat) : Complex) ^ (-s))‖ = (n : Real) ^ (-s.re) := by
    dsimp [n]
    simpa using
      (Complex.norm_natCast_cpow_of_re_ne_zero n (s := -s)
        (Complex.re_neg_ne_zero_of_one_lt_re hs1))
  have hNormShift : ‖(((n : Nat) : Complex) ^ (-(s - 1)))‖ = (n : Real) ^ (1 - s.re) := by
    dsimp [n]
    simpa [Complex.sub_re, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (Complex.norm_natCast_cpow_of_re_ne_zero n (s := -(s - 1))
        (Complex.re_neg_ne_zero_of_one_lt_re hsShift))
  have hMulNorm : (n : Real) * ‖(((n : Nat) : Complex) ^ (-s))‖ =
      ‖(((n : Nat) : Complex) ^ (-(s - 1)))‖ := by
    rw [hNormNeg, hNormShift]
    calc
      (n : Real) * (n : Real) ^ (-s.re) = (n : Real) ^ (-s.re) * (n : Real) := by rw [mul_comm]
      _ = (n : Real) ^ (-s.re) * (n : Real) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (n : Real) ^ ((-s.re) + 1) := by rw [← Real.rpow_add (by exact_mod_cast hn)]
      _ = (n : Real) ^ (1 - s.re) := by congr 1; ring
  have hAntitone :
      ‖(((n : Nat) : Complex) ^ (-(s - 1)))‖ <=
        ‖(((oddCore m : Nat) : Complex) ^ (-(s - 1)))‖ := by
    dsimp [n]
    exact norm_natCast_cpow_neg_antitone hsShift
      (oddCore_pos m) (oddCore_le_natDescendant_shift j m epsilon)
  unfold legTerm
  rw [norm_mul]
  calc
    (n : Real) * (‖dyadicComplexWeight (j + 2)‖ * ‖(((n : Nat) : Complex) ^ (-s))‖)
        = ‖dyadicComplexWeight (j + 2)‖ *
            ((n : Real) * ‖(((n : Nat) : Complex) ^ (-s))‖) := by ring
    _ = ‖dyadicComplexWeight (j + 2)‖ * ‖(((n : Nat) : Complex) ^ (-(s - 1)))‖ := by
          rw [hMulNorm]
    _ <= ‖dyadicComplexWeight (j + 2)‖ * ‖(((oddCore m : Nat) : Complex) ^ (-(s - 1)))‖ := by
          exact mul_le_mul_of_nonneg_left hAntitone (norm_nonneg _)

lemma cutoffResidualCoeffPair_shift_le {s : Complex} (hs : 2 < s.re) (j m : Nat) :
    (natDescendant (j + 2) BranchSign.minus (oddCore m) : Real) *
        ‖legTerm s (j + 2) m BranchSign.minus‖ +
      (natDescendant (j + 2) BranchSign.plus (oddCore m) : Real) *
        ‖legTerm s (j + 2) m BranchSign.plus‖ <=
      ‖(2 : Complex) * dyadicComplexWeight (j + 2)‖ *
        ‖(((oddCore m : Nat) : Complex) ^ (-(s - 1)))‖ := by
  have hminus := cutoffResidualCoeffLeg_shift_le hs j m BranchSign.minus
  have hplus := cutoffResidualCoeffLeg_shift_le hs j m BranchSign.plus
  calc
    (natDescendant (j + 2) BranchSign.minus (oddCore m) : Real) *
          ‖legTerm s (j + 2) m BranchSign.minus‖ +
        (natDescendant (j + 2) BranchSign.plus (oddCore m) : Real) *
          ‖legTerm s (j + 2) m BranchSign.plus‖
      <= ‖dyadicComplexWeight (j + 2)‖ * ‖(((oddCore m : Nat) : Complex) ^ (-(s - 1)))‖ +
          ‖dyadicComplexWeight (j + 2)‖ * ‖(((oddCore m : Nat) : Complex) ^ (-(s - 1)))‖ :=
            add_le_add hminus hplus
    _ = ‖(2 : Complex) * dyadicComplexWeight (j + 2)‖ *
          ‖(((oddCore m : Nat) : Complex) ^ (-(s - 1)))‖ := by
          rw [norm_mul, Complex.norm_two]
          ring

lemma canonicalCutoffResidualCoeff_le_majorant_of_two_lt_re {s : Complex}
    (hs : 2 < s.re) (X : Nat) :
    canonicalCutoffResidualCoeff s X <=
      ∑ m ∈ Finset.range (X + 1),
        ∑ j ∈ Finset.range (X + 1),
          ‖(2 : Complex) * dyadicComplexWeight (j + 2)‖ *
            ‖(((oddCore m : Nat) : Complex) ^ (-(s - 1)))‖ := by
  unfold canonicalCutoffResidualCoeff cutoffResidualFiniteCoeff cutoffDepth
  refine Finset.sum_le_sum ?_
  intro m hm
  rw [depthWindow_eq_Ico_succ, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_le_sum ?_
  intro j hj
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    cutoffResidualCoeffPair_shift_le hs j m

theorem canonicalCutoffResidualCoeff_bounded_of_two_lt_re {s : Complex}
    (hs : 2 < s.re) :
    ∃ C : Real, 0 <= C ∧ ∀ X : Nat, canonicalCutoffResidualCoeff s X <= C := by
  let coeff2 : Nat -> Real := fun j => ‖(2 : Complex) * dyadicComplexWeight (j + 2)‖
  let oddNorm : Nat -> Real := fun m => ‖(((oddCore m : Nat) : Complex) ^ (-(s - 1)))‖
  have hsShift : 1 < (s - 1).re := by
    have hShift : 1 < s.re - 1 := by linarith
    simpa [Complex.sub_re] using hShift
  have hcoeff2 : Summable coeff2 := by
    simpa [coeff2] using summable_norm_const_dyadicWeight_shift (2 : Complex)
  have hodd : Summable oddNorm := by
    simpa [oddNorm] using summable_norm_oddCore_cpow_neg (s := s - 1) hsShift
  refine ⟨(∑' j : Nat, coeff2 j) * ∑' m : Nat, oddNorm m, by positivity, ?_⟩
  intro X
  refine (canonicalCutoffResidualCoeff_le_majorant_of_two_lt_re hs X).trans ?_
  calc
    ∑ m ∈ Finset.range (X + 1), ∑ j ∈ Finset.range (X + 1), coeff2 j * oddNorm m
        <= ∑ m ∈ Finset.range (X + 1), ((∑' j : Nat, coeff2 j) * oddNorm m) := by
            refine Finset.sum_le_sum ?_
            intro m hm
            refine (Summable.sum_le_tsum (Finset.range (X + 1)) (fun j hj => by positivity)
              (hcoeff2.mul_right (oddNorm m))).trans_eq ?_
            simpa [coeff2] using hcoeff2.tsum_mul_right (oddNorm m)
    _ <= (∑' j : Nat, coeff2 j) * ∑' m : Nat, oddNorm m := by
          refine (Summable.sum_le_tsum (Finset.range (X + 1)) (fun m hm => by positivity)
            (hodd.mul_left (∑' j : Nat, coeff2 j))).trans_eq ?_
          simpa [oddNorm, mul_assoc, mul_left_comm, mul_comm] using
            hodd.tsum_mul_left (∑' j : Nat, coeff2 j)

theorem norm_canonicalCutoffResidual_le_const_div_of_two_lt_re {s : Complex}
    (hs : 2 < s.re) :
    ∃ C : Real, 0 <= C ∧ ∀ X : Nat, ‖canonicalCutoffResidual X s‖ <= C / cutoffScale X := by
  rcases canonicalCutoffResidualCoeff_bounded_of_two_lt_re hs with ⟨C, hCnonneg, hC⟩
  refine ⟨C, hCnonneg, ?_⟩
  intro X
  exact le_trans (norm_canonicalCutoffResidual_le X s)
    (div_le_div_of_nonneg_right (hC X) (le_of_lt (cutoffScale_pos X)))

/-!
Scaffold for the residue term `R_X = D_X - D_infty`.

Primary sources:
- docs/c2_prova_taxa_decaimento_cutoff.md
- docs/nota_cutoff_c2.md

Legacy seeds:
- Lean/Antigo_Lean_C2/CutoffDecay.lean

This file now sits above `Operators/Cutoff.lean`: the canonical family is already the smooth one,
while the residual layer compares it explicitly against the old sharp scaffold `sharpCutoffFamily`.
-/

end LeanC2
