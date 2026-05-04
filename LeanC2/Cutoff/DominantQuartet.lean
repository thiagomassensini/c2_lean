import Mathlib
import LeanC2.Cutoff.Residue

set_option linter.style.whitespace false

namespace LeanC2

open scoped BigOperators

/-- Four-shell kernel carried by the dominant quartet package. -/
noncomputable def dominantQuartetKernel (z : Complex) : Complex :=
  1 + z + z ^ 2 + z ^ 3

/-- Shell coefficient contributed by the dominant quartet `k = 2,3,4,5`. -/
noncomputable def dominantQuartetCoeff (s : Complex) : Complex :=
  ∑ k ∈ Finset.Icc 2 5, (2 : Complex) * shellRatio s ^ k

/-- Finite shell tail beyond the dominant quartet. -/
noncomputable def dominantTailCoeff (s : Complex) (K : Nat) : Complex :=
  ∑ k ∈ Finset.Icc 6 K, (2 : Complex) * shellRatio s ^ k

/-- Cutoff first-shell channel `F_2` summed over the finite odd-core window. -/
noncomputable def cutoffFirstShell (X : Nat) (s : Complex) : Complex :=
  ((2 : Complex) * shellRatio s ^ 2) * oddZetaPartial s (X + 1)

/-- Dominant quartet contribution inside the finite cutoff window. -/
noncomputable def cutoffDominantQuartet (X : Nat) (s : Complex) : Complex :=
  dominantQuartetCoeff s * oddZetaPartial s (X + 1)

/-- Finite tail contribution beyond the dominant quartet. -/
noncomputable def cutoffDominantTail (X : Nat) (s : Complex) : Complex :=
  dominantTailCoeff s (cutoffDepth X) * oddZetaPartial s (X + 1)

theorem dominantQuartetKernel_eq_closedForm {z : Complex} (hneq : z ≠ 1) :
    dominantQuartetKernel z = (1 - z ^ 4) / (1 - z) := by
  have hz : (1 : Complex) - z ≠ 0 := by
    exact sub_ne_zero.mpr (by simpa [eq_comm] using hneq)
  have hcf : (1 - z ^ 4) / (1 - z) = dominantQuartetKernel z := by
    apply (div_eq_iff hz).2
    unfold dominantQuartetKernel
    ring
  exact hcf.symm

theorem norm_dominantQuartetKernel_ge_sharp {z : Complex} (hz1 : ‖z‖ < 1) :
    (1 - ‖z‖) * (1 + ‖z‖ ^ 2) ≤ ‖dominantQuartetKernel z‖ := by
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hneq : z ≠ 1 := by
    intro hz
    have hnorm : ‖z‖ = 1 := by simp [hz]
    linarith
  have hdenUpper : ‖1 - z‖ ≤ 1 + ‖z‖ := by
    calc
      ‖1 - z‖ = ‖(1 : Complex) + (-z)‖ := by simp [sub_eq_add_neg]
      _ ≤ ‖(1 : Complex)‖ + ‖-z‖ := norm_add_le _ _
      _ = 1 + ‖z‖ := by rw [norm_one, norm_neg]
  have hz4 : ‖z ^ 4‖ = ‖z‖ ^ 4 := by rw [norm_pow]
  have hnumLower : 1 - ‖z‖ ^ 4 ≤ ‖1 - z ^ 4‖ := by
    have hraw : ‖(1 : Complex)‖ - ‖z ^ 4‖ ≤ ‖(1 : Complex) - z ^ 4‖ :=
      norm_sub_norm_le _ _
    rw [norm_one, hz4] at hraw
    simpa using hraw
  have hdenPos : 0 < ‖1 - z‖ := by
    apply norm_pos_iff.mpr
    exact sub_ne_zero.mpr hneq.symm
  have hinv : (1 + ‖z‖)⁻¹ ≤ ‖1 - z‖⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hdenPos hdenUpper
  have hpowlt : ‖z‖ ^ 4 < 1 := by
    exact pow_lt_one₀ hz0 hz1 (by decide : (4 : Nat) ≠ 0)
  have hbound : (1 - ‖z‖ ^ 4) / (1 + ‖z‖) ≤ ‖1 - z ^ 4‖ / ‖1 - z‖ := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hbound1 : (1 - ‖z‖ ^ 4) * (1 + ‖z‖)⁻¹ ≤ ‖1 - z ^ 4‖ * (1 + ‖z‖)⁻¹ := by
      apply mul_le_mul_of_nonneg_right hnumLower
      positivity
    have hbound2 : ‖1 - z ^ 4‖ * (1 + ‖z‖)⁻¹ ≤ ‖1 - z ^ 4‖ * ‖1 - z‖⁻¹ := by
      exact mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
    exact le_trans hbound1 hbound2
  have hsharp : (1 - ‖z‖ ^ 4) / (1 + ‖z‖) = (1 - ‖z‖) * (1 + ‖z‖ ^ 2) := by
    have hneq' : (1 : Real) + ‖z‖ ≠ 0 := by linarith
    field_simp [hneq']
    ring
  have hnorm : ‖dominantQuartetKernel z‖ = ‖1 - z ^ 4‖ / ‖1 - z‖ := by
    rw [dominantQuartetKernel_eq_closedForm hneq, norm_div]
  calc
    (1 - ‖z‖) * (1 + ‖z‖ ^ 2) = (1 - ‖z‖ ^ 4) / (1 + ‖z‖) := hsharp.symm
    _ ≤ ‖1 - z ^ 4‖ / ‖1 - z‖ := hbound
    _ = ‖dominantQuartetKernel z‖ := hnorm.symm

theorem dominantTailCoeff_eq_geometric (s : Complex) {K : Nat} (hK : 6 ≤ K)
    (hq : shellRatio s ≠ 1) :
    dominantTailCoeff s K =
      (2 : Complex) * ((shellRatio s ^ 6 - shellRatio s ^ (K + 1)) / (1 - shellRatio s)) := by
  unfold dominantTailCoeff
  rw [show Finset.Icc 6 K = Finset.Ico 6 (K + 1) by
    ext k
    simp]
  rw [← Finset.mul_sum]
  rw [geom_sum_Ico' hq (by omega)]

theorem norm_dominantTailCoeff_le (s : Complex) {K : Nat} (hs : -1 < s.re) :
    ‖dominantTailCoeff s K‖ ≤ 2 * ‖shellRatio s‖ ^ 6 / (1 - ‖shellRatio s‖) := by
  let q : Real := ‖shellRatio s‖
  have hq0 : 0 ≤ q := by
    simp [q]
  have hq1 : q < 1 := by
    simpa [q] using norm_shellRatio_lt_one_of_re_gt_neg_one hs
  have hIcc : Finset.Icc 6 K = Finset.Ico 6 (K + 1) := by
    ext k
    simp
  calc
    ‖dominantTailCoeff s K‖
      ≤ ∑ k ∈ Finset.Icc 6 K, ‖(2 : Complex) * shellRatio s ^ k‖ := by
          unfold dominantTailCoeff
          exact norm_sum_le _ _
    _ = ∑ k ∈ Finset.Icc 6 K, (2 : Real) * q ^ k := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          simp [q, norm_pow]
    _ = ∑ k ∈ Finset.Ico 6 (K + 1), (2 : Real) * q ^ k := by
          rw [hIcc]
    _ = (2 : Real) * ∑ k ∈ Finset.Ico 6 (K + 1), q ^ k := by
          rw [← Finset.mul_sum]
    _ ≤ (2 : Real) * (q ^ 6 / (1 - q)) := by
          exact mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq0 hq1) (by norm_num)
    _ = 2 * ‖shellRatio s‖ ^ 6 / (1 - ‖shellRatio s‖) := by
          simp [q, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

theorem norm_cutoffFirstShell (X : Nat) (s : Complex) :
    ‖cutoffFirstShell X s‖ = (2 * ‖shellRatio s‖ ^ 2) * ‖oddZetaPartial s (X + 1)‖ := by
  unfold cutoffFirstShell
  calc
    ‖((2 : Complex) * shellRatio s ^ 2) * oddZetaPartial s (X + 1)‖ =
        ‖(2 : Complex) * shellRatio s ^ 2‖ * ‖oddZetaPartial s (X + 1)‖ := by
          rw [norm_mul]
    _ = (2 * ‖shellRatio s‖ ^ 2) * ‖oddZetaPartial s (X + 1)‖ := by
          rw [norm_mul, norm_pow]
          norm_num

theorem norm_cutoffDominantTail_le (X : Nat) (s : Complex) (hs : -1 < s.re) :
    ‖cutoffDominantTail X s‖ ≤
      (2 * ‖shellRatio s‖ ^ 6 / (1 - ‖shellRatio s‖)) * ‖oddZetaPartial s (X + 1)‖ := by
  unfold cutoffDominantTail
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_dominantTailCoeff_le s hs) (norm_nonneg _)

theorem norm_cutoffDominantTail_le_cutoffFirstShell (X : Nat) (s : Complex) (hs : -1 < s.re) :
    ‖cutoffDominantTail X s‖ ≤
      (‖shellRatio s‖ ^ 4 / (1 - ‖shellRatio s‖)) * ‖cutoffFirstShell X s‖ := by
  have hq : ‖shellRatio s‖ < 1 := norm_shellRatio_lt_one_of_re_gt_neg_one hs
  have hden : 1 - ‖shellRatio s‖ ≠ 0 := by
    apply sub_ne_zero.mpr
    linarith
  calc
    ‖cutoffDominantTail X s‖
      ≤ (2 * ‖shellRatio s‖ ^ 6 / (1 - ‖shellRatio s‖)) * ‖oddZetaPartial s (X + 1)‖ := by
          exact norm_cutoffDominantTail_le X s hs
    _ = (‖shellRatio s‖ ^ 4 / (1 - ‖shellRatio s‖)) *
          ((2 * ‖shellRatio s‖ ^ 2) * ‖oddZetaPartial s (X + 1)‖) := by
            field_simp [hden]
    _ = (‖shellRatio s‖ ^ 4 / (1 - ‖shellRatio s‖)) * ‖cutoffFirstShell X s‖ := by
          rw [norm_cutoffFirstShell]

theorem dominantQuartetCoeff_eq_firstShell_mul_kernel (s : Complex) :
    dominantQuartetCoeff s =
      ((2 : Complex) * shellRatio s ^ 2) * dominantQuartetKernel (shellRatio s) := by
  unfold dominantQuartetCoeff dominantQuartetKernel
  rw [show Finset.Icc 2 5 = ({2, 3, 4, 5} : Finset Nat) by decide]
  simp
  ring

theorem cutoffDominantQuartet_eq_firstShell_mul_kernel (X : Nat) (s : Complex) :
    cutoffDominantQuartet X s =
      cutoffFirstShell X s * dominantQuartetKernel (shellRatio s) := by
  unfold cutoffDominantQuartet cutoffFirstShell
  rw [dominantQuartetCoeff_eq_firstShell_mul_kernel]
  ring

theorem norm_cutoffDominantQuartet_ge (X : Nat) (s : Complex) (hs : -1 < s.re) :
    ((1 - ‖shellRatio s‖) * (1 + ‖shellRatio s‖ ^ 2)) * ‖cutoffFirstShell X s‖ ≤
      ‖cutoffDominantQuartet X s‖ := by
  have hkernel :
      (1 - ‖shellRatio s‖) * (1 + ‖shellRatio s‖ ^ 2) ≤
        ‖dominantQuartetKernel (shellRatio s)‖ := by
    exact norm_dominantQuartetKernel_ge_sharp (norm_shellRatio_lt_one_of_re_gt_neg_one hs)
  calc
    ((1 - ‖shellRatio s‖) * (1 + ‖shellRatio s‖ ^ 2)) * ‖cutoffFirstShell X s‖ =
        ‖cutoffFirstShell X s‖ * ((1 - ‖shellRatio s‖) * (1 + ‖shellRatio s‖ ^ 2)) := by
          ring
    _ ≤ ‖cutoffFirstShell X s‖ * ‖dominantQuartetKernel (shellRatio s)‖ := by
          exact mul_le_mul_of_nonneg_left hkernel (norm_nonneg _)
    _ = ‖cutoffDominantQuartet X s‖ := by
          rw [cutoffDominantQuartet_eq_firstShell_mul_kernel, norm_mul]

theorem cutoffDominantQuartet_sub_tail_margin_lower_bound
  (X : Nat) (s : Complex) (hs : -1 < s.re) :
    (((1 - ‖shellRatio s‖) * (1 + ‖shellRatio s‖ ^ 2)) -
        (‖shellRatio s‖ ^ 4 / (1 - ‖shellRatio s‖))) * ‖cutoffFirstShell X s‖ ≤
      ‖cutoffDominantQuartet X s‖ - ‖cutoffDominantTail X s‖ := by
  have hQuartet :
      ((1 - ‖shellRatio s‖) * (1 + ‖shellRatio s‖ ^ 2)) * ‖cutoffFirstShell X s‖ ≤
        ‖cutoffDominantQuartet X s‖ :=
    norm_cutoffDominantQuartet_ge X s hs
  have hTail :
      ‖cutoffDominantTail X s‖ ≤
        (‖shellRatio s‖ ^ 4 / (1 - ‖shellRatio s‖)) * ‖cutoffFirstShell X s‖ :=
    norm_cutoffDominantTail_le_cutoffFirstShell X s hs
  linarith

theorem norm_shellRatio_eq_criticalLine (s : Complex) (hcrit : s.re = (1 : ℝ) / 2) :
    ‖shellRatio s‖ = Real.sqrt 2 / 4 := by
  rw [norm_shellRatio_eq, hcrit]
  calc
    (1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 2 : ℝ)) = (1 / 2 : ℝ) * ((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
      rw [Real.rpow_neg (by positivity)]
    _ = (1 / 2 : ℝ) * (Real.sqrt 2)⁻¹ := by
      rw [Real.sqrt_eq_rpow]
    _ = Real.sqrt 2 / 4 := by
      have hsqrt_pos : 0 < Real.sqrt 2 := by
        exact Real.sqrt_pos.2 (by positivity)
      have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := by
        rw [Real.sq_sqrt]
        positivity
      field_simp [hsqrt_pos.ne']
      nlinarith

theorem criticalLine_cutoffDominantQuartet_margin_coeff_eq (s : Complex)
    (hcrit : s.re = (1 : ℝ) / 2) :
    ((1 - ‖shellRatio s‖) * (1 + ‖shellRatio s‖ ^ 2) -
      (‖shellRatio s‖ ^ 4 / (1 - ‖shellRatio s‖))) =
        31 / 28 - 2 * Real.sqrt 2 / 7 := by
  rw [norm_shellRatio_eq_criticalLine s hcrit]
  set t : ℝ := Real.sqrt 2
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    exact Real.sqrt_nonneg 2
  have ht_sq : t ^ 2 = 2 := by
    dsimp [t]
    rw [Real.sq_sqrt]
    positivity
  have hq2 : (t / 4) ^ 2 = (1 / 8 : ℝ) := by
    field_simp
    nlinarith [ht_sq]
  have hq4 : (t / 4) ^ 4 = (1 / 64 : ℝ) := by
    calc
      (t / 4) ^ 4 = ((t / 4) ^ 2) ^ 2 := by ring
      _ = (1 / 8 : ℝ) ^ 2 := by rw [hq2]
      _ = (1 / 64 : ℝ) := by norm_num
  have hden : 1 - t / 4 ≠ 0 := by
    nlinarith [ht_nonneg, ht_sq]
  have hrecip : (1 / (1 - t / 4) : ℝ) = 8 / 7 + 2 * t / 7 := by
    apply (div_eq_iff hden).2
    nlinarith [ht_sq]
  have hinv : (1 - t / 4)⁻¹ = 8 / 7 + 2 * t / 7 := by
    simpa [one_div] using hrecip
  have hdiv : (1 / 64 : ℝ) / (1 - t / 4) = 1 / 56 + t / 224 := by
    rw [div_eq_mul_inv, hinv]
    ring
  change ((1 - t / 4) * (1 + (t / 4) ^ 2) - ((t / 4) ^ 4 / (1 - t / 4))) =
      31 / 28 - 2 * t / 7
  rw [hq2, hq4, hdiv]
  ring

theorem criticalLine_cutoffDominantQuartet_margin_coeff_ge_seventyHundredths (s : Complex)
    (hcrit : s.re = (1 : ℝ) / 2) :
    (7 / 10 : ℝ) ≤
      ((1 - ‖shellRatio s‖) * (1 + ‖shellRatio s‖ ^ 2) -
        (‖shellRatio s‖ ^ 4 / (1 - ‖shellRatio s‖))) := by
  rw [criticalLine_cutoffDominantQuartet_margin_coeff_eq s hcrit]
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := by
    rw [Real.sq_sqrt]
    positivity
  nlinarith [Real.sqrt_nonneg 2, hsqrt_sq]

theorem cutoffDominantQuartet_sub_tail_margin_lower_bound_criticalLine_seventyHundredths
    (X : Nat) (s : Complex) (hcrit : s.re = (1 : ℝ) / 2) :
    (7 / 10 : ℝ) * ‖cutoffFirstShell X s‖ ≤
      ‖cutoffDominantQuartet X s‖ - ‖cutoffDominantTail X s‖ := by
  have hs : -1 < s.re := by linarith [hcrit]
  have hcoeff :
      (7 / 10 : ℝ) ≤
        ((1 - ‖shellRatio s‖) * (1 + ‖shellRatio s‖ ^ 2) -
          (‖shellRatio s‖ ^ 4 / (1 - ‖shellRatio s‖))) :=
    criticalLine_cutoffDominantQuartet_margin_coeff_ge_seventyHundredths s hcrit
  have hmargin := cutoffDominantQuartet_sub_tail_margin_lower_bound X s hs
  have hscaled :
      (7 / 10 : ℝ) * ‖cutoffFirstShell X s‖ ≤
        (((1 - ‖shellRatio s‖) * (1 + ‖shellRatio s‖ ^ 2)) -
          (‖shellRatio s‖ ^ 4 / (1 - ‖shellRatio s‖))) * ‖cutoffFirstShell X s‖ := by
    exact mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
  exact le_trans hscaled hmargin

theorem centerCoeffPartial_eq_dominantQuartetCoeff_add_tail {s : Complex} {K : Nat}
    (hK : 5 ≤ K) :
    centerCoeffPartial s K = dominantQuartetCoeff s + dominantTailCoeff s K := by
  unfold centerCoeffPartial dominantQuartetCoeff dominantTailCoeff depthWindow
  have hUnion :
      Finset.Icc 2 K = Finset.Icc 2 5 ∪ Finset.Icc 6 K := by
    ext k
    simp
    omega
  have hDisj : Disjoint (Finset.Icc 2 5) (Finset.Icc 6 K) := by
    refine Finset.disjoint_left.2 ?_
    intro k hk1 hk2
    simp at hk1 hk2
    omega
  rw [hUnion, Finset.sum_union hDisj]

theorem partialNumeratorSum_eq_dominantQuartet_add_tail {s : Complex} {K M : Nat}
    (hK : 5 ≤ K) :
    (∑ m ∈ Finset.range M, partialFCore s K m) =
      dominantQuartetCoeff s * oddZetaPartial s M +
        dominantTailCoeff s K * oddZetaPartial s M := by
  rw [finiteNumerator_sum_eq_centerCoeffPartial_mul_oddZetaPartial,
    centerCoeffPartial_eq_dominantQuartetCoeff_add_tail hK]
  simp [add_mul]

theorem sharpCutoffFamily_eq_partialNumeratorSum (X : Nat) (s : Complex) :
    sharpCutoffFamily X s =
      ∑ m ∈ cutoffCoreWindow X, partialFCore s (cutoffDepth X) m := by
  unfold sharpCutoffFamily sharpCutoffD canonicalCutoffB cutoffCoreWindow partialFCore
  rw [← Finset.sum_sub_distrib]

theorem sharpCutoffFamily_eq_cutoffDominantQuartet_add_tail {X : Nat} (s : Complex)
    (hX : 3 ≤ X) :
    sharpCutoffFamily X s = cutoffDominantQuartet X s + cutoffDominantTail X s := by
  have hK : 5 ≤ cutoffDepth X := by
    unfold cutoffDepth
    omega
  calc
    sharpCutoffFamily X s = ∑ m ∈ Finset.range (X + 1), partialFCore s (cutoffDepth X) m := by
      simpa [cutoffCoreWindow] using sharpCutoffFamily_eq_partialNumeratorSum X s
    _ = dominantQuartetCoeff s * oddZetaPartial s (X + 1) +
          dominantTailCoeff s (cutoffDepth X) * oddZetaPartial s (X + 1) := by
            exact partialNumeratorSum_eq_dominantQuartet_add_tail hK
    _ = cutoffDominantQuartet X s + cutoffDominantTail X s := by
          rfl

theorem canonicalCutoffFamily_eq_cutoffDominantQuartet_add_tail_add_residual
    {X : Nat} (s : Complex) (hX : 3 ≤ X) :
    canonicalCutoffFamily X s =
      cutoffDominantQuartet X s + cutoffDominantTail X s + canonicalCutoffResidual X s := by
  calc
    canonicalCutoffFamily X s = sharpCutoffFamily X s + canonicalCutoffResidual X s := by
      exact canonicalCutoffFamily_eq_sharpCutoffFamily_add_residual X s
    _ = (cutoffDominantQuartet X s + cutoffDominantTail X s) + canonicalCutoffResidual X s := by
      rw [sharpCutoffFamily_eq_cutoffDominantQuartet_add_tail (X := X) s hX]
    _ = cutoffDominantQuartet X s + cutoffDominantTail X s + canonicalCutoffResidual X s := by
      ring

end LeanC2