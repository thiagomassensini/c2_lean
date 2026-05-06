import Mathlib
import Antigo_Lean_C2.Pushforward
import LeanC2.Operators.Genuine

set_option linter.style.whitespace false

namespace LeanC2

open scoped BigOperators

/-- Real odd Dirichlet series over the positive odd cores. -/
noncomputable def ZOddReal (sigma : Real) : Real :=
  ∑' n : Nat, ((oddCore n : Real) ^ (-sigma))

/-- Finite-cutoff odd Dirichlet approximant built from the arithmetic pushforward mass. -/
noncomputable def AMReal (M : Nat) (sigma : Real) : Real :=
  ∑' n : Nat, pushforwardMass M (oddCore n) * ((oddCore n : Real) ^ (-sigma))

/-- Pointwise odd-channel error coefficient. -/
noncomputable def oddPushforwardErrorTerm (M : Nat) (sigma : Real) (n : Nat) : Real :=
  (1 - pushforwardMass M (oddCore n)) * ((oddCore n : Real) ^ (-sigma))

/-- Explicit subcritical constant for the `A_M` approximation bound. -/
noncomputable def subcriticalBoundConst (sigma : Real) : Real :=
  (2 : Real) ^ (sigma - 1) *
    (4 + (4 : Real) ^ (sigma - 1) / (2 - sigma) +
      sigma / (sigma - 1) * (4 : Real) ^ (sigma - 1))

/-- Explicit supercritical constant for the `A_M` approximation bound. -/
noncomputable def supercriticalBoundConst (sigma : Real) : Real :=
  8 * (sigma - 1) / (sigma - 2)

lemma oddCore_succ_le (n : Nat) : n + 1 ≤ oddCore n := by
  unfold oddCore
  omega

lemma oddCore_rpow_neg_le_natSucc_rpow_neg {sigma : Real} (hs : 0 < sigma) (n : Nat) :
    ((oddCore n : Real) ^ (-sigma)) ≤ ((n + 1 : Real) ^ (-sigma)) := by
  have hoddPos : 0 < (oddCore n : Real) := by exact_mod_cast oddCore_pos n
  have hsuccPos : 0 < (n + 1 : Real) := by positivity
  have hneg : -sigma < 0 := by linarith
  rw [Real.rpow_le_rpow_iff_of_neg hoddPos hsuccPos hneg]
  exact_mod_cast oddCore_succ_le n

lemma oddCore_rpow_one_sub_le_natSucc_rpow_one_sub {sigma : Real} (hs : 1 < sigma) (n : Nat) :
    ((oddCore n : Real) ^ (1 - sigma)) ≤ ((n + 1 : Real) ^ (1 - sigma)) := by
  have hoddPos : 0 < (oddCore n : Real) := by exact_mod_cast oddCore_pos n
  have hsuccPos : 0 < (n + 1 : Real) := by positivity
  have hneg : 1 - sigma < 0 := by linarith
  rw [Real.rpow_le_rpow_iff_of_neg hoddPos hsuccPos hneg]
  exact_mod_cast oddCore_succ_le n

lemma pushforwardMass_nonneg (M m : Nat) : 0 ≤ pushforwardMass M m := by
  unfold pushforwardMass
  refine add_nonneg ?_ ?_
  · exact Finset.sum_nonneg fun k _ => by
      simp [dyadicWeight]
  · exact Finset.sum_nonneg fun k _ => by
      simp [dyadicWeight]

lemma oddPushforwardErrorTerm_nonneg (M : Nat) (sigma : Real) (n : Nat) :
    0 ≤ oddPushforwardErrorTerm M sigma n := by
  unfold oddPushforwardErrorTerm
  have hcoeff : 0 ≤ 1 - pushforwardMass M (oddCore n) := by
    linarith [pushforwardMass_le_one M (oddCore n)]
  have hpow : 0 ≤ ((oddCore n : Real) ^ (-sigma)) := by positivity
  positivity

lemma oddPushforwardErrorTerm_le_oddCoreTerm (M : Nat) (sigma : Real) (n : Nat) :
    oddPushforwardErrorTerm M sigma n ≤ ((oddCore n : Real) ^ (-sigma)) := by
  have hpow : 0 ≤ ((oddCore n : Real) ^ (-sigma)) := by positivity
  have hcoeff : 1 - pushforwardMass M (oddCore n) ≤ 1 := by
    linarith [pushforwardMass_nonneg M (oddCore n)]
  calc
    oddPushforwardErrorTerm M sigma n =
        (1 - pushforwardMass M (oddCore n)) * ((oddCore n : Real) ^ (-sigma)) := by
          rfl
    _ ≤ 1 * ((oddCore n : Real) ^ (-sigma)) := by gcongr
    _ = ((oddCore n : Real) ^ (-sigma)) := by ring

lemma quarter_scale_rpow (M : Nat) (sigma : Real) :
    (((M - 1 : Real) / 4) ^ (1 - sigma)) =
      (4 : Real) ^ (sigma - 1) * (M - 1 : Real) ^ (1 - sigma) := by
  have hM1 : 0 ≤ (((M - 1 : Nat) : Real)) := by positivity
  have hM1' : 0 ≤ (M - 1 : Real) := by simpa using hM1
  calc
    (((M - 1 : Real) / 4) ^ (1 - sigma)) =
        (M - 1 : Real) ^ (1 - sigma) / (4 : Real) ^ (1 - sigma) := by
          rw [Real.div_rpow hM1' (by positivity) (1 - sigma)]
    _ = (M - 1 : Real) ^ (1 - sigma) * ((4 : Real) ^ (1 - sigma))⁻¹ := by
          rw [div_eq_mul_inv]
    _ = (M - 1 : Real) ^ (1 - sigma) * (4 : Real) ^ (sigma - 1) := by
          congr 1
          rw [← Real.rpow_neg (by positivity : 0 ≤ (4 : Real))]
          congr 1
          ring
    _ = (4 : Real) ^ (sigma - 1) * (M - 1 : Real) ^ (1 - sigma) := by ring

lemma summable_natSucc_rpow_neg {sigma : Real} (hs : 1 < sigma) :
    Summable (fun n : Nat => ((n + 1 : Real) ^ (-sigma))) := by
  simpa [add_comm, add_left_comm, add_assoc] using
    ((_root_.summable_nat_add_iff 1).2 (Real.summable_nat_rpow.mpr (by linarith : -sigma < -1)))

lemma summable_shift_natSucc_rpow_neg {sigma : Real} (hs : 1 < sigma) (K : Nat) :
    Summable (fun n : Nat => ((n + K + 1 : Real) ^ (-sigma))) := by
  simpa [add_assoc] using
    ((summable_nat_add_iff K).2 (summable_natSucc_rpow_neg hs))

lemma summable_ZOddReal (sigma : Real) (hs : 1 < sigma) :
    Summable (fun n : Nat => ((oddCore n : Real) ^ (-sigma))) := by
  exact Summable.of_nonneg_of_le (f := fun n : Nat => ((n + 1 : Real) ^ (-sigma)))
    (fun n => by positivity)
    (fun n => oddCore_rpow_neg_le_natSucc_rpow_neg (by linarith) n)
    (summable_natSucc_rpow_neg hs)

lemma summable_AMReal (M : Nat) (sigma : Real) (hs : 1 < sigma) :
    Summable (fun n : Nat => pushforwardMass M (oddCore n) * ((oddCore n : Real) ^ (-sigma))) := by
  refine Summable.of_nonneg_of_le ?_ ?_ (summable_ZOddReal sigma hs)
  · intro n
    exact mul_nonneg (pushforwardMass_nonneg M (oddCore n)) (by positivity)
  · intro n
    have hpow : 0 ≤ ((oddCore n : Real) ^ (-sigma)) := by positivity
    calc
      pushforwardMass M (oddCore n) * ((oddCore n : Real) ^ (-sigma))
        ≤ 1 * ((oddCore n : Real) ^ (-sigma)) := by
            gcongr
            exact pushforwardMass_le_one M (oddCore n)
      _ = ((oddCore n : Real) ^ (-sigma)) := by ring

lemma summable_oddPushforwardErrorTerm (M : Nat) (sigma : Real) (hs : 1 < sigma) :
    Summable (fun n : Nat => oddPushforwardErrorTerm M sigma n) := by
  refine Summable.of_nonneg_of_le ?_ ?_ (summable_natSucc_rpow_neg hs)
  · intro n
    exact oddPushforwardErrorTerm_nonneg M sigma n
  · intro n
    calc
      oddPushforwardErrorTerm M sigma n ≤ ((oddCore n : Real) ^ (-sigma)) :=
        oddPushforwardErrorTerm_le_oddCoreTerm M sigma n
      _ ≤ ((n + 1 : Real) ^ (-sigma)) :=
        oddCore_rpow_neg_le_natSucc_rpow_neg (by linarith) n

theorem ZOddReal_sub_AMReal_eq_tsum_error (M : Nat) (sigma : Real) (hs : 1 < sigma) :
    ZOddReal sigma - AMReal M sigma = ∑' n : Nat, oddPushforwardErrorTerm M sigma n := by
  have hsum : HasSum
      (fun n : Nat =>
        ((oddCore n : Real) ^ (-sigma)) -
          pushforwardMass M (oddCore n) * ((oddCore n : Real) ^ (-sigma)))
      (ZOddReal sigma - AMReal M sigma) := by
    simpa [ZOddReal, AMReal] using
      (summable_ZOddReal sigma hs).hasSum.sub (summable_AMReal M sigma hs).hasSum
  calc
    ZOddReal sigma - AMReal M sigma =
        ∑' n : Nat,
          (((oddCore n : Real) ^ (-sigma)) -
            pushforwardMass M (oddCore n) * ((oddCore n : Real) ^ (-sigma))) := by
              exact hsum.tsum_eq.symm
    _ = ∑' n : Nat, oddPushforwardErrorTerm M sigma n := by
          congr with n
          simp [oddPushforwardErrorTerm]
          ring

theorem ZOddReal_sub_AMReal_nonneg (M : Nat) (sigma : Real) (hs : 1 < sigma) :
    0 ≤ ZOddReal sigma - AMReal M sigma := by
  rw [ZOddReal_sub_AMReal_eq_tsum_error M sigma hs]
  exact tsum_nonneg (fun n => oddPushforwardErrorTerm_nonneg M sigma n)

theorem ZOddReal_sub_AMReal_eq_inside_add_tail (M : Nat) (sigma : Real) (hs : 1 < sigma)
    (K : Nat) :
    ZOddReal sigma - AMReal M sigma =
      (∑ n ∈ Finset.range K, oddPushforwardErrorTerm M sigma n) +
        ∑' n : Nat, oddPushforwardErrorTerm M sigma (n + K) := by
  rw [ZOddReal_sub_AMReal_eq_tsum_error M sigma hs]
  exact ((summable_oddPushforwardErrorTerm M sigma hs).sum_add_tsum_nat_add K).symm

lemma sum_range_natSucc_rpow_one_sub_le {sigma : Real} (hs1 : 1 < sigma) (hs2 : sigma < 2)
    (K : Nat) :
    ∑ n ∈ Finset.range K, ((n + 1 : Real) ^ (1 - sigma)) ≤
      1 + (K : Real) ^ (2 - sigma) / (2 - sigma) := by
  by_cases hK0 : K = 0
  · subst hK0
    have hnonneg : 0 ≤ 1 + (0 : Real) ^ (2 - sigma) / (2 - sigma) := by positivity
    simp [hnonneg]
  have hK : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr hK0
  calc
    ∑ n ∈ Finset.range K, ((n + 1 : Real) ^ (1 - sigma)) =
        1 + ∑ n ∈ Finset.Ico 1 K, ((n + 1 : Real) ^ (1 - sigma)) := by
          rw [Finset.sum_range_eq_add_Ico _ hK]
          simp
    _ ≤ 1 + ∫ x in (1 : Real)..(K : Real), x ^ (1 - sigma) := by
          gcongr
          exact @AntitoneOn.sum_le_integral_Ico 1 K
            (fun x : ℝ => x ^ (1 - sigma)) (by exact_mod_cast hK) <| by
              intro x hx y hy hxy
              have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
              have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy.1
              have hneg : 1 - sigma < 0 := by linarith
              rw [Real.rpow_le_rpow_iff_of_neg hypos hxpos hneg]
              linarith
    _ = 1 + (((K : Real) ^ (2 - sigma) - (1 : Real) ^ (2 - sigma)) / (2 - sigma)) := by
          congr 1
          rw [integral_rpow (Or.inr ?_)]
          · ring_nf
          · constructor
            · linarith
            · simp [Set.uIcc_of_le, hK]
    _ ≤ 1 + (K : Real) ^ (2 - sigma) / (2 - sigma) := by
          have hpos : 0 < 2 - sigma := by linarith
          have hbound : ((K : Real) ^ (2 - sigma) - (1 : Real) ^ (2 - sigma)) / (2 - sigma)
              ≤ (K : Real) ^ (2 - sigma) / (2 - sigma) := by
            have hnonneg : 0 ≤ (1 : Real) / (2 - sigma) := by positivity
            simp
            nlinarith
          linarith

lemma sum_range_natSucc_inv_le_one_add_log (K : Nat) :
    ∑ n ∈ Finset.range K, ((n + 1 : Real)⁻¹) ≤ 1 + Real.log (K + 1) := by
  calc
    ∑ n ∈ Finset.range K, ((n + 1 : Real)⁻¹)
      ≤ ∑ n ∈ Finset.range (K + 1), ((n + 1 : Real)⁻¹) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hn) (Nat.le_succ K))
          intro n hn hnot
          positivity
    _ = ((harmonic (K + 1) : ℚ) : ℝ) := by
          simp [harmonic]
    _ ≤ 1 + Real.log (K + 1) := by
          simpa using (harmonic_le_one_add_log (K + 1))

lemma sum_range_shift_rpow_neg_le {sigma : Real} (hs : 1 < sigma) (K N : Nat) :
    ∑ n ∈ Finset.range N, ((n + K + 1 : Real) ^ (-sigma)) ≤
      sigma / (sigma - 1) * ((K + 1 : Real) ^ (1 - sigma)) := by
  by_cases hN0 : N = 0
  · subst hN0
    have hnonneg : 0 ≤ sigma / (sigma - 1) * ((K + 1 : Real) ^ (1 - sigma)) := by positivity
    simp [hnonneg]
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  have hab : (K + 1 : Real) ≤ K + N := by
    exact_mod_cast Nat.add_le_add_left hN K
  have hiA : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-sigma)) (Set.Ioi (K + 1 : Real)) := by
    exact integrableOn_Ioi_rpow_of_lt (by linarith) (by positivity)
  have hIoiNonneg : 0 ≤ ∫ x in Set.Ioi (K + N : Real), x ^ (-sigma) := by
    exact MeasureTheory.integral_nonneg fun x => by positivity
  calc
    ∑ n ∈ Finset.range N, ((n + K + 1 : Real) ^ (-sigma)) =
        ((K + 1 : Real) ^ (-sigma)) +
          ∑ n ∈ Finset.Ico 1 N, ((n + K + 1 : Real) ^ (-sigma)) := by
          rw [Finset.sum_range_eq_add_Ico _ hN]
          ring_nf
    _ ≤ ((K + 1 : Real) ^ (-sigma)) + ∫ x in (K + 1 : Real)..(K + N : Real), x ^ (-sigma) := by
          gcongr
          have hsum := @AntitoneOn.sum_le_integral_Ico (K + 1) (K + N)
            (fun x : ℝ => x ^ (-sigma)) (by omega) <| by
              intro x hx y hy hxy
              have hxpos : 0 < x := lt_of_lt_of_le (by exact_mod_cast Nat.succ_pos K) hx.1
              have hypos : 0 < y := lt_of_lt_of_le (by exact_mod_cast Nat.succ_pos K) hy.1
              have hneg : -sigma < 0 := by linarith
              rw [Real.rpow_le_rpow_iff_of_neg hypos hxpos hneg]
              linarith
          have hsubNat : K + N - (K + 1) = N - 1 := by omega
          simpa [Finset.sum_Ico_eq_sum_range, hsubNat, add_assoc, add_left_comm, add_comm] using hsum
    _ ≤ ((K + 1 : Real) ^ (-sigma)) + ∫ x in Set.Ioi (K + 1 : Real), x ^ (-sigma) := by
          have hsub := intervalIntegral.integral_Ioi_sub_Ioi
            (μ := MeasureTheory.volume) (f := fun x : ℝ => x ^ (-sigma)) hiA hab
          linarith
    _ = ((K + 1 : Real) ^ (-sigma)) + ((K + 1 : Real) ^ (1 - sigma) / (sigma - 1)) := by
          rw [integral_Ioi_rpow_of_lt (a := -sigma) (c := K + 1) (by linarith) (by positivity)]
          field_simp [show (sigma - 1) ≠ 0 by linarith]
          ring_nf
    _ ≤ sigma / (sigma - 1) * ((K + 1 : Real) ^ (1 - sigma)) := by
          have hbase : 1 ≤ (K + 1 : Real) := by positivity
          have hpow : ((K + 1 : Real) ^ (-sigma)) ≤ ((K + 1 : Real) ^ (1 - sigma)) := by
            exact Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
          have hden : 0 < sigma - 1 := by linarith
          gcongr
          · exact hpow
          · exact le_of_lt hden
          · positivity
          · positivity
          · field_simp [show (sigma - 1) ≠ 0 by linarith]
            ring

lemma tsum_shift_natSucc_rpow_neg_le {sigma : Real} (hs : 1 < sigma) (K : Nat) :
    ∑' n : Nat, ((n + K + 1 : Real) ^ (-sigma)) ≤
      sigma / (sigma - 1) * ((K + 1 : Real) ^ (1 - sigma)) := by
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) ?_
  intro N
  exact sum_range_shift_rpow_neg_le hs K N

lemma pushforwardMassError_le_linear {M m : Nat} (hM : 2 ≤ M) (hm : Odd m) :
    1 - pushforwardMass M m ≤ (4 : Real) * m / (M - 1) := by
  have hm1 : 1 ≤ m := one_le_of_nat_odd hm
  have hmpos : 0 < m := Nat.succ_le_iff.mp hm1
  have hM1pos : 0 < (M - 1 : Real) := by
    exact_mod_cast Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hM)
  by_cases hrow : natDescendant 2 BranchSign.plus m ≤ M
  · let K := plusCutoff M m
    have hK : 2 ≤ K := by
      exact (plus_cutoff_iff hmpos (by decide : 2 ≤ 2)).1 hrow
    have hmass : 1 - pushforwardMass M m ≤ 2 * dyadicWeight K := by
      have hlower : 1 - 2 * dyadicWeight K ≤ pushforwardMass M m := by
        exact pushforwardMass_ge_one_sub_two_mul_dyadicWeight hmpos hK
          ((plus_cutoff_iff hmpos hK).2 le_rfl)
      linarith
    have hnotNext : ¬ natDescendant (K + 1) BranchSign.plus m ≤ M := by
      intro hnext
      have : K + 1 ≤ plusCutoff M m :=
        (plus_cutoff_iff hmpos (show 2 ≤ K + 1 by omega)).1 hnext
      omega
    have hltNat : M - 1 < 2 ^ (K + 1) * m := by
      have hgt : M < natDescendant (K + 1) BranchSign.plus m := Nat.lt_of_not_ge hnotNext
      have hgt' : M < 2 ^ (K + 1) * m + 1 := by
        simpa [natDescendant] using hgt
      omega
    have hleReal : (M - 1 : Real) ≤ (2 : Real) ^ (K + 1) * m := by
      exact_mod_cast Nat.le_of_lt hltNat
    have hdyadic : 2 * dyadicWeight K ≤ (4 : Real) * m / (M - 1) := by
      have hpowPos : 0 < (2 : Real) ^ K := by positivity
      have hineq : 2 * (M - 1 : Real) ≤ 4 * m * (2 : Real) ^ K := by
        calc
          2 * (M - 1 : Real) ≤ 2 * ((2 : Real) ^ (K + 1) * m) := by gcongr
          _ = 4 * m * (2 : Real) ^ K := by
            rw [pow_succ]
            ring
      have hdiv : (2 : Real) / (2 : Real) ^ K ≤ (4 : Real) * m / (M - 1) := by
        rw [div_le_div_iff hpowPos hM1pos]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hineq
      calc
        2 * dyadicWeight K = (2 : Real) / (2 : Real) ^ K := by
          rw [dyadicWeight, one_div_pow]
          ring
        _ ≤ (4 : Real) * m / (M - 1) := hdiv
    exact hmass.trans hdyadic
  · have hltNat : M - 1 < 4 * m := by
      have hgt : M < natDescendant 2 BranchSign.plus m := Nat.lt_of_not_ge hrow
      have hgt' : M < 4 * m + 1 := by
        simpa [natDescendant] using hgt
      omega
    have hbase : (1 : Real) ≤ (4 : Real) * m / (M - 1) := by
      have hleReal : (M - 1 : Real) ≤ (4 : Real) * m := by
        exact_mod_cast Nat.le_of_lt hltNat
      rw [le_div_iff₀ hM1pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hleReal
    have hcoeff : 1 - pushforwardMass M m ≤ 1 := by
      linarith [pushforwardMass_nonneg M m]
    exact hcoeff.trans hbase

lemma oddPushforwardErrorTerm_le_linear {M : Nat} {sigma : Real} (hM : 2 ≤ M) (n : Nat) :
    oddPushforwardErrorTerm M sigma n ≤
      (4 : Real) / (M - 1) * ((oddCore n : Real) ^ (1 - sigma)) := by
  have hcorePos : 0 < (oddCore n : Real) := by positivity
  calc
    oddPushforwardErrorTerm M sigma n =
        (1 - pushforwardMass M (oddCore n)) * ((oddCore n : Real) ^ (-sigma)) := by
          rfl
    _ ≤ ((4 : Real) * (oddCore n : Real) / (M - 1)) * ((oddCore n : Real) ^ (-sigma)) := by
          gcongr
          exact pushforwardMassError_le_linear hM (odd_oddCore n)
    _ = (4 : Real) / (M - 1) * (((oddCore n : Real) ^ (1 - sigma))) := by
          rw [show ((oddCore n : Real) ^ (1 - sigma)) =
              ((oddCore n : Real) ^ (1 + -sigma)) by ring]
          rw [Real.rpow_add hcorePos]
          rw [Real.rpow_one]
          ring

lemma sub_one_rpow_one_sub_le {M : Nat} (hM : 2 ≤ M) {sigma : Real} (hs : 1 < sigma) :
    (M - 1 : Real) ^ (1 - sigma) ≤ (2 : Real) ^ (sigma - 1) * (M : Real) ^ (1 - sigma) := by
  have hM1pos : 0 < (M - 1 : Real) := by
    exact_mod_cast Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hM)
  have hhalf : (M : Real) / 2 ≤ (M - 1 : Real) := by
    have htwo : (2 : Real) ≤ M := by exact_mod_cast hM
    nlinarith
  have hpow : (M - 1 : Real) ^ (1 - sigma) ≤ ((M : Real) / 2) ^ (1 - sigma) := by
    have hneg : 1 - sigma < 0 := by linarith
    rw [Real.rpow_le_rpow_iff_of_neg hM1pos (by positivity : 0 < (M : Real) / 2) hneg]
    exact hhalf
  calc
    (M - 1 : Real) ^ (1 - sigma) ≤ ((M : Real) / 2) ^ (1 - sigma) := hpow
    _ = (2 : Real) ^ (sigma - 1) * (M : Real) ^ (1 - sigma) := by
          rw [Real.div_rpow (by positivity : 0 ≤ (M : Real)) (by positivity : 0 ≤ (2 : Real))]
          rw [div_eq_mul_inv, mul_comm]
          congr 1
          rw [← Real.rpow_neg (by positivity : 0 ≤ (2 : Real))]
          congr 1
          ring

theorem abs_ZOddReal_sub_AMReal_le_subcritical {M : Nat} (hM : 2 ≤ M)
    {sigma : Real} (hs1 : 1 < sigma) (hs2 : sigma < 2) :
    |ZOddReal sigma - AMReal M sigma| ≤
      subcriticalBoundConst sigma * (M : Real) ^ (1 - sigma) := by
  let K : Nat := (M - 1) / 4
  have hnonneg : 0 ≤ ZOddReal sigma - AMReal M sigma :=
    ZOddReal_sub_AMReal_nonneg M sigma hs1
  have hM1pos : 0 < (M - 1 : Real) := by
    exact_mod_cast Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hM)
  have hKle : (K : Real) ≤ (M - 1 : Real) / 4 := by
    exact_mod_cast Nat.div_le_self (M - 1) 4
  have hKpow : (K : Real) ^ (2 - sigma) ≤ ((M - 1 : Real) / 4) ^ (2 - sigma) := by
    exact Real.rpow_le_rpow (by positivity) hKle (by linarith)
  have hKlowerNat : M - 1 < 4 * (K + 1) := by
    have hmod := Nat.mod_lt (M - 1) (by decide : 0 < 4)
    omega [Nat.div_add_mod (M - 1) 4]
  have hKlower : ((M - 1 : Real) / 4) < K + 1 := by
    have hlt : (M - 1 : Real) < 4 * (K + 1) := by exact_mod_cast hKlowerNat
    rw [div_lt_iff (by norm_num : (0 : Real) < 4)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlt
  have htailPow : ((K + 1 : Real) ^ (1 - sigma)) ≤ ((M - 1 : Real) / 4) ^ (1 - sigma) := by
    have hneg : 1 - sigma < 0 := by linarith
    rw [Real.rpow_le_rpow_iff_of_neg (by positivity : 0 < (K + 1 : Real))
      (by positivity : 0 < (M - 1 : Real) / 4) hneg]
    exact le_of_lt hKlower
  rw [abs_of_nonneg hnonneg, ZOddReal_sub_AMReal_eq_inside_add_tail M sigma hs1 K]
  have hinside :
      ∑ n ∈ Finset.range K, oddPushforwardErrorTerm M sigma n ≤
        (4 : Real) / (M - 1) * (1 + (K : Real) ^ (2 - sigma) / (2 - sigma)) := by
    calc
      ∑ n ∈ Finset.range K, oddPushforwardErrorTerm M sigma n
        ≤ ∑ n ∈ Finset.range K,
            (4 : Real) / (M - 1) * ((oddCore n : Real) ^ (1 - sigma)) := by
              apply Finset.sum_le_sum
              intro n hn
              exact oddPushforwardErrorTerm_le_linear hM n
      _ ≤ ∑ n ∈ Finset.range K, (4 : Real) / (M - 1) * ((n + 1 : Real) ^ (1 - sigma)) := by
              apply Finset.sum_le_sum
              intro n hn
              have hfac : 0 ≤ (4 : Real) / (M - 1) := by positivity
              gcongr
              exact oddCore_rpow_one_sub_le_natSucc_rpow_one_sub hs1 n
      _ = (4 : Real) / (M - 1) * ∑ n ∈ Finset.range K, ((n + 1 : Real) ^ (1 - sigma)) := by
            rw [← Finset.mul_sum]
      _ ≤ (4 : Real) / (M - 1) * (1 + (K : Real) ^ (2 - sigma) / (2 - sigma)) := by
            gcongr
            exact sum_range_natSucc_rpow_one_sub_le hs1 hs2 K
  have htail :
      ∑' n : Nat, oddPushforwardErrorTerm M sigma (n + K) ≤
        sigma / (sigma - 1) * ((K + 1 : Real) ^ (1 - sigma)) := by
    refine (summable_oddPushforwardErrorTerm M sigma hs1).tsum_le_tsum ?_
      (summable_shift_natSucc_rpow_neg hs1 K)
    intro n
    calc
      oddPushforwardErrorTerm M sigma (n + K)
        ≤ ((oddCore (n + K) : Real) ^ (-sigma)) :=
          oddPushforwardErrorTerm_le_oddCoreTerm M sigma (n + K)
      _ ≤ ((n + K + 1 : Real) ^ (-sigma)) :=
          oddCore_rpow_neg_le_natSucc_rpow_neg (by linarith) (n + K)
  have hfirstTerm :
      (4 : Real) / (M - 1) ≤ 4 * (M - 1 : Real) ^ (1 - sigma) := by
    have hM1ge1 : 1 ≤ M - 1 := by omega
    have hpow : (M - 1 : Real) ^ (-1) ≤ (M - 1 : Real) ^ (1 - sigma) := by
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hM1ge1) (by linarith)
    calc
      (4 : Real) / (M - 1) = 4 * (M - 1 : Real) ^ (-1) := by
        rw [Real.rpow_neg (by positivity : 0 ≤ (M - 1 : Real)), Real.rpow_one]
        ring
      _ ≤ 4 * (M - 1 : Real) ^ (1 - sigma) := by gcongr
  have hsecondTerm :
      (4 : Real) / (M - 1) * ((((M - 1 : Real) / 4) ^ (2 - sigma)) / (2 - sigma)) =
        ((4 : Real) ^ (sigma - 1) / (2 - sigma)) * (M - 1 : Real) ^ (1 - sigma) := by
    have hquarterPos : 0 < ((M - 1 : Real) / 4) := by positivity
    calc
      (4 : Real) / (M - 1) * ((((M - 1 : Real) / 4) ^ (2 - sigma)) / (2 - sigma)) =
          ((4 : Real) / (M - 1) * (((M - 1 : Real) / 4) ^ (2 - sigma))) / (2 - sigma) := by ring
      _ = ((((M - 1 : Real) / 4) ^ (1 - sigma))) / (2 - sigma) := by
          rw [show (((M - 1 : Real) / 4) ^ (2 - sigma)) =
              ((M - 1 : Real) / 4) * (((M - 1 : Real) / 4) ^ (1 - sigma)) by
                rw [show 2 - sigma = 1 + (1 - sigma) by ring, Real.rpow_add hquarterPos]
                ring]
          have hcancel : (4 : Real) / (M - 1) * ((M - 1 : Real) / 4) = 1 := by
            field_simp [hM1pos.ne']
          rw [mul_assoc, hcancel, one_mul]
      _ = ((4 : Real) ^ (sigma - 1) * (M - 1 : Real) ^ (1 - sigma)) / (2 - sigma) := by
          rw [quarter_scale_rpow M sigma]
      _ = ((4 : Real) ^ (sigma - 1) / (2 - sigma)) * (M - 1 : Real) ^ (1 - sigma) := by ring
  have hinsideBound :
      ∑ n ∈ Finset.range K, oddPushforwardErrorTerm M sigma n ≤
        (4 + (4 : Real) ^ (sigma - 1) / (2 - sigma)) * (M - 1 : Real) ^ (1 - sigma) := by
    have hmid :
        (4 : Real) / (M - 1) * (1 + (K : Real) ^ (2 - sigma) / (2 - sigma)) ≤
          (4 : Real) / (M - 1) +
            (4 : Real) / (M - 1) * ((((M - 1 : Real) / 4) ^ (2 - sigma)) / (2 - sigma)) := by
      calc
        (4 : Real) / (M - 1) * (1 + (K : Real) ^ (2 - sigma) / (2 - sigma)) =
            (4 : Real) / (M - 1) +
              (4 : Real) / (M - 1) * ((K : Real) ^ (2 - sigma) / (2 - sigma)) := by ring
        _ ≤ (4 : Real) / (M - 1) +
              (4 : Real) / (M - 1) * ((((M - 1 : Real) / 4) ^ (2 - sigma)) / (2 - sigma)) := by
              gcongr
              · exact hKpow
              · positivity
    calc
      ∑ n ∈ Finset.range K, oddPushforwardErrorTerm M sigma n
        ≤ (4 : Real) / (M - 1) * (1 + (K : Real) ^ (2 - sigma) / (2 - sigma)) := hinside
      _ ≤ (4 : Real) / (M - 1) +
            (4 : Real) / (M - 1) * ((((M - 1 : Real) / 4) ^ (2 - sigma)) / (2 - sigma)) := hmid
      _ ≤ 4 * (M - 1 : Real) ^ (1 - sigma) +
            (((4 : Real) ^ (sigma - 1) / (2 - sigma)) * (M - 1 : Real) ^ (1 - sigma)) := by
              rw [hsecondTerm]
              gcongr
      _ = (4 + (4 : Real) ^ (sigma - 1) / (2 - sigma)) * (M - 1 : Real) ^ (1 - sigma) := by
            ring
  have htailBound :
      ∑' n : Nat, oddPushforwardErrorTerm M sigma (n + K) ≤
        (sigma / (sigma - 1) * (4 : Real) ^ (sigma - 1)) * (M - 1 : Real) ^ (1 - sigma) := by
    calc
      ∑' n : Nat, oddPushforwardErrorTerm M sigma (n + K)
        ≤ sigma / (sigma - 1) * ((K + 1 : Real) ^ (1 - sigma)) := htail
      _ ≤ sigma / (sigma - 1) * (((M - 1 : Real) / 4) ^ (1 - sigma)) := by
            gcongr
      _ = (sigma / (sigma - 1) * (4 : Real) ^ (sigma - 1)) * (M - 1 : Real) ^ (1 - sigma) := by
            rw [quarter_scale_rpow M sigma]
            ring
  have hmain :
      ZOddReal sigma - AMReal M sigma ≤
        (4 + (4 : Real) ^ (sigma - 1) / (2 - sigma) +
          sigma / (sigma - 1) * (4 : Real) ^ (sigma - 1)) * (M - 1 : Real) ^ (1 - sigma) := by
    linarith [hinsideBound, htailBound]
  calc
    ZOddReal sigma - AMReal M sigma
      ≤ (4 + (4 : Real) ^ (sigma - 1) / (2 - sigma) +
          sigma / (sigma - 1) * (4 : Real) ^ (sigma - 1)) * (M - 1 : Real) ^ (1 - sigma) := hmain
    _ ≤ (4 + (4 : Real) ^ (sigma - 1) / (2 - sigma) +
          sigma / (sigma - 1) * (4 : Real) ^ (sigma - 1)) *
          ((2 : Real) ^ (sigma - 1) * (M : Real) ^ (1 - sigma)) := by
            gcongr
            · positivity
            · exact sub_one_rpow_one_sub_le hM hs1
    _ = subcriticalBoundConst sigma * (M : Real) ^ (1 - sigma) := by
          rw [subcriticalBoundConst]
          ring

theorem abs_ZOddReal_sub_AMReal_le_critical {M : Nat} (hM : 2 ≤ M) :
    |ZOddReal 2 - AMReal M 2| ≤ ((24 : Real) + 8 * Real.log M) / M := by
  let K : Nat := (M - 1) / 4
  have hnonneg : 0 ≤ ZOddReal 2 - AMReal M 2 :=
    ZOddReal_sub_AMReal_nonneg M 2 (by norm_num)
  have hM1pos : 0 < (M - 1 : Real) := by
    exact_mod_cast Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hM)
  have hMpos : 0 < (M : Real) := by positivity
  have hfrac : (4 : Real) / (M - 1) ≤ 8 / M := by
    rw [div_le_div_iff hM1pos hMpos]
    have htwo : (2 : Real) ≤ M := by exact_mod_cast hM
    nlinarith
  have hKleNat : K ≤ M - 1 := by
    exact Nat.div_le_self (M - 1) 4
  have hK1leM : (K + 1 : Real) ≤ M := by
    exact_mod_cast (by omega : K + 1 ≤ M)
  rw [abs_of_nonneg hnonneg, ZOddReal_sub_AMReal_eq_inside_add_tail M 2 (by norm_num) K]
  have hinside :
      ∑ n ∈ Finset.range K, oddPushforwardErrorTerm M 2 n ≤
        (4 : Real) / (M - 1) * (1 + Real.log M) := by
    calc
      ∑ n ∈ Finset.range K, oddPushforwardErrorTerm M 2 n
        ≤ ∑ n ∈ Finset.range K, (4 : Real) / (M - 1) * ((oddCore n : Real) ^ (1 - (2 : Real))) := by
              apply Finset.sum_le_sum
              intro n hn
              exact oddPushforwardErrorTerm_le_linear hM n
      _ ≤ ∑ n ∈ Finset.range K, (4 : Real) / (M - 1) * ((n + 1 : Real) ^ (1 - (2 : Real))) := by
              apply Finset.sum_le_sum
              intro n hn
              gcongr
              exact oddCore_rpow_one_sub_le_natSucc_rpow_one_sub (by norm_num : 1 < (2 : Real)) n
      _ = (4 : Real) / (M - 1) * ∑ n ∈ Finset.range K, ((n + 1 : Real)⁻¹) := by
            rw [← Finset.mul_sum]
            simp
      _ ≤ (4 : Real) / (M - 1) * (1 + Real.log (K + 1)) := by
            gcongr
            exact sum_range_natSucc_inv_le_one_add_log K
      _ ≤ (4 : Real) / (M - 1) * (1 + Real.log M) := by
            gcongr
            exact Real.log_le_log (by positivity) hK1leM
  have htail :
      ∑' n : Nat, oddPushforwardErrorTerm M 2 (n + K) ≤ 2 * ((K + 1 : Real) ^ (1 - (2 : Real))) := by
    refine (summable_oddPushforwardErrorTerm M 2 (by norm_num)).tsum_le_tsum ?_
      (summable_shift_natSucc_rpow_neg (by norm_num : 1 < (2 : Real)) K)
    intro n
    calc
      oddPushforwardErrorTerm M 2 (n + K)
        ≤ ((oddCore (n + K) : Real) ^ (-(2 : Real))) :=
          oddPushforwardErrorTerm_le_oddCoreTerm M 2 (n + K)
      _ ≤ ((n + K + 1 : Real) ^ (-(2 : Real))) :=
          oddCore_rpow_neg_le_natSucc_rpow_neg (by norm_num : 0 < (2 : Real)) (n + K)
  have htail' :
      ∑' n : Nat, oddPushforwardErrorTerm M 2 (n + K) ≤ 2 * ((K + 1 : Real) ^ (1 - (2 : Real))) := by
    calc
      ∑' n : Nat, oddPushforwardErrorTerm M 2 (n + K)
        ≤ ∑' n : Nat, ((n + K + 1 : Real) ^ (-(2 : Real))) := by
              exact (summable_oddPushforwardErrorTerm M 2 (by norm_num)).tsum_le_tsum
                (fun n => by
                  calc
                    oddPushforwardErrorTerm M 2 (n + K)
                      ≤ ((oddCore (n + K) : Real) ^ (-(2 : Real))) :=
                        oddPushforwardErrorTerm_le_oddCoreTerm M 2 (n + K)
                    _ ≤ ((n + K + 1 : Real) ^ (-(2 : Real))) :=
                        oddCore_rpow_neg_le_natSucc_rpow_neg (by norm_num : 0 < (2 : Real)) (n + K))
                (summable_shift_natSucc_rpow_neg (by norm_num : 1 < (2 : Real)) K)
      _ ≤ 2 * ((K + 1 : Real) ^ (1 - (2 : Real))) :=
            tsum_shift_natSucc_rpow_neg_le (sigma := 2) (by norm_num : 1 < (2 : Real)) K
  have hKlowerNat : M - 1 < 4 * (K + 1) := by
    have hmod := Nat.mod_lt (M - 1) (by decide : 0 < 4)
    omega [Nat.div_add_mod (M - 1) 4]
  have hKlower : ((M - 1 : Real) / 4) < K + 1 := by
    have hlt : (M - 1 : Real) < 4 * (K + 1) := by exact_mod_cast hKlowerNat
    rw [div_lt_iff (by norm_num : (0 : Real) < 4)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlt
  have htailBound :
      ∑' n : Nat, oddPushforwardErrorTerm M 2 (n + K) ≤ 8 / (M - 1) := by
    calc
      ∑' n : Nat, oddPushforwardErrorTerm M 2 (n + K)
        ≤ 2 * ((K + 1 : Real) ^ (1 - (2 : Real))) := htail'
      _ = 2 / (K + 1) := by
            rw [show (1 - (2 : Real)) = -1 by norm_num]
            rw [Real.rpow_neg (by positivity : 0 ≤ (K + 1 : Real)), Real.rpow_one]
            ring
      _ ≤ 8 / (M - 1) := by
            rw [div_le_div_iff (by positivity : 0 < (K + 1 : Real)) hM1pos]
            nlinarith
  have hlogNonneg : 0 ≤ 1 + Real.log M := by
    have hMge1 : (1 : Real) ≤ M := by exact_mod_cast (Nat.one_le_of_lt (lt_of_lt_of_le (by decide : 0 < 2) hM))
    exact add_nonneg zero_le_one (Real.log_nonneg hMge1)
  calc
    ZOddReal 2 - AMReal M 2
      ≤ (4 : Real) / (M - 1) * (1 + Real.log M) + 8 / (M - 1) := by
          linarith [hinside, htailBound]
    _ ≤ (8 : Real) / M * (1 + Real.log M) + 16 / M := by
          have hfrac8 : (8 : Real) / (M - 1) ≤ 16 / M := by
            nlinarith [hfrac]
          nlinarith [hfrac, hfrac8, hlogNonneg]
    _ = ((24 : Real) + 8 * Real.log M) / M := by
          ring

theorem abs_ZOddReal_sub_AMReal_le_supercritical {M : Nat} (hM : 2 ≤ M)
    {sigma : Real} (hs : 2 < sigma) :
    |ZOddReal sigma - AMReal M sigma| ≤ supercriticalBoundConst sigma / M := by
  have hs1 : 1 < sigma := by linarith
  have hnonneg : 0 ≤ ZOddReal sigma - AMReal M sigma :=
    ZOddReal_sub_AMReal_nonneg M sigma hs1
  have hM1pos : 0 < (M - 1 : Real) := by
    exact_mod_cast Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hM)
  have hMpos : 0 < (M : Real) := by positivity
  rw [abs_of_nonneg hnonneg, ZOddReal_sub_AMReal_eq_tsum_error M sigma hs1]
  have hupperSummable : Summable (fun n : Nat => (4 : Real) / (M - 1) * ((n + 1 : Real) ^ (1 - sigma))) := by
    simpa using ((summable_nat_add_iff 1).2 (Real.summable_nat_rpow.mpr (by linarith : 1 - sigma < -1))).mul_left ((4 : Real) / (M - 1))
  have hcompare :
      ∑' n : Nat, oddPushforwardErrorTerm M sigma n ≤
        ∑' n : Nat, (4 : Real) / (M - 1) * ((n + 1 : Real) ^ (1 - sigma)) := by
    refine (summable_oddPushforwardErrorTerm M sigma hs1).tsum_le_tsum ?_ hupperSummable
    intro n
    calc
      oddPushforwardErrorTerm M sigma n
        ≤ (4 : Real) / (M - 1) * ((oddCore n : Real) ^ (1 - sigma)) :=
          oddPushforwardErrorTerm_le_linear hM n
      _ ≤ (4 : Real) / (M - 1) * ((n + 1 : Real) ^ (1 - sigma)) := by
            gcongr
            exact oddCore_rpow_one_sub_le_natSucc_rpow_one_sub hs1 n
  have htsum :
      ∑' n : Nat, ((n + 1 : Real) ^ (1 - sigma)) ≤ (sigma - 1) / (sigma - 2) := by
    simpa using
      (tsum_shift_natSucc_rpow_neg_le (sigma := sigma - 1) (by linarith : 1 < sigma - 1) 0)
  have hfrac : (4 : Real) / (M - 1) ≤ 8 / M := by
    rw [div_le_div_iff hM1pos hMpos]
    have htwo : (2 : Real) ≤ M := by exact_mod_cast hM
    nlinarith
  calc
    ZOddReal sigma - AMReal M sigma
      ≤ ∑' n : Nat, (4 : Real) / (M - 1) * ((n + 1 : Real) ^ (1 - sigma)) := hcompare
    _ = (4 : Real) / (M - 1) * ∑' n : Nat, ((n + 1 : Real) ^ (1 - sigma)) := by
          rw [tsum_mul_left]
    _ ≤ (4 : Real) / (M - 1) * ((sigma - 1) / (sigma - 2)) := by
          gcongr
    _ ≤ (8 : Real) / M * ((sigma - 1) / (sigma - 2)) := by
          gcongr
          · exact hfrac
          · positivity
    _ = supercriticalBoundConst sigma / M := by
          rw [supercriticalBoundConst]
          ring

end LeanC2
