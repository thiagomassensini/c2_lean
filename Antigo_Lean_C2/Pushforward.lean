import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import LeanC2.Tree

namespace LeanC2

open scoped BigOperators LSeries.notation

set_option linter.style.setOption false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- Dyadic depth weight `2^{-k}` used in the odd pushforward. -/
noncomputable def dyadicWeight (k : ℕ) : ℝ := ((1 : ℝ) / 2) ^ k

lemma dyadicWeight_succ (k : ℕ) :
    dyadicWeight (k + 1) = dyadicWeight k / 2 := by
  simp [dyadicWeight, pow_succ, div_eq_mul_inv]

/-- Lower dyadic cutoff for the `2^k m - 1` branch. -/
def minusCutoff (M m : ℕ) : ℕ := Nat.log2 ((M + 1) / m)

/-- Upper dyadic cutoff for the `2^k m + 1` branch. -/
def plusCutoff (M m : ℕ) : ℕ := Nat.log2 ((M - 1) / m)

/-- Exact arithmetic pushforward mass `a_M(m)` of the odd fiber over `m`. -/
noncomputable def pushforwardMass (M m : ℕ) : ℝ :=
  Finset.sum (Finset.Icc 2 (minusCutoff M m)) dyadicWeight +
    Finset.sum (Finset.Icc 2 (plusCutoff M m)) dyadicWeight

/-- Addresses on the `2^k m - 1` branch that survive the cutoff. -/
def minusAddresses (M m : ℕ) : Finset (ℕ × BranchSign) :=
  (Finset.Icc 2 (minusCutoff M m)).image fun k => (k, BranchSign.minus)

/-- Addresses on the `2^k m + 1` branch that survive the cutoff. -/
def plusAddresses (M m : ℕ) : Finset (ℕ × BranchSign) :=
  (Finset.Icc 2 (plusCutoff M m)).image fun k => (k, BranchSign.plus)

lemma natDescendant_minus_add_one {k m : ℕ} (hm : 0 < m) :
    natDescendant k BranchSign.minus m + 1 = 2 ^ k * m := by
  have hpow : 0 < 2 ^ k := by positivity
  have hpos : 0 < 2 ^ k * m := Nat.mul_pos hpow hm
  simpa [natDescendant, Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hpos

lemma depth_lt_cutoff_of_rowBound {M m k : ℕ} {ε : BranchSign} (hm : 0 < m)
    (hcut : natDescendant k ε m ≤ M) :
    k < M + 1 := by
  have hm1 : 1 ≤ m := Nat.succ_le_of_lt hm
  cases ε with
  | minus =>
      have hmul : 2 ^ k * m ≤ M + 1 := by
        have hcut' := Nat.add_le_add_right hcut 1
        simpa [natDescendant_minus_add_one hm] using hcut'
      have hpow : 2 ^ k ≤ M + 1 := by
        calc
          2 ^ k = 2 ^ k * 1 := by simp
          _ ≤ 2 ^ k * m := by simpa using Nat.mul_le_mul_left (2 ^ k) hm1
          _ ≤ M + 1 := hmul
      exact lt_of_lt_of_le Nat.lt_two_pow_self hpow
  | plus =>
      have hcut' : 2 ^ k * m + 1 ≤ M := by
        simpa [natDescendant] using hcut
      have hlt : 2 ^ k * m < M := Nat.lt_of_succ_le hcut'
      have hmul : 2 ^ k * m ≤ M - 1 := Nat.le_pred_of_lt hlt
      have hpow : 2 ^ k ≤ M := by
        calc
          2 ^ k = 2 ^ k * 1 := by simp
          _ ≤ 2 ^ k * m := by simpa using Nat.mul_le_mul_left (2 ^ k) hm1
          _ ≤ M - 1 := hmul
          _ ≤ M := Nat.sub_le _ _
      exact lt_of_lt_of_le Nat.lt_two_pow_self (Nat.le_succ_of_le hpow)

lemma minus_cutoff_iff {M m k : ℕ} (hm : 0 < m) (hk : 2 ≤ k) :
    natDescendant k BranchSign.minus m ≤ M ↔ k ≤ minusCutoff M m := by
  constructor
  · intro hcut
    have hmul : 2 ^ k * m ≤ M + 1 := by
      have hcut' := Nat.add_le_add_right hcut 1
      simpa [natDescendant_minus_add_one hm] using hcut'
    have hdiv : 2 ^ k ≤ (M + 1) / m :=
      (Nat.le_div_iff_mul_le hm).2 hmul
    have hlog : k ≤ Nat.log 2 ((M + 1) / m) :=
      Nat.le_log_of_pow_le Nat.one_lt_two hdiv
    simpa [minusCutoff, Nat.log2_eq_log_two] using hlog
  · intro hcut
    have hlog : k ≤ Nat.log 2 ((M + 1) / m) := by
      simpa [minusCutoff, Nat.log2_eq_log_two] using hcut
    have hquot_ne : (M + 1) / m ≠ 0 := by
      intro hzero
      have : k ≤ 0 := by simpa [hzero] using hlog
      omega
    have hdiv : 2 ^ k ≤ (M + 1) / m :=
      Nat.pow_le_of_le_log hquot_ne hlog
    have hmul : 2 ^ k * m ≤ M + 1 :=
      (Nat.le_div_iff_mul_le hm).1 hdiv
    have hcut' : natDescendant k BranchSign.minus m + 1 ≤ M + 1 := by
      simpa [natDescendant_minus_add_one hm] using hmul
    omega

lemma plus_cutoff_iff {M m k : ℕ} (hm : 0 < m) (hk : 2 ≤ k) :
    natDescendant k BranchSign.plus m ≤ M ↔ k ≤ plusCutoff M m := by
  constructor
  · intro hcut
    have hcut' : 2 ^ k * m + 1 ≤ M := by
      simpa [natDescendant] using hcut
    have hlt : 2 ^ k * m < M := Nat.lt_of_succ_le hcut'
    have hmul : 2 ^ k * m ≤ M - 1 := Nat.le_pred_of_lt hlt
    have hdiv : 2 ^ k ≤ (M - 1) / m :=
      (Nat.le_div_iff_mul_le hm).2 hmul
    have hlog : k ≤ Nat.log 2 ((M - 1) / m) :=
      Nat.le_log_of_pow_le Nat.one_lt_two hdiv
    simpa [plusCutoff, Nat.log2_eq_log_two] using hlog
  · intro hcut
    have hlog : k ≤ Nat.log 2 ((M - 1) / m) := by
      simpa [plusCutoff, Nat.log2_eq_log_two] using hcut
    have hquot_ne : (M - 1) / m ≠ 0 := by
      intro hzero
      have : k ≤ 0 := by simpa [hzero] using hlog
      omega
    have hdiv : 2 ^ k ≤ (M - 1) / m :=
      Nat.pow_le_of_le_log hquot_ne hlog
    have hmul : 2 ^ k * m ≤ M - 1 :=
      (Nat.le_div_iff_mul_le hm).1 hdiv
    have hM : 1 ≤ M := by
      have hpos : 1 ≤ 2 ^ k * m := by
        have hpow : 0 < 2 ^ k := by positivity
        exact Nat.succ_le_of_lt (Nat.mul_pos hpow hm)
      exact le_trans hpos (le_trans hmul (Nat.sub_le _ _))
    have hcut' : 2 ^ k * m + 1 ≤ M := by
      calc
        2 ^ k * m + 1 ≤ (M - 1) + 1 := Nat.add_le_add_right hmul 1
        _ = M := Nat.sub_add_cancel hM
    simpa [natDescendant] using hcut'

lemma minus_mem_rowSupport_iff {M m k : ℕ} (hm : 0 < m) :
    (k, BranchSign.minus) ∈ rowSupport M m ↔ k ∈ Finset.Icc 2 (minusCutoff M m) := by
  constructor
  · intro hk
    rcases mem_rowSupport_iff.mp hk with ⟨_, hk2, hcut⟩
    exact Finset.mem_Icc.mpr ⟨hk2, (minus_cutoff_iff hm hk2).1 hcut⟩
  · intro hk
    rcases Finset.mem_Icc.mp hk with ⟨hk2, hcut⟩
    have hrow : natDescendant k BranchSign.minus m ≤ M := (minus_cutoff_iff hm hk2).2 hcut
    exact mem_rowSupport_iff.mpr ⟨depth_lt_cutoff_of_rowBound hm hrow, hk2, hrow⟩

lemma plus_mem_rowSupport_iff {M m k : ℕ} (hm : 0 < m) :
    (k, BranchSign.plus) ∈ rowSupport M m ↔ k ∈ Finset.Icc 2 (plusCutoff M m) := by
  constructor
  · intro hk
    rcases mem_rowSupport_iff.mp hk with ⟨_, hk2, hcut⟩
    exact Finset.mem_Icc.mpr ⟨hk2, (plus_cutoff_iff hm hk2).1 hcut⟩
  · intro hk
    rcases Finset.mem_Icc.mp hk with ⟨hk2, hcut⟩
    have hrow : natDescendant k BranchSign.plus m ≤ M := (plus_cutoff_iff hm hk2).2 hcut
    exact mem_rowSupport_iff.mpr ⟨depth_lt_cutoff_of_rowBound hm hrow, hk2, hrow⟩

lemma sum_dyadicWeight_Icc {K : ℕ} (hK : 1 ≤ K) :
    (Finset.Icc 2 K).sum dyadicWeight = 1 / 2 - dyadicWeight K := by
  rcases Nat.exists_eq_add_of_le hK with ⟨n, rfl⟩
  induction n with
  | zero =>
      simp [dyadicWeight]
  | succ n ih =>
      have htop : 2 ≤ (n + 1) + 1 := by omega
      have ih' : (Finset.Icc 2 (n + 1)).sum dyadicWeight = 1 / 2 - dyadicWeight (n + 1) := by
        simpa [Nat.add_comm] using ih (by omega)
      rw [show 1 + (n + 1) = (n + 1) + 1 by omega]
      rw [Finset.sum_Icc_succ_top htop]
      rw [ih']
      rw [show n + 2 = (n + 1) + 1 by omega, dyadicWeight_succ (k := n + 1)]
      rw [dyadicWeight_succ (k := n)]
      ring

theorem pushforwardMass_eq_one_sub_two_mul_dyadicWeight {M m K : ℕ}
    (hminus : minusCutoff M m = K) (hplus : plusCutoff M m = K) (hK : 1 ≤ K) :
    pushforwardMass M m = 1 - 2 * dyadicWeight K := by
  rw [pushforwardMass, hminus, hplus]
  simp_rw [sum_dyadicWeight_Icc hK]
  ring

theorem pushforwardMass_dyadic_extrapolation {M m : ℕ} (hm : Odd m) (hmem : m ≤ M) :
    2 * pushforwardMass (8 * M) m - pushforwardMass (4 * M) m = 1 := by
  have hm1 : 1 ≤ m := one_le_of_nat_odd hm
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 1) hm1
  have hminus2 : 2 ≤ minusCutoff (4 * M) m := by
    have hrow : natDescendant 2 BranchSign.minus m ≤ 4 * M := by
      simp [natDescendant]
      omega
    exact (minus_cutoff_iff hmpos (by decide : 2 ≤ 2)).1 hrow
  have hplus1 : 1 ≤ plusCutoff (4 * M) m := by
    have hdiv : 2 ≤ (4 * M - 1) / m := by
      refine (Nat.le_div_iff_mul_le hmpos).2 ?_
      omega
    have hpow1 : 2 ^ 1 ≤ (4 * M - 1) / m := by simpa using hdiv
    have hlog : 1 ≤ Nat.log 2 ((4 * M - 1) / m) := Nat.le_log_of_pow_le Nat.one_lt_two hpow1
    simpa [plusCutoff, Nat.log2_eq_log_two] using hlog
  have hminus_eq : minusCutoff (8 * M) m = minusCutoff (4 * M) m + 1 := by
    let K := minusCutoff (4 * M) m
    have hK2 : 2 ≤ K := by simpa [K] using hminus2
    have hKrow : natDescendant K BranchSign.minus m ≤ 4 * M := by
      exact (minus_cutoff_iff hmpos hK2).2 le_rfl
    have hEvenPow : Even (2 ^ K * m) := by
      rcases Nat.exists_eq_add_of_le (show 1 ≤ K by omega) with ⟨t, hK⟩
      rw [hK]
      refine ⟨2 ^ t * m, ?_⟩
      calc
        2 ^ (1 + t) * m = ((2 ^ 1) * 2 ^ t) * m := by rw [pow_add]
        _ = 2 * (2 ^ t * m) := by rw [pow_one, Nat.mul_assoc]
        _ = 2 ^ t * m + 2 ^ t * m := by omega
    have hPowLe : 2 ^ K * m ≤ 4 * M := by
      have hPowLe' : 2 ^ K * m ≤ 4 * M + 1 := by
        simpa [natDescendant] using Nat.add_le_add_right hKrow 1
      have hneq : 2 ^ K * m ≠ 4 * M + 1 := by
        intro hEq
        have hnotEven : ¬ Even (4 * M + 1) := by
          rintro ⟨u, hu⟩
          omega
        exact hnotEven (hEq ▸ hEvenPow)
      by_contra hgt
      have hge : 4 * M + 1 ≤ 2 ^ K * m := by omega
      exact hneq (le_antisymm hPowLe' hge)
    have hlowerRow : natDescendant (K + 1) BranchSign.minus m ≤ 8 * M := by
      have hcalc : natDescendant (K + 1) BranchSign.minus m = 2 * (2 ^ K * m) - 1 := by
        simp [natDescendant, pow_succ', Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      rw [hcalc]
      omega
    have hlower : K + 1 ≤ minusCutoff (8 * M) m := by
      exact (minus_cutoff_iff hmpos (show 2 ≤ K + 1 by omega)).1 hlowerRow
    have hupper : minusCutoff (8 * M) m ≤ K + 1 := by
      by_contra hcontra
      have hbig : K + 2 ≤ minusCutoff (8 * M) m := by omega
      have hrow : natDescendant (K + 2) BranchSign.minus m ≤ 8 * M := by
        exact (minus_cutoff_iff hmpos (show 2 ≤ K + 2 by omega)).2 hbig
      have hprevRow : natDescendant (K + 1) BranchSign.minus m ≤ 4 * M := by
        have hcalc : natDescendant (K + 2) BranchSign.minus m =
            2 * natDescendant (K + 1) BranchSign.minus m + 1 := by
          have hpos' : 0 < 2 ^ (K + 1) * m := Nat.mul_pos (pow_pos (by decide) _) hmpos
          calc
            natDescendant (K + 2) BranchSign.minus m = 2 ^ (K + 2) * m - 1 := by
              simp [natDescendant]
            _ = 2 * (2 ^ (K + 1) * m) - 1 := by
              simp [pow_succ', Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
            _ = 2 * (2 ^ (K + 1) * m - 1) + 1 := by omega
            _ = 2 * natDescendant (K + 1) BranchSign.minus m + 1 := by
              simp [natDescendant]
        rw [hcalc] at hrow
        have hprevRow_lt : natDescendant (K + 1) BranchSign.minus m < 4 * M := by
          omega
        exact Nat.le_of_lt hprevRow_lt
      have : K + 1 ≤ minusCutoff (4 * M) m := by
        exact (minus_cutoff_iff hmpos (show 2 ≤ K + 1 by omega)).1 hprevRow
      omega
    simpa [K] using Nat.le_antisymm hupper hlower
  have hplus_eq : plusCutoff (8 * M) m = plusCutoff (4 * M) m + 1 := by
    let K := plusCutoff (4 * M) m
    have hK1 : 1 ≤ K := by simpa [K] using hplus1
    have hquot_ne : (4 * M - 1) / m ≠ 0 := by
      intro hzero
      have : K = 0 := by simpa [K, plusCutoff, Nat.log2_eq_log_two, hzero]
      omega
    have hpow : 2 ^ K ≤ (4 * M - 1) / m := by
      exact Nat.pow_le_of_le_log hquot_ne (by simpa [K, plusCutoff, Nat.log2_eq_log_two] using le_rfl)
    have hpowMul : 2 ^ K * m ≤ 4 * M - 1 := by
      exact (Nat.le_div_iff_mul_le hmpos).1 hpow
    have hlowerRow : natDescendant (K + 1) BranchSign.plus m ≤ 8 * M := by
      have hcalc : natDescendant (K + 1) BranchSign.plus m = 2 * (2 ^ K * m) + 1 := by
        simp [natDescendant, pow_succ', Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      rw [hcalc]
      omega
    have hlower : K + 1 ≤ plusCutoff (8 * M) m := by
      exact (plus_cutoff_iff hmpos (show 2 ≤ K + 1 by omega)).1 hlowerRow
    have hupper : plusCutoff (8 * M) m ≤ K + 1 := by
      by_contra hcontra
      have hbig : K + 2 ≤ plusCutoff (8 * M) m := by omega
      have hrow : natDescendant (K + 2) BranchSign.plus m ≤ 8 * M := by
        exact (plus_cutoff_iff hmpos (show 2 ≤ K + 2 by omega)).2 hbig
      have hprevRow : natDescendant (K + 1) BranchSign.plus m ≤ 4 * M := by
        have hcalc : natDescendant (K + 2) BranchSign.plus m =
            2 * natDescendant (K + 1) BranchSign.plus m - 1 := by
          calc
            natDescendant (K + 2) BranchSign.plus m = 2 ^ (K + 2) * m + 1 := by
              simp [natDescendant]
            _ = 2 * (2 ^ (K + 1) * m) + 1 := by
              simp [pow_succ', Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
            _ = 2 * (2 ^ (K + 1) * m + 1) - 1 := by omega
            _ = 2 * natDescendant (K + 1) BranchSign.plus m - 1 := by
              simp [natDescendant]
        rw [hcalc] at hrow
        have hprevRow_lt : natDescendant (K + 1) BranchSign.plus m < 4 * M + 1 := by
          omega
        exact Nat.lt_succ_iff.mp hprevRow_lt
      have : K + 1 ≤ plusCutoff (4 * M) m := by
        exact (plus_cutoff_iff hmpos (show 2 ≤ K + 1 by omega)).1 hprevRow
      omega
    simpa [K] using Nat.le_antisymm hupper hlower
  have hminus8 : 1 ≤ minusCutoff (8 * M) m := by
    rw [hminus_eq]
    omega
  have hplus8 : 1 ≤ plusCutoff (8 * M) m := by
    rw [hplus_eq]
    omega
  rw [pushforwardMass, pushforwardMass]
  rw [sum_dyadicWeight_Icc hminus8, sum_dyadicWeight_Icc hplus8]
  rw [sum_dyadicWeight_Icc (show 1 ≤ minusCutoff (4 * M) m by omega), sum_dyadicWeight_Icc hplus1]
  rw [hminus_eq, hplus_eq, dyadicWeight_succ, dyadicWeight_succ]
  ring

lemma dyadicWeight_tendsto_zero :
    Filter.Tendsto dyadicWeight Filter.atTop (nhds 0) := by
  change Filter.Tendsto (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) Filter.atTop (nhds 0)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one
    (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) < 1 by norm_num)

lemma sum_dyadicWeight_Icc_le_half (K : ℕ) :
    Finset.sum (Finset.Icc 2 K) dyadicWeight ≤ (1 / 2 : ℝ) := by
  by_cases hK : 1 ≤ K
  · rw [sum_dyadicWeight_Icc hK]
    have hnonneg : 0 ≤ dyadicWeight K := by
      simpa [dyadicWeight] using (pow_nonneg (show 0 ≤ (1 / 2 : ℝ) by norm_num) K)
    nlinarith
  · have hK0 : K = 0 := by omega
    subst hK0
    simp

theorem pushforwardMass_le_one (M m : ℕ) :
    pushforwardMass M m ≤ 1 := by
  unfold pushforwardMass
  have hminus := sum_dyadicWeight_Icc_le_half (minusCutoff M m)
  have hplus := sum_dyadicWeight_Icc_le_half (plusCutoff M m)
  nlinarith

theorem pushforwardMass_ge_one_sub_two_mul_dyadicWeight {M m K : ℕ}
    (hm : 0 < m) (hK : 2 ≤ K) (hcut : natDescendant K BranchSign.plus m ≤ M) :
    1 - 2 * dyadicWeight K ≤ pushforwardMass M m := by
  have hminusRow : natDescendant K BranchSign.minus m ≤ M := by
    have hle : natDescendant K BranchSign.minus m ≤ natDescendant K BranchSign.plus m := by
      simp [natDescendant]
      omega
    exact le_trans hle hcut
  have hminusK : K ≤ minusCutoff M m := (minus_cutoff_iff hm hK).1 hminusRow
  have hplusK : K ≤ plusCutoff M m := (plus_cutoff_iff hm hK).1 hcut
  have hsubsetMinus : Finset.Icc 2 K ⊆ Finset.Icc 2 (minusCutoff M m) := by
    intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hk2, hkK⟩
    exact Finset.mem_Icc.mpr ⟨hk2, le_trans hkK hminusK⟩
  have hsubsetPlus : Finset.Icc 2 K ⊆ Finset.Icc 2 (plusCutoff M m) := by
    intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hk2, hkK⟩
    exact Finset.mem_Icc.mpr ⟨hk2, le_trans hkK hplusK⟩
  have hminusSum :
      Finset.sum (Finset.Icc 2 K) dyadicWeight ≤
        Finset.sum (Finset.Icc 2 (minusCutoff M m)) dyadicWeight := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubsetMinus <| by
      intro k hk hnot
      simpa [dyadicWeight] using (pow_nonneg (show 0 ≤ (1 / 2 : ℝ) by norm_num) k)
  have hplusSum :
      Finset.sum (Finset.Icc 2 K) dyadicWeight ≤
        Finset.sum (Finset.Icc 2 (plusCutoff M m)) dyadicWeight := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubsetPlus <| by
      intro k hk hnot
      simpa [dyadicWeight] using (pow_nonneg (show 0 ≤ (1 / 2 : ℝ) by norm_num) k)
  have hsum :
      2 * Finset.sum (Finset.Icc 2 K) dyadicWeight ≤ pushforwardMass M m := by
    unfold pushforwardMass
    nlinarith
  calc
    1 - 2 * dyadicWeight K = 2 * Finset.sum (Finset.Icc 2 K) dyadicWeight := by
      rw [sum_dyadicWeight_Icc (show 1 ≤ K by omega)]
      ring
    _ ≤ pushforwardMass M m := hsum

theorem pushforwardMass_tendsto_one {m : ℕ} (hm : Odd m) :
    Filter.Tendsto (fun M : ℕ => pushforwardMass M m) Filter.atTop (nhds 1) := by
  have hm1 : 1 ≤ m := one_le_of_nat_odd hm
  have hmpos : 0 < m := Nat.succ_le_iff.mp hm1
  have hshiftNat : Filter.Tendsto (fun k : ℕ => k + 2) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, ?_⟩
    intro k hk
    exact le_trans hk (Nat.le_add_right _ _)
  have hdecayShift :
      Filter.Tendsto (fun k : ℕ => dyadicWeight (k + 2)) Filter.atTop (nhds 0) := by
    exact dyadicWeight_tendsto_zero.comp hshiftNat
  have hdecay :
      Filter.Tendsto (fun k : ℕ => 2 * dyadicWeight (k + 2)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hdecayShift)
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  rcases Metric.tendsto_atTop.1 hdecay ε hε with ⟨K, hK⟩
  refine ⟨natDescendant (K + 2) BranchSign.plus m, ?_⟩
  intro M hM
  have hlower :
      1 - 2 * dyadicWeight (K + 2) ≤ pushforwardMass M m :=
    pushforwardMass_ge_one_sub_two_mul_dyadicWeight hmpos (show 2 ≤ K + 2 by omega) hM
  have hupper : pushforwardMass M m ≤ 1 := pushforwardMass_le_one M m
  have hbound : |pushforwardMass M m - 1| ≤ 2 * dyadicWeight (K + 2) := by
    have hnonpos : pushforwardMass M m - 1 ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos]
    nlinarith
  have hsmall : 2 * dyadicWeight (K + 2) < ε := by
    have hsmall' : 2 * |dyadicWeight (K + 2)| < ε := by
      simpa [Real.dist_eq] using hK K le_rfl
    have hnonneg : 0 ≤ dyadicWeight (K + 2) := by
      simpa [dyadicWeight] using (pow_nonneg (show 0 ≤ (1 / 2 : ℝ) by norm_num) (K + 2))
    simpa [abs_of_nonneg hnonneg] using hsmall'
  simpa [Real.dist_eq] using lt_of_le_of_lt hbound hsmall

/-- Odd proper divisors used in the weighted Möbius recurrence on the odd base. -/
def oddProperDivisors (m : ℕ) : Finset ℕ := m.properDivisors.filter Odd

lemma mem_oddProperDivisors {m d : ℕ} :
    d ∈ oddProperDivisors m ↔ d ∣ m ∧ d < m ∧ Odd d := by
  simp [oddProperDivisors, Nat.mem_properDivisors, and_assoc]

lemma oddProperDivisors_prime {p : ℕ} (hp : p.Prime) :
    oddProperDivisors p = {1} := by
  ext d
  constructor
  · intro hd
    rcases mem_oddProperDivisors.mp hd with ⟨hdvd, hlt, _⟩
    rcases (Nat.dvd_prime hp).mp hdvd with rfl | rfl
    · simp
    · exfalso
      omega
  · intro hd
    rcases Finset.mem_singleton.mp hd with rfl
    simp [oddProperDivisors, Nat.one_mem_properDivisors_iff_one_lt.2 hp.one_lt]

lemma oddProperDivisors_prime_pow {p k : ℕ} (hp : p.Prime) (hodd : Odd p) :
    oddProperDivisors (p ^ k) =
      (Finset.range k).map ⟨(p ^ ·), Nat.pow_right_injective hp.two_le⟩ := by
  rw [oddProperDivisors, Nat.properDivisors_prime_pow hp]
  refine Finset.filter_true_of_mem ?_
  intro x hx
  rcases Finset.mem_map.mp hx with ⟨j, hj, rfl⟩
  exact (show Odd (p ^ j) from hodd.pow)

lemma oddProperDivisors_prime_mul {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hneq : p ≠ q) (hpodd : Odd p) (hqodd : Odd q) :
  oddProperDivisors (p * q) = insert 1 (insert p ({q} : Finset ℕ)) := by
  ext d
  constructor
  · intro hd
    rcases mem_oddProperDivisors.mp hd with ⟨hdvd, hlt, _⟩
    by_cases hpd : p ∣ d
    · rcases hpd with ⟨k, rfl⟩
      have hkdivq : k ∣ q := by
        rcases hdvd with ⟨e, he⟩
        refine ⟨e, ?_⟩
        apply Nat.eq_of_mul_eq_mul_left hp.pos
        simpa [Nat.mul_assoc] using he
      rcases (Nat.dvd_prime hq).mp hkdivq with hk | hk
      · subst hk
        simp [hneq]
      · subst hk
        exfalso
        omega
    · rcases hdvd with ⟨e, he⟩
      have hpmul : p ∣ d * e := ⟨q, he.symm⟩
      have hpe : p ∣ e := (hp.dvd_mul.mp hpmul).resolve_left hpd
      rcases hpe with ⟨k, hk⟩
      have hddivq : d ∣ q := by
        refine ⟨k, ?_⟩
        apply Nat.eq_of_mul_eq_mul_left hp.pos
        calc
          p * q = d * e := he
          _ = d * (p * k) := by rw [hk]
          _ = p * (d * k) := by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      rcases (Nat.dvd_prime hq).mp hddivq with hd1 | hdq
      · subst hd1
        simp [hneq]
      · subst hdq
        simp [hneq]
  · intro hd
    have hpq_gt : 1 < p * q := by
      nlinarith [hp.two_le, hq.two_le]
    have hp_lt_pq : p < p * q := by
      nlinarith [hp.pos, hq.two_le]
    have hq_lt_pq : q < p * q := by
      nlinarith [hq.pos, hp.two_le]
    simp [mem_oddProperDivisors, hneq] at hd ⊢
    rcases hd with rfl | rfl | rfl
    · constructor
      · exact one_dvd _
      constructor
      · exact hpq_gt
      · decide
    · constructor
      · exact ⟨q, rfl⟩
      constructor
      · exact hp_lt_pq
      · exact hpodd
    · constructor
      · exact ⟨p, by rw [Nat.mul_comm]⟩
      constructor
      · exact hq_lt_pq
      · exact hqodd

lemma oddProperDivisors_eq_properDivisors {m : ℕ} (hm : Odd m) :
    oddProperDivisors m = m.properDivisors := by
  refine Finset.filter_true_of_mem ?_
  intro d hd
  exact hm.of_dvd_nat (Nat.mem_properDivisors.mp hd).1

theorem odd_log_eq_vonMangoldt_add_sum_oddProperDivisors {m : ℕ} (hm : Odd m) :
    Real.log (m : ℝ) =
      ArithmeticFunction.vonMangoldt m +
        ∑ d ∈ oddProperDivisors m, ArithmeticFunction.vonMangoldt d := by
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0] at hm
    simp at hm
  calc
    Real.log (m : ℝ) = ∑ d ∈ m.divisors, ArithmeticFunction.vonMangoldt d := by
      symm
      exact ArithmeticFunction.vonMangoldt_sum (n := m)
    _ = ArithmeticFunction.vonMangoldt m +
          ∑ d ∈ m.properDivisors, ArithmeticFunction.vonMangoldt d := by
      rw [← Nat.insert_self_properDivisors hm0, Finset.sum_insert Nat.self_notMem_properDivisors]
    _ = ArithmeticFunction.vonMangoldt m +
          ∑ d ∈ oddProperDivisors m, ArithmeticFunction.vonMangoldt d := by
      rw [oddProperDivisors_eq_properDivisors hm]

/-- One weighted Möbius inversion step driven by already computed smaller odd-base coefficients. -/
noncomputable def pushforwardMangoldtStep (M m : ℕ) (prev : ∀ d, d < m → ℝ) : ℝ :=
  if _hm : m ≤ 1 then
    0
  else
    pushforwardMass M m * Real.log (m : ℝ) -
      ∑ d : oddProperDivisors m,
        prev d ((mem_oddProperDivisors.mp d.2).2.1) * pushforwardMass M (m / d)

/-- Finite weighted Möbius approximation to the odd von Mangoldt channel. -/
noncomputable def pushforwardMangoldtApprox (M m : ℕ) : ℝ :=
  Nat.strongRecOn' m (pushforwardMangoldtStep M)

theorem pushforwardMangoldtApprox_eq_step (M m : ℕ) :
    pushforwardMangoldtApprox M m =
      pushforwardMangoldtStep M m (fun d _ => pushforwardMangoldtApprox M d) := by
  unfold pushforwardMangoldtApprox
  simpa using (Nat.strongRecOn'_beta (n := m) (h := pushforwardMangoldtStep M))

@[simp] theorem pushforwardMangoldtApprox_zero (M : ℕ) :
    pushforwardMangoldtApprox M 0 = 0 := by
  rw [pushforwardMangoldtApprox_eq_step]
  simp [pushforwardMangoldtStep]

@[simp] theorem pushforwardMangoldtApprox_one (M : ℕ) :
    pushforwardMangoldtApprox M 1 = 0 := by
  rw [pushforwardMangoldtApprox_eq_step]
  simp [pushforwardMangoldtStep]

/-- Deviation of the finite odd pushforward mass from its limiting value `1`. -/
noncomputable def pushforwardMassError (M m : ℕ) : ℝ :=
  pushforwardMass M m - 1

/-- Deviation of the finite odd Möbius channel from the von Mangoldt function. -/
noncomputable def pushforwardMangoldtError (M m : ℕ) : ℝ :=
  pushforwardMangoldtApprox M m - ArithmeticFunction.vonMangoldt m

theorem pushforwardMassError_tendsto_zero {m : ℕ} (hm : Odd m) :
    Filter.Tendsto (fun M : ℕ => pushforwardMassError M m) Filter.atTop (nhds 0) := by
  have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
  simpa [pushforwardMassError] using (pushforwardMass_tendsto_one hm).sub hconst

lemma odd_div_of_dvd {m d : ℕ} (hm : Odd m) (hdvd : d ∣ m) (hodd : Odd d) :
    Odd (m / d) := by
  rcases hdvd with ⟨k, hk⟩
  have hkodd : Odd k := by
    have hprod : Odd (d * k) := by simpa [hk] using hm
    exact Nat.Odd.of_mul_right hprod
  have hdpos : 0 < d := Nat.succ_le_iff.mp (one_le_of_nat_odd hodd)
  have hdiv : k * d / d = k := Nat.mul_div_left k hdpos
  simpa [hk, Nat.mul_comm d k, hdiv] using hkodd

theorem pushforwardMangoldtError_eq {M m : ℕ} (hm : Odd m) (hm1 : 1 < m) :
    pushforwardMangoldtError M m =
      pushforwardMassError M m * Real.log (m : ℝ) -
        ∑ d ∈ oddProperDivisors m, pushforwardMangoldtError M d -
        ∑ d ∈ oddProperDivisors m,
          ArithmeticFunction.vonMangoldt d * pushforwardMassError M (m / d) -
        ∑ d ∈ oddProperDivisors m,
          pushforwardMangoldtError M d * pushforwardMassError M (m / d) := by
  have hmle : ¬ m ≤ 1 := Nat.not_le_of_gt hm1
  rw [pushforwardMangoldtError, pushforwardMangoldtApprox_eq_step]
  simp [pushforwardMangoldtStep, hmle]
  rw [odd_log_eq_vonMangoldt_add_sum_oddProperDivisors hm]
  have hsum_expand' :
      ∑ d ∈ oddProperDivisors m, pushforwardMangoldtApprox M d * pushforwardMass M (m / d) =
        (∑ d ∈ oddProperDivisors m, ArithmeticFunction.vonMangoldt d) +
          ∑ d ∈ oddProperDivisors m, pushforwardMangoldtError M d +
          ((∑ d ∈ oddProperDivisors m,
            ArithmeticFunction.vonMangoldt d * pushforwardMassError M (m / d)) +
          ∑ d ∈ oddProperDivisors m,
            pushforwardMangoldtError M d * pushforwardMassError M (m / d)) := by
    calc
      _ = ∑ d ∈ oddProperDivisors m,
            ((pushforwardMangoldtError M d + ArithmeticFunction.vonMangoldt d) *
              (pushforwardMassError M (m / d) + 1)) := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            simp [pushforwardMangoldtError, pushforwardMassError]
      _ = ∑ d ∈ oddProperDivisors m,
            ((ArithmeticFunction.vonMangoldt d + pushforwardMangoldtError M d) +
              (ArithmeticFunction.vonMangoldt d * pushforwardMassError M (m / d) +
                pushforwardMangoldtError M d * pushforwardMassError M (m / d))) := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            ring
      _ = (∑ d ∈ oddProperDivisors m,
            (ArithmeticFunction.vonMangoldt d + pushforwardMangoldtError M d)) +
          ∑ d ∈ oddProperDivisors m,
            (ArithmeticFunction.vonMangoldt d * pushforwardMassError M (m / d) +
              pushforwardMangoldtError M d * pushforwardMassError M (m / d)) := by
            rw [Finset.sum_add_distrib]
      _ = (∑ d ∈ oddProperDivisors m, ArithmeticFunction.vonMangoldt d) +
          ∑ d ∈ oddProperDivisors m, pushforwardMangoldtError M d +
          ((∑ d ∈ oddProperDivisors m,
            ArithmeticFunction.vonMangoldt d * pushforwardMassError M (m / d)) +
            ∑ d ∈ oddProperDivisors m,
              pushforwardMangoldtError M d * pushforwardMassError M (m / d)) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hsum_expand :
      ∑ x ∈ (oddProperDivisors m).attach,
          pushforwardMangoldtApprox M ↑x * pushforwardMass M (m / ↑x) =
        (∑ d ∈ oddProperDivisors m, ArithmeticFunction.vonMangoldt d) +
          ∑ d ∈ oddProperDivisors m, pushforwardMangoldtError M d +
          ((∑ d ∈ oddProperDivisors m,
            ArithmeticFunction.vonMangoldt d * pushforwardMassError M (m / d)) +
          ∑ d ∈ oddProperDivisors m,
            pushforwardMangoldtError M d * pushforwardMassError M (m / d)) := by
    calc
      ∑ x ∈ (oddProperDivisors m).attach,
          pushforwardMangoldtApprox M ↑x * pushforwardMass M (m / ↑x) =
        ∑ d ∈ oddProperDivisors m,
          pushforwardMangoldtApprox M d * pushforwardMass M (m / d) := by
            simpa using (Finset.sum_attach (s := oddProperDivisors m)
              (f := fun d => pushforwardMangoldtApprox M d * pushforwardMass M (m / d)))
      _ =
        (∑ d ∈ oddProperDivisors m, ArithmeticFunction.vonMangoldt d) +
          ∑ d ∈ oddProperDivisors m, pushforwardMangoldtError M d +
          ((∑ d ∈ oddProperDivisors m,
            ArithmeticFunction.vonMangoldt d * pushforwardMassError M (m / d)) +
          ∑ d ∈ oddProperDivisors m,
            pushforwardMangoldtError M d * pushforwardMassError M (m / d)) := hsum_expand'
  rw [hsum_expand]
  rw [pushforwardMassError]
  ring

theorem pushforwardMangoldtApprox_nonPrimePow {M m : ℕ} (hnot : ¬ IsPrimePow m) :
    pushforwardMangoldtApprox M m = pushforwardMangoldtError M m := by
  rw [pushforwardMangoldtError, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnot, sub_zero]

theorem pushforwardMangoldtApprox_nonPrimePow_residual {M m : ℕ}
    (hm : Odd m) (hm1 : 1 < m) (hnot : ¬ IsPrimePow m) :
    pushforwardMangoldtApprox M m =
      pushforwardMassError M m * Real.log (m : ℝ) -
        ∑ d ∈ oddProperDivisors m, pushforwardMangoldtError M d -
        ∑ d ∈ oddProperDivisors m,
          ArithmeticFunction.vonMangoldt d * pushforwardMassError M (m / d) -
        ∑ d ∈ oddProperDivisors m,
          pushforwardMangoldtError M d * pushforwardMassError M (m / d) := by
  rw [pushforwardMangoldtApprox_nonPrimePow hnot]
  exact pushforwardMangoldtError_eq hm hm1

theorem pushforwardMangoldtApprox_prime_pow_succ {M p k : ℕ}
    (hp : p.Prime) (hodd : Odd p) :
    pushforwardMangoldtApprox M (p ^ (k + 1)) =
      pushforwardMass M (p ^ (k + 1)) * Real.log ((p ^ (k + 1) : ℕ) : ℝ) -
        Finset.sum (Finset.range (k + 1)) (fun i =>
          pushforwardMangoldtApprox M (p ^ i) *
            pushforwardMass M (p ^ ((k + 1) - i))) := by
  rw [pushforwardMangoldtApprox_eq_step, pushforwardMangoldtStep]
  have hpow_gt : 1 < p ^ (k + 1) := Nat.one_lt_pow (Nat.succ_ne_zero k) hp.one_lt
  have hle : ¬ p ^ (k + 1) ≤ 1 := Nat.not_le_of_gt hpow_gt
  simp [hle]
  rw [oddProperDivisors_prime_pow hp hodd]
  rw [show
      ∑ d ∈ ((Finset.range (k + 1)).map ⟨(p ^ ·), Nat.pow_right_injective hp.two_le⟩).attach,
        pushforwardMangoldtApprox M ↑d * pushforwardMass M (p ^ (k + 1) / ↑d) =
      Finset.sum ((Finset.range (k + 1)).map ⟨(p ^ ·), Nat.pow_right_injective hp.two_le⟩)
        (fun d => pushforwardMangoldtApprox M d * pushforwardMass M (p ^ (k + 1) / d)) by
      simpa using
        (Finset.sum_attach
          (s := (Finset.range (k + 1)).map ⟨(p ^ ·), Nat.pow_right_injective hp.two_le⟩)
          (f := fun d =>
            pushforwardMangoldtApprox M d * pushforwardMass M (p ^ (k + 1) / d)))]
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl ?_
  intro i hi
  change
    pushforwardMangoldtApprox M (p ^ i) * pushforwardMass M (p ^ (k + 1) / (p ^ i)) =
      pushforwardMangoldtApprox M (p ^ i) * pushforwardMass M (p ^ (k + 1 - i))
  rw [Nat.pow_div (le_of_lt (Finset.mem_range.mp hi)) hp.pos]

theorem pushforwardMangoldtApprox_prime_sq_step {M p : ℕ}
    (hp : p.Prime) (hodd : Odd p) :
    pushforwardMangoldtApprox M (p ^ 2) =
      pushforwardMass M (p ^ 2) * Real.log ((p ^ 2 : ℕ) : ℝ) -
        pushforwardMangoldtApprox M p * pushforwardMass M p := by
  rw [pushforwardMangoldtApprox_prime_pow_succ (M := M) (p := p) (k := 1) hp hodd]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [pow_two, pushforwardMangoldtApprox_one]

theorem pushforwardMangoldtApprox_prime_sq {M p : ℕ}
    (hp : p.Prime) (hodd : Odd p) :
    pushforwardMangoldtApprox M (p ^ 2) =
      (2 * pushforwardMass M (p ^ 2) - pushforwardMass M p ^ 2) * Real.log (p : ℝ) := by
  have hprime :
      pushforwardMangoldtApprox M p = pushforwardMass M p * Real.log (p : ℝ) := by
    rw [pushforwardMangoldtApprox_eq_step, pushforwardMangoldtStep]
    have hp1 : ¬ p ≤ 1 := Nat.not_le_of_gt hp.one_lt
    by_cases hle : p ≤ 1
    · exact (hp1 hle).elim
    · rw [oddProperDivisors_prime hp]
      simp [hle]
  rw [pushforwardMangoldtApprox_prime_sq_step hp hodd, hprime]
  calc
    pushforwardMass M (p ^ 2) * Real.log ((p ^ 2 : ℕ) : ℝ) -
        (pushforwardMass M p * Real.log (p : ℝ)) * pushforwardMass M p =
      pushforwardMass M (p ^ 2) * (2 * Real.log (p : ℝ)) -
        (pushforwardMass M p)^2 * Real.log (p : ℝ) := by
          rw [Nat.cast_pow, Real.log_pow, show (2 : ℝ) = (2 : ℕ) by norm_num]
          ring
    _ = (2 * pushforwardMass M (p ^ 2) - pushforwardMass M p ^ 2) * Real.log (p : ℝ) := by
      ring

theorem pushforwardMangoldtApprox_prime {M p : ℕ} (hp : p.Prime) :
    pushforwardMangoldtApprox M p = pushforwardMass M p * Real.log (p : ℝ) := by
  rw [pushforwardMangoldtApprox_eq_step, pushforwardMangoldtStep]
  have hp1 : ¬ p ≤ 1 := Nat.not_le_of_gt hp.one_lt
  by_cases hle : p ≤ 1
  · exact (hp1 hle).elim
  · rw [oddProperDivisors_prime hp]
    simp [hle]

theorem pushforwardMangoldtApprox_prime_dyadic_extrapolation {M p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hmem : p ≤ M) :
    2 * pushforwardMangoldtApprox (8 * M) p - pushforwardMangoldtApprox (4 * M) p =
      Real.log (p : ℝ) := by
  rw [pushforwardMangoldtApprox_prime hp, pushforwardMangoldtApprox_prime hp]
  calc
    2 * (pushforwardMass (8 * M) p * Real.log (p : ℝ)) -
        pushforwardMass (4 * M) p * Real.log (p : ℝ) =
        (2 * pushforwardMass (8 * M) p - pushforwardMass (4 * M) p) * Real.log (p : ℝ) := by
          ring
    _ = Real.log (p : ℝ) := by
      rw [pushforwardMass_dyadic_extrapolation (M := M) (m := p) hodd hmem]
      ring

theorem pushforwardMangoldtApprox_semiprime_distinct {M p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hneq : p ≠ q) (hpodd : Odd p) (hqodd : Odd q) :
    pushforwardMangoldtApprox M (p * q) =
      (pushforwardMass M (p * q) - pushforwardMass M p * pushforwardMass M q) *
        Real.log ((p * q : ℕ) : ℝ) := by
  rw [pushforwardMangoldtApprox_eq_step, pushforwardMangoldtStep]
  have hpqle : ¬ p * q ≤ 1 := by
    nlinarith [hp.two_le, hq.two_le]
  simp [hpqle]
  rw [oddProperDivisors_prime_mul hp hq hneq hpodd hqodd]
  rw [show
      ∑ d ∈ (insert 1 (insert p ({q} : Finset ℕ))).attach,
        pushforwardMangoldtApprox M ↑d * pushforwardMass M (p * q / ↑d) =
      Finset.sum (insert 1 (insert p ({q} : Finset ℕ)))
        (fun d => pushforwardMangoldtApprox M d * pushforwardMass M (p * q / d)) by
      simpa using
        (Finset.sum_attach
          (s := insert 1 (insert p ({q} : Finset ℕ)))
          (f := fun d =>
            pushforwardMangoldtApprox M d * pushforwardMass M (p * q / d)))]
  have hpdiv : p * q / p = q := by
    simpa [Nat.mul_comm] using (Nat.mul_div_right q hp.pos)
  have hqdiv : p * q / q = p := by
    simpa [Nat.mul_comm] using (Nat.mul_div_right p hq.pos)
  simp [pushforwardMangoldtApprox_one, pushforwardMangoldtApprox_prime hp,
    pushforwardMangoldtApprox_prime hq, hneq, hpdiv, hqdiv]
  calc
    pushforwardMass M (p * q) * Real.log ((p : ℝ) * q) -
        (pushforwardMass M p * Real.log (p : ℝ) * pushforwardMass M q +
          pushforwardMass M q * Real.log (q : ℝ) * pushforwardMass M p) =
      pushforwardMass M (p * q) * (Real.log (p : ℝ) + Real.log (q : ℝ)) -
        (pushforwardMass M p * pushforwardMass M q) * Real.log (p : ℝ) -
        (pushforwardMass M p * pushforwardMass M q) * Real.log (q : ℝ) := by
          rw [Real.log_mul (Nat.cast_ne_zero.mpr hp.ne_zero) (Nat.cast_ne_zero.mpr hq.ne_zero)]
          ring
    _ = (pushforwardMass M (p * q) - pushforwardMass M p * pushforwardMass M q) *
        (Real.log (p : ℝ) + Real.log (q : ℝ)) := by
          ring
    _ = (pushforwardMass M (p * q) - pushforwardMass M p * pushforwardMass M q) *
        Real.log ((p : ℝ) * q) := by
          rw [Real.log_mul (Nat.cast_ne_zero.mpr hp.ne_zero) (Nat.cast_ne_zero.mpr hq.ne_zero)]

lemma oddProperDivisors_prime_mul_mul {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpodd : Odd p) (hqodd : Odd q) (hrodd : Odd r) :
    oddProperDivisors (p * q * r) =
      insert 1 (insert p (insert q (insert r (insert (p * q) (insert (p * r) ({q * r} : Finset ℕ)))))) := by
  ext d
  have hr_mem :
      r ∈ insert 1 (insert p (insert q (insert r (insert (p * q) (insert (p * r)
        ({q * r} : Finset ℕ)))))) := by
    exact Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inl rfl
  have hpq_mem :
      p * q ∈ insert 1 (insert p (insert q (insert r (insert (p * q) (insert (p * r)
        ({q * r} : Finset ℕ)))))) := by
    exact Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inl rfl
  have hp_mem :
      p ∈ insert 1 (insert p (insert q (insert r (insert (p * q) (insert (p * r)
        ({q * r} : Finset ℕ)))))) := by
    exact Finset.mem_insert.mpr <| Or.inr <| Finset.mem_insert.mpr <| Or.inl rfl
  have hq_mem :
      q ∈ insert 1 (insert p (insert q (insert r (insert (p * q) (insert (p * r)
        ({q * r} : Finset ℕ)))))) := by
    exact Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inl rfl
  have hpr_mem :
      p * r ∈ insert 1 (insert p (insert q (insert r (insert (p * q) (insert (p * r)
        ({q * r} : Finset ℕ)))))) := by
    exact Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inl rfl
  have hqr_mem :
      q * r ∈ insert 1 (insert p (insert q (insert r (insert (p * q) (insert (p * r)
        ({q * r} : Finset ℕ)))))) := by
    exact Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_insert.mpr <| Or.inr <|
      Finset.mem_singleton.mpr rfl
  constructor
  · intro hd
    rcases mem_oddProperDivisors.mp hd with ⟨hdvd, hlt, hodd⟩
    by_cases hrd : r ∣ d
    · rcases hrd with ⟨k, hk⟩
      have hkdiv : k ∣ p * q := by
        rcases hdvd with ⟨e, he⟩
        refine ⟨e, ?_⟩
        apply Nat.eq_of_mul_eq_mul_left hr.pos
        calc
          r * (p * q) = p * q * r := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          _ = d * e := he
          _ = (r * k) * e := by rw [hk]
          _ = r * (k * e) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have hklt : k < p * q := by
        by_contra hkge
        have hmul : p * q * r ≤ k * r := by
          exact Nat.mul_le_mul_right r (Nat.not_lt.mp hkge)
        have : p * q * r ≤ d := by
          simpa [hk, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
        exact not_lt_of_ge this hlt
      have hkodd : Odd k := by
        have hprod : Odd (r * k) := by
          simpa [hk, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hodd
        exact Nat.Odd.of_mul_right hprod
      have hkmem : k ∈ oddProperDivisors (p * q) :=
        mem_oddProperDivisors.mpr ⟨hkdiv, hklt, hkodd⟩
      rw [oddProperDivisors_prime_mul hp hq hpq hpodd hqodd] at hkmem
      rcases Finset.mem_insert.mp hkmem with hk1 | hkmem
      · subst hk1
        simpa [hk] using hr_mem
      · rcases Finset.mem_insert.mp hkmem with hkp | hkq
        · subst hkp
          simpa [hk, Nat.mul_comm] using hpr_mem
        · rcases Finset.mem_singleton.mp hkq with rfl
          simpa [hk, Nat.mul_comm] using hqr_mem
    · have hddiv : d ∣ p * q := by
        rcases hdvd with ⟨e, he⟩
        have hremul : r ∣ d * e := by
          refine ⟨p * q, ?_⟩
          calc
            d * e = p * q * r := he.symm
            _ = r * (p * q) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        have hre : r ∣ e := (hr.dvd_mul.mp hremul).resolve_left hrd
        rcases hre with ⟨e', he'⟩
        refine ⟨e', ?_⟩
        apply Nat.eq_of_mul_eq_mul_left hr.pos
        calc
          r * (p * q) = p * q * r := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          _ = d * e := he
          _ = d * (r * e') := by rw [he']
          _ = r * (d * e') := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      by_cases hdlt : d < p * q
      · have hdmem : d ∈ oddProperDivisors (p * q) :=
          mem_oddProperDivisors.mpr ⟨hddiv, hdlt, hodd⟩
        rw [oddProperDivisors_prime_mul hp hq hpq hpodd hqodd] at hdmem
        rcases Finset.mem_insert.mp hdmem with hd1 | hdmem
        · subst hd1
          exact Finset.mem_insert.mpr (Or.inl rfl)
        · rcases Finset.mem_insert.mp hdmem with hdp | hdq
          · subst hdp
            simpa using hp_mem
          · rcases Finset.mem_singleton.mp hdq with rfl
            simpa using hq_mem
      · have hdle : d ≤ p * q := Nat.le_of_dvd (Nat.mul_pos hp.pos hq.pos) hddiv
        have hdeq : d = p * q := by omega
        subst hdeq
        simpa using hpq_mem
  · intro hd
    have hpq_gt_one : 1 < p * q := by
      have hpq_ge_q : q ≤ p * q := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_right q (le_of_lt hp.one_lt)
      exact lt_of_lt_of_le hq.one_lt hpq_ge_q
    have hpr_gt_one : 1 < p * r := by
      have hpr_ge_r : r ≤ p * r := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_right r (le_of_lt hp.one_lt)
      exact lt_of_lt_of_le hr.one_lt hpr_ge_r
    have hqr_gt_one : 1 < q * r := by
      have hqr_ge_r : r ≤ q * r := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_right r (le_of_lt hq.one_lt)
      exact lt_of_lt_of_le hr.one_lt hqr_ge_r
    have hp_lt : p < p * q * r := by
      have hmul : p * 1 < p * (q * r) :=
        Nat.mul_lt_mul_of_pos_left hqr_gt_one hp.pos
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
    have hpqr_gt_one : 1 < p * q * r := lt_trans hp.one_lt hp_lt
    have hq_lt : q < p * q * r := by
      have hmul : q * 1 < q * (p * r) :=
        Nat.mul_lt_mul_of_pos_left hpr_gt_one hq.pos
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
    have hr_lt : r < p * q * r := by
      have hmul : r * 1 < r * (p * q) :=
        Nat.mul_lt_mul_of_pos_left hpq_gt_one hr.pos
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
    have hpq_lt : p * q < p * q * r := by
      have hmul : (p * q) * 1 < (p * q) * r :=
        Nat.mul_lt_mul_of_pos_left hr.one_lt (Nat.mul_pos hp.pos hq.pos)
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
    have hpr_lt : p * r < p * q * r := by
      have hmul : (p * r) * 1 < (p * r) * q :=
        Nat.mul_lt_mul_of_pos_left hq.one_lt (Nat.mul_pos hp.pos hr.pos)
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
    have hqr_lt : q * r < p * q * r := by
      have hmul : 1 * (q * r) < p * (q * r) := by
        exact Nat.mul_lt_mul_of_pos_right hp.one_lt (Nat.mul_pos hq.pos hr.pos)
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
    rcases Finset.mem_insert.mp hd with hd1 | hd
    · rcases hd1 with rfl
      exact mem_oddProperDivisors.mpr ⟨one_dvd _, hpqr_gt_one, by decide⟩
    rcases Finset.mem_insert.mp hd with hdp | hd
    · rcases hdp with rfl
      exact mem_oddProperDivisors.mpr ⟨⟨q * r, by simp [Nat.mul_assoc]⟩, hp_lt, hpodd⟩
    rcases Finset.mem_insert.mp hd with hdq | hd
    · rcases hdq with rfl
      exact mem_oddProperDivisors.mpr ⟨⟨p * r, by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]⟩, hq_lt, hqodd⟩
    rcases Finset.mem_insert.mp hd with hdr | hd
    · rcases hdr with rfl
      exact mem_oddProperDivisors.mpr ⟨⟨p * q, by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]⟩, hr_lt, hrodd⟩
    rcases Finset.mem_insert.mp hd with hdpq | hd
    · rcases hdpq with rfl
      exact mem_oddProperDivisors.mpr ⟨⟨r, by simp [Nat.mul_assoc]⟩, hpq_lt, hpodd.mul hqodd⟩
    rcases Finset.mem_insert.mp hd with hdpr | hdqr
    · rcases hdpr with rfl
      exact mem_oddProperDivisors.mpr ⟨⟨q, by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]⟩, hpr_lt, hpodd.mul hrodd⟩
    · rcases Finset.mem_singleton.mp hdqr with rfl
      exact mem_oddProperDivisors.mpr ⟨⟨p, by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]⟩, hqr_lt, hqodd.mul hrodd⟩

def squarefreeThreeDivisors (p q r : ℕ) : Finset ℕ :=
  insert 1 (insert p (insert q (insert r (insert (p * q) (insert (p * r)
    ({q * r} : Finset ℕ))))))

theorem pushforwardMangoldtApprox_squarefree_three_sum {M p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpodd : Odd p) (hqodd : Odd q) (hrodd : Odd r) :
    pushforwardMangoldtApprox M (p * q * r) =
      pushforwardMass M (p * q * r) * Real.log ((p * q * r : ℕ) : ℝ) -
        Finset.sum (squarefreeThreeDivisors p q r)
          (fun d => pushforwardMangoldtApprox M d * pushforwardMass M (p * q * r / d)) := by
  rw [pushforwardMangoldtApprox_eq_step, pushforwardMangoldtStep]
  have hpqrle : ¬ p * q * r ≤ 1 := by
    have hqr_gt_one : 1 < q * r := by
      have hqr_ge_r : r ≤ q * r := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_right r (le_of_lt hq.one_lt)
      exact lt_of_lt_of_le hr.one_lt hqr_ge_r
    have hp_lt : p < p * q * r := by
      have hmul : p * 1 < p * (q * r) :=
        Nat.mul_lt_mul_of_pos_left hqr_gt_one hp.pos
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
    exact Nat.not_le_of_gt (lt_trans hp.one_lt hp_lt)
  split_ifs
  rw [oddProperDivisors_prime_mul_mul hp hq hr hpq hpr hqr hpodd hqodd hrodd]
  simp only [Finset.univ_eq_attach]
  change
    pushforwardMass M (p * q * r) * Real.log ((p * q * r : ℕ) : ℝ) -
        ∑ d ∈ (squarefreeThreeDivisors p q r).attach,
          pushforwardMangoldtApprox M ↑d * pushforwardMass M (p * q * r / ↑d) =
      pushforwardMass M (p * q * r) * Real.log ((p * q * r : ℕ) : ℝ) -
        Finset.sum (squarefreeThreeDivisors p q r)
          (fun d => pushforwardMangoldtApprox M d * pushforwardMass M (p * q * r / d))
  rw [show
      ∑ d ∈ (squarefreeThreeDivisors p q r).attach,
        pushforwardMangoldtApprox M ↑d * pushforwardMass M (p * q * r / ↑d) =
      Finset.sum (squarefreeThreeDivisors p q r)
        (fun d => pushforwardMangoldtApprox M d * pushforwardMass M (p * q * r / d)) by
      simpa using
        (Finset.sum_attach
          (s := squarefreeThreeDivisors p q r)
          (f := fun d =>
            pushforwardMangoldtApprox M d * pushforwardMass M (p * q * r / d)))]

theorem pushforwardMangoldtError_tendsto_zero {m : ℕ} (hm : Odd m) :
    Filter.Tendsto (fun M : ℕ => pushforwardMangoldtError M m) Filter.atTop (nhds 0) := by
  revert hm
  refine Nat.strong_induction_on m ?_
  intro m ih hm
  by_cases hm1 : 1 < m
  · have hterm1 :
        Filter.Tendsto
          (fun M : ℕ => pushforwardMassError M m * Real.log (m : ℝ))
          Filter.atTop (nhds 0) := by
      simpa [zero_mul] using (pushforwardMassError_tendsto_zero hm).mul tendsto_const_nhds
    have hterm2 :
        Filter.Tendsto
          (fun M : ℕ => ∑ d ∈ oddProperDivisors m, pushforwardMangoldtError M d)
          Filter.atTop (nhds 0) := by
      have hterm2' :
          Filter.Tendsto
            (fun M : ℕ => ∑ d ∈ oddProperDivisors m, pushforwardMangoldtError M d)
            Filter.atTop (nhds (∑ d ∈ oddProperDivisors m, (0 : ℝ))) := by
        refine tendsto_finset_sum (oddProperDivisors m) ?_
        intro d hd
        rcases mem_oddProperDivisors.mp hd with ⟨_, hlt, hodd⟩
        simpa using (ih d hlt hodd)
      simpa using hterm2'
    have hterm3 :
        Filter.Tendsto
          (fun M : ℕ =>
            ∑ d ∈ oddProperDivisors m,
              ArithmeticFunction.vonMangoldt d * pushforwardMassError M (m / d))
          Filter.atTop (nhds 0) := by
      have hterm3' :
          Filter.Tendsto
            (fun M : ℕ =>
              ∑ d ∈ oddProperDivisors m,
                ArithmeticFunction.vonMangoldt d * pushforwardMassError M (m / d))
            Filter.atTop (nhds (∑ d ∈ oddProperDivisors m, (0 : ℝ))) := by
        refine tendsto_finset_sum (oddProperDivisors m) ?_
        intro d hd
        rcases mem_oddProperDivisors.mp hd with ⟨hdvd, _, hodd⟩
        simpa using
          (tendsto_const_nhds.mul (pushforwardMassError_tendsto_zero (odd_div_of_dvd hm hdvd hodd)))
      simpa using hterm3'
    have hterm4 :
        Filter.Tendsto
          (fun M : ℕ =>
            ∑ d ∈ oddProperDivisors m,
              pushforwardMangoldtError M d * pushforwardMassError M (m / d))
          Filter.atTop (nhds 0) := by
      have hterm4' :
          Filter.Tendsto
            (fun M : ℕ =>
              ∑ d ∈ oddProperDivisors m,
                pushforwardMangoldtError M d * pushforwardMassError M (m / d))
            Filter.atTop (nhds (∑ d ∈ oddProperDivisors m, (0 : ℝ))) := by
        refine tendsto_finset_sum (oddProperDivisors m) ?_
        intro d hd
        rcases mem_oddProperDivisors.mp hd with ⟨hdvd, hlt, hodd⟩
        simpa using
          ((ih d hlt hodd).mul (pushforwardMassError_tendsto_zero (odd_div_of_dvd hm hdvd hodd)))
      simpa using hterm4'
    convert (((hterm1.sub hterm2).sub hterm3).sub hterm4) using 1
    · ext M
      exact pushforwardMangoldtError_eq (M := M) hm hm1
    · simp
  · have hle : m ≤ 1 := Nat.le_of_not_gt hm1
    have hmge : 1 ≤ m := one_le_of_nat_odd hm
    have hm_eq : m = 1 := by omega
    subst hm_eq
    simp [pushforwardMangoldtError]

theorem pushforwardMangoldtApprox_tendsto_vonMangoldt {m : ℕ} (hm : Odd m) :
    Filter.Tendsto (fun M : ℕ => pushforwardMangoldtApprox M m)
      Filter.atTop (nhds (ArithmeticFunction.vonMangoldt m)) := by
  have hrewrite :
      (fun M : ℕ => pushforwardMangoldtApprox M m) =
        fun M : ℕ => pushforwardMangoldtError M m + ArithmeticFunction.vonMangoldt m := by
    funext M
    simp [pushforwardMangoldtError, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [hrewrite]
  have hconst :
      Filter.Tendsto (fun _ : ℕ => ArithmeticFunction.vonMangoldt m)
        Filter.atTop (nhds (ArithmeticFunction.vonMangoldt m)) := tendsto_const_nhds
  simpa using (pushforwardMangoldtError_tendsto_zero hm).add hconst

theorem pushforwardMangoldtApprox_tendsto_zero_nonPrimePow {m : ℕ}
    (hm : Odd m) (hnot : ¬ IsPrimePow m) :
    Filter.Tendsto (fun M : ℕ => pushforwardMangoldtApprox M m) Filter.atTop (nhds 0) := by
  simpa [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnot] using
    (pushforwardMangoldtApprox_tendsto_vonMangoldt hm)

/-- Principal Dirichlet character modulo `2`, isolating the odd channel used by the C2
pushforward. -/
noncomputable def c2OddPrincipalChar : DirichletCharacter ℂ 2 := 1

/-- Complex von Mangoldt coefficients in the odd channel recovered by the C2 pushforward. -/
noncomputable def c2OddRecoveredVonMangoldtCoeff (n : ℕ) : ℂ :=
  (↗c2OddPrincipalChar * ↗ArithmeticFunction.vonMangoldt) n

/-- Dirichlet series of the odd von Mangoldt channel recovered by the C2 pushforward. -/
noncomputable def c2OddRecoveredVonMangoldtLSeries (s : ℂ) : ℂ :=
  L c2OddRecoveredVonMangoldtCoeff s

theorem c2OddRecoveredVonMangoldtCoeff_of_odd {m : ℕ} (hm : Odd m) :
    c2OddRecoveredVonMangoldtCoeff m = (ArithmeticFunction.vonMangoldt m : ℂ) := by
  have hunit : IsUnit ((m : ZMod 2)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact hm.coprime_two_right
  rw [c2OddRecoveredVonMangoldtCoeff, c2OddPrincipalChar, Pi.mul_apply,
    MulChar.one_apply hunit, one_mul]

theorem c2OddRecoveredVonMangoldtCoeff_of_not_odd {m : ℕ} (hm : ¬ Odd m) :
    c2OddRecoveredVonMangoldtCoeff m = 0 := by
  have hnonunit : ¬ IsUnit ((m : ZMod 2)) := by
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_two_right]
    exact hm
  rw [c2OddRecoveredVonMangoldtCoeff, c2OddPrincipalChar, Pi.mul_apply,
    MulChar.map_nonunit _ hnonunit, zero_mul]

theorem c2OddRecoveredVonMangoldtCoeff_from_pushforward {m : ℕ} (hm : Odd m) :
    Filter.Tendsto (fun M : ℕ => ((pushforwardMangoldtApprox M m : ℝ) : ℂ))
      Filter.atTop (nhds (c2OddRecoveredVonMangoldtCoeff m)) := by
  rw [c2OddRecoveredVonMangoldtCoeff_of_odd hm]
  exact (Complex.continuous_ofReal.tendsto (ArithmeticFunction.vonMangoldt m)).comp
    (pushforwardMangoldtApprox_tendsto_vonMangoldt (m := m) hm)

theorem c2OddRecoveredVonMangoldtLSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable c2OddRecoveredVonMangoldtCoeff s := by
  simpa [c2OddRecoveredVonMangoldtCoeff, c2OddPrincipalChar] using
    (DirichletCharacter.LSeriesSummable_twist_vonMangoldt
      (χ := (1 : DirichletCharacter ℂ 2)) (s := s) hs)

theorem c2OddRecoveredVonMangoldtLSeries_eq_logDeriv_channel {s : ℂ} (hs : 1 < s.re) :
    c2OddRecoveredVonMangoldtLSeries s =
      - deriv (L ↗c2OddPrincipalChar) s / L ↗c2OddPrincipalChar s := by
  simpa [c2OddRecoveredVonMangoldtLSeries, c2OddRecoveredVonMangoldtCoeff,
    c2OddPrincipalChar] using
    (DirichletCharacter.LSeries_twist_vonMangoldt_eq
      (χ := (1 : DirichletCharacter ℂ 2)) (s := s) hs)

end LeanC2
