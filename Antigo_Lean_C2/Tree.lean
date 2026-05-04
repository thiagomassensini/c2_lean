import Mathlib

namespace LeanC2

/-- The two C2 branch directions. -/
inductive BranchSign where
  | minus
  | plus
deriving DecidableEq, Repr, Fintype

namespace BranchSign

/-- The signed offset attached to a branch. -/
def toInt : BranchSign → ℤ
  | minus => -1
  | plus => 1

@[simp] theorem toInt_minus : toInt BranchSign.minus = -1 := rfl
@[simp] theorem toInt_plus : toInt BranchSign.plus = 1 := rfl

end BranchSign

/-- The descendant produced from an odd core `m` at depth `k`. -/
def descendant (k : ℕ) (ε : BranchSign) (m : ℤ) : ℤ :=
  (2 : ℤ) ^ k * m + ε.toInt

lemma pow_two_ne_zero (k : ℕ) : (2 : ℤ) ^ k ≠ 0 := by
  exact pow_ne_zero k (by norm_num)

lemma four_mul_form (d : ℕ) : (2 : ℤ) ^ (d + 2) = 4 * (2 : ℤ) ^ d := by
  calc
    (2 : ℤ) ^ (d + 2) = (2 : ℤ) ^ d * (2 : ℤ) ^ 2 := by
      rw [pow_add]
    _ = (2 : ℤ) ^ d * 4 := by norm_num
    _ = 4 * (2 : ℤ) ^ d := by ring

lemma even_two_pow_mul (d : ℕ) (m : ℤ) : Even ((2 : ℤ) ^ (d + 1) * m) := by
  refine ⟨(2 : ℤ) ^ d * m, by
    rw [pow_succ']
    ring⟩

lemma odd_not_even {m : ℤ} (hm : Odd m) : ¬ Even m := by
  rintro ⟨a, ha⟩
  rcases hm with ⟨b, hb⟩
  omega

lemma same_depth_same_sign_injective {k : ℕ} {m m' : ℤ} {ε : BranchSign}
    (h : descendant k ε m = descendant k ε m') :
    m = m' := by
  have hMul : (2 : ℤ) ^ k * m = (2 : ℤ) ^ k * m' := by
    cases ε <;> simpa [descendant] using h
  exact mul_left_cancel₀ (pow_two_ne_zero k) hMul

lemma same_depth_opposite_sign_ne {k : ℕ} (hk : 2 ≤ k) {m m' : ℤ} :
    descendant k BranchSign.minus m ≠ descendant k BranchSign.plus m' := by
  intro h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hDesc : (2 : ℤ) ^ (2 + d) * m + -1 = (2 : ℤ) ^ (2 + d) * m' + 1 := by
    simpa [descendant] using h
  have hEq' : (2 : ℤ) ^ (d + 2) * (m - m') = 2 := by
    have h' := congrArg (fun z => z + 1 - ((2 : ℤ) ^ (2 + d) * m')) hDesc
    calc
      (2 : ℤ) ^ (d + 2) * (m - m') = (2 : ℤ) ^ (d + 2) * m - (2 : ℤ) ^ (d + 2) * m' := by
        ring
      _ = 2 := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
  have hDivPow : (4 : ℤ) ∣ (2 : ℤ) ^ (d + 2) := by
    refine ⟨(2 : ℤ) ^ d, ?_⟩
    simpa [mul_comm] using four_mul_form d
  have hDivL : (4 : ℤ) ∣ (2 : ℤ) ^ (d + 2) * (m - m') :=
    dvd_mul_of_dvd_left hDivPow (m - m')
  have hDivR : (4 : ℤ) ∣ 2 := by
    rw [← hEq']
    exact hDivL
  norm_num at hDivR

lemma same_depth_address_unique {k : ℕ} (hk : 2 ≤ k) {m m' : ℤ} {ε ε' : BranchSign}
    (h : descendant k ε m = descendant k ε' m') :
    ε = ε' ∧ m = m' := by
  cases ε <;> cases ε'
  · exact ⟨rfl, same_depth_same_sign_injective h⟩
  · exfalso
    exact same_depth_opposite_sign_ne hk h
  · exfalso
    exact same_depth_opposite_sign_ne hk h.symm
  · exact ⟨rfl, same_depth_same_sign_injective h⟩

lemma different_depth_same_sign_ne {k k' : ℕ} (hkk' : k < k')
    {m m' : ℤ} (hm : Odd m) {ε : BranchSign} :
    descendant k ε m ≠ descendant k' ε m' := by
  intro h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkk'
  have hNoOffset : (2 : ℤ) ^ k * m = (2 : ℤ) ^ (k + (d + 1)) * m' := by
    cases ε <;> simpa [descendant] using h
  have hCore : m = (2 : ℤ) ^ (d + 1) * m' := by
    have hMul' : (2 : ℤ) ^ k * m = (2 : ℤ) ^ k * ((2 : ℤ) ^ (d + 1) * m') := by
      calc
        (2 : ℤ) ^ k * m = (2 : ℤ) ^ (k + (d + 1)) * m' := hNoOffset
        _ = (2 : ℤ) ^ k * ((2 : ℤ) ^ (d + 1) * m') := by
          rw [pow_add]
          ring
    exact mul_left_cancel₀ (pow_two_ne_zero k) hMul'
  have hmEven : Even m := by
    rw [hCore]
    exact even_two_pow_mul d m'
  exact odd_not_even hm hmEven

lemma different_depth_opposite_sign_ne {k k' : ℕ} (hk : 2 ≤ k) (hkk' : k < k')
    {m m' : ℤ} {ε ε' : BranchSign} (hSign : ε ≠ ε') :
    descendant k ε m ≠ descendant k' ε' m' := by
  intro h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkk'
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hk
  cases ε <;> cases ε'
  · contradiction
  · have hEq : (2 : ℤ) ^ (e + 2) * (m - (2 : ℤ) ^ (d + 1) * m') = 2 := by
      have hDesc :
          (2 : ℤ) ^ (2 + e) * m + -1 = (2 : ℤ) ^ (2 + e + d + 1) * m' + 1 := by
        simpa [descendant] using h
      have h' := congrArg (fun z => z + 1 - ((2 : ℤ) ^ (2 + e + d + 1) * m')) hDesc
      calc
        (2 : ℤ) ^ (e + 2) * (m - (2 : ℤ) ^ (d + 1) * m') =
            (2 : ℤ) ^ (e + 2) * m - (2 : ℤ) ^ (e + 2 + (d + 1)) * m' := by
              rw [mul_sub, pow_add]
              ring
        _ = 2 := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
    have hDivPow : (4 : ℤ) ∣ (2 : ℤ) ^ (e + 2) := by
      refine ⟨(2 : ℤ) ^ e, ?_⟩
      simpa [mul_comm] using four_mul_form e
    have hDivL : (4 : ℤ) ∣ (2 : ℤ) ^ (e + 2) * (m - (2 : ℤ) ^ (d + 1) * m') :=
      dvd_mul_of_dvd_left hDivPow (m - (2 : ℤ) ^ (d + 1) * m')
    have hDivR : (4 : ℤ) ∣ 2 := by
      rw [← hEq]
      exact hDivL
    norm_num at hDivR
  · have hEq : (2 : ℤ) ^ (e + 2) * (m - (2 : ℤ) ^ (d + 1) * m') = -2 := by
      have hDesc :
          (2 : ℤ) ^ (2 + e) * m + 1 = (2 : ℤ) ^ (2 + e + d + 1) * m' + -1 := by
        simpa [descendant] using h
      have h' := congrArg (fun z => z - 1 - ((2 : ℤ) ^ (2 + e + d + 1) * m')) hDesc
      calc
        (2 : ℤ) ^ (e + 2) * (m - (2 : ℤ) ^ (d + 1) * m') =
            (2 : ℤ) ^ (e + 2) * m - (2 : ℤ) ^ (e + 2 + (d + 1)) * m' := by
              rw [mul_sub, pow_add]
              ring
        _ = -2 := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
    have hDivPow : (4 : ℤ) ∣ (2 : ℤ) ^ (e + 2) := by
      refine ⟨(2 : ℤ) ^ e, ?_⟩
      simpa [mul_comm] using four_mul_form e
    have hDivL : (4 : ℤ) ∣ (2 : ℤ) ^ (e + 2) * (m - (2 : ℤ) ^ (d + 1) * m') :=
      dvd_mul_of_dvd_left hDivPow (m - (2 : ℤ) ^ (d + 1) * m')
    have hDivR : (4 : ℤ) ∣ (-2 : ℤ) := by
      rw [← hEq]
      exact hDivL
    norm_num at hDivR
  · contradiction

theorem descendant_address_unique {k k' : ℕ} (hk : 2 ≤ k) (hk' : 2 ≤ k')
    {m m' : ℤ} (hm : Odd m) (hm' : Odd m') {ε ε' : BranchSign}
    (h : descendant k ε m = descendant k' ε' m') :
    k = k' ∧ ε = ε' ∧ m = m' := by
  rcases lt_trichotomy k k' with hlt | rfl | hgt
  · exfalso
    by_cases hSign : ε = ε'
    · exact different_depth_same_sign_ne hlt hm (hSign ▸ h)
    · exact different_depth_opposite_sign_ne hk hlt hSign h
  · rcases same_depth_address_unique hk h with ⟨hε, hmEq⟩
    exact ⟨rfl, hε, hmEq⟩
  · exfalso
    by_cases hSign : ε = ε'
    · exact different_depth_same_sign_ne hgt hm' (hSign ▸ h.symm)
    · have hSign' : ε' ≠ ε := by simpa [eq_comm] using hSign
      exact different_depth_opposite_sign_ne hk' hgt hSign' h.symm

/-- The C2 descendants of a core, ignoring the cutoff. -/
def descendantSet (m : ℤ) : Set ℤ :=
  {n | ∃ k ≥ 2, ∃ ε : BranchSign, descendant k ε m = n}

theorem disjoint_descendantSets {m m' : ℤ} (hm : Odd m) (hm' : Odd m')
    (hmm' : m ≠ m') :
    Disjoint (descendantSet m) (descendantSet m') := by
  refine Set.disjoint_left.2 ?_
  intro n hn hn'
  rcases hn with ⟨k, hk, ε, hε⟩
  rcases hn' with ⟨k', hk', ε', hε'⟩
  rcases descendant_address_unique hk hk' hm hm' (hε.trans hε'.symm) with ⟨_, _, hmEq⟩
  exact hmm' hmEq

/-- Natural-number descendant used for finite cutoffs. -/
def natDescendant (k : ℕ) (ε : BranchSign) (m : ℕ) : ℕ :=
  match ε with
  | BranchSign.minus => 2 ^ k * m - 1
  | BranchSign.plus => 2 ^ k * m + 1

lemma one_le_of_nat_odd {m : ℕ} (hm : Odd m) : 1 ≤ m := by
  rcases hm with ⟨t, rfl⟩
  omega

lemma natDescendant_mono (k : ℕ) (ε : BranchSign) {m m' : ℕ} (hmm' : m ≤ m') :
    natDescendant k ε m ≤ natDescendant k ε m' := by
  cases ε
  · exact Nat.sub_le_sub_right (Nat.mul_le_mul_left _ hmm') 1
  · exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hmm') 1

/-- Finite C2 row support up to the cutoff `M`. -/
def rowSupport (M m : ℕ) : Finset (ℕ × BranchSign) :=
  ((Finset.range (M + 1)).product Finset.univ).filter fun p =>
    2 ≤ p.1 ∧ natDescendant p.1 p.2 m ≤ M

lemma mem_rowSupport_iff {M m : ℕ} {p : ℕ × BranchSign} :
    p ∈ rowSupport M m ↔ p.1 < M + 1 ∧ 2 ≤ p.1 ∧ natDescendant p.1 p.2 m ≤ M := by
  classical
  simp [rowSupport]

lemma rowSupport_subset_at_one {M m : ℕ} (hm : Odd m) :
    rowSupport M m ⊆ rowSupport M 1 := by
  intro p hp
  rcases (mem_rowSupport_iff.mp hp) with ⟨hpRange, hpDepth, hpCutoff⟩
  refine mem_rowSupport_iff.mpr ⟨hpRange, hpDepth, ?_⟩
  have hm1 : 1 ≤ m := one_le_of_nat_odd hm
  have hmono : natDescendant p.1 p.2 1 ≤ natDescendant p.1 p.2 m :=
    natDescendant_mono p.1 p.2 hm1
  exact le_trans hmono hpCutoff

/-- Row mass with generic nonnegative depth weights. -/
def rowMass (M : ℕ) (w : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ p ∈ rowSupport M m, w p.1

theorem rowMass_le_rowMass_one {M m : ℕ} (hm : Odd m) {w : ℕ → ℝ}
    (hw : ∀ k, 0 ≤ w k) :
    rowMass M w m ≤ rowMass M w 1 := by
  classical
  unfold rowMass
  exact Finset.sum_le_sum_of_subset_of_nonneg (rowSupport_subset_at_one hm) <| by
    intro p hp1 hp0
    exact hw p.1


end LeanC2
