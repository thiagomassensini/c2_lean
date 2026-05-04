import Mathlib
import LeanC2.Foundations.Basic

set_option linter.style.whitespace false

namespace LeanC2

/-- The two C2 branch directions. -/
inductive BranchSign where
  | minus
  | plus
deriving DecidableEq, Repr, Fintype

namespace BranchSign

/-- The signed offset attached to a branch. -/
def toInt : BranchSign -> Int
  | minus => -1
  | plus => 1

@[simp] theorem toInt_minus : toInt BranchSign.minus = -1 := rfl
@[simp] theorem toInt_plus : toInt BranchSign.plus = 1 := rfl

end BranchSign

/-- The descendant produced from an odd core `m` at depth `k`. -/
def descendant (k : Nat) (epsilon : BranchSign) (m : Int) : Int :=
  (2 : Int) ^ k * m + epsilon.toInt

lemma pow_two_ne_zero (k : Nat) : (2 : Int) ^ k ≠ 0 := by
  exact pow_ne_zero k (by norm_num)

lemma four_mul_form (depth : Nat) : (2 : Int) ^ (depth + 2) = 4 * (2 : Int) ^ depth := by
  calc
    (2 : Int) ^ (depth + 2) = (2 : Int) ^ depth * (2 : Int) ^ 2 := by
      rw [pow_add]
    _ = (2 : Int) ^ depth * 4 := by norm_num
    _ = 4 * (2 : Int) ^ depth := by ring

lemma even_two_pow_mul (depth : Nat) (m : Int) : Even ((2 : Int) ^ (depth + 1) * m) := by
  refine ⟨(2 : Int) ^ depth * m, ?_⟩
  rw [pow_succ']
  ring

lemma odd_not_even {m : Int} (hm : Odd m) : ¬ Even m := by
  rintro ⟨a, ha⟩
  rcases hm with ⟨b, hb⟩
  omega

lemma same_depth_same_sign_injective {k : Nat} {m m' : Int} {epsilon : BranchSign}
    (h : descendant k epsilon m = descendant k epsilon m') :
    m = m' := by
  have hMul : (2 : Int) ^ k * m = (2 : Int) ^ k * m' := by
    cases epsilon <;> simpa [descendant] using h
  exact mul_left_cancel₀ (pow_two_ne_zero k) hMul

lemma same_depth_opposite_sign_ne {k : Nat} (hk : 2 <= k) {m m' : Int} :
    descendant k BranchSign.minus m ≠ descendant k BranchSign.plus m' := by
  intro h
  obtain ⟨depth, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hDesc :
      (2 : Int) ^ (2 + depth) * m + -1 = (2 : Int) ^ (2 + depth) * m' + 1 := by
    simpa [descendant] using h
  have hEq' : (2 : Int) ^ (depth + 2) * (m - m') = 2 := by
    have h' := congrArg (fun z => z + 1 - ((2 : Int) ^ (2 + depth) * m')) hDesc
    calc
      (2 : Int) ^ (depth + 2) * (m - m') =
          (2 : Int) ^ (depth + 2) * m - (2 : Int) ^ (depth + 2) * m' := by
        ring
      _ = 2 := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
  have hDivPow : (4 : Int) ∣ (2 : Int) ^ (depth + 2) := by
    refine ⟨(2 : Int) ^ depth, ?_⟩
    simpa [mul_comm] using four_mul_form depth
  have hDivL : (4 : Int) ∣ (2 : Int) ^ (depth + 2) * (m - m') :=
    dvd_mul_of_dvd_left hDivPow (m - m')
  have hDivR : (4 : Int) ∣ 2 := by
    rw [← hEq']
    exact hDivL
  norm_num at hDivR

lemma same_depth_address_unique {k : Nat} (hk : 2 <= k) {m m' : Int} {epsilon epsilon' : BranchSign}
    (h : descendant k epsilon m = descendant k epsilon' m') :
    epsilon = epsilon' ∧ m = m' := by
  cases epsilon <;> cases epsilon'
  · exact ⟨rfl, same_depth_same_sign_injective h⟩
  · exfalso
    exact same_depth_opposite_sign_ne hk h
  · exfalso
    exact same_depth_opposite_sign_ne hk h.symm
  · exact ⟨rfl, same_depth_same_sign_injective h⟩

lemma different_depth_same_sign_ne {k k' : Nat} (hkk' : k < k')
    {m m' : Int} (hm : Odd m) {epsilon : BranchSign} :
    descendant k epsilon m ≠ descendant k' epsilon m' := by
  intro h
  obtain ⟨depth, rfl⟩ := Nat.exists_eq_add_of_lt hkk'
  have hNoOffset : (2 : Int) ^ k * m = (2 : Int) ^ (k + (depth + 1)) * m' := by
    cases epsilon <;> simpa [descendant] using h
  have hCore : m = (2 : Int) ^ (depth + 1) * m' := by
    have hMul' : (2 : Int) ^ k * m = (2 : Int) ^ k * ((2 : Int) ^ (depth + 1) * m') := by
      calc
        (2 : Int) ^ k * m = (2 : Int) ^ (k + (depth + 1)) * m' := hNoOffset
        _ = (2 : Int) ^ k * ((2 : Int) ^ (depth + 1) * m') := by
          rw [pow_add]
          ring
    exact mul_left_cancel₀ (pow_two_ne_zero k) hMul'
  have hmEven : Even m := by
    rw [hCore]
    exact even_two_pow_mul depth m'
  exact odd_not_even hm hmEven

lemma different_depth_opposite_sign_ne {k k' : Nat} (hk : 2 <= k) (hkk' : k < k')
    {m m' : Int} {epsilon epsilon' : BranchSign} (hSign : epsilon ≠ epsilon') :
    descendant k epsilon m ≠ descendant k' epsilon' m' := by
  intro h
  obtain ⟨depth, rfl⟩ := Nat.exists_eq_add_of_lt hkk'
  obtain ⟨base, rfl⟩ := Nat.exists_eq_add_of_le hk
  cases epsilon <;> cases epsilon'
  · contradiction
  · have hEq : (2 : Int) ^ (base + 2) * (m - (2 : Int) ^ (depth + 1) * m') = 2 := by
      have hDesc :
          (2 : Int) ^ (2 + base) * m + -1 = (2 : Int) ^ (2 + base + depth + 1) * m' + 1 := by
        simpa [descendant] using h
      have h' := congrArg (fun z => z + 1 - ((2 : Int) ^ (2 + base + depth + 1) * m')) hDesc
      calc
        (2 : Int) ^ (base + 2) * (m - (2 : Int) ^ (depth + 1) * m') =
            (2 : Int) ^ (base + 2) * m - (2 : Int) ^ (base + 2 + (depth + 1)) * m' := by
              rw [mul_sub, pow_add]
              ring
        _ = 2 := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
    have hDivPow : (4 : Int) ∣ (2 : Int) ^ (base + 2) := by
      refine ⟨(2 : Int) ^ base, ?_⟩
      simpa [mul_comm] using four_mul_form base
    have hDivL : (4 : Int) ∣ (2 : Int) ^ (base + 2) * (m - (2 : Int) ^ (depth + 1) * m') :=
      dvd_mul_of_dvd_left hDivPow (m - (2 : Int) ^ (depth + 1) * m')
    have hDivR : (4 : Int) ∣ 2 := by
      rw [← hEq]
      exact hDivL
    norm_num at hDivR
  · have hEq : (2 : Int) ^ (base + 2) * (m - (2 : Int) ^ (depth + 1) * m') = -2 := by
      have hDesc :
          (2 : Int) ^ (2 + base) * m + 1 = (2 : Int) ^ (2 + base + depth + 1) * m' + -1 := by
        simpa [descendant] using h
      have h' := congrArg (fun z => z - 1 - ((2 : Int) ^ (2 + base + depth + 1) * m')) hDesc
      calc
        (2 : Int) ^ (base + 2) * (m - (2 : Int) ^ (depth + 1) * m') =
            (2 : Int) ^ (base + 2) * m - (2 : Int) ^ (base + 2 + (depth + 1)) * m' := by
              rw [mul_sub, pow_add]
              ring
        _ = -2 := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
    have hDivPow : (4 : Int) ∣ (2 : Int) ^ (base + 2) := by
      refine ⟨(2 : Int) ^ base, ?_⟩
      simpa [mul_comm] using four_mul_form base
    have hDivL : (4 : Int) ∣ (2 : Int) ^ (base + 2) * (m - (2 : Int) ^ (depth + 1) * m') :=
      dvd_mul_of_dvd_left hDivPow (m - (2 : Int) ^ (depth + 1) * m')
    have hDivR : (4 : Int) ∣ (-2 : Int) := by
      rw [← hEq]
      exact hDivL
    norm_num at hDivR
  · contradiction

theorem descendant_address_unique {k k' : Nat} (hk : 2 <= k) (hk' : 2 <= k')
    {m m' : Int} (hm : Odd m) (hm' : Odd m') {epsilon epsilon' : BranchSign}
    (h : descendant k epsilon m = descendant k' epsilon' m') :
    k = k' ∧ epsilon = epsilon' ∧ m = m' := by
  rcases lt_trichotomy k k' with hlt | rfl | hgt
  · exfalso
    by_cases hSign : epsilon = epsilon'
    · exact different_depth_same_sign_ne hlt hm (hSign ▸ h)
    · exact different_depth_opposite_sign_ne hk hlt hSign h
  · rcases same_depth_address_unique hk h with ⟨hEps, hmEq⟩
    exact ⟨rfl, hEps, hmEq⟩
  · exfalso
    by_cases hSign : epsilon = epsilon'
    · exact different_depth_same_sign_ne hgt hm' (hSign ▸ h.symm)
    · have hSign' : epsilon' ≠ epsilon := by simpa [eq_comm] using hSign
      exact different_depth_opposite_sign_ne hk' hgt hSign' h.symm

/-- The C2 descendants of a core, ignoring the cutoff. -/
def descendantSet (m : Int) : Set Int :=
  {n | ∃ k ≥ 2, ∃ epsilon : BranchSign, descendant k epsilon m = n}

theorem disjoint_descendantSets {m m' : Int} (hm : Odd m) (hm' : Odd m')
    (hmm' : m ≠ m') :
    Disjoint (descendantSet m) (descendantSet m') := by
  refine Set.disjoint_left.2 ?_
  intro n hn hn'
  rcases hn with ⟨k, hk, epsilon, hEps⟩
  rcases hn' with ⟨k', hk', epsilon', hEps'⟩
  rcases descendant_address_unique hk hk' hm hm' (hEps.trans hEps'.symm) with ⟨_, _, hmEq⟩
  exact hmm' hmEq

/-- Natural-number descendant used for finite cutoffs. -/
def natDescendant (k : Nat) (epsilon : BranchSign) (m : Nat) : Nat :=
  match epsilon with
  | BranchSign.minus => 2 ^ k * m - 1
  | BranchSign.plus => 2 ^ k * m + 1

lemma one_le_of_nat_odd {m : Nat} (hm : Odd m) : 1 <= m := by
  rcases hm with ⟨t, rfl⟩
  omega

lemma natDescendant_mono (k : Nat) (epsilon : BranchSign) {m m' : Nat} (hmm' : m <= m') :
    natDescendant k epsilon m <= natDescendant k epsilon m' := by
  cases epsilon
  · exact Nat.sub_le_sub_right (Nat.mul_le_mul_left _ hmm') 1
  · exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hmm') 1

/-- Finite C2 row support up to the cutoff `M`. -/
def rowSupport (M m : Nat) : Finset (Nat × BranchSign) :=
  ((Finset.range (M + 1)).product Finset.univ).filter fun p =>
    2 <= p.1 ∧ natDescendant p.1 p.2 m <= M

lemma mem_rowSupport_iff {M m : Nat} {p : Nat × BranchSign} :
    p ∈ rowSupport M m ↔ p.1 < M + 1 ∧ 2 <= p.1 ∧ natDescendant p.1 p.2 m <= M := by
  classical
  simp [rowSupport]

lemma rowSupport_subset_at_one {M m : Nat} (hm : Odd m) :
    rowSupport M m ⊆ rowSupport M 1 := by
  intro p hp
  rcases mem_rowSupport_iff.mp hp with ⟨hpRange, hpDepth, hpCutoff⟩
  refine mem_rowSupport_iff.mpr ⟨hpRange, hpDepth, ?_⟩
  have hm1 : 1 <= m := one_le_of_nat_odd hm
  have hmono : natDescendant p.1 p.2 1 <= natDescendant p.1 p.2 m :=
    natDescendant_mono p.1 p.2 hm1
  exact le_trans hmono hpCutoff

/-- Row mass with generic nonnegative depth weights. -/
def rowMass (M : Nat) (w : Nat -> Real) (m : Nat) : Real :=
  ∑ p ∈ rowSupport M m, w p.1

theorem rowMass_le_rowMass_one {M m : Nat} (hm : Odd m) {w : Nat -> Real}
    (hw : ∀ k, 0 <= w k) :
    rowMass M w m <= rowMass M w 1 := by
  classical
  unfold rowMass
  exact Finset.sum_le_sum_of_subset_of_nonneg (rowSupport_subset_at_one hm) <| by
    intro p hp1 hp0
    exact hw p.1

end LeanC2