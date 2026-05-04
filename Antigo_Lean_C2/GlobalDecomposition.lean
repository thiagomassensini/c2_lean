import LeanC2.Tree

namespace LeanC2

/-- The three global C2 positions: left neighbor, dyadic center, right neighbor. -/
inductive GlobalSign where
  | minus
  | center
  | plus
deriving DecidableEq, Repr, Fintype

namespace GlobalSign

/-- The signed offset attached to a global address. -/
def toInt : GlobalSign → ℤ
  | minus => -1
  | center => 0
  | plus => 1

/-- Restrict a side branch sign to the corresponding global sign. -/
def ofBranchSign : BranchSign → GlobalSign
  | BranchSign.minus => GlobalSign.minus
  | BranchSign.plus => GlobalSign.plus

@[simp] theorem toInt_minus : toInt GlobalSign.minus = -1 := rfl
@[simp] theorem toInt_center : toInt GlobalSign.center = 0 := rfl
@[simp] theorem toInt_plus : toInt GlobalSign.plus = 1 := rfl

@[simp] theorem ofBranchSign_minus : ofBranchSign BranchSign.minus = GlobalSign.minus := rfl
@[simp] theorem ofBranchSign_plus : ofBranchSign BranchSign.plus = GlobalSign.plus := rfl

end GlobalSign

/-- Natural-number realization of the global C2 address. -/
def globalNatDescendant (k : ℕ) (ε : GlobalSign) (m : ℕ) : ℕ :=
  match ε with
  | GlobalSign.minus => 2 ^ k * m - 1
  | GlobalSign.center => 2 ^ k * m
  | GlobalSign.plus => 2 ^ k * m + 1

/-- Global C2 address on all positive integers. -/
structure GlobalAddress where
  depth : ℕ
  core : ℕ
  sign : GlobalSign
deriving DecidableEq, Repr

namespace GlobalAddress

/-- Evaluate a global address as a natural number. -/
def eval (a : GlobalAddress) : ℕ :=
  globalNatDescendant a.depth a.sign a.core

/-- Valid global addresses are dyadic centers, the two odd side branches above depth `2`,
and the seed `(1, 1, -1)`. -/
def Valid (a : GlobalAddress) : Prop :=
  Odd a.core ∧
    match a.sign with
    | GlobalSign.center => 1 ≤ a.depth
    | GlobalSign.plus => 2 ≤ a.depth
    | GlobalSign.minus => (a.depth = 1 ∧ a.core = 1) ∨ 2 ≤ a.depth

@[simp] theorem eval_mk (k m ε) : eval ⟨k, m, ε⟩ = globalNatDescendant k ε m := rfl

@[simp] theorem valid_center_iff {k m : ℕ} :
    Valid ⟨k, m, GlobalSign.center⟩ ↔ Odd m ∧ 1 ≤ k := by
  rfl

@[simp] theorem valid_plus_iff {k m : ℕ} :
    Valid ⟨k, m, GlobalSign.plus⟩ ↔ Odd m ∧ 2 ≤ k := by
  rfl

@[simp] theorem valid_minus_iff {k m : ℕ} :
    Valid ⟨k, m, GlobalSign.minus⟩ ↔ Odd m ∧ ((k = 1 ∧ m = 1) ∨ 2 ≤ k) := by
  rfl

end GlobalAddress

lemma odd_int_of_nat {n : ℕ} (hn : Odd n) : Odd (n : ℤ) := by
  rcases hn with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  exact_mod_cast hk

lemma odd_nat_not_even {n : ℕ} (hn : Odd n) : ¬ Even n :=
  Nat.not_even_iff_odd.mpr hn

@[simp] lemma globalNatDescendant_seed : globalNatDescendant 1 GlobalSign.minus 1 = 1 := by
  simp [globalNatDescendant]

lemma globalNatDescendant_center_even {k m : ℕ} (hk : 1 ≤ k) :
    Even (globalNatDescendant k GlobalSign.center m) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨2 ^ d * m, ?_⟩
  dsimp [globalNatDescendant]
  rw [Nat.add_comm 1 d, pow_succ']
  ring

lemma globalNatDescendant_plus_odd {k m : ℕ} (hk : 1 ≤ k) :
    Odd (globalNatDescendant k GlobalSign.plus m) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨2 ^ d * m, ?_⟩
  dsimp [globalNatDescendant]
  rw [Nat.add_comm 1 d, pow_succ']
  ring

lemma globalNatDescendant_minus_odd {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    Odd (globalNatDescendant k GlobalSign.minus m) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨2 ^ d * m - 1, ?_⟩
  have hmPos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  have hprod : 0 < 2 ^ d * m := Nat.mul_pos (pow_pos (by decide) d) hmPos
  have hle : 1 ≤ 2 ^ d * m := Nat.succ_le_of_lt hprod
  set a := 2 ^ d * m with ha
  have hleA : 1 ≤ a := by simpa [ha] using hle
  dsimp [globalNatDescendant]
  rw [Nat.add_comm 1 d, pow_succ']
  have hrepr : 2 * 2 ^ d * m = 2 * a := by
    simp [ha, Nat.mul_left_comm, Nat.mul_comm]
  rw [hrepr]
  change 2 * a - 1 = 2 * (a - 1) + 1
  omega

lemma globalNatDescendant_plus_ge_three {k m : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m) :
    3 ≤ globalNatDescendant k GlobalSign.plus m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hpow1 : 1 ≤ 2 ^ d := Nat.succ_le_of_lt (pow_pos (by decide) d)
  have hpow4 : 4 ≤ 2 ^ (2 + d) := by
    rw [Nat.add_comm 2 d, pow_add]
    norm_num
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul_left 4 hpow1
  have hmul : 4 ≤ 2 ^ (2 + d) * m := by
    calc
      4 = 4 * 1 := by simp
      _ ≤ 4 * m := Nat.mul_le_mul_left 4 hm
      _ ≤ 2 ^ (2 + d) * m := Nat.mul_le_mul_right m hpow4
  have hfive : 5 ≤ globalNatDescendant (2 + d) GlobalSign.plus m := by
    simpa [globalNatDescendant] using Nat.succ_le_succ hmul
  exact le_trans (by decide : 3 ≤ 5) hfive

lemma globalNatDescendant_minus_ge_three {k m : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m) :
    3 ≤ globalNatDescendant k GlobalSign.minus m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hpow1 : 1 ≤ 2 ^ d := Nat.succ_le_of_lt (pow_pos (by decide) d)
  have hpow4 : 4 ≤ 2 ^ (2 + d) := by
    rw [Nat.add_comm 2 d, pow_add]
    norm_num
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul_left 4 hpow1
  have hmul : 4 ≤ 2 ^ (2 + d) * m := by
    calc
      4 = 4 * 1 := by simp
      _ ≤ 4 * m := Nat.mul_le_mul_left 4 hm
      _ ≤ 2 ^ (2 + d) * m := Nat.mul_le_mul_right m hpow4
  simpa [globalNatDescendant] using Nat.sub_le_sub_right hmul 1

lemma center_address_unique {k k' : ℕ} (hk : 1 ≤ k) (hk' : 1 ≤ k')
    {m m' : ℕ} (hm : Odd m) (hm' : Odd m')
    (h : globalNatDescendant k GlobalSign.center m = globalNatDescendant k' GlobalSign.center m') :
    k = k' ∧ m = m' := by
  have hInt : (2 : ℤ) ^ k * m = (2 : ℤ) ^ k' * m' := by
    exact_mod_cast h
  have hmz : Odd (m : ℤ) := odd_int_of_nat hm
  have hmz' : Odd (m' : ℤ) := odd_int_of_nat hm'
  rcases lt_trichotomy k k' with hlt | rfl | hgt
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have hCore : (m : ℤ) = (2 : ℤ) ^ (d + 1) * m' := by
      have hMul' : (2 : ℤ) ^ k * m = (2 : ℤ) ^ k * ((2 : ℤ) ^ (d + 1) * m') := by
        calc
          (2 : ℤ) ^ k * m = (2 : ℤ) ^ (k + (d + 1)) * m' := by simpa using hInt
          _ = (2 : ℤ) ^ k * ((2 : ℤ) ^ (d + 1) * m') := by
            rw [pow_add]
            ring
      exact mul_left_cancel₀ (pow_two_ne_zero k) hMul'
    have hmEven : Even (m : ℤ) := by
      rw [hCore]
      exact even_two_pow_mul d m'
    exact odd_not_even hmz hmEven
  · have hmEqInt : (m : ℤ) = m' := by
      have hMul : (2 : ℤ) ^ k * m = (2 : ℤ) ^ k * m' := by simpa using hInt
      exact mul_left_cancel₀ (pow_two_ne_zero k) hMul
    exact ⟨rfl, by exact_mod_cast hmEqInt⟩
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    have hCore : (m' : ℤ) = (2 : ℤ) ^ (d + 1) * m := by
      have hMul' : (2 : ℤ) ^ k' * m' = (2 : ℤ) ^ k' * ((2 : ℤ) ^ (d + 1) * m) := by
        calc
          (2 : ℤ) ^ k' * m' = (2 : ℤ) ^ (k' + (d + 1)) * m := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInt.symm
          _ = (2 : ℤ) ^ k' * ((2 : ℤ) ^ (d + 1) * m) := by
            rw [pow_add]
            ring
      exact mul_left_cancel₀ (pow_two_ne_zero k') hMul'
    have hmEven : Even (m' : ℤ) := by
      rw [hCore]
      exact even_two_pow_mul d m
    exact odd_not_even hmz' hmEven

lemma natCast_globalNatDescendant_ofBranchSign {k : ℕ} {ε : BranchSign} {m : ℕ}
    (hm : 1 ≤ m) :
    (globalNatDescendant k (GlobalSign.ofBranchSign ε) m : ℤ) = descendant k ε m := by
  cases ε
  · have hmPos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
    have hge : 1 ≤ 2 ^ k * m := by
      exact Nat.succ_le_of_lt (Nat.mul_pos (pow_pos (by decide) k) hmPos)
    simp [globalNatDescendant, GlobalSign.ofBranchSign, descendant,
      BranchSign.toInt_minus, Int.ofNat_sub hge]
    ring
  · simp [globalNatDescendant, GlobalSign.ofBranchSign, descendant]

lemma side_address_unique {k k' : ℕ} (hk : 2 ≤ k) (hk' : 2 ≤ k')
    {m m' : ℕ} (hm : Odd m) (hm' : Odd m') {ε ε' : BranchSign}
    (h : globalNatDescendant k (GlobalSign.ofBranchSign ε) m =
        globalNatDescendant k' (GlobalSign.ofBranchSign ε') m') :
    k = k' ∧ ε = ε' ∧ m = m' := by
  have hmPos : 1 ≤ m := one_le_of_nat_odd hm
  have hmPos' : 1 ≤ m' := one_le_of_nat_odd hm'
  have hInt : descendant k ε (m : ℤ) = descendant k' ε' (m' : ℤ) := by
    calc
      descendant k ε (m : ℤ) = (globalNatDescendant k (GlobalSign.ofBranchSign ε) m : ℤ) := by
        symm
        exact natCast_globalNatDescendant_ofBranchSign hmPos
      _ = globalNatDescendant k' (GlobalSign.ofBranchSign ε') m' := by
        exact_mod_cast h
      _ = descendant k' ε' (m' : ℤ) := by
        exact natCast_globalNatDescendant_ofBranchSign hmPos'
  have hmz : Odd (m : ℤ) := odd_int_of_nat hm
  have hmz' : Odd (m' : ℤ) := odd_int_of_nat hm'
  rcases descendant_address_unique hk hk' hmz hmz' hInt with ⟨hkk', hε, hmEqInt⟩
  exact ⟨hkk', hε, by exact_mod_cast hmEqInt⟩

/-- Existence of the canonical global C2 address for every positive integer. -/
theorem exists_valid_globalAddress (n : ℕ) (hn : 0 < n) :
    ∃ a : GlobalAddress, a.Valid ∧ a.eval = n := by
  by_cases h1 : n = 1
  · refine ⟨⟨1, 1, GlobalSign.minus⟩, ?_, ?_⟩
    · simp [GlobalAddress.Valid]
    · simp [h1, GlobalAddress.eval, globalNatDescendant]
  · by_cases hEven : Even n
    · obtain ⟨k, m, hm, hdecomp⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.ne_zero_of_lt hn)
      have hk : 1 ≤ k := by
        by_contra hk
        have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
        rw [hk0, pow_zero, one_mul] at hdecomp
        exact odd_nat_not_even hm (hdecomp ▸ hEven)
      refine ⟨⟨k, m, GlobalSign.center⟩, ?_, ?_⟩
      · simpa [GlobalAddress.Valid] using And.intro hm hk
      · exact hdecomp.symm
    · rcases Nat.not_even_iff_odd.mp hEven with ⟨t, rfl⟩
      by_cases htEven : Even t
      · have htPos : 0 < t := by
          by_contra ht0
          have ht0' : t = 0 := Nat.eq_zero_of_not_pos ht0
          apply h1
          rw [ht0']
          omega
        obtain ⟨d, m, hm, ht⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.ne_zero_of_lt htPos)
        have hd : 1 ≤ d := by
          by_contra hd
          have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
          rw [hd0, pow_zero, one_mul] at ht
          exact odd_nat_not_even hm (ht ▸ htEven)
        refine ⟨⟨d + 1, m, GlobalSign.plus⟩, ?_, ?_⟩
        · simpa [GlobalAddress.Valid] using And.intro hm (Nat.succ_le_succ hd)
        · calc
            GlobalAddress.eval ⟨d + 1, m, GlobalSign.plus⟩ = 2 * (2 ^ d * m) + 1 := by
              dsimp [GlobalAddress.eval, globalNatDescendant]
              rw [pow_succ']
              ring
            _ = 2 * t + 1 := by rw [ht]
      · have htOdd : Odd t := Nat.not_even_iff_odd.mp htEven
        obtain ⟨d, m, hm, ht⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.succ_ne_zero t)
        have ht1Even : Even (t + 1) := htOdd.add_one
        have hd : 1 ≤ d := by
          by_contra hd
          have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
          rw [hd0, pow_zero, one_mul] at ht
          exact odd_nat_not_even hm (ht ▸ ht1Even)
        refine ⟨⟨d + 1, m, GlobalSign.minus⟩, ?_, ?_⟩
        · simpa [GlobalAddress.Valid] using And.intro hm (Or.inr (Nat.succ_le_succ hd))
        · have hsucc : GlobalAddress.eval ⟨d + 1, m, GlobalSign.minus⟩ + 1 = 2 * (t + 1) := by
            have hmPos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (one_le_of_nat_odd hm)
            have hle : 1 ≤ 2 ^ d * m := by
              exact Nat.succ_le_of_lt (Nat.mul_pos (pow_pos (by decide) d) hmPos)
            calc
              GlobalAddress.eval ⟨d + 1, m, GlobalSign.minus⟩ + 1 = 2 * (2 ^ d * m) := by
                set a := 2 ^ d * m with ha
                have hleA : 1 ≤ a := by simpa [ha] using hle
                dsimp [GlobalAddress.eval, globalNatDescendant]
                rw [pow_succ']
                have hrepr : 2 * 2 ^ d * m = 2 * a := by
                  simp [ha, Nat.mul_left_comm, Nat.mul_comm]
                rw [hrepr]
                change 2 * a - 1 + 1 = 2 * a
                omega
              _ = 2 * (t + 1) := by rw [← ht]
          omega

/-- Uniqueness of valid global C2 addresses. -/
theorem globalAddress_fields_unique
    {k k' m m' : ℕ} {ε ε' : GlobalSign}
    (ha : GlobalAddress.Valid ⟨k, m, ε⟩) (hb : GlobalAddress.Valid ⟨k', m', ε'⟩)
    (h : globalNatDescendant k ε m = globalNatDescendant k' ε' m') :
    k = k' ∧ ε = ε' ∧ m = m' := by
  cases ε <;> cases ε'
  case minus.minus =>
    rcases GlobalAddress.valid_minus_iff.mp ha with ⟨hm, hminus⟩
    rcases GlobalAddress.valid_minus_iff.mp hb with ⟨hm', hminus'⟩
    cases hminus with
    | inl hseed =>
        rcases hseed with ⟨hk, hm1⟩
        subst hk
        subst hm1
        cases hminus' with
        | inl hseed' =>
            rcases hseed' with ⟨hk', hm1'⟩
            subst hk'
            subst hm1'
            exact ⟨rfl, rfl, rfl⟩
        | inr hk' =>
            exfalso
            have hmPos' : 1 ≤ m' := one_le_of_nat_odd hm'
            have hge : 3 ≤ globalNatDescendant k' GlobalSign.minus m' :=
              globalNatDescendant_minus_ge_three hk' hmPos'
            have hone : globalNatDescendant k' GlobalSign.minus m' = 1 := by
              simpa [globalNatDescendant] using h.symm
            omega
    | inr hk =>
        cases hminus' with
        | inl hseed' =>
            rcases hseed' with ⟨hk', hm1'⟩
            subst hk'
            subst hm1'
            exfalso
            have hmPos : 1 ≤ m := one_le_of_nat_odd hm
            have hge : 3 ≤ globalNatDescendant k GlobalSign.minus m :=
              globalNatDescendant_minus_ge_three hk hmPos
            have hone : globalNatDescendant k GlobalSign.minus m = 1 := by
              simpa [globalNatDescendant] using h
            omega
        | inr hk' =>
            rcases side_address_unique hk hk' hm hm'
                (ε := BranchSign.minus) (ε' := BranchSign.minus) h with
              ⟨hkk', hε, hmm'⟩
            exact ⟨hkk', by cases hε; rfl, hmm'⟩
  case minus.center =>
    rcases GlobalAddress.valid_minus_iff.mp ha with ⟨hm, hminus⟩
    rcases GlobalAddress.valid_center_iff.mp hb with ⟨hm', hk'⟩
    exfalso
    have hmPos : 1 ≤ m := one_le_of_nat_odd hm
    have hk : 1 ≤ k := by
      cases hminus with
      | inl hseed => omega
      | inr hk => exact le_trans (by decide) hk
    have hOdd : Odd (globalNatDescendant k GlobalSign.minus m) :=
      globalNatDescendant_minus_odd hk hmPos
    have hEven : Even (globalNatDescendant k' GlobalSign.center m') :=
      globalNatDescendant_center_even hk'
    exact (Nat.not_even_iff_odd.mpr hOdd) (h.symm ▸ hEven)
  case minus.plus =>
    rcases GlobalAddress.valid_minus_iff.mp ha with ⟨hm, hminus⟩
    rcases GlobalAddress.valid_plus_iff.mp hb with ⟨hm', hk'⟩
    cases hminus with
    | inl hseed =>
        rcases hseed with ⟨hk, hm1⟩
        subst hk
        subst hm1
        exfalso
        have hmPos' : 1 ≤ m' := one_le_of_nat_odd hm'
        have hge : 3 ≤ globalNatDescendant k' GlobalSign.plus m' :=
          globalNatDescendant_plus_ge_three hk' hmPos'
        have hone : globalNatDescendant k' GlobalSign.plus m' = 1 := by
          simpa [globalNatDescendant] using h.symm
        omega
    | inr hk =>
        rcases side_address_unique hk hk' hm hm'
            (ε := BranchSign.minus) (ε' := BranchSign.plus) h with
          ⟨hkk', hε, hmm'⟩
        exact ⟨hkk', by simpa using congrArg GlobalSign.ofBranchSign hε, hmm'⟩
  case center.minus =>
    rcases GlobalAddress.valid_center_iff.mp ha with ⟨hm, hk⟩
    rcases GlobalAddress.valid_minus_iff.mp hb with ⟨hm', hminus'⟩
    exfalso
    have hmPos' : 1 ≤ m' := one_le_of_nat_odd hm'
    have hk' : 1 ≤ k' := by
      cases hminus' with
      | inl hseed => omega
      | inr hk' => exact le_trans (by decide) hk'
    have hEven : Even (globalNatDescendant k GlobalSign.center m) :=
      globalNatDescendant_center_even hk
    have hOdd : Odd (globalNatDescendant k' GlobalSign.minus m') :=
      globalNatDescendant_minus_odd hk' hmPos'
    exact (Nat.not_even_iff_odd.mpr hOdd) (h ▸ hEven)
  case center.center =>
    rcases GlobalAddress.valid_center_iff.mp ha with ⟨hm, hk⟩
    rcases GlobalAddress.valid_center_iff.mp hb with ⟨hm', hk'⟩
    rcases center_address_unique hk hk' hm hm' h with ⟨hkk', hmm'⟩
    exact ⟨hkk', rfl, hmm'⟩
  case center.plus =>
    rcases GlobalAddress.valid_center_iff.mp ha with ⟨hm, hk⟩
    rcases GlobalAddress.valid_plus_iff.mp hb with ⟨hm', hk'⟩
    exfalso
    have hEven : Even (globalNatDescendant k GlobalSign.center m) :=
      globalNatDescendant_center_even hk
    have hOdd : Odd (globalNatDescendant k' GlobalSign.plus m') :=
      globalNatDescendant_plus_odd (le_trans (by decide) hk')
    exact (Nat.not_even_iff_odd.mpr hOdd) (h ▸ hEven)
  case plus.minus =>
    rcases GlobalAddress.valid_plus_iff.mp ha with ⟨hm, hk⟩
    rcases GlobalAddress.valid_minus_iff.mp hb with ⟨hm', hminus'⟩
    cases hminus' with
    | inl hseed' =>
        rcases hseed' with ⟨hk', hm1'⟩
        subst hk'
        subst hm1'
        exfalso
        have hmPos : 1 ≤ m := one_le_of_nat_odd hm
        have hge : 3 ≤ globalNatDescendant k GlobalSign.plus m :=
          globalNatDescendant_plus_ge_three hk hmPos
        have hone : globalNatDescendant k GlobalSign.plus m = 1 := by
          simpa [globalNatDescendant] using h
        omega
    | inr hk' =>
        rcases side_address_unique hk hk' hm hm'
            (ε := BranchSign.plus) (ε' := BranchSign.minus) h with
          ⟨hkk', hε, hmm'⟩
        exact ⟨hkk', by simpa using congrArg GlobalSign.ofBranchSign hε, hmm'⟩
  case plus.center =>
    rcases GlobalAddress.valid_plus_iff.mp ha with ⟨hm, hk⟩
    rcases GlobalAddress.valid_center_iff.mp hb with ⟨hm', hk'⟩
    exfalso
    have hOdd : Odd (globalNatDescendant k GlobalSign.plus m) :=
      globalNatDescendant_plus_odd (le_trans (by decide) hk)
    have hEven : Even (globalNatDescendant k' GlobalSign.center m') :=
      globalNatDescendant_center_even hk'
    exact (Nat.not_even_iff_odd.mpr hOdd) (h.symm ▸ hEven)
  case plus.plus =>
    rcases GlobalAddress.valid_plus_iff.mp ha with ⟨hm, hk⟩
    rcases GlobalAddress.valid_plus_iff.mp hb with ⟨hm', hk'⟩
    rcases side_address_unique hk hk' hm hm'
        (ε := BranchSign.plus) (ε' := BranchSign.plus) h with
      ⟨hkk', hε, hmm'⟩
    exact ⟨hkk', by cases hε; rfl, hmm'⟩

theorem globalAddress_eq_of_same_eval {a b : GlobalAddress}
    (ha : a.Valid) (hb : b.Valid) (h : a.eval = b.eval) :
    a = b := by
  rcases a with ⟨k, m, ε⟩
  rcases b with ⟨k', m', ε'⟩
  rcases globalAddress_fields_unique ha hb h with ⟨hkk', hε, hmm'⟩
  cases hkk'
  cases hε
  cases hmm'
  rfl

/-- Global C2 decomposition: every positive integer has a unique valid global address. -/
theorem existsUnique_valid_globalAddress (n : ℕ) (hn : 0 < n) :
    ∃! a : GlobalAddress, a.Valid ∧ a.eval = n := by
  rcases exists_valid_globalAddress n hn with ⟨a, haValid, haEval⟩
  refine ⟨a, ⟨haValid, haEval⟩, ?_⟩
  intro b hb
  exact globalAddress_eq_of_same_eval (a := b) (b := a) hb.1 haValid (hb.2.trans haEval.symm)

end LeanC2
