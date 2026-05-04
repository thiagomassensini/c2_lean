import Mathlib
import LeanC2.Operators.Branch
import LeanC2.Operators.Genuine

set_option linter.style.whitespace false

namespace LeanC2

open scoped BigOperators

lemma twoPowNatCast_cpow_neg (s : Complex) (k : Nat) :
    (((2 ^ k : Nat) : Complex) ^ (-s)) = (((2 : Complex) ^ (-s)) ^ k) := by
  calc
    (((2 ^ k : Nat) : Complex) ^ (-s)) = ((((2 : Nat) : Complex) ^ k) ^ (-s)) := by
      rw [Nat.cast_pow]
    _ = ((2 : Complex) ^ (((k : Nat) : Complex) * (-s))) := by
      simpa using (Complex.natCast_cpow_natCast_mul 2 k (-s)).symm
    _ = ((2 : Complex) ^ ((-s) * k)) := by
      rw [mul_comm]
    _ = (((2 : Complex) ^ (-s)) ^ k) := by
      rw [Complex.cpow_mul_nat]

theorem centerTerm_eq_shellRatio_pow_mul_oddCore (s : Complex) (k m : Nat) :
    centerTerm s k m =
      ((2 : Complex) * shellRatio s ^ k) *
        ((((oddCore m : Nat) : Complex) ^ (-s))) := by
  unfold centerTerm shellRatio dyadicComplexWeight centerNat
  rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  rw [twoPowNatCast_cpow_neg]
  calc
    (2 : Complex) * (((1 : Complex) / 2) ^ k) *
        ((((2 : Complex) ^ (-s)) ^ k) * ((((oddCore m : Nat) : Complex) ^ (-s))))
        = (2 : Complex) *
            ((((1 : Complex) / 2) ^ k) * (((2 : Complex) ^ (-s)) ^ k)) *
              ((((oddCore m : Nat) : Complex) ^ (-s))) := by ring
    _ = (2 : Complex) * ((((1 : Complex) / 2) * ((2 : Complex) ^ (-s))) ^ k) *
          ((((oddCore m : Nat) : Complex) ^ (-s))) := by
            rw [← mul_pow]
        _ = ((2 : Complex) * shellRatio s ^ k) *
          ((((oddCore m : Nat) : Complex) ^ (-s))) := by
          simp [shellRatio, mul_assoc]

lemma depthWindow_eq_Ico_succ (K : Nat) : depthWindow K = Finset.Ico 2 (K + 1) := by
  ext k
  simp [depthWindow]

/--
Exact factorization of the finite center channel into a geometric shell factor times the odd core.
-/
theorem centerPartial_eq_centerCoeffPartial_mul_oddCore (s : Complex) (K m : Nat) :
    centerPartial s K m =
      centerCoeffPartial s K * ((((oddCore m : Nat) : Complex) ^ (-s))) := by
  unfold centerPartial centerCoeffPartial
  calc
    ∑ k ∈ depthWindow K, centerTerm s k m
        = ∑ k ∈ depthWindow K,
            ((2 : Complex) * shellRatio s ^ k) * ((((oddCore m : Nat) : Complex) ^ (-s))) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              exact centerTerm_eq_shellRatio_pow_mul_oddCore s k m
    _ = (∑ k ∈ depthWindow K, (2 : Complex) * shellRatio s ^ k) *
          ((((oddCore m : Nat) : Complex) ^ (-s))) := by
            rw [Finset.sum_mul]
    _ = centerCoeffPartial s K * ((((oddCore m : Nat) : Complex) ^ (-s))) := by
          rfl

/-- Closed form of the finite geometric shell coefficient. -/
theorem centerCoeffPartial_eq_geometric (s : Complex) {K : Nat} (hK : 2 <= K)
    (hq : shellRatio s ≠ 1) :
    centerCoeffPartial s K =
      (2 : Complex) * ((shellRatio s ^ 2 - shellRatio s ^ (K + 1)) / (1 - shellRatio s)) := by
  unfold centerCoeffPartial
  rw [depthWindow_eq_Ico_succ]
  rw [← Finset.mul_sum]
  rw [geom_sum_Ico' hq (by omega)]

/--
Finite sum over odd cores: the center channel separates into shell coefficient times odd zeta
partial.
-/
theorem sum_centerPartial_eq_centerCoeffPartial_mul_oddZetaPartial
    (s : Complex) (K M : Nat) :
    ∑ m ∈ Finset.range M, centerPartial s K m = centerCoeffPartial s K * oddZetaPartial s M := by
  unfold oddZetaPartial
  calc
    ∑ m ∈ Finset.range M, centerPartial s K m
        = ∑ m ∈ Finset.range M,
            centerCoeffPartial s K * ((((oddCore m : Nat) : Complex) ^ (-s))) := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              exact centerPartial_eq_centerCoeffPartial_mul_oddCore s K m
    _ = centerCoeffPartial s K *
          ∑ m ∈ Finset.range M, ((((oddCore m : Nat) : Complex) ^ (-s))) := by
            rw [← Finset.mul_sum]
    _ = centerCoeffPartial s K * oddZetaPartial s M := by
          rfl

/-- Exact one-shell cancellation: the two legs minus the bracket leave only the center. -/
theorem legPair_sub_bracket_eq_centerTerm (s : Complex) (k m : Nat) :
    legPairTerm s k m - bracketTerm s k m = centerTerm s k m := by
  unfold legPairTerm legTerm bracketTerm centerTerm dyadicComplexWeight
  ring

/-- Equivalent one-shell form with the bracket moved to the right-hand side. -/
theorem legPair_eq_bracket_add_centerTerm (s : Complex) (k m : Nat) :
    legPairTerm s k m = bracketTerm s k m + centerTerm s k m := by
  unfold legPairTerm legTerm bracketTerm centerTerm dyadicComplexWeight
  ring

/-- Finite-depth exact cancellation over one odd core. -/
theorem partialFCore_eq_centerPartial (s : Complex) (K m : Nat) :
    partialFCore s K m = centerPartial s K m := by
  unfold partialFCore partialDCore partialBCore centerPartial depthWindow
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro k hk
  exact legPair_sub_bracket_eq_centerTerm s k m

/-- Same finite cancellation rewritten as `D = B + center`. -/
theorem partialDCore_eq_partialBCore_add_centerPartial (s : Complex) (K m : Nat) :
    partialDCore s K m = partialBCore s K m + centerPartial s K m := by
  have h : partialDCore s K m - partialBCore s K m = centerPartial s K m :=
    partialFCore_eq_centerPartial s K m
  have h' : partialDCore s K m = centerPartial s K m + partialBCore s K m :=
    (sub_eq_iff_eq_add.mp h)
  simpa [add_comm] using h'

/-- Rota K finite algebraic core of Thm 13 before taking infinite limits. -/
theorem routeK_thm13_core_finite (s : Complex) (K m : Nat) :
    partialDCore s K m - partialBCore s K m = centerPartial s K m :=
  partialFCore_eq_centerPartial s K m

/--
Finite Thm 13 core: after exact cancellation, the finite numerator is shell-factor times odd
zeta partial.
-/
theorem finiteNumerator_sum_eq_centerCoeffPartial_mul_oddZetaPartial
    (s : Complex) (K M : Nat) :
    ∑ m ∈ Finset.range M, partialFCore s K m =
      centerCoeffPartial s K * oddZetaPartial s M := by
  calc
    ∑ m ∈ Finset.range M, partialFCore s K m
        = ∑ m ∈ Finset.range M, centerPartial s K m := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            exact partialFCore_eq_centerPartial s K m
    _ = centerCoeffPartial s K * oddZetaPartial s M := by
          exact sum_centerPartial_eq_centerCoeffPartial_mul_oddZetaPartial s K M

/-- Rota K finite geometric factorization of the numerator into shell and odd-zeta pieces. -/
theorem routeK_thm13_geometric_factorization_finite (s : Complex) (K M : Nat) :
    ∑ m ∈ Finset.range M, partialFCore s K m =
      centerCoeffPartial s K * oddZetaPartial s M :=
  finiteNumerator_sum_eq_centerCoeffPartial_mul_oddZetaPartial s K M

/-!
Bridge from branch quantities to genuine C2 channels.

Primary sources:
- docs/c2_operador_ramo_invariancia_t_ponte_genuine.md

Legacy seeds:
- Lean/Antigo_Lean_C2/Chain.lean
- Lean/Antigo_Lean_C2/OperatorNorm.lean
-/

end LeanC2