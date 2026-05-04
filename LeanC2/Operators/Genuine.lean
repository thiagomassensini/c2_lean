import Mathlib
import LeanC2.Foundations.DyadicArith

set_option linter.style.whitespace false

namespace LeanC2

open scoped BigOperators

/-- Enumerator `0,1,2,... ↦ 1,3,5,...` for positive odd cores. -/
def oddCore (m : Nat) : Nat :=
  2 * m + 1

@[simp] theorem odd_oddCore (m : Nat) : Odd (oddCore m) := by
  refine ⟨m, ?_⟩
  unfold oddCore
  omega

@[simp] theorem oddCore_pos (m : Nat) : 0 < oddCore m := by
  unfold oddCore
  omega

@[simp] theorem one_le_oddCore (m : Nat) : 1 <= oddCore m := by
  exact Nat.succ_le_of_lt (oddCore_pos m)

/-- The even center `c = 2^k m` attached to depth `k` and odd core `m`. -/
def centerNat (k m : Nat) : Nat :=
  2 ^ k * oddCore m

@[simp] theorem centerNat_pos (k m : Nat) : 0 < centerNat k m := by
  unfold centerNat
  exact Nat.mul_pos (pow_pos (by decide : 0 < 2) _) (oddCore_pos m)

/-- Dyadic branch weight written in complex form. -/
noncomputable def dyadicComplexWeight (k : Nat) : Complex :=
  (((1 : Complex) / 2) ^ k)

/-- A single leg contribution attached to one branch sign. -/
noncomputable def legTerm (s : Complex) (k m : Nat) (epsilon : BranchSign) : Complex :=
  dyadicComplexWeight k *
    ((((natDescendant k epsilon (oddCore m) : Nat) : Complex) ^ (-s)))

/-- The two-leg package at depth `k` over the odd core `m`. -/
noncomputable def legPairTerm (s : Complex) (k m : Nat) : Complex :=
  legTerm s k m BranchSign.minus + legTerm s k m BranchSign.plus

/-- A single centered bracket contribution. -/
noncomputable def bracketTerm (s : Complex) (k m : Nat) : Complex :=
  dyadicComplexWeight k *
    (((((natDescendant k BranchSign.minus (oddCore m) : Nat) : Complex) ^ (-s))) +
      ((((natDescendant k BranchSign.plus (oddCore m) : Nat) : Complex) ^ (-s))) -
      2 * ((((centerNat k m : Nat) : Complex) ^ (-s))))

/-- The center term left over after exact cancellation of the two legs. -/
noncomputable def centerTerm (s : Complex) (k m : Nat) : Complex :=
  (2 : Complex) * dyadicComplexWeight k * ((((centerNat k m : Nat) : Complex) ^ (-s)))

/-- Common shell ratio appearing in the geometric factorization of the center series. -/
noncomputable def shellRatio (s : Complex) : Complex :=
  ((1 : Complex) / 2) * ((2 : Complex) ^ (-s))

/-- Finite depth window used for exact algebraic partial sums. -/
def depthWindow (K : Nat) : Finset Nat :=
  Finset.Icc 2 K

/-- Partial sum of the direct odd-leg channel over one odd core. -/
noncomputable def partialDCore (s : Complex) (K m : Nat) : Complex :=
  ∑ k ∈ depthWindow K, legPairTerm s k m

/-- Partial sum of the bracket channel over one odd core. -/
noncomputable def partialBCore (s : Complex) (K m : Nat) : Complex :=
  ∑ k ∈ depthWindow K, bracketTerm s k m

/-- Partial sum of the exact post-cancellation center channel over one odd core. -/
noncomputable def centerPartial (s : Complex) (K m : Nat) : Complex :=
  ∑ k ∈ depthWindow K, centerTerm s k m

/-- Finite geometric coefficient multiplying the odd-core Dirichlet factor. -/
noncomputable def centerCoeffPartial (s : Complex) (K : Nat) : Complex :=
  ∑ k ∈ depthWindow K, (2 : Complex) * shellRatio s ^ k

/-- Finite algebraic numerator attached to one odd core. -/
noncomputable def partialFCore (s : Complex) (K m : Nat) : Complex :=
  partialDCore s K m - partialBCore s K m

/-- Finite partial odd Dirichlet series over the first `M` odd cores. -/
noncomputable def oddZetaPartial (s : Complex) (M : Nat) : Complex :=
  ∑ m ∈ Finset.range M, ((((oddCore m : Nat) : Complex) ^ (-s)))

/-- Positive odd Dirichlet series written with the enumerator `oddCore`. -/
noncomputable def oddZeta (s : Complex) : Complex :=
  ∑' m : Nat, ((((oddCore m : Nat) : Complex) ^ (-s)))

/-- Closed geometric shell coefficient expected after summing the depth variable. -/
noncomputable def centerCoeff (s : Complex) : Complex :=
  (2 : Complex) * shellRatio s ^ 2 / (1 - shellRatio s)

/-- Infinite direct odd-leg channel. -/
noncomputable def DInfinity (s : Complex) : Complex :=
  ∑' j : Nat, ∑' m : Nat, legPairTerm s (j + 2) m

/-- Infinite bracket channel. -/
noncomputable def BInfinity (s : Complex) : Complex :=
  ∑' j : Nat, ∑' m : Nat, bracketTerm s (j + 2) m

/-- Infinite center-only channel obtained after the exact algebraic cancellation. -/
noncomputable def centerSeries (s : Complex) : Complex :=
  ∑' j : Nat, ∑' m : Nat, centerTerm s (j + 2) m

/-- Genuine C2 numerator. -/
noncomputable def FInfinity (s : Complex) : Complex :=
  DInfinity s - BInfinity s

/-!
Core genuine-channel layer.

Primary sources:
- docs/c2_rota_K_rigorosamente_fechada.md
- docs/algebra_Z_igual_zeta.md

Legacy seeds:
- Lean/Antigo_Lean_C2/Pushforward.lean
- Lean/Antigo_Lean_C2/Composite.lean
-/

end LeanC2