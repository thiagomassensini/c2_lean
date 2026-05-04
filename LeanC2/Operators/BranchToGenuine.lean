import Mathlib
import LeanC2.Operators.Branch
import LeanC2.Operators.Genuine

set_option linter.style.whitespace false

namespace LeanC2

open scoped BigOperators

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

/-!
Bridge from branch quantities to genuine C2 channels.

Primary sources:
- docs/c2_operador_ramo_invariancia_t_ponte_genuine.md

Legacy seeds:
- Lean/Antigo_Lean_C2/Chain.lean
- Lean/Antigo_Lean_C2/OperatorNorm.lean
-/

end LeanC2