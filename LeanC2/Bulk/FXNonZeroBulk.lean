import Mathlib
import LeanC2.Bulk.BulkLowerBound
import LeanC2.Cutoff.DecayRate
import LeanC2.Glue.Decomposition

namespace LeanC2

def bulkRegionEventuallyNonvanishing
    (FX : Nat -> Complex -> Complex) (deltaStar : ℝ -> ℝ) (eps T0 : ℝ) : Prop :=
  ∃ X0 : Nat,
    ∀ X : Nat, X0 ≤ X -> ∀ s : Complex, bulkRegion deltaStar eps T0 s -> FX X s ≠ 0

/--
Route 3 lower-bound input for the limiting bulk model.

The function `B` is the positive regional lower bound from the bulk notes, e.g. the
`c_min * exp(-C_* (log T)^(2/3+eta))` bound produced by the classical zeta input.
-/
def bulkLimitLowerBound
    (limitFun : Complex -> Complex) (B : Complex -> ℝ)
    (deltaStar : ℝ -> ℝ) (eps T0 : ℝ) : Prop :=
  ∀ s : Complex, bulkRegion deltaStar eps T0 s -> 0 < B s ∧ B s ≤ ‖limitFun s‖

/--
Route 3 cutoff-coupling input: eventually the cutoff error is smaller than the
regional lower bound for the limiting model.
-/
def bulkCutoffErrorEventuallyBelow
    (FX : Nat -> Complex -> Complex) (limitFun : Complex -> Complex) (B : Complex -> ℝ)
    (deltaStar : ℝ -> ℝ) (eps T0 : ℝ) : Prop :=
  ∃ X0 : Nat,
    ∀ X : Nat, X0 ≤ X -> ∀ s : Complex,
      bulkRegion deltaStar eps T0 s -> ‖FX X s - limitFun s‖ < B s

/--
Route 3 bulk certificate interface.

This is the Lean-side form of the notes' proof pattern:
`|F∞| >= B > 0` on the bulk and `|F_X - F∞| < B` for all sufficiently
large cutoffs.
-/
def Route3BulkCertificate
    (FX : Nat -> Complex -> Complex) (limitFun : Complex -> Complex)
    (deltaStar : ℝ -> ℝ) (eps T0 : ℝ) : Prop :=
  ∃ B : Complex -> ℝ,
    bulkLimitLowerBound limitFun B deltaStar eps T0 ∧
      bulkCutoffErrorEventuallyBelow FX limitFun B deltaStar eps T0

theorem bulkRegionEventuallyNonvanishing_of_route3BulkCertificate
    {FX : Nat -> Complex -> Complex} {limitFun : Complex -> Complex}
    {deltaStar : ℝ -> ℝ} {eps T0 : ℝ}
    (hRoute3 : Route3BulkCertificate FX limitFun deltaStar eps T0) :
    bulkRegionEventuallyNonvanishing FX deltaStar eps T0 := by
  rcases hRoute3 with ⟨B, hLower, hError⟩
  rcases hError with ⟨X0, hX0⟩
  refine ⟨X0, ?_⟩
  intro X hX s hs hZero
  have hErr := hX0 X hX s hs
  have hLowerS := hLower s hs
  have hEq : ‖FX X s - limitFun s‖ = ‖limitFun s‖ := by
    rw [hZero, zero_sub, norm_neg]
  have hSelfLt : ‖limitFun s‖ < ‖limitFun s‖ := by
    calc
      ‖limitFun s‖ = ‖FX X s - limitFun s‖ := hEq.symm
      _ < B s := hErr
      _ ≤ ‖limitFun s‖ := hLowerS.2
  exact (lt_irrefl _ hSelfLt)

/-!
Scaffold for the bulk zero-free region of `F_X`.

Primary sources:
- docs/c2_bulk_offaxis_glue.md
- docs/c2_bulk_offaxis_route3_tilt.md

This layer now includes the Route 3 proof skeleton used by the notes: a positive lower bound for
the limiting bulk model plus a dominated cutoff error implies eventual nonvanishing of the cutoff
family on the bulk region. The classical analytic ingredients that produce the lower bound remain
explicit upstream inputs.
-/

end LeanC2
