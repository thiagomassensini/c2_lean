import Mathlib
import LeanC2.Bulk.ClassicalAxioms
import LeanC2.Identity.C0NonZero

namespace LeanC2

/-!
Bulk lower bound for the continued C2 numerator.

Provides the concrete ingredients for the Route 3 lower-bound leg:

1. `c0_norm_pos_of_re_pos`: `‖c0 s‖ > 0` for Re(s) > 0.
2. `norm_continuedFInfinity_eq_mul_norm_riemannZeta`: norm factorisation via `F∞ = c₀·ζ`.
3. `zetaVKBound`: the Vinogradov-Korobov-Ford lower-bound function.
4. `adaptiveCutoffThreshold`: the cutoff index X₀(B, C) := ⌈2C/B⌉₊.
5. `adaptiveCutoff_error_lt_margin`: once X ≥ X₀ and the decay satisfies ‖err‖ ≤ C/X,
   the error is strictly below the margin B.

The theorem `continuedFInfinity_bulkLowerBound_of_VK` — combining these ingredients with
`bulkLimitLowerBound` (defined in `FXNonZeroBulk`) — is proved in that file.

Primary sources:
- docs/c2_bulk_offaxis_route3_tilt.md §6
-/

/-! ### c₀ positivity and norm factorisation -/

/-- `‖c0 s‖ > 0` for Re(s) > 0, from `c0_ne_zero_of_re_pos`. -/
theorem c0_norm_pos_of_re_pos {s : Complex} (hs : 0 < s.re) : 0 < ‖c0 s‖ :=
  norm_pos_iff.mpr (c0_ne_zero_of_re_pos hs)

/-- The norm of `continuedFInfinity s = c0 s * ζ(s)` factors multiplicatively. -/
theorem norm_continuedFInfinity_eq_mul_norm_riemannZeta (s : Complex) :
    ‖continuedFInfinity s‖ = ‖c0 s‖ * ‖riemannZeta s‖ := by
  unfold continuedFInfinity
  exact norm_mul _ _

/-! ### Vinogradov-Korobov-Ford bound function -/

/--
The VK lower-bound function evaluated at `s`:
  B_VK(C_VK, s) := exp(−C_VK · (log|Im(s)|)^(2/3) · (log log|Im(s)|)^(1/3)).
-/
noncomputable def zetaVKBound (C_VK : ℝ) (s : Complex) : ℝ :=
  Real.exp (-(C_VK *
    (Real.log |s.im|) ^ (2 / 3 : ℝ) *
    (Real.log (Real.log |s.im|)) ^ (1 / 3 : ℝ)))

theorem zetaVKBound_pos (C_VK : ℝ) (s : Complex) : 0 < zetaVKBound C_VK s :=
  Real.exp_pos _

/-! ### Adaptive cutoff threshold -/

/--
Adaptive cutoff threshold:
  X₀(B, C) := ⌈2·C / B⌉₊.

Once `X ≥ X₀(B, C)`, any decay bound `‖err‖ ≤ C / X` implies `‖err‖ < B / 2 < B`,
so the cutoff error is strictly dominated by the bulk lower-bound margin.
-/
noncomputable def adaptiveCutoffThreshold (B C : ℝ) : ℕ := ⌈2 * C / B⌉₊

/--
Algebraic key: if `X ≥ adaptiveCutoffThreshold B C`, `0 ≤ err`, and `err ≤ C / X`,
then `err < B`.

Proof: `2·C/B ≤ X` ⟹ `C/X ≤ B/2` ⟹ `err ≤ C/X < B`.
-/
theorem adaptiveCutoff_error_lt_margin
    {B C : ℝ} (hB : 0 < B) (hC : 0 < C)
    {X : ℕ} (hX : adaptiveCutoffThreshold B C ≤ X)
    {err : ℝ} (_hErrNn : 0 ≤ err) (hDecay : err ≤ C / (X : ℝ)) :
    err < B := by
  -- 2·C/B ≤ X (as reals) from ceiling bound
  have hXge : 2 * C / B ≤ (X : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hX)
  -- X > 0 as a real
  have hXpos : (0 : ℝ) < (X : ℝ) :=
    lt_of_lt_of_le (by positivity) hXge
  -- 2·C ≤ B·X: multiply hXge on both sides by B
  have h2C : 2 * C ≤ B * (X : ℝ) := by
    have step := mul_le_mul_of_nonneg_right hXge hB.le
    rw [div_mul_cancel₀ (2 * C) hB.ne'] at step
    linarith
  -- C / X < B: use C < B·X and cancel X
  have hCX_lt_B : C / (X : ℝ) < B := by
    have hClt : C < B * (X : ℝ) := by linarith
    by_contra hle
    push Not at hle  -- hle : B ≤ C / X
    have h1 : B * (X : ℝ) ≤ C / (X : ℝ) * (X : ℝ) :=
      mul_le_mul_of_nonneg_right hle hXpos.le
    rw [div_mul_cancel₀ C hXpos.ne'] at h1
    linarith
  linarith [hDecay.trans_lt hCX_lt_B]

end LeanC2
