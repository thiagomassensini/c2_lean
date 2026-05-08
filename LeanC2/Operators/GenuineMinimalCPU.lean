import Mathlib
import LeanC2.Identity.FundamentalIdentity
import LeanC2.Operators.Cutoff

set_option linter.style.whitespace false

namespace LeanC2

open scoped BigOperators

/--
Finite odd window used by the CPU scanner direct channel:
odd integers `n >= 3` up to the chosen cutoff `Nmax`.
-/
def cpuOddLegWindow (Nmax : Nat) : Finset Nat :=
  (Finset.range (Nmax + 1)).filter fun n => 3 <= n ∧ Odd n

/-- Finite odd-core window used by the CPU scanner bracket channel. -/
def cpuOddCoreValueWindow (Mlim : Nat) : Finset Nat :=
  (Finset.range (Mlim + 1)).filter fun m => Odd m

/--
Per-depth odd-core cap used by `c2_genuine_minimal_cpu.py`:
`m_lim = min((Nmax - 1) / 2^k, Mmax)`.
-/
def cpuBackgroundCoreLimit (Nmax k Mmax : Nat) : Nat :=
  min ((Nmax - 1) / 2 ^ k) Mmax

/-- Per-depth odd-core bracket window used by the minimal CPU scanner. -/
def cpuBackgroundCoreWindow (Nmax k Mmax : Nat) : Finset Nat :=
  cpuOddCoreValueWindow (cpuBackgroundCoreLimit Nmax k Mmax)

/--
The effective 2-adic level used in the Python scanner:
`k_eff(n) = max(v₂(n-1), v₂(n+1))`.
-/
def oddKeff (n : Nat) : Nat :=
  max ((n - 1).factorization 2) ((n + 1).factorization 2)

/-- The dyadic direct-channel weight `2^{-k_eff(n)}` in complex form. -/
noncomputable def oddKeffComplexWeight (n : Nat) : Complex :=
  ((1 : Complex) / 2) ^ oddKeff n

/-- Smooth CPU cutoff weight `exp(-n / scale)`. -/
noncomputable def cpuSmoothCutoffWeight (scale : Real) (n : Nat) : Complex :=
  ((Real.exp (-((n : Real) / scale)) : Real) : Complex)

/-- One term of the CPU direct channel. -/
noncomputable def cpuDirectTerm (scale : Real) (s : Complex) (n : Nat) : Complex :=
  oddKeffComplexWeight n * cpuSmoothCutoffWeight scale n * (((n : Complex) ^ (-s)))

/-- Direct channel from `c2_genuine_minimal_cpu.py`. -/
noncomputable def genuineMinimalCPUDirect
    (scale : Real) (Nmax : Nat) (s : Complex) : Complex :=
  ∑ n ∈ cpuOddLegWindow Nmax, cpuDirectTerm scale s n

/-- Center value `c = 2^k m`, with `m` the actual odd core value. -/
def cpuCenterNat (k m : Nat) : Nat :=
  2 ^ k * m

/-- One bracket term from the CPU background channel. -/
noncomputable def cpuBracketTerm (s : Complex) (k m : Nat) : Complex :=
  dyadicComplexWeight k *
    (((natDescendant k BranchSign.minus m : Complex) ^ (-s)) +
      ((natDescendant k BranchSign.plus m : Complex) ^ (-s)) -
      2 * (((cpuCenterNat k m : Nat) : Complex) ^ (-s)))

/-- Bracket/background channel from `c2_genuine_minimal_cpu.py`. -/
noncomputable def genuineMinimalCPUBackground
    (Nmax Kmax Mmax : Nat) (s : Complex) : Complex :=
  ∑ k ∈ Finset.Icc 2 Kmax, ∑ m ∈ cpuBackgroundCoreWindow Nmax k Mmax,
    cpuBracketTerm s k m

/-- Finite CPU numerator `D_cpu - B_cpu`. -/
noncomputable def genuineMinimalCPUNumerator
    (scale : Real) (Nmax Kmax Mmax : Nat) (s : Complex) : Complex :=
  genuineMinimalCPUDirect scale Nmax s - genuineMinimalCPUBackground Nmax Kmax Mmax s

/-- Normalized CPU scanner operator `Z_cpu = (D_cpu - B_cpu) / c0`. -/
noncomputable def genuineMinimalCPUOperator
    (scale : Real) (Nmax Kmax Mmax : Nat) (s : Complex) : Complex :=
  genuineMinimalCPUNumerator scale Nmax Kmax Mmax s / c0 s

/--
Exact residual between the finite CPU numerator and the infinite genuine numerator.
This packages all finite-window, cutoff, and background-depth defects in one object.
-/
noncomputable def genuineMinimalCPUResidual
    (scale : Real) (Nmax Kmax Mmax : Nat) (s : Complex) : Complex :=
  genuineMinimalCPUNumerator scale Nmax Kmax Mmax s - FInfinity s

theorem genuineMinimalCPUNumerator_eq_FInfinity_add_residual
    (scale : Real) (Nmax Kmax Mmax : Nat) (s : Complex) :
    genuineMinimalCPUNumerator scale Nmax Kmax Mmax s =
      FInfinity s + genuineMinimalCPUResidual scale Nmax Kmax Mmax s := by
  unfold genuineMinimalCPUResidual
  abel

/-- Dividing by `c0` is harmless wherever `c0` is nonzero. -/
theorem genuineMinimalCPUOperator_mul_c0
    {scale : Real} {Nmax Kmax Mmax : Nat} {s : Complex}
    (hc0 : c0 s ≠ 0) :
    genuineMinimalCPUOperator scale Nmax Kmax Mmax s * c0 s =
      genuineMinimalCPUNumerator scale Nmax Kmax Mmax s := by
  unfold genuineMinimalCPUOperator
  field_simp [hc0]

/-- The normalized scanner has exactly the same zeros as its numerator when `c0` is nonzero. -/
theorem genuineMinimalCPUOperator_eq_zero_iff_numerator_eq_zero
    {scale : Real} {Nmax Kmax Mmax : Nat} {s : Complex}
    (hc0 : c0 s ≠ 0) :
    genuineMinimalCPUOperator scale Nmax Kmax Mmax s = 0 ↔
      genuineMinimalCPUNumerator scale Nmax Kmax Mmax s = 0 := by
  constructor
  · intro hZ
    have hmul := congrArg (fun z : Complex => z * c0 s) hZ
    simpa [genuineMinimalCPUOperator_mul_c0 (scale := scale) (Nmax := Nmax)
      (Kmax := Kmax) (Mmax := Mmax) (s := s) hc0] using hmul
  · intro hF
    simp [genuineMinimalCPUOperator, hF]

theorem genuineMinimalCPUOperator_ne_zero_iff_numerator_ne_zero
    {scale : Real} {Nmax Kmax Mmax : Nat} {s : Complex}
    (hc0 : c0 s ≠ 0) :
    genuineMinimalCPUOperator scale Nmax Kmax Mmax s ≠ 0 ↔
      genuineMinimalCPUNumerator scale Nmax Kmax Mmax s ≠ 0 := by
  exact not_congr (genuineMinimalCPUOperator_eq_zero_iff_numerator_eq_zero
    (scale := scale) (Nmax := Nmax) (Kmax := Kmax) (Mmax := Mmax) (s := s) hc0)

/-- Critical-line specialization used by the zero scanner. -/
theorem genuineMinimalCPUOperator_eq_zero_iff_numerator_eq_zero_criticalLine
    (scale : Real) (Nmax Kmax Mmax : Nat) (t : Real) :
    genuineMinimalCPUOperator scale Nmax Kmax Mmax (((1 : Complex) / 2) + t * Complex.I) = 0 ↔
      genuineMinimalCPUNumerator scale Nmax Kmax Mmax
        (((1 : Complex) / 2) + t * Complex.I) = 0 := by
  exact genuineMinimalCPUOperator_eq_zero_iff_numerator_eq_zero
    (scale := scale) (Nmax := Nmax) (Kmax := Kmax) (Mmax := Mmax)
    (s := (((1 : Complex) / 2) + t * Complex.I)) (c0_ne_zero_on_critical t)

theorem genuineMinimalCPUOperator_ne_zero_iff_numerator_ne_zero_criticalLine
    (scale : Real) (Nmax Kmax Mmax : Nat) (t : Real) :
    genuineMinimalCPUOperator scale Nmax Kmax Mmax (((1 : Complex) / 2) + t * Complex.I) ≠ 0 ↔
      genuineMinimalCPUNumerator scale Nmax Kmax Mmax
        (((1 : Complex) / 2) + t * Complex.I) ≠ 0 := by
  exact genuineMinimalCPUOperator_ne_zero_iff_numerator_ne_zero
    (scale := scale) (Nmax := Nmax) (Kmax := Kmax) (Mmax := Mmax)
    (s := (((1 : Complex) / 2) + t * Complex.I)) (c0_ne_zero_on_critical t)

/--
Generic exact comparison: if the infinite genuine numerator is identified with `c0 * zetaFun`,
then the finite CPU scanner is exactly `zetaFun + residual/c0`.
-/
theorem genuineMinimalCPUOperator_eq_model_add_residual_div_c0
    {scale : Real} {Nmax Kmax Mmax : Nat} {s : Complex} {zetaFun : Complex -> Complex}
    (hId : FInfinity s = c0 s * zetaFun s) (hc0 : c0 s ≠ 0) :
    genuineMinimalCPUOperator scale Nmax Kmax Mmax s =
      zetaFun s + genuineMinimalCPUResidual scale Nmax Kmax Mmax s / c0 s := by
  unfold genuineMinimalCPUOperator
  rw [genuineMinimalCPUNumerator_eq_FInfinity_add_residual scale Nmax Kmax Mmax s]
  rw [hId]
  field_simp [hc0]

/-- On the convergent half-plane, the CPU scanner differs from ζ by exactly `residual/c0`. -/
theorem genuineMinimalCPUOperator_eq_riemannZeta_add_residual_div_c0
    {scale : Real} {Nmax Kmax Mmax : Nat} {s : Complex} (hs : 1 < s.re) :
    genuineMinimalCPUOperator scale Nmax Kmax Mmax s =
      riemannZeta s + genuineMinimalCPUResidual scale Nmax Kmax Mmax s / c0 s := by
  exact genuineMinimalCPUOperator_eq_model_add_residual_div_c0
    (scale := scale) (Nmax := Nmax) (Kmax := Kmax) (Mmax := Mmax)
    (s := s) (zetaFun := riemannZeta)
    (fundamentalIdentity_riemannZeta_on_right_half_plane s hs)
    (c0_ne_zero_of_re_pos (by linarith))

theorem genuineMinimalCPUOperator_eq_residual_div_c0_of_model_zero
    {scale : Real} {Nmax Kmax Mmax : Nat} {s : Complex} {zetaFun : Complex -> Complex}
    (hId : FInfinity s = c0 s * zetaFun s) (hc0 : c0 s ≠ 0)
    (hz : zetaFun s = 0) :
    genuineMinimalCPUOperator scale Nmax Kmax Mmax s =
      genuineMinimalCPUResidual scale Nmax Kmax Mmax s / c0 s := by
  rw [genuineMinimalCPUOperator_eq_model_add_residual_div_c0
    (scale := scale) (Nmax := Nmax) (Kmax := Kmax) (Mmax := Mmax)
    (s := s) hId hc0, hz, zero_add]

/-!
Finite formal layer for `scripts/c2_genuine_minimal_cpu.py`.

This module does not turn the Python zero scan into a proof of zero locations. It formalizes the
finite operator that the scanner evaluates, proves that the normalization by `c0` preserves zeros
on the critical line, and records the exact residual identity `Z_cpu = zeta + R/c0` wherever the
infinite genuine identity is available.
-/

end LeanC2
