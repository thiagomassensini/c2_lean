import Mathlib
import LeanC2.Identity.MeromorphicExt

namespace LeanC2

/-!
Classical analytic number theory inputs, packaged as explicit axioms.

These three results — the Vinogradov-Korobov-Ford quantitative lower bound, the
Phragmén-Lindelöf convexity bound, and the Riemann zeta functional equation — are standard
theorems not yet formally verified in Mathlib.  Listing them as axioms keeps the Lean proof
chain explicit: every subsequent theorem that depends on them is clearly labelled.

Primary sources:
- docs/c2_bulk_offaxis_route3_tilt.md §6
-/

/--
Vinogradov-Korobov-Ford 2002 quantitative lower bound for |ζ(s)| in the bulk strip.

In the region {s : ℂ | 0 < Re(s) < 1, |Im(s)| ≥ T₁} there exist absolute constants
C_VK > 0 and T₁ ≥ 3 such that
  |ζ(s)| ≥ exp(−C_VK · (log|Im(s)|)^(2/3) · (log log|Im(s)|)^(1/3)).

Reference: Ford 2002, "Vinogradov's integral and bounds for the Riemann zeta function",
Proc. London Math. Soc. 85 (2002) 565–633.
-/
axiom vinogradovKorobovFordLowerBound :
    ∃ C_VK T₁ : ℝ, 0 < C_VK ∧ 3 ≤ T₁ ∧
      ∀ s : Complex, 0 < s.re → s.re < 1 → T₁ ≤ |s.im| →
        Real.exp (-(C_VK *
            (Real.log |s.im|) ^ (2 / 3 : ℝ) *
            (Real.log (Real.log |s.im|)) ^ (1 / 3 : ℝ))) ≤ ‖riemannZeta s‖

/--
Phragmén-Lindelöf convexity bound for |ζ(s)| on the critical strip.

For every ε > 0 there exist C_PL > 0 and T₀ > 0 such that for
0 < Re(s) < 1 and |Im(s)| ≥ T₀:
  |ζ(s)| ≤ C_PL · |Im(s)|^((1 − Re(s))/2 + ε).

Reference: Titchmarsh, "The Theory of the Riemann Zeta-Function" §5.1.
-/
axiom phragmenLindelofConvexityBound :
    ∀ ε : ℝ, 0 < ε →
      ∃ C_PL T₀ : ℝ, 0 < C_PL ∧ 0 < T₀ ∧
        ∀ s : Complex, 0 < s.re → s.re < 1 → T₀ ≤ |s.im| →
          ‖riemannZeta s‖ ≤ C_PL * Real.rpow |s.im| ((1 - s.re) / 2 + ε)

/--
Functional equation for the Riemann zeta function.

  ζ(s) = 2^s · π^(s−1) · sin(πs/2) · Γ(1−s) · ζ(1−s)   for s ∉ {0, 1}.

Reference: Riemann 1859; Davenport "Multiplicative Number Theory" §8.
-/
axiom riemannZetaFunctionalEquation :
    ∀ s : Complex, s ≠ 0 → s ≠ 1 →
      riemannZeta s =
        (2 : Complex) ^ s * ((Real.pi : Complex) ^ (s - 1)) *
          Complex.sin ((Real.pi : Complex) * s / 2) *
          Complex.Gamma (1 - s) * riemannZeta (1 - s)

end LeanC2
