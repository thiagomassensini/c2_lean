import LeanC2.C2OddChannel

namespace LeanC2

open scoped BigOperators

/-!
### Argument-principle certificate interface for the C2 odd channel

Mathlib currently does not expose a ready-made rectangle winding-number
argument-principle theorem in the form needed by the Route-K shell argument.
This module therefore records the exact certificate boundary between a
computable/analytic winding verification and the C2 dyadic shell API.

No RH statement and no off-axis transfer to zeta is used here.  The function
being counted is the C2 odd principal channel.
-/

/--
Finite boundary/winding certificate for a single contour.

`contour` is the intended boundary set, `boundarySamples` is the finite
certificate footprint on that contour, `windingCount` is the certified winding
count, and `zeroCount` is the shell zero count delivered by the argument
principle.  The equality `zeroCount = windingCount` is the formal hand-off from
the winding calculation to zero counting.
-/
def routeK_C2ArgumentPrincipleCountCertificate
    (F : ℂ → ℂ) (contour : Set ℂ) (boundarySamples : Finset ℂ)
    (windingCount zeroCount : ℕ) : Prop :=
  (∀ z ∈ boundarySamples, z ∈ contour ∧ F z ≠ 0) ∧
    zeroCount = windingCount

/--
Shellwise argument-principle certificate for the C2 odd channel.

Compared with `routeK_C2OddDyadicZeroCountingCertificateAt`, the density bound
is stated for the winding count.  The theorem below transports it to the zero
count using the argument-principle equality `zeroCount = windingCount`.
-/
def routeK_C2OddArgumentPrincipleShellCertificateAt
    (s : ℂ) (shells : Finset ℕ)
    (contour : ℕ → Set ℂ) (boundarySamples : ℕ → Finset ℂ)
    (windingCount zeroCount : ℕ → ℕ)
    (shellContribution shellScale : ℕ → ℝ)
    (base densityC shellCountC C : ℝ) : Prop :=
  ∃ ell : ℝ,
    ell = Real.log (routeK_offAxisHeight s) ∧
    0 ≤ base ∧
    0 ≤ densityC ∧
    0 ≤ shellCountC ∧
    1 ≤ ell ∧
    ‖c2OddPrincipalChannelBeta s‖ ≤
      base * ell + ∑ j ∈ shells, shellContribution j ∧
    (∀ j ∈ shells,
      routeK_C2ArgumentPrincipleCountCertificate c2OddPrincipalChannel
        (contour j) (boundarySamples j) (windingCount j) (zeroCount j) ∧
      0 < shellScale j ∧
      0 ≤ shellContribution j ∧
      shellContribution j ≤ (zeroCount j : ℝ) / shellScale j ∧
      (windingCount j : ℝ) ≤ densityC * shellScale j * ell) ∧
    (shells.card : ℝ) ≤ shellCountC * ell ∧
    base + densityC * shellCountC ≤ C

/--
The argument-principle shell certificate produces the zero-counting shell
certificate required by the C2 odd-channel beta bound.
-/
theorem routeK_C2OddDyadicZeroCountingCertificateAt_of_argumentPrincipleShellCertificate
    {s : ℂ} {shells : Finset ℕ}
    {contour : ℕ → Set ℂ} {boundarySamples : ℕ → Finset ℂ}
    {windingCount zeroCount : ℕ → ℕ}
    {shellContribution shellScale : ℕ → ℝ}
    {base densityC shellCountC C : ℝ}
    (hcert : routeK_C2OddArgumentPrincipleShellCertificateAt s shells contour
      boundarySamples windingCount zeroCount shellContribution shellScale
      base densityC shellCountC C) :
    routeK_C2OddDyadicZeroCountingCertificateAt s shells zeroCount
      shellContribution shellScale base densityC shellCountC C := by
  rcases hcert with
    ⟨ell, hLdef, hbase0, hdensity0, hshellCountC0, hL1, hBeta, hShell, hCard, hC⟩
  refine ⟨ell, hLdef, hbase0, hdensity0, hshellCountC0, hL1, hBeta, ?_, hCard, hC⟩
  intro j hj
  rcases hShell j hj with
    ⟨hAP, hscale_pos, hcontrib0, hcontrib, hwindDensity⟩
  rcases hAP with ⟨_hboundary, hcount⟩
  exact ⟨hscale_pos, hcontrib0, hcontrib, by simpa [hcount] using hwindDensity⟩

/--
Pointwise C2 odd-channel beta bound obtained from shellwise winding/argument
principle certificates.
-/
theorem routeK_C2OddChannelBetaBoundAt_of_argumentPrincipleShellCertificate
    {s : ℂ} {shells : Finset ℕ}
    {contour : ℕ → Set ℂ} {boundarySamples : ℕ → Finset ℂ}
    {windingCount zeroCount : ℕ → ℕ}
    {shellContribution shellScale : ℕ → ℝ}
    {base densityC shellCountC C : ℝ}
    (hcert : routeK_C2OddArgumentPrincipleShellCertificateAt s shells contour
      boundarySamples windingCount zeroCount shellContribution shellScale
      base densityC shellCountC C) :
    routeK_C2OddChannelBetaBoundAt s C := by
  exact routeK_C2OddChannelBetaBoundAt_of_dyadicZeroCountingCertificate
    (routeK_C2OddDyadicZeroCountingCertificateAt_of_argumentPrincipleShellCertificate hcert)

/-- Explicit-constant pointwise variant. -/
theorem routeK_C2OddChannelBetaBoundExplicitAt_of_argumentPrincipleShellCertificate
    {s : ℂ} {shells : Finset ℕ}
    {contour : ℕ → Set ℂ} {boundarySamples : ℕ → Finset ℂ}
    {windingCount zeroCount : ℕ → ℕ}
    {shellContribution shellScale : ℕ → ℝ}
    {base densityC shellCountC : ℝ}
    (hcert : routeK_C2OddArgumentPrincipleShellCertificateAt s shells contour
      boundarySamples windingCount zeroCount shellContribution shellScale
      base densityC shellCountC routeK_explicitTaylorC) :
    routeK_C2OddChannelBetaBoundExplicitAt s := by
  simpa [routeK_C2OddChannelBetaBoundExplicitAt] using
    routeK_C2OddChannelBetaBoundAt_of_argumentPrincipleShellCertificate hcert

/-- Global shellwise argument-principle certificate for the C2 odd channel. -/
def routeK_C2OddArgumentPrincipleShellCertificateGlobal
    (shells : ℂ → Finset ℕ)
    (contour : ℂ → ℕ → Set ℂ) (boundarySamples : ℂ → ℕ → Finset ℂ)
    (windingCount zeroCount : ℂ → ℕ → ℕ)
    (shellContribution shellScale : ℂ → ℕ → ℝ)
    (base densityC shellCountC C : ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
    routeK_C2OddArgumentPrincipleShellCertificateAt s (shells s)
      (contour s) (boundarySamples s) (windingCount s) (zeroCount s)
      (shellContribution s) (shellScale s) base densityC shellCountC C

/--
The global argument-principle shell certificate promotes to the global
zero-counting shell certificate.
-/
theorem routeK_C2OddDyadicZeroCountingCertificateGlobal_of_argumentPrincipleShellCertificateGlobal
    {shells : ℂ → Finset ℕ}
    {contour : ℂ → ℕ → Set ℂ} {boundarySamples : ℂ → ℕ → Finset ℂ}
    {windingCount zeroCount : ℂ → ℕ → ℕ}
    {shellContribution shellScale : ℂ → ℕ → ℝ}
    {base densityC shellCountC C : ℝ}
    (hcert : routeK_C2OddArgumentPrincipleShellCertificateGlobal shells contour
      boundarySamples windingCount zeroCount shellContribution shellScale
      base densityC shellCountC C) :
    routeK_C2OddDyadicZeroCountingCertificateGlobal shells zeroCount
      shellContribution shellScale base densityC shellCountC C := by
  intro s hs hstrip hhalf
  exact routeK_C2OddDyadicZeroCountingCertificateAt_of_argumentPrincipleShellCertificate
    (hcert s hs hstrip hhalf)

/--
Global C2 odd-channel beta bound obtained from shellwise winding/argument
principle certificates.
-/
theorem routeK_C2OddChannelBetaBoundGlobal_of_argumentPrincipleShellCertificateGlobal
    {shells : ℂ → Finset ℕ}
    {contour : ℂ → ℕ → Set ℂ} {boundarySamples : ℂ → ℕ → Finset ℂ}
    {windingCount zeroCount : ℂ → ℕ → ℕ}
    {shellContribution shellScale : ℂ → ℕ → ℝ}
    {base densityC shellCountC C : ℝ}
    (hcert : routeK_C2OddArgumentPrincipleShellCertificateGlobal shells contour
      boundarySamples windingCount zeroCount shellContribution shellScale
      base densityC shellCountC C) :
    routeK_C2OddChannelBetaBoundGlobal C := by
  have hzero :
      routeK_C2OddDyadicZeroCountingCertificateGlobal shells zeroCount
        shellContribution shellScale base densityC shellCountC C :=
    routeK_C2OddDyadicZeroCountingCertificateGlobal_of_argumentPrincipleShellCertificateGlobal
      hcert
  exact routeK_C2OddChannelBetaBoundGlobal_of_dyadicZeroCountingCertificateGlobal
    hzero

/-- Global explicit-constant variant. -/
theorem routeK_C2OddChannelBetaBoundExplicitGlobal_of_argumentPrincipleShellCertificateGlobal
    {shells : ℂ → Finset ℕ}
    {contour : ℂ → ℕ → Set ℂ} {boundarySamples : ℂ → ℕ → Finset ℂ}
    {windingCount zeroCount : ℂ → ℕ → ℕ}
    {shellContribution shellScale : ℂ → ℕ → ℝ}
    {base densityC shellCountC : ℝ}
    (hcert : routeK_C2OddArgumentPrincipleShellCertificateGlobal shells contour
      boundarySamples windingCount zeroCount shellContribution shellScale
      base densityC shellCountC routeK_explicitTaylorC) :
    routeK_C2OddChannelBetaBoundExplicitGlobal := by
  simpa [routeK_C2OddChannelBetaBoundExplicitGlobal] using
    routeK_C2OddChannelBetaBoundGlobal_of_argumentPrincipleShellCertificateGlobal hcert

end LeanC2
