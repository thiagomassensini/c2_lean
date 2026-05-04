import LeanC2.Pushforward
import LeanC2.TransversalAnalytic

namespace LeanC2

open scoped BigOperators LSeries.notation

/-!
### C2 odd Dirichlet channel

This module keeps the new research direction separate from the classical zeta
endpoint.  The odd channel is the principal Dirichlet channel modulo `2`
attached to the C2 pushforward recovery of `Λ`; its zero-counting input is
packaged as a certificate that can be supplied without invoking RH or any
off-axis transfer statement for zeta.
-/

/-- Principal odd Dirichlet channel, i.e. the L-series of the principal
character modulo `2`. -/
noncomputable def c2OddPrincipalChannel (s : ℂ) : ℂ :=
  L ↗c2OddPrincipalChar s

/-- Log-derivative channel recovered from the C2 von Mangoldt coefficients. -/
noncomputable def c2OddPrincipalChannelLogDerivative (s : ℂ) : ℂ :=
  c2OddRecoveredVonMangoldtLSeries s

/--
On the half-plane of absolute convergence, the C2-recovered von Mangoldt
channel is the negative logarithmic derivative of the odd principal channel.
-/
theorem c2OddPrincipalChannelLogDerivative_eq {s : ℂ} (hs : 1 < s.re) :
    c2OddPrincipalChannelLogDerivative s =
      - deriv c2OddPrincipalChannel s / c2OddPrincipalChannel s := by
  simpa [c2OddPrincipalChannelLogDerivative, c2OddPrincipalChannel] using
    (c2OddRecoveredVonMangoldtLSeries_eq_logDeriv_channel (s := s) hs)

/--
The beta-ratio of the odd principal channel.  This is the C2-channel analogue
of the transversal ratio `F''/F'` used in the zeta-facing Taylor layer.
-/
noncomputable def c2OddPrincipalChannelBeta (s : ℂ) : ℂ :=
  routeK_transversalBeta (deriv c2OddPrincipalChannel s)
    (deriv (deriv c2OddPrincipalChannel) s)

/-- Pointwise `log² |Im(s)|` beta bound for the C2 odd channel. -/
def routeK_C2OddChannelBetaBoundAt (s : ℂ) (C : ℝ) : Prop :=
  ‖c2OddPrincipalChannelBeta s‖ ≤ C * (Real.log (routeK_offAxisHeight s)) ^ 2

/-- Global off-axis beta bound for the C2 odd channel on the Route-K strip. -/
def routeK_C2OddChannelBetaBoundGlobal (C : ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
    routeK_C2OddChannelBetaBoundAt s C

/-- Explicit-constant specialization of the C2 odd-channel beta bound. -/
def routeK_C2OddChannelBetaBoundExplicitAt (s : ℂ) : Prop :=
  routeK_C2OddChannelBetaBoundAt s routeK_explicitTaylorC

/-- Global explicit-constant specialization of the C2 odd-channel beta bound. -/
def routeK_C2OddChannelBetaBoundExplicitGlobal : Prop :=
  routeK_C2OddChannelBetaBoundGlobal routeK_explicitTaylorC

/--
Dyadic zero-counting certificate for the beta-ratio of the C2 odd channel.

For each dyadic shell `j`, `zeroCount j` is a finite shell count,
`shellScale j` is the lower distance scale, and `shellContribution j` is the
contribution of that shell to the regular part.  The certificate records the
Route-K mechanism:

* a base contribution `base * log |Im(s)|`,
* shell count bound `zeroCount j <= densityC * shellScale j * log |Im(s)|`,
* distance bound `shellContribution j <= zeroCount j / shellScale j`,
* at most `shellCountC * log |Im(s)|` relevant shells.

The theorem below performs the arithmetic cancellation
`(densityC * scale * L) / scale <= densityC * L` and sums over shells.
-/
def routeK_C2OddDyadicZeroCountingCertificateAt
    (s : ℂ) (shells : Finset ℕ) (zeroCount : ℕ → ℕ)
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
      0 < shellScale j ∧
      0 ≤ shellContribution j ∧
      shellContribution j ≤ (zeroCount j : ℝ) / shellScale j ∧
      (zeroCount j : ℝ) ≤ densityC * shellScale j * ell) ∧
    (shells.card : ℝ) ≤ shellCountC * ell ∧
    base + densityC * shellCountC ≤ C

/--
A dyadic zero-counting certificate discharges the C2 odd-channel beta bound.
-/
theorem routeK_C2OddChannelBetaBoundAt_of_dyadicZeroCountingCertificate
    {s : ℂ} {shells : Finset ℕ} {zeroCount : ℕ → ℕ}
    {shellContribution shellScale : ℕ → ℝ}
    {base densityC shellCountC C : ℝ}
    (hcert : routeK_C2OddDyadicZeroCountingCertificateAt s shells zeroCount
      shellContribution shellScale base densityC shellCountC C) :
    routeK_C2OddChannelBetaBoundAt s C := by
  rcases hcert with
    ⟨ell, hLdef, hbase0, hdensity0, _hshellCountC0, hL1, hBeta, hShell, hCard, hC⟩
  have hL0 : 0 ≤ ell := by linarith
  have hDensityL0 : 0 ≤ densityC * ell := mul_nonneg hdensity0 hL0
  have hShell_le :
      ∀ j ∈ shells, shellContribution j ≤ densityC * ell := by
    intro j hj
    rcases hShell j hj with ⟨hscale_pos, _hcontrib0, hcontrib, hcount⟩
    have hscale_nonneg : 0 ≤ shellScale j := le_of_lt hscale_pos
    have hcount_div :
        (zeroCount j : ℝ) / shellScale j ≤
          (densityC * shellScale j * ell) / shellScale j := by
      exact div_le_div_of_nonneg_right hcount hscale_nonneg
    have hcollapse :
        (densityC * shellScale j * ell) / shellScale j = densityC * ell := by
      field_simp [ne_of_gt hscale_pos]
    exact hcontrib.trans (hcount_div.trans_eq hcollapse)
  have hsum_le_const :
      (∑ j ∈ shells, shellContribution j) ≤ ∑ j ∈ shells, densityC * ell := by
    exact Finset.sum_le_sum fun j hj => hShell_le j hj
  have hsum_const :
      (∑ j ∈ shells, densityC * ell) = (shells.card : ℝ) * (densityC * ell) := by
    simp
  have hsum_le_card :
      (∑ j ∈ shells, shellContribution j) ≤ (shells.card : ℝ) * (densityC * ell) := by
    calc
      (∑ j ∈ shells, shellContribution j) ≤
          ∑ j ∈ shells, densityC * ell := hsum_le_const
      _ = (shells.card : ℝ) * (densityC * ell) := hsum_const
  have hsum_le_logSq :
      (∑ j ∈ shells, shellContribution j) ≤ densityC * shellCountC * ell ^ 2 := by
    calc
      (∑ j ∈ shells, shellContribution j) ≤
          (shells.card : ℝ) * (densityC * ell) := hsum_le_card
      _ ≤ (shellCountC * ell) * (densityC * ell) :=
          mul_le_mul_of_nonneg_right hCard hDensityL0
      _ = densityC * shellCountC * ell ^ 2 := by ring
  have hL_le_sq : ell ≤ ell ^ 2 := by nlinarith
  have hbase_le_logSq : base * ell ≤ base * ell ^ 2 :=
    mul_le_mul_of_nonneg_left hL_le_sq hbase0
  have hmain :
      ‖c2OddPrincipalChannelBeta s‖ ≤
        (base + densityC * shellCountC) * ell ^ 2 := by
    calc
      ‖c2OddPrincipalChannelBeta s‖ ≤
          base * ell + ∑ j ∈ shells, shellContribution j := hBeta
      _ ≤ base * ell ^ 2 + densityC * shellCountC * ell ^ 2 :=
          add_le_add hbase_le_logSq hsum_le_logSq
      _ = (base + densityC * shellCountC) * ell ^ 2 := by ring
  have hfinal :
      (base + densityC * shellCountC) * ell ^ 2 ≤ C * ell ^ 2 :=
    mul_le_mul_of_nonneg_right hC (sq_nonneg ell)
  unfold routeK_C2OddChannelBetaBoundAt
  simpa [hLdef] using hmain.trans hfinal

/--
Explicit-constant variant of the C2 odd-channel zero-counting certificate.
-/
theorem routeK_C2OddChannelBetaBoundExplicitAt_of_dyadicZeroCountingCertificate
    {s : ℂ} {shells : Finset ℕ} {zeroCount : ℕ → ℕ}
    {shellContribution shellScale : ℕ → ℝ}
    {base densityC shellCountC : ℝ}
    (hcert : routeK_C2OddDyadicZeroCountingCertificateAt s shells zeroCount
      shellContribution shellScale base densityC shellCountC routeK_explicitTaylorC) :
    routeK_C2OddChannelBetaBoundExplicitAt s := by
  simpa [routeK_C2OddChannelBetaBoundExplicitAt] using
    routeK_C2OddChannelBetaBoundAt_of_dyadicZeroCountingCertificate hcert

/-- Global dyadic zero-counting certificate for the C2 odd channel. -/
def routeK_C2OddDyadicZeroCountingCertificateGlobal
    (shells : ℂ → Finset ℕ) (zeroCount : ℂ → ℕ → ℕ)
    (shellContribution shellScale : ℂ → ℕ → ℝ)
    (base densityC shellCountC C : ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ (1 : ℝ) / 2 →
    routeK_C2OddDyadicZeroCountingCertificateAt s (shells s) (zeroCount s)
      (shellContribution s) (shellScale s) base densityC shellCountC C

/--
A global dyadic zero-counting certificate promotes to the global C2 odd-channel
beta bound.
-/
theorem routeK_C2OddChannelBetaBoundGlobal_of_dyadicZeroCountingCertificateGlobal
    {shells : ℂ → Finset ℕ} {zeroCount : ℂ → ℕ → ℕ}
    {shellContribution shellScale : ℂ → ℕ → ℝ}
    {base densityC shellCountC C : ℝ}
    (hcert : routeK_C2OddDyadicZeroCountingCertificateGlobal shells zeroCount
      shellContribution shellScale base densityC shellCountC C) :
    routeK_C2OddChannelBetaBoundGlobal C := by
  intro s hs hstrip hhalf
  exact routeK_C2OddChannelBetaBoundAt_of_dyadicZeroCountingCertificate
    (hcert s hs hstrip hhalf)

/-- Global explicit-constant variant for the C2 odd channel. -/
theorem routeK_C2OddChannelBetaBoundExplicitGlobal_of_dyadicZeroCountingCertificateGlobal
    {shells : ℂ → Finset ℕ} {zeroCount : ℂ → ℕ → ℕ}
    {shellContribution shellScale : ℂ → ℕ → ℝ}
    {base densityC shellCountC : ℝ}
    (hcert : routeK_C2OddDyadicZeroCountingCertificateGlobal shells zeroCount
      shellContribution shellScale base densityC shellCountC routeK_explicitTaylorC) :
    routeK_C2OddChannelBetaBoundExplicitGlobal := by
  simpa [routeK_C2OddChannelBetaBoundExplicitGlobal] using
    routeK_C2OddChannelBetaBoundGlobal_of_dyadicZeroCountingCertificateGlobal hcert

end LeanC2
