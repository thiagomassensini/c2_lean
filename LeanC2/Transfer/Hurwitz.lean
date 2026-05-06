import Mathlib
import LeanC2.Cutoff.DecayRate
import LeanC2.Cutoff.Universality
import LeanC2.Glue.Decomposition
import LeanC2.Identity.MeromorphicExt

namespace LeanC2

/-- Left connected component of the open critical strip with the critical line removed. -/
def leftOffCriticalStripComponent (s : Complex) : Prop :=
  0 < s.re ∧ s.re < (1 : ℝ) / 2

/-- Right connected component of the open critical strip with the critical line removed. -/
def rightOffCriticalStripComponent (s : Complex) : Prop :=
  (1 : ℝ) / 2 < s.re ∧ s.re < 1

/--
The limiting numerator is not identically zero on either connected component of the off-critical
strip. This is the extra hypothesis needed to use the classical Hurwitz alternative as a
nonvanishing theorem rather than merely "nonvanishing or identically zero".
-/
def cutoffLimitNontrivialOnOffCriticalStrip (numFun : Complex -> Complex) : Prop :=
  (∃ s : Complex, leftOffCriticalStripComponent s ∧ numFun s ≠ 0) ∧
    (∃ s : Complex, rightOffCriticalStripComponent s ∧ numFun s ≠ 0)

/-- Combined cutoff approximation data feeding the Hurwitz step on the off-critical strip. -/
structure CutoffApproximationData
    (FX : Nat -> Complex -> Complex)
    (numFun : Complex -> Complex) : Prop where
  hAnalyticData : CutoffAnalyticData FX
  hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun
  hNontrivial : cutoffLimitNontrivialOnOffCriticalStrip numFun

/--
Classical Hurwitz transfer on the off-critical strip.

This packages the standard Hurwitz theorem together with the elimination of the zero-limit
alternative on the two components of the off-critical strip.
-/
axiom hurwitzTransferOffCriticalStrip
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hNontrivial : cutoffLimitNontrivialOnOffCriticalStrip numFun)
    (hFX : cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX) :
    offCriticalStripNonvanishing numFun

/-- Direct packaged form of the Hurwitz step `F_X -> numFun` on the off-critical strip. -/
theorem offCriticalStripNonvanishing_of_hurwitz
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hNontrivial : cutoffLimitNontrivialOnOffCriticalStrip numFun)
    (hFX : cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX) :
    offCriticalStripNonvanishing numFun :=
  hurwitzTransferOffCriticalStrip hAnalytic hConv hNontrivial hFX

/-- Hurwitz step with analyticity supplied by cutoff-layer analytic data. -/
theorem offCriticalStripNonvanishing_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hNontrivial : cutoffLimitNontrivialOnOffCriticalStrip numFun)
    (hFX : cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX) :
    offCriticalStripNonvanishing numFun := by
  exact offCriticalStripNonvanishing_of_hurwitz
    (cutoffAnalyticOnOffCriticalStrip_of_data hAnalyticData) hConv hNontrivial hFX

/-- Hurwitz step driven by the bundled cutoff approximation package. -/
theorem offCriticalStripNonvanishing_of_cutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hApprox : CutoffApproximationData FX numFun)
    (hFX : cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX) :
    offCriticalStripNonvanishing numFun :=
  offCriticalStripNonvanishing_of_cutoffAnalyticData
    hApprox.hAnalyticData hApprox.hConv hApprox.hNontrivial hFX

theorem canonicalCutoffFamily_approximationData_of_convergence
    {numFun : Complex -> Complex}
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hNontrivial : cutoffLimitNontrivialOnOffCriticalStrip numFun) :
    CutoffApproximationData canonicalCutoffFamily numFun := by
  refine ⟨canonicalCutoffFamily_analyticData, hConv, hNontrivial⟩

theorem canonicalCutoffFamily_approximationData_of_sharpCutoffFamily
    {numFun : Complex -> Complex}
    (hSharp :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip sharpCutoffFamily numFun)
    (hResidual :
      cutoffResidualVanishesLocallyUniformlyOnOffCriticalStrip canonicalCutoffResidual)
    (hNontrivial : cutoffLimitNontrivialOnOffCriticalStrip numFun) :
    CutoffApproximationData canonicalCutoffFamily numFun := by
  exact canonicalCutoffFamily_approximationData_of_convergence
    (canonicalCutoffFamily_convergesLocallyUniformlyOnOffCriticalStrip_of_sharpCutoffFamily
      hSharp hResidual) hNontrivial

theorem canonicalCutoffFamily_approximationData_of_sharpCutoffFamily_OInv
    {numFun : Complex -> Complex}
    (hSharp :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip sharpCutoffFamily numFun)
    (hResidual :
      cutoffResidualIsOInvLocallyUniformlyOnOffCriticalStrip canonicalCutoffResidual)
    (hNontrivial : cutoffLimitNontrivialOnOffCriticalStrip numFun) :
    CutoffApproximationData canonicalCutoffFamily numFun := by
  exact canonicalCutoffFamily_approximationData_of_convergence
    (canonicalCutoffFamily_convergesLocallyUniformlyOnOffCriticalStrip_of_sharpCutoffFamily_OInv
      hSharp hResidual) hNontrivial

theorem canonicalCutoffFamily_approximationData_of_sharpCutoff_coeffBound
    {numFun : Complex -> Complex}
    (hSharp :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip sharpCutoffFamily numFun)
    (hResidual : canonicalCutoffResidualCoeffUniformlyBoundedOnOffCriticalStrip)
    (hNontrivial : cutoffLimitNontrivialOnOffCriticalStrip numFun) :
    CutoffApproximationData canonicalCutoffFamily numFun := by
  exact canonicalCutoffFamily_approximationData_of_convergence
    (canonicalCutoffFamily_converges_of_sharpCutoffFamily_coeffBound
      hSharp hResidual) hNontrivial

/-- Coordinate form of the Hurwitz step on the off-critical strip. -/
theorem routeK_hurwitz_nonzero_offaxis
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hNontrivial : cutoffLimitNontrivialOnOffCriticalStrip numFun)
    (hFX : cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX)
    {sigma t : Real} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hhalf : sigma ≠ (1 : ℝ) / 2) :
    numFun ((sigma : Complex) + t * Complex.I) ≠ 0 := by
  exact offCriticalStripNonvanishing_of_hurwitz hAnalytic hConv hNontrivial hFX
    ((sigma : Complex) + t * Complex.I)
    ⟨by simpa using hsigma0, by simpa using hsigma1, by simpa using hhalf⟩

/-- Coordinate Hurwitz transfer with analyticity coming from cutoff-layer analytic data. -/
theorem routeK_hurwitz_nonzero_offaxis_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hNontrivial : cutoffLimitNontrivialOnOffCriticalStrip numFun)
    (hFX : cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX)
    {sigma t : Real} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hhalf : sigma ≠ (1 : ℝ) / 2) :
    numFun ((sigma : Complex) + t * Complex.I) ≠ 0 := by
  exact routeK_hurwitz_nonzero_offaxis
    (cutoffAnalyticOnOffCriticalStrip_of_data hAnalyticData) hConv hNontrivial hFX
    hsigma0 hsigma1 hhalf

/-- Coordinate Hurwitz transfer using the bundled cutoff approximation package. -/
theorem routeK_hurwitz_nonzero_offaxis_of_cutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hApprox : CutoffApproximationData FX numFun)
    (hFX : cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX)
    {sigma t : Real} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hhalf : sigma ≠ (1 : ℝ) / 2) :
    numFun ((sigma : Complex) + t * Complex.I) ≠ 0 := by
  exact routeK_hurwitz_nonzero_offaxis_of_cutoffAnalyticData
    hApprox.hAnalyticData hApprox.hConv hApprox.hNontrivial hFX hsigma0 hsigma1 hhalf

/-!
Scaffold for the Hurwitz step `F_X -> numFun`.

Primary sources:
- docs/c2_bulk_offaxis_transfer.md

This file keeps the genuinely classical Hurwitz step explicit as an axiom-level interface.
The cutoff-family hypothesis is intentionally eventual in `X`, matching the actual gluing/cutoff
architecture above. For the concrete cutoff family, analyticity is packaged canonically,
while convergence remains an explicit input until the `O(1 / X)` route is fully internalized.
-/

end LeanC2
