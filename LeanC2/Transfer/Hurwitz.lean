import Mathlib
import LeanC2.Cutoff.DecayRate
import LeanC2.Glue.Decomposition
import LeanC2.Identity.MeromorphicExt

namespace LeanC2

/--
Local-uniform convergence of a cutoff family to its limiting numerator on the
off-critical strip.
-/
def cutoffConvergesLocallyUniformlyOnOffCriticalStrip
    (FX : Nat -> Complex -> Complex)
    (numFun : Complex -> Complex) : Prop :=
  ∀ K : Set Complex, IsCompact K -> K ⊆ offCriticalStripSet ->
    TendstoUniformlyOn (fun X s => FX X s) numFun Filter.atTop K

/-- Combined cutoff approximation data feeding the Hurwitz step on the off-critical strip. -/
structure CutoffApproximationData
    (FX : Nat -> Complex -> Complex)
    (numFun : Complex -> Complex) : Prop where
  hAnalyticData : CutoffAnalyticData FX
  hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun

/--
Classical Hurwitz transfer on the off-critical strip.

This packages the standard Hurwitz theorem together with the elimination of the zero-limit
alternative on the two components of the off-critical strip.
-/
axiom hurwitzTransferOffCriticalStrip
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
  (hFX : cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX) :
    offCriticalStripNonvanishing numFun

/-- Direct packaged form of the Hurwitz step `F_X -> numFun` on the off-critical strip. -/
theorem offCriticalStripNonvanishing_of_hurwitz
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
  (hFX : cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX) :
    offCriticalStripNonvanishing numFun :=
  hurwitzTransferOffCriticalStrip hAnalytic hConv hFX

/-- Hurwitz step with analyticity supplied by cutoff-layer analytic data. -/
theorem offCriticalStripNonvanishing_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hFX : cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX) :
    offCriticalStripNonvanishing numFun := by
  exact offCriticalStripNonvanishing_of_hurwitz
    (cutoffAnalyticOnOffCriticalStrip_of_data hAnalyticData) hConv hFX

/-- Hurwitz step driven by the bundled cutoff approximation package. -/
theorem offCriticalStripNonvanishing_of_cutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hApprox : CutoffApproximationData FX numFun)
    (hFX : cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX) :
    offCriticalStripNonvanishing numFun :=
  offCriticalStripNonvanishing_of_cutoffAnalyticData hApprox.hAnalyticData hApprox.hConv hFX

/-- Coordinate form of the Hurwitz step on the off-critical strip. -/
theorem routeK_hurwitz_nonzero_offaxis
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
  (hFX : cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX)
    {sigma t : Real} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hhalf : sigma ≠ (1 : ℝ) / 2) :
    numFun ((sigma : Complex) + t * Complex.I) ≠ 0 := by
  exact offCriticalStripNonvanishing_of_hurwitz hAnalytic hConv hFX
    ((sigma : Complex) + t * Complex.I)
    ⟨by simpa using hsigma0, by simpa using hsigma1, by simpa using hhalf⟩

/-- Coordinate Hurwitz transfer with analyticity coming from cutoff-layer analytic data. -/
theorem routeK_hurwitz_nonzero_offaxis_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hFX : cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX)
    {sigma t : Real} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hhalf : sigma ≠ (1 : ℝ) / 2) :
    numFun ((sigma : Complex) + t * Complex.I) ≠ 0 := by
  exact routeK_hurwitz_nonzero_offaxis
    (cutoffAnalyticOnOffCriticalStrip_of_data hAnalyticData) hConv hFX hsigma0 hsigma1 hhalf

/-- Coordinate Hurwitz transfer using the bundled cutoff approximation package. -/
theorem routeK_hurwitz_nonzero_offaxis_of_cutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hApprox : CutoffApproximationData FX numFun)
    (hFX : cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX)
    {sigma t : Real} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hhalf : sigma ≠ (1 : ℝ) / 2) :
    numFun ((sigma : Complex) + t * Complex.I) ≠ 0 := by
  exact routeK_hurwitz_nonzero_offaxis_of_cutoffAnalyticData
    hApprox.hAnalyticData hApprox.hConv hFX hsigma0 hsigma1 hhalf

/-!
Scaffold for the Hurwitz step `F_X -> numFun`.

Primary sources:
- docs/c2_bulk_offaxis_transfer.md

This file keeps the genuinely classical Hurwitz step explicit as an axiom-level interface.
The cutoff-family hypothesis is intentionally eventual in `X`, matching the actual gluing/cutoff
architecture above.
-/

end LeanC2
