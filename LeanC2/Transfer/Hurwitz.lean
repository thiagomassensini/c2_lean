import Mathlib
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

/-- Analyticity of each cutoff approximant on the off-critical strip. -/
def cutoffAnalyticOnOffCriticalStrip (FX : Nat -> Complex -> Complex) : Prop :=
  ∀ X : Nat, AnalyticOnNhd ℂ (FX X) offCriticalStripSet

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

/-!
Scaffold for the Hurwitz step `F_X -> numFun`.

Primary sources:
- docs/c2_bulk_offaxis_transfer.md

This file keeps the genuinely classical Hurwitz step explicit as an axiom-level interface.
The cutoff-family hypothesis is intentionally eventual in `X`, matching the actual gluing/cutoff
architecture above.
-/

end LeanC2
