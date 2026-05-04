import Mathlib
import LeanC2.Finite.FiniteCertificate
import LeanC2.Glue.GlueTheorem
import LeanC2.Identity.MeromorphicExt
import LeanC2.Numerical.Constants
import LeanC2.Transfer.Hurwitz

namespace LeanC2

/-- Direct pointwise transfer from continued numerator nonvanishing to zeta nonvanishing. -/
theorem zetaNonzero_of_numFunNonzero {numFun zetaFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun zetaFun)
    {s : Complex} (hs0 : 0 < s.re) (hs1 : s.re < 1) (hNum : numFun s ≠ 0) :
    zetaFun s ≠ 0 := by
  exact (fundamentalIdentity_nonzero_iff_of_punctured_model hId hs0 (re_lt_one_ne_one hs1)).1 hNum

/-- Strip-level nonvanishing transfer from the continued numerator to the zeta channel. -/
theorem offCriticalStripNonvanishing_of_numFunNonvanishing
    {numFun zetaFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun zetaFun)
    (hNum : offCriticalStripNonvanishing numFun) :
    offCriticalStripNonvanishing zetaFun := by
  intro s hs
  exact zetaNonzero_of_numFunNonzero hId hs.1 hs.2.1 (hNum s hs)

/-- Coordinate form of the Thm 17 transfer on the off-critical strip. -/
theorem routeK_transfer_offaxis {numFun zetaFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun zetaFun)
    {sigma t : Real} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hNum : numFun ((sigma : Complex) + t * Complex.I) ≠ 0) :
    zetaFun ((sigma : Complex) + t * Complex.I) ≠ 0 := by
  exact (routeK_thm17_nonzero_transfer hId hsigma0 hsigma1).1 hNum

/-- Specialized off-axis transfer theorem for the Riemann zeta function. -/
theorem riemannZeta_nonzero_of_numFunNonzero {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    {s : Complex} (hs0 : 0 < s.re) (hs1 : s.re < 1) (hNum : numFun s ≠ 0) :
    riemannZeta s ≠ 0 := by
  exact zetaNonzero_of_numFunNonzero hId hs0 hs1 hNum

/-- Global off-critical-strip nonvanishing transfer to the Riemann zeta function. -/
theorem riemannZeta_nonvanishing_offCriticalStrip_of_numFunNonvanishing
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hNum : offCriticalStripNonvanishing numFun) :
    offCriticalStripNonvanishing riemannZeta := by
  exact offCriticalStripNonvanishing_of_numFunNonvanishing hId hNum

/-- Direct transfer from a nonvanishing cutoff family to the Riemann zeta function. -/
theorem riemannZeta_nonvanishing_offCriticalStrip_of_hurwitz
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hFX : cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_numFunNonvanishing hId
    (offCriticalStripNonvanishing_of_hurwitz hAnalytic hConv hFX)

/-- Direct transfer from finite coverage plus high-height gluing to zeta nonvanishing. -/
theorem riemannZeta_nonvanishing_offCriticalStrip_of_finite_and_high
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex} {H : ℝ}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hFinite : cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip FX H)
    (hHigh : cutoffFamilyEventuallyNonvanishingOnHighOffCriticalStrip FX H) :
    offCriticalStripNonvanishing riemannZeta := by
  apply riemannZeta_nonvanishing_offCriticalStrip_of_hurwitz hId hAnalytic hConv
  exact cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_finite_and_high hFinite hHigh

theorem riemannZeta_nonvanishing_offCriticalStrip_of_finite_and_high_of_le
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex} {T0 H : ℝ}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hT : T0 ≤ H)
    (hFinite : cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip FX H)
    (hHigh : cutoffFamilyEventuallyNonvanishingOnHighOffCriticalStrip FX T0) :
    offCriticalStripNonvanishing riemannZeta := by
  apply riemannZeta_nonvanishing_offCriticalStrip_of_hurwitz hId hAnalytic hConv
  exact cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_finite_and_high_of_le
    hT hFinite hHigh

theorem riemannZeta_nonvanishing_offCriticalStrip_of_default_finite_and_high
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hFinite : cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip FX defaultCertifiedHeight)
    (hHigh : cutoffFamilyEventuallyNonvanishingOnHighOffCriticalStrip FX defaultT0) :
    offCriticalStripNonvanishing riemannZeta := by
  apply riemannZeta_nonvanishing_offCriticalStrip_of_hurwitz hId hAnalytic hConv
  exact cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_default_finite_and_high
    hFinite hHigh

theorem riemannZeta_nonvanishing_offCriticalStrip_of_default_finite_and_glue
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex} {deltaStar : ℝ -> ℝ}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hDelta : ∀ t : ℝ, 0 ≤ deltaStar t)
    (hNear : nearRegionEventuallyNonvanishing FX deltaStar defaultT0)
    (hBulk : bulkRegionEventuallyNonvanishing FX deltaStar defaultEps defaultT0)
    (hEdge : edgeRegionEventuallyNonvanishing FX defaultEps defaultT0)
    (hFinite : cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip FX defaultCertifiedHeight) :
    offCriticalStripNonvanishing riemannZeta := by
  apply riemannZeta_nonvanishing_offCriticalStrip_of_default_finite_and_high
    hId hAnalytic hConv hFinite
  exact glueTheorem_highOffCriticalStrip_default hDelta hNear hBulk hEdge

theorem riemannZeta_nonvanishing_offCriticalStrip_of_defaultData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex} {deltaStar : ℝ -> ℝ}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultFiniteAndGlueData FX deltaStar) :
    offCriticalStripNonvanishing riemannZeta := by
  apply riemannZeta_nonvanishing_offCriticalStrip_of_hurwitz hId hAnalytic hConv
  exact cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_defaultData hData

theorem riemannZeta_nonvanishing_offCriticalStrip_of_defaultTaylorData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex} {deltaStar : ℝ -> ℝ}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultFiniteAndGlueTaylorData FX deltaStar) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultData hId hAnalytic hConv
    (defaultFiniteAndGlueData_of_taylorData hData)

theorem riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultData hId hAnalytic hConv hData

theorem riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData
    hId (cutoffAnalyticOnOffCriticalStrip_of_data hAnalyticData) hConv hData

theorem riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData_of_cutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hApprox : CutoffApproximationData FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData_of_cutoffAnalyticData
    hId hApprox.hAnalyticData hApprox.hConv hData

theorem riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundTaylorData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData
    hId hAnalytic hConv (defaultGlobalBoundData_of_taylorData hData)

theorem
    riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundTaylorData_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundTaylorData
    hId (cutoffAnalyticOnOffCriticalStrip_of_data hAnalyticData) hConv hData

theorem riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundTaylorData_of_cutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hApprox : CutoffApproximationData FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact
    riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundTaylorData_of_cutoffAnalyticData
    hId
    hApprox.hAnalyticData
    hApprox.hConv
    hData

theorem riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData_of_poleClearedAnalytic
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData
    (fundamentalIdentity_riemannZeta_on_puncturedRightHalfPlane_of_data hIdData)
    hAnalytic hConv hData

theorem
    riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData_of_poleClearedAnalytic_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData_of_poleClearedAnalytic
    hIdData (cutoffAnalyticOnOffCriticalStrip_of_data hAnalyticData) hConv hData

theorem
  riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData_of_poleClearedCutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hApprox : CutoffApproximationData FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact
    riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData_of_poleClearedAnalytic_of_cutoffAnalyticData
    hIdData
    hApprox.hAnalyticData
    hApprox.hConv
    hData

theorem
  riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundTaylorData_of_poleClearedAnalytic
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundTaylorData
    (fundamentalIdentity_riemannZeta_on_puncturedRightHalfPlane_of_data hIdData)
    hAnalytic hConv hData

theorem
    riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundTaylorData_of_poleClearedAnalytic_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundTaylorData_of_poleClearedAnalytic
    hIdData (cutoffAnalyticOnOffCriticalStrip_of_data hAnalyticData) hConv hData

theorem
  riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundTaylorData_of_poleClearedCutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hApprox : CutoffApproximationData FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact
    riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundTaylorData_of_poleClearedAnalytic_of_cutoffAnalyticData
    hIdData
    hApprox.hAnalyticData
    hApprox.hConv
    hData

theorem routeK_default_offaxis_riemannZeta_nonvanishing
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex} {deltaStar : ℝ -> ℝ}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultFiniteAndGlueData FX deltaStar) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultData hId hAnalytic hConv hData

theorem routeK_default_taylor_offaxis_riemannZeta_nonvanishing
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex} {deltaStar : ℝ -> ℝ}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultFiniteAndGlueTaylorData FX deltaStar) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultTaylorData
    hId hAnalytic hConv hData

theorem routeK_default_globalBound_offaxis_riemannZeta_nonvanishing
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData
    hId hAnalytic hConv hData

theorem routeK_default_globalBound_offaxis_riemannZeta_nonvanishing_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData_of_cutoffAnalyticData
    hId hAnalyticData hConv hData

theorem routeK_default_globalBound_offaxis_riemannZeta_nonvanishing_of_cutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hApprox : CutoffApproximationData FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData_of_cutoffData
    hId hApprox hData

theorem routeK_default_globalBound_taylor_offaxis_riemannZeta_nonvanishing
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundTaylorData
    hId hAnalytic hConv hData

theorem
    routeK_default_globalBound_taylor_offaxis_riemannZeta_nonvanishing_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundTaylorData_of_cutoffAnalyticData
    hId hAnalyticData hConv hData

theorem routeK_default_globalBound_taylor_offaxis_riemannZeta_nonvanishing_of_cutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hApprox : CutoffApproximationData FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundTaylorData_of_cutoffData
    hId hApprox hData

theorem routeK_default_globalBound_poleCleared_offaxis_riemannZeta_nonvanishing
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData_of_poleClearedAnalytic
    hIdData hAnalytic hConv hData

theorem
    routeK_default_globalBound_poleCleared_offaxis_riemannZeta_nonvanishing_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact
    riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData_of_poleClearedAnalytic_of_cutoffAnalyticData
    hIdData
    hAnalyticData
    hConv
    hData

theorem
    routeK_default_globalBound_poleCleared_offaxis_riemannZeta_nonvanishing_of_cutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hApprox : CutoffApproximationData FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData_of_poleClearedCutoffData
    hIdData hApprox hData

theorem
  routeK_default_globalBound_taylor_poleCleared_offaxis_riemannZeta_nonvanishing
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact
    riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundTaylorData_of_poleClearedAnalytic
    hIdData
    hAnalytic
    hConv
    hData

theorem
    routeK_default_globalBound_taylor_poleCleared_offaxis_riemannZeta_nonvanishing_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact
    riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundTaylorData_of_poleClearedAnalytic_of_cutoffAnalyticData
    hIdData
    hAnalyticData
    hConv
    hData

theorem
    routeK_default_globalBound_taylor_poleCleared_offaxis_riemannZeta_nonvanishing_of_cutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hApprox : CutoffApproximationData FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    offCriticalStripNonvanishing riemannZeta := by
  exact
    riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundTaylorData_of_poleClearedAnalytic_of_cutoffAnalyticData
    hIdData
    hApprox.hAnalyticData
    hApprox.hConv
    hData

/-!
Transfer layer from continued numerator nonvanishing to zeta nonvanishing.

Primary sources:
- docs/c2_bulk_offaxis_transfer.md
- Lean/Antigo_Lean_C2/Continuation.lean

This file only uses the continuation identity from Thm 17. The genuinely analytic step
from cutoff nonvanishing to continued numerator nonvanishing is consumed from `Hurwitz.lean`.
-/

end LeanC2
