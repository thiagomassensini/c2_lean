import Mathlib
import LeanC2.Finite.FiniteCertificate
import LeanC2.Transfer.ZetaTransfer

set_option linter.style.longLine false

namespace LeanC2

/-- C2-form statement of RH: every zero in the open critical strip lies on the critical line. -/
def RiemannHypothesisC2 : Prop :=
  ∀ s : Complex, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = (1 : ℝ) / 2

/-- Off-axis nonvanishing on the critical strip implies the C2 form of RH. -/
theorem riemannHypothesisC2_of_offCriticalStripNonvanishing
    (hOff : offCriticalStripNonvanishing riemannZeta) :
    RiemannHypothesisC2 := by
  intro s hz hs0 hs1
  by_contra hsHalf
  exact hOff s ⟨hs0, hs1, hsHalf⟩ hz

/-- Pointwise critical-line restriction extracted from the packaged C2 form of RH. -/
theorem riemannZeta_zero_on_criticalLine_of_riemannHypothesisC2
    (hRH : RiemannHypothesisC2) {s : Complex}
    (hz : riemannZeta s = 0) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    s.re = (1 : ℝ) / 2 := by
  exact hRH s hz hs0 hs1

/-- Pointwise critical-line restriction obtained from off-strip nonvanishing. -/
theorem riemannZeta_zero_on_criticalLine_of_offCriticalStripNonvanishing
    (hOff : offCriticalStripNonvanishing riemannZeta) {s : Complex}
    (hz : riemannZeta s = 0) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    s.re = (1 : ℝ) / 2 := by
  exact riemannZeta_zero_on_criticalLine_of_riemannHypothesisC2
    (riemannHypothesisC2_of_offCriticalStripNonvanishing hOff) hz hs0 hs1

/-- Final RH packaging from nonvanishing of the continued numerator on the off-critical strip. -/
theorem riemannHypothesisC2_of_numFunNonvanishing
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hNum : offCriticalStripNonvanishing numFun) :
    RiemannHypothesisC2 := by
  apply riemannHypothesisC2_of_offCriticalStripNonvanishing
  exact riemannZeta_nonvanishing_offCriticalStrip_of_numFunNonvanishing hId hNum

/-- Final RH packaging directly from a nonvanishing cutoff family and the Hurwitz bridge. -/
theorem riemannHypothesisC2_of_hurwitz
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
  (hFX : cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX) :
    RiemannHypothesisC2 := by
  apply riemannHypothesisC2_of_offCriticalStripNonvanishing
  exact riemannZeta_nonvanishing_offCriticalStrip_of_hurwitz hId hAnalytic hConv hFX

/-- Final RH packaging from finite coverage plus high-height gluing. -/
theorem riemannHypothesisC2_of_finite_and_high
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex} {H : ℝ}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hFinite : cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip FX H)
    (hHigh : cutoffFamilyEventuallyNonvanishingOnHighOffCriticalStrip FX H) :
    RiemannHypothesisC2 := by
  apply riemannHypothesisC2_of_offCriticalStripNonvanishing
  exact riemannZeta_nonvanishing_offCriticalStrip_of_finite_and_high
    hId hAnalytic hConv hFinite hHigh

theorem riemannHypothesisC2_of_finite_and_high_of_le
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex} {T0 H : ℝ}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hT : T0 ≤ H)
    (hFinite : cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip FX H)
    (hHigh : cutoffFamilyEventuallyNonvanishingOnHighOffCriticalStrip FX T0) :
    RiemannHypothesisC2 := by
  apply riemannHypothesisC2_of_offCriticalStripNonvanishing
  exact riemannZeta_nonvanishing_offCriticalStrip_of_finite_and_high_of_le
    hId hAnalytic hConv hT hFinite hHigh

theorem riemannHypothesisC2_of_default_finite_and_high
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hFinite : cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip FX defaultCertifiedHeight)
    (hHigh : cutoffFamilyEventuallyNonvanishingOnHighOffCriticalStrip FX defaultT0) :
    RiemannHypothesisC2 := by
  apply riemannHypothesisC2_of_offCriticalStripNonvanishing
  exact riemannZeta_nonvanishing_offCriticalStrip_of_default_finite_and_high
    hId hAnalytic hConv hFinite hHigh

theorem riemannHypothesisC2_of_default_finite_and_glue
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex} {deltaStar : ℝ -> ℝ}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hDelta : ∀ t : ℝ, 0 ≤ deltaStar t)
    (hNear : nearRegionEventuallyNonvanishing FX deltaStar defaultT0)
    (hBulk : bulkRegionEventuallyNonvanishing FX deltaStar defaultEps defaultT0)
    (hEdge : edgeRegionEventuallyNonvanishing FX defaultEps defaultT0)
    (hFinite : cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip FX defaultCertifiedHeight) :
    RiemannHypothesisC2 := by
  apply riemannHypothesisC2_of_offCriticalStripNonvanishing
  exact riemannZeta_nonvanishing_offCriticalStrip_of_default_finite_and_glue
    hId hAnalytic hConv hDelta hNear hBulk hEdge hFinite

theorem riemannHypothesisC2_of_defaultData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex} {deltaStar : ℝ -> ℝ}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultFiniteAndGlueData FX deltaStar) :
    RiemannHypothesisC2 := by
  apply riemannHypothesisC2_of_offCriticalStripNonvanishing
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultData hId hAnalytic hConv hData

theorem riemannHypothesisC2_of_defaultTaylorData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex} {deltaStar : ℝ -> ℝ}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultFiniteAndGlueTaylorData FX deltaStar) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultData hId hAnalytic hConv
    (defaultFiniteAndGlueData_of_taylorData hData)

theorem riemannHypothesisC2_of_defaultGlobalBoundData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    RiemannHypothesisC2 := by
  apply riemannHypothesisC2_of_offCriticalStripNonvanishing
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData
    hId hAnalytic hConv hData

/-- Pointwise zero restriction along the default global-bound route. -/
theorem riemannZeta_zero_on_criticalLine_of_defaultGlobalBoundData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundData FX)
    {s : Complex} (hz : riemannZeta s = 0) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    s.re = (1 : ℝ) / 2 := by
  exact riemannZeta_zero_on_criticalLine_of_riemannHypothesisC2
    (riemannHypothesisC2_of_defaultGlobalBoundData hId hAnalytic hConv hData) hz hs0 hs1

theorem riemannHypothesisC2_of_defaultGlobalBoundData_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundData
    hId (cutoffAnalyticOnOffCriticalStrip_of_data hAnalyticData) hConv hData

theorem riemannHypothesisC2_of_defaultGlobalBoundData_of_cutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hApprox : CutoffApproximationData FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundData_of_cutoffAnalyticData
    hId hApprox.hAnalyticData hApprox.hConv hData

theorem riemannHypothesisC2_of_defaultGlobalBoundData_of_canonicalCutoffFamily
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultGlobalBoundData canonicalCutoffFamily) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundData_of_cutoffData
    hId (canonicalCutoffFamily_approximationData_of_convergence hConv) hData

theorem
  riemannHypothesisC2_of_defaultGlobalBoundData_of_sharpCutoff_coeffBound
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hSharp :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip sharpCutoffFamily numFun)
    (hResidual : canonicalCutoffResidualCoeffUniformlyBoundedOnOffCriticalStrip)
    (hData : DefaultGlobalBoundData canonicalCutoffFamily) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundData_of_cutoffData
    hId
    (canonicalCutoffFamily_approximationData_of_sharpCutoff_coeffBound hSharp hResidual)
    hData

theorem riemannHypothesisC2_of_defaultGlobalBoundTaylorData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    RiemannHypothesisC2 := by
  apply riemannHypothesisC2_of_offCriticalStripNonvanishing
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundTaylorData
    hId hAnalytic hConv hData

/-- Pointwise zero restriction along the default Taylor global-bound route. -/
theorem riemannZeta_zero_on_criticalLine_of_defaultGlobalBoundTaylorData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX)
    {s : Complex} (hz : riemannZeta s = 0) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    s.re = (1 : ℝ) / 2 := by
  exact riemannZeta_zero_on_criticalLine_of_riemannHypothesisC2
    (riemannHypothesisC2_of_defaultGlobalBoundTaylorData hId hAnalytic hConv hData)
    hz hs0 hs1

theorem riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundTaylorData
    hId (cutoffAnalyticOnOffCriticalStrip_of_data hAnalyticData) hConv hData

theorem riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_cutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hApprox : CutoffApproximationData FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_cutoffAnalyticData
    hId hApprox.hAnalyticData hApprox.hConv hData

theorem riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_canonicalCutoffFamily
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultGlobalBoundTaylorData canonicalCutoffFamily) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_cutoffData
    hId (canonicalCutoffFamily_approximationData_of_convergence hConv) hData

theorem
  riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_sharpCutoff_coeffBound
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hSharp :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip sharpCutoffFamily numFun)
    (hResidual : canonicalCutoffResidualCoeffUniformlyBoundedOnOffCriticalStrip)
    (hData : DefaultGlobalBoundTaylorData canonicalCutoffFamily) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_cutoffData
    hId
    (canonicalCutoffFamily_approximationData_of_sharpCutoff_coeffBound hSharp hResidual)
    hData

theorem riemannHypothesisC2_of_defaultGlobalBoundData_of_poleClearedAnalytic
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundData
    (fundamentalIdentity_riemannZeta_on_puncturedRightHalfPlane_of_data hIdData)
    hAnalytic hConv hData

theorem
    riemannHypothesisC2_of_defaultGlobalBoundData_of_poleClearedAnalytic_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundData_of_poleClearedAnalytic
    hIdData (cutoffAnalyticOnOffCriticalStrip_of_data hAnalyticData) hConv hData

theorem riemannHypothesisC2_of_defaultGlobalBoundData_of_poleClearedCutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hApprox : CutoffApproximationData FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    RiemannHypothesisC2 := by
  exact
    riemannHypothesisC2_of_defaultGlobalBoundData_of_poleClearedAnalytic_of_cutoffAnalyticData
    hIdData
    hApprox.hAnalyticData
    hApprox.hConv
    hData

theorem riemannHypothesisC2_of_defaultGlobalBoundData_of_poleClearedCanonicalCutoffFamily
    {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultGlobalBoundData canonicalCutoffFamily) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundData_of_poleClearedCutoffData
    hIdData (canonicalCutoffFamily_approximationData_of_convergence hConv) hData

theorem
  riemannHypothesisC2_of_defaultGlobalBoundData_of_poleClearedSharpCutoff_coeffBound
    {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hSharp :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip sharpCutoffFamily numFun)
    (hResidual : canonicalCutoffResidualCoeffUniformlyBoundedOnOffCriticalStrip)
    (hData : DefaultGlobalBoundData canonicalCutoffFamily) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundData_of_poleClearedCutoffData
    hIdData
    (canonicalCutoffFamily_approximationData_of_sharpCutoff_coeffBound hSharp hResidual)
    hData

theorem riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_poleClearedAnalytic
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundTaylorData
    (fundamentalIdentity_riemannZeta_on_puncturedRightHalfPlane_of_data hIdData)
    hAnalytic hConv hData

theorem
    riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_poleClearedAnalytic_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_poleClearedAnalytic
    hIdData (cutoffAnalyticOnOffCriticalStrip_of_data hAnalyticData) hConv hData

theorem
  riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_poleClearedCutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hApprox : CutoffApproximationData FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    RiemannHypothesisC2 := by
  exact
    riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_poleClearedAnalytic_of_cutoffAnalyticData
    hIdData
    hApprox.hAnalyticData
    hApprox.hConv
    hData

theorem
  riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_poleClearedCanonicalCutoffFamily
    {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultGlobalBoundTaylorData canonicalCutoffFamily) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_poleClearedCutoffData
    hIdData (canonicalCutoffFamily_approximationData_of_convergence hConv) hData

theorem
  riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_poleClearedSharpCutoff_coeffBound
    {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hSharp :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip sharpCutoffFamily numFun)
    (hResidual : canonicalCutoffResidualCoeffUniformlyBoundedOnOffCriticalStrip)
    (hData : DefaultGlobalBoundTaylorData canonicalCutoffFamily) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_poleClearedCutoffData
    hIdData
    (canonicalCutoffFamily_approximationData_of_sharpCutoff_coeffBound hSharp hResidual)
    hData

theorem routeK_default_chain_RH
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex} {deltaStar : ℝ -> ℝ}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultFiniteAndGlueData FX deltaStar) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultData hId hAnalytic hConv hData

theorem routeK_default_taylor_chain_RH
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex} {deltaStar : ℝ -> ℝ}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultFiniteAndGlueTaylorData FX deltaStar) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultTaylorData hId hAnalytic hConv hData

theorem routeK_default_globalBound_chain_RH
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundData hId hAnalytic hConv hData

theorem routeK_default_globalBound_chain_RH_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundData_of_cutoffAnalyticData
    hId hAnalyticData hConv hData

theorem routeK_default_globalBound_chain_RH_of_cutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hApprox : CutoffApproximationData FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundData_of_cutoffData hId hApprox hData

theorem routeK_default_globalBound_chain_RH_of_canonicalCutoffFamily
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultGlobalBoundData canonicalCutoffFamily) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundData_of_canonicalCutoffFamily hId hConv hData

theorem routeK_default_globalBound_chain_RH_of_sharpCutoff_coeffBound
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hSharp :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip sharpCutoffFamily numFun)
    (hResidual : canonicalCutoffResidualCoeffUniformlyBoundedOnOffCriticalStrip)
    (hData : DefaultGlobalBoundData canonicalCutoffFamily) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundData_of_sharpCutoff_coeffBound
    hId hSharp hResidual hData

theorem routeK_default_globalBound_taylor_chain_RH
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundTaylorData hId hAnalytic hConv hData

theorem routeK_default_globalBound_taylor_chain_RH_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_cutoffAnalyticData
    hId hAnalyticData hConv hData

theorem routeK_default_globalBound_taylor_chain_RH_of_cutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hApprox : CutoffApproximationData FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_cutoffData hId hApprox hData

theorem routeK_default_globalBound_taylor_chain_RH_of_canonicalCutoffFamily
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultGlobalBoundTaylorData canonicalCutoffFamily) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_canonicalCutoffFamily hId hConv hData

theorem routeK_default_globalBound_taylor_chain_RH_of_sharpCutoff_coeffBound
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hSharp :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip sharpCutoffFamily numFun)
    (hResidual : canonicalCutoffResidualCoeffUniformlyBoundedOnOffCriticalStrip)
    (hData : DefaultGlobalBoundTaylorData canonicalCutoffFamily) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_sharpCutoff_coeffBound
    hId hSharp hResidual hData

theorem routeK_default_globalBound_poleCleared_chain_RH
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundData_of_poleClearedAnalytic
    hIdData hAnalytic hConv hData

theorem
    routeK_default_globalBound_poleCleared_chain_RH_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundData_of_poleClearedAnalytic_of_cutoffAnalyticData
    hIdData hAnalyticData hConv hData

theorem routeK_default_globalBound_poleCleared_chain_RH_of_cutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hApprox : CutoffApproximationData FX numFun)
    (hData : DefaultGlobalBoundData FX) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundData_of_poleClearedCutoffData
    hIdData hApprox hData

theorem routeK_default_globalBound_poleCleared_chain_RH_of_canonicalCutoffFamily
    {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultGlobalBoundData canonicalCutoffFamily) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundData_of_poleClearedCanonicalCutoffFamily
    hIdData hConv hData

theorem routeK_default_globalBound_poleCleared_chain_RH_of_sharpCutoff_coeffBound
    {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hSharp :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip sharpCutoffFamily numFun)
    (hResidual : canonicalCutoffResidualCoeffUniformlyBoundedOnOffCriticalStrip)
    (hData : DefaultGlobalBoundData canonicalCutoffFamily) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundData_of_poleClearedSharpCutoff_coeffBound
    hIdData hSharp hResidual hData

theorem routeK_default_globalBound_taylor_poleCleared_chain_RH
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_poleClearedAnalytic
    hIdData hAnalytic hConv hData

theorem
    routeK_default_globalBound_taylor_poleCleared_chain_RH_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_poleClearedAnalytic_of_cutoffAnalyticData
    hIdData hAnalyticData hConv hData

theorem routeK_default_globalBound_taylor_poleCleared_chain_RH_of_cutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hApprox : CutoffApproximationData FX numFun)
    (hData : DefaultGlobalBoundTaylorData FX) :
    RiemannHypothesisC2 := by
  exact
    riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_poleClearedCutoffData
    hIdData
    hApprox
    hData

theorem routeK_default_globalBound_taylor_poleCleared_chain_RH_of_canonicalCutoffFamily
    {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultGlobalBoundTaylorData canonicalCutoffFamily) :
    RiemannHypothesisC2 := by
  exact
    riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_poleClearedCanonicalCutoffFamily
    hIdData
    hConv
    hData

theorem routeK_default_globalBound_taylor_poleCleared_chain_RH_of_sharpCutoff_coeffBound
    {numFun : Complex -> Complex}
    (hIdData : PoleClearedRiemannZetaData numFun)
    (hSharp :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip sharpCutoffFamily numFun)
    (hResidual : canonicalCutoffResidualCoeffUniformlyBoundedOnOffCriticalStrip)
    (hData : DefaultGlobalBoundTaylorData canonicalCutoffFamily) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_poleClearedSharpCutoff_coeffBound
    hIdData hSharp hResidual hData

/-!
Final Riemann-Hypothesis packaging in the C2 architecture.

Primary sources:
- docs/c2_bulk_offaxis_transfer.md

Legacy seeds:
- Lean/Antigo_Lean_C2/Continuation.lean
- Lean/Antigo_Lean_C2/Chain.lean
-/

end LeanC2
