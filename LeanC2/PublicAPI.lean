import LeanC2.Foundations.Tilt
import LeanC2.Identity.C0NonZero
import LeanC2.Identity.FundamentalIdentity
import LeanC2.Identity.MeromorphicExt
import LeanC2.NearAxis.TaylorRadius
import LeanC2.Numerical.Generated.DefaultGlobalBoundScaffold
import LeanC2.Transfer.Hurwitz
import LeanC2.Transfer.ZetaTransfer
import LeanC2.Transfer.RH

namespace LeanC2

/--
Public critical-line characterization of tilt annihilation in the
right-half-plane parametrization.
-/
theorem tiltBracket_zero_iff_sigma_half_on_rightHalfPlane
    {sigma c : Real} (hsigma : 0 < sigma) (hc : 1 < c) :
    tiltBracket (sigma - (1 : Real) / 2) c = 0 ↔ sigma = (1 : Real) / 2 := by
  exact tiltBracket_eq_zero_iff_sigma_half_of_sigma_pos hsigma hc

/-- Public nonvanishing form of tilt away from the critical line. -/
theorem tiltBracket_nonzero_off_criticalLine_on_rightHalfPlane
    {sigma c : Real} (hsigma : 0 < sigma) (hc : 1 < c)
    (hhalf : sigma ≠ (1 : Real) / 2) :
    tiltBracket (sigma - (1 : Real) / 2) c ≠ 0 := by
  exact tiltBracket_ne_zero_of_sigma_pos_of_ne_half hsigma hc hhalf

/-- Formal alias for nonvanishing of `c0` on the open right half-plane. -/
theorem c0_nonzero_on_rightHalfPlane {s : Complex} (hs : 0 < s.re) : c0 s ≠ 0 := by
  exact c0_ne_zero_of_re_pos hs

/-- Formal alias for nonvanishing of `c0` on the critical line. -/
theorem c0_nonzero_on_criticalLine (t : Real) :
    c0 (((1 : Complex) / 2) + t * Complex.I) ≠ 0 := by
  exact c0_ne_zero_on_critical t

/-- Coordinate ratio form of the convergent-side fundamental identity. -/
theorem fundamentalIdentity_ratio_on_rightHalfPlaneCoordinate
    {zetaFun : Complex -> Complex}
    (hId : fundamentalIdentityOnRightHalfPlane zetaFun)
    {sigma t : Real} (hsigma : 1 < sigma) :
    FInfinity ((sigma : Complex) + t * Complex.I) /
        c0 ((sigma : Complex) + t * Complex.I) =
      zetaFun ((sigma : Complex) + t * Complex.I) := by
  exact routeK_thm13_ratio_offaxis hId hsigma

/-- Coordinate nonvanishing transfer on the convergent side `Re(s) > 1`. -/
theorem fundamentalIdentity_nonzero_transfer_on_rightHalfPlaneCoordinate
    {zetaFun : Complex -> Complex}
    (hId : fundamentalIdentityOnRightHalfPlane zetaFun)
    {sigma t : Real} (hsigma : 1 < sigma) :
    FInfinity ((sigma : Complex) + t * Complex.I) ≠ 0 ↔
      zetaFun ((sigma : Complex) + t * Complex.I) ≠ 0 := by
  exact routeK_thm13_nonzero_transfer hId hsigma

/-- Coordinate ratio form of the punctured fundamental identity on the critical strip. -/
theorem puncturedFundamentalIdentity_ratio_on_offCriticalStripCoordinate
    {numFun zetaFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun zetaFun)
    {sigma t : Real} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    spectralZeta numFun ((sigma : Complex) + t * Complex.I) =
      zetaFun ((sigma : Complex) + t * Complex.I) := by
  exact routeK_thm17_ratio_offaxis hId hsigma0 hsigma1

/-- Coordinate nonvanishing transfer on the off-critical strip. -/
theorem puncturedFundamentalIdentity_nonzero_transfer_on_offCriticalStripCoordinate
    {numFun zetaFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun zetaFun)
    {sigma t : Real} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    numFun ((sigma : Complex) + t * Complex.I) ≠ 0 ↔
      zetaFun ((sigma : Complex) + t * Complex.I) ≠ 0 := by
  exact routeK_thm17_nonzero_transfer hId hsigma0 hsigma1

/-- Taylor domination of the linear term over the quadratic correction. -/
theorem taylorLinearTermDominatesQuadratic
    (m M₂ δ : ℝ)
    (hm : 0 < m) (hM₂ : 0 < M₂) (hδ : 0 < δ)
    (hδ_small : δ < taylorExclusionRadius m M₂) :
    0 < δ * m - δ ^ 2 / 2 * M₂ := by
  exact routeK_elo5_firstorder_dominates m M₂ δ hm hM₂ hδ hδ_small

/-- Positivity of the Taylor exclusion radius. -/
theorem taylorExclusionRadius_pos
    (m M₂ : ℝ) (hm : 0 < m) (hM₂ : 0 < M₂) :
    0 < taylorExclusionRadius m M₂ := by
  exact routeK_elo5_exclusion_radius_pos m M₂ hm hM₂

/-- Nonvanishing forced by the standard Taylor-dominance inequality. -/
theorem nonzero_of_taylorDominance
    (m M₂ R : ℝ) (hm : 0 < m) (hM₂ : 0 < M₂)
    (δ : ℝ) (hδ : 0 < δ) (hδ_small : δ < taylorExclusionRadius m M₂)
    (hR : 0 ≤ R) (hR_small : R < δ * m - δ ^ 2 / 2 * M₂)
    (F : Complex) (hF_lb : δ * m - δ ^ 2 / 2 * M₂ - R ≤ ‖F‖) :
    F ≠ 0 := by
  exact routeK_elo5_nonzero_from_taylor m M₂ R hm hM₂ δ hδ hδ_small hR hR_small F hF_lb

/-- Lower bound on the Taylor exclusion radius from an `M₂` upper bound. -/
theorem taylorExclusionRadius_lower_bound_from_M2Bound
    (m M₂ M₂bound : ℝ)
    (hm : 1 ≤ m) (hM₂pos : 0 < M₂) (hBoundPos : 0 < M₂bound)
    (hM₂le : M₂ ≤ M₂bound) :
    2 / M₂bound ≤ taylorExclusionRadius m M₂ := by
  exact routeK_thm10_deltaStar_lower_bound_from_M2bound
    m M₂ M₂bound hm hM₂pos hBoundPos hM₂le

/-- Scaled lower bound on the Taylor exclusion radius from an `M₂` upper bound. -/
theorem taylorExclusionRadius_scaled_lower_bound_from_M2Bound
    (m M₂ M₂bound : ℝ)
    (hm : 0 < m) (hM₂pos : 0 < M₂) (hBoundPos : 0 < M₂bound)
    (hM₂le : M₂ ≤ M₂bound) :
    2 * m / M₂bound ≤ taylorExclusionRadius m M₂ := by
  exact routeK_thm10_deltaStar_lower_bound_scaled_from_M2bound
    m M₂ M₂bound hm hM₂pos hBoundPos hM₂le

/-- Logarithmic lower bound on the Taylor exclusion radius. -/
theorem taylorExclusionRadius_lower_bound_logSqBound
    (m M₂ A C γ : ℝ)
    (hm : 1 ≤ m) (hM₂pos : 0 < M₂)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hM₂le : M₂ ≤ 2 * A + C * (Real.log γ) ^ 2) :
    2 / (2 * A + C * (Real.log γ) ^ 2) ≤ taylorExclusionRadius m M₂ := by
  exact routeK_thm10_deltaStar_lower_bound_logSq m M₂ A C γ hm hM₂pos hA hC hM₂le

/-- Scaled logarithmic lower bound on the Taylor exclusion radius. -/
theorem taylorExclusionRadius_scaled_lower_bound_logSqBound
    (m M₂ A C γ : ℝ)
    (hm : 0 < m) (hM₂pos : 0 < M₂)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hM₂le : M₂ ≤ 2 * A + C * (Real.log γ) ^ 2) :
    2 * m / (2 * A + C * (Real.log γ) ^ 2) ≤ taylorExclusionRadius m M₂ := by
  exact routeK_thm10_deltaStar_lower_bound_scaled_logSq m M₂ A C γ hm hM₂pos hA hC hM₂le

/-- Coordinate Hurwitz nonvanishing on the off-critical strip. -/
theorem continuedNumerator_nonzero_on_offCriticalStripCoordinate_of_hurwitz
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hAnalytic : cutoffAnalyticOnOffCriticalStrip FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hFX : cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX)
    {sigma t : Real} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hhalf : sigma ≠ (1 : ℝ) / 2) :
    numFun ((sigma : Complex) + t * Complex.I) ≠ 0 := by
  exact routeK_hurwitz_nonzero_offaxis hAnalytic hConv hFX hsigma0 hsigma1 hhalf

/-- Coordinate Hurwitz nonvanishing with analyticity supplied by cutoff data. -/
theorem continuedNumerator_nonzero_on_offCriticalStripCoordinate_of_cutoffAnalyticData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hAnalyticData : CutoffAnalyticData FX)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun)
    (hFX : cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX)
    {sigma t : Real} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hhalf : sigma ≠ (1 : ℝ) / 2) :
    numFun ((sigma : Complex) + t * Complex.I) ≠ 0 := by
  exact routeK_hurwitz_nonzero_offaxis_of_cutoffAnalyticData
    hAnalyticData hConv hFX hsigma0 hsigma1 hhalf

/-- Coordinate Hurwitz nonvanishing with the bundled cutoff approximation package. -/
theorem continuedNumerator_nonzero_on_offCriticalStripCoordinate_of_cutoffData
    {FX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hApprox : CutoffApproximationData FX numFun)
    (hFX : cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX)
    {sigma t : Real} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hhalf : sigma ≠ (1 : ℝ) / 2) :
    numFun ((sigma : Complex) + t * Complex.I) ≠ 0 := by
  exact routeK_hurwitz_nonzero_offaxis_of_cutoffData
    hApprox hFX hsigma0 hsigma1 hhalf

/-- Canonical-cutoff off-strip nonvanishing of `riemannZeta` from default global-bound data. -/
theorem canonicalCutoff_riemannZeta_nonvanishing_of_defaultGlobalBoundData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultGlobalBoundData canonicalCutoffFamily) :
    offCriticalStripNonvanishing riemannZeta := by
  exact
    riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData_of_canonicalCutoffFamily
      hId hConv hData

/--
Canonical-cutoff off-strip nonvanishing of `riemannZeta` from default Taylor global-bound data.
-/
theorem
  canonicalCutoff_riemannZeta_nonvanishing_of_defaultGlobalBoundTaylorData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultGlobalBoundTaylorData canonicalCutoffFamily) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundTaylorData_of_cutoffData
    hId
    (canonicalCutoffFamily_approximationData_of_convergence hConv)
    hData

/--
Sharp-cutoff coefficient-bound route to off-strip nonvanishing of `riemannZeta`.
-/
theorem sharpCutoffCoeffBound_riemannZeta_nonvanishing_of_defaultGlobalBoundData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hSharp :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip sharpCutoffFamily numFun)
    (hResidual : canonicalCutoffResidualCoeffUniformlyBoundedOnOffCriticalStrip)
    (hData : DefaultGlobalBoundData canonicalCutoffFamily) :
    offCriticalStripNonvanishing riemannZeta := by
  exact
    riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData_of_sharpCutoff_coeffBound
      hId hSharp hResidual hData

/--
Sharp-cutoff coefficient-bound route to off-strip nonvanishing of `riemannZeta` at Taylor level.
-/
theorem
  sharpCutoffCoeffBound_riemannZeta_nonvanishing_of_defaultGlobalBoundTaylorData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hSharp :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip sharpCutoffFamily numFun)
    (hResidual : canonicalCutoffResidualCoeffUniformlyBoundedOnOffCriticalStrip)
    (hData : DefaultGlobalBoundTaylorData canonicalCutoffFamily) :
    offCriticalStripNonvanishing riemannZeta := by
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundTaylorData_of_cutoffData
    hId
    (canonicalCutoffFamily_approximationData_of_sharpCutoff_coeffBound hSharp hResidual)
    hData

/-- Canonical-cutoff RH package from default global-bound data. -/
theorem canonicalCutoff_riemannHypothesis_of_defaultGlobalBoundData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultGlobalBoundData canonicalCutoffFamily) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundData_of_canonicalCutoffFamily hId hConv hData

/-- Canonical-cutoff RH package from default Taylor global-bound data. -/
theorem canonicalCutoff_riemannHypothesis_of_defaultGlobalBoundTaylorData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultGlobalBoundTaylorData canonicalCutoffFamily) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_canonicalCutoffFamily hId hConv hData

/-- Sharp-cutoff coefficient-bound RH package from default global-bound data. -/
theorem sharpCutoffCoeffBound_riemannHypothesis_of_defaultGlobalBoundData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hSharp :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip sharpCutoffFamily numFun)
    (hResidual : canonicalCutoffResidualCoeffUniformlyBoundedOnOffCriticalStrip)
    (hData : DefaultGlobalBoundData canonicalCutoffFamily) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundData_of_sharpCutoff_coeffBound
    hId hSharp hResidual hData

/-- Sharp-cutoff coefficient-bound RH package from default Taylor global-bound data. -/
theorem sharpCutoffCoeffBound_riemannHypothesis_of_defaultGlobalBoundTaylorData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hSharp :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip sharpCutoffFamily numFun)
    (hResidual : canonicalCutoffResidualCoeffUniformlyBoundedOnOffCriticalStrip)
    (hData : DefaultGlobalBoundTaylorData canonicalCutoffFamily) :
    RiemannHypothesisC2 := by
  exact riemannHypothesisC2_of_defaultGlobalBoundTaylorData_of_sharpCutoff_coeffBound
    hId hSharp hResidual hData

/-- Public pointwise form of the RH package: zeros in the strip lie on the critical line. -/
theorem riemannZeta_zero_on_criticalLine_of_riemannHypothesis
    (hRH : RiemannHypothesisC2) {s : Complex}
    (hz : riemannZeta s = 0) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    s.re = (1 : ℝ) / 2 := by
  exact riemannZeta_zero_on_criticalLine_of_riemannHypothesisC2 hRH hz hs0 hs1

/-- Canonical-cutoff pointwise critical-line restriction from default global-bound data. -/
theorem canonicalCutoff_riemannZeta_zero_on_criticalLine_of_defaultGlobalBoundData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultGlobalBoundData canonicalCutoffFamily)
    {s : Complex} (hz : riemannZeta s = 0) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    s.re = (1 : ℝ) / 2 := by
  exact riemannZeta_zero_on_criticalLine_of_riemannHypothesis
    (canonicalCutoff_riemannHypothesis_of_defaultGlobalBoundData hId hConv hData) hz hs0 hs1

/-- Canonical-cutoff pointwise critical-line restriction from default Taylor global-bound data. -/
theorem canonicalCutoff_riemannZeta_zero_on_criticalLine_of_defaultGlobalBoundTaylorData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultGlobalBoundTaylorData canonicalCutoffFamily)
    {s : Complex} (hz : riemannZeta s = 0) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    s.re = (1 : ℝ) / 2 := by
  exact riemannZeta_zero_on_criticalLine_of_riemannHypothesis
    (canonicalCutoff_riemannHypothesis_of_defaultGlobalBoundTaylorData hId hConv hData)
    hz hs0 hs1

/-- Public exported generated default global-bound package for the canonical cutoff family. -/
theorem canonicalCutoff_generatedDefaultGlobalBoundData :
    DefaultGlobalBoundData canonicalCutoffFamily := by
  exact canonicalDefaultGlobalBoundData_of_generatedCertificates

/-- Public exported generated Taylor package for the canonical cutoff family. -/
theorem canonicalCutoff_generatedDefaultGlobalBoundTaylorData :
    DefaultGlobalBoundTaylorData canonicalCutoffFamily := by
  exact canonicalDefaultGlobalBoundTaylorData_of_generatedCertificates

/-- Public exported off-strip nonvanishing of the canonical cutoff family from generated data. -/
theorem canonicalCutoff_eventuallyNonvanishingOnOffCriticalStrip_of_generatedCertificates :
    cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip canonicalCutoffFamily := by
  exact canonicalCutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_generatedCertificates

/-- Canonical-cutoff off-strip nonvanishing of `riemannZeta` from generated default data. -/
theorem canonicalCutoff_riemannZeta_nonvanishing_of_generatedDefaultGlobalBoundData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun) :
    offCriticalStripNonvanishing riemannZeta := by
  exact canonicalCutoff_riemannZeta_nonvanishing_of_defaultGlobalBoundData
    hId hConv canonicalCutoff_generatedDefaultGlobalBoundData

/-- Canonical-cutoff RH package from generated default global-bound data. -/
theorem canonicalCutoff_riemannHypothesis_of_generatedDefaultGlobalBoundData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun) :
    RiemannHypothesisC2 := by
  exact canonicalCutoff_riemannHypothesis_of_defaultGlobalBoundData
    hId hConv canonicalCutoff_generatedDefaultGlobalBoundData

/-- Pointwise critical-line restriction from generated default global-bound data. -/
theorem canonicalCutoff_riemannZeta_zero_on_criticalLine_of_generatedDefaultGlobalBoundData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    {s : Complex} (hz : riemannZeta s = 0) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    s.re = (1 : ℝ) / 2 := by
  exact canonicalCutoff_riemannZeta_zero_on_criticalLine_of_defaultGlobalBoundData
    hId hConv canonicalCutoff_generatedDefaultGlobalBoundData hz hs0 hs1

/-!
Stable public aliases for the main coordinate-level interfaces used in the off-axis chain.

This file keeps the implementation modules unchanged while exposing descriptive theorem names for
the current public surface.
-/

end LeanC2
