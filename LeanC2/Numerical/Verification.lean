import Mathlib
import LeanC2.CriticalLine.Nonvanishing
import LeanC2.Finite.FiniteCertificate
import LeanC2.Numerical.Constants
import LeanC2.Transfer.RH

set_option linter.style.whitespace false

namespace LeanC2

/--
Reserved entry point for external numerical or analytic data that certifies the canonical
off-strip route through the explicit global Taylor-radius model
`δ*(γ) ≥ 2 / (2A + C log^2 γ)`.
-/
abbrev DefaultCanonicalOffStripVerificationData :=
  DefaultGlobalBoundData canonicalCutoffFamily

/--
Reserved entry point for external analytic data that certifies the canonical off-strip route
through the theoretical model driven by the proved `c0'/c0` bound.
-/
abbrev DefaultCanonicalOffStripTheoreticalVerificationData :=
  DefaultFiniteAndGlueData canonicalCutoffFamily theoreticalDeltaStarLowerModel

/--
Reserved entry point for external data that certifies the canonical off-strip route at the more
primitive Taylor-witness level.
-/
abbrev DefaultCanonicalOffStripTaylorVerificationData :=
  DefaultGlobalBoundTaylorData canonicalCutoffFamily

/--
Reserved entry point for external analytic data that certifies the canonical off-strip route at
the Taylor-witness level using the theoretical `c0'/c0` bound.
-/
abbrev DefaultCanonicalOffStripTheoreticalTaylorVerificationData :=
  DefaultFiniteAndGlueTaylorData canonicalCutoffFamily theoreticalDeltaStarLowerModel

/--
Reserved entry point for external numerical data that certifies the canonical critical-line route.
-/
abbrev DefaultCanonicalCriticalLineVerificationData :=
  DefaultCanonicalCriticalLineAsymptoticData

theorem
    canonicalCutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_defaultOffStripVerificationData
    (hData : DefaultCanonicalOffStripVerificationData) :
    cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip canonicalCutoffFamily := by
  exact cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_defaultGlobalBoundData hData

theorem
  canonicalCutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_defaultOffStripTheoreticalData
    (hData : DefaultCanonicalOffStripTheoreticalVerificationData) :
    cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip canonicalCutoffFamily := by
  exact cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_defaultData hData

theorem
    canonicalCutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_defaultTaylorData
    (hData : DefaultCanonicalOffStripTaylorVerificationData) :
    cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip canonicalCutoffFamily := by
  exact
    cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_defaultGlobalBoundTaylorData hData

theorem
    canonicalCutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_defaultTheoreticalTaylorData
    (hData : DefaultCanonicalOffStripTheoreticalTaylorVerificationData) :
    cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip canonicalCutoffFamily := by
  exact cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_defaultTaylorData hData

theorem canonicalCutoffFamilyEventuallyNonvanishingOnCriticalLine_of_defaultVerificationData
    (hData : DefaultCanonicalCriticalLineVerificationData) :
    cutoffFamilyEventuallyNonvanishingOnCriticalLine canonicalCutoffFamily := by
  exact canonicalCutoffFamilyEventuallyNonvanishingOnCriticalLine_of_defaultAsymptoticData hData

theorem
  canonicalOffStrip_riemannZeta_nonvanishing_of_defaultVerificationData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultCanonicalOffStripVerificationData) :
    offCriticalStripNonvanishing riemannZeta := by
  exact routeK_default_globalBound_offaxis_riemannZeta_nonvanishing_of_canonicalCutoffFamily
    hId hConv hData

theorem
  canonicalOffStrip_riemannZeta_nonvanishing_of_defaultTheoreticalVerificationData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultCanonicalOffStripTheoreticalVerificationData) :
    offCriticalStripNonvanishing riemannZeta := by
  have hApprox := canonicalCutoffFamily_approximationData_of_convergence hConv
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultData
    hId
    (cutoffAnalyticOnOffCriticalStrip_of_data hApprox.hAnalyticData)
    hApprox.hConv
    hData

theorem
  canonicalOffStrip_riemannZeta_nonvanishing_of_defaultTaylorVerificationData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultCanonicalOffStripTaylorVerificationData) :
    offCriticalStripNonvanishing riemannZeta := by
  exact
    routeK_default_globalBound_taylor_offaxis_riemannZeta_nonvanishing_of_canonicalCutoffFamily
    hId hConv hData

theorem
  canonicalOffStrip_riemannZeta_nonvanishing_of_defaultTheoreticalTaylorVerificationData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultCanonicalOffStripTheoreticalTaylorVerificationData) :
    offCriticalStripNonvanishing riemannZeta := by
  have hApprox := canonicalCutoffFamily_approximationData_of_convergence hConv
  exact riemannZeta_nonvanishing_offCriticalStrip_of_defaultTaylorData
    hId
    (cutoffAnalyticOnOffCriticalStrip_of_data hApprox.hAnalyticData)
    hApprox.hConv
    hData

theorem riemannHypothesisC2_of_defaultOffStripVerificationData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultCanonicalOffStripVerificationData) :
    RiemannHypothesisC2 := by
  exact routeK_default_globalBound_chain_RH_of_canonicalCutoffFamily hId hConv hData

theorem riemannHypothesisC2_of_defaultOffStripTheoreticalVerificationData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultCanonicalOffStripTheoreticalVerificationData) :
    RiemannHypothesisC2 := by
  have hApprox := canonicalCutoffFamily_approximationData_of_convergence hConv
  exact riemannHypothesisC2_of_defaultData
    hId
    (cutoffAnalyticOnOffCriticalStrip_of_data hApprox.hAnalyticData)
    hApprox.hConv
    hData

theorem
  riemannHypothesisC2_of_defaultOffStripTaylorVerificationData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultCanonicalOffStripTaylorVerificationData) :
    RiemannHypothesisC2 := by
  exact routeK_default_globalBound_taylor_chain_RH_of_canonicalCutoffFamily hId hConv hData

theorem riemannHypothesisC2_of_defaultOffStripTheoreticalTaylorVerificationData
    {numFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta)
    (hConv :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun)
    (hData : DefaultCanonicalOffStripTheoreticalTaylorVerificationData) :
    RiemannHypothesisC2 := by
  have hApprox := canonicalCutoffFamily_approximationData_of_convergence hConv
  exact riemannHypothesisC2_of_defaultTaylorData
    hId
    (cutoffAnalyticOnOffCriticalStrip_of_data hApprox.hAnalyticData)
    hApprox.hConv
    hData

/-!
Reserved module for importing external numerical certificates as explicit assumptions.

Current endpoints:
- `DefaultCanonicalOffStripVerificationData` and
  `DefaultCanonicalOffStripTaylorVerificationData` for the off-strip route driven by the explicit
  model `δ*(γ) ≥ 2 / (2A + C log^2 γ)` from the certified global bound.
- `DefaultCanonicalOffStripTheoreticalVerificationData` and
  `DefaultCanonicalOffStripTheoreticalTaylorVerificationData` for the parallel off-strip route
  driven by the proved critical-line bound on `α = c0'/c0`, hence by the theoretical model
  `theoreticalDeltaStarLowerModel`.
- `DefaultCanonicalCriticalLineVerificationData` for the critical-line route driven by the explicit
  residual dominance hypothesis `‖canonicalCutoffResidual‖ < (7/10) * ‖cutoffFirstShell‖`.

Natural producers for the off-strip package are the current global-bound and transfer sources,
notably `docs/c2_certificacao_bound_global.md`, `docs/c2_bulk_offaxis_transfer.md`, and the
existing bulk/coverage scripts. Natural producers for the critical-line package are the scripts
that probe the cutoff family on `Re(s)=1/2`, such as `scripts/colagem_global.py`,
`scripts/2_gpu_c2_zero_detector_genuine.py`, and `scripts/route_K7_rigorous_closure.py`.
-/

end LeanC2