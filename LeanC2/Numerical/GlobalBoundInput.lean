import LeanC2.Finite.FiniteCertificate
import LeanC2.Glue.GlueTheorem
import LeanC2.NearAxis.FXNonZero
import LeanC2.Operators.Cutoff

set_option linter.style.whitespace false

namespace LeanC2

/--
External near-axis Taylor certificate for the canonical cutoff family using the default
log-square model `deltaStarLowerModel`.
-/
abbrev CanonicalNearAxisGlobalBoundTaylorCertificate : Prop :=
  ∃ X0 : Nat,
    ∀ X : Nat, X0 ≤ X -> ∀ s : Complex,
      nearRegion deltaStarLowerModel defaultT0 s ->
        taylorNonvanishingWitness (canonicalCutoffFamily X s) |criticalOffset s|

theorem canonicalNearAxisEventuallyNonvanishing_of_globalBoundTaylorCertificate
    (hCert : CanonicalNearAxisGlobalBoundTaylorCertificate) :
    nearRegionEventuallyNonvanishing canonicalCutoffFamily deltaStarLowerModel defaultT0 := by
  exact nearRegionEventuallyNonvanishing_of_taylorWitness hCert

/--
External finite-height certificate for the canonical cutoff family up to
`defaultCertifiedHeight`.
-/
abbrev CanonicalFiniteHeightGlobalBoundCertificate : Prop :=
  cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip
    canonicalCutoffFamily defaultCertifiedHeight

/--
External bulk-region certificate for the canonical cutoff family and the default
log-square model.
-/
abbrev CanonicalBulkGlobalBoundCertificate : Prop :=
  bulkRegionEventuallyNonvanishing
    canonicalCutoffFamily deltaStarLowerModel defaultEps defaultT0

/-- External edge-region certificate for the canonical cutoff family. -/
abbrev CanonicalEdgeGlobalBoundCertificate : Prop :=
  edgeRegionEventuallyNonvanishing canonicalCutoffFamily defaultEps defaultT0

theorem canonicalHighOffCriticalStripEventuallyNonvanishing_of_components
    (hTaylor : CanonicalNearAxisGlobalBoundTaylorCertificate)
    (hBulk : CanonicalBulkGlobalBoundCertificate)
    (hEdge : CanonicalEdgeGlobalBoundCertificate) :
    cutoffFamilyEventuallyNonvanishingOnHighOffCriticalStrip canonicalCutoffFamily defaultT0 := by
  exact glueTheorem_highOffCriticalStrip_deltaStarLowerModel_of_canonicalCutoffFamily
    (canonicalNearAxisEventuallyNonvanishing_of_globalBoundTaylorCertificate hTaylor)
    hBulk
    hEdge

theorem canonicalDefaultGlobalBoundTaylorData_of_components
    (hFinite :
      cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip
        canonicalCutoffFamily defaultCertifiedHeight)
    (hTaylor : CanonicalNearAxisGlobalBoundTaylorCertificate)
    (hBulk :
      bulkRegionEventuallyNonvanishing
        canonicalCutoffFamily deltaStarLowerModel defaultEps defaultT0)
    (hEdge : edgeRegionEventuallyNonvanishing canonicalCutoffFamily defaultEps defaultT0) :
    DefaultGlobalBoundTaylorData canonicalCutoffFamily := by
  exact ⟨hFinite, hTaylor, hBulk, hEdge⟩

theorem canonicalDefaultGlobalBoundData_of_components
    (hFinite :
      cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip
        canonicalCutoffFamily defaultCertifiedHeight)
    (hTaylor : CanonicalNearAxisGlobalBoundTaylorCertificate)
    (hBulk :
      bulkRegionEventuallyNonvanishing
        canonicalCutoffFamily deltaStarLowerModel defaultEps defaultT0)
    (hEdge : edgeRegionEventuallyNonvanishing canonicalCutoffFamily defaultEps defaultT0) :
    DefaultGlobalBoundData canonicalCutoffFamily := by
  exact defaultGlobalBoundData_of_taylorData
    (canonicalDefaultGlobalBoundTaylorData_of_components hFinite hTaylor hBulk hEdge)

/-!
Lean-side hook for importing the numerical global Taylor-radius certification.

This file isolates the exact propositions that the external certification artifacts should deliver
for the canonical off-strip route. The near-axis hook is specialized to the Taylor-radius model,
while bulk and edge are kept at the regional eventual-nonvanishing level. The only remaining
independent component not covered here is the finite-height strip certificate.
-/

end LeanC2