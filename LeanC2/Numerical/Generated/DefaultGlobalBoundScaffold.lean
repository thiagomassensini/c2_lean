import LeanC2.Numerical.Generated.FiniteHeightCertificate
import LeanC2.Numerical.Generated.HighStripCertificates

set_option linter.style.whitespace false

namespace LeanC2

theorem canonicalDefaultGlobalBoundData_of_generatedHighCertificates
    (hFinite : CanonicalFiniteHeightGlobalBoundCertificate) :
    DefaultGlobalBoundData canonicalCutoffFamily := by
  exact canonicalDefaultGlobalBoundData_of_components
    hFinite
    certifiedCanonicalNearAxisGlobalBoundTaylorCertificate
    certifiedCanonicalBulkGlobalBoundCertificate
    certifiedCanonicalEdgeGlobalBoundCertificate

theorem canonicalDefaultGlobalBoundTaylorData_of_generatedHighCertificates
    (hFinite : CanonicalFiniteHeightGlobalBoundCertificate) :
    DefaultGlobalBoundTaylorData canonicalCutoffFamily := by
  exact canonicalDefaultGlobalBoundTaylorData_of_components
    hFinite
    certifiedCanonicalNearAxisGlobalBoundTaylorCertificate
    certifiedCanonicalBulkGlobalBoundCertificate
    certifiedCanonicalEdgeGlobalBoundCertificate

theorem canonicalDefaultGlobalBoundData_of_generatedCertificates :
    DefaultGlobalBoundData canonicalCutoffFamily := by
  exact canonicalDefaultGlobalBoundData_of_generatedHighCertificates
    certifiedCanonicalFiniteHeightGlobalBoundCertificate

theorem canonicalDefaultGlobalBoundTaylorData_of_generatedCertificates :
    DefaultGlobalBoundTaylorData canonicalCutoffFamily := by
  exact canonicalDefaultGlobalBoundTaylorData_of_generatedHighCertificates
    certifiedCanonicalFiniteHeightGlobalBoundCertificate

theorem canonicalCutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_generatedCertificates :
    cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip canonicalCutoffFamily := by
  exact cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_defaultGlobalBoundData
    canonicalDefaultGlobalBoundData_of_generatedCertificates

end LeanC2