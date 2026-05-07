import Mathlib
import LeanC2.Bulk.FXNonZeroBulk
import LeanC2.NearAxis.GlobalBound

namespace LeanC2

/--
Canonical Route 3 bulk certificate.

The limiting function is the C2 numerator `FInfinity`.  The bound function hidden in
`Route3BulkCertificate` corresponds to the bulk notes' lower bound
`c_min(eps) * exp(-C_* (log T)^(2/3+eta))`; the certificate also includes the cutoff
coupling `|F_X - FInfinity| < B` for all sufficiently large cutoffs.
-/
abbrev Route3CanonicalBulkCertificate : Prop :=
  Route3BulkCertificate
    canonicalCutoffFamily FInfinity deltaStarLowerModel defaultEps defaultT0

/--
Route 3 closes the canonical bulk leg once its lower-bound and cutoff-coupling inputs
are supplied.
-/
theorem canonicalBulkGlobalBoundCertificate_of_route3
    (hRoute3 : Route3CanonicalBulkCertificate) :
    bulkRegionEventuallyNonvanishing
      canonicalCutoffFamily deltaStarLowerModel defaultEps defaultT0 := by
  exact bulkRegionEventuallyNonvanishing_of_route3BulkCertificate hRoute3

/-!
Route 3 bulk interface.

Primary source:
- docs/c2_bulk_offaxis_route3_tilt.md

The notes state explicitly that Route 3 does not prove a purely C2 lower bound by itself:
the lower bound for `FInfinity` uses the identity `FInfinity = c0 * zeta` together with
classical zeta input such as Vinogradov-Korobov/Ford, Phragmen-Lindelof, the functional
equation, and the nonvanishing/lower bound for `c0`.  This module formalizes the Lean
kernel part of the argument that follows from those inputs: once the limit lower bound
and the cutoff error domination are available, nonvanishing of the canonical cutoff
family on the bulk region is a theorem, not an opaque final axiom.
-/

end LeanC2
