import Mathlib
import LeanC2.Finite.DyadicCoverage
import LeanC2.Glue.GlueTheorem
import LeanC2.Numerical.Constants

namespace LeanC2

structure DefaultFiniteAndGlueData
    (FX : Nat -> Complex -> Complex) (deltaStar : ℝ -> ℝ) : Prop where
  hFinite : cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip FX defaultCertifiedHeight
  hDelta : ∀ t : ℝ, 0 ≤ deltaStar t
  hNear : nearRegionEventuallyNonvanishing FX deltaStar defaultT0
  hBulk : bulkRegionEventuallyNonvanishing FX deltaStar defaultEps defaultT0
  hEdge : edgeRegionEventuallyNonvanishing FX defaultEps defaultT0

theorem cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_finite_and_high
    {FX : Nat -> Complex -> Complex} {H : ℝ}
    (hFinite : cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip FX H)
    (hHigh : cutoffFamilyEventuallyNonvanishingOnHighOffCriticalStrip FX H) :
    cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX := by
  rcases hFinite with ⟨XFinite, hFiniteX⟩
  rcases hHigh with ⟨XHigh, hHighX⟩
  let X0 := max XFinite XHigh
  refine ⟨X0, ?_⟩
  intro X hX s hs
  by_cases hHeight : stripHeight s ≤ H
  · exact hFiniteX X (le_trans (le_max_left _ _) hX) s ⟨hs, hHeight⟩
  · have hHighHeight : H ≤ stripHeight s := le_of_not_ge hHeight
    exact hHighX X (le_trans (le_max_right _ _) hX) s ⟨hs, hHighHeight⟩

theorem cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_finite_and_high_of_le
    {FX : Nat -> Complex -> Complex} {T0 H : ℝ}
    (hT : T0 ≤ H)
    (hFinite : cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip FX H)
    (hHigh : cutoffFamilyEventuallyNonvanishingOnHighOffCriticalStrip FX T0) :
    cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX := by
  rcases hFinite with ⟨XFinite, hFiniteX⟩
  rcases hHigh with ⟨XHigh, hHighX⟩
  let X0 := max XFinite XHigh
  refine ⟨X0, ?_⟩
  intro X hX s hs
  by_cases hHeight : stripHeight s ≤ H
  · exact hFiniteX X (le_trans (le_max_left _ _) hX) s ⟨hs, hHeight⟩
  · have hHighHeight : T0 ≤ stripHeight s := by
      have hHeightLt : H < stripHeight s := lt_of_not_ge hHeight
      linarith
    exact hHighX X (le_trans (le_max_right _ _) hX) s ⟨hs, hHighHeight⟩

theorem cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_default_finite_and_high
    {FX : Nat -> Complex -> Complex}
    (hFinite : cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip FX defaultCertifiedHeight)
    (hHigh : cutoffFamilyEventuallyNonvanishingOnHighOffCriticalStrip FX defaultT0) :
    cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX := by
  exact cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_finite_and_high_of_le
    defaultT0_le_defaultCertifiedHeight hFinite hHigh

theorem cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_defaultData
    {FX : Nat -> Complex -> Complex} {deltaStar : ℝ -> ℝ}
    (hData : DefaultFiniteAndGlueData FX deltaStar) :
    cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX := by
  apply cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_default_finite_and_high
  · exact hData.hFinite
  · exact glueTheorem_highOffCriticalStrip_default
      hData.hDelta hData.hNear hData.hBulk hData.hEdge

/-!
Reserved module for importing external numerical certificates as explicit assumptions.

Primary sources:
- docs/teorema_faixa_diadica_zero_free.md

At the current abstraction level, this file combines the finite-height certificate with the glued
high-height theorem to obtain eventual nonvanishing on the full off-critical strip.
-/

end LeanC2
