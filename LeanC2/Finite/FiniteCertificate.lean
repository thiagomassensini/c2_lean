import Mathlib
import LeanC2.Finite.DyadicCoverage
import LeanC2.Glue.GlueTheorem
import LeanC2.NearAxis.GlobalBound
import LeanC2.Numerical.Constants

namespace LeanC2

structure DefaultFiniteAndGlueData
    (FX : Nat -> Complex -> Complex) (deltaStar : ℝ -> ℝ) : Prop where
  hFinite : cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip FX defaultCertifiedHeight
  hDelta : ∀ t : ℝ, 0 ≤ deltaStar t
  hNear : nearRegionEventuallyNonvanishing FX deltaStar defaultT0
  hBulk : bulkRegionEventuallyNonvanishing FX deltaStar defaultEps defaultT0
  hEdge : edgeRegionEventuallyNonvanishing FX defaultEps defaultT0

/--
Default finite-plus-glue data where the near-axis leg is supplied through Taylor witnesses.
-/
structure DefaultFiniteAndGlueTaylorData
    (FX : Nat -> Complex -> Complex) (deltaStar : ℝ -> ℝ) : Prop where
  hFinite : cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip FX defaultCertifiedHeight
  hDelta : ∀ t : ℝ, 0 ≤ deltaStar t
  hTaylor :
    ∃ X0 : Nat,
      ∀ X : Nat, X0 ≤ X -> ∀ s : Complex,
        nearRegion deltaStar defaultT0 s ->
          taylorNonvanishingWitness (FX X s) |criticalOffset s|
  hBulk : bulkRegionEventuallyNonvanishing FX deltaStar defaultEps defaultT0
  hEdge : edgeRegionEventuallyNonvanishing FX defaultEps defaultT0

/--
Default global-bound package where the near-axis input is supplied through eventual Taylor witnesses
rather than directly as a regional nonvanishing hypothesis.
-/
structure DefaultGlobalBoundTaylorData (FX : Nat -> Complex -> Complex) : Prop where
  hFinite : cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip FX defaultCertifiedHeight
  hTaylor :
    ∃ X0 : Nat,
      ∀ X : Nat, X0 ≤ X -> ∀ s : Complex,
        nearRegion deltaStarLowerModel defaultT0 s ->
          taylorNonvanishingWitness (FX X s) |criticalOffset s|
  hBulk : bulkRegionEventuallyNonvanishing FX deltaStarLowerModel defaultEps defaultT0
  hEdge : edgeRegionEventuallyNonvanishing FX defaultEps defaultT0

/-- Any global-bound Taylor package upgrades to the canonical default global-bound data package. -/
theorem defaultFiniteAndGlueData_of_taylorData
    {FX : Nat -> Complex -> Complex} {deltaStar : ℝ -> ℝ}
    (hData : DefaultFiniteAndGlueTaylorData FX deltaStar) :
    DefaultFiniteAndGlueData FX deltaStar := by
  refine ⟨hData.hFinite, hData.hDelta, ?_, hData.hBulk, hData.hEdge⟩
  exact nearRegionEventuallyNonvanishing_of_taylorWitness hData.hTaylor

abbrev DefaultGlobalBoundData (FX : Nat -> Complex -> Complex) : Prop :=
  DefaultFiniteAndGlueData FX deltaStarLowerModel

/-- Any global-bound Taylor package upgrades to the canonical default global-bound data package. -/
theorem defaultGlobalBoundData_of_taylorData
    {FX : Nat -> Complex -> Complex}
    (hData : DefaultGlobalBoundTaylorData FX) :
    DefaultGlobalBoundData FX := by
  refine ⟨hData.hFinite, deltaStarLowerModel_nonneg, ?_, hData.hBulk, hData.hEdge⟩
  exact nearRegionEventuallyNonvanishing_of_taylorWitness hData.hTaylor

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

theorem cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_defaultTaylorData
    {FX : Nat -> Complex -> Complex} {deltaStar : ℝ -> ℝ}
    (hData : DefaultFiniteAndGlueTaylorData FX deltaStar) :
    cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX := by
  exact cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_defaultData
    (defaultFiniteAndGlueData_of_taylorData hData)

theorem cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_defaultGlobalBoundData
    {FX : Nat -> Complex -> Complex}
    (hData : DefaultGlobalBoundData FX) :
    cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX := by
  exact cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_defaultData hData

theorem cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_defaultGlobalBoundTaylorData
    {FX : Nat -> Complex -> Complex}
    (hData : DefaultGlobalBoundTaylorData FX) :
    cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip FX := by
  exact cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_defaultGlobalBoundData
    (defaultGlobalBoundData_of_taylorData hData)

/-!
Reserved module for importing external numerical certificates as explicit assumptions.

Primary sources:
- docs/teorema_faixa_diadica_zero_free.md

At the current abstraction level, this file combines the finite-height certificate with the glued
high-height theorem to obtain eventual nonvanishing on the full off-critical strip.
-/

end LeanC2
