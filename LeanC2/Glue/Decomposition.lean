import Mathlib
import LeanC2.Numerical.Constants

namespace LeanC2

noncomputable section

def offCriticalStrip (s : Complex) : Prop :=
  0 < s.re ∧ s.re < 1 ∧ s.re ≠ (1 : ℝ) / 2

def offCriticalStripSet : Set Complex := {s : Complex | offCriticalStrip s}

def offCriticalStripNonvanishing (f : Complex -> Complex) : Prop :=
  ∀ s : Complex, offCriticalStrip s → f s ≠ 0

def cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip
    (FX : Nat -> Complex -> Complex) : Prop :=
  ∃ X0 : Nat, ∀ X : Nat, X0 ≤ X -> offCriticalStripNonvanishing (FX X)

/-- Absolute height of a point in the strip. -/
def stripHeight (s : Complex) : ℝ :=
  |s.im|

def highOffCriticalStrip (T0 : ℝ) (s : Complex) : Prop :=
  offCriticalStrip s ∧ T0 ≤ stripHeight s

def highOffCriticalStripNonvanishing (T0 : ℝ) (f : Complex -> Complex) : Prop :=
  ∀ s : Complex, highOffCriticalStrip T0 s → f s ≠ 0

def cutoffFamilyEventuallyNonvanishingOnHighOffCriticalStrip
    (FX : Nat -> Complex -> Complex) (T0 : ℝ) : Prop :=
  ∃ X0 : Nat, ∀ X : Nat, X0 ≤ X -> highOffCriticalStripNonvanishing T0 (FX X)

/-- Horizontal displacement from the critical line. -/
def criticalOffset (s : Complex) : ℝ :=
  s.re - (1 : ℝ) / 2

def nearRegion (deltaStar : ℝ -> ℝ) (T0 : ℝ) (s : Complex) : Prop :=
  highOffCriticalStrip T0 s ∧
    |criticalOffset s| ≤ (11 : ℝ) / 10 * deltaStar (stripHeight s)

def bulkRegion (deltaStar : ℝ -> ℝ) (eps T0 : ℝ) (s : Complex) : Prop :=
  highOffCriticalStrip T0 s ∧
    (9 : ℝ) / 10 * deltaStar (stripHeight s) ≤ |criticalOffset s| ∧
    |criticalOffset s| ≤ (1 : ℝ) / 2 - (9 : ℝ) / 10 * eps

def edgeRegion (eps T0 : ℝ) (s : Complex) : Prop :=
  highOffCriticalStrip T0 s ∧
    (s.re ≤ (11 : ℝ) / 10 * eps ∨ 1 - (11 : ℝ) / 10 * eps ≤ s.re)

def glueCovering (deltaStar : ℝ -> ℝ) (eps T0 : ℝ) : Prop :=
  ∀ s : Complex, highOffCriticalStrip T0 s →
    nearRegion deltaStar T0 s ∨ bulkRegion deltaStar eps T0 s ∨ edgeRegion eps T0 s

theorem nearRegion_mem_highOffCriticalStrip {deltaStar : ℝ -> ℝ} {T0 : ℝ} {s : Complex}
    (hs : nearRegion deltaStar T0 s) : highOffCriticalStrip T0 s :=
  hs.1

theorem nearRegion_mono {deltaStar₀ deltaStar₁ : ℝ -> ℝ} {T0 : ℝ} {s : Complex}
    (hDelta : ∀ t : ℝ, deltaStar₀ t ≤ deltaStar₁ t)
    (hs : nearRegion deltaStar₀ T0 s) :
    nearRegion deltaStar₁ T0 s := by
  refine ⟨hs.1, ?_⟩
  have hScale :
      (11 : ℝ) / 10 * deltaStar₀ (stripHeight s) ≤
        (11 : ℝ) / 10 * deltaStar₁ (stripHeight s) := by
    exact mul_le_mul_of_nonneg_left (hDelta (stripHeight s)) (by norm_num : 0 ≤ (11 : ℝ) / 10)
  exact le_trans hs.2 hScale

theorem bulkRegion_mem_highOffCriticalStrip {deltaStar : ℝ -> ℝ} {eps T0 : ℝ} {s : Complex}
    (hs : bulkRegion deltaStar eps T0 s) : highOffCriticalStrip T0 s :=
  hs.1

theorem edgeRegion_mem_highOffCriticalStrip {eps T0 : ℝ} {s : Complex}
    (hs : edgeRegion eps T0 s) : highOffCriticalStrip T0 s :=
  hs.1

theorem highOffCriticalStrip_mono {T0 T1 : ℝ} (hT : T0 ≤ T1) {s : Complex}
    (hs : highOffCriticalStrip T1 s) : highOffCriticalStrip T0 s :=
  ⟨hs.1, le_trans hT hs.2⟩

theorem highOffCriticalStripNonvanishing_mono {T0 T1 : ℝ} {f : Complex -> Complex}
    (hT : T0 ≤ T1) (hf : highOffCriticalStripNonvanishing T0 f) :
    highOffCriticalStripNonvanishing T1 f := by
  intro s hs
  exact hf s (highOffCriticalStrip_mono hT hs)

theorem cutoffFamilyEventuallyNonvanishingOnHighOffCriticalStrip_mono
    {FX : Nat -> Complex -> Complex} {T0 T1 : ℝ}
    (hT : T0 ≤ T1)
    (hFX : cutoffFamilyEventuallyNonvanishingOnHighOffCriticalStrip FX T0) :
    cutoffFamilyEventuallyNonvanishingOnHighOffCriticalStrip FX T1 := by
  rcases hFX with ⟨X0, hX0⟩
  refine ⟨X0, ?_⟩
  intro X hX
  exact highOffCriticalStripNonvanishing_mono hT (hX0 X hX)

theorem glueCovering_of_nonneg
    {deltaStar : ℝ -> ℝ} {eps T0 : ℝ}
    (hDelta : ∀ t : ℝ, 0 ≤ deltaStar t)
    (hEps : 0 ≤ eps) :
    glueCovering deltaStar eps T0 := by
  intro s hs
  by_cases hEdge : s.re ≤ (11 : ℝ) / 10 * eps ∨ 1 - (11 : ℝ) / 10 * eps ≤ s.re
  · exact Or.inr (Or.inr ⟨hs, hEdge⟩)
  · by_cases hNear : |criticalOffset s| ≤ (11 : ℝ) / 10 * deltaStar (stripHeight s)
    · exact Or.inl ⟨hs, hNear⟩
    · have hsLeft : (11 : ℝ) / 10 * eps < s.re := by
        have hsNotLeft : ¬ s.re ≤ (11 : ℝ) / 10 * eps := by
          intro hsLeftLe
          exact hEdge (Or.inl hsLeftLe)
        exact lt_of_not_ge hsNotLeft
      have hsRight : s.re < 1 - (11 : ℝ) / 10 * eps := by
        have hsNotRight : ¬ 1 - (11 : ℝ) / 10 * eps ≤ s.re := by
          intro hsRightLe
          exact hEdge (Or.inr hsRightLe)
        exact lt_of_not_ge hsNotRight
      have hLower : (9 : ℝ) / 10 * deltaStar (stripHeight s) ≤ |criticalOffset s| := by
        have hNearLt : (11 : ℝ) / 10 * deltaStar (stripHeight s) < |criticalOffset s| :=
          lt_of_not_ge hNear
        have hScale :
            (9 : ℝ) / 10 * deltaStar (stripHeight s) ≤
              (11 : ℝ) / 10 * deltaStar (stripHeight s) := by
          have hNonneg : 0 ≤ deltaStar (stripHeight s) := hDelta (stripHeight s)
          linarith
        exact le_trans hScale hNearLt.le
      have hUpperAux : |s.re - (1 : ℝ) / 2| ≤ (1 : ℝ) / 2 - (11 : ℝ) / 10 * eps := by
        rw [abs_le]
        constructor
        · linarith
        · linarith
      have hUpper : |criticalOffset s| ≤ (1 : ℝ) / 2 - (9 : ℝ) / 10 * eps := by
        have hWindow : (1 : ℝ) / 2 - (11 : ℝ) / 10 * eps ≤ (1 : ℝ) / 2 - (9 : ℝ) / 10 * eps := by
          linarith
        have hUpper' : |criticalOffset s| ≤ (1 : ℝ) / 2 - (11 : ℝ) / 10 * eps := by
          simpa [criticalOffset] using hUpperAux
        exact le_trans hUpper' hWindow
      exact Or.inr (Or.inl ⟨hs, hLower, hUpper⟩)

theorem defaultGlueCovering {deltaStar : ℝ -> ℝ}
    (hDelta : ∀ t : ℝ, 0 ≤ deltaStar t) :
    glueCovering deltaStar defaultEps defaultT0 := by
  exact glueCovering_of_nonneg hDelta defaultEps_nonneg

/-!
Scaffold for the decomposition of the admissible region into near, bulk, and edge.

Primary sources:
- docs/c2_bulk_offaxis_glue.md

This file now holds the common off-critical-strip domain, height cutoffs, and the abstract region
predicates used both by the gluing layer and by the Hurwitz transfer layer.
-/

end

end LeanC2
