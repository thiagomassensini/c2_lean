import Mathlib
import LeanC2.Bulk.FXNonZeroBulk
import LeanC2.Cutoff.DominantQuartet
import LeanC2.NearAxis.GlobalBound

set_option linter.style.whitespace false

namespace LeanC2

/--
Bulk margin left by the dominant quartet after subtracting the finite shell tail.

This is the same coefficient already proved in `Cutoff.DominantQuartet`, exposed as a named
bulk quantity for the direct `F_X` route.
-/
noncomputable def dominantQuartetBulkMarginCoeff (s : Complex) : ℝ :=
  ((1 - ‖shellRatio s‖) * (1 + ‖shellRatio s‖ ^ 2)) -
    (‖shellRatio s‖ ^ 4 / (1 - ‖shellRatio s‖))

/--
The dominant quartet plus finite shell tail gives a direct lower bound for the sharp cutoff
family, with no limiting function.
-/
theorem norm_sharpCutoffFamily_ge_bulkMargin
    {X : Nat} (hX : 3 ≤ X) (s : Complex) (hs : -1 < s.re) :
    dominantQuartetBulkMarginCoeff s * ‖cutoffFirstShell X s‖ ≤
      ‖sharpCutoffFamily X s‖ := by
  have hmargin := cutoffDominantQuartet_sub_tail_margin_lower_bound X s hs
  have htriangle :
      ‖cutoffDominantQuartet X s‖ - ‖cutoffDominantTail X s‖ ≤
        ‖cutoffDominantQuartet X s + cutoffDominantTail X s‖ := by
    simpa [sub_eq_add_neg, norm_neg] using
      (norm_sub_norm_le (cutoffDominantQuartet X s) (-cutoffDominantTail X s))
  calc
    dominantQuartetBulkMarginCoeff s * ‖cutoffFirstShell X s‖
        ≤ ‖cutoffDominantQuartet X s‖ - ‖cutoffDominantTail X s‖ := by
          simpa [dominantQuartetBulkMarginCoeff] using hmargin
    _ ≤ ‖cutoffDominantQuartet X s + cutoffDominantTail X s‖ := htriangle
    _ = ‖sharpCutoffFamily X s‖ := by
          rw [← sharpCutoffFamily_eq_cutoffDominantQuartet_add_tail (X := X) s hX]

/--
Direct lower bound for the full canonical cutoff family after paying the canonical residual.
-/
theorem norm_canonicalCutoffFamily_ge_bulkMargin_sub_residual
    {X : Nat} (hX : 3 ≤ X) (s : Complex) (hs : -1 < s.re) :
    dominantQuartetBulkMarginCoeff s * ‖cutoffFirstShell X s‖ -
        ‖canonicalCutoffResidual X s‖ ≤
      ‖canonicalCutoffFamily X s‖ := by
  have hsharp := norm_sharpCutoffFamily_ge_bulkMargin hX s hs
  have htriangle :
      ‖sharpCutoffFamily X s‖ - ‖canonicalCutoffResidual X s‖ ≤
        ‖sharpCutoffFamily X s + canonicalCutoffResidual X s‖ := by
    simpa [sub_eq_add_neg, norm_neg] using
      (norm_sub_norm_le (sharpCutoffFamily X s) (-canonicalCutoffResidual X s))
  calc
    dominantQuartetBulkMarginCoeff s * ‖cutoffFirstShell X s‖ -
        ‖canonicalCutoffResidual X s‖
        ≤ ‖sharpCutoffFamily X s‖ - ‖canonicalCutoffResidual X s‖ := by
          linarith
    _ ≤ ‖sharpCutoffFamily X s + canonicalCutoffResidual X s‖ := htriangle
    _ = ‖canonicalCutoffFamily X s‖ := by
          rw [canonicalCutoffFamily_eq_sharpCutoffFamily_add_residual]

/--
Pointwise direct `F_X` nonvanishing from residual domination by the quartet margin.
-/
theorem canonicalCutoffFamily_nonzero_of_bulk_direct_dominance
    {X : Nat} (hX : 3 ≤ X) (s : Complex) (hs : -1 < s.re)
    (hResidual :
      ‖canonicalCutoffResidual X s‖ <
        dominantQuartetBulkMarginCoeff s * ‖cutoffFirstShell X s‖) :
    canonicalCutoffFamily X s ≠ 0 := by
  apply norm_pos_iff.mp
  have hlow := norm_canonicalCutoffFamily_ge_bulkMargin_sub_residual hX s hs
  have hpos :
      0 < dominantQuartetBulkMarginCoeff s * ‖cutoffFirstShell X s‖ -
        ‖canonicalCutoffResidual X s‖ := by
    linarith
  exact lt_of_lt_of_le hpos hlow

/--
Bulk certificate for the direct `F_X` route.

It asks only for eventual domination of the canonical residual by the explicit quartet margin
times the first shell. Unlike Route 3, this interface does not mention `FInfinity`, zeta, or a
Hurwitz transfer.
-/
def canonicalDirectDominanceOnBulk
    (deltaStar : ℝ -> ℝ) (eps T0 : ℝ) : Prop :=
  ∃ X0 : Nat,
    ∀ X : Nat, X0 ≤ X -> ∀ s : Complex,
      bulkRegion deltaStar eps T0 s ->
        ‖canonicalCutoffResidual X s‖ <
          dominantQuartetBulkMarginCoeff s * ‖cutoffFirstShell X s‖

/--
Right-hand side of the bulk region.

The direct quartet/residual route is tracked separately here because the numerical scout shows
its obstruction on the left side of the bulk. Route 3 remains the global bulk route.
-/
def rightBulkRegion (deltaStar : ℝ -> ℝ) (eps T0 : ℝ) (s : Complex) : Prop :=
  bulkRegion deltaStar eps T0 s ∧ (1 : ℝ) / 2 < s.re

def rightBulkRegionEventuallyNonvanishing
    (FX : Nat -> Complex -> Complex) (deltaStar : ℝ -> ℝ) (eps T0 : ℝ) : Prop :=
  ∃ X0 : Nat,
    ∀ X : Nat, X0 ≤ X -> ∀ s : Complex, rightBulkRegion deltaStar eps T0 s -> FX X s ≠ 0

theorem rightBulkRegion_mem_bulkRegion
    {deltaStar : ℝ -> ℝ} {eps T0 : ℝ} {s : Complex}
    (hs : rightBulkRegion deltaStar eps T0 s) :
    bulkRegion deltaStar eps T0 s :=
  hs.1

/--
Right-bulk certificate for the direct `F_X` route.

This is a restricted version of `canonicalDirectDominanceOnBulk`; it is useful as an auxiliary
certificate and diagnostic target, not as a replacement for the Route 3 global bulk certificate.
-/
def canonicalDirectDominanceOnRightBulk
    (deltaStar : ℝ -> ℝ) (eps T0 : ℝ) : Prop :=
  ∃ X0 : Nat,
    ∀ X : Nat, X0 ≤ X -> ∀ s : Complex,
      rightBulkRegion deltaStar eps T0 s ->
        ‖canonicalCutoffResidual X s‖ <
          dominantQuartetBulkMarginCoeff s * ‖cutoffFirstShell X s‖

/--
Coefficient-level direct dominance on the bulk.

This is the form closest to the cutoff notes: Lean already proves
`‖canonicalCutoffResidual X s‖ <= canonicalCutoffResidualCoeff s X / cutoffScale X`,
so a producer only has to certify that this explicit coefficient bound is smaller than
the quartet margin.
-/
def canonicalDirectCoefficientDominanceOnBulk
    (deltaStar : ℝ -> ℝ) (eps T0 : ℝ) : Prop :=
  ∃ X0 : Nat,
    ∀ X : Nat, X0 ≤ X -> ∀ s : Complex,
      bulkRegion deltaStar eps T0 s ->
        canonicalCutoffResidualCoeff s X / cutoffScale X <
          dominantQuartetBulkMarginCoeff s * ‖cutoffFirstShell X s‖

/--
The coefficient-level cutoff bound supplies the direct residual domination needed on the bulk.
-/
theorem canonicalDirectDominanceOnBulk_of_coefficientDominance
    {deltaStar : ℝ -> ℝ} {eps T0 : ℝ}
    (hCoeff : canonicalDirectCoefficientDominanceOnBulk deltaStar eps T0) :
    canonicalDirectDominanceOnBulk deltaStar eps T0 := by
  rcases hCoeff with ⟨X0, hX0⟩
  refine ⟨X0, ?_⟩
  intro X hX s hs
  exact lt_of_le_of_lt (norm_canonicalCutoffResidual_le X s) (hX0 X hX s hs)

/--
Scaled lower-bound package for the direct bulk route.

The notes usually produce residual control as `C/X` and a separate lower scale for the
dominant term.  This structure records that pattern without mentioning `FInfinity`:
eventually the scale is below the quartet margin, and the canonical residual is below
a strict fraction of that scale.
-/
structure DirectFXBulkDominanceData
    (deltaStar : ℝ -> ℝ) (eps T0 : ℝ) where
  scale : Nat -> Complex -> ℝ
  kappa : ℝ
  hkappa : kappa < 1
  hScalePos :
    ∀ X : Nat, ∀ s : Complex,
      bulkRegion deltaStar eps T0 s -> 0 < scale X s
  hMarginLower :
    ∃ X0 : Nat,
      ∀ X : Nat, X0 ≤ X -> ∀ s : Complex,
        bulkRegion deltaStar eps T0 s ->
          scale X s ≤ dominantQuartetBulkMarginCoeff s * ‖cutoffFirstShell X s‖
  hResidualUpper :
    ∃ X0 : Nat,
      ∀ X : Nat, X0 ≤ X -> ∀ s : Complex,
        bulkRegion deltaStar eps T0 s ->
          ‖canonicalCutoffResidual X s‖ ≤ kappa * scale X s

/--
The scaled dominance package implies the direct bulk certificate.
-/
theorem canonicalDirectDominanceOnBulk_of_dominanceData
    {deltaStar : ℝ -> ℝ} {eps T0 : ℝ}
    (hData : DirectFXBulkDominanceData deltaStar eps T0) :
    canonicalDirectDominanceOnBulk deltaStar eps T0 := by
  rcases hData.hMarginLower with ⟨XMargin, hMargin⟩
  rcases hData.hResidualUpper with ⟨XResidual, hResidual⟩
  refine ⟨max XMargin XResidual, ?_⟩
  intro X hX s hs
  have hMarginX :
      hData.scale X s ≤ dominantQuartetBulkMarginCoeff s * ‖cutoffFirstShell X s‖ :=
    hMargin X (le_trans (le_max_left _ _) hX) s hs
  have hResidualX :
      ‖canonicalCutoffResidual X s‖ ≤ hData.kappa * hData.scale X s :=
    hResidual X (le_trans (le_max_right _ _) hX) s hs
  have hScalePos : 0 < hData.scale X s := hData.hScalePos X s hs
  have hKappaScale :
      hData.kappa * hData.scale X s < hData.scale X s := by
    nlinarith [hData.hkappa, hScalePos]
  exact lt_of_le_of_lt hResidualX (lt_of_lt_of_le hKappaScale hMarginX)

/--
The direct dominance certificate closes bulk eventual nonvanishing for the canonical cutoff
family.
-/
theorem canonicalCutoffFamily_bulkRegionEventuallyNonvanishing_of_directDominance
    {deltaStar : ℝ -> ℝ} {eps T0 : ℝ}
    (hDominance : canonicalDirectDominanceOnBulk deltaStar eps T0) :
    bulkRegionEventuallyNonvanishing canonicalCutoffFamily deltaStar eps T0 := by
  rcases hDominance with ⟨XDom, hDom⟩
  refine ⟨max 3 XDom, ?_⟩
  intro X hX s hs
  have hX3 : 3 ≤ X := le_trans (le_max_left 3 XDom) hX
  have hXDom : XDom ≤ X := le_trans (le_max_right 3 XDom) hX
  have hsHigh : highOffCriticalStrip T0 s :=
    bulkRegion_mem_highOffCriticalStrip (deltaStar := deltaStar) (eps := eps) hs
  have hsOff : offCriticalStrip s := hsHigh.1
  have hsRe : -1 < s.re := by
    linarith [hsOff.1]
  exact canonicalCutoffFamily_nonzero_of_bulk_direct_dominance
    hX3 s hsRe (hDom X hXDom s hs)

/--
The restricted direct dominance certificate closes nonvanishing on the right side of the bulk.
-/
theorem canonicalCutoffFamily_rightBulkRegionEventuallyNonvanishing_of_directDominance
    {deltaStar : ℝ -> ℝ} {eps T0 : ℝ}
    (hDominance : canonicalDirectDominanceOnRightBulk deltaStar eps T0) :
    rightBulkRegionEventuallyNonvanishing canonicalCutoffFamily deltaStar eps T0 := by
  rcases hDominance with ⟨XDom, hDom⟩
  refine ⟨max 3 XDom, ?_⟩
  intro X hX s hs
  have hX3 : 3 ≤ X := le_trans (le_max_left 3 XDom) hX
  have hXDom : XDom ≤ X := le_trans (le_max_right 3 XDom) hX
  have hsBulk : bulkRegion deltaStar eps T0 s := rightBulkRegion_mem_bulkRegion hs
  have hsHigh : highOffCriticalStrip T0 s :=
    bulkRegion_mem_highOffCriticalStrip (deltaStar := deltaStar) (eps := eps) hsBulk
  have hsOff : offCriticalStrip s := hsHigh.1
  have hsRe : -1 < s.re := by
    linarith [hsOff.1]
  exact canonicalCutoffFamily_nonzero_of_bulk_direct_dominance
    hX3 s hsRe (hDom X hXDom s hs)

/-- Canonical direct bulk certificate at the repository default constants. -/
abbrev DirectFXCanonicalBulkCertificate : Prop :=
  canonicalDirectDominanceOnBulk deltaStarLowerModel defaultEps defaultT0

/-- Canonical direct right-bulk certificate at the repository default constants. -/
abbrev DirectFXCanonicalRightBulkCertificate : Prop :=
  canonicalDirectDominanceOnRightBulk deltaStarLowerModel defaultEps defaultT0

/-- Canonical coefficient-level direct bulk certificate at the repository default constants. -/
abbrev DirectFXCanonicalCoefficientBulkCertificate : Prop :=
  canonicalDirectCoefficientDominanceOnBulk deltaStarLowerModel defaultEps defaultT0

/-- Canonical scaled dominance data for the direct bulk route at the default constants. -/
abbrev DirectFXCanonicalBulkDominanceData : Type :=
  DirectFXBulkDominanceData deltaStarLowerModel defaultEps defaultT0

/-- Coefficient-level canonical data produces the direct bulk certificate. -/
theorem directFXCanonicalBulkCertificate_of_coefficientCertificate
    (hCoeff : DirectFXCanonicalCoefficientBulkCertificate) :
    DirectFXCanonicalBulkCertificate := by
  exact canonicalDirectDominanceOnBulk_of_coefficientDominance hCoeff

/-- Scaled canonical dominance data produces the direct bulk certificate. -/
theorem directFXCanonicalBulkCertificate_of_dominanceData
    (hData : DirectFXCanonicalBulkDominanceData) :
    DirectFXCanonicalBulkCertificate := by
  exact canonicalDirectDominanceOnBulk_of_dominanceData hData

/-- Canonical default bulk leg obtained from the direct `F_X` certificate. -/
theorem canonicalBulkGlobalBoundCertificate_of_directFX
    (hDirect : DirectFXCanonicalBulkCertificate) :
    bulkRegionEventuallyNonvanishing
      canonicalCutoffFamily deltaStarLowerModel defaultEps defaultT0 := by
  exact canonicalCutoffFamily_bulkRegionEventuallyNonvanishing_of_directDominance hDirect

/-- Canonical default bulk leg obtained from a coefficient-level direct certificate. -/
theorem canonicalBulkGlobalBoundCertificate_of_directFXCoefficient
    (hCoeff : DirectFXCanonicalCoefficientBulkCertificate) :
    bulkRegionEventuallyNonvanishing
      canonicalCutoffFamily deltaStarLowerModel defaultEps defaultT0 := by
  exact canonicalBulkGlobalBoundCertificate_of_directFX
    (directFXCanonicalBulkCertificate_of_coefficientCertificate hCoeff)

/-- Canonical default bulk leg obtained from scaled direct dominance data. -/
theorem canonicalBulkGlobalBoundCertificate_of_directFXDominanceData
    (hData : DirectFXCanonicalBulkDominanceData) :
    bulkRegionEventuallyNonvanishing
      canonicalCutoffFamily deltaStarLowerModel defaultEps defaultT0 := by
  exact canonicalBulkGlobalBoundCertificate_of_directFX
    (directFXCanonicalBulkCertificate_of_dominanceData hData)

/-- Canonical default right-bulk leg obtained from the restricted direct `F_X` certificate. -/
theorem canonicalRightBulkGlobalBoundCertificate_of_directFX
    (hDirect : DirectFXCanonicalRightBulkCertificate) :
    rightBulkRegionEventuallyNonvanishing
      canonicalCutoffFamily deltaStarLowerModel defaultEps defaultT0 := by
  exact canonicalCutoffFamily_rightBulkRegionEventuallyNonvanishing_of_directDominance hDirect

/-!
Direct bulk interface for `F_X`.

This module formalizes the part of the direct route that is already available in Lean:
the dominant quartet controls the sharp cutoff, and the full cutoff is nonzero once the
canonical residual is dominated by that explicit margin. The remaining analytic/numeric
input for this route is exactly `DirectFXCanonicalBulkCertificate`, or one of the more
structured producer-facing packages:

- `DirectFXCanonicalCoefficientBulkCertificate`;
- `DirectFXCanonicalBulkDominanceData`.
- `DirectFXCanonicalRightBulkCertificate`.

Primary note references:
- docs/c2_quarteto_dominante_cutoff.md
- docs/c2_prova_taxa_decaimento_cutoff.md
- docs/c2_cutoff_adaptativo_quarteto.md
-/

end LeanC2
