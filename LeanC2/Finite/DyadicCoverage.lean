import Mathlib
import LeanC2.Glue.Decomposition

namespace LeanC2

def finiteHeightOffCriticalStrip (H : ℝ) (s : Complex) : Prop :=
  offCriticalStrip s ∧ stripHeight s ≤ H

def finiteHeightOffCriticalStripNonvanishing (H : ℝ) (f : Complex -> Complex) : Prop :=
  ∀ s : Complex, finiteHeightOffCriticalStrip H s → f s ≠ 0

def cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip
    (FX : Nat -> Complex -> Complex) (H : ℝ) : Prop :=
  ∃ X0 : Nat, ∀ X : Nat, X0 ≤ X -> finiteHeightOffCriticalStripNonvanishing H (FX X)

theorem finiteHeightOffCriticalStrip_mono {H0 H1 : ℝ} (hH : H0 ≤ H1) {s : Complex}
    (hs : finiteHeightOffCriticalStrip H0 s) : finiteHeightOffCriticalStrip H1 s :=
  ⟨hs.1, le_trans hs.2 hH⟩

theorem finiteHeightOffCriticalStripNonvanishing_mono {H0 H1 : ℝ} {f : Complex -> Complex}
    (hH : H0 ≤ H1) (hf : finiteHeightOffCriticalStripNonvanishing H1 f) :
    finiteHeightOffCriticalStripNonvanishing H0 f := by
  intro s hs
  exact hf s (finiteHeightOffCriticalStrip_mono hH hs)

theorem cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip_mono
    {FX : Nat -> Complex -> Complex} {H0 H1 : ℝ}
    (hH : H0 ≤ H1)
    (hFX : cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip FX H1) :
    cutoffFamilyEventuallyNonvanishingOnFiniteHeightStrip FX H0 := by
  rcases hFX with ⟨X0, hX0⟩
  refine ⟨X0, ?_⟩
  intro X hX
  exact finiteHeightOffCriticalStripNonvanishing_mono hH (hX0 X hX)

/-!
Scaffold for the finite dyadic coverage statement up to the certified height.

Primary sources:
- docs/teorema_faixa_diadica_zero_free.md

This file records the low-height portion of the cutoff-family nonvanishing argument as an explicit
eventual interface in the cutoff parameter `X`.
-/

end LeanC2
