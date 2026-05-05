import Mathlib
import LeanC2.Cutoff.DominantQuartet
import LeanC2.Glue.Decomposition
import LeanC2.Numerical.Constants

set_option linter.style.whitespace false

namespace LeanC2

def criticalLine (s : Complex) : Prop :=
  s.re = (1 : ℝ) / 2

def criticalLineNonvanishing (f : Complex -> Complex) : Prop :=
  ∀ s : Complex, criticalLine s -> f s ≠ 0

def highCriticalLine (T0 : ℝ) (s : Complex) : Prop :=
  criticalLine s ∧ T0 ≤ stripHeight s

def highCriticalLineNonvanishing (T0 : ℝ) (f : Complex -> Complex) : Prop :=
  ∀ s : Complex, highCriticalLine T0 s -> f s ≠ 0

def cutoffFamilyEventuallyNonvanishingOnHighCriticalLine
    (FX : Nat -> Complex -> Complex) (T0 : ℝ) : Prop :=
  ∃ X0 : Nat, ∀ X : Nat, X0 ≤ X -> highCriticalLineNonvanishing T0 (FX X)

def finiteHeightCriticalLine (H : ℝ) (s : Complex) : Prop :=
  criticalLine s ∧ stripHeight s ≤ H

def finiteHeightCriticalLineNonvanishing (H : ℝ) (f : Complex -> Complex) : Prop :=
  ∀ s : Complex, finiteHeightCriticalLine H s -> f s ≠ 0

def cutoffFamilyEventuallyNonvanishingOnFiniteHeightCriticalLine
    (FX : Nat -> Complex -> Complex) (H : ℝ) : Prop :=
  ∃ X0 : Nat, ∀ X : Nat, X0 ≤ X -> finiteHeightCriticalLineNonvanishing H (FX X)

def cutoffFamilyEventuallyNonvanishingOnCriticalLine
    (FX : Nat -> Complex -> Complex) : Prop :=
  ∃ X0 : Nat, ∀ X : Nat, X0 ≤ X -> criticalLineNonvanishing (FX X)

theorem finiteHeightCriticalLine_mono {H0 H1 : ℝ} (hH : H0 ≤ H1) {s : Complex}
    (hs : finiteHeightCriticalLine H0 s) : finiteHeightCriticalLine H1 s :=
  ⟨hs.1, le_trans hs.2 hH⟩

theorem finiteHeightCriticalLineNonvanishing_mono {H0 H1 : ℝ} {f : Complex -> Complex}
    (hH : H0 ≤ H1) (hf : finiteHeightCriticalLineNonvanishing H1 f) :
    finiteHeightCriticalLineNonvanishing H0 f := by
  intro s hs
  exact hf s (finiteHeightCriticalLine_mono hH hs)

theorem cutoffFamilyEventuallyNonvanishingOnFiniteHeightCriticalLine_mono
    {FX : Nat -> Complex -> Complex} {H0 H1 : ℝ}
    (hH : H0 ≤ H1)
    (hFX : cutoffFamilyEventuallyNonvanishingOnFiniteHeightCriticalLine FX H1) :
    cutoffFamilyEventuallyNonvanishingOnFiniteHeightCriticalLine FX H0 := by
  rcases hFX with ⟨X0, hX0⟩
  refine ⟨X0, ?_⟩
  intro X hX
  exact finiteHeightCriticalLineNonvanishing_mono hH (hX0 X hX)

theorem highCriticalLine_mono {T0 T1 : ℝ} (hT : T0 ≤ T1) {s : Complex}
    (hs : highCriticalLine T1 s) : highCriticalLine T0 s :=
  ⟨hs.1, le_trans hT hs.2⟩

theorem highCriticalLineNonvanishing_mono {T0 T1 : ℝ} {f : Complex -> Complex}
    (hT : T0 ≤ T1) (hf : highCriticalLineNonvanishing T0 f) :
    highCriticalLineNonvanishing T1 f := by
  intro s hs
  exact hf s (highCriticalLine_mono hT hs)

theorem cutoffFamilyEventuallyNonvanishingOnHighCriticalLine_mono
    {FX : Nat -> Complex -> Complex} {T0 T1 : ℝ}
    (hT : T0 ≤ T1)
    (hFX : cutoffFamilyEventuallyNonvanishingOnHighCriticalLine FX T0) :
    cutoffFamilyEventuallyNonvanishingOnHighCriticalLine FX T1 := by
  rcases hFX with ⟨X0, hX0⟩
  refine ⟨X0, ?_⟩
  intro X hX
  exact highCriticalLineNonvanishing_mono hT (hX0 X hX)

theorem cutoffFamilyEventuallyNonvanishingOnCriticalLine_of_finite_and_high_of_le
    {FX : Nat -> Complex -> Complex} {T0 H : ℝ}
    (hT : T0 ≤ H)
    (hFinite : cutoffFamilyEventuallyNonvanishingOnFiniteHeightCriticalLine FX H)
    (hHigh : cutoffFamilyEventuallyNonvanishingOnHighCriticalLine FX T0) :
    cutoffFamilyEventuallyNonvanishingOnCriticalLine FX := by
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

theorem cutoffFamilyEventuallyNonvanishingOnCriticalLine_of_default_finite_and_high
    {FX : Nat -> Complex -> Complex}
    (hFinite :
      cutoffFamilyEventuallyNonvanishingOnFiniteHeightCriticalLine FX defaultCertifiedHeight)
    (hHigh : cutoffFamilyEventuallyNonvanishingOnHighCriticalLine FX defaultT0) :
    cutoffFamilyEventuallyNonvanishingOnCriticalLine FX := by
  exact cutoffFamilyEventuallyNonvanishingOnCriticalLine_of_finite_and_high_of_le
    defaultT0_le_defaultCertifiedHeight hFinite hHigh

def cutoffFirstShellEventuallyNonzeroOnHighCriticalLine (T0 : ℝ) : Prop :=
  ∃ X0 : Nat,
    ∀ X : Nat, X0 ≤ X -> ∀ s : Complex,
      highCriticalLine T0 s -> cutoffFirstShell X s ≠ 0

def canonicalResidualDominatedOnHighCriticalLine (T0 : ℝ) : Prop :=
  ∃ X0 : Nat,
    ∀ X : Nat, X0 ≤ X -> ∀ s : Complex,
      highCriticalLine T0 s ->
        ‖canonicalCutoffResidual X s‖ < (7 / 10 : ℝ) * ‖cutoffFirstShell X s‖

structure CanonicalCriticalLineAsymptoticData (T0 : ℝ) where
  scale : Nat -> Complex -> ℝ
  kappa : ℝ
  hkappa : kappa < (7 / 10 : ℝ)
  hScalePos :
    ∀ X : Nat, ∀ s : Complex, highCriticalLine T0 s -> 0 < scale X s
  hFirstShellLower :
    ∃ X0 : Nat,
      ∀ X : Nat, X0 ≤ X -> ∀ s : Complex,
        highCriticalLine T0 s -> scale X s ≤ ‖cutoffFirstShell X s‖
  hResidualUpper :
    ∃ X0 : Nat,
      ∀ X : Nat, X0 ≤ X -> ∀ s : Complex,
        highCriticalLine T0 s -> ‖canonicalCutoffResidual X s‖ ≤ kappa * scale X s

theorem canonicalResidualDominatedOnHighCriticalLine_of_asymptoticData
    {T0 : ℝ} (hData : CanonicalCriticalLineAsymptoticData T0) :
    canonicalResidualDominatedOnHighCriticalLine T0 := by
  rcases hData.hFirstShellLower with ⟨XFirst, hFirst⟩
  rcases hData.hResidualUpper with ⟨XResidual, hResidual⟩
  refine ⟨max XFirst XResidual, ?_⟩
  intro X hX s hs
  have hLower : hData.scale X s ≤ ‖cutoffFirstShell X s‖ :=
    hFirst X (le_trans (le_max_left _ _) hX) s hs
  have hUpper : ‖canonicalCutoffResidual X s‖ ≤ hData.kappa * hData.scale X s :=
    hResidual X (le_trans (le_max_right _ _) hX) s hs
  have hScalePos : 0 < hData.scale X s := hData.hScalePos X s hs
  have hKappaScale : hData.kappa * hData.scale X s < (7 / 10 : ℝ) * hData.scale X s := by
    nlinarith [hData.hkappa, hScalePos]
  have hScaleToFirst :
      (7 / 10 : ℝ) * hData.scale X s ≤ (7 / 10 : ℝ) * ‖cutoffFirstShell X s‖ := by
    exact mul_le_mul_of_nonneg_left hLower (by norm_num)
  exact lt_of_le_of_lt hUpper (lt_of_lt_of_le hKappaScale hScaleToFirst)

theorem cutoffFirstShellEventuallyNonzeroOnHighCriticalLine_of_asymptoticData
    {T0 : ℝ} (hData : CanonicalCriticalLineAsymptoticData T0) :
    cutoffFirstShellEventuallyNonzeroOnHighCriticalLine T0 := by
  rcases hData.hFirstShellLower with ⟨XFirst, hFirst⟩
  refine ⟨XFirst, ?_⟩
  intro X hX s hs
  apply norm_pos_iff.mp
  have hScalePos : 0 < hData.scale X s := hData.hScalePos X s hs
  have hLower : hData.scale X s ≤ ‖cutoffFirstShell X s‖ := hFirst X hX s hs
  exact lt_of_lt_of_le hScalePos hLower

theorem sharpCutoffFamilyEventuallyNonvanishingOnHighCriticalLine_of_firstShell
    {T0 : ℝ}
    (hFirst : cutoffFirstShellEventuallyNonzeroOnHighCriticalLine T0) :
    cutoffFamilyEventuallyNonvanishingOnHighCriticalLine sharpCutoffFamily T0 := by
  rcases hFirst with ⟨XFirst, hXFirst⟩
  refine ⟨max 3 XFirst, ?_⟩
  intro X hX s hs
  have hX3 : 3 ≤ X := le_trans (le_max_left _ _) hX
  have hFirstX : cutoffFirstShell X s ≠ 0 :=
    hXFirst X (le_trans (le_max_right _ _) hX) s hs
  exact sharpCutoffFamily_nonzero_of_criticalLine_cutoffFirstShell_ne_zero hX3 s hs.1 hFirstX

theorem sharpCutoffFamilyEventuallyNonvanishingOnHighCriticalLine_of_asymptoticData
    {T0 : ℝ} (hData : CanonicalCriticalLineAsymptoticData T0) :
    cutoffFamilyEventuallyNonvanishingOnHighCriticalLine sharpCutoffFamily T0 := by
  exact sharpCutoffFamilyEventuallyNonvanishingOnHighCriticalLine_of_firstShell
    (cutoffFirstShellEventuallyNonzeroOnHighCriticalLine_of_asymptoticData hData)

theorem canonicalCutoffFamilyEventuallyNonvanishingOnHighCriticalLine_of_residualDominance
    {T0 : ℝ}
    (hResidual : canonicalResidualDominatedOnHighCriticalLine T0) :
    cutoffFamilyEventuallyNonvanishingOnHighCriticalLine canonicalCutoffFamily T0 := by
  rcases hResidual with ⟨XResidual, hXResidual⟩
  refine ⟨max 3 XResidual, ?_⟩
  intro X hX s hs
  have hX3 : 3 ≤ X := le_trans (le_max_left _ _) hX
  have hResidualX :
      ‖canonicalCutoffResidual X s‖ < (7 / 10 : ℝ) * ‖cutoffFirstShell X s‖ :=
    hXResidual X (le_trans (le_max_right _ _) hX) s hs
  exact canonicalCutoffFamily_nonzero_of_criticalLine_residual_lt_seventyHundredths
    hX3 s hs.1 hResidualX

theorem canonicalCutoffFamilyEventuallyNonvanishingOnHighCriticalLine_of_asymptoticData
    {T0 : ℝ} (hData : CanonicalCriticalLineAsymptoticData T0) :
    cutoffFamilyEventuallyNonvanishingOnHighCriticalLine canonicalCutoffFamily T0 := by
  exact canonicalCutoffFamilyEventuallyNonvanishingOnHighCriticalLine_of_residualDominance
    (canonicalResidualDominatedOnHighCriticalLine_of_asymptoticData hData)

structure DefaultCriticalLineData (FX : Nat -> Complex -> Complex) : Prop where
  hFinite : cutoffFamilyEventuallyNonvanishingOnFiniteHeightCriticalLine FX defaultCertifiedHeight
  hHigh : cutoffFamilyEventuallyNonvanishingOnHighCriticalLine FX defaultT0

theorem cutoffFamilyEventuallyNonvanishingOnCriticalLine_of_defaultData
    {FX : Nat -> Complex -> Complex}
    (hData : DefaultCriticalLineData FX) :
    cutoffFamilyEventuallyNonvanishingOnCriticalLine FX := by
  exact cutoffFamilyEventuallyNonvanishingOnCriticalLine_of_default_finite_and_high
    hData.hFinite hData.hHigh

structure DefaultCanonicalCriticalLineResidualData : Prop where
  hFinite :
    cutoffFamilyEventuallyNonvanishingOnFiniteHeightCriticalLine
      canonicalCutoffFamily defaultCertifiedHeight
  hResidual : canonicalResidualDominatedOnHighCriticalLine defaultT0

structure DefaultCanonicalCriticalLineAsymptoticData where
  hFinite :
    cutoffFamilyEventuallyNonvanishingOnFiniteHeightCriticalLine
      canonicalCutoffFamily defaultCertifiedHeight
  hAsymptotic : CanonicalCriticalLineAsymptoticData defaultT0

theorem defaultCanonicalCriticalLineResidualData_of_asymptoticData
    (hData : DefaultCanonicalCriticalLineAsymptoticData) :
    DefaultCanonicalCriticalLineResidualData := by
  refine ⟨hData.hFinite, ?_⟩
  exact canonicalResidualDominatedOnHighCriticalLine_of_asymptoticData hData.hAsymptotic

theorem defaultCriticalLineData_of_canonicalResidualData
    (hData : DefaultCanonicalCriticalLineResidualData) :
    DefaultCriticalLineData canonicalCutoffFamily := by
  refine ⟨hData.hFinite, ?_⟩
  exact canonicalCutoffFamilyEventuallyNonvanishingOnHighCriticalLine_of_residualDominance
    hData.hResidual

theorem canonicalCutoffFamilyEventuallyNonvanishingOnCriticalLine_of_defaultResidualData
    (hData : DefaultCanonicalCriticalLineResidualData) :
    cutoffFamilyEventuallyNonvanishingOnCriticalLine canonicalCutoffFamily := by
  have hDefault := defaultCriticalLineData_of_canonicalResidualData hData
  exact cutoffFamilyEventuallyNonvanishingOnCriticalLine_of_defaultData hDefault

theorem canonicalCutoffFamilyEventuallyNonvanishingOnCriticalLine_of_defaultAsymptoticData
    (hData : DefaultCanonicalCriticalLineAsymptoticData) :
    cutoffFamilyEventuallyNonvanishingOnCriticalLine canonicalCutoffFamily := by
  exact canonicalCutoffFamilyEventuallyNonvanishingOnCriticalLine_of_defaultResidualData
    (defaultCanonicalCriticalLineResidualData_of_asymptoticData hData)
end LeanC2