import Mathlib
import LeanC2.Glue.Decomposition
import LeanC2.Cutoff.Residue

namespace LeanC2

/-- Analyticity of each cutoff approximant on the off-critical strip. -/
def cutoffAnalyticOnOffCriticalStrip (FX : Nat -> Complex -> Complex) : Prop :=
  ∀ X : Nat, AnalyticOnNhd ℂ (FX X) offCriticalStripSet

/--
Cutoff-layer package for off-strip analyticity of a cutoff family.

This keeps the analytic cutoff input anchored in the cutoff layer rather than in the Hurwitz
transfer layer.
-/
structure CutoffAnalyticData (FX : Nat -> Complex -> Complex) : Prop where
  hAnalytic : cutoffAnalyticOnOffCriticalStrip FX

theorem cutoffAnalyticOnOffCriticalStrip_of_pointwise
    {FX : Nat -> Complex -> Complex}
    (hAnalytic : ∀ X : Nat, AnalyticOnNhd ℂ (FX X) offCriticalStripSet) :
    cutoffAnalyticOnOffCriticalStrip FX := hAnalytic

theorem cutoffAnalyticOnOffCriticalStrip_of_data
    {FX : Nat -> Complex -> Complex}
    (hData : CutoffAnalyticData FX) :
    cutoffAnalyticOnOffCriticalStrip FX := hData.hAnalytic

/-!
Scaffold for Thm 16: `|R_X| = O(1 / X)`.

Primary sources:
- docs/c2_prova_taxa_decaimento_cutoff.md
- docs/nota_cutoff_c2.md

Legacy seeds:
- Lean/Antigo_Lean_C2/CutoffDecay.lean

Besides the quantitative decay side, this file now hosts the canonical cutoff-layer packaging of
off-strip analyticity for cutoff families, so the Hurwitz/transfer layer can consume a theoremized
cutoff API instead of a raw analytic hypothesis.
-/

end LeanC2
