import Mathlib
import LeanC2.Glue.Decomposition
import LeanC2.Operators.Cutoff

namespace LeanC2

noncomputable section

/--
Local-uniform convergence of a cutoff family to its limiting numerator on the
off-critical strip.
-/
def cutoffConvergesLocallyUniformlyOnOffCriticalStrip
    (FX : Nat -> Complex -> Complex)
    (numFun : Complex -> Complex) : Prop :=
  ∀ K : Set Complex, IsCompact K -> K ⊆ offCriticalStripSet ->
    TendstoUniformlyOn (fun X s => FX X s) numFun Filter.atTop K

/--
Canonical convergence package for the concrete family `canonicalCutoffFamily`.

This isolates the concrete Thm-3-style universality input in the cutoff layer,
so the Hurwitz layer can consume a packaged family-specific limit statement.
-/
structure CanonicalCutoffConvergenceData where
  numFun : Complex -> Complex
  hConv :
    cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun

/--
Axiom-level cutoff universality package for `canonicalCutoffFamily`.

This should eventually be replaced by the concrete `O(1 / X)` residual estimate
specialized to `canonicalCutoffFamily`.
-/
axiom canonicalCutoffConvergenceData : CanonicalCutoffConvergenceData

/-- Canonical limiting numerator attached to the concrete cutoff family. -/
abbrev canonicalCutoffLimitFun : Complex -> Complex :=
  canonicalCutoffConvergenceData.numFun

theorem canonicalCutoffFamily_convergesLocallyUniformlyOnOffCriticalStrip :
    cutoffConvergesLocallyUniformlyOnOffCriticalStrip
      canonicalCutoffFamily canonicalCutoffLimitFun :=
  canonicalCutoffConvergenceData.hConv

/-!
Scaffold for the cutoff universality layer (Thm 3).

Primary sources:
- docs/c2_rota_K_rigorosamente_fechada.md

Legacy seeds:
- Lean/Antigo_Lean_C2/CutoffDecay.lean

The abstract local-uniform convergence predicate now lives here, together with
the concrete cutoff-layer package for `canonicalCutoffFamily`. The underlying
quantitative proof remains an explicit universality input until the residual
estimate is wired to this family.
-/

end

end LeanC2
