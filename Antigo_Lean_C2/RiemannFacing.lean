import LeanC2.FullChain

namespace LeanC2

/-!
# Riemann-facing consequence wrappers

This module is deliberately documentary.  It does not add analytic input and it
does not use Lean as a premise for the paper.  It packages the final paper-level
sanity check:

`C2 off-axis exclusion for Z_spec` + `Z_spec = zeta` on `Re(s) > 0`
implies the critical-line restriction for zeros of the zeta-facing channel.
-/

/-- The open critical strip, expressed only by the real part. -/
def routeK_CriticalStrip (s : ℂ) : Prop :=
  0 < s.re ∧ s.re < 1

/-- The critical line. -/
def routeK_CriticalLine (s : ℂ) : Prop :=
  s.re = (1 : ℝ) / 2

/-- Off the critical line. -/
def routeK_OffCriticalLine (s : ℂ) : Prop :=
  ¬ routeK_CriticalLine s

/--
The paper's RH-facing endpoint, stated for an abstract zeta-facing channel
`ζfun`: every zero in the critical strip lies on the critical line.
-/
def routeK_RHFacingZetaConsequence (ζfun : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, routeK_CriticalStrip s → ζfun s = 0 → routeK_CriticalLine s

/--
C2-side off-axis exclusion for the normalized limiting channel `Z_spec`.
This is the exact C2 input needed by the paper's zeta-facing corollary.
-/
def routeK_ZspecOffAxisExclusion (Dinf Binf : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, routeK_CriticalStrip s → routeK_OffCriticalLine s →
    routeK_Zspec Dinf Binf s ≠ 0

/--
Logical equivalence between the critical-line zero restriction and off-critical
nonvanishing in the critical strip.
-/
theorem routeK_RHFacingZetaConsequence_iff_offCritical_nonvanishing
    (ζfun : ℂ → ℂ) :
    routeK_RHFacingZetaConsequence ζfun ↔
      ∀ s : ℂ, routeK_CriticalStrip s → routeK_OffCriticalLine s →
        ζfun s ≠ 0 := by
  constructor
  · intro hRH s hstrip hoff hzero
    exact hoff (hRH s hstrip hzero)
  · intro hNonzero s hstrip hzero
    by_contra hoff
    exact hNonzero s hstrip hoff hzero

/--
Pointwise paper corollary: under continuation and C2 off-axis exclusion for
`Z_spec`, any zeta-facing zero in the critical strip lies on the critical line.
-/
theorem routeK_zeta_zero_in_strip_on_criticalLine_of_Zspec_offaxis_exclusion
    {Dinf Binf ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s)
    (hZspec : routeK_ZspecOffAxisExclusion Dinf Binf)
    {s : ℂ} (hstrip : routeK_CriticalStrip s)
    (hzero : ζfun s = 0) :
    routeK_CriticalLine s := by
  by_contra hoff
  have hZzero : routeK_Zspec Dinf Binf s = 0 :=
    (routeK_continuation_zero_iff
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun)
      hCont hstrip.1).2 hzero
  exact hZspec s hstrip hoff hZzero

/--
Global paper corollary: C2 off-axis exclusion for `Z_spec`, together with the
continued identity `Z_spec = zeta`, gives the RH-facing zeta consequence.
-/
theorem routeK_RHFacingZetaConsequence_of_Zspec_offaxis_exclusion
    {Dinf Binf ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s)
    (hZspec : routeK_ZspecOffAxisExclusion Dinf Binf) :
    routeK_RHFacingZetaConsequence ζfun := by
  intro s hstrip hzero
  exact routeK_zeta_zero_in_strip_on_criticalLine_of_Zspec_offaxis_exclusion
    (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun)
    hCont hZspec hstrip hzero

/--
Compatibility wrapper for the existing continuation-layer API, whose global
off-axis exclusion hypothesis is written with explicit real-part arguments.
-/
theorem routeK_RHFacingZetaConsequence_of_global_Zspec_nonvanishing
    {Dinf Binf ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s)
    (hZspec : ∀ s : ℂ, 0 < s.re → s.re < 1 →
      s.re ≠ (1 : ℝ) / 2 → routeK_Zspec Dinf Binf s ≠ 0) :
    routeK_RHFacingZetaConsequence ζfun := by
  apply routeK_RHFacingZetaConsequence_of_Zspec_offaxis_exclusion hCont
  intro s hstrip hoff
  exact hZspec s hstrip.1 hstrip.2
    (by
      intro hcrit
      exact hoff (by simpa [routeK_CriticalLine] using hcrit))

/--
Full-chain sanity wrapper: Taylor-dominance data for the C2 numerator implies the
paper's RH-facing zeta consequence through the existing endpoint theorem.
-/
theorem routeK_RHFacingZetaConsequence_of_taylor_dominance
    {Dinf Binf ζfun : ℂ → ℂ}
    (hCont : ∀ s : ℂ, 0 < s.re →
      Dinf s - Binf s = c0Complex s * ζfun s)
    (hTaylor : routeK_OffAxisTaylorDominanceGlobal Dinf Binf) :
    routeK_RHFacingZetaConsequence ζfun := by
  intro s hstrip hzero
  by_contra hoff
  have hhalf : s.re ≠ (1 : ℝ) / 2 := by
    intro hcrit
    exact hoff (by simpa [routeK_CriticalLine] using hcrit)
  have hζne : ζfun s ≠ 0 :=
    routeK_full_chain_zeta_endpoint_of_taylor_dominance
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun)
      hCont hTaylor s hstrip.1 hstrip.2 hhalf
  exact hζne hzero

end LeanC2
