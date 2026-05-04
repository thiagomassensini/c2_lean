import Mathlib
import LeanC2.Identity.C0NonZero
import LeanC2.Identity.FundamentalIdentity

set_option linter.style.whitespace false

namespace LeanC2

/-- Open right half-plane used throughout the continuation layer. -/
def openRightHalfPlane : Set Complex := {s : Complex | 0 < s.re}

/-- Punctured open right half-plane, excluding the pole at `s = 1`. -/
def puncturedOpenRightHalfPlane : Set Complex := {s : Complex | 0 < s.re ∧ s ≠ 1}

/--
An abstract continuation of the numerator agrees with `F∞` on the original domain `Re(s) > 1`.
-/
def extendsFInfinityOnRightHalfPlane (numFun : Complex -> Complex) : Prop :=
  ∀ s : Complex, 1 < s.re → numFun s = FInfinity s

/--
Thm 17 packaged as the continued identity on `Re(s) > 0`, away from the pole at `s = 1`.
-/
def fundamentalIdentityOnPuncturedRightHalfPlane
    (numFun zetaFun : Complex -> Complex) : Prop :=
  ∀ s : Complex, 0 < s.re → s ≠ 1 → numFun s = c0 s * zetaFun s

/--
Pole-cleared analytic data sufficient to derive the punctured half-plane continuation identity.
-/
structure PoleClearedContinuationData
    (numFun zetaFun : Complex -> Complex) : Prop where
  hExt : extendsFInfinityOnRightHalfPlane numFun
  hNum : AnalyticOnNhd ℂ (fun s => (s - 1) * numFun s) openRightHalfPlane
  hZeta : AnalyticOnNhd ℂ (fun s => (s - 1) * (c0 s * zetaFun s)) openRightHalfPlane

/-- Specialized pole-cleared continuation package for the Riemann zeta channel. -/
abbrev PoleClearedRiemannZetaData (numFun : Complex -> Complex) : Prop :=
  PoleClearedContinuationData numFun riemannZeta

/-- Spectral quotient attached to a continued numerator. -/
noncomputable def spectralZeta (numFun : Complex -> Complex) (s : Complex) : Complex :=
  numFun s / c0 s

/-- Backward-compatible alias for the Thm 17 continuation model. -/
abbrev routeK_thm17_model (numFun zetaFun : Complex -> Complex) : Prop :=
  fundamentalIdentityOnPuncturedRightHalfPlane numFun zetaFun

theorem routeK_thm17_model_iff (numFun zetaFun : Complex -> Complex) :
    routeK_thm17_model numFun zetaFun ↔
      fundamentalIdentityOnPuncturedRightHalfPlane numFun zetaFun := by
  rfl

lemma openRightHalfPlane_convex : Convex ℝ openRightHalfPlane := by
  intro x hx y hy a b ha hb hab
  dsimp [openRightHalfPlane] at hx hy ⊢
  simp only [zero_mul, sub_zero]
  have hxa : 0 ≤ a * x.re := mul_nonneg ha hx.le
  have hyb : 0 ≤ b * y.re := mul_nonneg hb hy.le
  have habPos : 0 < a ∨ 0 < b := by
    by_cases ha0 : a = 0
    · right
      linarith
    · left
      exact lt_of_le_of_ne ha (Ne.symm ha0)
  rcases habPos with haPos | hbPos
  · exact add_pos_of_pos_of_nonneg (mul_pos haPos hx) hyb
  · exact add_pos_of_nonneg_of_pos hxa (mul_pos hbPos hy)

lemma openRightHalfPlane_preconnected : IsPreconnected openRightHalfPlane :=
  openRightHalfPlane_convex.isPreconnected

lemma re_lt_one_ne_one {s : Complex} (hs : s.re < 1) : s ≠ 1 := by
  intro h
  have : s.re = 1 := by simp [h]
  linarith

/--
Identity principle on the open right half-plane from agreement on the smaller half-plane
`Re(s) > 1`.
-/
theorem analyticContinuationBridgeOnOpenRightHalfPlane
    {F G : Complex -> Complex}
    (hF : AnalyticOnNhd ℂ F openRightHalfPlane)
    (hG : AnalyticOnNhd ℂ G openRightHalfPlane)
    (hFG : ∀ s : Complex, 1 < s.re → F s = G s) :
    ∀ s : Complex, 0 < s.re → F s = G s := by
  have hz0 : (2 : Complex) ∈ openRightHalfPlane := by
    simp [openRightHalfPlane]
  have hEv : F =ᶠ[nhds (2 : Complex)] G := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨{s : Complex | 1 < s.re}, ?_, ?_⟩
    · exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    · intro s hs
      exact hFG s hs
  have hEqOn : Set.EqOn F G openRightHalfPlane :=
    hF.eqOn_of_preconnected_of_eventuallyEq hG openRightHalfPlane_preconnected hz0 hEv
  intro s hs
  exact hEqOn hs

/--
Pole-cleared continuation bridge: if `(s - 1) * numFun(s)` and `(s - 1) * c0(s) * ζ(s)`
are analytic on `Re(s) > 0` and agree with the Thm 13 numerator on `Re(s) > 1`, then the
fundamental identity extends to `Re(s) > 0` away from the pole at `s = 1`.
-/
theorem fundamentalIdentityOnPuncturedRightHalfPlane_of_poleClearedAnalytic
    {numFun zetaFun : Complex -> Complex}
    (hExt : extendsFInfinityOnRightHalfPlane numFun)
    (hNum : AnalyticOnNhd ℂ (fun s => (s - 1) * numFun s) openRightHalfPlane)
    (hZeta : AnalyticOnNhd ℂ (fun s => (s - 1) * (c0 s * zetaFun s)) openRightHalfPlane)
    (hId : fundamentalIdentityOnRightHalfPlane zetaFun) :
    fundamentalIdentityOnPuncturedRightHalfPlane numFun zetaFun := by
  intro s hs hs1
  have hProd :=
    analyticContinuationBridgeOnOpenRightHalfPlane hNum hZeta
      (fun z hz => by
        calc
          (z - 1) * numFun z = (z - 1) * FInfinity z := by rw [hExt z hz]
          _ = (z - 1) * (c0 z * zetaFun z) := by rw [hId z hz]) s hs
  exact mul_left_cancel₀ (sub_ne_zero.mpr hs1) hProd

/-- Packaged derivation of the punctured continuation identity from pole-cleared analytic data. -/
theorem fundamentalIdentityOnPuncturedRightHalfPlane_of_data
    {numFun zetaFun : Complex -> Complex}
    (hData : PoleClearedContinuationData numFun zetaFun)
    (hId : fundamentalIdentityOnRightHalfPlane zetaFun) :
    fundamentalIdentityOnPuncturedRightHalfPlane numFun zetaFun := by
  exact fundamentalIdentityOnPuncturedRightHalfPlane_of_poleClearedAnalytic
    hData.hExt hData.hNum hData.hZeta hId

/-- Specialized Thm 17 continuation interface for the Riemann zeta channel. -/
theorem fundamentalIdentity_riemannZeta_on_puncturedRightHalfPlane_of_poleClearedAnalytic
    {numFun : Complex -> Complex}
    (hExt : extendsFInfinityOnRightHalfPlane numFun)
    (hNum : AnalyticOnNhd ℂ (fun s => (s - 1) * numFun s) openRightHalfPlane)
    (hZeta : AnalyticOnNhd ℂ (fun s => (s - 1) * (c0 s * riemannZeta s)) openRightHalfPlane) :
    fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta := by
  exact fundamentalIdentityOnPuncturedRightHalfPlane_of_poleClearedAnalytic
    hExt hNum hZeta fundamentalIdentity_riemannZeta_on_right_half_plane

/-- Packaged specialized derivation of the Riemann-zeta continuation identity. -/
theorem fundamentalIdentity_riemannZeta_on_puncturedRightHalfPlane_of_data
    {numFun : Complex -> Complex}
    (hData : PoleClearedRiemannZetaData numFun) :
    fundamentalIdentityOnPuncturedRightHalfPlane numFun riemannZeta := by
  exact fundamentalIdentityOnPuncturedRightHalfPlane_of_data hData
    fundamentalIdentity_riemannZeta_on_right_half_plane

/-- Ratio form of Thm 17 away from the pole at `s = 1`. -/
theorem fundamentalIdentity_ratio_of_punctured_model {numFun zetaFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun zetaFun)
    {s : Complex} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    spectralZeta numFun s = zetaFun s := by
  have hc0 : c0 s ≠ 0 := c0_ne_zero_of_re_pos hs
  unfold spectralZeta
  calc
    numFun s / c0 s = (c0 s * zetaFun s) / c0 s := by rw [hId s hs hs1]
    _ = zetaFun s := by field_simp [hc0]

/-- Thm 17 transfers nonvanishing between the continued numerator and the zeta channel. -/
theorem fundamentalIdentity_nonzero_iff_of_punctured_model {numFun zetaFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun zetaFun)
    {s : Complex} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    numFun s ≠ 0 ↔ zetaFun s ≠ 0 := by
  have hc0 : c0 s ≠ 0 := c0_ne_zero_of_re_pos hs
  constructor
  · intro hNum hZeta
    apply hNum
    rw [hId s hs hs1, hZeta, mul_zero]
  · intro hZeta hNum
    rw [hId s hs hs1] at hNum
    exact hZeta ((mul_eq_zero.mp hNum).resolve_left hc0)

/-- Off-axis ratio form of Thm 17 on the critical strip `0 < σ < 1`. -/
theorem routeK_thm17_ratio_offaxis {numFun zetaFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun zetaFun)
    {sigma t : Real} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    spectralZeta numFun ((sigma : Complex) + t * Complex.I) =
      zetaFun ((sigma : Complex) + t * Complex.I) := by
  refine fundamentalIdentity_ratio_of_punctured_model hId ?_ ?_
  · simpa [openRightHalfPlane] using hsigma0
  · exact re_lt_one_ne_one (by simpa using hsigma1)

/-- Off-axis nonvanishing transfer on the critical strip `0 < σ < 1`. -/
theorem routeK_thm17_nonzero_transfer {numFun zetaFun : Complex -> Complex}
    (hId : fundamentalIdentityOnPuncturedRightHalfPlane numFun zetaFun)
    {sigma t : Real} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    numFun ((sigma : Complex) + t * Complex.I) ≠ 0 ↔
      zetaFun ((sigma : Complex) + t * Complex.I) ≠ 0 := by
  refine fundamentalIdentity_nonzero_iff_of_punctured_model hId ?_ ?_
  · simpa [openRightHalfPlane] using hsigma0
  · exact re_lt_one_ne_one (by simpa using hsigma1)

/-!
Scaffold for the meromorphic extension step (Thm 17).

Primary sources:
- docs/c2_prova_continuacao_Z_zeta.md
- docs/algebra_Z_igual_zeta.md

The actual continuation object is kept abstract as `numFun`; this avoids forcing the raw
Dirichlet-series definition `FInfinity` outside its convergence domain while still exposing the
ratio and nonvanishing consequences required by the transfer layer.
-/

end LeanC2