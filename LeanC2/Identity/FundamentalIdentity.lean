import Mathlib
import LeanC2.Identity.C0NonZero
import LeanC2.Operators.Genuine

set_option linter.style.whitespace false

namespace LeanC2

/-- Thm 13 packaged as a statement on the half-plane `Re(s) > 1`. -/
def fundamentalIdentityOnRightHalfPlane (zetaFun : Complex -> Complex) : Prop :=
  ∀ s : Complex, 1 < s.re → FInfinity s = c0 s * zetaFun s

/-- Backward-compatible alias for the Thm 13 model statement. -/
abbrev routeK_thm13_model (zetaFun : Complex -> Complex) : Prop :=
  fundamentalIdentityOnRightHalfPlane zetaFun

theorem routeK_thm13_model_iff (zetaFun : Complex -> Complex) :
    routeK_thm13_model zetaFun ↔ fundamentalIdentityOnRightHalfPlane zetaFun := by
  rfl

/-- Pointwise ratio form of Thm 13 on the convergent side `Re(s) > 1`. -/
theorem fundamentalIdentity_ratio_of_model {zetaFun : Complex -> Complex}
    (hId : fundamentalIdentityOnRightHalfPlane zetaFun) {s : Complex} (hs : 1 < s.re) :
    FInfinity s / c0 s = zetaFun s := by
  have hc0 : c0 s ≠ 0 := c0_ne_zero_of_re_pos (by linarith)
  calc
    FInfinity s / c0 s = (c0 s * zetaFun s) / c0 s := by simp [hId s hs]
    _ = zetaFun s := by field_simp [hc0]

/-- Thm 13 transfers nonvanishing between the numerator and the zeta channel. -/
theorem fundamentalIdentity_nonzero_iff {zetaFun : Complex -> Complex}
    (hId : fundamentalIdentityOnRightHalfPlane zetaFun) {s : Complex} (hs : 1 < s.re) :
    FInfinity s ≠ 0 ↔ zetaFun s ≠ 0 := by
  have hc0 : c0 s ≠ 0 := c0_ne_zero_of_re_pos (by linarith)
  constructor
  · intro hF hz
    apply hF
    rw [hId s hs, hz, mul_zero]
  · intro hz hF
    rw [hId s hs] at hF
    exact hz ((mul_eq_zero.mp hF).resolve_left hc0)

/-- Off-axis evaluation form of the ratio statement, still on the side `σ > 1`. -/
theorem routeK_thm13_ratio_offaxis {zetaFun : Complex -> Complex}
    (hId : fundamentalIdentityOnRightHalfPlane zetaFun) {sigma t : Real} (hsigma : 1 < sigma) :
    FInfinity ((sigma : Complex) + t * Complex.I) /
        c0 ((sigma : Complex) + t * Complex.I) =
      zetaFun ((sigma : Complex) + t * Complex.I) := by
  simpa using
    (fundamentalIdentity_ratio_of_model hId
      (s := ((sigma : Complex) + t * Complex.I))
      (by simpa using hsigma))

/-- Right-half-plane nonvanishing transfer from `F∞` to the zeta channel. -/
theorem routeK_thm13_nonzero_transfer {zetaFun : Complex -> Complex}
    (hId : fundamentalIdentityOnRightHalfPlane zetaFun) {sigma t : Real} (hsigma : 1 < sigma) :
    FInfinity ((sigma : Complex) + t * Complex.I) ≠ 0 ↔
      zetaFun ((sigma : Complex) + t * Complex.I) ≠ 0 := by
  simpa using
    (fundamentalIdentity_nonzero_iff hId
      (s := ((sigma : Complex) + t * Complex.I))
      (by simpa using hsigma))

/-!
Usable Thm 13 interface: once the identity `F_infty = c0 * zeta` is established on
`Re(s) > 1`, this file exposes the ratio and nonvanishing consequences needed by the
later transfer layers.

Primary sources:
- docs/algebra_Z_igual_zeta.md
- docs/c2_rota_K_rigorosamente_fechada.md

Legacy seeds:
- Lean/Antigo_Lean_C2/Identity.lean
-/

end LeanC2