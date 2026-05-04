import Mathlib
import LeanC2.Normalization

namespace LeanC2

/-- Canonical Thm 13 identity equation. -/
def routeK_thm13_identity (Dinf Binf c0 zeta : ℂ) : Prop :=
  Dinf - Binf = c0 * zeta

/-- Backward-compatibility alias for older `_model` API. -/
abbrev routeK_thm13_model (Dinf Binf c0 zeta : ℂ) : Prop :=
  routeK_thm13_identity Dinf Binf c0 zeta

/-- Thm 13 model consequence: ratio form from product form (assuming `c0 ≠ 0`). -/
theorem routeK_thm13_ratio_of_model {Dinf Binf c0 zeta : ℂ}
    (h : routeK_thm13_model Dinf Binf c0 zeta) (hc0 : c0 ≠ 0) :
    (Dinf - Binf) / c0 = zeta := by
  dsimp [routeK_thm13_model, routeK_thm13_identity] at h
  calc
    (Dinf - Binf) / c0 = (c0 * zeta) / c0 := by simp [h]
    _ = zeta := by field_simp [hc0]

/-- Canonical Thm 17 continuation identity on the half-plane `Re(s) > 0`. -/
def routeK_thm17_halfplane_eq (F G : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, 0 < s.re → F s = G s

/-- Backward-compatibility alias for older `_model` API. -/
abbrev routeK_thm17_model (F G : ℂ → ℂ) : Prop :=
  routeK_thm17_halfplane_eq F G

/-- Direct constructor for the Thm 17 model wrapper. -/
theorem routeK_thm17_model_intro {F G : ℂ → ℂ}
    (h : ∀ s : ℂ, 0 < s.re → F s = G s) : routeK_thm17_model F G :=
  h

theorem routeK_thm13_identity_iff (Dinf Binf c0 zeta : ℂ) :
    routeK_thm13_identity Dinf Binf c0 zeta ↔ routeK_thm13_model Dinf Binf c0 zeta := by
  rfl

/-- Promoted Thm 13 ratio consequence (non-model API). -/
theorem routeK_thm13_ratio {Dinf Binf c0 zeta : ℂ}
    (h : routeK_thm13_identity Dinf Binf c0 zeta) (hc0 : c0 ≠ 0) :
    (Dinf - Binf) / c0 = zeta := by
  exact routeK_thm13_ratio_of_model h hc0


theorem routeK_thm17_halfplane_eq_iff (F G : ℂ → ℂ) :
    routeK_thm17_halfplane_eq F G ↔ routeK_thm17_model F G := by
  rfl

/-- Promoted direct constructor for the Thm 17 half-plane identity. -/
theorem routeK_thm17_halfplane_eq_intro {F G : ℂ → ℂ}
    (h : ∀ s : ℂ, 0 < s.re → F s = G s) : routeK_thm17_halfplane_eq F G := by
  exact routeK_thm17_model_intro h

/--
Promoted Thm 17 off-axis evaluator:
instantiates the half-plane identity on points `σ + it` with `σ > 0`.
-/
theorem routeK_thm17_offaxis_eval {F G : ℂ → ℂ}
    (hFG : routeK_thm17_halfplane_eq F G) {σ t : ℝ} (hσ : 0 < σ) :
    F ((σ : ℂ) + t * Complex.I) = G ((σ : ℂ) + t * Complex.I) := by
  exact hFG _ (by simpa using hσ)

/--
Promoted Thm 13 concrete off-axis ratio consequence with `c0 = c0Complex(σ+it)`.
-/
theorem routeK_thm13_ratio_offaxis (σ t : ℝ) (hσ : 0 < σ)
    (Dinf Binf zeta : ℂ)
    (hId : Dinf - Binf = c0Complex ((σ : ℂ) + t * Complex.I) * zeta) :
    (Dinf - Binf) / c0Complex ((σ : ℂ) + t * Complex.I) = zeta := by
  have hc0 : c0Complex ((σ : ℂ) + t * Complex.I) ≠ 0 := by
    exact routeK_thm14_c0_nonvanishing_halfplane (by simpa using hσ)
  calc
    (Dinf - Binf) / c0Complex ((σ : ℂ) + t * Complex.I)
        = (c0Complex ((σ : ℂ) + t * Complex.I) * zeta) /
            c0Complex ((σ : ℂ) + t * Complex.I) := by simp [hId]
    _ = zeta := by field_simp [hc0]

/-- Critical-line specialization of `routeK_thm13_ratio_offaxis`. -/
theorem routeK_thm13_ratio_critical (t : ℝ)
    (Dinf Binf zeta : ℂ)
    (hId : Dinf - Binf = c0Complex (((1 : ℂ) / 2) + t * Complex.I) * zeta) :
    (Dinf - Binf) / c0Complex (((1 : ℂ) / 2) + t * Complex.I) = zeta := by
  have hc0 : c0Complex (((1 : ℂ) / 2) + t * Complex.I) ≠ 0 :=
    routeK_thm14_c0_nonvanishing_critical t
  calc
    (Dinf - Binf) / c0Complex (((1 : ℂ) / 2) + t * Complex.I)
        = (c0Complex (((1 : ℂ) / 2) + t * Complex.I) * zeta) /
            c0Complex (((1 : ℂ) / 2) + t * Complex.I) := by rw [hId]
    _ = zeta := by
      have hc0' : c0Complex ((1 + 2 * (t : ℂ) * Complex.I) / 2) ≠ 0 := by
        simpa [show ((1 + 2 * (t : ℂ) * Complex.I) / 2) =
          ((1 : ℂ) / 2) + t * Complex.I by ring] using hc0
      field_simp [hc0']


end LeanC2
