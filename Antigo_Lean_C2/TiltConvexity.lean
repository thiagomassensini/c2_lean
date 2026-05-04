import Mathlib
import LeanC2.Tilt

namespace LeanC2

/-!
# Tilt Convexity Interface

This module isolates the convexity/concavity infrastructure underlying the
tilt-bracket sign theorems already proved in `Tilt.lean`.
-/

/--
Centered-second-difference positivity on `Set.Ici 0` from strict convexity.
-/
theorem routeK_centeredSecond_pos_of_strictConvexOn_Ici
    {f : ℝ → ℝ} (hconv : StrictConvexOn ℝ (Set.Ici 0) f) {c : ℝ}
    (hc : 1 < c) :
    0 < f (c - 1) + f (c + 1) - 2 * f c :=
  centeredSecond_pos_of_strictConvexOn_Ici hconv hc

/--
Centered-second-difference positivity on `Set.Ioi 0` from strict convexity.
-/
theorem routeK_centeredSecond_pos_of_strictConvexOn_Ioi
    {f : ℝ → ℝ} (hconv : StrictConvexOn ℝ (Set.Ioi 0) f) {c : ℝ}
    (hc : 1 < c) :
    0 < f (c - 1) + f (c + 1) - 2 * f c :=
  centeredSecond_pos_of_strictConvexOn_Ioi hconv hc

/--
Centered-second-difference negativity on `Set.Ici 0` from strict concavity.
-/
theorem routeK_centeredSecond_neg_of_strictConcaveOn_Ici
    {f : ℝ → ℝ} (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) {c : ℝ}
    (hc : 1 < c) :
    f (c - 1) + f (c + 1) - 2 * f c < 0 :=
  centeredSecond_neg_of_strictConcaveOn_Ici hconc hc

/--
For negative exponent `p`, `x ↦ x^p` is strictly convex on `(0,∞)`.
-/
theorem routeK_strictConvexOn_rpow_of_neg {p : ℝ} (hp : p < 0) :
    StrictConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x ^ p) :=
  strictConvexOn_rpow_of_neg hp

/--
Convexity/concavity package for the tilt bracket sign regimes.
-/
theorem routeK_tilt_convexity_sign_package {δ c : ℝ} (hc : 1 < c) :
    (0 < δ → 0 < tiltBracket δ c) ∧
    (-1 < δ → δ < 0 → tiltBracket δ c < 0) ∧
    (δ < -1 → 0 < tiltBracket δ c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hδ
    exact tiltBracket_pos_of_pos hδ hc
  · intro hδ0 hδ1
    exact tiltBracket_neg_of_neg_one_lt hδ0 hδ1 hc
  · intro hδ
    exact tiltBracket_pos_of_lt_neg_one hδ hc

/--
Positive-regime tilt sign from convexity of `x ↦ x^(-δ)`.
-/
theorem routeK_tilt_positive_of_convexity {δ c : ℝ}
    (hδ : 0 < δ) (hc : 1 < c) :
    0 < tiltBracket δ c :=
  tiltBracket_pos_of_pos hδ hc

/--
Inner negative-regime tilt sign from concavity of `x ↦ x^(-δ)`.
-/
theorem routeK_tilt_negative_of_concavity {δ c : ℝ}
    (hδ0 : -1 < δ) (hδ1 : δ < 0) (hc : 1 < c) :
    tiltBracket δ c < 0 :=
  tiltBracket_neg_of_neg_one_lt hδ0 hδ1 hc

/--
Outer negative-regime tilt sign from convexity of `x ↦ x^(-δ)`.
-/
theorem routeK_tilt_positive_of_large_negative {δ c : ℝ}
    (hδ : δ < -1) (hc : 1 < c) :
    0 < tiltBracket δ c :=
  tiltBracket_pos_of_lt_neg_one hδ hc

end LeanC2
