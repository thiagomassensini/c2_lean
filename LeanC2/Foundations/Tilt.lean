import Mathlib
import LeanC2.Foundations.Basic
import LeanC2.Foundations.DiscreteLaplacian

namespace LeanC2

open scoped Topology

noncomputable def tiltReal (delta x : Real) : Real :=
  Real.rpow x (-delta)

/-- Real-model tilt bracket used in the C2 route. -/
noncomputable def tiltBracket (delta c : Real) : Real :=
  tiltReal delta (c - 1) + tiltReal delta (c + 1) - 2 * tiltReal delta c

@[simp] theorem tiltBracket_zero (c : Real) :
    tiltBracket 0 c = 0 := by
  simp [tiltBracket, tiltReal]
  ring

@[simp] theorem tiltBracket_neg_one (c : Real) :
    tiltBracket (-1) c = 0 := by
  simp [tiltBracket, tiltReal]
  ring

theorem tiltBracket_one_pos {c : Real} (hc : 1 < c) :
    0 < tiltBracket 1 c := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hcm1 : 0 < c - 1 := sub_pos.mpr hc
  have hcp1 : 0 < c + 1 := by linarith
  have hrepr : tiltBracket 1 c = (c - 1)⁻¹ + (c + 1)⁻¹ - 2 * c⁻¹ := by
    simp [tiltBracket, tiltReal, Real.rpow_neg_one]
  rw [hrepr]
  have hformula :
      (c - 1)⁻¹ + (c + 1)⁻¹ - 2 * c⁻¹ = 2 / (c * (c - 1) * (c + 1)) := by
    field_simp [hc0.ne', hcm1.ne', hcp1.ne']
    ring_nf
  rw [hformula]
  have hden : 0 < c * (c - 1) * (c + 1) :=
    mul_pos (mul_pos hc0 hcm1) hcp1
  exact div_pos (by norm_num) hden

lemma centeredSecond_pos_of_strictConvexOn_Ici {f : Real -> Real}
    (hconv : StrictConvexOn Real (Set.Ici 0) f) {c : Real} (hc : 1 < c) :
    0 < f (c - 1) + f (c + 1) - 2 * f c := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hcm1 : c - 1 ∈ Set.Ici 0 := by
    exact sub_nonneg.mpr (le_of_lt hc)
  have hcp1 : c + 1 ∈ Set.Ici 0 := by
    exact le_of_lt (add_pos hc0 zero_lt_one)
  have hxy : c - 1 ≠ c + 1 := by linarith
  have hmid := hconv.2 hcm1 hcp1 hxy (by norm_num : 0 < (1 / 2 : Real))
    (by norm_num : 0 < (1 / 2 : Real)) (by norm_num : (1 / 2 : Real) + 1 / 2 = 1)
  have hcomb : (2 : Real)⁻¹ * (c - 1) + (2 : Real)⁻¹ * (c + 1) = c := by ring
  have hmid0 :
      f ((2 : Real)⁻¹ * (c - 1) + (2 : Real)⁻¹ * (c + 1)) <
        (2 : Real)⁻¹ * f (c - 1) + (2 : Real)⁻¹ * f (c + 1) := by
    simpa [smul_eq_mul] using hmid
  have hmid1 :
      f c < (2 : Real)⁻¹ * f (c - 1) + (2 : Real)⁻¹ * f (c + 1) := by
    simpa [hcomb] using hmid0
  have h2 : 2 * f c < f (c - 1) + f (c + 1) := by
    nlinarith [hmid1]
  linarith [h2]

lemma centeredSecond_pos_of_strictConvexOn_Ioi {f : Real -> Real}
    (hconv : StrictConvexOn Real (Set.Ioi 0) f) {c : Real} (hc : 1 < c) :
    0 < f (c - 1) + f (c + 1) - 2 * f c := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hcm1 : c - 1 ∈ Set.Ioi 0 := by
    exact sub_pos.mpr hc
  have hcp1 : c + 1 ∈ Set.Ioi 0 := by
    exact add_pos hc0 zero_lt_one
  have hxy : c - 1 ≠ c + 1 := by linarith
  have hmid := hconv.2 hcm1 hcp1 hxy (by norm_num : 0 < (1 / 2 : Real))
    (by norm_num : 0 < (1 / 2 : Real)) (by norm_num : (1 / 2 : Real) + 1 / 2 = 1)
  have hcomb : (2 : Real)⁻¹ * (c - 1) + (2 : Real)⁻¹ * (c + 1) = c := by ring
  have hmid0 :
      f ((2 : Real)⁻¹ * (c - 1) + (2 : Real)⁻¹ * (c + 1)) <
        (2 : Real)⁻¹ * f (c - 1) + (2 : Real)⁻¹ * f (c + 1) := by
    simpa [smul_eq_mul] using hmid
  have hmid1 :
      f c < (2 : Real)⁻¹ * f (c - 1) + (2 : Real)⁻¹ * f (c + 1) := by
    simpa [hcomb] using hmid0
  have h2 : 2 * f c < f (c - 1) + f (c + 1) := by
    nlinarith [hmid1]
  linarith [h2]

lemma centeredSecond_neg_of_strictConcaveOn_Ici {f : Real -> Real}
    (hconc : StrictConcaveOn Real (Set.Ici 0) f) {c : Real} (hc : 1 < c) :
    f (c - 1) + f (c + 1) - 2 * f c < 0 := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hcm1 : c - 1 ∈ Set.Ici 0 := by
    exact sub_nonneg.mpr (le_of_lt hc)
  have hcp1 : c + 1 ∈ Set.Ici 0 := by
    exact le_of_lt (add_pos hc0 zero_lt_one)
  have hxy : c - 1 ≠ c + 1 := by linarith
  have hmid := hconc.2 hcm1 hcp1 hxy (by norm_num : 0 < (1 / 2 : Real))
    (by norm_num : 0 < (1 / 2 : Real)) (by norm_num : (1 / 2 : Real) + 1 / 2 = 1)
  have hcomb : (2 : Real)⁻¹ * (c - 1) + (2 : Real)⁻¹ * (c + 1) = c := by ring
  have hmid0 :
      (2 : Real)⁻¹ * f (c - 1) + (2 : Real)⁻¹ * f (c + 1) <
        f ((2 : Real)⁻¹ * (c - 1) + (2 : Real)⁻¹ * (c + 1)) := by
    simpa [smul_eq_mul] using hmid
  have hmid1 : (2 : Real)⁻¹ * f (c - 1) + (2 : Real)⁻¹ * f (c + 1) < f c := by
    simpa [hcomb] using hmid0
  have h2 : f (c - 1) + f (c + 1) < 2 * f c := by
    nlinarith [hmid1]
  linarith [h2]

theorem tiltBracket_pos_of_lt_neg_one {delta c : Real} (hdelta : delta < -1) (hc : 1 < c) :
    0 < tiltBracket delta c := by
  have hp : 1 < -delta := by linarith
  have hconv : StrictConvexOn Real (Set.Ici 0) (fun x : Real => x ^ (-delta)) :=
    strictConvexOn_rpow hp
  have hpos := centeredSecond_pos_of_strictConvexOn_Ici hconv hc
  simpa [tiltBracket, tiltReal] using hpos

theorem tiltBracket_neg_of_neg_one_lt {delta c : Real} (hdelta0 : -1 < delta) (hdelta1 : delta < 0)
    (hc : 1 < c) :
    tiltBracket delta c < 0 := by
  have hp0 : 0 < -delta := by linarith
  have hp1 : -delta < 1 := by linarith
  have hconc : StrictConcaveOn Real (Set.Ici 0) (fun x : Real => x ^ (-delta)) :=
    Real.strictConcaveOn_rpow hp0 hp1
  have hneg := centeredSecond_neg_of_strictConcaveOn_Ici hconc hc
  simpa [tiltBracket, tiltReal] using hneg

/-- For `p < 0`, `x ↦ x ^ p` is strictly convex on `(0, ∞)`. -/
theorem strictConvexOn_rpow_of_neg {p : Real} (hp : p < 0) :
    StrictConvexOn Real (Set.Ioi 0) (fun x : Real => x ^ p) := by
  apply strictConvexOn_of_deriv2_pos (convex_Ioi 0)
  · exact fun x hx =>
      (Real.continuousAt_rpow_const x p (Or.inl (ne_of_gt hx))).continuousWithinAt
  intro x hx
  rw [interior_Ioi, Set.mem_Ioi] at hx
  simp only [Real.iter_deriv_rpow_const]
  apply mul_pos
  · have : (descPochhammer Real 2).eval p = p * (p - 1) := by
      simp [descPochhammer, Polynomial.eval_mul, Polynomial.eval_sub]
    rw [this]
    exact mul_pos_of_neg_of_neg hp (by linarith)
  · exact Real.rpow_pos_of_pos hx _

theorem tiltBracket_pos_of_pos {delta c : Real} (hdelta : 0 < delta) (hc : 1 < c) :
    0 < tiltBracket delta c := by
  have hp : -delta < 0 := by linarith
  have hconv := strictConvexOn_rpow_of_neg hp
  have hpos := centeredSecond_pos_of_strictConvexOn_Ioi hconv hc
  simpa [tiltBracket, tiltReal] using hpos

theorem tiltBracket_pos_of_nat {n : Nat} (hn : 0 < n) {c : Real} (hc : 1 < c) :
    0 < tiltBracket (n : Real) c := by
  have hconv : StrictConvexOn Real (Set.Ioi 0) (fun x : Real => x ^ (-(n : Int))) := by
    exact strictConvexOn_zpow (by omega) (by omega)
  have hpos : 0 < (c - 1) ^ (-(n : Int)) + (c + 1) ^ (-(n : Int)) - 2 * c ^ (-(n : Int)) := by
    exact centeredSecond_pos_of_strictConvexOn_Ioi hconv hc
  have hrewrite :
      tiltBracket (n : Real) c =
        (c - 1) ^ (-(n : Int)) + (c + 1) ^ (-(n : Int)) - 2 * c ^ (-(n : Int)) := by
    simp [tiltBracket, tiltReal, Real.rpow_neg_natCast]
  rw [hrewrite]
  exact hpos

theorem tiltBracket_sign_definiteness {delta c : Real} (hc : 1 < c) :
    (0 < delta -> 0 < tiltBracket delta c) ∧
    (delta = 0 -> tiltBracket delta c = 0) ∧
    (-1 < delta -> delta < 0 -> tiltBracket delta c < 0) ∧
    (delta = -1 -> tiltBracket delta c = 0) ∧
    (delta < -1 -> 0 < tiltBracket delta c) := by
  exact ⟨fun hdelta => tiltBracket_pos_of_pos hdelta hc,
    fun hEq => by simp [hEq],
    fun hgt hlt => tiltBracket_neg_of_neg_one_lt hgt hlt hc,
    fun hEq => by simp [hEq],
    fun hlt => tiltBracket_pos_of_lt_neg_one hlt hc⟩

theorem tiltBracket_sign_definiteness_nonpos {delta c : Real} (hc : 1 < c) :
    (delta < -1 -> 0 < tiltBracket delta c) ∧
    (delta = -1 -> tiltBracket delta c = 0) ∧
    (-1 < delta -> delta < 0 -> tiltBracket delta c < 0) ∧
    (delta = 0 -> tiltBracket delta c = 0) := by
  obtain ⟨hpos, hzero, hneg, hm1, hltm1⟩ := tiltBracket_sign_definiteness hc
  exact ⟨hltm1, hm1, hneg, hzero⟩

theorem routeK_thm2_tilt_annihilation (c : Real) :
    tiltBracket 0 c = 0 := by
  exact tiltBracket_zero c

theorem routeK_thm5_sign_nonpos {delta c : Real} (hc : 1 < c) :
    (delta < -1 -> 0 < tiltBracket delta c) ∧
    (delta = -1 -> tiltBracket delta c = 0) ∧
    (-1 < delta -> delta < 0 -> tiltBracket delta c < 0) ∧
    (delta = 0 -> tiltBracket delta c = 0) := by
  exact tiltBracket_sign_definiteness_nonpos hc

theorem routeK_thm5_sign_pos {delta : Real} (hdelta : 0 < delta) {c : Real} (hc : 1 < c) :
    0 < tiltBracket delta c := by
  exact tiltBracket_pos_of_pos hdelta hc

theorem routeK_thm5_sign_nat_pos {n : Nat} (hn : 0 < n) {c : Real} (hc : 1 < c) :
    0 < tiltBracket (n : Real) c := by
  exact tiltBracket_pos_of_nat hn hc

theorem routeK_thm5_sign_bundle {c : Real} (hc : 1 < c) :
    (∀ delta : Real, 0 < delta -> 0 < tiltBracket delta c) ∧
    (∀ delta : Real, delta = 0 -> tiltBracket delta c = 0) ∧
    (∀ delta : Real, -1 < delta -> delta < 0 -> tiltBracket delta c < 0) ∧
    (∀ delta : Real, delta = -1 -> tiltBracket delta c = 0) ∧
    (∀ delta : Real, delta < -1 -> 0 < tiltBracket delta c) := by
  exact ⟨fun delta hdelta => tiltBracket_pos_of_pos hdelta hc,
    fun delta hdelta => by simp [hdelta],
    fun delta hdelta0 hdelta1 => tiltBracket_neg_of_neg_one_lt hdelta0 hdelta1 hc,
    fun delta hdelta => by simp [hdelta],
    fun delta hdelta => tiltBracket_pos_of_lt_neg_one hdelta hc⟩

/-!
Scaffold for Thm 2 and Thm 5: annihilation and sign-definiteness.

Primary sources:
- docs/derivacao_tilt_c2_global.md
- docs/c2_rota_K_rigorosamente_fechada.md

Legacy seeds:
- Lean/Antigo_Lean_C2/Tilt.lean
- Lean/Antigo_Lean_C2/TiltConvexity.lean
-/

end LeanC2
