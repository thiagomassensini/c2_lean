import Mathlib
import LeanC2.Normalization
import LeanC2.OperatorNorm

namespace LeanC2

open scoped Topology

/-- Centered finite-difference bracket at integer center `c`. -/
def centeredBracket (f : ℤ → ℝ) (c : ℤ) : ℝ :=
  f (c - 1) + f (c + 1) - 2 * f c

@[simp] theorem centeredBracket_const (a : ℝ) (c : ℤ) :
    centeredBracket (fun _ : ℤ => a) c = 0 := by
  simp [centeredBracket]
  ring

@[simp] theorem centeredBracket_affine (a b : ℝ) (c : ℤ) :
    centeredBracket (fun n : ℤ => a * (n : ℝ) + b) c = 0 := by
  simp [centeredBracket]
  ring

/-- Real-model tilt bracket used in the C2 route. -/
noncomputable def tiltBracket (δ c : ℝ) : ℝ :=
  Real.rpow (c - 1) (-δ) + Real.rpow (c + 1) (-δ) - 2 * Real.rpow c (-δ)

@[simp] theorem tiltBracket_zero (c : ℝ) :
    tiltBracket 0 c = 0 := by
  simp [tiltBracket]
  ring

@[simp] theorem tiltBracket_neg_one (c : ℝ) :
    tiltBracket (-1) c = 0 := by
  simp [tiltBracket]
  ring

theorem tiltBracket_one_pos {c : ℝ} (hc : 1 < c) :
    0 < tiltBracket 1 c := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hcm1 : 0 < c - 1 := sub_pos.mpr hc
  have hcp1 : 0 < c + 1 := by linarith
  have hrepr : tiltBracket 1 c = (c - 1)⁻¹ + (c + 1)⁻¹ - 2 * c⁻¹ := by
    simp [tiltBracket, Real.rpow_neg_one]
  rw [hrepr]
  have hformula :
      (c - 1)⁻¹ + (c + 1)⁻¹ - 2 * c⁻¹ = 2 / (c * (c - 1) * (c + 1)) := by
    field_simp [hc0.ne', hcm1.ne', hcp1.ne']
    ring_nf
  rw [hformula]
  have hden : 0 < c * (c - 1) * (c + 1) :=
    mul_pos (mul_pos hc0 hcm1) hcp1
  exact div_pos (by norm_num) hden

lemma centeredSecond_pos_of_strictConvexOn_Ici {f : ℝ → ℝ}
    (hconv : StrictConvexOn ℝ (Set.Ici 0) f) {c : ℝ} (hc : 1 < c) :
    0 < f (c - 1) + f (c + 1) - 2 * f c := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hcm1 : c - 1 ∈ Set.Ici 0 := by
    exact sub_nonneg.mpr (le_of_lt hc)
  have hcp1 : c + 1 ∈ Set.Ici 0 := by
    exact le_of_lt (add_pos hc0 zero_lt_one)
  have hxy : c - 1 ≠ c + 1 := by linarith
  have hmid := hconv.2 hcm1 hcp1 hxy (by norm_num : 0 < (1 / 2 : ℝ))
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hcomb : (2 : ℝ)⁻¹ * (c - 1) + (2 : ℝ)⁻¹ * (c + 1) = c := by ring
  have hmid0 :
      f ((2 : ℝ)⁻¹ * (c - 1) + (2 : ℝ)⁻¹ * (c + 1)) <
        (2 : ℝ)⁻¹ * f (c - 1) + (2 : ℝ)⁻¹ * f (c + 1) := by
    simpa [smul_eq_mul] using hmid
  have hmid1 :
      f c < (2 : ℝ)⁻¹ * f (c - 1) + (2 : ℝ)⁻¹ * f (c + 1) := by
    simpa [hcomb] using hmid0
  have h2 : 2 * f c < f (c - 1) + f (c + 1) := by
    nlinarith [hmid1]
  have hfinal : 0 < f (c - 1) + f (c + 1) - 2 * f c := by
    linarith [h2]
  exact hfinal

lemma centeredSecond_pos_of_strictConvexOn_Ioi {f : ℝ → ℝ}
    (hconv : StrictConvexOn ℝ (Set.Ioi 0) f) {c : ℝ} (hc : 1 < c) :
    0 < f (c - 1) + f (c + 1) - 2 * f c := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hcm1 : c - 1 ∈ Set.Ioi 0 := by
    exact sub_pos.mpr hc
  have hcp1 : c + 1 ∈ Set.Ioi 0 := by
    exact add_pos hc0 zero_lt_one
  have hxy : c - 1 ≠ c + 1 := by linarith
  have hmid := hconv.2 hcm1 hcp1 hxy (by norm_num : 0 < (1 / 2 : ℝ))
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hcomb : (2 : ℝ)⁻¹ * (c - 1) + (2 : ℝ)⁻¹ * (c + 1) = c := by ring
  have hmid0 :
      f ((2 : ℝ)⁻¹ * (c - 1) + (2 : ℝ)⁻¹ * (c + 1)) <
        (2 : ℝ)⁻¹ * f (c - 1) + (2 : ℝ)⁻¹ * f (c + 1) := by
    simpa [smul_eq_mul] using hmid
  have hmid1 :
      f c < (2 : ℝ)⁻¹ * f (c - 1) + (2 : ℝ)⁻¹ * f (c + 1) := by
    simpa [hcomb] using hmid0
  have h2 : 2 * f c < f (c - 1) + f (c + 1) := by
    nlinarith [hmid1]
  have hfinal : 0 < f (c - 1) + f (c + 1) - 2 * f c := by
    linarith [h2]
  exact hfinal

lemma centeredSecond_neg_of_strictConcaveOn_Ici {f : ℝ → ℝ}
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) {c : ℝ} (hc : 1 < c) :
    f (c - 1) + f (c + 1) - 2 * f c < 0 := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hcm1 : c - 1 ∈ Set.Ici 0 := by
    exact sub_nonneg.mpr (le_of_lt hc)
  have hcp1 : c + 1 ∈ Set.Ici 0 := by
    exact le_of_lt (add_pos hc0 zero_lt_one)
  have hxy : c - 1 ≠ c + 1 := by linarith
  have hmid := hconc.2 hcm1 hcp1 hxy (by norm_num : 0 < (1 / 2 : ℝ))
    (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hcomb : (2 : ℝ)⁻¹ * (c - 1) + (2 : ℝ)⁻¹ * (c + 1) = c := by ring
  have hmid0 :
      (2 : ℝ)⁻¹ * f (c - 1) + (2 : ℝ)⁻¹ * f (c + 1) <
        f ((2 : ℝ)⁻¹ * (c - 1) + (2 : ℝ)⁻¹ * (c + 1)) := by
    simpa [smul_eq_mul] using hmid
  have hmid1 : (2 : ℝ)⁻¹ * f (c - 1) + (2 : ℝ)⁻¹ * f (c + 1) < f c := by
    simpa [hcomb] using hmid0
  have h2 : f (c - 1) + f (c + 1) < 2 * f c := by
    nlinarith [hmid1]
  have hfinal : f (c - 1) + f (c + 1) - 2 * f c < 0 := by
    linarith [h2]
  exact hfinal

theorem tiltBracket_pos_of_lt_neg_one {δ c : ℝ} (hδ : δ < -1) (hc : 1 < c) :
    0 < tiltBracket δ c := by
  have hp : 1 < -δ := by linarith
  have hconv : StrictConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ (-δ)) :=
    strictConvexOn_rpow hp
  have hpos := centeredSecond_pos_of_strictConvexOn_Ici hconv hc
  simpa [tiltBracket] using hpos

theorem tiltBracket_neg_of_neg_one_lt {δ c : ℝ} (hδ0 : -1 < δ) (hδ1 : δ < 0) (hc : 1 < c) :
    tiltBracket δ c < 0 := by
  have hp0 : 0 < -δ := by linarith
  have hp1 : -δ < 1 := by linarith
  have hconc : StrictConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ (-δ)) :=
    Real.strictConcaveOn_rpow hp0 hp1
  have hneg := centeredSecond_neg_of_strictConcaveOn_Ici hconc hc
  simpa [tiltBracket] using hneg

/-- For `p < 0`, `x ↦ x ^ p` is strictly convex on `(0, ∞)`.
    Proof: second derivative is `p(p-1)x^{p-2} > 0` since both `p` and `p-1` are negative. -/
theorem strictConvexOn_rpow_of_neg {p : ℝ} (hp : p < 0) :
    StrictConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x ^ p) := by
  apply strictConvexOn_of_deriv2_pos (convex_Ioi 0)
  · exact fun x hx =>
      (Real.continuousAt_rpow_const x p (Or.inl (ne_of_gt hx))).continuousWithinAt
  intro x hx
  rw [interior_Ioi, Set.mem_Ioi] at hx
  simp only [Real.iter_deriv_rpow_const]
  apply mul_pos
  · -- (descPochhammer ℝ 2).eval p > 0, i.e., p * (p - 1) > 0
    have : (descPochhammer ℝ 2).eval p = p * (p - 1) := by
      simp [descPochhammer, Polynomial.eval_mul, Polynomial.eval_sub]
    rw [this]
    exact mul_pos_of_neg_of_neg hp (by linarith)
  · exact Real.rpow_pos_of_pos hx _

/-- For `δ > 0` (real), the tilt bracket is strictly positive for `c > 1`.
    This is the continuous-δ generalization of `tiltBracket_pos_of_nat`. -/
theorem tiltBracket_pos_of_pos {δ c : ℝ} (hδ : 0 < δ) (hc : 1 < c) :
    0 < tiltBracket δ c := by
  have hp : -δ < 0 := by linarith
  have hconv := strictConvexOn_rpow_of_neg hp
  have hpos := centeredSecond_pos_of_strictConvexOn_Ioi hconv hc
  simpa [tiltBracket] using hpos

theorem tiltBracket_pos_of_nat {n : ℕ} (hn : 0 < n) {c : ℝ} (hc : 1 < c) :
    0 < tiltBracket (n : ℝ) c := by
  have hconv : StrictConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x ^ (-(n : ℤ))) := by
    exact strictConvexOn_zpow (by omega) (by omega)
  have hpos : 0 < (c - 1) ^ (-(n : ℤ)) + (c + 1) ^ (-(n : ℤ)) - 2 * c ^ (-(n : ℤ)) := by
    exact centeredSecond_pos_of_strictConvexOn_Ioi hconv hc
  have hrewrite :
      tiltBracket (n : ℝ) c =
        (c - 1) ^ (-(n : ℤ)) + (c + 1) ^ (-(n : ℤ)) - 2 * c ^ (-(n : ℤ)) := by
    simp [tiltBracket, Real.rpow_neg_natCast]
  rw [hrewrite]
  exact hpos

/--
Full sign-definiteness package for the tilt bracket.

For `c > 1`, the tilt bracket `Δ²[x^{-δ}](c)` has a definite sign
determined by the regime of `δ`:
- `δ > 0`: positive  (strict convexity of `x^{-δ}` for negative exponent)
- `δ = 0`: zero      (annihilation)
- `-1 < δ < 0`: negative (strict concavity of `x^{-δ}` for `0 < -δ < 1`)
- `δ = -1`: zero     (affine function)
- `δ < -1`: positive (strict convexity of `x^{-δ}` for `-δ > 1`)
-/
theorem tiltBracket_sign_definiteness {δ c : ℝ} (hc : 1 < c) :
    (0 < δ → 0 < tiltBracket δ c) ∧
    (δ = 0 → tiltBracket δ c = 0) ∧
    (-1 < δ → δ < 0 → tiltBracket δ c < 0) ∧
    (δ = -1 → tiltBracket δ c = 0) ∧
    (δ < -1 → 0 < tiltBracket δ c) := by
  exact ⟨fun hδ => tiltBracket_pos_of_pos hδ hc,
         fun hEq => by simp [hEq],
         fun hgt hlt => tiltBracket_neg_of_neg_one_lt hgt hlt hc,
         fun hEq => by simp [hEq],
         fun hlt => tiltBracket_pos_of_lt_neg_one hlt hc⟩

/-- Backward-compatible alias for the nonpositive regime. -/
theorem tiltBracket_sign_definiteness_nonpos {δ c : ℝ} (hc : 1 < c) :
    (δ < -1 → 0 < tiltBracket δ c) ∧
    (δ = -1 → tiltBracket δ c = 0) ∧
    (-1 < δ → δ < 0 → tiltBracket δ c < 0) ∧
    (δ = 0 → tiltBracket δ c = 0) := by
  obtain ⟨hpos, hzero, hneg, hm1, hltm1⟩ := tiltBracket_sign_definiteness hc
  exact ⟨hltm1, hm1, hneg, hzero⟩

/-- Rota K Thm 2 (core direction): at `δ = 0`, tilt is annihilated for every center. -/
theorem routeK_thm2_tilt_annihilation (c : ℝ) :
    tiltBracket 0 c = 0 := by
  exact tiltBracket_zero c

/-- Rota K Thm 5 (formalized nonpositive regime package). -/
theorem routeK_thm5_sign_nonpos {δ c : ℝ} (hc : 1 < c) :
    (δ < -1 → 0 < tiltBracket δ c) ∧
    (δ = -1 → tiltBracket δ c = 0) ∧
    (-1 < δ → δ < 0 → tiltBracket δ c < 0) ∧
    (δ = 0 → tiltBracket δ c = 0) := by
  exact tiltBracket_sign_definiteness_nonpos hc

/-- Rota K Thm 5 (positive real δ): bracket is positive for all `δ > 0`. -/
theorem routeK_thm5_sign_pos {δ : ℝ} (hδ : 0 < δ) {c : ℝ} (hc : 1 < c) :
    0 < tiltBracket δ c := by
  exact tiltBracket_pos_of_pos hδ hc

/-- Rota K Thm 5 (positive natural-exponent slice): `δ = n > 0` gives positive tilt bracket. -/
theorem routeK_thm5_sign_nat_pos {n : ℕ} (hn : 0 < n) {c : ℝ} (hc : 1 < c) :
    0 < tiltBracket (n : ℝ) c := by
  exact tiltBracket_pos_of_nat hn hc

/--
Rota K Thm 5 complete sign bundle:
positive for `δ > 0` (real), zero at `δ = 0` and `δ = -1`,
negative for `-1 < δ < 0`, positive for `δ < -1`.
-/
theorem routeK_thm5_sign_bundle {c : ℝ} (hc : 1 < c) :
    (∀ δ : ℝ, 0 < δ → 0 < tiltBracket δ c) ∧
    (∀ δ : ℝ, δ = 0 → tiltBracket δ c = 0) ∧
    (∀ δ : ℝ, -1 < δ → δ < 0 → tiltBracket δ c < 0) ∧
    (∀ δ : ℝ, δ = -1 → tiltBracket δ c = 0) ∧
    (∀ δ : ℝ, δ < -1 → 0 < tiltBracket δ c) := by
  exact ⟨fun δ hδ => tiltBracket_pos_of_pos hδ hc,
         fun δ hδ => by simp [hδ],
         fun δ hδ0 hδ1 => tiltBracket_neg_of_neg_one_lt hδ0 hδ1 hc,
         fun δ hδ => by simp [hδ],
         fun δ hδ => tiltBracket_pos_of_lt_neg_one hδ hc⟩

/--
Abstract Leibniz collapse at order `m`.

Interpret `c j` and `z j` as the `j`-th coefficients/derivatives at a point.
If all `z k` vanish for `k < m`, then only the `j = 0` Leibniz term survives.
-/
theorem leibnizCollapseByMultiplicity (m : ℕ) (c z : ℕ → ℂ)
    (hz : ∀ k < m, z k = 0) :
    Finset.sum (Finset.range (m + 1)) (fun j => (Nat.choose m j : ℂ) * c j * z (m - j)) =
      c 0 * z m := by
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hjmem hj0
    have hjlt : j < m + 1 := Finset.mem_range.mp hjmem
    have hjle : j ≤ m := Nat.lt_succ_iff.mp hjlt
    have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hmpos : 0 < m := lt_of_lt_of_le hjpos hjle
    have hmjlt : m - j < m := Nat.sub_lt hmpos hjpos
    have hzj : z (m - j) = 0 := hz (m - j) hmjlt
    simp [hzj]
  · intro h0
    simp at h0

/--
Non-degeneracy corollary for the collapsed Leibniz expression:
if `c 0 ≠ 0` and the first nonzero term of `z` is at order `m`,
then the order-`m` Leibniz sum is nonzero.
-/
theorem leibnizNondegenerateByMultiplicity (m : ℕ) (c z : ℕ → ℂ)
    (hz : ∀ k < m, z k = 0) (hc0 : c 0 ≠ 0) (hzm : z m ≠ 0) :
  Finset.sum (Finset.range (m + 1)) (fun j => (Nat.choose m j : ℂ) * c j * z (m - j)) ≠ 0 := by
  rw [leibnizCollapseByMultiplicity m c z hz]
  exact mul_ne_zero hc0 hzm

/--
Abstract Thm-8 wrapper (transversality/non-degeneracy):
the order-`m` Leibniz jet is nonzero when `z` has multiplicity `m` and `c 0 ≠ 0`.
-/
theorem transversalJet_nonzero_of_multiplicity (m : ℕ) (c z : ℕ → ℂ)
    (hz : ∀ k < m, z k = 0) (hc0 : c 0 ≠ 0) (hzm : z m ≠ 0) :
    Finset.sum (Finset.range (m + 1)) (fun j => (Nat.choose m j : ℂ) * c j * z (m - j)) ≠ 0 := by
  exact leibnizNondegenerateByMultiplicity m c z hz hc0 hzm

/-- Rota K (Thm 8 abstract form): multiplicity collapse yields transversal non-degeneracy. -/
theorem routeK_thm8_transversal_abstract (m : ℕ) (c z : ℕ → ℂ)
    (hz : ∀ k < m, z k = 0) (hc0 : c 0 ≠ 0) (hzm : z m ≠ 0) :
    Finset.sum (Finset.range (m + 1)) (fun j => (Nat.choose m j : ℂ) * c j * z (m - j)) ≠ 0 := by
  exact transversalJet_nonzero_of_multiplicity m c z hz hc0 hzm

/--
Rota K chain (Thm 14 -> Thm 8, abstract):
if `c 0` is identified with `c0Complex s` and `Re(s)>0`, transversality follows.
-/
theorem routeK_chain_thm14_to_thm8_abstract {s : ℂ} (hs : 0 < s.re)
    (m : ℕ) (c z : ℕ → ℂ)
    (hz : ∀ k < m, z k = 0) (hcId : c 0 = c0Complex s) (hzm : z m ≠ 0) :
    Finset.sum (Finset.range (m + 1)) (fun j => (Nat.choose m j : ℂ) * c j * z (m - j)) ≠ 0 := by
  have hc0s : c0Complex s ≠ 0 := routeK_thm14_c0_nonvanishing_halfplane hs
  have hc0 : c 0 ≠ 0 := by
    intro hc
    apply hc0s
    simpa [hcId] using hc
  exact routeK_thm8_transversal_abstract m c z hz hc0 hzm

/-- Critical-line specialization of `routeK_chain_thm14_to_thm8_abstract`. -/
theorem routeK_chain_thm14_to_thm8_critical (t : ℝ)
    (m : ℕ) (c z : ℕ → ℂ)
    (hz : ∀ k < m, z k = 0)
    (hcId : c 0 = c0Complex (((1 : ℂ) / 2) + t * Complex.I))
    (hzm : z m ≠ 0) :
    Finset.sum (Finset.range (m + 1)) (fun j => (Nat.choose m j : ℂ) * c j * z (m - j)) ≠ 0 := by
  have hs : 0 < ((((1 : ℂ) / 2) + t * Complex.I)).re := by
    simp
  exact routeK_chain_thm14_to_thm8_abstract hs m c z hz hcId hzm

/--
Rota K Thm-8 concrete bridge (jet form): if `Fjet` is the Leibniz jet of `F = c0 * z`, then
Thm-14 non-vanishing of `c0` and multiplicity assumptions force `Fjet ≠ 0`.
-/
theorem routeK_thm8_transversal_product_jet {s : ℂ} (hs : 0 < s.re)
    (m : ℕ) (cJet zJet : ℕ → ℂ) (Fjet : ℂ)
    (hz : ∀ k < m, zJet k = 0)
    (hcId : cJet 0 = c0Complex s)
    (hzm : zJet m ≠ 0)
    (hLeibniz :
      Fjet = Finset.sum (Finset.range (m + 1))
        (fun j => (Nat.choose m j : ℂ) * cJet j * zJet (m - j))) :
    Fjet ≠ 0 := by
  intro hF0
  have hsum0 :
      Finset.sum (Finset.range (m + 1))
        (fun j => (Nat.choose m j : ℂ) * cJet j * zJet (m - j)) = 0 := by
    simpa [hLeibniz] using hF0
  have hsumNe :
      Finset.sum (Finset.range (m + 1))
        (fun j => (Nat.choose m j : ℂ) * cJet j * zJet (m - j)) ≠ 0 :=
    routeK_chain_thm14_to_thm8_abstract hs m cJet zJet hz hcId hzm
  exact hsumNe hsum0

/-- Critical-line specialization of `routeK_thm8_transversal_product_jet`. -/
theorem routeK_thm8_transversal_product_jet_critical (t : ℝ)
    (m : ℕ) (cJet zJet : ℕ → ℂ) (Fjet : ℂ)
    (hz : ∀ k < m, zJet k = 0)
    (hcId : cJet 0 = c0Complex (((1 : ℂ) / 2) + t * Complex.I))
    (hzm : zJet m ≠ 0)
    (hLeibniz :
      Fjet = Finset.sum (Finset.range (m + 1))
        (fun j => (Nat.choose m j : ℂ) * cJet j * zJet (m - j))) :
    Fjet ≠ 0 := by
  have hs : 0 < ((((1 : ℂ) / 2) + t * Complex.I)).re := by
    simp
  exact routeK_thm8_transversal_product_jet hs m cJet zJet Fjet hz hcId hzm hLeibniz

/-- Literal Leibniz collapse for repeated `σ`-derivatives. -/
theorem iteratedDeriv_mul_collapse_of_multiplicity
    {f g : ℝ → ℂ} {σ : ℝ} (m : ℕ)
    (hf : ContDiffAt ℝ m f σ) (hg : ContDiffAt ℝ m g σ)
    (hz : ∀ k < m, iteratedDeriv k g σ = 0) :
    iteratedDeriv m (fun u : ℝ => f u * g u) σ = f σ * iteratedDeriv m g σ := by
  calc
    iteratedDeriv m (fun u : ℝ => f u * g u) σ =
        Finset.sum (Finset.range (m + 1))
          (fun j => (Nat.choose m j : ℂ) * iteratedDeriv j f σ * iteratedDeriv (m - j) g σ) := by
      simpa using (iteratedDeriv_fun_mul (n := m) (x := σ) hf hg)
    _ = f σ * iteratedDeriv m g σ := by
      simpa using
        leibnizCollapseByMultiplicity m
          (fun j => iteratedDeriv j f σ)
          (fun j => iteratedDeriv j g σ)
          hz

/-- Non-degeneracy of the repeated-derivative Leibniz collapse. -/
theorem iteratedDeriv_mul_nonzero_of_multiplicity
    {f g : ℝ → ℂ} {σ : ℝ} (m : ℕ)
    (hf : ContDiffAt ℝ m f σ) (hg : ContDiffAt ℝ m g σ)
    (hz : ∀ k < m, iteratedDeriv k g σ = 0)
    (hf0 : f σ ≠ 0) (hgm : iteratedDeriv m g σ ≠ 0) :
    iteratedDeriv m (fun u : ℝ => f u * g u) σ ≠ 0 := by
  have hcollapse :=
    iteratedDeriv_mul_collapse_of_multiplicity (m := m) (σ := σ) hf hg hz
  rw [hcollapse]
  exact mul_ne_zero hf0 hgm

/-- Thm 8 in literal `σ`-derivative form along a horizontal line. -/
theorem routeK_thm8_transversal_sigma_product {σ t : ℝ} (hσ : 0 < σ)
    (m : ℕ) {cLine ζLine : ℝ → ℂ}
    (hcLine : ContDiffAt ℝ m cLine σ)
    (hcId : cLine σ = c0Complex ((σ : ℂ) + t * Complex.I))
    (hzLine : ContDiffAt ℝ m ζLine σ)
    (hz : ∀ k < m, iteratedDeriv k ζLine σ = 0)
    (hzm : iteratedDeriv m ζLine σ ≠ 0) :
    iteratedDeriv m
        (fun u : ℝ => cLine u * ζLine u) σ =
          c0Complex ((σ : ℂ) + t * Complex.I) * iteratedDeriv m ζLine σ ∧
      iteratedDeriv m
        (fun u : ℝ => cLine u * ζLine u) σ ≠ 0 := by
  have hcollapse :=
    iteratedDeriv_mul_collapse_of_multiplicity (m := m) (σ := σ) hcLine hzLine hz
  refine ⟨?_, ?_⟩
  · calc
      iteratedDeriv m (fun u : ℝ => cLine u * ζLine u) σ = cLine σ * iteratedDeriv m ζLine σ :=
        hcollapse
      _ = c0Complex ((σ : ℂ) + t * Complex.I) * iteratedDeriv m ζLine σ := by
        rw [hcId]
  · rw [hcollapse, hcId]
    have hs : 0 < (((σ : ℂ) + t * Complex.I)).re := by
      simpa using hσ
    exact mul_ne_zero (c0Complex_ne_zero_of_re_pos hs) hzm

/-- Thm 8 transported to any local identity `F = c0 * ζ` near `σ`. -/
theorem routeK_thm8_transversal_sigma_identity {σ t : ℝ} (hσ : 0 < σ)
    (m : ℕ) {FLine cLine ζLine : ℝ → ℂ}
    (hEq : FLine =ᶠ[𝓝 σ] fun u : ℝ => cLine u * ζLine u)
    (hcLine : ContDiffAt ℝ m cLine σ)
    (hcId : cLine σ = c0Complex ((σ : ℂ) + t * Complex.I))
    (hzLine : ContDiffAt ℝ m ζLine σ)
    (hz : ∀ k < m, iteratedDeriv k ζLine σ = 0)
    (hzm : iteratedDeriv m ζLine σ ≠ 0) :
    iteratedDeriv m FLine σ =
        c0Complex ((σ : ℂ) + t * Complex.I) * iteratedDeriv m ζLine σ ∧
      iteratedDeriv m FLine σ ≠ 0 := by
  have hprod := routeK_thm8_transversal_sigma_product
    (σ := σ) (t := t) hσ m hcLine hcId hzLine hz hzm
  have hIter :
      iteratedDeriv m FLine σ =
        iteratedDeriv m (fun u : ℝ => cLine u * ζLine u) σ := by
    rw [Filter.EventuallyEq.iteratedDeriv_eq m hEq]
  refine ⟨hIter.trans hprod.1, ?_⟩
  intro hzero
  have hzero' :
      iteratedDeriv m (fun u : ℝ => cLine u * ζLine u) σ = 0 := by
    simpa [hIter] using hzero
  exact hprod.2 hzero'

/-- Pointwise half-plane identity implies the local `σ`-derivative version of Thm 8. -/
theorem routeK_thm8_transversal_sigma_identity_of_pos {σ t : ℝ} (hσ : 0 < σ)
    (m : ℕ) {FLine cLine ζLine : ℝ → ℂ}
    (hEq : ∀ u > 0, FLine u = cLine u * ζLine u)
    (hcLine : ContDiffAt ℝ m cLine σ)
    (hcId : cLine σ = c0Complex ((σ : ℂ) + t * Complex.I))
    (hzLine : ContDiffAt ℝ m ζLine σ)
    (hz : ∀ k < m, iteratedDeriv k ζLine σ = 0)
    (hzm : iteratedDeriv m ζLine σ ≠ 0) :
    iteratedDeriv m FLine σ =
        c0Complex ((σ : ℂ) + t * Complex.I) * iteratedDeriv m ζLine σ ∧
      iteratedDeriv m FLine σ ≠ 0 := by
  have hEvent : FLine =ᶠ[𝓝 σ] fun u : ℝ => cLine u * ζLine u := by
    filter_upwards [isOpen_Ioi.mem_nhds hσ] with u hu
    exact hEq u hu
  exact routeK_thm8_transversal_sigma_identity
    (σ := σ) (t := t) hσ m hEvent hcLine hcId hzLine hz hzm

/-- Critical-line specialization of `routeK_thm8_transversal_sigma_product`. -/
theorem routeK_thm8_transversal_sigma_product_critical (t : ℝ)
    (m : ℕ) {cLine ζLine : ℝ → ℂ}
    (hcLine : ContDiffAt ℝ m cLine ((1 : ℝ) / 2))
  (hcId : cLine ((1 : ℝ) / 2) = c0Complex (((((1 : ℝ) / 2) : ℂ) + t * Complex.I)))
    (hzLine : ContDiffAt ℝ m ζLine ((1 : ℝ) / 2))
    (hz : ∀ k < m, iteratedDeriv k ζLine ((1 : ℝ) / 2) = 0)
    (hzm : iteratedDeriv m ζLine ((1 : ℝ) / 2) ≠ 0) :
    iteratedDeriv m
        (fun u : ℝ => cLine u * ζLine u) ((1 : ℝ) / 2) =
          c0Complex (((((1 : ℝ) / 2) : ℂ) + t * Complex.I)) * iteratedDeriv m ζLine ((1 : ℝ) / 2) ∧
      iteratedDeriv m
        (fun u : ℝ => cLine u * ζLine u) ((1 : ℝ) / 2) ≠ 0 := by
  simpa using
    routeK_thm8_transversal_sigma_product
      (σ := (1 : ℝ) / 2) (t := t) (by norm_num) m hcLine (by simpa using hcId) hzLine hz hzm

/-- Critical-line specialization of `routeK_thm8_transversal_sigma_identity_of_pos`. -/
theorem routeK_thm8_transversal_sigma_identity_critical (t : ℝ)
    (m : ℕ) {FLine cLine ζLine : ℝ → ℂ}
    (hEq : ∀ u > 0, FLine u = cLine u * ζLine u)
    (hcLine : ContDiffAt ℝ m cLine ((1 : ℝ) / 2))
  (hcId : cLine ((1 : ℝ) / 2) = c0Complex (((((1 : ℝ) / 2) : ℂ) + t * Complex.I)))
    (hzLine : ContDiffAt ℝ m ζLine ((1 : ℝ) / 2))
    (hz : ∀ k < m, iteratedDeriv k ζLine ((1 : ℝ) / 2) = 0)
    (hzm : iteratedDeriv m ζLine ((1 : ℝ) / 2) ≠ 0) :
    iteratedDeriv m FLine ((1 : ℝ) / 2) =
      c0Complex (((((1 : ℝ) / 2) : ℂ) + t * Complex.I)) * iteratedDeriv m ζLine ((1 : ℝ) / 2) ∧
      iteratedDeriv m FLine ((1 : ℝ) / 2) ≠ 0 := by
  simpa using
    routeK_thm8_transversal_sigma_identity_of_pos
      (σ := (1 : ℝ) / 2) (t := t) (by norm_num) m hEq hcLine (by simpa using hcId) hzLine hz hzm

/-- Integer-indexed tilt profile (absolute value model). -/
noncomputable def tiltProfile (δ : ℝ) (n : ℤ) : ℝ :=
  Real.rpow (Int.natAbs n : ℝ) (-δ)

@[simp] theorem tiltProfile_zero (n : ℤ) : tiltProfile 0 n = 1 := by
  simp [tiltProfile]

@[simp] theorem centeredBracket_tilt_zero (c : ℤ) :
    centeredBracket (tiltProfile 0) c = 0 := by
  simp [centeredBracket]
  ring

end LeanC2
