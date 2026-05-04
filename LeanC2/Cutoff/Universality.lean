import Mathlib
import LeanC2.Cutoff.Residue
import LeanC2.Glue.Decomposition

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

/-- Local-uniform vanishing of a residual family on the off-critical strip. -/
def cutoffResidualVanishesLocallyUniformlyOnOffCriticalStrip
    (RX : Nat -> Complex -> Complex) : Prop :=
  cutoffConvergesLocallyUniformlyOnOffCriticalStrip RX (fun _ : Complex => 0)

/-- Uniform `O((X+1)⁻¹)` control of a residual family on compact off-strip sets. -/
def cutoffResidualIsOInvLocallyUniformlyOnOffCriticalStrip
    (RX : Nat -> Complex -> Complex) : Prop :=
  ∀ K : Set Complex, IsCompact K -> K ⊆ offCriticalStripSet ->
    ∃ C : Real, 0 ≤ C ∧ ∀ X : Nat, ∀ s ∈ K, ‖RX X s‖ ≤ C / cutoffScale X

/-- Uniform compact control of the explicit coefficient that bounds `canonicalCutoffResidual`. -/
def canonicalCutoffResidualCoeffUniformlyBoundedOnOffCriticalStrip : Prop :=
  ∀ K : Set Complex, IsCompact K -> K ⊆ offCriticalStripSet ->
    ∃ C : Real, 0 ≤ C ∧ ∀ X : Nat, ∀ s ∈ K, canonicalCutoffResidualCoeff s X ≤ C

theorem cutoffResidualVanishesLocallyUniformlyOnOffCriticalStrip_of_OInv
    {RX : Nat -> Complex -> Complex}
    (hO : cutoffResidualIsOInvLocallyUniformlyOnOffCriticalStrip RX) :
    cutoffResidualVanishesLocallyUniformlyOnOffCriticalStrip RX := by
  intro K hK hKs
  rcases hO K hK hKs with ⟨C, hCnonneg, hBound⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_cases hC : C = 0
  · refine Filter.Eventually.of_forall ?_
    intro X s hs
    have hNormLe : ‖RX X s‖ ≤ 0 := by simpa [hC] using hBound X s hs
    have hZero : RX X s = 0 := by
      exact norm_eq_zero.mp (le_antisymm hNormLe (norm_nonneg _))
    simpa [hZero]
  · have hC0 : 0 ≠ C := by
      intro hZero
      exact hC hZero.symm
    have hCpos : 0 < C := lt_of_le_of_ne hCnonneg hC0
    obtain ⟨N, hN⟩ : ∃ N : Nat, 1 / cutoffScale N < ε / C := by
      simpa [cutoffScale] using (exists_nat_one_div_lt (K := ℝ) (div_pos hε hCpos))
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro X hX s hs
    have hScale : cutoffScale N ≤ cutoffScale X := by
      unfold cutoffScale
      exact_mod_cast Nat.succ_le_succ hX
    have hInv : 1 / cutoffScale X ≤ 1 / cutoffScale N := by
      exact one_div_le_one_div_of_le (cutoffScale_pos N) hScale
    have hScaled : C / cutoffScale X ≤ C / cutoffScale N := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_left hInv hCnonneg)
    have hMul : C * (cutoffScale N)⁻¹ < C * (ε / C) := by
      simpa [one_div, div_eq_mul_inv, cutoffScale, mul_comm, mul_left_comm, mul_assoc] using
        (mul_lt_mul_of_pos_left hN hCpos)
    have hCN : C / cutoffScale N < ε := by
      rw [div_eq_mul_inv]
      calc
        C * (cutoffScale N)⁻¹ < C * (ε / C) := hMul
        _ = ε := by field_simp [hCpos.ne']
    have hNorm : ‖RX X s‖ < ε := lt_of_le_of_lt (le_trans (hBound X s hs) hScaled) hCN
    simpa [dist_eq_norm, norm_neg] using hNorm

theorem canonicalCutoffResidual_isOInvLocallyUniformlyOnOffCriticalStrip_of_coeffBound
    (hCoeff : canonicalCutoffResidualCoeffUniformlyBoundedOnOffCriticalStrip) :
    cutoffResidualIsOInvLocallyUniformlyOnOffCriticalStrip canonicalCutoffResidual := by
  intro K hK hKs
  rcases hCoeff K hK hKs with ⟨C, hCnonneg, hCoeffBound⟩
  refine ⟨C, hCnonneg, ?_⟩
  intro X s hs
  exact le_trans (norm_canonicalCutoffResidual_le X s)
    (div_le_div_of_nonneg_right (hCoeffBound X s hs) (le_of_lt (cutoffScale_pos X)))

theorem canonicalCutoffResidualVanishesLocallyUniformlyOnOffCriticalStrip_of_coeffBound
    (hCoeff : canonicalCutoffResidualCoeffUniformlyBoundedOnOffCriticalStrip) :
    cutoffResidualVanishesLocallyUniformlyOnOffCriticalStrip canonicalCutoffResidual := by
  exact cutoffResidualVanishesLocallyUniformlyOnOffCriticalStrip_of_OInv
    (canonicalCutoffResidual_isOInvLocallyUniformlyOnOffCriticalStrip_of_coeffBound hCoeff)

theorem canonicalCutoffResidualCoeffUniformlyBoundedOnCompacts_of_re_ge
    {σ0 : Real} (hσ0 : 2 < σ0) :
    ∀ K : Set Complex, IsCompact K -> K ⊆ {s : Complex | σ0 <= s.re} ->
      ∃ C : Real, 0 <= C ∧
        ∀ X : Nat, ∀ s ∈ K, canonicalCutoffResidualCoeff s X <= C := by
  intro K hK hKσ
  rcases canonicalCutoffResidualCoeff_bounded_of_re_ge hσ0 with ⟨C, hCnonneg, hC⟩
  refine ⟨C, hCnonneg, ?_⟩
  intro X s hs
  exact hC X s (hKσ hs)

theorem canonicalCutoffResidualIsOInvOnCompacts_of_re_ge
    {σ0 : Real} (hσ0 : 2 < σ0) :
    ∀ K : Set Complex, IsCompact K -> K ⊆ {s : Complex | σ0 <= s.re} ->
      ∃ C : Real, 0 <= C ∧
        ∀ X : Nat, ∀ s ∈ K, ‖canonicalCutoffResidual X s‖ <= C / cutoffScale X := by
  intro K hK hKσ
  rcases canonicalCutoffResidualCoeffUniformlyBoundedOnCompacts_of_re_ge hσ0 K hK hKσ with
      ⟨C, hCnonneg, hCoeff⟩
  refine ⟨C, hCnonneg, ?_⟩
  intro X s hs
  exact le_trans (norm_canonicalCutoffResidual_le X s)
    (div_le_div_of_nonneg_right (hCoeff X s hs) (le_of_lt (cutoffScale_pos X)))

theorem cutoffConvergesLocallyUniformlyOnOffCriticalStrip_of_add_residual
    {FX GX RX : Nat -> Complex -> Complex} {numFun : Complex -> Complex}
    (hDecomp : ∀ X : Nat, ∀ s : Complex, FX X s = GX X s + RX X s)
    (hConv : cutoffConvergesLocallyUniformlyOnOffCriticalStrip GX numFun)
    (hResidual : cutoffResidualVanishesLocallyUniformlyOnOffCriticalStrip RX) :
    cutoffConvergesLocallyUniformlyOnOffCriticalStrip FX numFun := by
  intro K hK hKs
  have hAdd :
      TendstoUniformlyOn
        ((fun X s => GX X s) + fun X s => RX X s)
        (numFun + fun _ : Complex => 0)
        Filter.atTop K := by
    exact (hConv K hK hKs).add (hResidual K hK hKs)
  have hEq :
      ∀ᶠ X in Filter.atTop, Set.EqOn (fun s => GX X s + RX X s) (fun s => FX X s) K :=
    Filter.Eventually.of_forall fun X s hs => (hDecomp X s).symm
  have hAdd' :
      TendstoUniformlyOn
        (fun X s => GX X s + RX X s)
        (fun s => numFun s + 0)
        Filter.atTop K := by
    exact hAdd.congr (Filter.Eventually.of_forall fun X s hs => rfl)
  exact (hAdd'.congr hEq).congr_right (by
    intro s hs
    simp)

theorem canonicalCutoffFamily_convergesLocallyUniformlyOnOffCriticalStrip_of_sharpCutoffFamily
    {numFun : Complex -> Complex}
    (hSharp :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip sharpCutoffFamily numFun)
    (hResidual :
      cutoffResidualVanishesLocallyUniformlyOnOffCriticalStrip canonicalCutoffResidual) :
    cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun := by
  refine cutoffConvergesLocallyUniformlyOnOffCriticalStrip_of_add_residual ?_ hSharp hResidual
  intro X s
  exact canonicalCutoffFamily_eq_sharpCutoffFamily_add_residual X s

theorem canonicalCutoffFamily_convergesLocallyUniformlyOnOffCriticalStrip_of_sharpCutoffFamily_OInv
    {numFun : Complex -> Complex}
    (hSharp :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip sharpCutoffFamily numFun)
    (hResidual :
      cutoffResidualIsOInvLocallyUniformlyOnOffCriticalStrip canonicalCutoffResidual) :
    cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun := by
  exact canonicalCutoffFamily_convergesLocallyUniformlyOnOffCriticalStrip_of_sharpCutoffFamily
    hSharp
    (cutoffResidualVanishesLocallyUniformlyOnOffCriticalStrip_of_OInv hResidual)

theorem canonicalCutoffFamily_converges_of_sharpCutoffFamily_coeffBound
    {numFun : Complex -> Complex}
    (hSharp :
      cutoffConvergesLocallyUniformlyOnOffCriticalStrip sharpCutoffFamily numFun)
    (hResidual : canonicalCutoffResidualCoeffUniformlyBoundedOnOffCriticalStrip) :
    cutoffConvergesLocallyUniformlyOnOffCriticalStrip canonicalCutoffFamily numFun := by
  exact canonicalCutoffFamily_convergesLocallyUniformlyOnOffCriticalStrip_of_sharpCutoffFamily
    hSharp
    (canonicalCutoffResidualVanishesLocallyUniformlyOnOffCriticalStrip_of_coeffBound hResidual)

/-!
Scaffold for the cutoff universality layer (Thm 3).

Primary sources:
- docs/c2_rota_K_rigorosamente_fechada.md

Legacy seeds:
- Lean/Antigo_Lean_C2/CutoffDecay.lean

The abstract local-uniform convergence predicate now lives here. The canonical
smooth family is now linked formally to the old sharp scaffold: proving
convergence for `sharpCutoffFamily` together with local-uniform vanishing of the
residual already suffices to recover convergence of `canonicalCutoffFamily`.
-/

end

end LeanC2
