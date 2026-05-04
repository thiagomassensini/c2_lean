import Mathlib
import LeanC2.Foundations.Basic
import LeanC2.Glue.Decomposition
import LeanC2.Operators.BranchToGenuine
import LeanC2.Operators.Genuine

namespace LeanC2

open scoped BigOperators

/-- Positive cutoff scale attached to the natural parameter `X`. -/
def cutoffScale (X : Nat) : Real :=
  X + 1

/-- Depth parameter used by the canonical finite cutoff family. -/
def cutoffDepth (X : Nat) : Nat :=
  X + 2

/-- Finite odd-core window used by the canonical finite cutoff family. -/
def cutoffCoreWindow (X : Nat) : Finset Nat :=
  Finset.range (X + 1)

/-- Sharp finite direct cutoff channel obtained by truncating the depth and odd-core windows. -/
noncomputable def sharpCutoffD (X : Nat) (s : Complex) : Complex :=
  ∑ m ∈ cutoffCoreWindow X, partialDCore s (cutoffDepth X) m

/-- Finite bracket cutoff channel obtained by truncating both the depth and the odd-core windows. -/
noncomputable def canonicalCutoffB (X : Nat) (s : Complex) : Complex :=
  ∑ m ∈ cutoffCoreWindow X, partialBCore s (cutoffDepth X) m

/-- Smooth leg cutoff weight `e^{-n/(X+1)}`. -/
noncomputable def cutoffWeight (X n : Nat) : Real :=
  Real.exp (-((n : Real) / cutoffScale X))

/-- Residual cutoff defect `g_X(n) = e^{-n/(X+1)} - 1`. -/
noncomputable def cutoffDefectWeight (X n : Nat) : Real :=
  cutoffWeight X n - 1

/-- One leg weighted by the smooth cutoff. -/
noncomputable def smoothCutoffLegTerm
    (X : Nat) (s : Complex) (k m : Nat) (epsilon : BranchSign) : Complex :=
  (((cutoffWeight X (natDescendant k epsilon (oddCore m)) : Real) : Complex)) *
    legTerm s k m epsilon

/-- Finite smooth-cutoff direct channel on one odd core. -/
noncomputable def smoothCutoffDCore (X : Nat) (s : Complex) (K m : Nat) : Complex :=
  ∑ k ∈ depthWindow K,
    (smoothCutoffLegTerm X s k m BranchSign.minus +
      smoothCutoffLegTerm X s k m BranchSign.plus)

/-- Finite smooth-cutoff direct channel on the first `M` odd cores. -/
noncomputable def smoothCutoffDFinite (X : Nat) (s : Complex) (K M : Nat) : Complex :=
  ∑ m ∈ Finset.range M, smoothCutoffDCore X s K m

/-- Canonical finite direct channel using the smooth cutoff on the direct side. -/
noncomputable def canonicalCutoffD (X : Nat) (s : Complex) : Complex :=
  smoothCutoffDFinite X s (cutoffDepth X) (X + 1)

/-- Sharp finite cutoff numerator mirroring the old truncation model `D_X - B_X`. -/
noncomputable def sharpCutoffFamily (X : Nat) (s : Complex) : Complex :=
  sharpCutoffD X s - canonicalCutoffB X s

/-- Canonical finite cutoff numerator: smooth direct channel minus truncated bracket channel. -/
noncomputable def canonicalCutoffFamily (X : Nat) (s : Complex) : Complex :=
  canonicalCutoffD X s - canonicalCutoffB X s

lemma cutoffScale_pos (X : Nat) : 0 < cutoffScale X := by
  unfold cutoffScale
  positivity

lemma natCast_mem_slitPlane_of_pos {n : Nat} (hn : 0 < n) :
    ((n : Complex) ∈ Complex.slitPlane) := by
  simpa using (Complex.ofReal_mem_slitPlane.2 (show (0 : ℝ) < n by exact_mod_cast hn))

lemma natCpowNeg_analyticOnNhd {n : Nat} (hn : 0 < n) :
    AnalyticOnNhd ℂ (fun s : Complex => ((n : Complex) ^ (-s))) offCriticalStripSet := by
  intro s hs
  have hBase : (n : Complex) ∈ Complex.slitPlane := natCast_mem_slitPlane_of_pos hn
  simpa using
    (AnalyticAt.cpow
      (f := fun _ : Complex => (n : Complex))
      (g := fun z : Complex => -z)
      analyticAt_const analyticAt_id.neg hBase)

lemma natDescendant_oddCore_pos (k m : Nat) (epsilon : BranchSign) (hk : 2 ≤ k) :
    0 < natDescendant k epsilon (oddCore m) := by
  obtain ⟨depth, rfl⟩ := Nat.exists_eq_add_of_le hk
  cases epsilon <;> unfold natDescendant oddCore
  · have hpow : 4 ≤ 2 ^ depth * 4 := by
      calc
        4 = 1 * 4 := by norm_num
        _ ≤ 2 ^ depth * 4 := by
          gcongr
          exact Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) depth)
    have hlt : 1 < (2 ^ depth * 4) * (2 * m + 1) := by
      have hmul : 4 ≤ (2 ^ depth * 4) * (2 * m + 1) := by
        calc
          4 ≤ (2 ^ depth * 4) * 1 := by simpa using hpow
          _ ≤ (2 ^ depth * 4) * (2 * m + 1) := by
            gcongr
            omega
      exact lt_of_lt_of_le (by norm_num : 1 < 4) hmul
    simpa [pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (Nat.sub_pos_of_lt hlt)
  · exact Nat.succ_pos _

lemma legTerm_analyticOnNhd {k m : Nat} {epsilon : BranchSign} (hk : 2 ≤ k) :
    AnalyticOnNhd ℂ (fun s : Complex => legTerm s k m epsilon) offCriticalStripSet := by
  have hPow :
      AnalyticOnNhd ℂ
        (fun s : Complex =>
          (((natDescendant k epsilon (oddCore m) : Nat) : Complex) ^ (-s)))
        offCriticalStripSet :=
    natCpowNeg_analyticOnNhd (natDescendant_oddCore_pos k m epsilon hk)
  simpa [legTerm] using (analyticOnNhd_const.mul hPow)

lemma legPairTerm_analyticOnNhd {k m : Nat} (hk : 2 ≤ k) :
    AnalyticOnNhd ℂ (fun s : Complex => legPairTerm s k m) offCriticalStripSet := by
  simpa [legPairTerm] using
    (legTerm_analyticOnNhd (k := k) (m := m) (epsilon := BranchSign.minus) hk).add
      (legTerm_analyticOnNhd (k := k) (m := m) (epsilon := BranchSign.plus) hk)

lemma centerTerm_analyticOnNhd (k m : Nat) :
    AnalyticOnNhd ℂ (fun s : Complex => centerTerm s k m) offCriticalStripSet := by
  have hPow :
      AnalyticOnNhd ℂ
        (fun s : Complex => (((centerNat k m : Nat) : Complex) ^ (-s)))
        offCriticalStripSet :=
    natCpowNeg_analyticOnNhd (centerNat_pos k m)
  simpa [centerTerm] using (analyticOnNhd_const.mul hPow)

lemma bracketTerm_analyticOnNhd {k m : Nat} (hk : 2 ≤ k) :
    AnalyticOnNhd ℂ (fun s : Complex => bracketTerm s k m) offCriticalStripSet := by
  have hPair : AnalyticOnNhd ℂ (fun s : Complex => legPairTerm s k m) offCriticalStripSet :=
    legPairTerm_analyticOnNhd (k := k) (m := m) hk
  have hCenter : AnalyticOnNhd ℂ (fun s : Complex => centerTerm s k m) offCriticalStripSet :=
    centerTerm_analyticOnNhd k m
  have hSub :
      AnalyticOnNhd ℂ (fun s : Complex => legPairTerm s k m - centerTerm s k m)
        offCriticalStripSet :=
    hPair.sub hCenter
  convert hSub using 1
  ext s
  symm
  exact sub_eq_iff_eq_add.mpr (legPair_eq_bracket_add_centerTerm s k m)

lemma partialDCore_analyticOnNhd (K m : Nat) :
    AnalyticOnNhd ℂ (fun s : Complex => partialDCore s K m) offCriticalStripSet := by
  unfold partialDCore
  exact (depthWindow K).analyticOnNhd_fun_sum fun k hk =>
    legPairTerm_analyticOnNhd (k := k) (m := m) (Finset.mem_Icc.mp hk).1

lemma smoothCutoffLegTerm_analyticOnNhd
    {X k m : Nat} {epsilon : BranchSign} (hk : 2 ≤ k) :
    AnalyticOnNhd ℂ (fun s : Complex => smoothCutoffLegTerm X s k m epsilon)
      offCriticalStripSet := by
  simpa [smoothCutoffLegTerm] using
    (analyticOnNhd_const.mul (legTerm_analyticOnNhd (k := k) (m := m) (epsilon := epsilon) hk))

lemma smoothCutoffDCore_analyticOnNhd (X K m : Nat) :
    AnalyticOnNhd ℂ (fun s : Complex => smoothCutoffDCore X s K m) offCriticalStripSet := by
  unfold smoothCutoffDCore
  exact (depthWindow K).analyticOnNhd_fun_sum fun k hk => by
    simpa using
      (smoothCutoffLegTerm_analyticOnNhd (X := X) (k := k) (m := m)
        (epsilon := BranchSign.minus) (Finset.mem_Icc.mp hk).1).add
        (smoothCutoffLegTerm_analyticOnNhd (X := X) (k := k) (m := m)
          (epsilon := BranchSign.plus) (Finset.mem_Icc.mp hk).1)

lemma partialBCore_analyticOnNhd (K m : Nat) :
    AnalyticOnNhd ℂ (fun s : Complex => partialBCore s K m) offCriticalStripSet := by
  unfold partialBCore
  exact (depthWindow K).analyticOnNhd_fun_sum fun k hk =>
    bracketTerm_analyticOnNhd (k := k) (m := m) (Finset.mem_Icc.mp hk).1

lemma sharpCutoffD_analyticOnNhd (X : Nat) :
    AnalyticOnNhd ℂ (sharpCutoffD X) offCriticalStripSet := by
  unfold sharpCutoffD
  exact (cutoffCoreWindow X).analyticOnNhd_fun_sum fun m hm =>
    partialDCore_analyticOnNhd (cutoffDepth X) m

lemma canonicalCutoffD_analyticOnNhd (X : Nat) :
    AnalyticOnNhd ℂ (canonicalCutoffD X) offCriticalStripSet := by
  unfold canonicalCutoffD
  exact (cutoffCoreWindow X).analyticOnNhd_fun_sum fun m hm =>
    smoothCutoffDCore_analyticOnNhd X (cutoffDepth X) m

lemma canonicalCutoffB_analyticOnNhd (X : Nat) :
    AnalyticOnNhd ℂ (canonicalCutoffB X) offCriticalStripSet := by
  unfold canonicalCutoffB
  exact (cutoffCoreWindow X).analyticOnNhd_fun_sum fun m hm =>
    partialBCore_analyticOnNhd (cutoffDepth X) m

theorem canonicalCutoffFamily_analyticOnOffCriticalStrip :
    ∀ X : Nat, AnalyticOnNhd ℂ (canonicalCutoffFamily X) offCriticalStripSet := by
  intro X
  simpa [canonicalCutoffFamily] using
    (canonicalCutoffD_analyticOnNhd X).sub (canonicalCutoffB_analyticOnNhd X)

/-!
Scaffold for the finite-cutoff channels `D_X`, `B_X`, and `F_X`.

Primary sources:
- docs/c2_cutoff_adaptativo_quarteto.md
- docs/nota_cutoff_c2.md

Legacy seeds:
- Lean/Antigo_Lean_C2/CutoffDecay.lean
- Lean/Antigo_Lean_C2/Composite.lean

This file now materializes the canonical finite cutoff family with a smooth direct-side cutoff and a
truncated bracket-side channel. The previous sharp direct truncation remains available explicitly as
`sharpCutoffD`/`sharpCutoffFamily`, so the residual layer can compare the smooth canonical family to
the old finite scaffold without changing downstream APIs.
-/

end LeanC2
