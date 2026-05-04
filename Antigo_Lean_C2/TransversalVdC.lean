import Mathlib
import LeanC2.TransversalAnalytic
import LeanC2.VanDerCorput

namespace LeanC2

/-!
# Optional Van der Corput Transversal Layer

This module contains the logarithmic phase-curvature and super-Weyl bridge
wrappers that depend on `VanDerCorput.lean`.  The main Taylor/log² chain lives
in `TransversalAnalytic.lean` and does not import this file.
-/

/--
Native off-axis phase-curvature source obtained by feeding the internal height
`|Im(s)|` into the logarithmic phase from `VanDerCorput.lean`.
-/
def routeK_offAxisPhaseCurvatureAt (s : ℂ) : Prop :=
  ∀ {k m : ℕ}, 2 ≤ m ->
    c2LogPhase (routeK_offAxisHeight s) k (m + 2) -
      2 * c2LogPhase (routeK_offAxisHeight s) k (m + 1) +
      c2LogPhase (routeK_offAxisHeight s) k m ≠ 0

/--
The Van der Corput phase-curvature input becomes an internal theorem at the
point `s` as soon as the attached height `|Im(s)|` is nonzero.
-/
theorem routeK_offAxisPhaseCurvatureAt_of_nonzero_height
    {s : ℂ} (hs : routeK_offAxisHeight s ≠ 0) :
    routeK_offAxisPhaseCurvatureAt s := by
  intro k m hm
  have hm' : 1 ≤ m := le_trans (by omega) hm
  exact routeK_thm7_phase_input (t := routeK_offAxisHeight s) hs hm'

/--
Quantitative phase-curvature datum on a finite Van der Corput window.

This is the explicit lower-bound form needed to instantiate
`VanDerCorputHyp` for the internal logarithmic phase.
-/
def routeK_offAxisPhaseCurvatureWindowAt (s : ℂ) (N : ℕ) (lam : ℝ) : Prop :=
  ∀ {k m : ℕ}, 1 ≤ m → m + 2 ≤ N →
    lam ≤ |c2LogPhase (routeK_offAxisHeight s) k (m + 2) -
      2 * c2LogPhase (routeK_offAxisHeight s) k (m + 1) +
      c2LogPhase (routeK_offAxisHeight s) k m|

/--
Finite collection of explicit logarithmic curvature-kernel values relevant to a
Van der Corput window of length `N`.
-/
noncomputable def routeK_offAxisPhaseCurvatureKernelWindow (N : ℕ) : Finset ℝ := by
  classical
  exact (Finset.Icc 1 (N - 2)).image c2LogPhaseCurvatureKernel

/--
For `N ≥ 3`, the finite curvature-kernel window is nonempty.
-/
theorem routeK_offAxisPhaseCurvatureKernelWindow_nonempty
    {N : ℕ} (hN : 3 ≤ N) :
    (routeK_offAxisPhaseCurvatureKernelWindow N).Nonempty := by
  classical
  have h12 : 1 ≤ N - 2 := by
    omega
  rw [routeK_offAxisPhaseCurvatureKernelWindow]
  refine Finset.Nonempty.image ?_ _
  refine ⟨1, ?_⟩
  simp [Finset.mem_Icc, h12]

/--
Canonical lower bound for the explicit logarithmic curvature kernel on the
window `1 ≤ m ≤ N - 2`.
-/
noncomputable def routeK_offAxisPhaseCurvatureLambdaBase
    (N : ℕ) (hN : 3 ≤ N) : ℝ := by
  classical
  exact (routeK_offAxisPhaseCurvatureKernelWindow N).min'
    (routeK_offAxisPhaseCurvatureKernelWindow_nonempty hN)

/--
The canonical finite-window lower bound for the logarithmic curvature kernel is
strictly positive.
-/
theorem routeK_offAxisPhaseCurvatureLambdaBase_pos
    {N : ℕ} (hN : 3 ≤ N) :
    0 < routeK_offAxisPhaseCurvatureLambdaBase N hN := by
  classical
  have hlt : (0 : ℝ) < (routeK_offAxisPhaseCurvatureKernelWindow N).min'
      (routeK_offAxisPhaseCurvatureKernelWindow_nonempty hN) := by
    rw [Finset.lt_min'_iff]
    intro y hy
    rw [routeK_offAxisPhaseCurvatureKernelWindow] at hy
    rcases Finset.mem_image.mp hy with ⟨m, hm, rfl⟩
    exact c2LogPhaseCurvatureKernel_pos (Finset.mem_Icc.mp hm).1
  simpa [routeK_offAxisPhaseCurvatureLambdaBase] using hlt

/--
The canonical finite-window lower bound is below every kernel value appearing
in the window.
-/
theorem routeK_offAxisPhaseCurvatureLambdaBase_le_kernel
    {N m : ℕ} (hN : 3 ≤ N) (hm : 1 ≤ m) (hNm : m + 2 ≤ N) :
    routeK_offAxisPhaseCurvatureLambdaBase N hN ≤
      c2LogPhaseCurvatureKernel m := by
  classical
  have hmIcc : m ∈ Finset.Icc 1 (N - 2) := by
    have hmUpper : m ≤ N - 2 := by
      omega
    simp [Finset.mem_Icc, hm, hmUpper]
  have hmem : c2LogPhaseCurvatureKernel m ∈
      routeK_offAxisPhaseCurvatureKernelWindow N := by
    rw [routeK_offAxisPhaseCurvatureKernelWindow]
    exact Finset.mem_image.mpr ⟨m, hmIcc, rfl⟩
  simpa [routeK_offAxisPhaseCurvatureLambdaBase]
    using (Finset.min'_le
      (s := routeK_offAxisPhaseCurvatureKernelWindow N)
      (x := c2LogPhaseCurvatureKernel m) hmem)

/--
Canonical quantitative Van der Corput scale attached to the point `s` and the
finite window `N`.
-/
noncomputable def routeK_offAxisPhaseCurvatureLambda
    (s : ℂ) (N : ℕ) (hN : 3 ≤ N) : ℝ :=
  |routeK_offAxisHeight s| * routeK_offAxisPhaseCurvatureLambdaBase N hN

/--
The canonical quantitative Van der Corput scale is strictly positive whenever
the internal height is nonzero.
-/
theorem routeK_offAxisPhaseCurvatureLambda_pos
    {s : ℂ} {N : ℕ} (hN : 3 ≤ N) (hs : routeK_offAxisHeight s ≠ 0) :
    0 < routeK_offAxisPhaseCurvatureLambda s N hN := by
  dsimp [routeK_offAxisPhaseCurvatureLambda]
  exact mul_pos (abs_pos.mpr hs) (routeK_offAxisPhaseCurvatureLambdaBase_pos hN)

/--
The canonical quantitative Van der Corput scale gives a finite-window
phase-curvature witness automatically.
-/
theorem routeK_offAxisPhaseCurvatureWindowAt_canonical
    {s : ℂ} {N : ℕ} (hN : 3 ≤ N) :
    routeK_offAxisPhaseCurvatureWindowAt s N
      (routeK_offAxisPhaseCurvatureLambda s N hN) := by
  intro k m hm hNm
  dsimp [routeK_offAxisPhaseCurvatureLambda]
  simpa [c2LogPhase_secondDiff_abs_eq (t := routeK_offAxisHeight s) (k := k) hm]
    using mul_le_mul_of_nonneg_left
    (routeK_offAxisPhaseCurvatureLambdaBase_le_kernel hN hm hNm)
    (abs_nonneg _)

/--
Any explicit lower bound against the exact logarithmic curvature kernel yields
a quantitative Van der Corput window for the internal phase.
-/
theorem routeK_offAxisPhaseCurvatureWindowAt_of_kernel_lower
    {s : ℂ} {N : ℕ} {lam : ℝ}
    (hLam : ∀ m : ℕ, 1 ≤ m → m + 2 ≤ N →
      lam ≤ |routeK_offAxisHeight s| * c2LogPhaseCurvatureKernel m) :
    routeK_offAxisPhaseCurvatureWindowAt s N lam := by
  intro k m hm hN
  simpa [c2LogPhase_secondDiff_abs_eq (t := routeK_offAxisHeight s) (k := k) hm]
    using hLam m hm hN

/--
Repackage a finite-window quantitative curvature witness as the exact
`VanDerCorputHyp` required by `routeK_thm7_superWeyl`.
-/
theorem routeK_vdcHyp_of_offAxisPhaseCurvatureWindowAt
    {s : ℂ} {N : ℕ} {lam : ℝ} {k : ℕ}
    (hlam : 0 < lam) (hN : 0 < N)
    (hPhase : routeK_offAxisPhaseCurvatureWindowAt s N lam) :
    VanDerCorputHyp (c2LogPhase (routeK_offAxisHeight s) k) N lam := by
  refine ⟨hlam, hN, ?_⟩
  intro m hm hNbound
  simpa using hPhase (k := k) hm hNbound

/--
Unified pointwise bridge packing the Van der Corput finite-window curvature
input together with a pointwise Taylor witness controlled by a curvature
envelope `M₂Envelope`.
-/
def routeK_OffAxisVdCToM2EnvelopeBridgeAt
    (Dinf Binf : ℂ → ℂ) (s : ℂ) (N : ℕ) (lam : ℝ)
    (M₂Envelope : ℂ → ℝ) : Prop :=
  routeK_offAxisPhaseCurvatureWindowAt s N lam ∧
    routeK_OffAxisTaylorDominanceEnvelopeAt Dinf Binf s M₂Envelope

/--
API-level coupling lemma: from the unified bridge one simultaneously recovers
the exact `VanDerCorputHyp` needed for super-Weyl and the explicit Taylor
exclusion-radius data controlled by `M₂Envelope`.
-/
theorem routeK_vdcHyp_and_taylor_envelope_data_of_bridgeAt
    {Dinf Binf : ℂ → ℂ} {s : ℂ} {N : ℕ} {lam : ℝ}
    {M₂Envelope : ℂ → ℝ} {k : ℕ}
    (hlam : 0 < lam) (hN : 0 < N)
    (hBridge : routeK_OffAxisVdCToM2EnvelopeBridgeAt
      Dinf Binf s N lam M₂Envelope) :
    VanDerCorputHyp (c2LogPhase (routeK_offAxisHeight s) k) N lam ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / M₂Envelope s ≤ δStar := by
  rcases hBridge with ⟨hPhase, hTaylor⟩
  refine ⟨routeK_vdcHyp_of_offAxisPhaseCurvatureWindowAt hlam hN hPhase, ?_⟩
  rcases hTaylor with ⟨m, M₂, R, δ, hm, hM₂, hδ, hδsmall, hR, hRsmall, hF_lb, hM₂le⟩
  refine ⟨m, M₂, δ, 2 * m / M₂, hm, hM₂, hδ, rfl, ?_, ?_, ?_⟩
  · simpa using hδsmall
  · exact routeK_elo5_exclusion_radius_pos m M₂ hm hM₂
  · have hEnvelopePos : 0 < M₂Envelope s := lt_of_lt_of_le hM₂ hM₂le
    exact routeK_thm10_deltaStar_lower_bound_scaled_from_M2bound
      m M₂ (M₂Envelope s) hm hM₂ hEnvelopePos hM₂le

/--
Canonical quantitative Van der Corput hypothesis for the internal logarithmic
phase, obtained from the explicit finite-window curvature minimum.
-/
theorem routeK_vdcHyp_canonical_of_nonzero_height
    {s : ℂ} {N k : ℕ} (hN : 3 ≤ N)
    (hs : routeK_offAxisHeight s ≠ 0) :
    VanDerCorputHyp (c2LogPhase (routeK_offAxisHeight s) k) N
      (routeK_offAxisPhaseCurvatureLambda s N hN) := by
  refine routeK_vdcHyp_of_offAxisPhaseCurvatureWindowAt
    (routeK_offAxisPhaseCurvatureLambda_pos hN hs) ?_
    (routeK_offAxisPhaseCurvatureWindowAt_canonical hN)
  omega

/--
Geometric version of the canonical quantitative Van der Corput hypothesis.
-/
theorem routeK_vdcHyp_canonical_of_im_ne_zero
    {s : ℂ} {N k : ℕ} (hN : 3 ≤ N) (hs : s.im ≠ 0) :
    VanDerCorputHyp (c2LogPhase (routeK_offAxisHeight s) k) N
      (routeK_offAxisPhaseCurvatureLambda s N hN) := by
  exact routeK_vdcHyp_canonical_of_nonzero_height hN
    ((routeK_offAxisHeight_ne_zero_iff).2 hs)

/--
Generic off-axis super-Weyl endpoint obtained from a quantitative finite-window
phase-curvature witness and an amplitude bound.
-/
theorem routeK_thm7_superWeyl_of_offAxisPhaseCurvatureWindowAt
    (a : ℕ → ℂ) {s : ℂ} {k N : ℕ} {lam A : ℝ}
    (hlam : 0 < lam) (hN : 0 < N)
    (hPhase : routeK_offAxisPhaseCurvatureWindowAt s N lam)
    (hAmpl : ∀ m : ℕ, 1 ≤ m → m ≤ N → ‖a m‖ ≤ A)
    (hVdC : VanDerCorputSpec a (c2LogPhase (routeK_offAxisHeight s) k) N lam A) :
    ∃ C_vdc : ℝ, 0 < C_vdc ∧
      ‖(Finset.Icc 1 N).sum (fun m =>
        a m * Complex.exp (↑(c2LogPhase (routeK_offAxisHeight s) k m) * Complex.I))‖ ≤
          C_vdc * Real.sqrt (lam⁻¹) := by
  exact routeK_thm7_superWeyl a (routeK_offAxisHeight s) k N lam A
    (routeK_vdcHyp_of_offAxisPhaseCurvatureWindowAt hlam hN hPhase)
    hAmpl hVdC

/--
Canonical off-axis super-Weyl endpoint from nonzero internal height, using the
finite-window scale `λ_N(s)` extracted from the explicit curvature kernel.
-/
theorem routeK_thm7_superWeyl_canonical_of_nonzero_height
    (a : ℕ → ℂ) {s : ℂ} {k N : ℕ} {A : ℝ}
    (hN : 3 ≤ N)
    (hs : routeK_offAxisHeight s ≠ 0)
    (hAmpl : ∀ m : ℕ, 1 ≤ m → m ≤ N → ‖a m‖ ≤ A)
    (hVdC : VanDerCorputSpec a (c2LogPhase (routeK_offAxisHeight s) k) N
      (routeK_offAxisPhaseCurvatureLambda s N hN) A) :
    ∃ C_vdc : ℝ, 0 < C_vdc ∧
      ‖(Finset.Icc 1 N).sum (fun m =>
        a m * Complex.exp (↑(c2LogPhase (routeK_offAxisHeight s) k m) * Complex.I))‖ ≤
          C_vdc * Real.sqrt ((routeK_offAxisPhaseCurvatureLambda s N hN)⁻¹) := by
  exact routeK_thm7_superWeyl_of_offAxisPhaseCurvatureWindowAt a
    (routeK_offAxisPhaseCurvatureLambda_pos hN hs) (by omega)
    (routeK_offAxisPhaseCurvatureWindowAt_canonical hN) hAmpl hVdC

/--
Geometric version of the canonical off-axis super-Weyl endpoint, using
`Im(s) ≠ 0` as the native hypothesis.
-/
theorem routeK_thm7_superWeyl_canonical_of_im_ne_zero
    (a : ℕ → ℂ) {s : ℂ} {k N : ℕ} {A : ℝ}
    (hN : 3 ≤ N)
    (hs : s.im ≠ 0)
    (hAmpl : ∀ m : ℕ, 1 ≤ m → m ≤ N → ‖a m‖ ≤ A)
    (hVdC : VanDerCorputSpec a (c2LogPhase (routeK_offAxisHeight s) k) N
      (routeK_offAxisPhaseCurvatureLambda s N hN) A) :
    ∃ C_vdc : ℝ, 0 < C_vdc ∧
      ‖(Finset.Icc 1 N).sum (fun m =>
        a m * Complex.exp (↑(c2LogPhase (routeK_offAxisHeight s) k m) * Complex.I))‖ ≤
          C_vdc * Real.sqrt ((routeK_offAxisPhaseCurvatureLambda s N hN)⁻¹) := by
  exact routeK_thm7_superWeyl_canonical_of_nonzero_height a hN
    ((routeK_offAxisHeight_ne_zero_iff).2 hs) hAmpl hVdC

end LeanC2
