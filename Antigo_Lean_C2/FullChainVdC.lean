import Mathlib
import LeanC2.FullChain
import LeanC2.TransversalVdC

namespace LeanC2

/-!
# Optional Full-Chain Van der Corput Endpoints

These wrappers keep the super-Weyl/VdC consequences available without making
`FullChain.lean` depend on `VanDerCorput.lean`.
-/

/--
Full-chain-facing off-axis super-Weyl endpoint from a quantitative finite-window
phase-curvature witness and an amplitude bound.
-/
theorem routeK_full_chain_superWeyl_of_offAxisPhaseCurvatureWindowAt
    (a : ℕ → ℂ) {s : ℂ} {k N : ℕ} {lam A : ℝ}
    (hlam : 0 < lam) (hN : 0 < N)
    (hPhase : routeK_offAxisPhaseCurvatureWindowAt s N lam)
    (hAmpl : ∀ m : ℕ, 1 ≤ m → m ≤ N → ‖a m‖ ≤ A)
    (hVdC : VanDerCorputSpec a (c2LogPhase (routeK_offAxisHeight s) k) N lam A) :
    ∃ C_vdc : ℝ, 0 < C_vdc ∧
      ‖(Finset.Icc 1 N).sum (fun m =>
        a m * Complex.exp (↑(c2LogPhase (routeK_offAxisHeight s) k m) * Complex.I))‖ ≤
          C_vdc * Real.sqrt (lam⁻¹) := by
  exact routeK_thm7_superWeyl_of_offAxisPhaseCurvatureWindowAt
    a hlam hN hPhase hAmpl hVdC

/--
Full-chain-facing canonical off-axis super-Weyl endpoint from nonzero internal
height, using the finite-window canonical scale `λ_N(s)`.
-/
theorem routeK_full_chain_superWeyl_canonical_of_nonzero_height
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
  exact routeK_thm7_superWeyl_canonical_of_nonzero_height
    a hN hs hAmpl hVdC

/--
Geometric full-chain-facing canonical off-axis super-Weyl endpoint, using the
native hypothesis `Im(s) ≠ 0`.
-/
theorem routeK_full_chain_superWeyl_canonical_of_im_ne_zero
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
  exact routeK_thm7_superWeyl_canonical_of_im_ne_zero
    a hN hs hAmpl hVdC

/--
Unified endpoint bridge: a single pointwise hypothesis carrying both the
finite-window VdC curvature input and a Taylor witness controlled by
`M₂Envelope` yields, at once, the super-Weyl endpoint and the numerator-side
explicit exclusion-radius package.
-/
theorem routeK_full_chain_superWeyl_and_numerator_envelope_of_vdc_to_M2Envelope
    (a : ℕ → ℂ) {Dinf Binf : ℂ → ℂ} {s : ℂ} {k N : ℕ}
    {lam A : ℝ} {M₂Envelope : ℂ → ℝ}
    (hlam : 0 < lam) (hN : 0 < N)
    (hBridge : routeK_OffAxisVdCToM2EnvelopeBridgeAt
      Dinf Binf s N lam M₂Envelope)
    (hAmpl : ∀ m : ℕ, 1 ≤ m → m ≤ N → ‖a m‖ ≤ A)
    (hVdC : VanDerCorputSpec a (c2LogPhase (routeK_offAxisHeight s) k) N lam A) :
    (∃ C_vdc : ℝ, 0 < C_vdc ∧
      ‖(Finset.Icc 1 N).sum (fun m =>
        a m * Complex.exp (↑(c2LogPhase (routeK_offAxisHeight s) k m) * Complex.I))‖ ≤
          C_vdc * Real.sqrt (lam⁻¹)) ∧
      Dinf s - Binf s ≠ 0 ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / M₂Envelope s ≤ δStar := by
  rcases hBridge with ⟨hPhase, hTaylor⟩
  have hSuper :
      ∃ C_vdc : ℝ, 0 < C_vdc ∧
        ‖(Finset.Icc 1 N).sum (fun m =>
          a m * Complex.exp (↑(c2LogPhase (routeK_offAxisHeight s) k m) * Complex.I))‖ ≤
            C_vdc * Real.sqrt (lam⁻¹) :=
    routeK_full_chain_superWeyl_of_offAxisPhaseCurvatureWindowAt
      a hlam hN hPhase hAmpl hVdC
  have hNum : Dinf s - Binf s ≠ 0 := by
    rcases hTaylor with
      ⟨m, M₂, R, δ, hm, hM₂, hδ, hδsmall, hR, hRsmall, hF_lb, hM₂le⟩
    exact routeK_numerator_nonzero_of_taylor_dominance_at
      ⟨m, M₂, R, δ, hm, hM₂, hδ, hδsmall, hR, hRsmall, hF_lb⟩
  have hRadius :
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / M₂Envelope s ≤ δStar :=
    routeK_taylor_envelope_exclusion_radius_data_at
      (Dinf := Dinf) (Binf := Binf) (s := s)
      (M₂Envelope := M₂Envelope) hTaylor
  exact ⟨hSuper, hNum, hRadius⟩

/--
Continuation lift of the unified bridge: a single pointwise
`VdC → M₂Envelope` hypothesis gives the super-Weyl endpoint, zeta-side
nonvanishing, and the same explicit Taylor exclusion-radius package.
-/
theorem routeK_full_chain_superWeyl_and_zeta_envelope_of_vdc_to_M2Envelope
    (a : ℕ → ℂ) {Dinf Binf ζfun : ℂ → ℂ} {s : ℂ} {k N : ℕ}
    {lam A : ℝ} {M₂Envelope : ℂ → ℝ}
    (hs : 0 < s.re) (hlam : 0 < lam) (hN : 0 < N)
    (hCont : ∀ z : ℂ, 0 < z.re -> Dinf z - Binf z = c0Complex z * ζfun z)
    (hBridge : routeK_OffAxisVdCToM2EnvelopeBridgeAt
      Dinf Binf s N lam M₂Envelope)
    (hAmpl : ∀ m : ℕ, 1 ≤ m → m ≤ N → ‖a m‖ ≤ A)
    (hVdC : VanDerCorputSpec a (c2LogPhase (routeK_offAxisHeight s) k) N lam A) :
    (∃ C_vdc : ℝ, 0 < C_vdc ∧
      ‖(Finset.Icc 1 N).sum (fun m =>
        a m * Complex.exp (↑(c2LogPhase (routeK_offAxisHeight s) k m) * Complex.I))‖ ≤
          C_vdc * Real.sqrt (lam⁻¹)) ∧
      ζfun s ≠ 0 ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / M₂Envelope s ≤ δStar := by
  rcases routeK_full_chain_superWeyl_and_numerator_envelope_of_vdc_to_M2Envelope
      (a := a) (Dinf := Dinf) (Binf := Binf) (s := s) (k := k)
      (N := N) (lam := lam) (A := A) (M₂Envelope := M₂Envelope)
      hlam hN hBridge hAmpl hVdC with
    ⟨hSuper, hNum, hRadius⟩
  have hζ : ζfun s ≠ 0 :=
    (routeK_continuation_nonzero_iff_zeta_nonzero
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) hCont s hs).1 hNum
  exact ⟨hSuper, hζ, hRadius⟩

/--
`Z_spec` lift of the unified bridge: the same pointwise bridge gives the
super-Weyl endpoint, strict norm positivity of `Z_spec`, and the explicit
Taylor exclusion-radius package.
-/
theorem routeK_full_chain_superWeyl_and_Zspec_norm_pos_envelope_of_vdc_to_M2Envelope
    (a : ℕ → ℂ) {Dinf Binf ζfun : ℂ → ℂ} {s : ℂ} {k N : ℕ}
    {lam A : ℝ} {M₂Envelope : ℂ → ℝ}
    (hs : 0 < s.re) (hlam : 0 < lam) (hN : 0 < N)
    (hCont : ∀ z : ℂ, 0 < z.re -> Dinf z - Binf z = c0Complex z * ζfun z)
    (hBridge : routeK_OffAxisVdCToM2EnvelopeBridgeAt
      Dinf Binf s N lam M₂Envelope)
    (hAmpl : ∀ m : ℕ, 1 ≤ m → m ≤ N → ‖a m‖ ≤ A)
    (hVdC : VanDerCorputSpec a (c2LogPhase (routeK_offAxisHeight s) k) N lam A) :
    (∃ C_vdc : ℝ, 0 < C_vdc ∧
      ‖(Finset.Icc 1 N).sum (fun m =>
        a m * Complex.exp (↑(c2LogPhase (routeK_offAxisHeight s) k m) * Complex.I))‖ ≤
          C_vdc * Real.sqrt (lam⁻¹)) ∧
      0 < ‖routeK_Zspec Dinf Binf s‖ ∧
      ∃ m M₂ δ δStar : ℝ,
        0 < m ∧
        0 < M₂ ∧
        0 < δ ∧
        δStar = 2 * m / M₂ ∧
        δ < δStar ∧
        0 < δStar ∧
        2 * m / M₂Envelope s ≤ δStar := by
  rcases routeK_full_chain_superWeyl_and_zeta_envelope_of_vdc_to_M2Envelope
      (a := a) (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) (s := s)
      (k := k) (N := N) (lam := lam) (A := A) (M₂Envelope := M₂Envelope)
      hs hlam hN hCont hBridge hAmpl hVdC with
    ⟨hSuper, hζ, hRadius⟩
  exact ⟨hSuper,
    routeK_continuation_Zspec_norm_pos_of_zeta_nonzero
      (Dinf := Dinf) (Binf := Binf) (ζfun := ζfun) hCont hs hζ,
    hRadius⟩

end LeanC2
